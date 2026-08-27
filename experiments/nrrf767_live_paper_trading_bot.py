"""NRRF767 public-book paper trading bot.

The bot observes the Bitstamp BTC/USD, ETH/USD, and ETH/BTC public order
books, evaluates both reciprocal spot routes with depth and declared costs,
and returns either ``HOLD`` or ``PAPER_SIGNAL``.  It has deliberately no
authenticated endpoint and no order-submission operation.

Raw HTTP response bytes are stored by SHA-256.  Each round is bound to a
hashed configuration and appended to a hash chain.  ``verify_run`` reloads
the raw bytes and recomputes every public-book decision.  This makes a run
replayable and tamper-evident relative to its manifest and chain head; it does
not make the observations simultaneous, externally immutable, or executable.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import ssl
import time
import urllib.request
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path, PurePosixPath
from typing import Iterable, Mapping, Sequence


SCHEMA_VERSION = "nrrf767.live_public_paper.v1"
ARITHMETIC_PRECISION = 80
MAX_PROTOCOL_SIGNIFICANT_DIGITS = 50
MAX_PROTOCOL_ADJUSTED_EXPONENT = 30
PAIR_ORDER = ("BTC_USD", "ETH_USD", "ETH_BTC")
PAIR_ASSETS = {
    "BTC_USD": ("BTC", "USD"),
    "ETH_USD": ("ETH", "USD"),
    "ETH_BTC": ("ETH", "BTC"),
}
PUBLIC_BOOK_ENDPOINTS = {
    "BTC_USD": "https://www.bitstamp.net/api/v2/order_book/btcusd/?group=1",
    "ETH_USD": "https://www.bitstamp.net/api/v2/order_book/ethusd/?group=1",
    "ETH_BTC": "https://www.bitstamp.net/api/v2/order_book/ethbtc/?group=1",
}
PUBLIC_API_DOCUMENTATION = "https://www.bitstamp.net/api/"
FEE_SCHEDULE_REFERENCE = "https://www.bitstamp.net/fee-schedule/"
NON_EXECUTION_LIMITATIONS = (
    "ACCOUNT_BALANCES_NOT_OBSERVED",
    "ACCOUNT_FEE_TIER_NOT_AUTHENTICATED",
    "ATOMIC_EXECUTION_NOT_AVAILABLE",
    "MARKET_MINIMUMS_AND_PRECISION_NOT_MODELLED",
    "PUBLIC_REST_BOOKS_ARE_NONATOMIC",
    "TRADING_STATUS_NOT_AUTHENTICATED",
)
EXPECTED_RUN_KIND = "LIVE_PUBLIC_PAPER_ONLY"
EXPECTED_SOURCE = {
    "venue": "Bitstamp",
    "public_api_documentation": PUBLIC_API_DOCUMENTATION,
    "fee_schedule_reference": FEE_SCHEDULE_REFERENCE,
    "account_specific_fee_verified": False,
}
EXPECTED_MANIFEST_BOUNDARY = {
    "orders_enabled": False,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "formal_receipt_admissions": 0,
    "authenticated_settled_pnl_usd": None,
}
MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "configuration",
    "configuration_sha256",
    "genesis_hash",
    "event_count",
    "final_event_hash",
    "first_recorded_utc",
    "last_recorded_utc",
    "events_file",
    "events_sha256",
    "summary_file",
    "summary_sha256",
    "raw_files",
    "raw_file_sha256",
    "program",
    "program_sha256",
    "source",
    "boundary",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "recorded_unix_us",
    "recorded_utc",
    "configuration_sha256",
    "capture",
    "observation",
    "evaluations",
    "selected_paper_signal",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
CAPTURE_FIELDS = {
    "name",
    "requested_url",
    "final_url",
    "request_started_unix_us",
    "request_started_utc",
    "request_completed_unix_us",
    "request_completed_utc",
    "duration_monotonic_us",
    "http_status",
    "content_type",
    "raw_sha256",
    "raw_file",
    "raw_complete",
    "transport_failure",
}


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def sorted_witnesses(values: Iterable[str]) -> tuple[str, ...]:
    return tuple(sorted(set(values)))


def decimal_text(value: Decimal | None) -> str | None:
    if value is None:
        return None
    if not value.is_finite():
        raise ValueError("non-finite Decimal cannot be serialized")
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text or "0"


def milliseconds_text(microseconds: int | None) -> str | None:
    if microseconds is None:
        return None
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        return decimal_text(Decimal(microseconds) / Decimal(1000))


def milliseconds_to_microseconds(value: Decimal) -> int:
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        return int(value * Decimal(1000))


def iso_from_unix_us(unix_us: int) -> str:
    seconds, micros = divmod(unix_us, 1_000_000)
    instant = datetime.fromtimestamp(seconds, tz=timezone.utc) + timedelta(microseconds=micros)
    return instant.isoformat(timespec="microseconds").replace("+00:00", "Z")


def parse_decimal(value: object) -> Decimal:
    parsed = Decimal(str(value))
    if not parsed.is_finite():
        raise InvalidOperation(str(value))
    return parsed


def bounded_protocol_decimal(value: object) -> Decimal:
    parsed = parse_decimal(value)
    if parsed != 0 and (
        len(parsed.as_tuple().digits) > MAX_PROTOCOL_SIGNIFICANT_DIGITS
        or abs(parsed.adjusted()) > MAX_PROTOCOL_ADJUSTED_EXPONENT
    ):
        raise ValueError("decimal exceeds the protocol precision bounds")
    return parsed


def strict_json_loads(raw: bytes) -> object:
    def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    return json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object)


@dataclass(frozen=True)
class PaperConfig:
    fee_bps_per_leg: Decimal = Decimal("25")
    safety_bps: Decimal = Decimal("5")
    notionals_usd: tuple[Decimal, ...] = (
        Decimal("100"),
        Decimal("1000"),
        Decimal("10000"),
    )
    max_book_age_ms: Decimal = Decimal("5000")
    max_future_ms: Decimal = Decimal("1000")
    max_cross_book_skew_ms: Decimal = Decimal("1500")
    max_acquisition_span_ms: Decimal = Decimal("2500")
    max_request_start_skew_ms: Decimal = Decimal("250")
    request_timeout_seconds: Decimal = Decimal("20")
    max_response_bytes: int = 8 * 1024 * 1024

    def __post_init__(self) -> None:
        decimal_fields = (
            self.fee_bps_per_leg,
            self.safety_bps,
            *self.notionals_usd,
            self.max_book_age_ms,
            self.max_future_ms,
            self.max_cross_book_skew_ms,
            self.max_acquisition_span_ms,
            self.max_request_start_skew_ms,
            self.request_timeout_seconds,
        )
        if any(not value.is_finite() for value in decimal_fields):
            raise ValueError("all numeric configuration values must be finite")
        if any(
            len(value.as_tuple().digits) > MAX_PROTOCOL_SIGNIFICANT_DIGITS
            or abs(value.adjusted()) > MAX_PROTOCOL_ADJUSTED_EXPONENT
            for value in decimal_fields
            if value != 0
        ):
            raise ValueError("numeric configuration exceeds the protocol precision bounds")
        if not (Decimal(0) <= self.fee_bps_per_leg < Decimal(10_000)):
            raise ValueError("fee_bps_per_leg must satisfy 0 <= fee < 10000")
        if self.safety_bps < 0:
            raise ValueError("safety_bps must be nonnegative")
        if not self.notionals_usd or any(value <= 0 for value in self.notionals_usd):
            raise ValueError("notionals_usd must be nonempty and positive")
        if len(set(self.notionals_usd)) != len(self.notionals_usd):
            raise ValueError("notionals_usd must not contain duplicates")
        positive_limits = (
            self.max_book_age_ms,
            self.max_cross_book_skew_ms,
            self.max_acquisition_span_ms,
            self.max_request_start_skew_ms,
            self.request_timeout_seconds,
        )
        if any(value <= 0 for value in positive_limits):
            raise ValueError("age, skew, span, start-skew, and timeout limits must be positive")
        if self.max_future_ms < 0:
            raise ValueError("max_future_ms must be nonnegative")
        if (
            type(self.max_response_bytes) is not int
            or not (0 < self.max_response_bytes <= 64 * 1024 * 1024)
        ):
            raise ValueError("max_response_bytes must be between 1 and 64 MiB")

    def as_dict(self) -> dict[str, object]:
        return {
            "fee_bps_per_leg": decimal_text(self.fee_bps_per_leg),
            "fee_model": "deduct declared fee from the received asset after each leg",
            "safety_bps": decimal_text(self.safety_bps),
            "notionals_usd": [decimal_text(value) for value in self.notionals_usd],
            "max_book_age_ms": decimal_text(self.max_book_age_ms),
            "max_future_ms": decimal_text(self.max_future_ms),
            "max_cross_book_skew_ms": decimal_text(self.max_cross_book_skew_ms),
            "max_acquisition_span_ms": decimal_text(self.max_acquisition_span_ms),
            "max_request_start_skew_ms": decimal_text(self.max_request_start_skew_ms),
            "request_timeout_seconds": decimal_text(self.request_timeout_seconds),
            "max_response_bytes": self.max_response_bytes,
            "endpoints": dict(PUBLIC_BOOK_ENDPOINTS),
            "transport": "parallel public HTTPS GET only",
            "orders_enabled": False,
        }

    @classmethod
    def from_dict(cls, value: Mapping[str, object]) -> "PaperConfig":
        expected_endpoints = dict(PUBLIC_BOOK_ENDPOINTS)
        if value.get("endpoints") != expected_endpoints:
            raise ValueError("manifest endpoints do not match the fixed public endpoints")
        if value.get("orders_enabled") is not False:
            raise ValueError("orders_enabled must be false")
        if type(value.get("max_response_bytes")) is not int:
            raise ValueError("max_response_bytes must be an integer")
        config = cls(
            fee_bps_per_leg=parse_decimal(value["fee_bps_per_leg"]),
            safety_bps=parse_decimal(value["safety_bps"]),
            notionals_usd=tuple(parse_decimal(item) for item in value["notionals_usd"]),
            max_book_age_ms=parse_decimal(value["max_book_age_ms"]),
            max_future_ms=parse_decimal(value["max_future_ms"]),
            max_cross_book_skew_ms=parse_decimal(value["max_cross_book_skew_ms"]),
            max_acquisition_span_ms=parse_decimal(value["max_acquisition_span_ms"]),
            max_request_start_skew_ms=parse_decimal(value["max_request_start_skew_ms"]),
            request_timeout_seconds=parse_decimal(value["request_timeout_seconds"]),
            max_response_bytes=value["max_response_bytes"],
        )
        if dict(value) != config.as_dict():
            raise ValueError("configuration contains altered or noncanonical fields")
        return config

    @property
    def digest(self) -> str:
        return sha256_bytes(canonical_json_bytes(self.as_dict()))


@dataclass(frozen=True)
class Amount:
    asset: str
    value: Decimal

    def __post_init__(self) -> None:
        if not self.value.is_finite() or self.value < 0:
            raise ValueError("amount must be finite and nonnegative")


@dataclass(frozen=True)
class Book:
    name: str
    base: str
    quote: str
    bids: tuple[tuple[Decimal, Decimal], ...]
    asks: tuple[tuple[Decimal, Decimal], ...]


@dataclass(frozen=True)
class CaptureReceipt:
    name: str
    requested_url: str
    final_url: str | None
    request_started_unix_us: int
    request_completed_unix_us: int
    duration_monotonic_us: int
    http_status: int | None
    content_type: str | None
    raw: bytes | None
    raw_complete: bool
    transport_failure: str | None


@dataclass(frozen=True)
class LegResult:
    output: Amount
    gross_output: Decimal
    fee_amount: Decimal
    full_depth_coverage: bool
    levels_used: int
    remaining_input: Decimal
    worst_price: Decimal | None

    def as_dict(self, leg: str, input_amount: Amount) -> dict[str, object]:
        return {
            "leg": leg,
            "input_asset": input_amount.asset,
            "input_amount": decimal_text(input_amount.value),
            "output_asset": self.output.asset,
            "gross_output": decimal_text(self.gross_output),
            "fee_amount": decimal_text(self.fee_amount),
            "net_output": decimal_text(self.output.value),
            "full_depth_coverage": self.full_depth_coverage,
            "levels_used": self.levels_used,
            "remaining_input": decimal_text(self.remaining_input),
            "worst_price": decimal_text(self.worst_price),
        }


def validate_levels(
    raw_levels: object,
    *,
    side: str,
    market: str,
) -> tuple[tuple[tuple[Decimal, Decimal], ...], tuple[str, ...]]:
    if side not in {"bids", "asks"}:
        raise ValueError(side)
    if not isinstance(raw_levels, list) or not raw_levels:
        return (), (f"EMPTY_{side.upper()}_{market}",)
    parsed: list[tuple[Decimal, Decimal]] = []
    failures: list[str] = []
    for level in raw_levels:
        try:
            if not isinstance(level, list) or len(level) != 2:
                raise ValueError("level must be [price, base_amount]")
            if not isinstance(level[0], str) or not isinstance(level[1], str):
                raise ValueError("Bitstamp level values must be decimal strings")
            price = bounded_protocol_decimal(level[0])
            base_amount = bounded_protocol_decimal(level[1])
            if price <= 0 or base_amount <= 0:
                raise ValueError("level values must be positive")
            parsed.append((price, base_amount))
        except (InvalidOperation, TypeError, ValueError):
            failures.append(f"INVALID_{side.upper()}_LEVEL_{market}")
            return tuple(parsed), sorted_witnesses(failures)
    if side == "bids":
        ordered = all(left[0] >= right[0] for left, right in zip(parsed, parsed[1:]))
    else:
        ordered = all(left[0] <= right[0] for left, right in zip(parsed, parsed[1:]))
    if not ordered:
        failures.append(f"UNSORTED_{side.upper()}_{market}")
    if len({price for price, _amount in parsed}) != len(parsed):
        failures.append(f"DUPLICATE_{side.upper()}_PRICE_{market}")
    return tuple(parsed), sorted_witnesses(failures)


def parse_public_book(
    receipt: CaptureReceipt,
    config: PaperConfig,
) -> tuple[Book | None, dict[str, object]]:
    failures: list[str] = []
    exchange_microtimestamp: int | None = None
    age_us: int | None = None
    bids: tuple[tuple[Decimal, Decimal], ...] = ()
    asks: tuple[tuple[Decimal, Decimal], ...] = ()

    if receipt.name not in PAIR_ASSETS:
        failures.append("UNKNOWN_MARKET")
    if receipt.requested_url != PUBLIC_BOOK_ENDPOINTS.get(receipt.name):
        failures.append(f"UNEXPECTED_ENDPOINT_{receipt.name}")
    if receipt.request_completed_unix_us < receipt.request_started_unix_us:
        failures.append(f"WALL_CLOCK_REGRESSION_{receipt.name}")
    if receipt.duration_monotonic_us < 0:
        failures.append(f"NEGATIVE_DURATION_{receipt.name}")
    if receipt.duration_monotonic_us > milliseconds_to_microseconds(
        config.max_acquisition_span_ms
    ):
        failures.append(f"REQUEST_DURATION_EXCEEDED_{receipt.name}")
    if receipt.transport_failure is not None:
        failures.append(f"TRANSPORT_FAILURE_{receipt.name}")
    if receipt.http_status != 200:
        failures.append(f"HTTP_STATUS_{receipt.name}")
    if receipt.final_url != receipt.requested_url:
        failures.append(f"UNEXPECTED_REDIRECT_{receipt.name}")
    if not receipt.content_type or "json" not in receipt.content_type.lower():
        failures.append(f"UNEXPECTED_CONTENT_TYPE_{receipt.name}")
    if not receipt.raw_complete:
        failures.append(f"INCOMPLETE_RESPONSE_{receipt.name}")
    if receipt.raw is None:
        failures.append(f"MISSING_RAW_RESPONSE_{receipt.name}")
    elif len(receipt.raw) > config.max_response_bytes:
        failures.append(f"OVERSIZED_RESPONSE_{receipt.name}")

    payload: object | None = None
    if not failures and receipt.raw is not None:
        try:
            payload = strict_json_loads(receipt.raw)
        except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError):
            failures.append(f"INVALID_JSON_{receipt.name}")
    if payload is not None and not isinstance(payload, dict):
        failures.append(f"INVALID_ROOT_{receipt.name}")
    if isinstance(payload, dict):
        bids, bid_failures = validate_levels(payload.get("bids"), side="bids", market=receipt.name)
        asks, ask_failures = validate_levels(payload.get("asks"), side="asks", market=receipt.name)
        failures.extend(bid_failures)
        failures.extend(ask_failures)
        try:
            raw_microtimestamp = payload["microtimestamp"]
            raw_timestamp = payload["timestamp"]
            if (
                not isinstance(raw_microtimestamp, str)
                or not raw_microtimestamp.isdigit()
                or len(raw_microtimestamp) > 20
                or not isinstance(raw_timestamp, str)
                or not raw_timestamp.isdigit()
                or len(raw_timestamp) > 20
            ):
                raise ValueError("timestamps must be unsigned decimal strings")
            exchange_microtimestamp = int(raw_microtimestamp)
            exchange_timestamp = int(raw_timestamp)
            if exchange_microtimestamp // 1_000_000 != exchange_timestamp:
                failures.append(f"TIMESTAMP_MISMATCH_{receipt.name}")
            age_us = receipt.request_completed_unix_us - exchange_microtimestamp
            if age_us < -milliseconds_to_microseconds(config.max_future_ms):
                failures.append(f"FUTURE_BOOK_{receipt.name}")
            if age_us > milliseconds_to_microseconds(config.max_book_age_ms):
                failures.append(f"STALE_BOOK_{receipt.name}")
        except (KeyError, TypeError, ValueError, OverflowError):
            failures.append(f"INVALID_TIMESTAMP_{receipt.name}")
        if bids and asks and bids[0][0] >= asks[0][0]:
            failures.append(f"LOCKED_OR_CROSSED_BOOK_{receipt.name}")

    failures_tuple = sorted_witnesses(failures)
    market_meta = {
        "exchange_microtimestamp": (
            str(exchange_microtimestamp) if exchange_microtimestamp is not None else None
        ),
        "book_age_ms_at_receipt": milliseconds_text(age_us),
        "bid_levels": len(bids),
        "ask_levels": len(asks),
        "best_bid": decimal_text(bids[0][0]) if bids else None,
        "best_ask": decimal_text(asks[0][0]) if asks else None,
        "validation_witnesses": list(failures_tuple),
    }
    if failures_tuple or receipt.name not in PAIR_ASSETS:
        return None, market_meta
    base, quote = PAIR_ASSETS[receipt.name]
    return Book(receipt.name, base, quote, bids, asks), market_meta


def walk_buy_base(quote_input: Amount, book: Book, fee_rate: Decimal) -> LegResult:
    if quote_input.asset != book.quote:
        raise ValueError(f"expected {book.quote}, received {quote_input.asset}")
    remaining = quote_input.value
    gross_base = Decimal(0)
    levels_used = 0
    worst_price: Decimal | None = None
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        for price, available_base in book.asks:
            spend = min(remaining, price * available_base)
            if spend > 0:
                gross_base += spend / price
                remaining -= spend
                levels_used += 1
                worst_price = price
            if remaining == 0:
                break
        fee_amount = gross_base * fee_rate
        net_base = gross_base - fee_amount
    return LegResult(
        output=Amount(book.base, net_base),
        gross_output=gross_base,
        fee_amount=fee_amount,
        full_depth_coverage=remaining == 0,
        levels_used=levels_used,
        remaining_input=remaining,
        worst_price=worst_price,
    )


def walk_sell_base(base_input: Amount, book: Book, fee_rate: Decimal) -> LegResult:
    if base_input.asset != book.base:
        raise ValueError(f"expected {book.base}, received {base_input.asset}")
    remaining = base_input.value
    gross_quote = Decimal(0)
    levels_used = 0
    worst_price: Decimal | None = None
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        for price, available_base in book.bids:
            sold = min(remaining, available_base)
            if sold > 0:
                gross_quote += sold * price
                remaining -= sold
                levels_used += 1
                worst_price = price
            if remaining == 0:
                break
        fee_amount = gross_quote * fee_rate
        net_quote = gross_quote - fee_amount
    return LegResult(
        output=Amount(book.quote, net_quote),
        gross_output=gross_quote,
        fee_amount=fee_amount,
        full_depth_coverage=remaining == 0,
        levels_used=levels_used,
        remaining_input=remaining,
        worst_price=worst_price,
    )


def evaluate_route(
    orientation: str,
    start_usd: Decimal,
    books: Mapping[str, Book],
    config: PaperConfig,
    observation_witnesses: Sequence[str] = (),
) -> dict[str, object]:
    result: dict[str, object] = {
        "orientation": orientation,
        "path": (
            "USD->BTC->ETH->USD" if orientation == "PLUS" else "USD->ETH->BTC->USD"
        ),
        "start_usd": decimal_text(start_usd),
        "decision": "HOLD",
        "full_depth_coverage": False,
        "candidate_final_usd": None,
        "candidate_delta_usd": None,
        "candidate_return_bps": None,
        "no_order_account_delta_usd": "0",
        "authenticated_settled_pnl_usd": None,
        "orders_submitted": 0,
        "formal_receipt_admissions": 0,
        "witnesses": list(sorted_witnesses(observation_witnesses)),
        "non_execution_limitations": list(NON_EXECUTION_LIMITATIONS),
        "leg_trace": [],
    }
    if observation_witnesses or len(books) != 3:
        result["witnesses"] = list(
            sorted_witnesses((*observation_witnesses, "PUBLIC_OBSERVATION_OPEN"))
        )
        return result

    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        fee_rate = config.fee_bps_per_leg / Decimal(10_000)
    current = Amount("USD", start_usd)
    trace: list[dict[str, object]] = []
    if orientation == "PLUS":
        plan = (
            ("USD->BTC", "buy", books["BTC_USD"]),
            ("BTC->ETH", "buy", books["ETH_BTC"]),
            ("ETH->USD", "sell", books["ETH_USD"]),
        )
    elif orientation == "MINUS":
        plan = (
            ("USD->ETH", "buy", books["ETH_USD"]),
            ("ETH->BTC", "sell", books["ETH_BTC"]),
            ("BTC->USD", "sell", books["BTC_USD"]),
        )
    else:
        raise ValueError(f"unknown orientation: {orientation}")

    failures: list[str] = []
    for label, operation, book in plan:
        leg_input = current
        leg = (
            walk_buy_base(leg_input, book, fee_rate)
            if operation == "buy"
            else walk_sell_base(leg_input, book, fee_rate)
        )
        trace.append(leg.as_dict(label, leg_input))
        if not leg.full_depth_coverage:
            failures.append(f"INSUFFICIENT_PUBLIC_DEPTH_{label.replace('->', '_TO_')}")
            break
        current = leg.output

    result["leg_trace"] = trace
    if failures or len(trace) != 3:
        result["witnesses"] = list(sorted_witnesses(failures))
        return result
    if current.asset != "USD":
        raise AssertionError("route did not return to USD")
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        delta = current.value - start_usd
        return_bps = delta / start_usd * Decimal(10_000)
    if return_bps <= 0:
        failures.append("NONPOSITIVE_CANDIDATE_AFTER_DECLARED_COSTS")
    elif return_bps <= config.safety_bps:
        failures.append("CANDIDATE_NOT_ABOVE_SAFETY_RESERVE")

    result.update(
        {
            "decision": "PAPER_SIGNAL" if not failures else "HOLD",
            "full_depth_coverage": True,
            "candidate_final_usd": decimal_text(current.value),
            "candidate_delta_usd": decimal_text(delta),
            "candidate_return_bps": decimal_text(return_bps),
            "witnesses": list(sorted_witnesses(failures)),
        }
    )
    return result


def derive_round(
    receipts: Mapping[str, CaptureReceipt],
    config: PaperConfig,
) -> dict[str, object]:
    books: dict[str, Book] = {}
    markets: dict[str, dict[str, object]] = {}
    failures: list[str] = []
    exchange_timestamps: list[int] = []
    starts: list[int] = []
    completions: list[int] = []

    for name in PAIR_ORDER:
        receipt = receipts.get(name)
        if receipt is None:
            failures.append(f"MISSING_RECEIPT_{name}")
            markets[name] = {
                "exchange_microtimestamp": None,
                "book_age_ms_at_receipt": None,
                "bid_levels": 0,
                "ask_levels": 0,
                "best_bid": None,
                "best_ask": None,
                "validation_witnesses": [f"MISSING_RECEIPT_{name}"],
            }
            continue
        book, meta = parse_public_book(receipt, config)
        markets[name] = meta
        failures.extend(meta["validation_witnesses"])
        starts.append(receipt.request_started_unix_us)
        completions.append(receipt.request_completed_unix_us)
        if meta["exchange_microtimestamp"] is not None:
            exchange_timestamps.append(int(meta["exchange_microtimestamp"]))
        if book is not None:
            books[name] = book

    cross_book_skew_us: int | None = None
    acquisition_span_us: int | None = None
    request_start_skew_us: int | None = None
    request_overlap_us: int | None = None
    if len(exchange_timestamps) == 3:
        cross_book_skew_us = max(exchange_timestamps) - min(exchange_timestamps)
        if cross_book_skew_us > milliseconds_to_microseconds(config.max_cross_book_skew_ms):
            failures.append("CROSS_BOOK_TIMESTAMP_SKEW")
    if len(starts) == 3 and len(completions) == 3:
        acquisition_span_us = max(completions) - min(starts)
        request_start_skew_us = max(starts) - min(starts)
        request_overlap_us = min(completions) - max(starts)
        if acquisition_span_us > milliseconds_to_microseconds(config.max_acquisition_span_ms):
            failures.append("ACQUISITION_SPAN_EXCEEDED")
        if request_start_skew_us > milliseconds_to_microseconds(
            config.max_request_start_skew_ms
        ):
            failures.append("REQUEST_START_SKEW_EXCEEDED")
        if request_overlap_us < 0:
            failures.append("REQUEST_WINDOWS_DO_NOT_OVERLAP")
    if len(books) != 3:
        failures.append("INCOMPLETE_PUBLIC_TRIANGLE")

    witnesses = sorted_witnesses(failures)
    observation = {
        "state": "IDENTIFIED_PUBLIC_BOOKS" if not witnesses else "OPEN_PUBLIC_BOOKS",
        "witnesses": list(witnesses),
        "markets": markets,
        "cross_book_timestamp_skew_ms": milliseconds_text(cross_book_skew_us),
        "acquisition_span_ms": milliseconds_text(acquisition_span_us),
        "request_start_skew_ms": milliseconds_text(request_start_skew_us),
        "request_window_overlap_ms": milliseconds_text(request_overlap_us),
    }
    evaluations = [
        evaluate_route(orientation, notional, books, config, witnesses)
        for orientation in ("PLUS", "MINUS")
        for notional in config.notionals_usd
    ]
    signals = [row for row in evaluations if row["decision"] == "PAPER_SIGNAL"]
    selected = (
        max(signals, key=lambda row: parse_decimal(row["candidate_return_bps"]))
        if signals
        else None
    )
    return {
        "observation": observation,
        "evaluations": evaluations,
        "selected_paper_signal": selected,
        "boundary": {
            "evidence_grade": "PUBLIC_REST_COUNTERFACTUAL",
            "execution_authorized": False,
            "orders_submitted": 0,
            "authenticated_fills": 0,
            "formal_receipt_admissions": 0,
            "no_order_account_delta_usd": "0",
            "authenticated_settled_pnl_usd": None,
            "limitations": list(NON_EXECUTION_LIMITATIONS),
        },
    }


def fetch_public_book(name: str, config: PaperConfig) -> CaptureReceipt:
    url = PUBLIC_BOOK_ENDPOINTS[name]
    request = urllib.request.Request(
        url,
        headers={"Accept": "application/json", "User-Agent": "NRRF767-Public-Paper/1.0"},
        method="GET",
    )
    wall_start_ns = time.time_ns()
    monotonic_start_ns = time.monotonic_ns()
    final_url: str | None = None
    status: int | None = None
    content_type: str | None = None
    raw: bytes | None = None
    raw_complete = False
    failure: str | None = None
    try:
        context = ssl.create_default_context()
        with urllib.request.urlopen(
            request,
            timeout=float(config.request_timeout_seconds),
            context=context,
        ) as response:
            final_url = response.geturl()
            status = response.status
            content_type = response.headers.get("Content-Type")
            raw = response.read(config.max_response_bytes + 1)
            raw_complete = len(raw) <= config.max_response_bytes
            if not raw_complete:
                failure = "response exceeded configured byte limit"
    except Exception as exc:  # expected transport failures become explicit HOLD evidence
        failure = f"{type(exc).__name__}: {exc}"
    monotonic_end_ns = time.monotonic_ns()
    wall_end_ns = time.time_ns()
    return CaptureReceipt(
        name=name,
        requested_url=url,
        final_url=final_url,
        request_started_unix_us=wall_start_ns // 1000,
        request_completed_unix_us=wall_end_ns // 1000,
        duration_monotonic_us=(monotonic_end_ns - monotonic_start_ns) // 1000,
        http_status=status,
        content_type=content_type,
        raw=raw,
        raw_complete=raw_complete,
        transport_failure=failure,
    )


def capture_public_round(config: PaperConfig) -> dict[str, CaptureReceipt]:
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        futures = {name: pool.submit(fetch_public_book, name, config) for name in PAIR_ORDER}
        return {name: futures[name].result() for name in PAIR_ORDER}


def receipt_record(receipt: CaptureReceipt, raw_file: str | None) -> dict[str, object]:
    return {
        "name": receipt.name,
        "requested_url": receipt.requested_url,
        "final_url": receipt.final_url,
        "request_started_unix_us": receipt.request_started_unix_us,
        "request_started_utc": iso_from_unix_us(receipt.request_started_unix_us),
        "request_completed_unix_us": receipt.request_completed_unix_us,
        "request_completed_utc": iso_from_unix_us(receipt.request_completed_unix_us),
        "duration_monotonic_us": receipt.duration_monotonic_us,
        "http_status": receipt.http_status,
        "content_type": receipt.content_type,
        "raw_sha256": sha256_bytes(receipt.raw) if receipt.raw is not None else None,
        "raw_file": raw_file,
        "raw_complete": receipt.raw_complete,
        "transport_failure": receipt.transport_failure,
    }


def receipt_from_record(record: Mapping[str, object], raw: bytes | None) -> CaptureReceipt:
    return CaptureReceipt(
        name=str(record["name"]),
        requested_url=str(record["requested_url"]),
        final_url=str(record["final_url"]) if record["final_url"] is not None else None,
        request_started_unix_us=int(record["request_started_unix_us"]),
        request_completed_unix_us=int(record["request_completed_unix_us"]),
        duration_monotonic_us=int(record["duration_monotonic_us"]),
        http_status=int(record["http_status"]) if record["http_status"] is not None else None,
        content_type=str(record["content_type"]) if record["content_type"] is not None else None,
        raw=raw,
        raw_complete=record["raw_complete"] is True,
        transport_failure=(
            str(record["transport_failure"]) if record["transport_failure"] is not None else None
        ),
    )


def genesis_hash(config: PaperConfig) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": "GENESIS",
                "configuration_sha256": config.digest,
            }
        )
    )


def build_event(
    round_index: int,
    receipts: Mapping[str, CaptureReceipt],
    raw_files: Mapping[str, str | None],
    config: PaperConfig,
    previous_event_hash: str,
) -> dict[str, object]:
    capture = {name: receipt_record(receipts[name], raw_files.get(name)) for name in PAIR_ORDER}
    completed = max(receipt.request_completed_unix_us for receipt in receipts.values())
    derived = derive_round(receipts, config)
    payload: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "event_kind": "PUBLIC_PAPER_ROUND",
        "round_index": round_index,
        "recorded_unix_us": completed,
        "recorded_utc": iso_from_unix_us(completed),
        "configuration_sha256": config.digest,
        "capture": capture,
        **derived,
        "previous_event_hash": previous_event_hash,
    }
    payload["event_hash"] = sha256_bytes(canonical_json_bytes(payload))
    return payload


def write_content_addressed_raw(root: Path, receipt: CaptureReceipt) -> str | None:
    if receipt.raw is None:
        return None
    digest = sha256_bytes(receipt.raw)
    relative = Path("raw") / f"{digest}.json"
    destination = root / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        if destination.read_bytes() != receipt.raw:
            raise ValueError("content-address collision")
    else:
        with destination.open("xb") as target:
            target.write(receipt.raw)
            target.flush()
            os.fsync(target.fileno())
    return relative.as_posix()


def summarize_events(events: Sequence[Mapping[str, object]]) -> dict[str, object]:
    evaluations = [item for event in events for item in event["evaluations"]]
    numeric = [item for item in evaluations if item["candidate_return_bps"] is not None]
    signals = [item for item in evaluations if item["decision"] == "PAPER_SIGNAL"]
    selected = [event["selected_paper_signal"] for event in events if event["selected_paper_signal"]]
    witnesses = Counter(witness for item in evaluations for witness in item["witnesses"])
    states = Counter(event["observation"]["state"] for event in events)
    best = max(numeric, key=lambda item: parse_decimal(item["candidate_return_bps"]), default=None)
    worst = min(numeric, key=lambda item: parse_decimal(item["candidate_return_bps"]), default=None)

    def median(values: Sequence[Decimal]) -> Decimal | None:
        if not values:
            return None
        ordered = sorted(values)
        middle = len(ordered) // 2
        if len(ordered) % 2:
            return ordered[middle]
        left, right = ordered[middle - 1], ordered[middle]
        least_exponent = min(left.as_tuple().exponent, right.as_tuple().exponent)
        greatest_adjusted = max(left.adjusted(), right.adjusted())
        with localcontext() as context:
            context.prec = max(
                ARITHMETIC_PRECISION,
                greatest_adjusted - least_exponent + 4,
            )
            return (left + right) / Decimal(2)

    def statistics(values: Sequence[Decimal]) -> dict[str, object]:
        return {
            "count": len(values),
            "minimum": decimal_text(min(values)) if values else None,
            "median": decimal_text(median(values)),
            "maximum": decimal_text(max(values)) if values else None,
        }

    def compact_candidate(item: Mapping[str, object] | None) -> dict[str, object] | None:
        if item is None:
            return None
        return {
            "orientation": item["orientation"],
            "path": item["path"],
            "start_usd": item["start_usd"],
            "decision": item["decision"],
            "candidate_final_usd": item["candidate_final_usd"],
            "candidate_delta_usd": item["candidate_delta_usd"],
            "candidate_return_bps": item["candidate_return_bps"],
            "witnesses": item["witnesses"],
            "no_order_account_delta_usd": item["no_order_account_delta_usd"],
            "authenticated_settled_pnl_usd": item["authenticated_settled_pnl_usd"],
        }

    route_size_statistics: dict[str, dict[str, object]] = {}
    for orientation in ("PLUS", "MINUS"):
        route_size_statistics[orientation] = {}
        for notional in sorted({str(item["start_usd"]) for item in evaluations}, key=Decimal):
            rows = [
                item
                for item in evaluations
                if item["orientation"] == orientation and item["start_usd"] == notional
            ]
            returns = [
                parse_decimal(item["candidate_return_bps"])
                for item in rows
                if item["candidate_return_bps"] is not None
            ]
            route_size_statistics[orientation][notional] = {
                "evaluations": len(rows),
                "full_depth_numeric": len(returns),
                "paper_signals": sum(item["decision"] == "PAPER_SIGNAL" for item in rows),
                "candidate_return_bps": statistics(returns),
            }

    timing_statistics: dict[str, object] = {}
    for field in (
        "cross_book_timestamp_skew_ms",
        "acquisition_span_ms",
        "request_start_skew_ms",
        "request_window_overlap_ms",
    ):
        values = [
            parse_decimal(event["observation"][field])
            for event in events
            if event["observation"][field] is not None
        ]
        timing_statistics[field] = statistics(values)
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds_returned": len(events),
        "observation_states": dict(sorted(states.items())),
        "route_size_evaluations": len(evaluations),
        "numeric_full_depth_evaluations": len(numeric),
        "paper_signals": len(signals),
        "rounds_with_selected_paper_signal": len(selected),
        "best_candidate": compact_candidate(best),
        "worst_candidate": compact_candidate(worst),
        "route_size_statistics": route_size_statistics,
        "timing_statistics_ms": timing_statistics,
        "witness_counts": dict(sorted(witnesses.items())),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "formal_receipt_admissions": 0,
        "no_order_account_delta_usd": "0",
        "authenticated_settled_pnl_usd": None,
        "profit_claimed": False,
        "alternative_simulations_aggregated_as_portfolio_pnl": False,
    }


def prepare_output_directory(root: Path) -> None:
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"refusing to overwrite nonempty run directory: {root}")
    root.mkdir(parents=True, exist_ok=True)


def capture_run(
    output_dir: Path,
    *,
    rounds: int,
    interval_seconds: Decimal,
    config: PaperConfig,
) -> dict[str, object]:
    if type(rounds) is not int or rounds <= 0:
        raise ValueError("rounds must be positive")
    if (
        not interval_seconds.is_finite()
        or interval_seconds < 0
        or (
            interval_seconds != 0
            and (
                len(interval_seconds.as_tuple().digits) > MAX_PROTOCOL_SIGNIFICANT_DIGITS
                or abs(interval_seconds.adjusted()) > MAX_PROTOCOL_ADJUSTED_EXPONENT
            )
        )
    ):
        raise ValueError("interval_seconds must be finite and nonnegative")
    prepare_output_directory(output_dir)
    ledger_path = output_dir / "events.jsonl"
    events: list[dict[str, object]] = []
    previous_hash = genesis_hash(config)
    with ledger_path.open("xb") as ledger:
        for index in range(rounds):
            round_start = time.monotonic()
            receipts = capture_public_round(config)
            raw_files = {
                name: write_content_addressed_raw(output_dir, receipts[name]) for name in PAIR_ORDER
            }
            event = build_event(index, receipts, raw_files, config, previous_hash)
            ledger.write(canonical_json_bytes(event) + b"\n")
            ledger.flush()
            os.fsync(ledger.fileno())
            events.append(event)
            previous_hash = str(event["event_hash"])
            if index + 1 < rounds:
                with localcontext() as context:
                    context.prec = ARITHMETIC_PRECISION
                    remaining = interval_seconds - Decimal(
                        str(time.monotonic() - round_start)
                    )
                if remaining > 0:
                    time.sleep(float(remaining))

    summary = summarize_events(events)
    summary_path = output_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    raw_files = sorted(path.relative_to(output_dir).as_posix() for path in (output_dir / "raw").glob("*"))
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": EXPECTED_RUN_KIND,
        "configuration": config.as_dict(),
        "configuration_sha256": config.digest,
        "genesis_hash": genesis_hash(config),
        "event_count": len(events),
        "final_event_hash": previous_hash,
        "first_recorded_utc": events[0]["recorded_utc"],
        "last_recorded_utc": events[-1]["recorded_utc"],
        "events_file": ledger_path.name,
        "events_sha256": sha256_file(ledger_path),
        "summary_file": summary_path.name,
        "summary_sha256": sha256_file(summary_path),
        "raw_files": raw_files,
        "raw_file_sha256": {relative: sha256_file(output_dir / relative) for relative in raw_files},
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "source": EXPECTED_SOURCE,
        "boundary": EXPECTED_MANIFEST_BOUNDARY,
    }
    manifest_path = output_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest


def verify_run(run_dir: Path) -> dict[str, object]:
    manifest_path = run_dir / "manifest.json"
    manifest = strict_json_loads(manifest_path.read_bytes())
    if not isinstance(manifest, dict) or manifest.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("invalid manifest schema")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("manifest fields do not match the protocol")
    if manifest.get("run_kind") != EXPECTED_RUN_KIND:
        raise ValueError("manifest run kind is not public paper")
    if manifest.get("source") != EXPECTED_SOURCE:
        raise ValueError("manifest source boundary mismatch")
    if manifest.get("boundary") != EXPECTED_MANIFEST_BOUNDARY:
        raise ValueError("manifest execution boundary mismatch")
    if manifest.get("program") != Path(__file__).name:
        raise ValueError("manifest program name mismatch")
    if manifest.get("program_sha256") != sha256_file(Path(__file__)):
        raise ValueError("manifest program hash does not match this verifier")
    if manifest.get("events_file") != "events.jsonl":
        raise ValueError("unexpected events path")
    if manifest.get("summary_file") != "summary.json":
        raise ValueError("unexpected summary path")
    if type(manifest.get("event_count")) is not int or manifest["event_count"] <= 0:
        raise ValueError("manifest event count must be a positive integer")
    config = PaperConfig.from_dict(manifest["configuration"])
    if config.digest != manifest["configuration_sha256"]:
        raise ValueError("configuration hash mismatch")
    if genesis_hash(config) != manifest["genesis_hash"]:
        raise ValueError("genesis hash mismatch")
    ledger_path = run_dir / "events.jsonl"
    if sha256_file(ledger_path) != manifest["events_sha256"]:
        raise ValueError("events file hash mismatch")
    ledger_bytes = ledger_path.read_bytes()
    if not ledger_bytes.endswith(b"\n") or b"\n\n" in ledger_bytes:
        raise ValueError("events file must contain complete nonempty lines")
    previous_hash = genesis_hash(config)
    events: list[dict[str, object]] = []
    referenced_raw: dict[str, str] = {}
    for expected_index, line in enumerate(ledger_bytes.splitlines()):
        event = strict_json_loads(line)
        if not isinstance(event, dict):
            raise ValueError("event is not an object")
        if set(event) != EVENT_FIELDS:
            raise ValueError("event fields do not match the protocol")
        if event.get("schema_version") != SCHEMA_VERSION:
            raise ValueError("event schema mismatch")
        if event.get("event_kind") != "PUBLIC_PAPER_ROUND":
            raise ValueError("event kind mismatch")
        if event.get("round_index") != expected_index:
            raise ValueError("round index mismatch")
        if event.get("configuration_sha256") != config.digest:
            raise ValueError("event configuration mismatch")
        if event.get("previous_event_hash") != previous_hash:
            raise ValueError("event predecessor mismatch")
        claimed_hash = event.get("event_hash")
        unhashed = dict(event)
        unhashed.pop("event_hash", None)
        if claimed_hash != sha256_bytes(canonical_json_bytes(unhashed)):
            raise ValueError("event hash mismatch")

        reconstructed: dict[str, CaptureReceipt] = {}
        if not isinstance(event.get("capture"), dict) or set(event["capture"]) != set(PAIR_ORDER):
            raise ValueError("event capture markets mismatch")
        for name in PAIR_ORDER:
            record = event["capture"][name]
            if not isinstance(record, dict) or set(record) != CAPTURE_FIELDS:
                raise ValueError(f"capture fields mismatch: {name}")
            if record.get("name") != name:
                raise ValueError(f"capture market name mismatch: {name}")
            if record.get("request_started_utc") != iso_from_unix_us(
                int(record["request_started_unix_us"])
            ):
                raise ValueError(f"capture start timestamp mismatch: {name}")
            if record.get("request_completed_utc") != iso_from_unix_us(
                int(record["request_completed_unix_us"])
            ):
                raise ValueError(f"capture completion timestamp mismatch: {name}")
            raw_file = record["raw_file"]
            raw = None
            if raw_file is not None:
                raw_relative = PurePosixPath(str(raw_file))
                raw_parts = raw_relative.parts
                if (
                    len(raw_parts) != 2
                    or raw_parts[0] != "raw"
                    or raw_relative.suffix != ".json"
                    or len(raw_relative.stem) != 64
                    or any(character not in "0123456789abcdef" for character in raw_relative.stem)
                ):
                    raise ValueError(f"invalid raw receipt path: {name}")
                raw_path = run_dir / Path(*raw_parts)
                raw = raw_path.read_bytes()
                if sha256_bytes(raw) != record["raw_sha256"]:
                    raise ValueError(f"raw receipt hash mismatch: {name}")
                if raw_relative.stem != record["raw_sha256"]:
                    raise ValueError(f"content-addressed filename mismatch: {name}")
                referenced_raw[str(raw_relative)] = str(record["raw_sha256"])
            elif record["raw_sha256"] is not None:
                raise ValueError(f"raw receipt reference missing: {name}")
            reconstructed[name] = receipt_from_record(record, raw)
        expected_recorded_us = max(
            receipt.request_completed_unix_us for receipt in reconstructed.values()
        )
        if event.get("recorded_unix_us") != expected_recorded_us:
            raise ValueError(f"event recorded timestamp mismatch: {expected_index}")
        if event.get("recorded_utc") != iso_from_unix_us(expected_recorded_us):
            raise ValueError(f"event recorded UTC mismatch: {expected_index}")
        derived = derive_round(reconstructed, config)
        for key in ("observation", "evaluations", "selected_paper_signal", "boundary"):
            if event.get(key) != derived[key]:
                raise ValueError(f"derived replay mismatch: {key} at round {expected_index}")
        previous_hash = str(claimed_hash)
        events.append(event)

    if len(events) != manifest["event_count"]:
        raise ValueError("event count mismatch")
    if previous_hash != manifest["final_event_hash"]:
        raise ValueError("final event hash mismatch")
    if manifest["first_recorded_utc"] != events[0]["recorded_utc"]:
        raise ValueError("first recorded timestamp mismatch")
    if manifest["last_recorded_utc"] != events[-1]["recorded_utc"]:
        raise ValueError("last recorded timestamp mismatch")
    summary_path = run_dir / "summary.json"
    if sha256_file(summary_path) != manifest["summary_sha256"]:
        raise ValueError("summary hash mismatch")
    recorded_summary = strict_json_loads(summary_path.read_bytes())
    if recorded_summary != summarize_events(events):
        raise ValueError("summary replay mismatch")
    if manifest.get("raw_files") != sorted(referenced_raw):
        raise ValueError("manifest raw file list mismatch")
    if manifest.get("raw_file_sha256") != referenced_raw:
        raise ValueError("manifest raw receipt map mismatch")
    actual_raw = sorted(
        path.relative_to(run_dir).as_posix()
        for path in (run_dir / "raw").glob("*")
        if path.is_file()
    )
    if actual_raw != sorted(referenced_raw):
        raise ValueError("run raw directory does not match referenced receipts")
    for relative, expected_hash in referenced_raw.items():
        if sha256_file(run_dir / relative) != expected_hash:
            raise ValueError(f"manifest raw hash mismatch: {relative}")
    return {
        "verified": True,
        "event_count": len(events),
        "configuration_sha256": config.digest,
        "final_event_hash": previous_hash,
        "events_sha256": manifest["events_sha256"],
        "summary": recorded_summary,
    }


def config_from_args(args: argparse.Namespace) -> PaperConfig:
    return PaperConfig(
        fee_bps_per_leg=args.fee_bps_per_leg,
        safety_bps=args.safety_bps,
        notionals_usd=tuple(args.notionals_usd),
        max_book_age_ms=args.max_book_age_ms,
        max_future_ms=args.max_future_ms,
        max_cross_book_skew_ms=args.max_cross_book_skew_ms,
        max_acquisition_span_ms=args.max_acquisition_span_ms,
        max_request_start_skew_ms=args.max_request_start_skew_ms,
        request_timeout_seconds=args.request_timeout_seconds,
        max_response_bytes=args.max_response_bytes,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    capture = subparsers.add_parser("capture", help="capture and evaluate public books")
    capture.add_argument("--output-dir", type=Path, required=True)
    capture.add_argument("--rounds", type=int, default=12)
    capture.add_argument("--interval-seconds", type=Decimal, default=Decimal("1"))
    capture.add_argument("--fee-bps-per-leg", type=Decimal, default=Decimal("25"))
    capture.add_argument("--safety-bps", type=Decimal, default=Decimal("5"))
    capture.add_argument(
        "--notionals-usd",
        type=Decimal,
        nargs="+",
        default=[Decimal("100"), Decimal("1000"), Decimal("10000")],
    )
    capture.add_argument("--max-book-age-ms", type=Decimal, default=Decimal("5000"))
    capture.add_argument("--max-future-ms", type=Decimal, default=Decimal("1000"))
    capture.add_argument("--max-cross-book-skew-ms", type=Decimal, default=Decimal("1500"))
    capture.add_argument("--max-acquisition-span-ms", type=Decimal, default=Decimal("2500"))
    capture.add_argument("--max-request-start-skew-ms", type=Decimal, default=Decimal("250"))
    capture.add_argument("--request-timeout-seconds", type=Decimal, default=Decimal("20"))
    capture.add_argument("--max-response-bytes", type=int, default=8 * 1024 * 1024)
    verify = subparsers.add_parser("verify", help="recompute a preserved run from raw bytes")
    verify.add_argument("--run-dir", type=Path, required=True)
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.command == "capture":
        manifest = capture_run(
            args.output_dir,
            rounds=args.rounds,
            interval_seconds=args.interval_seconds,
            config=config_from_args(args),
        )
        verification = verify_run(args.output_dir)
        print(
            json.dumps(
                {
                    "run_dir": str(args.output_dir),
                    "manifest": manifest,
                    "verification": verification,
                },
                indent=2,
                sort_keys=True,
            )
        )
    elif args.command == "verify":
        print(json.dumps(verify_run(args.run_dir), indent=2, sort_keys=True))
    else:
        raise AssertionError(args.command)


if __name__ == "__main__":
    main()
