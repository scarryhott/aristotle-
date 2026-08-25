"""Deterministic historical realization of continual trading Closure.

This module consumes three caller-supplied hourly OHLCV files and produces a
hash-chained ledger containing every declared hourly stage.  The chain is
tamper-evident relative to its committed head; it is not externally immutable
because the manifest and whole chain could be reauthored.  The module
deliberately does not fetch quotes, submit orders, or treat candles as fills.

The three price relations are interpreted observationally as

    PLUS  : USD -> BTC -> ETH -> USD = E / (B * X)
    MINUS : USD -> ETH -> BTC -> USD = (B * X) / E

where B=BTC/USD, E=ETH/USD, and X=ETH/BTC.  Candidate returns, the neutral
paper return produced by HOLD, and authenticated settled P&L are separate
fields.  The last is always undefined because OHLCV contains no fill receipt.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from collections import Counter
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from typing import Iterable, Iterator


SCHEMA_VERSION = "nrrf766.continual_closure_trading.v1"
PROVIDER_BANNER = "https://www.CryptoDataDownload.com"
PAIR_ORDER = ("BTC_USD", "ETH_USD", "ETH_BTC")
EXPECTED_SYMBOLS = {
    "BTC_USD": "BTC/USD",
    "ETH_USD": "ETH/USD",
    "ETH_BTC": "ETH/BTC",
}
KNOWN_SNAPSHOT = {
    "BTC_USD": {
        "url": "https://www.cryptodatadownload.com/cdd/Bitstamp_BTCUSD_1h.csv",
        "sha256": "12d159598194aab1307909e29d92a1c5e3cbc41af4d567563dad559d2397fcbb",
        "rows": 72_343,
        "recorded_download_utc": "2026-08-24T10:41:41.981008Z",
    },
    "ETH_USD": {
        "url": "https://www.cryptodatadownload.com/cdd/Bitstamp_ETHUSD_1h.csv",
        "sha256": "ef35440148bee7fd1dcb3b436e4c56d8d3ca4672d65d9f9293e168d9c05d1f53",
        "rows": 72_363,
    },
    "ETH_BTC": {
        "url": "https://www.cryptodatadownload.com/cdd/Bitstamp_ETHBTC_1h.csv",
        "sha256": "ae33e5751ca4243d59bf3d04373f6f3e36b8cc3a44ff055f0f6bfbe0dd5aeea3",
        "rows": 72_363,
    },
}


LEDGER_FIELDS = (
    "stage_sequence",
    "stage_unix",
    "stage_utc",
    "declared_bar_end_utc",
    "declared_replay_decision_at_utc",
    "stage_state",
    "paper_decision",
    "witnesses",
    "btc_usd_close",
    "eth_usd_close",
    "eth_btc_close",
    "btc_usd_receipt_hash",
    "eth_usd_receipt_hash",
    "eth_btc_receipt_hash",
    "plus_orientation",
    "minus_orientation",
    "gross_plus_candidate_ratio",
    "gross_minus_candidate_ratio",
    "cost_factor_per_leg",
    "net_plus_candidate_ratio",
    "net_minus_candidate_ratio",
    "candidate_plus_pnl_bps",
    "candidate_minus_pnl_bps",
    "paper_plus_closed_ratio",
    "paper_minus_closed_ratio",
    "paper_plus_closed_pnl_bps",
    "paper_minus_closed_pnl_bps",
    "settled_plus_pnl_usd",
    "settled_minus_pnl_usd",
    "source_state_hash",
    "target_state_hash",
    "previous_event_hash",
    "event_hash",
)

STATE_PAYLOAD_FIELDS = tuple(
    field
    for field in LEDGER_FIELDS
    if field
    not in {
        "source_state_hash",
        "target_state_hash",
        "previous_event_hash",
        "event_hash",
    }
)


@dataclass(frozen=True)
class Bar:
    unix: int
    close: Decimal
    base_volume: Decimal
    quote_volume: Decimal
    receipt_hash: str
    structurally_valid: bool
    witnesses: tuple[str, ...]


@dataclass(frozen=True)
class PairDataset:
    name: str
    bars: dict[int, Bar]
    audit: dict[str, object]


@dataclass(frozen=True)
class PaperClosure:
    decision: str
    returned_ratio: Decimal
    returned_pnl_bps: Decimal
    witnesses: tuple[str, ...]


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sorted_witnesses(values: Iterable[str]) -> tuple[str, ...]:
    return tuple(sorted(set(values)))


def failure_close(action: PaperClosure, witnesses: Iterable[str]) -> PaperClosure:
    """Return neutral HOLD while monotonically retaining all evidence.

    Union and sorting make repeated application with the same evidence
    idempotent.  A failed candidate never becomes an admitted profit.
    """

    return replace(
        action,
        decision="HOLD",
        returned_ratio=Decimal(1),
        returned_pnl_bps=Decimal(0),
        witnesses=sorted_witnesses((*action.witnesses, *tuple(witnesses))),
    )


def decimal_text(value: Decimal | None) -> str:
    if value is None:
        return ""
    if value == 0:
        return "0"
    # Decimal.normalize obeys the ambient precision and can silently shorten a
    # high-precision quotient.  Fixed-point formatting retains every digit.
    text = format(value, "f")
    return text.rstrip("0").rstrip(".") if "." in text else text


def iso(unix: int) -> str:
    return datetime.fromtimestamp(unix, tz=timezone.utc).isoformat().replace("+00:00", "Z")


def parse_utc(text: str) -> int:
    normalized = text[:-1] + "+00:00" if text.endswith("Z") else text
    parsed = datetime.fromisoformat(normalized)
    if parsed.tzinfo is None:
        raise ValueError("UTC timestamp must include Z or an explicit offset")
    parsed = parsed.astimezone(timezone.utc)
    unix = int(parsed.timestamp())
    if parsed.minute or parsed.second or parsed.microsecond or unix % 3600:
        raise ValueError("stage boundary must be an exact UTC hour")
    return unix


def parse_decimal(text: str) -> Decimal:
    value = Decimal(text)
    if not value.is_finite():
        raise InvalidOperation(text)
    return value


def load_pair(name: str, path: Path) -> PairDataset:
    """Parse and structurally audit one provider file without repairing it."""

    raw = path.read_bytes()
    bars: dict[int, Bar] = {}
    duplicates: set[int] = set()
    parsed_rows = 0
    unaddressable_rows = 0
    invalid_rows = 0
    date_mismatches = 0
    symbol_mismatches = 0
    timestamps_in_file_order: list[int] = []

    with path.open(newline="") as source:
        banner = next(source).strip()
        reader = csv.DictReader(source)
        if reader.fieldnames is None:
            raise ValueError(f"missing header in {path}")
        required = {"unix", "date", "symbol", "open", "high", "low", "close"}
        missing_columns = sorted(required - set(reader.fieldnames))
        volume_columns = [field for field in reader.fieldnames if field.startswith("Volume ")]
        if missing_columns or len(volume_columns) != 2:
            raise ValueError(
                f"invalid schema in {path}: missing={missing_columns}, volumes={volume_columns}"
            )

        for row in reader:
            parsed_rows += 1
            try:
                unix = int(row["unix"])
            except (TypeError, ValueError):
                unaddressable_rows += 1
                invalid_rows += 1
                continue

            timestamps_in_file_order.append(unix)
            witnesses: list[str] = []
            if unix in bars:
                duplicates.add(unix)
                witnesses.append(f"DUPLICATE_{name}")

            try:
                open_, high, low, close = (
                    parse_decimal(row[field]) for field in ("open", "high", "low", "close")
                )
                base_volume, quote_volume = (
                    parse_decimal(row[field]) for field in volume_columns
                )
            except (InvalidOperation, TypeError):
                invalid_rows += 1
                witnesses.append(f"NONNUMERIC_{name}")
                open_ = high = low = close = Decimal(0)
                base_volume = quote_volume = Decimal(0)

            if not (
                open_ > 0
                and high > 0
                and low > 0
                and close > 0
                and low <= min(open_, close)
                and high >= max(open_, close)
                and base_volume >= 0
                and quote_volume >= 0
            ):
                witnesses.append(f"INVALID_OHLCV_{name}")

            symbol = (row.get("symbol") or "").strip()
            if symbol != EXPECTED_SYMBOLS[name]:
                symbol_mismatches += 1
                witnesses.append(f"SYMBOL_MISMATCH_{name}")

            date_text = (row.get("date") or "").strip()
            try:
                date_unix = int(
                    datetime.strptime(date_text, "%Y-%m-%d %H:%M:%S")
                    .replace(tzinfo=timezone.utc)
                    .timestamp()
                )
                if date_unix != unix:
                    date_mismatches += 1
                    witnesses.append(f"DATE_MISMATCH_{name}")
            except ValueError:
                date_mismatches += 1
                witnesses.append(f"DATE_PARSE_{name}")

            identity = "|".join((row[field] or "").strip() for field in reader.fieldnames)
            bar = Bar(
                unix=unix,
                close=close,
                base_volume=base_volume,
                quote_volume=quote_volume,
                receipt_hash=sha256_bytes(identity.encode()),
                structurally_valid=not witnesses,
                witnesses=sorted_witnesses(witnesses),
            )
            if unix not in bars:
                bars[unix] = bar

    for unix in duplicates:
        original = bars[unix]
        bars[unix] = replace(
            original,
            structurally_valid=False,
            witnesses=sorted_witnesses((*original.witnesses, f"DUPLICATE_{name}")),
        )

    ordered = sorted(bars)
    if not ordered:
        raise ValueError(f"no addressable rows in {path}")
    internal_missing_hours = 0
    off_hour_grid_intervals = 0
    for left, right in zip(ordered, ordered[1:]):
        delta = right - left
        if delta % 3600:
            off_hour_grid_intervals += 1
        elif delta > 3600:
            internal_missing_hours += delta // 3600 - 1

    sha = sha256_bytes(raw)
    known = KNOWN_SNAPSHOT[name]
    audit: dict[str, object] = {
        "file": path.name,
        "source_url": known["url"] if sha == known["sha256"] else None,
        "recorded_download_utc": known.get("recorded_download_utc")
        if sha == known["sha256"]
        else None,
        "sha256": sha,
        "provider_banner": banner,
        "known_snapshot_verified": sha == known["sha256"] and parsed_rows == known["rows"],
        "rows_parsed": parsed_rows,
        "unique_timestamp_rows": len(bars),
        "duplicate_timestamp_rows": len(duplicates),
        "unaddressable_rows": unaddressable_rows,
        "structurally_invalid_unique_rows": sum(not bar.structurally_valid for bar in bars.values()),
        "date_mismatches": date_mismatches,
        "symbol_mismatches": symbol_mismatches,
        "file_order_strictly_descending": all(
            later < earlier
            for earlier, later in zip(timestamps_in_file_order, timestamps_in_file_order[1:])
        ),
        "internal_missing_hours": internal_missing_hours,
        "off_hour_grid_intervals": off_hour_grid_intervals,
        "first_timestamp_utc": iso(ordered[0]),
        "last_timestamp_utc": iso(ordered[-1]),
    }
    return PairDataset(name=name, bars=bars, audit=audit)


def stage_witnesses(
    datasets: dict[str, PairDataset], unix: int, provisional_tail_unix: int
) -> tuple[str, tuple[str, ...]]:
    if unix == provisional_tail_unix:
        return "PENDING_UNFINALIZED", (
            "AWAIT_FINALIZATION",
            "UNFINALIZED_PROVIDER_TAIL",
        )

    witnesses: list[str] = []
    bars = {name: datasets[name].bars.get(unix) for name in PAIR_ORDER}
    for name, bar in bars.items():
        if bar is None:
            witnesses.append(f"MISSING_{name}")
        elif not bar.structurally_valid:
            witnesses.extend(bar.witnesses or (f"INVALID_{name}",))

    if any(bar is None for bar in bars.values()):
        witnesses.append("DATA_GAP")
        return "OPEN_MISSING", sorted_witnesses(witnesses)
    if any(not bar.structurally_valid for bar in bars.values() if bar is not None):
        witnesses.append("INVALID_STRUCTURAL_DATA")
        return "INVALID_STRUCTURAL", sorted_witnesses(witnesses)

    for name, bar in bars.items():
        assert bar is not None
        if bar.base_volume <= 0 or bar.quote_volume <= 0:
            witnesses.append(f"ZERO_ACTIVITY_{name}")
    if witnesses:
        witnesses.append("INACTIVE_MARKET")
        return "INACTIVE", sorted_witnesses(witnesses)
    return "IDENTIFIED_ACTIVE", ()


def stage_rows(
    datasets: dict[str, PairDataset],
    start_unix: int,
    end_unix: int,
    provisional_tail_unix: int,
    cost_bps_per_leg: Decimal,
) -> Iterator[dict[str, str]]:
    cost_per_leg = Decimal(1) - cost_bps_per_leg / Decimal(10_000)
    if not Decimal(0) < cost_per_leg <= Decimal(1):
        raise ValueError("per-leg cost must be in [0, 10000) basis points")
    cost_factor = cost_per_leg**3

    for sequence, unix in enumerate(range(start_unix, end_unix + 1, 3600)):
        state, structural_witnesses = stage_witnesses(datasets, unix, provisional_tail_unix)
        bars = {name: datasets[name].bars.get(unix) for name in PAIR_ORDER}
        active = state == "IDENTIFIED_ACTIVE"

        gross_plus = gross_minus = net_plus = net_minus = None
        plus_pnl = minus_pnl = None
        if active:
            btc = bars["BTC_USD"]
            eth = bars["ETH_USD"]
            cross = bars["ETH_BTC"]
            assert btc is not None and eth is not None and cross is not None
            with localcontext() as context:
                context.prec = 80
                gross_plus = eth.close / (btc.close * cross.close)
                # Compute each orientation from its stated path equation.  The
                # product check below is equation consistency over shared
                # inputs, not independent market evidence.
                gross_minus = (btc.close * cross.close) / eth.close
                net_plus = gross_plus * cost_factor
                net_minus = gross_minus * cost_factor
                plus_pnl = (net_plus - 1) * Decimal(10_000)
                minus_pnl = (net_minus - 1) * Decimal(10_000)

        base_action = PaperClosure("UNSET", Decimal(1), Decimal(0), structural_witnesses)
        paper_action = failure_close(
            base_action,
            ("NO_AUTHENTICATED_FILL", "OHLCV_AGGREGATE_NOT_EXECUTABLE"),
        )
        declared_bar_end = "" if state == "PENDING_UNFINALIZED" else iso(unix + 3600)

        yield {
            "stage_sequence": str(sequence),
            "stage_unix": str(unix),
            "stage_utc": iso(unix),
            "declared_bar_end_utc": declared_bar_end,
            "declared_replay_decision_at_utc": declared_bar_end,
            "stage_state": state,
            "paper_decision": paper_action.decision,
            "witnesses": ";".join(paper_action.witnesses),
            "btc_usd_close": decimal_text(bars["BTC_USD"].close if bars["BTC_USD"] else None),
            "eth_usd_close": decimal_text(bars["ETH_USD"].close if bars["ETH_USD"] else None),
            "eth_btc_close": decimal_text(bars["ETH_BTC"].close if bars["ETH_BTC"] else None),
            "btc_usd_receipt_hash": bars["BTC_USD"].receipt_hash if bars["BTC_USD"] else "",
            "eth_usd_receipt_hash": bars["ETH_USD"].receipt_hash if bars["ETH_USD"] else "",
            "eth_btc_receipt_hash": bars["ETH_BTC"].receipt_hash if bars["ETH_BTC"] else "",
            "plus_orientation": "USD->BTC->ETH->USD",
            "minus_orientation": "USD->ETH->BTC->USD",
            "gross_plus_candidate_ratio": decimal_text(gross_plus),
            "gross_minus_candidate_ratio": decimal_text(gross_minus),
            "cost_factor_per_leg": decimal_text(cost_per_leg),
            "net_plus_candidate_ratio": decimal_text(net_plus),
            "net_minus_candidate_ratio": decimal_text(net_minus),
            "candidate_plus_pnl_bps": decimal_text(plus_pnl),
            "candidate_minus_pnl_bps": decimal_text(minus_pnl),
            "paper_plus_closed_ratio": decimal_text(paper_action.returned_ratio),
            "paper_minus_closed_ratio": decimal_text(paper_action.returned_ratio),
            "paper_plus_closed_pnl_bps": decimal_text(paper_action.returned_pnl_bps),
            "paper_minus_closed_pnl_bps": decimal_text(paper_action.returned_pnl_bps),
            "settled_plus_pnl_usd": "",
            "settled_minus_pnl_usd": "",
        }


def target_state_hash(row: dict[str, str], source_state_hash: str) -> str:
    payload = {field: row[field] for field in STATE_PAYLOAD_FIELDS}
    payload["source_state_hash"] = source_state_hash
    return sha256_bytes(canonical_json_bytes(payload))


def event_hash(row: dict[str, str]) -> str:
    return sha256_bytes(canonical_json_bytes({field: row[field] for field in LEDGER_FIELDS[:-1]}))


def initial_hashes(manifest_sha256: str) -> tuple[str, str]:
    return (
        sha256_bytes(f"NRRF766_STATE_GENESIS:{manifest_sha256}".encode()),
        sha256_bytes(f"NRRF766_EVENT_GENESIS:{manifest_sha256}".encode()),
    )


def candidate_distribution(
    observations: list[tuple[int, Decimal, Decimal]], safety_bps: Decimal
) -> dict[str, object]:
    """Describe the full same-bar candidate distribution without selection."""

    if not observations:
        return {
            "defined": 0,
            "net_positive": 0,
            "net_zero": 0,
            "net_negative": 0,
            "clears_safety": 0,
            "minimum_net_candidate_pnl_bps": None,
            "median_net_candidate_pnl_bps": None,
            "maximum_net_candidate_pnl_bps": None,
            "net_positive_stages": [],
        }
    ordered = sorted(pnl for _, _, pnl in observations)
    middle = len(ordered) // 2
    median = (
        ordered[middle]
        if len(ordered) % 2
        else (ordered[middle - 1] + ordered[middle]) / Decimal(2)
    )
    positive = [(unix, ratio, pnl) for unix, ratio, pnl in observations if pnl > 0]
    return {
        "defined": len(observations),
        "net_positive": len(positive),
        "net_zero": sum(pnl == 0 for _, _, pnl in observations),
        "net_negative": sum(pnl < 0 for _, _, pnl in observations),
        "clears_safety": sum(pnl > safety_bps for _, _, pnl in observations),
        "minimum_net_candidate_pnl_bps": decimal_text(ordered[0]),
        "median_net_candidate_pnl_bps": decimal_text(median),
        "maximum_net_candidate_pnl_bps": decimal_text(ordered[-1]),
        "net_positive_stages": [
            {
                "stage_utc": iso(unix),
                "net_candidate_ratio": decimal_text(ratio),
                "net_candidate_pnl_bps": decimal_text(pnl),
                "clears_safety": pnl > safety_bps,
            }
            for unix, ratio, pnl in positive
        ],
    }


def verify_ledger(ledger_path: Path, manifest_path: Path) -> dict[str, object]:
    """Recompute continuity, adjacency, declared replay lag, and event hashes."""

    manifest_sha = sha256_file(manifest_path)
    expected_source, expected_previous = initial_hashes(manifest_sha)
    rows = 0
    previous_unix: int | None = None
    state_counts: Counter[str] = Counter()
    with ledger_path.open(newline="") as source:
        reader = csv.DictReader(source)
        if tuple(reader.fieldnames or ()) != LEDGER_FIELDS:
            raise ValueError("ledger schema differs from NRRF766 v1")
        for row in reader:
            if row["source_state_hash"] != expected_source:
                raise ValueError(f"state adjacency failed at row {rows}")
            if row["previous_event_hash"] != expected_previous:
                raise ValueError(f"event adjacency failed at row {rows}")
            if row["target_state_hash"] != target_state_hash(row, expected_source):
                raise ValueError(f"target state hash failed at row {rows}")
            if row["event_hash"] != event_hash(row):
                raise ValueError(f"event hash failed at row {rows}")

            unix = int(row["stage_unix"])
            if previous_unix is not None and unix != previous_unix + 3600:
                raise ValueError(f"hourly continuity failed at row {rows}")
            if row["declared_replay_decision_at_utc"]:
                if parse_utc(row["declared_replay_decision_at_utc"]) != unix + 3600:
                    raise ValueError(f"declared replay lag failed at row {rows}")
            elif row["stage_state"] != "PENDING_UNFINALIZED":
                raise ValueError(f"missing declared replay time outside provisional tail at row {rows}")

            expected_source = row["target_state_hash"]
            expected_previous = row["event_hash"]
            previous_unix = unix
            state_counts[row["stage_state"]] += 1
            rows += 1
    return {
        "rows": rows,
        "final_state_hash": expected_source,
        "final_event_hash": expected_previous,
        "state_counts": dict(sorted(state_counts.items())),
    }


def run(
    btc_usd: Path,
    eth_usd: Path,
    eth_btc: Path,
    output_dir: Path,
    *,
    start_utc: str | None = None,
    cost_bps_per_leg: Decimal = Decimal(25),
    safety_bps: Decimal = Decimal(5),
) -> dict[str, object]:
    """Materialize one deterministic observational run and return its summary."""

    if cost_bps_per_leg < 0 or cost_bps_per_leg >= 10_000 or safety_bps < 0:
        raise ValueError("cost must be in [0,10000) bps and safety must be nonnegative")
    paths = {"BTC_USD": btc_usd, "ETH_USD": eth_usd, "ETH_BTC": eth_btc}
    datasets = {name: load_pair(name, path) for name, path in paths.items()}
    first_unix = min(min(dataset.bars) for dataset in datasets.values())
    provisional_tail_unix = max(max(dataset.bars) for dataset in datasets.values())
    start_unix = parse_utc(start_utc) if start_utc else first_unix
    if start_unix < first_unix or start_unix > provisional_tail_unix:
        raise ValueError("start stage is outside the supplied observation interval")

    total_stages = (provisional_tail_unix - start_unix) // 3600 + 1
    manifest: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "method": "continual local Closure over observational reciprocal price relations",
        "test_kind": "SAME_BAR_RELATION_AUDIT_NOT_FORWARD_RETURN_PERFORMANCE",
        "execution_mode": "HISTORICAL_OBSERVATIONAL_ONLY",
        "orders_enabled": False,
        "authenticated_settlement_available": False,
        "forward_return_performance_test": False,
        "inputs": {name: datasets[name].audit for name in PAIR_ORDER},
        "configuration": {
            "start_stage_utc": iso(start_unix),
            "provisional_tail_stage_utc": iso(provisional_tail_unix),
            "declared_hourly_stages": total_stages,
            "declared_bar_lag_seconds": 3600,
            "declared_bar_lag_status": (
                "REPLAY_CONVENTION_NOT_VERIFIED_HISTORICAL_PUBLICATION_TIME"
            ),
            "cost_bps_per_leg": decimal_text(cost_bps_per_leg),
            "safety_bps": decimal_text(safety_bps),
            "plus_orientation": "USD->BTC->ETH->USD",
            "minus_orientation": "USD->ETH->BTC->USD",
        },
        "semantics": {
            "candidate_pnl": "same-stage OHLCV close relation after the declared multiplicative costs",
            "paper_closed_pnl": (
                "current-stage no-order HOLD is defined to return neutral ratio 1 and P&L 0"
            ),
            "settled_pnl": "undefined without authenticated fills",
            "provisional_tail": "latest provider row is conservatively pending",
            "missing_data": "returned as witnessed HOLD; never forward-filled",
            "hold_continuation": (
                "HOLD is an identity/no-order runtime return, not formal Interaction and not "
                "process halting"
            ),
            "declared_replay_time": (
                "bar label plus one hour; static CSV supplies no historical publication receipt"
            ),
            "witness_integrity": (
                "hash-chained and tamper-evident relative to the committed head; the manifest "
                "and entire chain can be reauthored"
            ),
        },
        "formal_boundary": {
            "runtime_hash_chain_only": True,
            "lean_BoundaryMatches_instantiated": False,
            "lean_LocalTradeWitness_instantiated": False,
            "ReceiptBridge_required": True,
            "statement": (
                "Runtime continuity is not a Lean proof or instantiation of BoundaryMatches "
                "or LocalTradeWitness; a ReceiptBridge remains required."
            ),
        },
        "ledger_fields": list(LEDGER_FIELDS),
    }

    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = output_dir / "manifest.json"
    ledger_path = output_dir / "stage_ledger.csv"
    summary_path = output_dir / "summary.json"
    write_json(manifest_path, manifest)
    manifest_sha = sha256_file(manifest_path)
    source_hash, previous_hash = initial_hashes(manifest_sha)

    state_counts: Counter[str] = Counter()
    witness_counts: Counter[str] = Counter()
    candidate_observations: dict[str, list[tuple[int, Decimal, Decimal]]] = {
        "PLUS": [],
        "MINUS": [],
    }
    reciprocal_equation_checks = 0
    cost_product_checks = 0
    expected_cost_product = (Decimal(1) - cost_bps_per_leg / Decimal(10_000)) ** 6

    with ledger_path.open("w", newline="") as target:
        writer = csv.DictWriter(target, fieldnames=LEDGER_FIELDS, lineterminator="\n")
        writer.writeheader()
        for row in stage_rows(
            datasets,
            start_unix,
            provisional_tail_unix,
            provisional_tail_unix,
            cost_bps_per_leg,
        ):
            row["source_state_hash"] = source_hash
            row["target_state_hash"] = target_state_hash(row, source_hash)
            row["previous_event_hash"] = previous_hash
            row["event_hash"] = event_hash(row)
            writer.writerow(row)

            state_counts[row["stage_state"]] += 1
            witness_counts.update(filter(None, row["witnesses"].split(";")))
            if row["gross_plus_candidate_ratio"]:
                gross_plus = Decimal(row["gross_plus_candidate_ratio"])
                gross_minus = Decimal(row["gross_minus_candidate_ratio"])
                net_plus = Decimal(row["net_plus_candidate_ratio"])
                net_minus = Decimal(row["net_minus_candidate_ratio"])
                plus_pnl = Decimal(row["candidate_plus_pnl_bps"])
                minus_pnl = Decimal(row["candidate_minus_pnl_bps"])
                unix = int(row["stage_unix"])
                candidate_observations["PLUS"].append((unix, net_plus, plus_pnl))
                candidate_observations["MINUS"].append((unix, net_minus, minus_pnl))
                with localcontext() as context:
                    context.prec = 110
                    if abs(gross_plus * gross_minus - 1) <= Decimal("1e-70"):
                        reciprocal_equation_checks += 1
                    if abs(net_plus * net_minus - expected_cost_product) <= Decimal("1e-70"):
                        cost_product_checks += 1
            source_hash = row["target_state_hash"]
            previous_hash = row["event_hash"]

    verification = verify_ledger(ledger_path, manifest_path)
    if verification["rows"] != total_stages:
        raise AssertionError("ledger did not return exactly once for every declared stage")
    distributions = {
        orientation: candidate_distribution(observations, safety_bps)
        for orientation, observations in candidate_observations.items()
    }
    summary: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "manifest_sha256": manifest_sha,
        "stage_ledger_sha256": sha256_file(ledger_path),
        "stages": {
            "declared": total_stages,
            "returned": verification["rows"],
            "state_counts": dict(sorted(state_counts.items())),
            "witness_counts": dict(sorted(witness_counts.items())),
        },
        "candidate_layer": {
            "observation_class": "OHLCV_CLOSE_COUNTERFACTUAL",
            "executable": False,
            "same_bar_relation_audit": True,
            "forward_return_performance_test": False,
            "orientation_distribution": distributions,
            "reciprocal_equation_consistency_checks": reciprocal_equation_checks,
            "reciprocal_check_is_independent_evidence": False,
            "cost_product_checks": cost_product_checks,
            "expected_net_pair_product": decimal_text(expected_cost_product),
        },
        "paper_closed_layer": {
            "decision": "HOLD",
            "orientations_returned": total_stages * 2,
            "minimum_returned_ratio": "1",
            "maximum_returned_ratio": "1",
            "aggregate_pnl_bps": "0",
            "reason": "OHLCV_AGGREGATE_NOT_EXECUTABLE",
            "pnl_semantics": "defined current-stage no-order HOLD, not measured performance",
            "hold_is_process_halting": False,
        },
        "authenticated_settled_layer": {
            "fill_receipts": 0,
            "settled_orientations": 0,
            "pnl_usd": None,
        },
        "continual_closure_checks": {
            "hourly_stage_continuity": verification["rows"],
            "source_target_adjacency": verification["rows"],
            "event_hash_chain": verification["rows"],
            "declared_bar_lag_or_pending": verification["rows"],
            "final_state_hash": verification["final_state_hash"],
            "final_event_hash": verification["final_event_hash"],
            "no_forward_fill": True,
            "tamper_evidence_scope": (
                "relative to committed head; manifest and full chain can be reauthored"
            ),
        },
        "formal_boundary": {
            "runtime_hash_chain_only": True,
            "lean_BoundaryMatches_instantiated": False,
            "lean_LocalTradeWitness_instantiated": False,
            "ReceiptBridge_required": True,
        },
        "limitations": [
            "This is a same-bar relation audit, not a forward-return or performance test.",
            "Candles are aggregated observations, not synchronized executable quotes.",
            "The one-hour replay lag is declared; CSV contains no historical publication receipts.",
            "No bid/ask spread, depth, latency, account fee tier, balances, or atomicity is observed.",
            "Positive candidates are not paper admissions and are never called settled profit.",
            "Paper P&L zero is defined by no-order HOLD; HOLD does not halt the process.",
            "Runtime hash continuity does not instantiate Lean BoundaryMatches or LocalTradeWitness.",
            "The latest provider row is conservatively pending rather than retrospectively finalized.",
        ],
    }
    write_json(summary_path, summary)
    return summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--btc-usd", required=True, type=Path)
    parser.add_argument("--eth-usd", required=True, type=Path)
    parser.add_argument("--eth-btc", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--start-utc")
    parser.add_argument("--cost-bps-per-leg", type=Decimal, default=Decimal(25))
    parser.add_argument("--safety-bps", type=Decimal, default=Decimal(5))
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    summary = run(
        args.btc_usd,
        args.eth_usd,
        args.eth_btc,
        args.output_dir,
        start_utc=args.start_utc,
        cost_bps_per_leg=args.cost_bps_per_leg,
        safety_bps=args.safety_bps,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
