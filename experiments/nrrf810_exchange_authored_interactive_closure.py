"""Run translational closure on exchange-authored public order interactions.

Bitstamp's live order channels attach ``event_id`` and ``pre_event_id`` to each order event.
Those links, rather than polling time or price movement, author the interaction path.  An order's
exchange identity and invariant side/subtype fields are its natural form.  Creation unfolds the
form, changes translate inside it, and deletion folds the same form back to the zero pole.

The capture is public and observation-only.  It has no credential or order operation, and price,
cost, and profit never select a form or decide closure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Mapping, Sequence


SCHEMA_VERSION = "nrrf810.exchange_authored_interactive_closure.v1"
RUN_KIND = "LIVE_EXCHANGE_AUTHORED_INTERACTIVE_CLOSURE"
WEBSOCKET_URL = "wss://ws.bitstamp.net"
API_DOCUMENTATION = "https://www.bitstamp.net/api/"
CHANNELS = (
    "live_orders_btcusd",
    "live_orders_ethusd",
    "live_orders_ethbtc",
)
ORDER_EVENTS = {"order_created", "order_changed", "order_deleted"}
FORM_FIELDS = ("channel", "order_id", "order_type", "order_subtype")


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def iso_from_unix_us(value: int) -> str:
    seconds, micros = divmod(value, 1_000_000)
    instant = datetime.fromtimestamp(seconds, tz=timezone.utc).replace(microsecond=micros)
    return instant.isoformat(timespec="microseconds").replace("+00:00", "Z")


def strict_json_loads(raw: str) -> object:
    def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key: {key}")
            result[key] = value
        return result

    return json.loads(raw, object_pairs_hook=unique_object)


def read_json(path: Path) -> dict[str, object]:
    value = strict_json_loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"{path} is not a JSON object")
    return value


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def encode_receipts(receipts: Sequence[Mapping[str, object]]) -> bytes:
    return b"".join(canonical_json_bytes(receipt) + b"\n" for receipt in receipts)


def decode_receipts(raw: bytes) -> list[dict[str, object]]:
    receipts: list[dict[str, object]] = []
    for line in raw.splitlines():
        value = strict_json_loads(line.decode())
        if not isinstance(value, dict):
            raise ValueError("raw receipt is not an object")
        recorded = value.get("recorded_unix_us")
        message = value.get("message")
        if type(recorded) is not int or not isinstance(message, str):
            raise ValueError("raw receipt schema is invalid")
        if set(value) != {"recorded_unix_us", "message"}:
            raise ValueError("raw receipt has unexpected fields")
        receipts.append(value)
    return receipts


def form_from_message(channel: str, data: Mapping[str, object]) -> dict[str, object]:
    raw_order_id = data.get("id_str", data.get("id"))
    if not isinstance(raw_order_id, (str, int)) or not str(raw_order_id):
        raise ValueError("order event lacks an order identity")
    order_type = data.get("order_type")
    order_subtype = data.get("order_subtype")
    if type(order_type) not in {int, float} or type(order_subtype) not in {int, float}:
        raise ValueError("order event lacks its relational type")
    if int(order_type) != order_type or int(order_subtype) != order_subtype:
        raise ValueError("order relational type must be integral")
    form = {
        "channel": channel,
        "order_id": str(raw_order_id),
        "order_type": int(order_type),
        "order_subtype": int(order_subtype),
    }
    if tuple(form) != FORM_FIELDS:
        raise AssertionError("natural-form schema drift")
    return form


def presentation_from_message(data: Mapping[str, object]) -> dict[str, object]:
    def text(name: str) -> str | None:
        value = data.get(name)
        return value if isinstance(value, str) else None

    return {
        "microtimestamp": text("microtimestamp"),
        "price": text("price_str"),
        "amount": text("amount_str"),
        "amount_traded": text("amount_traded"),
    }


def lifecycle_state(
    event: str,
    key: tuple[str, str],
    form: Mapping[str, object],
    event_id: str,
    active: dict[tuple[str, str], dict[str, object]],
) -> tuple[str, str | None]:
    current = active.get(key)
    if event == "order_created":
        if current is not None:
            return "CONTRADICTED_DUPLICATE_UNFOLD", None
        active[key] = {"form": dict(form), "open_event_id": event_id, "changes": 0}
        return "UNFOLD_TO_INF", None
    if event == "order_changed":
        if current is None:
            return "PARTIAL_PRIOR_UNFOLD", None
        if current["form"] != dict(form):
            return "CONTRADICTED_FORM_TRANSLATION", str(current["open_event_id"])
        current["changes"] = int(current["changes"]) + 1
        return "TRANSLATE_WITHIN_INF_FORM", str(current["open_event_id"])
    if current is None:
        return "PARTIAL_PRIOR_UNFOLD", None
    if current["form"] != dict(form):
        return "CONTRADICTED_RETURN_FORM", str(current["open_event_id"])
    active.pop(key)
    return "FOLD_RETURN_TO_ZERO", str(current["open_event_id"])


def analyze_receipts(
    receipts: Sequence[Mapping[str, object]], channels: Sequence[str] = CHANNELS
) -> tuple[list[dict[str, object]], dict[str, object]]:
    allowed_channels = set(channels)
    subscriptions: set[str] = set()
    previous_source_event: dict[str, str] = {}
    seen_source_events: set[tuple[str, str]] = set()
    active: dict[tuple[str, str], dict[str, object]] = {}
    counts: Counter[str] = Counter()
    per_channel: dict[str, Counter[str]] = {channel: Counter() for channel in channels}
    records: list[dict[str, object]] = []

    for receipt in receipts:
        recorded = receipt.get("recorded_unix_us")
        message = receipt.get("message")
        if type(recorded) is not int or not isinstance(message, str):
            raise ValueError("receipt schema is invalid")
        payload = strict_json_loads(message)
        if not isinstance(payload, dict):
            raise ValueError("WebSocket message is not an object")
        event = payload.get("event")
        channel = payload.get("channel")
        if event == "bts:subscription_succeeded" and channel in allowed_channels:
            subscriptions.add(str(channel))
            continue
        if event not in ORDER_EVENTS or channel not in allowed_channels:
            counts["ignored_messages"] += 1
            continue
        event_id = payload.get("event_id")
        pre_event_id = payload.get("pre_event_id")
        order_source = payload.get("order_source")
        data = payload.get("data")
        if (
            not isinstance(event_id, str)
            or not event_id
            or not isinstance(pre_event_id, str)
            or not pre_event_id
            or order_source != "orderbook"
            or not isinstance(data, dict)
        ):
            raise ValueError("source-authored event provenance is incomplete")
        source_key = (str(channel), event_id)
        duplicate = source_key in seen_source_events
        seen_source_events.add(source_key)
        prior = previous_source_event.get(str(channel))
        continuous = prior is None or pre_event_id == prior
        if duplicate:
            counts["duplicate_source_event_ids"] += 1
        if not continuous:
            counts["source_chain_gaps"] += 1
            for active_key in [key for key in active if key[0] == channel]:
                active.pop(active_key)
                counts["forms_opened_by_source_gap"] += 1
        previous_source_event[str(channel)] = event_id

        form = form_from_message(str(channel), data)
        form_hash = sha256_bytes(canonical_json_bytes(form))
        key = (str(channel), str(form["order_id"]))
        state, open_event_id = lifecycle_state(
            str(event), key, form, event_id, active
        )
        counts["exchange_authored_events"] += 1
        per_channel[str(channel)][str(event)] += 1
        if state == "UNFOLD_TO_INF":
            counts["natural_forms_unfolded"] += 1
        elif state == "TRANSLATE_WITHIN_INF_FORM":
            counts["inf_path_translations"] += 1
        elif state == "FOLD_RETURN_TO_ZERO":
            counts["natural_forms_closed"] += 1
            counts["zero_pole_returns"] += 1
        elif state.startswith("PARTIAL"):
            counts["partial_boundary_events"] += 1
        elif state.startswith("CONTRADICTED"):
            counts["contradicted_forms"] += 1

        records.append(
            {
                "schema_version": SCHEMA_VERSION,
                "interaction_index": len(records),
                "recorded_unix_us": recorded,
                "recorded_utc": iso_from_unix_us(recorded),
                "channel": channel,
                "source_event": event,
                "source_event_id": event_id,
                "source_pre_event_id": pre_event_id,
                "source_chain_continuous": continuous,
                "source_event_id_unique": not duplicate,
                "order_source": order_source,
                "natural_form": form,
                "natural_form_sha256": form_hash,
                "presentation": presentation_from_message(data),
                "translation": state,
                "unfold_event_id": open_event_id,
                "zero_hair": state == "FOLD_RETURN_TO_ZERO",
                "profit_assessment": None,
                "orders_submitted": 0,
            }
        )

    status = "OPEN_NO_CLOSED_FORM"
    if counts["contradicted_forms"]:
        status = "CONTRADICTED"
    elif counts["source_chain_gaps"] or counts["duplicate_source_event_ids"]:
        status = "OPEN_PROVENANCE"
    elif counts["natural_forms_closed"]:
        status = "CONTINUAL_CLOSURE_WITH_OPEN_BOUNDARY"

    first_recorded = receipts[0]["recorded_unix_us"] if receipts else None
    last_recorded = receipts[-1]["recorded_unix_us"] if receipts else None
    summary = {
        "schema_version": SCHEMA_VERSION,
        "status": status,
        "channels_requested": list(channels),
        "channels_subscribed": sorted(subscriptions),
        "raw_messages": len(receipts),
        "exchange_authored_events": counts["exchange_authored_events"],
        "per_channel": {channel: dict(per_channel[channel]) for channel in channels},
        "source_chain_gaps": counts["source_chain_gaps"],
        "duplicate_source_event_ids": counts["duplicate_source_event_ids"],
        "natural_forms_unfolded": counts["natural_forms_unfolded"],
        "inf_path_translations": counts["inf_path_translations"],
        "natural_forms_closed": counts["natural_forms_closed"],
        "zero_pole_returns": counts["zero_pole_returns"],
        "natural_forms_open_at_capture_boundary": len(active),
        "forms_opened_by_source_gap": counts["forms_opened_by_source_gap"],
        "partial_boundary_events": counts["partial_boundary_events"],
        "contradicted_forms": counts["contradicted_forms"],
        "first_recorded_utc": iso_from_unix_us(first_recorded) if first_recorded else None,
        "last_recorded_utc": iso_from_unix_us(last_recorded) if last_recorded else None,
        "form_selector": "EXCHANGE_AUTHORED_ORDER_IDENTITY_AND_RELATIONAL_TYPE",
        "price_authors_form": False,
        "profit_authors_form": False,
        "profit_assessments": 0,
        "orders_enabled": False,
        "orders_submitted": 0,
    }
    return records, summary


def chain_records(
    records: Iterable[Mapping[str, object]], genesis_hash: str
) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    previous = genesis_hash
    for item in records:
        record = dict(item)
        record["previous_record_hash"] = previous
        record["record_hash"] = sha256_bytes(canonical_json_bytes(record))
        result.append(record)
        previous = str(record["record_hash"])
    return result


def capture_receipts(
    duration_seconds: float,
    max_events: int,
    channels: Sequence[str] = CHANNELS,
) -> list[dict[str, object]]:
    if duration_seconds <= 0 or duration_seconds > 60:
        raise ValueError("duration_seconds must be in (0, 60]")
    if max_events <= 0:
        raise ValueError("max_events must be positive")
    from websockets.sync.client import connect

    receipts: list[dict[str, object]] = []
    order_events = 0
    deadline = time.monotonic() + duration_seconds
    with connect(WEBSOCKET_URL, open_timeout=10, close_timeout=3, ping_interval=20) as socket:
        for channel in channels:
            socket.send(
                json.dumps(
                    {"event": "bts:subscribe", "data": {"channel": channel}},
                    separators=(",", ":"),
                )
            )
        while time.monotonic() < deadline and order_events < max_events:
            try:
                message = socket.recv(timeout=min(2, max(0.1, deadline - time.monotonic())))
            except TimeoutError:
                continue
            if not isinstance(message, str):
                raise ValueError("binary WebSocket message is not admissible")
            receipts.append({"recorded_unix_us": time.time_ns() // 1_000, "message": message})
            parsed = strict_json_loads(message)
            if isinstance(parsed, dict) and parsed.get("event") in ORDER_EVENTS:
                order_events += 1
    return receipts


def create_run(
    output_dir: Path,
    *,
    duration_seconds: float = 20,
    max_events: int = 20_000,
    channels: Sequence[str] = CHANNELS,
) -> dict[str, object]:
    if output_dir.exists():
        raise FileExistsError(output_dir)
    receipts = capture_receipts(duration_seconds, max_events, channels)
    records, summary = analyze_receipts(receipts, channels)
    configuration = {
        "websocket_url": WEBSOCKET_URL,
        "channels": list(channels),
        "duration_seconds": duration_seconds,
        "max_events": max_events,
        "orders_enabled": False,
    }
    genesis_hash = sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "run_kind": RUN_KIND,
                "configuration": configuration,
            }
        )
    )
    chained = chain_records(records, genesis_hash)
    raw_bytes = encode_receipts(receipts)
    event_bytes = b"".join(canonical_json_bytes(record) + b"\n" for record in chained)
    output_dir.mkdir(parents=True)
    raw_path = output_dir / "raw_messages.jsonl"
    events_path = output_dir / "events.jsonl"
    summary_path = output_dir / "summary.json"
    raw_path.write_bytes(raw_bytes)
    events_path.write_bytes(event_bytes)
    write_json(summary_path, summary)
    program = Path(__file__).resolve()
    repository = program.parents[1]
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "source": {
            "venue": "Bitstamp",
            "websocket_url": WEBSOCKET_URL,
            "api_documentation": API_DOCUMENTATION,
            "interaction_authorship": "event_id/pre_event_id supplied by exchange stream",
        },
        "configuration": configuration,
        "genesis_hash": genesis_hash,
        "event_count": len(chained),
        "final_record_hash": chained[-1]["record_hash"] if chained else genesis_hash,
        "raw_messages_file": raw_path.name,
        "raw_messages_sha256": sha256_bytes(raw_bytes),
        "events_file": events_path.name,
        "events_sha256": sha256_bytes(event_bytes),
        "summary_file": summary_path.name,
        "summary_sha256": sha256_file(summary_path),
        "program": program.relative_to(repository).as_posix(),
        "program_sha256": sha256_file(program),
        "boundary": {
            "price_authors_form": False,
            "profit_authors_form": False,
            "profit_assessments": 0,
            "orders_enabled": False,
            "orders_submitted": 0,
            "authenticated_fills": 0,
            "settled_profit_claimed": False,
        },
    }
    write_json(output_dir / "manifest.json", manifest)
    return {"manifest": manifest, "summary": summary}


def verify_run(run_dir: Path) -> dict[str, object]:
    manifest = read_json(run_dir / "manifest.json")
    if manifest.get("schema_version") != SCHEMA_VERSION or manifest.get("run_kind") != RUN_KIND:
        raise ValueError("run identity mismatch")
    boundary = manifest.get("boundary")
    if not isinstance(boundary, dict) or boundary != {
        "price_authors_form": False,
        "profit_authors_form": False,
        "profit_assessments": 0,
        "orders_enabled": False,
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "settled_profit_claimed": False,
    }:
        raise ValueError("execution boundary mismatch")
    program = Path(__file__).resolve()
    if manifest.get("program_sha256") != sha256_file(program):
        raise ValueError("program hash mismatch")
    raw_path = run_dir / str(manifest["raw_messages_file"])
    events_path = run_dir / str(manifest["events_file"])
    summary_path = run_dir / str(manifest["summary_file"])
    if manifest.get("raw_messages_sha256") != sha256_file(raw_path):
        raise ValueError("raw message hash mismatch")
    if manifest.get("events_sha256") != sha256_file(events_path):
        raise ValueError("event ledger hash mismatch")
    if manifest.get("summary_sha256") != sha256_file(summary_path):
        raise ValueError("summary hash mismatch")
    receipts = decode_receipts(raw_path.read_bytes())
    configuration = manifest.get("configuration")
    if not isinstance(configuration, dict) or configuration.get("orders_enabled") is not False:
        raise ValueError("configuration boundary mismatch")
    channels = configuration.get("channels")
    if not isinstance(channels, list) or not all(isinstance(item, str) for item in channels):
        raise ValueError("channel configuration mismatch")
    records, summary = analyze_receipts(receipts, channels)
    expected_events = b"".join(
        canonical_json_bytes(record) + b"\n"
        for record in chain_records(records, str(manifest["genesis_hash"]))
    )
    if expected_events != events_path.read_bytes():
        raise ValueError("offline interaction replay mismatch")
    if summary != read_json(summary_path):
        raise ValueError("offline summary replay mismatch")
    if len(records) != manifest.get("event_count"):
        raise ValueError("event count mismatch")
    final_hash = (
        strict_json_loads(expected_events.splitlines()[-1].decode())["record_hash"]
        if expected_events
        else manifest["genesis_hash"]
    )
    if final_hash != manifest.get("final_record_hash"):
        raise ValueError("final record hash mismatch")
    return {"verified": True, "summary": summary}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    capture = commands.add_parser("capture")
    capture.add_argument("--output-dir", type=Path, required=True)
    capture.add_argument("--duration-seconds", type=float, default=20)
    capture.add_argument("--max-events", type=int, default=20_000)
    verify = commands.add_parser("verify")
    verify.add_argument("--run-dir", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "capture":
        result = create_run(
            args.output_dir,
            duration_seconds=args.duration_seconds,
            max_events=args.max_events,
        )
    else:
        result = verify_run(args.run_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
