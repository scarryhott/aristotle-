"""Run the life action/potential global-hair executor over locked public-book evidence.

The input is the immutable NRRF780 price/cost completion joined to the immutable NRRF801
black-mirror phase audit. For each route-size presentation:

    action potential = zero-fee local-price final USD - starting USD
    global hair      = zero-fee local-price final USD - cost-completed final USD
    completed net    = action potential - global hair

The paper executor emits ACT exactly when the life pair is mirror-coherent and action potential is
strictly greater than global hair. It never submits an exchange order; authenticated execution is
a separate interface.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
    from experiments import nrrf780_local_price_global_cost_equality as cost_overlay
    from experiments import nrrf801_black_mirror_market_phase as phase_overlay
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot
    import nrrf780_local_price_global_cost_equality as cost_overlay
    import nrrf801_black_mirror_market_phase as phase_overlay


SCHEMA_VERSION = "nrrf804.life_global_hair_executor.v1"
RUN_KIND = "IMMUTABLE_LIFE_GLOBAL_HAIR_PAPER_EXECUTOR"
EVENT_KIND = "LIFE_GLOBAL_HAIR_ROUND"
EQUATION = "completed_net_usd = action_potential_usd - global_hair_usd"
EXECUTOR = {
    "action_continuation": "NRRF800.ballReturn",
    "potential_continuation": "NRRF800.hairReturn",
    "life_closure": "NRRF801.blackMirror",
    "executor": "global_hair_usd < action_potential_usd",
    "live_exchange_execution": False,
}
PAPER_BOUNDARY = {
    "paper_executor_active": True,
    "live_action_selected": False,
    "execution_authorized": False,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "formal_receipt_admissions": 0,
    "authenticated_settled_pnl_usd": None,
    "settled_profit_claimed": False,
}
TOLERANCE = Decimal("1e-90")

SOURCE_BINDING_FIELDS = {
    "cost_manifest_sha256",
    "cost_events_sha256",
    "cost_final_event_hash",
    "phase_manifest_sha256",
    "phase_events_sha256",
    "phase_final_event_hash",
}
RECORD_FIELDS = {
    "start_usd",
    "orientation",
    "path",
    "life_phase_state",
    "action_return",
    "potential_return",
    "action_potential_usd",
    "global_hair_usd",
    "completed_net_usd",
    "source_completed_net_usd",
    "closure_identity_error_usd",
    "verdict",
    "reason",
    "live_order_authorized",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "cost_source_event_hash",
    "phase_source_event_hash",
    "records",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "executor",
    "equation",
    "source_binding",
    "genesis_hash",
    "event_count",
    "final_event_hash",
    "events_file",
    "events_sha256",
    "summary_file",
    "summary_sha256",
    "program",
    "program_sha256",
    "boundary",
}


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def decimal_text(value: Decimal) -> str:
    return format(value, "f")


def parse_decimal(value: object) -> Decimal:
    if not isinstance(value, str):
        raise ValueError("expected decimal string")
    return Decimal(value)


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def read_json_object(path: Path) -> dict[str, object]:
    value = source_bot.strict_json_loads(path.read_bytes())
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def read_events(path: Path) -> list[dict[str, object]]:
    raw = path.read_bytes()
    if not raw.endswith(b"\n") or b"\n\n" in raw:
        raise ValueError("events must be complete nonempty lines")
    events: list[dict[str, object]] = []
    for line in raw.splitlines():
        value = source_bot.strict_json_loads(line)
        if not isinstance(value, dict):
            raise ValueError("event is not an object")
        events.append(value)
    return events


def prepare_output_directory(root: Path) -> None:
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"refusing to overwrite nonempty run directory: {root}")
    root.mkdir(parents=True, exist_ok=True)


def source_binding(cost_dir: Path, phase_dir: Path, source_run: Path) -> dict[str, object]:
    cost_overlay.verify_overlay(cost_dir, source_run)
    phase_overlay.verify_overlay(cost_dir, source_run, phase_dir)
    cost_manifest = read_json_object(cost_dir / "manifest.json")
    phase_manifest = read_json_object(phase_dir / "manifest.json")
    binding = {
        "cost_manifest_sha256": sha256_file(cost_dir / "manifest.json"),
        "cost_events_sha256": cost_manifest["events_sha256"],
        "cost_final_event_hash": cost_manifest["final_event_hash"],
        "phase_manifest_sha256": sha256_file(phase_dir / "manifest.json"),
        "phase_events_sha256": phase_manifest["events_sha256"],
        "phase_final_event_hash": phase_manifest["final_event_hash"],
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def derive_record(
    completion: Mapping[str, object], phase_pair: Mapping[str, object]
) -> dict[str, object]:
    start_text = completion.get("start_usd")
    orientation = completion.get("orientation")
    path = completion.get("path")
    completion_state = completion.get("state")
    phase_state = phase_pair.get("state")
    if start_text != phase_pair.get("start_usd"):
        raise ValueError("cost/phase start-size mismatch")
    base = {
        "start_usd": start_text,
        "orientation": orientation,
        "path": path,
        "life_phase_state": phase_state,
        "action_return": "ballReturn",
        "potential_return": "hairReturn",
        "live_order_authorized": False,
    }
    if completion_state == "OPEN" or phase_state == "OPEN":
        record = {
            **base,
            "action_potential_usd": None,
            "global_hair_usd": None,
            "completed_net_usd": None,
            "source_completed_net_usd": None,
            "closure_identity_error_usd": None,
            "verdict": "OPEN",
            "reason": "LOCAL_OR_LIFE_PRESENTATION_OPEN",
        }
    else:
        with localcontext() as context:
            context.prec = 180
            start = parse_decimal(start_text)
            zero_fee_final = parse_decimal(completion.get("exit_local_price_zero_fee_final_usd"))
            completed_final = parse_decimal(completion.get("exit_cost_completed_final_usd"))
            action_potential = zero_fee_final - start
            global_hair = zero_fee_final - completed_final
            completed_net = action_potential - global_hair
            source_net = completed_final - start
            error = abs(completed_net - source_net)
        if global_hair < 0:
            raise ValueError("derived global hair is negative")
        if error > TOLERANCE:
            raise ValueError("global-hair closure identity failed")
        if phase_state != "MIRROR_COHERENT":
            verdict = "HOLD_LIFE_OPEN"
            reason = "ACTION_AND_INVERSE_POTENTIAL_DO_NOT_CLOSE"
        elif global_hair < action_potential:
            verdict = "ACT"
            reason = "ACTION_POTENTIAL_EXCEEDS_GLOBAL_HAIR"
        else:
            verdict = "HOLD_GLOBAL_HAIR"
            reason = "GLOBAL_HAIR_NOT_EXCEEDED"
        record = {
            **base,
            "action_potential_usd": decimal_text(action_potential),
            "global_hair_usd": decimal_text(global_hair),
            "completed_net_usd": decimal_text(completed_net),
            "source_completed_net_usd": decimal_text(source_net),
            "closure_identity_error_usd": decimal_text(error),
            "verdict": verdict,
            "reason": reason,
        }
    if set(record) != RECORD_FIELDS:
        raise AssertionError("record schema drift")
    return record


def derive_event_payloads(cost_dir: Path, phase_dir: Path) -> list[dict[str, object]]:
    cost_events = read_events(cost_dir / "events.jsonl")
    phase_events = read_events(phase_dir / "events.jsonl")
    if len(cost_events) != len(phase_events):
        raise ValueError("cost/phase round count mismatch")
    payloads: list[dict[str, object]] = []
    for expected_index, (cost_event, phase_event) in enumerate(zip(cost_events, phase_events)):
        if cost_event.get("round_index") != expected_index or phase_event.get("round_index") != expected_index:
            raise ValueError("source round sequence mismatch")
        completions = cost_event.get("completions")
        phase_pairs = phase_event.get("phase_pairs")
        if not isinstance(completions, list) or not isinstance(phase_pairs, list):
            raise ValueError("source records are not lists")
        pairs_by_size = {pair.get("start_usd"): pair for pair in phase_pairs}
        records = []
        for completion in completions:
            if not isinstance(completion, dict):
                raise ValueError("completion is not an object")
            pair = pairs_by_size.get(completion.get("start_usd"))
            if not isinstance(pair, dict):
                raise ValueError("completion has no phase pair")
            records.append(derive_record(completion, pair))
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "round_index": expected_index,
                "cost_source_event_hash": cost_event["event_hash"],
                "phase_source_event_hash": phase_event["event_hash"],
                "records": records,
                "boundary": PAPER_BOUNDARY,
            }
        )
    return payloads


def genesis_hash(binding: Mapping[str, object]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": "GENESIS",
                "source_binding": binding,
                "executor": EXECUTOR,
                "equation": EQUATION,
            }
        )
    )


def chain_events(payloads: Sequence[Mapping[str, object]], genesis: str) -> list[dict[str, object]]:
    events: list[dict[str, object]] = []
    previous = genesis
    for payload in payloads:
        event = dict(payload)
        event["previous_event_hash"] = previous
        event["event_hash"] = sha256_bytes(canonical_json_bytes(event))
        if set(event) != EVENT_FIELDS:
            raise AssertionError("event schema drift")
        events.append(event)
        previous = str(event["event_hash"])
    return events


def summarize(events: Sequence[Mapping[str, object]]) -> dict[str, object]:
    records = [record for event in events for record in event["records"]]
    verdicts = Counter(str(record["verdict"]) for record in records)
    numeric = [record for record in records if record["completed_net_usd"] is not None]
    acts = [record for record in records if record["verdict"] == "ACT"]
    errors = [parse_decimal(record["closure_identity_error_usd"]) for record in numeric]
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "records": len(records),
        "verdicts": dict(sorted(verdicts.items())),
        "paper_actions_selected": len(acts),
        "maximum_closure_identity_error_usd": decimal_text(max(errors)) if errors else None,
        "all_numeric_records_close": all(error <= TOLERANCE for error in errors),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "authenticated_settled_pnl_usd": None,
        "settled_profit_claimed": False,
        "boundary": PAPER_BOUNDARY,
    }


def create_overlay(cost_dir: Path, phase_dir: Path, source_run: Path, output_dir: Path) -> dict[str, object]:
    binding = source_binding(cost_dir, phase_dir, source_run)
    genesis = genesis_hash(binding)
    events = chain_events(derive_event_payloads(cost_dir, phase_dir), genesis)
    summary = summarize(events)
    prepare_output_directory(output_dir)
    events_path = output_dir / "events.jsonl"
    summary_path = output_dir / "summary.json"
    manifest_path = output_dir / "manifest.json"
    ledger = b"".join(canonical_json_bytes(event) + b"\n" for event in events)
    events_path.write_bytes(ledger)
    write_json(summary_path, summary)
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "executor": EXECUTOR,
        "equation": EQUATION,
        "source_binding": binding,
        "genesis_hash": genesis,
        "event_count": len(events),
        "final_event_hash": events[-1]["event_hash"] if events else genesis,
        "events_file": "events.jsonl",
        "events_sha256": sha256_bytes(ledger),
        "summary_file": "summary.json",
        "summary_sha256": sha256_file(summary_path),
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "boundary": PAPER_BOUNDARY,
    }
    if set(manifest) != MANIFEST_FIELDS:
        raise AssertionError("manifest schema drift")
    write_json(manifest_path, manifest)
    return {"created": True, "event_count": len(events), "summary": summary}


def verify_overlay(cost_dir: Path, phase_dir: Path, source_run: Path, overlay_dir: Path) -> dict[str, object]:
    binding = source_binding(cost_dir, phase_dir, source_run)
    manifest = read_json_object(overlay_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("manifest fields mismatch")
    if manifest["schema_version"] != SCHEMA_VERSION or manifest["run_kind"] != RUN_KIND:
        raise ValueError("manifest identity mismatch")
    if manifest["executor"] != EXECUTOR or manifest["equation"] != EQUATION:
        raise ValueError("executor declaration mismatch")
    if manifest["source_binding"] != binding or manifest["boundary"] != PAPER_BOUNDARY:
        raise ValueError("manifest binding or boundary mismatch")
    if manifest["program"] != Path(__file__).name or manifest["program_sha256"] != sha256_file(Path(__file__)):
        raise ValueError("program identity mismatch")
    events_path = overlay_dir / str(manifest["events_file"])
    summary_path = overlay_dir / str(manifest["summary_file"])
    if sha256_file(events_path) != manifest["events_sha256"] or sha256_file(summary_path) != manifest["summary_sha256"]:
        raise ValueError("artifact hash mismatch")
    expected = chain_events(derive_event_payloads(cost_dir, phase_dir), genesis_hash(binding))
    actual = read_events(events_path)
    if any(
        set(event) != EVENT_FIELDS
        or not isinstance(event.get("records"), list)
        or any(not isinstance(record, dict) or set(record) != RECORD_FIELDS for record in event["records"])
        for event in actual
    ):
        raise ValueError("event schema mismatch")
    if actual != expected:
        raise ValueError("semantic replay mismatch")
    summary = summarize(expected)
    if read_json_object(summary_path) != summary:
        raise ValueError("summary replay mismatch")
    final_hash = expected[-1]["event_hash"] if expected else genesis_hash(binding)
    if manifest["genesis_hash"] != genesis_hash(binding) or manifest["event_count"] != len(expected) or manifest["final_event_hash"] != final_hash:
        raise ValueError("hash-chain terminal mismatch")
    return {"verified": True, "event_count": len(expected), "summary": summary}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for name in ("build", "verify"):
        command = subparsers.add_parser(name)
        command.add_argument("--cost-overlay", required=True, type=Path)
        command.add_argument("--phase-overlay", required=True, type=Path)
        command.add_argument("--source-run", required=True, type=Path)
        command.add_argument("--output", required=True, type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "build":
        result = create_overlay(args.cost_overlay, args.phase_overlay, args.source_run, args.output)
    else:
        result = verify_overlay(args.cost_overlay, args.phase_overlay, args.source_run, args.output)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
