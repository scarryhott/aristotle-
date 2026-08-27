"""NRRF802 unified-closure interpretation of the locked NRRF801 phase audit.

The source phase audit is immutable. This overlay reads each opposite-orientation PLUS/MINUS pair
through the generic quotient `NRRF802.Closure NRRF801.blackMirror`.  The quotient's concrete
invariant is the oriented phase:

    right/PLUS  -> phase
    left/MINUS  -> -phase  (mod 4)

For an opposite-orientation pair, equality of these readings is exactly the already audited
black-mirror equation. The overlay checks that the generic closure preserves every source result;
it does not add a market return, fill missing phases, or turn the one-point *two-return life*
theorem into a market prediction.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
    from experiments import nrrf801_black_mirror_market_phase as phase_overlay
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot
    import nrrf801_black_mirror_market_phase as phase_overlay


SCHEMA_VERSION = "nrrf802.unified_closure_market_phase.v1"
RUN_KIND = "IMMUTABLE_UNIFIED_CLOSURE_MARKET_PHASE_OVERLAY"
EVENT_KIND = "UNIFIED_CLOSURE_PHASE_ROUND"
CLOSURE_INTERFACE = {
    "construction": "NRRF802.Closure NRRF801.blackMirror",
    "closure_map": "NRRF802.cl NRRF801.blackMirror",
    "factored_reading": "NRRFTradingBlackMirror.PhaseReading.orientedPhase",
    "pair_condition": "opposite orientation and equal oriented phase",
    "two_return_life_collapse_assumed_for_market": False,
}
NO_EXECUTION_BOUNDARY = phase_overlay.NO_EXECUTION_BOUNDARY

MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "closure_interface",
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
SOURCE_BINDING_FIELDS = {
    "schema_version",
    "run_kind",
    "event_count",
    "final_event_hash",
    "events_sha256",
    "summary_sha256",
    "program",
    "program_sha256",
    "manifest_sha256",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "source_event_hash",
    "closure_pairs",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
PAIR_FIELDS = {
    "start_usd",
    "source_state",
    "state",
    "plus_phase",
    "minus_phase",
    "actual_closure_reading",
    "potential_closure_reading",
    "source_state_preserved",
    "boundary",
}


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def read_json_object(path: Path) -> dict[str, object]:
    value = source_bot.strict_json_loads(path.read_bytes())
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def read_events(path: Path) -> list[dict[str, object]]:
    ledger = path.read_bytes()
    if not ledger.endswith(b"\n") or b"\n\n" in ledger:
        raise ValueError("events must be complete nonempty lines")
    events: list[dict[str, object]] = []
    for line in ledger.splitlines():
        value = source_bot.strict_json_loads(line)
        if not isinstance(value, dict):
            raise ValueError("event is not an object")
        events.append(value)
    return events


def prepare_output_directory(root: Path) -> None:
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"refusing to overwrite nonempty run directory: {root}")
    root.mkdir(parents=True, exist_ok=True)


def source_binding(
    source_phase_overlay: Path,
    source_price_overlay: Path,
    source_run: Path,
) -> dict[str, object]:
    phase_overlay.verify_overlay(source_price_overlay, source_run, source_phase_overlay)
    manifest = read_json_object(source_phase_overlay / "manifest.json")
    binding = {
        "schema_version": manifest["schema_version"],
        "run_kind": manifest["run_kind"],
        "event_count": manifest["event_count"],
        "final_event_hash": manifest["final_event_hash"],
        "events_sha256": manifest["events_sha256"],
        "summary_sha256": manifest["summary_sha256"],
        "program": manifest["program"],
        "program_sha256": manifest["program_sha256"],
        "manifest_sha256": sha256_file(source_phase_overlay / "manifest.json"),
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def closure_pair(source_pair: Mapping[str, object]) -> dict[str, object]:
    source_state = source_pair.get("state")
    plus_phase = source_pair.get("plus_phase")
    minus_phase = source_pair.get("minus_phase")
    if source_state == "OPEN":
        if plus_phase is not None or minus_phase is not None:
            raise ValueError("OPEN source pair contains a phase")
        state = "OPEN"
        actual_reading = None
        potential_reading = None
        expected_source = "OPEN"
    else:
        if not isinstance(plus_phase, int) or not isinstance(minus_phase, int):
            raise ValueError("closed source pair has no integer phases")
        actual_reading = plus_phase % 4
        potential_reading = (-minus_phase) % 4
        state = "SAME_CLOSURE" if actual_reading == potential_reading else "DISTINCT_CLOSURE"
        expected_source = "MIRROR_COHERENT" if state == "SAME_CLOSURE" else "CONTRADICTED"
    preserved = source_state == expected_source
    if not preserved:
        raise ValueError("generic closure changed the source black-mirror result")
    record = {
        "start_usd": source_pair.get("start_usd"),
        "source_state": source_state,
        "state": state,
        "plus_phase": plus_phase,
        "minus_phase": minus_phase,
        "actual_closure_reading": actual_reading,
        "potential_closure_reading": potential_reading,
        "source_state_preserved": preserved,
        "boundary": NO_EXECUTION_BOUNDARY,
    }
    if set(record) != PAIR_FIELDS:
        raise AssertionError("closure pair schema drift")
    return record


def derive_event_payloads(source_phase_overlay: Path) -> list[dict[str, object]]:
    payloads: list[dict[str, object]] = []
    for expected_index, source_event in enumerate(
        read_events(source_phase_overlay / "events.jsonl")
    ):
        if source_event.get("round_index") != expected_index:
            raise ValueError("source round sequence mismatch")
        source_pairs = source_event.get("phase_pairs")
        if not isinstance(source_pairs, list):
            raise ValueError("source phase pairs are not a list")
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "round_index": expected_index,
                "source_event_hash": source_event["event_hash"],
                "closure_pairs": [closure_pair(pair) for pair in source_pairs],
                "boundary": NO_EXECUTION_BOUNDARY,
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
                "closure_interface": CLOSURE_INTERFACE,
            }
        )
    )


def chain_events(
    payloads: Sequence[Mapping[str, object]], genesis: str
) -> list[dict[str, object]]:
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
    pairs = [pair for event in events for pair in event["closure_pairs"]]
    states = Counter(str(pair["state"]) for pair in pairs)
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "closure_pairs": len(pairs),
        "closure_states": dict(sorted(states.items())),
        "all_source_states_preserved": all(pair["source_state_preserved"] is True for pair in pairs),
        "reinterpretation_changed_pair_results": False,
        "two_return_life_collapse_admitted_for_market": False,
        "prediction_admitted": False,
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "formal_receipt_admissions": 0,
        "authenticated_settled_pnl_usd": None,
        "settled_profit_claimed": False,
        "boundary": NO_EXECUTION_BOUNDARY,
    }


def create_overlay(
    source_phase_overlay: Path,
    source_price_overlay: Path,
    source_run: Path,
    output_dir: Path,
) -> dict[str, object]:
    binding = source_binding(source_phase_overlay, source_price_overlay, source_run)
    events = chain_events(derive_event_payloads(source_phase_overlay), genesis_hash(binding))
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
        "closure_interface": CLOSURE_INTERFACE,
        "source_binding": binding,
        "genesis_hash": genesis_hash(binding),
        "event_count": len(events),
        "final_event_hash": events[-1]["event_hash"] if events else genesis_hash(binding),
        "events_file": "events.jsonl",
        "events_sha256": sha256_bytes(ledger),
        "summary_file": "summary.json",
        "summary_sha256": sha256_file(summary_path),
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "boundary": NO_EXECUTION_BOUNDARY,
    }
    if set(manifest) != MANIFEST_FIELDS:
        raise AssertionError("manifest schema drift")
    write_json(manifest_path, manifest)
    return {
        "created": True,
        "event_count": len(events),
        "manifest_sha256": sha256_file(manifest_path),
        "summary": summary,
    }


def verify_overlay(
    source_phase_overlay: Path,
    source_price_overlay: Path,
    source_run: Path,
    overlay_dir: Path,
) -> dict[str, object]:
    binding = source_binding(source_phase_overlay, source_price_overlay, source_run)
    manifest = read_json_object(overlay_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("overlay manifest fields mismatch")
    if manifest["schema_version"] != SCHEMA_VERSION or manifest["run_kind"] != RUN_KIND:
        raise ValueError("overlay manifest identity mismatch")
    if manifest["closure_interface"] != CLOSURE_INTERFACE:
        raise ValueError("overlay closure interface mismatch")
    if manifest["source_binding"] != binding:
        raise ValueError("overlay source binding mismatch")
    if manifest["program"] != Path(__file__).name:
        raise ValueError("overlay program name mismatch")
    if manifest["program_sha256"] != sha256_file(Path(__file__)):
        raise ValueError("overlay program hash mismatch")
    if manifest["boundary"] != NO_EXECUTION_BOUNDARY:
        raise ValueError("overlay boundary mismatch")

    events_path = overlay_dir / str(manifest["events_file"])
    summary_path = overlay_dir / str(manifest["summary_file"])
    if sha256_file(events_path) != manifest["events_sha256"]:
        raise ValueError("overlay event file hash mismatch")
    if sha256_file(summary_path) != manifest["summary_sha256"]:
        raise ValueError("overlay summary hash mismatch")
    expected = chain_events(derive_event_payloads(source_phase_overlay), genesis_hash(binding))
    actual = read_events(events_path)
    if any(
        set(event) != EVENT_FIELDS
        or not isinstance(event.get("closure_pairs"), list)
        or any(not isinstance(pair, dict) or set(pair) != PAIR_FIELDS for pair in event["closure_pairs"])
        for event in actual
    ):
        raise ValueError("overlay event schema mismatch")
    if actual != expected:
        raise ValueError("overlay semantic replay mismatch")
    expected_summary = summarize(expected)
    if read_json_object(summary_path) != expected_summary:
        raise ValueError("overlay summary replay mismatch")
    final_hash = expected[-1]["event_hash"] if expected else genesis_hash(binding)
    if manifest["genesis_hash"] != genesis_hash(binding):
        raise ValueError("overlay genesis mismatch")
    if manifest["event_count"] != len(expected) or manifest["final_event_hash"] != final_hash:
        raise ValueError("overlay chain terminal mismatch")
    return {
        "verified": True,
        "event_count": len(expected),
        "closure_pairs": expected_summary["closure_pairs"],
        "closure_states": expected_summary["closure_states"],
        "all_source_states_preserved": expected_summary["all_source_states_preserved"],
        "prediction_admitted": expected_summary["prediction_admitted"],
        "manifest_sha256": sha256_file(overlay_dir / "manifest.json"),
    }


def add_source_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--source-phase-overlay", required=True, type=Path)
    parser.add_argument("--source-price-overlay", required=True, type=Path)
    parser.add_argument("--source-run", required=True, type=Path)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build")
    add_source_arguments(build)
    build.add_argument("--output-dir", required=True, type=Path)
    verify = subparsers.add_parser("verify")
    add_source_arguments(verify)
    verify.add_argument("--overlay-dir", required=True, type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    sources = (args.source_phase_overlay, args.source_price_overlay, args.source_run)
    if args.command == "build":
        result = create_overlay(*sources, args.output_dir)
    else:
        result = verify_overlay(*sources, args.overlay_dir)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
