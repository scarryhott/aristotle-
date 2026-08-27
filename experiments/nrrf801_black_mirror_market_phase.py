"""NRRF801 black-mirror phase audit over the locked NRRF780 price overlay.

This adapter derives a discrete local phase from the zero-fee local price relation only:

    ratio > 1  -> phase 1
    ratio = 1  -> phase 0
    ratio < 1  -> phase 3 = -1 in ZMod 4

For each round and starting balance, the PLUS and MINUS presentations are black-mirror coherent
exactly when their derived phases are negatives modulo four.  Declared cost, completed return,
numeric P&L sign, and round index are not inputs to the phase derivation.

The audit does not assume that these observations exhibit NRRF801's full four-phase continuity.
It records OPEN and CONTRADICTED pairs, checks whether all four phases were actually observed, and
keeps prediction and execution disabled unless evidence establishes the missing conditions.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from decimal import Decimal
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
    from experiments import nrrf780_local_price_global_cost_equality as price_overlay
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot
    import nrrf780_local_price_global_cost_equality as price_overlay


SCHEMA_VERSION = "nrrf801.black_mirror_market_phase.v1"
RUN_KIND = "IMMUTABLE_BLACK_MIRROR_MARKET_PHASE_OVERLAY"
EVENT_KIND = "BLACK_MIRROR_PHASE_ROUND"
PHASE_RULE = {
    "source": "exit_local_price_ratio from the NRRF780 zero-fee local price presentation",
    "above_unit": 1,
    "at_unit": 0,
    "below_unit": 3,
    "modulus": 4,
    "excluded_inputs": [
        "exit_global_cost_equal_ratio",
        "exit_completed_ratio",
        "numeric_sign",
        "round_index",
    ],
}
NO_EXECUTION_BOUNDARY = {
    "action_selected": False,
    "execution_authorized": False,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "formal_receipt_admissions": 0,
    "settled_profit_claimed": False,
    "authenticated_settled_pnl_usd": None,
}

MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "phase_rule",
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
    "source_observation_state",
    "phase_pairs",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
PAIR_FIELDS = {
    "start_usd",
    "state",
    "plus_local_price_ratio",
    "minus_local_price_ratio",
    "plus_phase",
    "minus_phase",
    "expected_minus_phase",
    "phase_derived_from_local_price_only",
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
    events: list[dict[str, object]] = []
    ledger = path.read_bytes()
    if not ledger.endswith(b"\n") or b"\n\n" in ledger:
        raise ValueError("events must be complete nonempty lines")
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


def phase_from_local_ratio(value: object) -> int:
    ratio = price_overlay.parse_decimal(value)
    if ratio > Decimal(1):
        return 1
    if ratio < Decimal(1):
        return 3
    return 0


def source_binding(source_overlay: Path, source_run: Path) -> dict[str, object]:
    price_overlay.verify_overlay(source_overlay, source_run)
    manifest = read_json_object(source_overlay / "manifest.json")
    binding = {
        "schema_version": manifest["schema_version"],
        "run_kind": manifest["run_kind"],
        "event_count": manifest["event_count"],
        "final_event_hash": manifest["final_event_hash"],
        "events_sha256": manifest["events_sha256"],
        "summary_sha256": manifest["summary_sha256"],
        "program": manifest["program"],
        "program_sha256": manifest["program_sha256"],
        "manifest_sha256": sha256_file(source_overlay / "manifest.json"),
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def keyed_completions(event: Mapping[str, object]) -> dict[tuple[str, str], Mapping[str, object]]:
    completions = event.get("completions")
    if not isinstance(completions, list):
        raise ValueError("source completions are not a list")
    keyed: dict[tuple[str, str], Mapping[str, object]] = {}
    for item in completions:
        if not isinstance(item, dict):
            raise ValueError("source completion is not an object")
        orientation = item.get("orientation")
        start_usd = item.get("start_usd")
        if orientation not in {"PLUS", "MINUS"} or not isinstance(start_usd, str):
            raise ValueError("source completion key is invalid")
        key = str(orientation), start_usd
        if key in keyed:
            raise ValueError("duplicate source completion key")
        keyed[key] = item
    return keyed


def phase_pair(plus: Mapping[str, object], minus: Mapping[str, object]) -> dict[str, object]:
    if plus.get("start_usd") != minus.get("start_usd"):
        raise ValueError("phase pair start balance mismatch")
    start_usd = plus.get("start_usd")
    plus_ratio = plus.get("exit_local_price_ratio")
    minus_ratio = minus.get("exit_local_price_ratio")
    if plus_ratio is None or minus_ratio is None:
        record = {
            "start_usd": start_usd,
            "state": "OPEN",
            "plus_local_price_ratio": plus_ratio,
            "minus_local_price_ratio": minus_ratio,
            "plus_phase": None,
            "minus_phase": None,
            "expected_minus_phase": None,
            "phase_derived_from_local_price_only": True,
            "boundary": NO_EXECUTION_BOUNDARY,
        }
    else:
        plus_phase = phase_from_local_ratio(plus_ratio)
        minus_phase = phase_from_local_ratio(minus_ratio)
        expected_minus = (-plus_phase) % 4
        record = {
            "start_usd": start_usd,
            "state": "MIRROR_COHERENT" if minus_phase == expected_minus else "CONTRADICTED",
            "plus_local_price_ratio": plus_ratio,
            "minus_local_price_ratio": minus_ratio,
            "plus_phase": plus_phase,
            "minus_phase": minus_phase,
            "expected_minus_phase": expected_minus,
            "phase_derived_from_local_price_only": True,
            "boundary": NO_EXECUTION_BOUNDARY,
        }
    if set(record) != PAIR_FIELDS:
        raise AssertionError("phase pair schema drift")
    return record


def derive_event_payloads(source_overlay: Path) -> list[dict[str, object]]:
    payloads: list[dict[str, object]] = []
    for expected_index, source_event in enumerate(read_events(source_overlay / "events.jsonl")):
        if source_event.get("round_index") != expected_index:
            raise ValueError("source round sequence mismatch")
        keyed = keyed_completions(source_event)
        starts = sorted({start for _, start in keyed}, key=Decimal)
        pairs = [phase_pair(keyed[("PLUS", start)], keyed[("MINUS", start)]) for start in starts]
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "round_index": expected_index,
                "source_event_hash": source_event["event_hash"],
                "source_observation_state": source_event["source_observation_state"],
                "phase_pairs": pairs,
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
                "phase_rule": PHASE_RULE,
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
    pairs = [pair for event in events for pair in event["phase_pairs"]]
    states = Counter(str(pair["state"]) for pair in pairs)
    phases = sorted(
        {
            int(phase)
            for pair in pairs
            for phase in (pair["plus_phase"], pair["minus_phase"])
            if phase is not None
        }
    )
    full_ball_coverage = phases == [0, 1, 2, 3]
    all_pairs_closed = bool(pairs) and all(pair["state"] == "MIRROR_COHERENT" for pair in pairs)
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "phase_pairs": len(pairs),
        "pair_states": dict(sorted(states.items())),
        "observed_phase_values": phases,
        "full_ball_coverage": full_ball_coverage,
        "all_pairs_mirror_coherent": all_pairs_closed,
        "one_to_one_continuity_admitted": False,
        "one_to_one_continuity_reason": (
            "the audit observes paired phase values, not a total bijection Ball -> Ball commuting "
            "with ballStep"
        ),
        "prediction_admitted": False,
        "prediction_reason": (
            "NRRF801 phase closure is a tested interface condition; it does not itself predict a "
            "future local price or authorize a trade"
        ),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "formal_receipt_admissions": 0,
        "authenticated_settled_pnl_usd": None,
        "settled_profit_claimed": False,
        "boundary": NO_EXECUTION_BOUNDARY,
    }


def create_overlay(source_overlay: Path, source_run: Path, output_dir: Path) -> dict[str, object]:
    binding = source_binding(source_overlay, source_run)
    events = chain_events(derive_event_payloads(source_overlay), genesis_hash(binding))
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
        "phase_rule": PHASE_RULE,
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


def verify_overlay(source_overlay: Path, source_run: Path, overlay_dir: Path) -> dict[str, object]:
    binding = source_binding(source_overlay, source_run)
    manifest = read_json_object(overlay_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("overlay manifest fields mismatch")
    if manifest["schema_version"] != SCHEMA_VERSION or manifest["run_kind"] != RUN_KIND:
        raise ValueError("overlay manifest identity mismatch")
    if manifest["phase_rule"] != PHASE_RULE:
        raise ValueError("overlay phase rule mismatch")
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
    expected = chain_events(derive_event_payloads(source_overlay), genesis_hash(binding))
    actual = read_events(events_path)
    if any(
        set(event) != EVENT_FIELDS
        or not isinstance(event.get("phase_pairs"), list)
        or any(not isinstance(pair, dict) or set(pair) != PAIR_FIELDS for pair in event["phase_pairs"])
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
        "phase_pairs": expected_summary["phase_pairs"],
        "pair_states": expected_summary["pair_states"],
        "observed_phase_values": expected_summary["observed_phase_values"],
        "prediction_admitted": expected_summary["prediction_admitted"],
        "manifest_sha256": sha256_file(overlay_dir / "manifest.json"),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build")
    build.add_argument("--source-overlay", required=True, type=Path)
    build.add_argument("--source-run", required=True, type=Path)
    build.add_argument("--output-dir", required=True, type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("--source-overlay", required=True, type=Path)
    verify.add_argument("--source-run", required=True, type=Path)
    verify.add_argument("--overlay-dir", required=True, type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "build":
        result = create_overlay(args.source_overlay, args.source_run, args.output_dir)
    else:
        result = verify_overlay(args.source_overlay, args.source_run, args.overlay_dir)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
