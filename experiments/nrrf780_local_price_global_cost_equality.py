"""NRRF780 local-price / global-cost-equality realization.

This versioned overlay does not mutate the locked NRRF767 public-book run.
It verifies that run, replays each admitted public-book observation once with
the declared fees and once with zero fees, and reads the two results as:

    local price form      = zero-fee route return ratio
    global cost equality = local price form / cost-completed return ratio
    completed return     = local price form / global cost equality

Thus cost is the translation which globally equalizes a local price
presentation, not a scalar subtracted after the price.  The final equation is
algebraically equivalent to the already recorded cost-completed candidate, so
the overlay audits whether the reinterpretation changes any numeric sign.  It
does not select an order, authenticate a fill, settle P&L, or claim profit.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import replace
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot


SCHEMA_VERSION = "nrrf780.local_price_global_cost_equality.v1"
RUN_KIND = "IMMUTABLE_LOCAL_PRICE_GLOBAL_COST_EQUALITY_OVERLAY"
EVENT_KIND = "PRICE_COST_COMPLETION_ROUND"
COMPLETION_EQUATION = (
    "exit_completed_ratio = exit_local_price_ratio / exit_global_cost_equal_ratio"
)
INTERPRETATION = {
    "price": "local public-order-book route presentation before declared fees",
    "cost": "global equality translating that local presentation to its declared-fee completion",
    "comparison": "entry and exit are compared only after the same completion interface",
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
NUMERIC_TOLERANCE = Decimal("1e-70")

MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "interpretation",
    "completion_equation",
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
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "source_event_hash",
    "source_observation_state",
    "completions",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
COMPLETION_FIELDS = {
    "orientation",
    "path",
    "start_usd",
    "state",
    "source_witnesses",
    "entry_local_price_ratio",
    "entry_global_cost_equal_ratio",
    "entry_completed_ratio",
    "exit_local_price_zero_fee_final_usd",
    "exit_cost_completed_final_usd",
    "exit_local_price_ratio",
    "exit_global_cost_equal_ratio",
    "exit_completed_ratio",
    "completion_equation",
    "completion_identity_error",
    "source_candidate_return_bps",
    "completed_residual_bps",
    "numeric_sign",
    "numeric_sign_matches_source",
    "boundary",
}
SOURCE_BINDING_FIELDS = {
    "schema_version",
    "run_kind",
    "configuration_sha256",
    "genesis_hash",
    "event_count",
    "final_event_hash",
    "events_sha256",
    "summary_sha256",
    "program",
    "program_sha256",
    "manifest_sha256",
}


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def decimal_text(value: Decimal | None) -> str | None:
    return source_bot.decimal_text(value) if value is not None else None


def parse_decimal(value: object) -> Decimal:
    if not isinstance(value, str):
        raise ValueError("protocol decimal must be a string")
    return source_bot.parse_decimal(value)


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def prepare_output_directory(root: Path) -> None:
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"refusing to overwrite nonempty run directory: {root}")
    root.mkdir(parents=True, exist_ok=True)


def read_json_object(path: Path) -> dict[str, object]:
    value = source_bot.strict_json_loads(path.read_bytes())
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def read_source_events(source_run: Path) -> list[dict[str, object]]:
    events: list[dict[str, object]] = []
    for line in (source_run / "events.jsonl").read_bytes().splitlines():
        event = source_bot.strict_json_loads(line)
        if not isinstance(event, dict):
            raise ValueError("source event is not an object")
        events.append(event)
    return events


def source_binding(source_run: Path) -> tuple[dict[str, object], source_bot.PaperConfig]:
    verification = source_bot.verify_run(source_run)
    manifest = read_json_object(source_run / "manifest.json")
    binding = {
        "schema_version": manifest["schema_version"],
        "run_kind": manifest["run_kind"],
        "configuration_sha256": verification["configuration_sha256"],
        "genesis_hash": manifest["genesis_hash"],
        "event_count": verification["event_count"],
        "final_event_hash": verification["final_event_hash"],
        "events_sha256": verification["events_sha256"],
        "summary_sha256": manifest["summary_sha256"],
        "program": manifest["program"],
        "program_sha256": manifest["program_sha256"],
        "manifest_sha256": sha256_file(source_run / "manifest.json"),
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding, source_bot.PaperConfig.from_dict(manifest["configuration"])


def reconstruct_receipts(
    source_run: Path,
    event: Mapping[str, object],
) -> dict[str, source_bot.CaptureReceipt]:
    capture = event.get("capture")
    if not isinstance(capture, dict) or set(capture) != set(source_bot.PAIR_ORDER):
        raise ValueError("source capture markets mismatch")
    receipts: dict[str, source_bot.CaptureReceipt] = {}
    for name in source_bot.PAIR_ORDER:
        record = capture[name]
        if not isinstance(record, dict):
            raise ValueError("source capture record is not an object")
        raw_file = record.get("raw_file")
        raw = (source_run / str(raw_file)).read_bytes() if raw_file is not None else None
        receipts[name] = source_bot.receipt_from_record(record, raw)
    return receipts


def evaluation_key(evaluation: Mapping[str, object]) -> tuple[str, str]:
    orientation = evaluation.get("orientation")
    start_usd = evaluation.get("start_usd")
    if orientation not in {"PLUS", "MINUS"} or not isinstance(start_usd, str):
        raise ValueError("source evaluation key is invalid")
    return str(orientation), start_usd


def sign(value: Decimal) -> str:
    if value > 0:
        return "POSITIVE"
    if value < 0:
        return "NEGATIVE"
    return "ZERO"


def completion_record(
    source_evaluation: Mapping[str, object],
    zero_fee_evaluation: Mapping[str, object],
) -> dict[str, object]:
    if evaluation_key(source_evaluation) != evaluation_key(zero_fee_evaluation):
        raise ValueError("zero-fee replay changed the evaluation key")
    orientation, start_text = evaluation_key(source_evaluation)
    path = source_evaluation.get("path")
    if path != zero_fee_evaluation.get("path"):
        raise ValueError("zero-fee replay changed the route path")
    source_witnesses = source_evaluation.get("witnesses")
    if not isinstance(source_witnesses, list):
        raise ValueError("source witnesses are not a list")

    base: dict[str, object] = {
        "orientation": orientation,
        "path": path,
        "start_usd": start_text,
        "state": "OPEN",
        "source_witnesses": source_witnesses,
        "entry_local_price_ratio": "1",
        "entry_global_cost_equal_ratio": "1",
        "entry_completed_ratio": "1",
        "exit_local_price_zero_fee_final_usd": None,
        "exit_cost_completed_final_usd": None,
        "exit_local_price_ratio": None,
        "exit_global_cost_equal_ratio": None,
        "exit_completed_ratio": None,
        "completion_equation": COMPLETION_EQUATION,
        "completion_identity_error": None,
        "source_candidate_return_bps": source_evaluation.get("candidate_return_bps"),
        "completed_residual_bps": None,
        "numeric_sign": None,
        "numeric_sign_matches_source": None,
        "boundary": NO_EXECUTION_BOUNDARY,
    }
    source_final_text = source_evaluation.get("candidate_final_usd")
    zero_final_text = zero_fee_evaluation.get("candidate_final_usd")
    if source_final_text is None:
        if zero_final_text is not None:
            raise ValueError("OPEN source became numeric under zero-fee replay")
        if set(base) != COMPLETION_FIELDS:
            raise AssertionError("completion schema drift")
        return base
    if zero_final_text is None:
        raise ValueError("numeric source has no zero-fee local price realization")

    start = parse_decimal(start_text)
    source_final = parse_decimal(source_final_text)
    zero_final = parse_decimal(zero_final_text)
    source_bps = parse_decimal(source_evaluation.get("candidate_return_bps"))
    with localcontext() as context:
        context.prec = 110
        local_ratio = zero_final / start
        source_completed_ratio = source_final / start
        global_cost_equal = local_ratio / source_completed_ratio
        recompleted_ratio = local_ratio / global_cost_equal
        identity_error = abs(recompleted_ratio - source_completed_ratio)
        completed_residual_bps = (recompleted_ratio - Decimal(1)) * Decimal(10_000)
        source_ratio_from_bps = Decimal(1) + source_bps / Decimal(10_000)
    if global_cost_equal < 1:
        raise ValueError("declared nonnegative fees reduced the global cost equality below one")
    if identity_error > NUMERIC_TOLERANCE:
        raise ValueError("price/cost completion identity exceeded tolerance")
    if abs(source_ratio_from_bps - source_completed_ratio) > NUMERIC_TOLERANCE:
        raise ValueError("source return basis-points equation failed")
    if abs(completed_residual_bps - source_bps) > NUMERIC_TOLERANCE:
        raise ValueError("completed residual changed the source numeric result")

    base.update(
        {
            "state": "COMPLETED_COUNTERFACTUAL",
            "exit_local_price_zero_fee_final_usd": decimal_text(zero_final),
            "exit_cost_completed_final_usd": decimal_text(source_final),
            "exit_local_price_ratio": decimal_text(local_ratio),
            "exit_global_cost_equal_ratio": decimal_text(global_cost_equal),
            "exit_completed_ratio": decimal_text(recompleted_ratio),
            "completion_identity_error": decimal_text(identity_error),
            "completed_residual_bps": decimal_text(completed_residual_bps),
            "numeric_sign": sign(completed_residual_bps),
            "numeric_sign_matches_source": sign(completed_residual_bps) == sign(source_bps),
        }
    )
    if set(base) != COMPLETION_FIELDS:
        raise AssertionError("completion schema drift")
    return base


def derive_event_payloads(
    source_run: Path,
    source_config: source_bot.PaperConfig,
) -> list[dict[str, object]]:
    zero_fee_config = replace(source_config, fee_bps_per_leg=Decimal(0))
    payloads: list[dict[str, object]] = []
    for expected_index, source_event in enumerate(read_source_events(source_run)):
        if source_event.get("round_index") != expected_index:
            raise ValueError("source round sequence mismatch")
        receipts = reconstruct_receipts(source_run, source_event)
        zero_fee_round = source_bot.derive_round(receipts, zero_fee_config)
        zero_evaluations = {
            evaluation_key(item): item for item in zero_fee_round["evaluations"]
        }
        source_evaluations = source_event.get("evaluations")
        if not isinstance(source_evaluations, list):
            raise ValueError("source evaluations are not a list")
        completions = [
            completion_record(item, zero_evaluations[evaluation_key(item)])
            for item in source_evaluations
        ]
        payload: dict[str, object] = {
            "schema_version": SCHEMA_VERSION,
            "event_kind": EVENT_KIND,
            "round_index": expected_index,
            "source_event_hash": source_event["event_hash"],
            "source_observation_state": source_event["observation"]["state"],
            "completions": completions,
            "boundary": NO_EXECUTION_BOUNDARY,
        }
        payloads.append(payload)
    return payloads


def genesis_hash(binding: Mapping[str, object]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": "GENESIS",
                "source_binding": binding,
                "completion_equation": COMPLETION_EQUATION,
            }
        )
    )


def chain_events(
    payloads: Sequence[Mapping[str, object]],
    genesis: str,
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
        previous = event["event_hash"]
    return events


def summarize(events: Sequence[Mapping[str, object]]) -> dict[str, object]:
    completions = [item for event in events for item in event["completions"]]
    numeric = [item for item in completions if item["state"] == "COMPLETED_COUNTERFACTUAL"]
    states = Counter(str(item["state"]) for item in completions)
    signs = Counter(str(item["numeric_sign"]) for item in numeric)
    burdens = [parse_decimal(item["exit_global_cost_equal_ratio"]) for item in numeric]
    errors = [parse_decimal(item["completion_identity_error"]) for item in numeric]
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "completion_records": len(completions),
        "completion_states": dict(sorted(states.items())),
        "numeric_records": len(numeric),
        "numeric_signs": dict(sorted(signs.items())),
        "all_numeric_signs_match_source": all(
            item["numeric_sign_matches_source"] is True for item in numeric
        ),
        "reinterpretation_changed_numeric_results": False,
        "reason_numeric_results_unchanged": (
            "the refactor changes the factorization: completed = local_price / global_cost_equal; "
            "it is proved and replayed equal to the source cost-completed candidate"
        ),
        "minimum_global_cost_equal_ratio": decimal_text(min(burdens)) if burdens else None,
        "maximum_global_cost_equal_ratio": decimal_text(max(burdens)) if burdens else None,
        "maximum_completion_identity_error": decimal_text(max(errors)) if errors else None,
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "formal_receipt_admissions": 0,
        "authenticated_settled_pnl_usd": None,
        "settled_profit_claimed": False,
        "boundary": NO_EXECUTION_BOUNDARY,
    }


def create_overlay(source_run: Path, output_dir: Path) -> dict[str, object]:
    binding, source_config = source_binding(source_run)
    payloads = derive_event_payloads(source_run, source_config)
    genesis = genesis_hash(binding)
    events = chain_events(payloads, genesis)
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
        "interpretation": INTERPRETATION,
        "completion_equation": COMPLETION_EQUATION,
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


def verify_overlay(overlay_dir: Path, source_run: Path) -> dict[str, object]:
    binding, source_config = source_binding(source_run)
    manifest = read_json_object(overlay_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("overlay manifest fields mismatch")
    if manifest["schema_version"] != SCHEMA_VERSION or manifest["run_kind"] != RUN_KIND:
        raise ValueError("overlay manifest identity mismatch")
    if manifest["interpretation"] != INTERPRETATION:
        raise ValueError("overlay interpretation mismatch")
    if manifest["completion_equation"] != COMPLETION_EQUATION:
        raise ValueError("overlay completion equation mismatch")
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
    expected = chain_events(derive_event_payloads(source_run, source_config), genesis_hash(binding))
    actual: list[dict[str, object]] = []
    ledger = events_path.read_bytes()
    if not ledger.endswith(b"\n") or b"\n\n" in ledger:
        raise ValueError("overlay events must be complete nonempty lines")
    for line in ledger.splitlines():
        event = source_bot.strict_json_loads(line)
        if not isinstance(event, dict) or set(event) != EVENT_FIELDS:
            raise ValueError("overlay event schema mismatch")
        completions = event.get("completions")
        if not isinstance(completions, list) or any(
            not isinstance(item, dict) or set(item) != COMPLETION_FIELDS
            for item in completions
        ):
            raise ValueError("overlay completion schema mismatch")
        actual.append(event)
    if actual != expected:
        raise ValueError("overlay semantic replay mismatch")
    expected_summary = summarize(expected)
    if read_json_object(summary_path) != expected_summary:
        raise ValueError("overlay summary replay mismatch")
    if manifest["event_count"] != len(expected):
        raise ValueError("overlay event count mismatch")
    final_hash = expected[-1]["event_hash"] if expected else genesis_hash(binding)
    if manifest["genesis_hash"] != genesis_hash(binding):
        raise ValueError("overlay genesis mismatch")
    if manifest["final_event_hash"] != final_hash:
        raise ValueError("overlay final hash mismatch")
    return {
        "verified": True,
        "event_count": len(expected),
        "numeric_records": expected_summary["numeric_records"],
        "numeric_signs": expected_summary["numeric_signs"],
        "reinterpretation_changed_numeric_results": expected_summary[
            "reinterpretation_changed_numeric_results"
        ],
        "manifest_sha256": sha256_file(overlay_dir / "manifest.json"),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build")
    build.add_argument("--source-run", required=True, type=Path)
    build.add_argument("--output-dir", required=True, type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("--source-run", required=True, type=Path)
    verify.add_argument("--overlay-dir", required=True, type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.command == "build":
        result = create_overlay(args.source_run, args.output_dir)
    else:
        result = verify_overlay(args.overlay_dir, args.source_run)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
