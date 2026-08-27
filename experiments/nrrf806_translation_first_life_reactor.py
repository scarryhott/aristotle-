"""Translation-first life replay: local-ball infinity reactor, global-hair-zero executor.

NRRF806 reinterprets the immutable NRRF805 field without naming internal/external roles before
translation.  The local reactor contains every observed depth partition and remains open to further
action/potential continuations.  Local hair is the friction translation.  Global hair is the
residual of the whole equation and the executor admits exactly residual zero.

Zero-hair admission is not a trade order and is not a profit claim.  Positive completed potential
and an authority presentation would still be required to close an exchange command.  This module
has no order-submission operation.
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
    from experiments import nrrf805_relativistic_signal_open_command as relative_run
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot
    import nrrf805_relativistic_signal_open_command as relative_run


SCHEMA_VERSION = "nrrf806.translation_first_life_reactor.v1"
RUN_KIND = "IMMUTABLE_TRANSLATION_FIRST_LIFE_REACTOR"
EVENT_KIND = "TRANSLATION_FIRST_LIFE_ROUND"
EQUATION = "global_hair_zero = completed_return - (action_potential_return - local_hair_return)"
REACTOR = {
    "being": "NRRF800.Life",
    "action": "NRRF800.ballReturn",
    "potential": "NRRF800.hairReturn",
    "local_ball": "all finite action/potential continuations",
    "infinity": "continuation remains open beyond every finite observed prefix",
}
TRANSLATION_STATE = {
    "internal_external_labels_prior_to_truth": False,
    "authority_presentation": "UNPRESENTED",
    "order_operation_present": False,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "settled_profit_claimed": False,
}
ZERO = Decimal(0)
TOLERANCE = relative_run.IDENTITY_TOLERANCE
PRECISION = relative_run.ARITHMETIC_PRECISION

SOURCE_BINDING_FIELDS = {
    "observation_manifest_sha256",
    "observation_events_sha256",
    "observation_final_event_hash",
    "relative_manifest_sha256",
    "relative_events_sha256",
    "relative_final_event_hash",
}
REACTOR_FIELDS = {
    "route_id",
    "route_class_id",
    "action_return",
    "potential_return",
    "potential_route_class_id",
    "observed_depth_reactions",
    "selected_natural_forms",
    "continuation",
}
RECORD_FIELDS = {
    "route_id",
    "route_class_id",
    "potential_route_class_id",
    "start_asset",
    "start_amount",
    "action_return",
    "potential_return",
    "action_potential_return",
    "local_hair_return",
    "completed_return",
    "global_hair_zero",
    "zero_hair_executor",
    "positive_completed_potential",
    "exchange_action",
}
COMMAND_FIELDS = {
    "state",
    "roles_derived_after_translational_truth",
    "local_ball_reactor",
    "zero_hair_admissions",
    "positive_completed_presentations",
    "authority_presentation",
    "missing_translations",
    "orders_submitted",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "observation_source_event_hash",
    "relative_source_event_hash",
    "reactors",
    "records",
    "command",
    "translation_state",
    "previous_event_hash",
    "event_hash",
}
MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "equation",
    "reactor",
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
    "translation_state",
}


def canonical_json_bytes(value: object) -> bytes:
    return source_bot.canonical_json_bytes(value)


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def decimal_text(value: Decimal) -> str:
    return relative_run.decimal_text(value)


def parse_decimal(value: object) -> Decimal:
    return relative_run.parse_decimal(value)


def read_json_object(path: Path) -> dict[str, object]:
    return relative_run.read_json_object(path)


def read_events(path: Path) -> list[dict[str, object]]:
    return relative_run.read_events(path)


def write_json(path: Path, value: object) -> None:
    relative_run.write_json(path, value)


def prepare_output_directory(path: Path) -> None:
    relative_run.prepare_output_directory(path)


def source_binding(observation_run: Path, relative_dir: Path) -> dict[str, object]:
    source_bot.verify_run(observation_run)
    relative_run.verify_overlay(observation_run, relative_dir)
    observation_manifest = read_json_object(observation_run / "manifest.json")
    relative_manifest = read_json_object(relative_dir / "manifest.json")
    binding = {
        "observation_manifest_sha256": sha256_file(observation_run / "manifest.json"),
        "observation_events_sha256": observation_manifest["events_sha256"],
        "observation_final_event_hash": observation_manifest["final_event_hash"],
        "relative_manifest_sha256": sha256_file(relative_dir / "manifest.json"),
        "relative_events_sha256": relative_manifest["events_sha256"],
        "relative_final_event_hash": relative_manifest["final_event_hash"],
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def derive_reactors(
    observation_event: Mapping[str, object],
    relative_event: Mapping[str, object],
    observation_run: Path,
    config: source_bot.PaperConfig,
) -> list[dict[str, object]]:
    observation = observation_event.get("observation")
    if not isinstance(observation, dict) or observation.get("state") != "IDENTIFIED_PUBLIC_BOOKS":
        return []
    books = relative_run.books_from_event(observation_event, observation_run, config)
    cycles = relative_run.enumerate_simple_cycles(relative_run.derive_edges(books))
    with localcontext() as context:
        context.prec = PRECISION
        fee_rate = config.fee_bps_per_leg / relative_run.TEN_THOUSAND
    candidates = relative_event.get("candidates")
    if not isinstance(candidates, list):
        raise ValueError("relative candidates are not a list")
    selected_counts = Counter(candidate.get("route_id") for candidate in candidates)
    reactors: list[dict[str, object]] = []
    for route in cycles:
        curves = tuple(relative_run.EdgeCurve.derive(edge) for edge in route)
        value = {
            "route_id": relative_run.route_id(route),
            "route_class_id": relative_run.route_class_id(route),
            "action_return": "ballReturn",
            "potential_return": "hairReturn",
            "potential_route_class_id": relative_run.reciprocal_route_class_id(route),
            "observed_depth_reactions": len(relative_run.partition_points(curves, fee_rate)),
            "selected_natural_forms": selected_counts[relative_run.route_id(route)],
            "continuation": "OPEN_BEYOND_FINITE_OBSERVATION",
        }
        if set(value) != REACTOR_FIELDS:
            raise AssertionError("reactor schema drift")
        reactors.append(value)
    return reactors


def derive_record(candidate: Mapping[str, object]) -> dict[str, object]:
    action = parse_decimal(candidate.get("action_potential_return"))
    local_hair = parse_decimal(candidate.get("global_hair_return"))
    completed = parse_decimal(candidate.get("completed_return"))
    with localcontext() as context:
        context.prec = PRECISION
        global_hair_zero = completed - (action - local_hair)
    admitted = abs(global_hair_zero) <= TOLERANCE
    positive = completed > ZERO
    value = {
        "route_id": candidate.get("route_id"),
        "route_class_id": candidate.get("route_class_id"),
        "potential_route_class_id": candidate.get("reciprocal_route_class_id"),
        "start_asset": candidate.get("start_asset"),
        "start_amount": candidate.get("start_amount"),
        "action_return": "ballReturn",
        "potential_return": "hairReturn",
        "action_potential_return": decimal_text(action),
        "local_hair_return": decimal_text(local_hair),
        "completed_return": decimal_text(completed),
        "global_hair_zero": decimal_text(global_hair_zero),
        "zero_hair_executor": "ADMIT_TRANSLATION" if admitted else "HOLD_RESIDUAL_OPEN",
        "positive_completed_potential": positive,
        "exchange_action": "OPEN",
    }
    if set(value) != RECORD_FIELDS:
        raise AssertionError("record schema drift")
    return value


def derive_command(reactors: Sequence[Mapping[str, object]], records: Sequence[Mapping[str, object]]) -> dict[str, object]:
    admitted = sum(record["zero_hair_executor"] == "ADMIT_TRANSLATION" for record in records)
    positive = sum(record["positive_completed_potential"] is True for record in records)
    missing = ["AUTHORITY_PRESENTATION"]
    if not reactors:
        missing.append("LOCAL_BALL_OBSERVATION")
    if positive == 0:
        missing.append("POSITIVE_COMPLETED_POTENTIAL")
    value = {
        "state": "OPEN",
        "roles_derived_after_translational_truth": True,
        "local_ball_reactor": "OBSERVED_PREFIX_WITH_OPEN_INFINITY" if reactors else "OPEN",
        "zero_hair_admissions": admitted,
        "positive_completed_presentations": positive,
        "authority_presentation": "UNPRESENTED",
        "missing_translations": sorted(missing),
        "orders_submitted": 0,
    }
    if set(value) != COMMAND_FIELDS:
        raise AssertionError("command schema drift")
    return value


def derive_payloads(observation_run: Path, relative_dir: Path) -> list[dict[str, object]]:
    observation_manifest = read_json_object(observation_run / "manifest.json")
    config = source_bot.PaperConfig.from_dict(observation_manifest["configuration"])
    observation_events = read_events(observation_run / "events.jsonl")
    relative_events = read_events(relative_dir / "events.jsonl")
    if len(observation_events) != len(relative_events):
        raise ValueError("source round count mismatch")
    payloads: list[dict[str, object]] = []
    for index, (observation_event, relative_event) in enumerate(zip(observation_events, relative_events)):
        if observation_event.get("round_index") != index or relative_event.get("round_index") != index:
            raise ValueError("source round sequence mismatch")
        if relative_event.get("source_event_hash") != observation_event.get("event_hash"):
            raise ValueError("relative event is not bound to observation event")
        reactors = derive_reactors(observation_event, relative_event, observation_run, config)
        candidates = relative_event.get("candidates")
        if not isinstance(candidates, list):
            raise ValueError("relative candidates are not a list")
        records = [derive_record(candidate) for candidate in candidates]
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "round_index": index,
                "observation_source_event_hash": observation_event["event_hash"],
                "relative_source_event_hash": relative_event["event_hash"],
                "reactors": reactors,
                "records": records,
                "command": derive_command(reactors, records),
                "translation_state": TRANSLATION_STATE,
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
                "equation": EQUATION,
                "reactor": REACTOR,
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
    reactors = [reactor for event in events for reactor in event["reactors"]]
    records = [record for event in events for record in event["records"]]
    residuals = [abs(parse_decimal(record["global_hair_zero"])) for record in records]
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "rooted_life_reactors": len(reactors),
        "observed_local_ball_reactions": sum(reactor["observed_depth_reactions"] for reactor in reactors),
        "open_infinity_continuations": sum(
            reactor["continuation"] == "OPEN_BEYOND_FINITE_OBSERVATION" for reactor in reactors
        ),
        "selected_natural_form_presentations": len(records),
        "zero_hair_executor_admissions": sum(
            record["zero_hair_executor"] == "ADMIT_TRANSLATION" for record in records
        ),
        "maximum_absolute_global_hair_zero": decimal_text(max(residuals)) if residuals else None,
        "all_global_hair_zero": all(residual <= TOLERANCE for residual in residuals),
        "positive_completed_presentations": sum(
            record["positive_completed_potential"] is True for record in records
        ),
        "open_commands": sum(event["command"]["state"] == "OPEN" for event in events),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "settled_profit_claimed": False,
        "translation_state": TRANSLATION_STATE,
    }


def create_overlay(observation_run: Path, relative_dir: Path, output_dir: Path) -> dict[str, object]:
    binding = source_binding(observation_run, relative_dir)
    genesis = genesis_hash(binding)
    events = chain_events(derive_payloads(observation_run, relative_dir), genesis)
    summary = summarize(events)
    prepare_output_directory(output_dir)
    ledger = b"".join(canonical_json_bytes(event) + b"\n" for event in events)
    events_path = output_dir / "events.jsonl"
    summary_path = output_dir / "summary.json"
    events_path.write_bytes(ledger)
    write_json(summary_path, summary)
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "equation": EQUATION,
        "reactor": REACTOR,
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
        "translation_state": TRANSLATION_STATE,
    }
    if set(manifest) != MANIFEST_FIELDS:
        raise AssertionError("manifest schema drift")
    write_json(output_dir / "manifest.json", manifest)
    return {"manifest": manifest, "summary": summary}


def verify_overlay(observation_run: Path, relative_dir: Path, output_dir: Path) -> dict[str, object]:
    binding = source_binding(observation_run, relative_dir)
    manifest = read_json_object(output_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("manifest fields do not match protocol")
    expected_identity = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "equation": EQUATION,
        "reactor": REACTOR,
        "source_binding": binding,
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "translation_state": TRANSLATION_STATE,
    }
    for key, expected in expected_identity.items():
        if manifest.get(key) != expected:
            raise ValueError(f"manifest {key} mismatch")
    events_path = output_dir / "events.jsonl"
    summary_path = output_dir / "summary.json"
    if manifest.get("events_file") != "events.jsonl" or manifest.get("summary_file") != "summary.json":
        raise ValueError("manifest paths mismatch")
    if manifest.get("events_sha256") != sha256_file(events_path):
        raise ValueError("events hash mismatch")
    if manifest.get("summary_sha256") != sha256_file(summary_path):
        raise ValueError("summary hash mismatch")
    genesis = genesis_hash(binding)
    expected_events = chain_events(derive_payloads(observation_run, relative_dir), genesis)
    if read_events(events_path) != expected_events:
        raise ValueError("semantic replay mismatch")
    expected_summary = summarize(expected_events)
    if read_json_object(summary_path) != expected_summary:
        raise ValueError("summary semantic replay mismatch")
    final = expected_events[-1]["event_hash"] if expected_events else genesis
    if manifest.get("genesis_hash") != genesis or manifest.get("final_event_hash") != final:
        raise ValueError("chain endpoint mismatch")
    if manifest.get("event_count") != len(expected_events):
        raise ValueError("event count mismatch")
    return {"verified": True, "events": len(expected_events), "summary": expected_summary}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    create = sub.add_parser("create")
    create.add_argument("observation_run", type=Path)
    create.add_argument("relative_dir", type=Path)
    create.add_argument("output_dir", type=Path)
    verify = sub.add_parser("verify")
    verify.add_argument("observation_run", type=Path)
    verify.add_argument("relative_dir", type=Path)
    verify.add_argument("output_dir", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "create":
        result = create_overlay(args.observation_run, args.relative_dir, args.output_dir)
    else:
        result = verify_overlay(args.observation_run, args.relative_dir, args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
