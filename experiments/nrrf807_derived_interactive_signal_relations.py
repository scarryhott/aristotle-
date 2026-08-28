"""Derive trading signals as relations across independently captured interactions.

At stage ``t`` the NRRF805 local-ball natural form is already committed by the immutable event
hash.  Its first directed edge is the action and is evaluated only on the books at ``t``.  The
remaining inverse-potential path is evaluated on the separately captured books at ``t+1``.

The prior potential is the zero-hair full-route reading committed at ``t``.  Local hair is derived
from the fee translation of the split action/potential realization.  Global hair is then

    completed - (prior_potential - local_hair).

Under the separately checked later accounting identity this equals realized_potential minus prior
potential.  Consequently global-hair zero is now an empirical cross-stage relation, not a
single-stage identity.  The replay is counterfactual and submits no order.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
    from experiments import nrrf805_relativistic_signal_open_command as relative_run
    from experiments import nrrf806_translation_first_life_reactor as life_run
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot
    import nrrf805_relativistic_signal_open_command as relative_run
    import nrrf806_translation_first_life_reactor as life_run


SCHEMA_VERSION = "nrrf807.derived_interactive_signal_relations.v1"
RUN_KIND = "IMMUTABLE_DERIVED_INTERACTIVE_SIGNAL_RELATIONS"
EVENT_KIND = "ADJACENT_INTERACTION"
EQUATION = "global_hair = completed - (prior_potential - local_hair)"
INTERACTION = {
    "prior_commitment": "NRRF805 natural form fixed by source event hash at t",
    "action": "first route edge on books at t",
    "potential": "remaining reciprocal path on independently captured books at t+1",
    "executor": "local_accounting_zero and global_hair_zero",
    "lookahead_used_for_prior_selection": False,
    "orders_enabled": False,
}
TRANSLATION_STATE = {
    "interaction_grade": "ADJACENT_PUBLIC_BOOK_COUNTERFACTUAL",
    "authority_presentation": "UNPRESENTED",
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "settled_profit_claimed": False,
}
ZERO = Decimal(0)
ONE = Decimal(1)
PRECISION = relative_run.ARITHMETIC_PRECISION
TOLERANCE = relative_run.IDENTITY_TOLERANCE

SOURCE_BINDING_FIELDS = {
    "observation_manifest_sha256",
    "observation_events_sha256",
    "observation_final_event_hash",
    "relative_manifest_sha256",
    "relative_events_sha256",
    "relative_final_event_hash",
    "life_manifest_sha256",
    "life_events_sha256",
    "life_final_event_hash",
}
RECORD_FIELDS = {
    "route_id",
    "route_class_id",
    "potential_route_class_id",
    "start_asset",
    "start_amount",
    "action_source_round",
    "potential_source_round",
    "action_return",
    "potential_return",
    "prior_action_potential",
    "realized_zero_hair_potential",
    "local_hair",
    "completed",
    "local_accounting_residual",
    "global_hair",
    "interactive_signal_relation",
    "zero_hair_executor",
    "positive_completed_potential",
    "full_interaction_depth",
    "exchange_action",
}
COMMAND_FIELDS = {
    "state",
    "derived_interactive_relations",
    "closed_interactive_signals",
    "positive_completed_presentations",
    "authority_presentation",
    "missing_translations",
    "orders_submitted",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "interaction_index",
    "prior_round_index",
    "later_round_index",
    "prior_observation_event_hash",
    "later_observation_event_hash",
    "prior_relative_event_hash",
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
    "interaction",
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


def source_binding(observation_run: Path, relative_dir: Path, life_dir: Path) -> dict[str, object]:
    source_bot.verify_run(observation_run)
    relative_run.verify_overlay(observation_run, relative_dir)
    life_run.verify_overlay(observation_run, relative_dir, life_dir)
    observation_manifest = read_json_object(observation_run / "manifest.json")
    relative_manifest = read_json_object(relative_dir / "manifest.json")
    life_manifest = read_json_object(life_dir / "manifest.json")
    binding = {
        "observation_manifest_sha256": sha256_file(observation_run / "manifest.json"),
        "observation_events_sha256": observation_manifest["events_sha256"],
        "observation_final_event_hash": observation_manifest["final_event_hash"],
        "relative_manifest_sha256": sha256_file(relative_dir / "manifest.json"),
        "relative_events_sha256": relative_manifest["events_sha256"],
        "relative_final_event_hash": relative_manifest["final_event_hash"],
        "life_manifest_sha256": sha256_file(life_dir / "manifest.json"),
        "life_events_sha256": life_manifest["events_sha256"],
        "life_final_event_hash": life_manifest["final_event_hash"],
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def routes_for_event(
    event: Mapping[str, object], observation_run: Path, config: source_bot.PaperConfig
) -> dict[str, tuple[relative_run.DirectedEdge, ...]]:
    observation = event.get("observation")
    if not isinstance(observation, dict) or observation.get("state") != "IDENTIFIED_PUBLIC_BOOKS":
        return {}
    books = relative_run.books_from_event(event, observation_run, config)
    cycles = relative_run.enumerate_simple_cycles(relative_run.derive_edges(books))
    return {relative_run.route_id(route): route for route in cycles}


def evaluate_split(
    prior_route: Sequence[relative_run.DirectedEdge],
    later_route: Sequence[relative_run.DirectedEdge],
    start: Decimal,
    fee_rate: Decimal,
) -> tuple[Decimal, bool]:
    if len(prior_route) != len(later_route) or not prior_route:
        raise ValueError("interaction routes are incompatible")
    prior_curve = relative_run.EdgeCurve.derive(prior_route[0])
    current, full = relative_run.walk_edge(start, prior_curve, fee_rate)
    for edge in later_route[1:]:
        current, leg_full = relative_run.walk_edge(
            current, relative_run.EdgeCurve.derive(edge), fee_rate
        )
        full = full and leg_full
        if not leg_full:
            break
    return current, full


def derive_record(
    candidate: Mapping[str, object],
    prior_route: Sequence[relative_run.DirectedEdge],
    later_route: Sequence[relative_run.DirectedEdge],
    prior_round: int,
    later_round: int,
    fee_rate: Decimal,
) -> dict[str, object]:
    start = parse_decimal(candidate.get("start_amount"))
    prior_potential = parse_decimal(candidate.get("action_potential_return"))
    zero_final, zero_full = evaluate_split(prior_route, later_route, start, ZERO)
    cost_final, cost_full = evaluate_split(prior_route, later_route, start, fee_rate)
    full = zero_full and cost_full
    base = {
        "route_id": candidate.get("route_id"),
        "route_class_id": candidate.get("route_class_id"),
        "potential_route_class_id": candidate.get("reciprocal_route_class_id"),
        "start_asset": candidate.get("start_asset"),
        "start_amount": candidate.get("start_amount"),
        "action_source_round": prior_round,
        "potential_source_round": later_round,
        "action_return": "ballReturn",
        "potential_return": "hairReturn",
        "prior_action_potential": decimal_text(prior_potential),
        "full_interaction_depth": full,
        "exchange_action": "OPEN",
    }
    if not full:
        value = {
            **base,
            "realized_zero_hair_potential": None,
            "local_hair": None,
            "completed": None,
            "local_accounting_residual": None,
            "global_hair": None,
            "interactive_signal_relation": "OPEN_DEPTH",
            "zero_hair_executor": "OPEN",
            "positive_completed_potential": None,
        }
    else:
        with localcontext() as context:
            context.prec = PRECISION
            realized = zero_final / start - ONE
            local_hair = (zero_final - cost_final) / start
            completed = cost_final / start - ONE
            local_residual = completed - (realized - local_hair)
            global_hair = completed - (prior_potential - local_hair)
        local_closed = abs(local_residual) <= TOLERANCE
        signal_closed = abs(global_hair) <= TOLERANCE
        admitted = local_closed and signal_closed
        value = {
            **base,
            "realized_zero_hair_potential": decimal_text(realized),
            "local_hair": decimal_text(local_hair),
            "completed": decimal_text(completed),
            "local_accounting_residual": decimal_text(local_residual),
            "global_hair": decimal_text(global_hair),
            "interactive_signal_relation": "CLOSED" if signal_closed else "OPEN_CHANGED",
            "zero_hair_executor": "ADMIT_INTERACTION" if admitted else "HOLD_GLOBAL_HAIR",
            "positive_completed_potential": completed > ZERO,
        }
    if set(value) != RECORD_FIELDS:
        raise AssertionError("record schema drift")
    return value


def derive_command(records: Sequence[Mapping[str, object]]) -> dict[str, object]:
    numeric = [record for record in records if record["completed"] is not None]
    closed = sum(record["zero_hair_executor"] == "ADMIT_INTERACTION" for record in numeric)
    positive = sum(record["positive_completed_potential"] is True for record in numeric)
    missing = ["AUTHORITY_PRESENTATION"]
    if not numeric:
        missing.append("FULL_INTERACTION_DEPTH")
    if closed == 0:
        missing.append("GLOBAL_HAIR_ZERO")
    if positive == 0:
        missing.append("POSITIVE_COMPLETED_POTENTIAL")
    value = {
        "state": "OPEN",
        "derived_interactive_relations": len(numeric),
        "closed_interactive_signals": closed,
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
    with localcontext() as context:
        context.prec = PRECISION
        fee_rate = config.fee_bps_per_leg / relative_run.TEN_THOUSAND
    payloads: list[dict[str, object]] = []
    for index in range(len(observation_events) - 1):
        prior_observation = observation_events[index]
        later_observation = observation_events[index + 1]
        prior_relative = relative_events[index]
        if prior_relative.get("source_event_hash") != prior_observation.get("event_hash"):
            raise ValueError("prior relative event binding mismatch")
        prior_routes = routes_for_event(prior_observation, observation_run, config)
        later_routes = routes_for_event(later_observation, observation_run, config)
        candidates = prior_relative.get("candidates")
        if not isinstance(candidates, list):
            raise ValueError("prior candidates are not a list")
        records: list[dict[str, object]] = []
        for candidate in candidates:
            route_id = candidate.get("route_id")
            prior_route = prior_routes.get(route_id)
            later_route = later_routes.get(route_id)
            if prior_route is None or later_route is None:
                continue
            records.append(
                derive_record(candidate, prior_route, later_route, index, index + 1, fee_rate)
            )
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "interaction_index": index,
                "prior_round_index": index,
                "later_round_index": index + 1,
                "prior_observation_event_hash": prior_observation["event_hash"],
                "later_observation_event_hash": later_observation["event_hash"],
                "prior_relative_event_hash": prior_relative["event_hash"],
                "records": records,
                "command": derive_command(records),
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
                "interaction": INTERACTION,
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
    numeric = [record for record in records if record["completed"] is not None]
    local_residuals = [abs(parse_decimal(record["local_accounting_residual"])) for record in numeric]
    global_hairs = [abs(parse_decimal(record["global_hair"])) for record in numeric]
    best = max(numeric, key=lambda record: parse_decimal(record["completed"]), default=None)
    global_hair_zero_closures = sum(value <= TOLERANCE for value in global_hairs)
    return {
        "schema_version": SCHEMA_VERSION,
        "adjacent_interactions": len(events),
        "interactions_with_numeric_relations": sum(bool(event["records"]) for event in events),
        "derived_interactive_relations": len(numeric),
        "open_depth_relations": len(records) - len(numeric),
        "local_accounting_closures": sum(value <= TOLERANCE for value in local_residuals),
        "global_hair_zero_closures": global_hair_zero_closures,
        "global_hair_open_changes": len(global_hairs) - global_hair_zero_closures,
        "maximum_absolute_local_accounting_residual": decimal_text(max(local_residuals)) if local_residuals else None,
        "minimum_absolute_global_hair": decimal_text(min(global_hairs)) if global_hairs else None,
        "maximum_absolute_global_hair": decimal_text(max(global_hairs)) if global_hairs else None,
        "positive_completed_presentations": sum(
            record["positive_completed_potential"] is True for record in numeric
        ),
        "best_completed_return": best["completed"] if best is not None else None,
        "best_route_id": best["route_id"] if best is not None else None,
        "open_commands": sum(event["command"]["state"] == "OPEN" for event in events),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "settled_profit_claimed": False,
        "translation_state": TRANSLATION_STATE,
    }


def create_overlay(
    observation_run: Path, relative_dir: Path, life_dir: Path, output_dir: Path
) -> dict[str, object]:
    binding = source_binding(observation_run, relative_dir, life_dir)
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
        "interaction": INTERACTION,
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


def verify_overlay(
    observation_run: Path, relative_dir: Path, life_dir: Path, output_dir: Path
) -> dict[str, object]:
    binding = source_binding(observation_run, relative_dir, life_dir)
    manifest = read_json_object(output_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("manifest fields do not match protocol")
    identity = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "equation": EQUATION,
        "interaction": INTERACTION,
        "source_binding": binding,
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "translation_state": TRANSLATION_STATE,
    }
    for key, expected in identity.items():
        if manifest.get(key) != expected:
            raise ValueError(f"manifest {key} mismatch")
    events_path = output_dir / "events.jsonl"
    summary_path = output_dir / "summary.json"
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
    for name in ("create", "verify"):
        command = sub.add_parser(name)
        command.add_argument("observation_run", type=Path)
        command.add_argument("relative_dir", type=Path)
        command.add_argument("life_dir", type=Path)
        command.add_argument("output_dir", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "create":
        result = create_overlay(args.observation_run, args.relative_dir, args.life_dir, args.output_dir)
    else:
        result = verify_overlay(args.observation_run, args.relative_dir, args.life_dir, args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
