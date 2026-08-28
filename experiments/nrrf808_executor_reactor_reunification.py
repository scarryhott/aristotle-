"""Reunify public trading data as reactor geometry before interaction authors a signal.

The public books present reciprocal local-price geometry.  They do not contain an authenticated
transaction by this system, so they do not author an action/potential turn and cannot determine a
trading natural form.  Global hair zero is recorded only as the universal executer reading; it is
never used as a score.  No route, depth, return, cost, or profit argmax occurs here.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
    from experiments import nrrf805_relativistic_signal_open_command as relative_run
    from experiments import nrrf806_translation_first_life_reactor as life_run
    from experiments import nrrf807_derived_interactive_signal_relations as interactive_run
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot
    import nrrf805_relativistic_signal_open_command as relative_run
    import nrrf806_translation_first_life_reactor as life_run
    import nrrf807_derived_interactive_signal_relations as interactive_run


SCHEMA_VERSION = "nrrf808.executor_reactor_reunification.v1"
RUN_KIND = "IMMUTABLE_EXECUTOR_REACTOR_REUNIFICATION"
EVENT_KIND = "REACTOR_PRESENTATION"
DERIVATION = {
    "truth_prior": "beat-generated translational closure",
    "executer_zero": "constant global-hair reading; never a selector",
    "reactor_inf": "all reciprocal public-book presentations; no representative chosen",
    "natural_isolation": "reactor kernel, identified only after an authored turn",
    "resource_metric_authors_form": False,
    "orders_enabled": False,
}
BOUNDARY = {
    "interaction_grade": "PUBLIC_BOOK_REACTOR_POTENTIAL_ONLY",
    "authored_transactional_actions": 0,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "profit_assessments": 0,
    "settled_profit_claimed": False,
}

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
    "interactive_manifest_sha256",
    "interactive_events_sha256",
    "interactive_final_event_hash",
}
PRESENTATION_FIELDS = {
    "input_asset",
    "output_asset",
    "book_side",
    "local_price",
    "price_unit",
}
FIBRE_FIELDS = {
    "reactor_relation_id",
    "market_source",
    "exchange_microtimestamp",
    "presentations",
    "presentation_set_sha256",
    "translational_truth",
    "global_hair_executer",
    "authored_turn",
    "identified_natural_form",
    "profit_assessment",
}
COMMAND_FIELDS = {
    "state",
    "reactor_fibres",
    "authored_turns",
    "identified_natural_forms",
    "missing_translations",
    "orders_submitted",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "source_event_hash",
    "observation_state",
    "reactor_fibres",
    "command",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "derivation",
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
    return source_bot.canonical_json_bytes(value)


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def read_json_object(path: Path) -> dict[str, object]:
    return relative_run.read_json_object(path)


def read_events(path: Path) -> list[dict[str, object]]:
    return relative_run.read_events(path)


def write_json(path: Path, value: object) -> None:
    relative_run.write_json(path, value)


def prepare_output_directory(path: Path) -> None:
    relative_run.prepare_output_directory(path)


def source_binding(
    observation_run: Path,
    relative_dir: Path,
    life_dir: Path,
    interactive_dir: Path,
) -> dict[str, object]:
    source_bot.verify_run(observation_run)
    relative_run.verify_overlay(observation_run, relative_dir)
    life_run.verify_overlay(observation_run, relative_dir, life_dir)
    interactive_run.verify_overlay(observation_run, relative_dir, life_dir, interactive_dir)
    observation_manifest = read_json_object(observation_run / "manifest.json")
    relative_manifest = read_json_object(relative_dir / "manifest.json")
    life_manifest = read_json_object(life_dir / "manifest.json")
    interactive_manifest = read_json_object(interactive_dir / "manifest.json")
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
        "interactive_manifest_sha256": sha256_file(interactive_dir / "manifest.json"),
        "interactive_events_sha256": interactive_manifest["events_sha256"],
        "interactive_final_event_hash": interactive_manifest["final_event_hash"],
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def reciprocal_presentations(
    market_id: str, market: Mapping[str, object]
) -> tuple[dict[str, object], dict[str, object]]:
    assets = market_id.split("_")
    if len(assets) != 2 or any(not asset for asset in assets):
        raise ValueError("market identifier does not present two assets")
    base, quote = assets
    best_bid = market.get("best_bid")
    best_ask = market.get("best_ask")
    if not isinstance(best_bid, str) or not isinstance(best_ask, str):
        raise ValueError("reactor presentation lacks string local prices")
    forward = {
        "input_asset": base,
        "output_asset": quote,
        "book_side": "BID",
        "local_price": best_bid,
        "price_unit": f"{quote}/{base}",
    }
    reverse = {
        "input_asset": quote,
        "output_asset": base,
        "book_side": "ASK_RECIPROCAL_PRESENTATION",
        "local_price": best_ask,
        "price_unit": f"{quote}/{base}",
    }
    if set(forward) != PRESENTATION_FIELDS or set(reverse) != PRESENTATION_FIELDS:
        raise AssertionError("presentation schema drift")
    return forward, reverse


def derive_reactor_fibres(event: Mapping[str, object]) -> list[dict[str, object]]:
    observation = event.get("observation")
    if not isinstance(observation, dict) or observation.get("state") != "IDENTIFIED_PUBLIC_BOOKS":
        return []
    markets = observation.get("markets")
    if not isinstance(markets, dict):
        raise ValueError("identified observation lacks markets")
    fibres: list[dict[str, object]] = []
    for market_id in sorted(markets):
        market = markets[market_id]
        if not isinstance(market, dict):
            raise ValueError("market metadata is not an object")
        presentations = list(reciprocal_presentations(market_id, market))
        assets = sorted({item["input_asset"] for item in presentations})
        fibre = {
            "reactor_relation_id": "<->".join(assets),
            "market_source": market_id,
            "exchange_microtimestamp": market.get("exchange_microtimestamp"),
            "presentations": presentations,
            "presentation_set_sha256": sha256_bytes(canonical_json_bytes(presentations)),
            "translational_truth": "RECIPROCAL_PRESENTATIONS_ONE_REACTOR",
            "global_hair_executer": "ZERO_UNIVERSAL_NOT_SIGNAL",
            "authored_turn": None,
            "identified_natural_form": None,
            "profit_assessment": None,
        }
        if set(fibre) != FIBRE_FIELDS:
            raise AssertionError("reactor fibre schema drift")
        fibres.append(fibre)
    return fibres


def derive_command(fibres: Sequence[Mapping[str, object]]) -> dict[str, object]:
    value = {
        "state": "OPEN_REACTOR",
        "reactor_fibres": len(fibres),
        "authored_turns": 0,
        "identified_natural_forms": 0,
        "missing_translations": ["AUTHORED_TRANSACTIONAL_ACTION"],
        "orders_submitted": 0,
    }
    if set(value) != COMMAND_FIELDS:
        raise AssertionError("command schema drift")
    return value


def derive_payloads(observation_run: Path) -> list[dict[str, object]]:
    events = read_events(observation_run / "events.jsonl")
    payloads: list[dict[str, object]] = []
    for event in events:
        observation = event.get("observation")
        observation_state = observation.get("state") if isinstance(observation, dict) else "OPEN"
        fibres = derive_reactor_fibres(event)
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "round_index": event["round_index"],
                "source_event_hash": event["event_hash"],
                "observation_state": observation_state,
                "reactor_fibres": fibres,
                "command": derive_command(fibres),
                "boundary": BOUNDARY,
            }
        )
    return payloads


def genesis_hash(binding: Mapping[str, object]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": "GENESIS",
                "derivation": DERIVATION,
                "source_binding": binding,
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
    fibres = [fibre for event in events for fibre in event["reactor_fibres"]]
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "rounds_with_reactor_geometry": sum(bool(event["reactor_fibres"]) for event in events),
        "reciprocal_reactor_fibres": len(fibres),
        "reciprocal_presentations": sum(len(fibre["presentations"]) for fibre in fibres),
        "universal_executer_zero_readings": len(fibres),
        "authored_transactional_actions": 0,
        "identified_natural_signal_forms": 0,
        "profit_assessments": 0,
        "open_reactor_commands": sum(event["command"]["state"] == "OPEN_REACTOR" for event in events),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "settled_profit_claimed": False,
        "boundary": BOUNDARY,
    }


def create_overlay(
    observation_run: Path,
    relative_dir: Path,
    life_dir: Path,
    interactive_dir: Path,
    output_dir: Path,
) -> dict[str, object]:
    binding = source_binding(observation_run, relative_dir, life_dir, interactive_dir)
    genesis = genesis_hash(binding)
    events = chain_events(derive_payloads(observation_run), genesis)
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
        "derivation": DERIVATION,
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
        "boundary": BOUNDARY,
    }
    if set(manifest) != MANIFEST_FIELDS:
        raise AssertionError("manifest schema drift")
    write_json(output_dir / "manifest.json", manifest)
    return {"manifest": manifest, "summary": summary}


def verify_overlay(
    observation_run: Path,
    relative_dir: Path,
    life_dir: Path,
    interactive_dir: Path,
    output_dir: Path,
) -> dict[str, object]:
    binding = source_binding(observation_run, relative_dir, life_dir, interactive_dir)
    manifest = read_json_object(output_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("manifest fields do not match protocol")
    identity = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "derivation": DERIVATION,
        "source_binding": binding,
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "boundary": BOUNDARY,
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
    expected_events = chain_events(derive_payloads(observation_run), genesis)
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
        command.add_argument("interactive_dir", type=Path)
        command.add_argument("output_dir", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "create":
        result = create_overlay(
            args.observation_run,
            args.relative_dir,
            args.life_dir,
            args.interactive_dir,
            args.output_dir,
        )
    else:
        result = verify_overlay(
            args.observation_run,
            args.relative_dir,
            args.life_dir,
            args.interactive_dir,
            args.output_dir,
        )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
