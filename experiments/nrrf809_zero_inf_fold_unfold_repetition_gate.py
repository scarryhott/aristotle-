"""Read public trading data through the derived 0-infinity pole interval.

The zero pole is the unconditional executer point.  The infinity pole is the reciprocal reactor
line.  A fold/unfold repetition reading requires an authored translation step; public books do not
provide one, so the reading remains open rather than becoming a price-pattern signal.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf808_executor_reactor_reunification as reunified
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf808_executor_reactor_reunification as reunified


SCHEMA_VERSION = "nrrf809.zero_inf_fold_unfold_repetition_gate.v1"
RUN_KIND = "IMMUTABLE_ZERO_INF_FOLD_UNFOLD_REPETITION_GATE"
EVENT_KIND = "ZERO_INF_POLE_READING"
DERIVATION = {
    "zero_pole": "greatest internal form; universal executer point",
    "inf_pole": "least internal form; beat-generated reciprocal reactor line",
    "fold": "quotient by an authored translation step",
    "unfold": "forward orbit of that same authored translation step",
    "repetition": "return within that orbit; unavailable before step authorship",
    "resource_metric_authors_step": False,
    "market_time_authors_step": False,
    "orders_enabled": False,
}
BOUNDARY = {
    "interaction_grade": "PUBLIC_BOOK_ZERO_INF_POLES_WITHOUT_AUTHORED_STEP",
    "authored_translation_steps": 0,
    "fold_readings": 0,
    "unfold_readings": 0,
    "repetition_readings": 0,
    "profit_assessments": 0,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "settled_profit_claimed": False,
}

SOURCE_BINDING_FIELDS = {
    "reunified_manifest_sha256",
    "reunified_events_sha256",
    "reunified_final_event_hash",
}
POLE_FIELDS = {"zero", "inf", "authored_translation_step", "second_level"}
ZERO_FIELDS = {"form", "role", "fold"}
INF_FIELDS = {
    "form",
    "role",
    "reactor_fibres",
    "reciprocal_presentations",
    "fold",
    "unfold",
    "repetition",
}
COMMAND_FIELDS = {
    "state",
    "missing_translations",
    "authored_translation_steps",
    "repetition_readings",
    "profit_assessments",
    "orders_submitted",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "source_event_hash",
    "observation_state",
    "zero_inf",
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
    return reunified.canonical_json_bytes(value)


def sha256_bytes(value: bytes) -> str:
    return reunified.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return reunified.sha256_file(path)


def read_json_object(path: Path) -> dict[str, object]:
    return reunified.read_json_object(path)


def read_events(path: Path) -> list[dict[str, object]]:
    return reunified.read_events(path)


def write_json(path: Path, value: object) -> None:
    reunified.write_json(path, value)


def prepare_output_directory(path: Path) -> None:
    reunified.prepare_output_directory(path)


def source_binding(
    observation_run: Path,
    relative_dir: Path,
    life_dir: Path,
    interactive_dir: Path,
    reunified_dir: Path,
) -> dict[str, object]:
    reunified.verify_overlay(
        observation_run, relative_dir, life_dir, interactive_dir, reunified_dir
    )
    manifest = read_json_object(reunified_dir / "manifest.json")
    binding = {
        "reunified_manifest_sha256": sha256_file(reunified_dir / "manifest.json"),
        "reunified_events_sha256": manifest["events_sha256"],
        "reunified_final_event_hash": manifest["final_event_hash"],
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def derive_zero_inf(source_event: Mapping[str, object]) -> dict[str, object]:
    fibres = source_event.get("reactor_fibres")
    if not isinstance(fibres, list):
        raise ValueError("source event lacks reactor fibres")
    for fibre in fibres:
        if not isinstance(fibre, dict):
            raise ValueError("reactor fibre is not an object")
        if fibre.get("authored_turn") is not None:
            raise ValueError("source claims an unauthenticated authored turn")
        if fibre.get("identified_natural_form") is not None:
            raise ValueError("source claims a form before step authorship")
    zero = {
        "form": "GREATEST_INTERNAL_FORM",
        "role": "GLOBAL_HAIR_EXECUTER_POINT",
        "fold": "IMMEDIATE_UNCONDITIONAL",
    }
    inf = {
        "form": "LEAST_INTERNAL_FORM",
        "role": "LOCAL_RECIPROCAL_REACTOR_LINE",
        "reactor_fibres": len(fibres),
        "reciprocal_presentations": sum(len(fibre["presentations"]) for fibre in fibres),
        "fold": None,
        "unfold": None,
        "repetition": None,
    }
    poles = {
        "zero": zero,
        "inf": inf,
        "authored_translation_step": None,
        "second_level": None,
    }
    if set(zero) != ZERO_FIELDS or set(inf) != INF_FIELDS or set(poles) != POLE_FIELDS:
        raise AssertionError("zero-infinity schema drift")
    return poles


def derive_command() -> dict[str, object]:
    command = {
        "state": "OPEN_ZERO_INF_TRANSLATION",
        "missing_translations": ["AUTHORED_TRANSLATION_STEP"],
        "authored_translation_steps": 0,
        "repetition_readings": 0,
        "profit_assessments": 0,
        "orders_submitted": 0,
    }
    if set(command) != COMMAND_FIELDS:
        raise AssertionError("command schema drift")
    return command


def derive_payloads(reunified_dir: Path) -> list[dict[str, object]]:
    payloads: list[dict[str, object]] = []
    for source_event in read_events(reunified_dir / "events.jsonl"):
        payloads.append(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": EVENT_KIND,
                "round_index": source_event["round_index"],
                "source_event_hash": source_event["event_hash"],
                "observation_state": source_event["observation_state"],
                "zero_inf": derive_zero_inf(source_event),
                "command": derive_command(),
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
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "rounds_with_inf_reactor_geometry": sum(
            bool(event["zero_inf"]["inf"]["reactor_fibres"]) for event in events
        ),
        "inf_reactor_fibres": sum(
            event["zero_inf"]["inf"]["reactor_fibres"] for event in events
        ),
        "inf_reciprocal_presentations": sum(
            event["zero_inf"]["inf"]["reciprocal_presentations"] for event in events
        ),
        "zero_pole_universal_readings": len(events),
        "authored_translation_steps": 0,
        "fold_readings": 0,
        "unfold_readings": 0,
        "repetition_readings": 0,
        "second_level_readings": 0,
        "profit_assessments": 0,
        "open_zero_inf_commands": len(events),
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
    reunified_dir: Path,
    output_dir: Path,
) -> dict[str, object]:
    binding = source_binding(
        observation_run, relative_dir, life_dir, interactive_dir, reunified_dir
    )
    genesis = genesis_hash(binding)
    events = chain_events(derive_payloads(reunified_dir), genesis)
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
    reunified_dir: Path,
    output_dir: Path,
) -> dict[str, object]:
    binding = source_binding(
        observation_run, relative_dir, life_dir, interactive_dir, reunified_dir
    )
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
    expected_events = chain_events(derive_payloads(reunified_dir), genesis)
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
        command.add_argument("reunified_dir", type=Path)
        command.add_argument("output_dir", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    function = create_overlay if args.command == "create" else verify_overlay
    result = function(
        args.observation_run,
        args.relative_dir,
        args.life_dir,
        args.interactive_dir,
        args.reunified_dir,
        args.output_dir,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
