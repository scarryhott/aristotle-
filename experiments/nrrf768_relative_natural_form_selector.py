"""NRRF768 relative-natural-form selector overlay.

This module does not alter NRRF767 and does not select a trade.  It verifies a
complete NRRF767 public-paper run, regards evaluations with the same
``start_usd`` as one relative-identity fibre, and authors exactly one of the
declared ``PLUS``/``MINUS`` presentations in every fibre.

The authored section evolves causally.  Its first orientation is supplied by
the author.  Later orientations are obtained only from the preceding selected
assessment: an OPEN assessment retains the representative, while a numeric
HOLD applies the declared polar reversal.  All other assessments retain it.
The choice is therefore a replayable frame trajectory, not an argmax, action,
execution authorization, or profit claim.

Overlay events bind the verified source-event hashes and form their own hash
chain.  ``verify_overlay`` recomputes the source run, its partition, every
section, every feedback translation, every selected assessment, the overlay
chain, and the summary.
"""

from __future__ import annotations

import argparse
import json
import os
from collections import Counter
from dataclasses import dataclass
from decimal import Decimal
from pathlib import Path
from typing import Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    # Direct invocation puts this file's directory, rather than the repository
    # root, on sys.path.  The fallback imports the same pinned sibling module.
    import nrrf767_live_paper_trading_bot as source_bot


SCHEMA_VERSION = "nrrf768.relative_natural_form_selector.v1"
RUN_KIND = "IMMUTABLE_RELATIVE_NATURAL_FORM_OVERLAY"
EVENT_KIND = "RELATIVE_NATURAL_FORM_SECTION"
PINNED_NRRF767_PROGRAM_SHA256 = (
    "37ec7ab19010530fedeb41e6152cd936e73e667a292e6343b18e721ab8e9fd02"
)
ORIENTATIONS = ("PLUS", "MINUS")
RELATIVE_IDENTITY = "SAME_START_USD_RADIUS"
POLAR_TRANSLATION = {"PLUS": "MINUS", "MINUS": "PLUS"}
SELECTION_SCOPE = "NATURAL_FORM_REPRESENTATIVE_ONLY"
FEEDBACK_RULE = (
    "preceding OPEN retains; preceding numeric HOLD reverses; "
    "every other preceding selected assessment retains"
)

NO_ORDER_BOUNDARY = {
    "selection_scope": SELECTION_SCOPE,
    "action_selected": False,
    "profit_selected": False,
    "execution_authorized": False,
    "orders_enabled": False,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "formal_receipt_admissions": 0,
    "no_order_account_delta_usd": "0",
    "authenticated_settled_pnl_usd": None,
}

MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "selector_configuration",
    "selector_configuration_sha256",
    "genesis_hash",
    "event_count",
    "final_event_hash",
    "events_file",
    "events_sha256",
    "summary_file",
    "summary_sha256",
    "program",
    "program_sha256",
    "source_binding",
    "boundary",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "source_event_hash",
    "context",
    "section",
    "translation_witnesses",
    "selected_empirical_assessments",
    "boundary",
    "previous_event_hash",
    "event_hash",
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
CONTEXT_FIELDS = {
    "relative_identity",
    "topological_reading",
    "freedom_reading",
    "source_round_index",
    "source_recorded_utc",
    "source_observation_state",
    "source_observation_witnesses",
    "source_event_hash",
    "fibres",
}
FIBRE_FIELDS = {
    "fibre_id",
    "start_usd",
    "member_orientations",
    "presentations",
    "polar_reversal",
}
PRESENTATION_FIELDS = {"presentation_id", "orientation", "path"}
SECTION_FIELDS = {
    "fibre_id",
    "start_usd",
    "chosen_orientation",
    "chosen_presentation_id",
}
TRANSLATION_FIELDS = {
    "fibre_id",
    "start_usd",
    "translation",
    "feedback_trigger",
    "from_orientation",
    "to_orientation",
    "from_presentation_id",
    "to_presentation_id",
    "same_relative_identity",
    "execution_effect",
}
ASSESSMENT_FIELDS = {
    "fibre_id",
    "presentation_id",
    "source_evaluation_sha256",
    "observation_state",
    "orientation",
    "path",
    "start_usd",
    "decision",
    "full_depth_coverage",
    "candidate_final_usd",
    "candidate_delta_usd",
    "candidate_return_bps",
    "witnesses",
    "empirical_scope",
    "action_selected",
    "execution_authorized",
    "profit_claimed",
}


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def strict_json_loads(raw: bytes) -> object:
    return source_bot.strict_json_loads(raw)


def require_sha256(value: object, label: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{label} is not a canonical SHA-256 digest")
    return value


def canonical_radius(value: object) -> str:
    if not isinstance(value, str):
        raise ValueError("start_usd radius must be a string")
    try:
        parsed = source_bot.parse_decimal(value)
    except Exception as error:
        raise ValueError("start_usd radius is not finite decimal text") from error
    if parsed <= 0 or source_bot.decimal_text(parsed) != value:
        raise ValueError("start_usd radius is not canonical positive decimal text")
    return value


def fibre_id(radius: str) -> str:
    radius = canonical_radius(radius)
    digest = sha256_bytes(
        canonical_json_bytes(
            {
                "relative_identity": RELATIVE_IDENTITY,
                "start_usd": radius,
                "member_orientations": list(ORIENTATIONS),
            }
        )
    )
    return f"radius:{digest}"


def presentation_id(radius: str, orientation: str) -> str:
    if orientation not in ORIENTATIONS:
        raise ValueError("orientation is not a declared polar presentation")
    digest = sha256_bytes(
        canonical_json_bytes(
            {
                "fibre_id": fibre_id(radius),
                "orientation": orientation,
            }
        )
    )
    return f"presentation:{digest}"


@dataclass(frozen=True)
class SelectorConfig:
    initial_authored_orientation: str = "PLUS"

    def __post_init__(self) -> None:
        if self.initial_authored_orientation not in ORIENTATIONS:
            raise ValueError("initial authored orientation must be PLUS or MINUS")

    def as_dict(self) -> dict[str, object]:
        return {
            "initial_authored_orientation": self.initial_authored_orientation,
            "relative_identity": RELATIVE_IDENTITY,
            "member_orientations": list(ORIENTATIONS),
            "polar_translation": dict(POLAR_TRANSLATION),
            "feedback_rule": FEEDBACK_RULE,
            "selection_scope": SELECTION_SCOPE,
            "orders_enabled": False,
        }

    @classmethod
    def from_dict(cls, value: object) -> "SelectorConfig":
        if not isinstance(value, dict):
            raise ValueError("selector configuration must be an object")
        config = cls(initial_authored_orientation=str(value.get("initial_authored_orientation")))
        if value != config.as_dict():
            raise ValueError("selector configuration contains altered or noncanonical fields")
        return config

    @property
    def digest(self) -> str:
        return sha256_bytes(canonical_json_bytes(self.as_dict()))


@dataclass(frozen=True)
class NaturalFormSection:
    """Exactly one authored orientation for each radius in its finite domain."""

    choices: tuple[tuple[str, str], ...]

    def __post_init__(self) -> None:
        seen: set[str] = set()
        for radius, orientation in self.choices:
            canonical_radius(radius)
            if radius in seen:
                raise ValueError("natural-form section duplicates a radius")
            if orientation not in ORIENTATIONS:
                raise ValueError("natural-form section invents an orientation")
            seen.add(radius)

    @classmethod
    def authored(
        cls,
        radii: Sequence[str],
        orientation: str,
    ) -> "NaturalFormSection":
        if orientation not in ORIENTATIONS:
            raise ValueError("authored orientation must be PLUS or MINUS")
        return cls(tuple((canonical_radius(radius), orientation) for radius in radii))

    def require_domain(self, radii: Sequence[str]) -> None:
        expected = tuple(canonical_radius(radius) for radius in radii)
        actual = tuple(radius for radius, _orientation in self.choices)
        if actual != expected:
            raise ValueError("natural-form section is missing, duplicated, or cross-radius")

    def orientation_at(self, radius: str) -> str:
        for existing, orientation in self.choices:
            if existing == radius:
                return orientation
        raise ValueError("natural-form section is missing a radius")


def source_radii(source_manifest: Mapping[str, object]) -> tuple[str, ...]:
    configuration = source_manifest.get("configuration")
    if not isinstance(configuration, dict):
        raise ValueError("source configuration is not an object")
    raw_radii = configuration.get("notionals_usd")
    if not isinstance(raw_radii, list) or not raw_radii:
        raise ValueError("source has no declared start_usd radii")
    radii = tuple(canonical_radius(value) for value in raw_radii)
    if len(set(radii)) != len(radii):
        raise ValueError("source declares duplicate start_usd radii")
    return radii


def source_partition(
    source_event: Mapping[str, object],
    radii: Sequence[str],
) -> tuple[dict[str, dict[str, object]], ...]:
    """Return the exact PLUS/MINUS fibre at every declared source radius."""

    expected_radii = tuple(canonical_radius(radius) for radius in radii)
    evaluations = source_event.get("evaluations")
    if not isinstance(evaluations, list):
        raise ValueError("source evaluations are not a list")
    indexed: dict[tuple[str, str], dict[str, object]] = {}
    for candidate in evaluations:
        if not isinstance(candidate, dict):
            raise ValueError("source evaluation is not an object")
        radius = canonical_radius(candidate.get("start_usd"))
        orientation = candidate.get("orientation")
        if radius not in expected_radii:
            raise ValueError("source evaluation crosses or invents a radius")
        if orientation not in ORIENTATIONS:
            raise ValueError("source evaluation invents a polar presentation")
        key = (radius, str(orientation))
        if key in indexed:
            raise ValueError("source evaluation duplicates a fibre presentation")
        indexed[key] = candidate

    expected_keys = {
        (radius, orientation)
        for radius in expected_radii
        for orientation in ORIENTATIONS
    }
    if set(indexed) != expected_keys:
        raise ValueError("source partition is missing or has extra fibre presentations")
    return tuple(
        {orientation: indexed[(radius, orientation)] for orientation in ORIENTATIONS}
        for radius in expected_radii
    )


def context_from_source(
    source_event: Mapping[str, object],
    radii: Sequence[str],
) -> tuple[dict[str, object], tuple[dict[str, dict[str, object]], ...]]:
    partitions = source_partition(source_event, radii)
    observation = source_event.get("observation")
    if not isinstance(observation, dict):
        raise ValueError("source observation is not an object")
    state = observation.get("state")
    if state not in ("IDENTIFIED_PUBLIC_BOOKS", "OPEN_PUBLIC_BOOKS"):
        raise ValueError("source observation state is not declared")
    witnesses = observation.get("witnesses")
    if not isinstance(witnesses, list) or any(not isinstance(item, str) for item in witnesses):
        raise ValueError("source observation witnesses are not canonical")
    source_hash = require_sha256(source_event.get("event_hash"), "source event hash")
    fibres: list[dict[str, object]] = []
    for radius, partition in zip(radii, partitions):
        presentations = [
            {
                "presentation_id": presentation_id(radius, orientation),
                "orientation": orientation,
                "path": partition[orientation]["path"],
            }
            for orientation in ORIENTATIONS
        ]
        fibres.append(
            {
                "fibre_id": fibre_id(radius),
                "start_usd": radius,
                "member_orientations": list(ORIENTATIONS),
                "presentations": presentations,
                "polar_reversal": {
                    orientation: presentation_id(radius, POLAR_TRANSLATION[orientation])
                    for orientation in ORIENTATIONS
                },
            }
        )
    context = {
        "relative_identity": RELATIVE_IDENTITY,
        "topological_reading": "ONE_POLAR_FIBRE_PER_START_USD_RADIUS",
        "freedom_reading": "EITHER_PRESENTATION_MAY_AUTHOR_ONE_TOTAL_SECTION",
        "source_round_index": source_event.get("round_index"),
        "source_recorded_utc": source_event.get("recorded_utc"),
        "source_observation_state": state,
        "source_observation_witnesses": list(witnesses),
        "source_event_hash": source_hash,
        "fibres": fibres,
    }
    return context, partitions


def assessment_from_source(
    radius: str,
    candidate: Mapping[str, object],
    observation_state: str,
) -> dict[str, object]:
    orientation = candidate.get("orientation")
    if orientation not in ORIENTATIONS or candidate.get("start_usd") != radius:
        raise ValueError("selected assessment is outside its declared fibre")
    assessment = {
        "fibre_id": fibre_id(radius),
        "presentation_id": presentation_id(radius, str(orientation)),
        "source_evaluation_sha256": sha256_bytes(canonical_json_bytes(candidate)),
        "observation_state": observation_state,
        "orientation": orientation,
        "path": candidate.get("path"),
        "start_usd": radius,
        "decision": candidate.get("decision"),
        "full_depth_coverage": candidate.get("full_depth_coverage"),
        "candidate_final_usd": candidate.get("candidate_final_usd"),
        "candidate_delta_usd": candidate.get("candidate_delta_usd"),
        "candidate_return_bps": candidate.get("candidate_return_bps"),
        "witnesses": candidate.get("witnesses"),
        "empirical_scope": "SELECTED_PUBLIC_REST_COUNTERFACTUAL_ASSESSMENT",
        "action_selected": False,
        "execution_authorized": False,
        "profit_claimed": False,
    }
    if set(assessment) != ASSESSMENT_FIELDS:
        raise AssertionError("assessment protocol construction failed")
    return assessment


def feedback_translation(preceding_assessment: Mapping[str, object]) -> tuple[str, str]:
    """Translate one representative using only its preceding assessment."""

    if preceding_assessment.get("observation_state") == "OPEN_PUBLIC_BOOKS":
        return "IDENTITY", "PRECEDING_OPEN_RETAINS"
    if (
        preceding_assessment.get("decision") == "HOLD"
        and preceding_assessment.get("candidate_return_bps") is not None
    ):
        return "POLAR_REVERSAL", "PRECEDING_NUMERIC_HOLD_REVERSES"
    return "IDENTITY", "PRECEDING_SELECTED_ASSESSMENT_RETAINS"


def translated_section(
    preceding_section: NaturalFormSection,
    preceding_assessments: Sequence[Mapping[str, object]],
    radii: Sequence[str],
) -> tuple[NaturalFormSection, tuple[tuple[str, str], ...]]:
    """Apply independent in-fibre feedback; alternatives are never ranked."""

    preceding_section.require_domain(radii)
    by_fibre: dict[str, Mapping[str, object]] = {}
    for assessment in preceding_assessments:
        identifier = assessment.get("fibre_id")
        if not isinstance(identifier, str) or identifier in by_fibre:
            raise ValueError("preceding assessments duplicate or omit a fibre")
        by_fibre[identifier] = assessment
    if set(by_fibre) != {fibre_id(radius) for radius in radii}:
        raise ValueError("preceding assessments do not form one total section")

    choices: list[tuple[str, str]] = []
    translations: list[tuple[str, str]] = []
    for radius in radii:
        previous_orientation = preceding_section.orientation_at(radius)
        assessment = by_fibre[fibre_id(radius)]
        if (
            assessment.get("orientation") != previous_orientation
            or assessment.get("start_usd") != radius
            or assessment.get("presentation_id")
            != presentation_id(radius, previous_orientation)
        ):
            raise ValueError("preceding assessment is not the section's chosen presentation")
        translation, trigger = feedback_translation(assessment)
        orientation = (
            POLAR_TRANSLATION[previous_orientation]
            if translation == "POLAR_REVERSAL"
            else previous_orientation
        )
        choices.append((radius, orientation))
        translations.append((translation, trigger))
    section = NaturalFormSection(tuple(choices))
    section.require_domain(radii)
    return section, tuple(translations)


def section_records(
    section: NaturalFormSection,
    radii: Sequence[str],
) -> list[dict[str, object]]:
    section.require_domain(radii)
    return [
        {
            "fibre_id": fibre_id(radius),
            "start_usd": radius,
            "chosen_orientation": section.orientation_at(radius),
            "chosen_presentation_id": presentation_id(
                radius, section.orientation_at(radius)
            ),
        }
        for radius in radii
    ]


def section_from_records(
    records: object,
    radii: Sequence[str],
) -> NaturalFormSection:
    if not isinstance(records, list):
        raise ValueError("section is not a list")
    choices: list[tuple[str, str]] = []
    for record in records:
        if not isinstance(record, dict) or set(record) != SECTION_FIELDS:
            raise ValueError("section choice fields do not match the protocol")
        radius = canonical_radius(record.get("start_usd"))
        orientation = record.get("chosen_orientation")
        if orientation not in ORIENTATIONS:
            raise ValueError("section choice invents an orientation")
        if record.get("fibre_id") != fibre_id(radius):
            raise ValueError("section choice crosses a radius fibre")
        if record.get("chosen_presentation_id") != presentation_id(radius, str(orientation)):
            raise ValueError("section presentation does not inhabit its radius fibre")
        choices.append((radius, str(orientation)))
    section = NaturalFormSection(tuple(choices))
    section.require_domain(radii)
    return section


def translation_records(
    preceding_section: NaturalFormSection | None,
    current_section: NaturalFormSection,
    translations: Sequence[tuple[str, str]],
    radii: Sequence[str],
) -> list[dict[str, object]]:
    current_section.require_domain(radii)
    if preceding_section is not None:
        preceding_section.require_domain(radii)
    if len(translations) != len(radii):
        raise ValueError("translation witnesses do not cover every radius")
    records: list[dict[str, object]] = []
    for radius, (translation, trigger) in zip(radii, translations):
        to_orientation = current_section.orientation_at(radius)
        from_orientation = (
            preceding_section.orientation_at(radius) if preceding_section is not None else None
        )
        record = {
            "fibre_id": fibre_id(radius),
            "start_usd": radius,
            "translation": translation,
            "feedback_trigger": trigger,
            "from_orientation": from_orientation,
            "to_orientation": to_orientation,
            "from_presentation_id": (
                presentation_id(radius, from_orientation)
                if from_orientation is not None
                else None
            ),
            "to_presentation_id": presentation_id(radius, to_orientation),
            "same_relative_identity": True,
            "execution_effect": "NONE",
        }
        records.append(record)
    return records


def build_overlay_event(
    source_event: Mapping[str, object],
    radii: Sequence[str],
    config: SelectorConfig,
    previous_overlay_event: Mapping[str, object] | None,
    previous_event_hash: str,
) -> dict[str, object]:
    # Author or translate the section before reading the current source event.
    # Thus only the preceding selected assessment can affect the present form;
    # the current books are subsequently used to assess that already-fixed form.
    if previous_overlay_event is None:
        section = NaturalFormSection.authored(radii, config.initial_authored_orientation)
        witness_kinds = tuple(
            ("AUTHORED_INITIAL", "INITIAL_AUTHORSHIP") for _radius in radii
        )
        preceding_section = None
    else:
        preceding_section = section_from_records(previous_overlay_event.get("section"), radii)
        preceding_assessments = previous_overlay_event.get("selected_empirical_assessments")
        if not isinstance(preceding_assessments, list):
            raise ValueError("preceding selected assessments are not a list")
        section, witness_kinds = translated_section(
            preceding_section, preceding_assessments, radii
        )

    context, partitions = context_from_source(source_event, radii)
    assessments = [
        assessment_from_source(
            radius,
            partition[section.orientation_at(radius)],
            str(context["source_observation_state"]),
        )
        for radius, partition in zip(radii, partitions)
    ]
    payload: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "event_kind": EVENT_KIND,
        "round_index": source_event.get("round_index"),
        "source_event_hash": context["source_event_hash"],
        "context": context,
        "section": section_records(section, radii),
        "translation_witnesses": translation_records(
            preceding_section, section, witness_kinds, radii
        ),
        "selected_empirical_assessments": assessments,
        "boundary": dict(NO_ORDER_BOUNDARY),
        "previous_event_hash": previous_event_hash,
    }
    payload["event_hash"] = sha256_bytes(canonical_json_bytes(payload))
    return payload


def selector_genesis(config: SelectorConfig, source_binding: Mapping[str, object]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": "GENESIS",
                "selector_configuration_sha256": config.digest,
                "source_binding": dict(source_binding),
            }
        )
    )


def source_binding(source_run: Path) -> tuple[dict[str, object], dict[str, object]]:
    current_source_program = Path(source_bot.__file__).resolve()
    if sha256_file(current_source_program) != PINNED_NRRF767_PROGRAM_SHA256:
        raise ValueError("the imported NRRF767 verifier does not match its pinned digest")
    verification = source_bot.verify_run(source_run)
    manifest_path = source_run / "manifest.json"
    manifest = strict_json_loads(manifest_path.read_bytes())
    if not isinstance(manifest, dict):
        raise ValueError("source manifest is not an object")
    binding = {
        "schema_version": manifest.get("schema_version"),
        "run_kind": manifest.get("run_kind"),
        "configuration_sha256": manifest.get("configuration_sha256"),
        "genesis_hash": manifest.get("genesis_hash"),
        "event_count": manifest.get("event_count"),
        "final_event_hash": manifest.get("final_event_hash"),
        "events_sha256": manifest.get("events_sha256"),
        "summary_sha256": manifest.get("summary_sha256"),
        "program": manifest.get("program"),
        "program_sha256": manifest.get("program_sha256"),
        "manifest_sha256": sha256_file(manifest_path),
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding protocol construction failed")
    if binding["schema_version"] != source_bot.SCHEMA_VERSION:
        raise ValueError("source schema is not NRRF767 v1")
    if binding["run_kind"] != source_bot.EXPECTED_RUN_KIND:
        raise ValueError("source run is not public paper evidence")
    if binding["program"] != Path(source_bot.__file__).name:
        raise ValueError("source program name mismatch")
    if binding["program_sha256"] != PINNED_NRRF767_PROGRAM_SHA256:
        raise ValueError("source manifest does not bind the pinned NRRF767 program")
    if verification.get("final_event_hash") != binding["final_event_hash"]:
        raise ValueError("source verification and binding disagree")
    return binding, manifest


def load_source_events(
    source_run: Path,
    expected_events_sha256: object,
) -> list[dict[str, object]]:
    expected_digest = require_sha256(
        expected_events_sha256, "expected source events digest"
    )
    raw = (source_run / "events.jsonl").read_bytes()
    if sha256_bytes(raw) != expected_digest:
        raise ValueError("source events changed after their verified binding")
    if not raw.endswith(b"\n") or b"\n\n" in raw:
        raise ValueError("source events are not complete nonempty lines")
    events: list[dict[str, object]] = []
    for line in raw.splitlines():
        value = strict_json_loads(line)
        if not isinstance(value, dict):
            raise ValueError("source event is not an object")
        events.append(value)
    return events


def summarize_overlay(events: Sequence[Mapping[str, object]]) -> dict[str, object]:
    orientations: Counter[str] = Counter()
    translations: Counter[str] = Counter()
    triggers: Counter[str] = Counter()
    observation_states: Counter[str] = Counter()
    decisions: Counter[str] = Counter()
    numeric = 0
    negative = 0
    zero = 0
    positive = 0
    selected_count = 0
    radii: list[str] = []

    for event_index, event in enumerate(events):
        context = event["context"]
        observation_states[str(context["source_observation_state"])] += 1
        section = event["section"]
        witnesses = event["translation_witnesses"]
        assessments = event["selected_empirical_assessments"]
        if event_index == 0:
            radii = [str(choice["start_usd"]) for choice in section]
        for choice in section:
            orientations[str(choice["chosen_orientation"])] += 1
        for witness in witnesses:
            translations[str(witness["translation"])] += 1
            triggers[str(witness["feedback_trigger"])] += 1
        for assessment in assessments:
            selected_count += 1
            decisions[str(assessment["decision"])] += 1
            return_text = assessment["candidate_return_bps"]
            if return_text is not None:
                numeric += 1
                value = Decimal(str(return_text))
                if value < 0:
                    negative += 1
                elif value > 0:
                    positive += 1
                else:
                    zero += 1

    return {
        "schema_version": SCHEMA_VERSION,
        "source_events": len(events),
        "declared_radii": radii,
        "sections": len(events),
        "selected_empirical_assessments": selected_count,
        "orientation_counts": dict(sorted(orientations.items())),
        "translation_counts": dict(sorted(translations.items())),
        "feedback_trigger_counts": dict(sorted(triggers.items())),
        "source_observation_states": dict(sorted(observation_states.items())),
        "assessment_decisions": dict(sorted(decisions.items())),
        "numeric_assessments": numeric,
        "negative_numeric_assessments": negative,
        "zero_numeric_assessments": zero,
        "positive_numeric_assessments": positive,
        "action_selections": 0,
        "profit_selections": 0,
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "formal_receipt_admissions": 0,
        "no_order_account_delta_usd": "0",
        "authenticated_settled_pnl_usd": None,
    }


def prepare_output_directory(output_dir: Path) -> None:
    if output_dir.exists():
        if not output_dir.is_dir() or any(output_dir.iterdir()):
            raise FileExistsError("overlay output directory must be absent or empty")
    else:
        output_dir.mkdir(parents=True)


def write_new(path: Path, content: bytes) -> None:
    with path.open("xb") as target:
        target.write(content)
        target.flush()
        os.fsync(target.fileno())


def create_overlay(
    source_run: Path,
    output_dir: Path,
    config: SelectorConfig = SelectorConfig(),
) -> dict[str, object]:
    binding, source_manifest = source_binding(source_run)
    radii = source_radii(source_manifest)
    source_events = load_source_events(source_run, binding["events_sha256"])
    if len(source_events) != binding["event_count"]:
        raise ValueError("source event count changed after verification")

    prepare_output_directory(output_dir)
    genesis = selector_genesis(config, binding)
    previous_hash = genesis
    previous_event: dict[str, object] | None = None
    events: list[dict[str, object]] = []
    for expected_index, source_event in enumerate(source_events):
        if source_event.get("round_index") != expected_index:
            raise ValueError("source round order changed after verification")
        event = build_overlay_event(
            source_event,
            radii,
            config,
            previous_event,
            previous_hash,
        )
        events.append(event)
        previous_event = event
        previous_hash = str(event["event_hash"])

    events_bytes = b"".join(canonical_json_bytes(event) + b"\n" for event in events)
    summary = summarize_overlay(events)
    summary_bytes = json.dumps(summary, indent=2, sort_keys=True).encode() + b"\n"
    program_path = Path(__file__).resolve()
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "selector_configuration": config.as_dict(),
        "selector_configuration_sha256": config.digest,
        "genesis_hash": genesis,
        "event_count": len(events),
        "final_event_hash": previous_hash,
        "events_file": "events.jsonl",
        "events_sha256": sha256_bytes(events_bytes),
        "summary_file": "summary.json",
        "summary_sha256": sha256_bytes(summary_bytes),
        "program": program_path.name,
        "program_sha256": sha256_file(program_path),
        "source_binding": binding,
        "boundary": dict(NO_ORDER_BOUNDARY),
    }
    write_new(output_dir / "events.jsonl", events_bytes)
    write_new(output_dir / "summary.json", summary_bytes)
    write_new(
        output_dir / "manifest.json",
        json.dumps(manifest, indent=2, sort_keys=True).encode() + b"\n",
    )
    return manifest


def validate_record_shapes(event: Mapping[str, object], radii: Sequence[str]) -> None:
    if set(event) != EVENT_FIELDS:
        raise ValueError("overlay event fields do not match the protocol")
    context = event.get("context")
    if not isinstance(context, dict) or set(context) != CONTEXT_FIELDS:
        raise ValueError("overlay context fields do not match the protocol")
    fibres = context.get("fibres")
    if not isinstance(fibres, list) or len(fibres) != len(radii):
        raise ValueError("overlay context does not contain every radius fibre")
    for radius, fibre in zip(radii, fibres):
        if not isinstance(fibre, dict) or set(fibre) != FIBRE_FIELDS:
            raise ValueError("overlay fibre fields do not match the protocol")
        if fibre.get("start_usd") != radius or fibre.get("fibre_id") != fibre_id(radius):
            raise ValueError("overlay context crosses a radius fibre")
        presentations = fibre.get("presentations")
        if not isinstance(presentations, list) or len(presentations) != len(ORIENTATIONS):
            raise ValueError("overlay fibre does not contain its two presentations")
        for presentation in presentations:
            if not isinstance(presentation, dict) or set(presentation) != PRESENTATION_FIELDS:
                raise ValueError("overlay presentation fields do not match the protocol")
    section_from_records(event.get("section"), radii)
    translations = event.get("translation_witnesses")
    if not isinstance(translations, list) or len(translations) != len(radii):
        raise ValueError("overlay translations do not cover every radius")
    for translation in translations:
        if not isinstance(translation, dict) or set(translation) != TRANSLATION_FIELDS:
            raise ValueError("overlay translation fields do not match the protocol")
    assessments = event.get("selected_empirical_assessments")
    if not isinstance(assessments, list) or len(assessments) != len(radii):
        raise ValueError("overlay assessments do not cover every radius")
    seen_assessments: set[str] = set()
    for assessment in assessments:
        if not isinstance(assessment, dict) or set(assessment) != ASSESSMENT_FIELDS:
            raise ValueError("overlay assessment fields do not match the protocol")
        identifier = assessment.get("fibre_id")
        if not isinstance(identifier, str) or identifier in seen_assessments:
            raise ValueError("overlay assessments duplicate a radius fibre")
        seen_assessments.add(identifier)
    if seen_assessments != {fibre_id(radius) for radius in radii}:
        raise ValueError("overlay assessments omit or invent a radius fibre")


def verify_overlay(overlay_dir: Path, source_run: Path) -> dict[str, object]:
    actual_entries = sorted(path.name for path in overlay_dir.iterdir())
    if actual_entries != ["events.jsonl", "manifest.json", "summary.json"]:
        raise ValueError("overlay directory does not contain exactly its three immutable files")
    manifest_path = overlay_dir / "manifest.json"
    manifest = strict_json_loads(manifest_path.read_bytes())
    if not isinstance(manifest, dict) or set(manifest) != MANIFEST_FIELDS:
        raise ValueError("overlay manifest fields do not match the protocol")
    if manifest.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("overlay manifest schema mismatch")
    if manifest.get("run_kind") != RUN_KIND:
        raise ValueError("overlay run kind mismatch")
    if manifest.get("events_file") != "events.jsonl":
        raise ValueError("overlay events path mismatch")
    if manifest.get("summary_file") != "summary.json":
        raise ValueError("overlay summary path mismatch")
    if manifest.get("boundary") != NO_ORDER_BOUNDARY:
        raise ValueError("overlay no-order boundary mismatch")
    if manifest.get("program") != Path(__file__).name:
        raise ValueError("overlay program name mismatch")
    if manifest.get("program_sha256") != sha256_file(Path(__file__).resolve()):
        raise ValueError("overlay program hash does not match this verifier")
    config = SelectorConfig.from_dict(manifest.get("selector_configuration"))
    if manifest.get("selector_configuration_sha256") != config.digest:
        raise ValueError("overlay selector configuration hash mismatch")

    binding, source_manifest = source_binding(source_run)
    recorded_binding = manifest.get("source_binding")
    if not isinstance(recorded_binding, dict) or set(recorded_binding) != SOURCE_BINDING_FIELDS:
        raise ValueError("overlay source binding fields do not match the protocol")
    for key in (
        "configuration_sha256",
        "genesis_hash",
        "final_event_hash",
        "events_sha256",
        "summary_sha256",
        "program_sha256",
        "manifest_sha256",
    ):
        require_sha256(recorded_binding.get(key), f"source binding {key}")
    if recorded_binding != binding:
        raise ValueError("overlay source binding does not match the supplied verified run")
    expected_genesis = selector_genesis(config, binding)
    if manifest.get("genesis_hash") != expected_genesis:
        raise ValueError("overlay genesis hash mismatch")

    events_path = overlay_dir / "events.jsonl"
    if manifest.get("events_sha256") != sha256_file(events_path):
        raise ValueError("overlay events file hash mismatch")
    ledger = events_path.read_bytes()
    if not ledger.endswith(b"\n") or b"\n\n" in ledger:
        raise ValueError("overlay events must contain complete nonempty lines")
    source_events = load_source_events(source_run, binding["events_sha256"])
    lines = ledger.splitlines()
    if type(manifest.get("event_count")) is not int or manifest["event_count"] <= 0:
        raise ValueError("overlay event count must be a positive integer")
    if len(lines) != manifest["event_count"] or len(source_events) != len(lines):
        raise ValueError("overlay and source event counts disagree")

    radii = source_radii(source_manifest)
    previous_hash = expected_genesis
    previous_expected: dict[str, object] | None = None
    events: list[dict[str, object]] = []
    for expected_index, (line, source_event) in enumerate(zip(lines, source_events)):
        recorded = strict_json_loads(line)
        if not isinstance(recorded, dict):
            raise ValueError("overlay event is not an object")
        validate_record_shapes(recorded, radii)
        if recorded.get("schema_version") != SCHEMA_VERSION:
            raise ValueError("overlay event schema mismatch")
        if recorded.get("event_kind") != EVENT_KIND:
            raise ValueError("overlay event kind mismatch")
        if recorded.get("round_index") != expected_index:
            raise ValueError("overlay round index mismatch")
        if recorded.get("previous_event_hash") != previous_hash:
            raise ValueError("overlay predecessor hash mismatch")
        unhashed = dict(recorded)
        claimed_hash = unhashed.pop("event_hash", None)
        if claimed_hash != sha256_bytes(canonical_json_bytes(unhashed)):
            raise ValueError("overlay event hash mismatch")
        expected = build_overlay_event(
            source_event,
            radii,
            config,
            previous_expected,
            previous_hash,
        )
        if recorded != expected:
            raise ValueError(
                f"overlay semantic replay mismatch at round {expected_index}; "
                "section may be missing, duplicated, cross-radius, invented, or noncausal"
            )
        previous_hash = str(claimed_hash)
        previous_expected = expected
        events.append(recorded)

    if manifest.get("final_event_hash") != previous_hash:
        raise ValueError("overlay final event hash mismatch")
    if manifest.get("event_count") != len(events):
        raise ValueError("overlay event count mismatch")
    summary_path = overlay_dir / "summary.json"
    if manifest.get("summary_sha256") != sha256_file(summary_path):
        raise ValueError("overlay summary hash mismatch")
    recorded_summary = strict_json_loads(summary_path.read_bytes())
    expected_summary = summarize_overlay(events)
    if recorded_summary != expected_summary:
        raise ValueError("overlay summary replay mismatch")
    return {
        "verified": True,
        "event_count": len(events),
        "selector_configuration_sha256": config.digest,
        "source_final_event_hash": binding["final_event_hash"],
        "final_event_hash": previous_hash,
        "events_sha256": manifest["events_sha256"],
        "summary_sha256": manifest["summary_sha256"],
        "manifest_sha256": sha256_file(manifest_path),
        "program_sha256": manifest["program_sha256"],
        "source_program_sha256": binding["program_sha256"],
        "summary": recorded_summary,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Build or verify an NRRF768 natural-form selector overlay"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build")
    build.add_argument("--source-run", type=Path, required=True)
    build.add_argument("--output-dir", type=Path, required=True)
    build.add_argument("--initial-orientation", choices=ORIENTATIONS, default="PLUS")
    verify = subparsers.add_parser("verify")
    verify.add_argument("--source-run", type=Path, required=True)
    verify.add_argument("--overlay-dir", type=Path, required=True)
    return parser


def main() -> None:
    args = build_parser().parse_args()
    if args.command == "build":
        result = create_overlay(
            args.source_run,
            args.output_dir,
            SelectorConfig(args.initial_orientation),
        )
        result = {
            "created": True,
            "manifest_sha256": sha256_file(args.output_dir / "manifest.json"),
            "manifest": result,
        }
    else:
        result = verify_overlay(args.overlay_dir, args.source_run)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
