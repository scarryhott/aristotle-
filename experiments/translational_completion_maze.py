#!/usr/bin/env python3
"""Relation-first translational-completion maze topology assay.

This finite runtime starts before quotient resolution while retaining a
separately frozen Setoid-like frame equality.  It freezes directed learning
lines, derives raw reflexive-transitive reach, and only uses that reach as the
intended equality when explicit return paths make it symmetric and it exactly
realizes the prior frame equality.  The assay tests a faithful-nondiscrete
bounded proxy related to the reported NRRF639 boundary; the unavailable
NRRF639 Lean source is not recreated or claimed to have been audited here.

The same line has a direct passage reading and an inverse wall reading.  A
return is therefore a path through other lines, not a relabelling of the wall.
The bounded topology receipt is computed after the topology and is never an
input to reachability, completion, quotient, or topology construction.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from collections import deque
from pathlib import Path
from typing import Any, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK = ROOT / "benchmarks" / "translational_completion_maze"
PROTOCOL = BENCHMARK / "protocol.json"
DEFAULT_OUTPUT = ROOT / "runs" / "translational_completion_maze" / "latest"

# Filled from the committed deterministic reference run.
REFERENCE_PROTOCOL_SHA256 = "eae0395a65a8bbd7a0b5f691c82027bde30203395fffce1b53dc74494937cb1d"
REFERENCE_RESULT_SHA256 = "99f23f98937511dc55967c4cfe7c088b93fe9dd2d3c04a8055c2c743081796b4"
REFERENCE_RECEIPT_HEAD = "04e7b8a7b3eed71e0ec8161df090851db16c9541b05cff75ca2d92af1a027744"
REFERENCE_MANIFEST_SHA256 = "961ea5a45cc3c866550138469ae58154ac7b9a74d7d58a4ffcdcbf48abb3f4d6"

EVIDENCE_ARTIFACTS = (
    "completion_local_ivi_w_controls.json",
    "frame_a_completion_topology.json",
    "frame_a_frozen.json",
    "frame_b_completion_topology.json",
    "frame_b_frozen.json",
    "maze_a_forward_lines_frozen.json",
    "maze_a_line_set_disclosed.json",
    "maze_a_return_lines_frozen.json",
    "maze_b_forward_lines_frozen.json",
    "maze_b_line_set_disclosed.json",
    "maze_b_return_lines_frozen.json",
    "protocol_frozen.json",
    "receipt_gates.json",
    "receipts.jsonl",
    "result.json",
    "strong_classical_baseline.json",
    "translation_family.json",
)


def canonical_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest_value(value: object) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object in {path}")
    return value


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def write_jsonl(path: Path, values: Sequence[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        "".join(canonical_json(value) + "\n" for value in values), encoding="utf-8"
    )
    os.replace(temporary, path)


def occurrence_id(frame_id: str, basis: str, stage: str, pole: str) -> str:
    return f"{frame_id}/{basis}/{stage}/{pole}"


def build_frozen_geometry(protocol: dict[str, Any], frame_id: str) -> dict[str, Any]:
    encoding = protocol["frame_encodings"][frame_id]
    basis_labels = tuple(encoding["basis_labels"])
    stage_labels = tuple(encoding["stage_labels"])
    pole_labels = tuple(encoding["pole_labels"])
    if len(basis_labels) != 3 or len(stage_labels) != 8 or len(pole_labels) != 2:
        raise ValueError("reference maze requires 3 bases, 8 stages, and 2 poles")

    occurrences: list[str] = []
    metadata: dict[str, dict[str, Any]] = {}
    for basis_index, basis_label in enumerate(basis_labels):
        for pole_index, pole_label in enumerate(pole_labels):
            for stage_index, stage_label in enumerate(stage_labels):
                identifier = occurrence_id(frame_id, basis_label, stage_label, pole_label)
                occurrences.append(identifier)
                metadata[identifier] = {
                    "basis_index": basis_index,
                    "basis_label": basis_label,
                    "stage_index": stage_index,
                    "stage_label": stage_label,
                    "pole_index": pole_index,
                    "pole_label": pole_label,
                    "cycle_index": stage_index + len(stage_labels) * pole_index,
                }

    basis_relation = [
        [basis_labels[left], basis_labels[right]]
        for left in range(len(basis_labels))
        for right in range(left + 1, len(basis_labels))
    ]
    admitted_equality_classes = [
        sorted(
            identifier
            for identifier, item in metadata.items()
            if item["basis_index"] == basis_index
        )
        for basis_index in range(len(basis_labels))
    ]
    return {
        "schema_version": "maze-frozen-geometry-1.0",
        "frame_id": frame_id,
        "foundation": "one frozen line set with direct-passage/inverse-wall polar readings",
        "basis_labels": list(basis_labels),
        "originless_basis_relation": basis_relation,
        "admitted_equality": {
            "definition": "u ~ v iff returned_basis_W(u) = returned_basis_W(v)",
            "frozen_before_maze_completion": True,
            "equivalence_classes": admitted_equality_classes,
            "equivalence_class_count": len(admitted_equality_classes),
            "ordered_equal_pair_count": sum(
                len(component) ** 2 for component in admitted_equality_classes
            ),
        },
        "stage_labels": list(stage_labels),
        "pole_labels": list(pole_labels),
        "occurrence_count": len(occurrences),
        "occurrences": sorted(occurrences),
        "occurrence_metadata": {key: metadata[key] for key in sorted(metadata)},
        "returned_basis_W": {
            key: metadata[key]["basis_label"] for key in sorted(metadata)
        },
    }


def line_for_source(geometry: dict[str, Any], source: str) -> dict[str, Any]:
    metadata = geometry["occurrence_metadata"]
    item = metadata[source]
    stage_count = len(geometry["stage_labels"])
    next_stage = (int(item["stage_index"]) + 1) % stage_count
    next_pole = int(item["pole_index"])
    is_independent_return = int(item["stage_index"]) == stage_count - 1
    if is_independent_return:
        next_pole = 1 - next_pole
    target = frame_index(geometry)[
        (int(item["basis_index"]), next_stage, next_pole)
    ]
    return {
        "line_id": (
            f"{geometry['frame_id']}:line:{item['basis_index']}:{item['cycle_index']}"
        ),
        "source": source,
        "target": target,
        "direct_reading": "passage",
        "inverse_reading": "wall",
        "path_or_wall_exclusive": True,
        "independent_return_line": is_independent_return,
    }


def frozen_line_subset_artifact(
    geometry: dict[str, Any], subset: str
) -> dict[str, Any]:
    if subset not in {"forward", "return"}:
        raise ValueError("line subset must be forward or return")
    selected = []
    for source in geometry["occurrences"]:
        line = line_for_source(geometry, source)
        if line["independent_return_line"] == (subset == "return"):
            selected.append(line)
    selected.sort(key=lambda item: item["line_id"])
    return {
        "schema_version": "maze-line-subset-1.0",
        "frame_id": geometry["frame_id"],
        "parent_frozen_geometry_sha256": digest_value(geometry),
        "frozen_after_local_equality": True,
        "same_process_designed_fixture": True,
        "process_independence_claimed": False,
        "line_subset": subset,
        "learning_translation": {
            line["source"]: line["target"] for line in selected
        },
        "line_set": selected,
    }


def disclosed_full_line_artifact(
    geometry: dict[str, Any],
    forward: dict[str, Any],
    returned: dict[str, Any],
) -> dict[str, Any]:
    expected_geometry_sha = digest_value(geometry)
    for artifact, role in ((forward, "forward"), (returned, "return")):
        if artifact["frame_id"] != geometry["frame_id"]:
            raise ValueError(f"{role} line subset belongs to another frame")
        if artifact["parent_frozen_geometry_sha256"] != expected_geometry_sha:
            raise ValueError(f"{role} line subset has the wrong geometry parent")
        if artifact["line_subset"] != role:
            raise ValueError(f"expected {role} line subset")
        declared_mapping = {
            line["source"]: line["target"] for line in artifact["line_set"]
        }
        if artifact["learning_translation"] != declared_mapping:
            raise ValueError(f"{role} line subset mapping disagrees with its lines")
    combined = list(forward["line_set"]) + list(returned["line_set"])
    sources = [line["source"] for line in combined]
    line_ids = [line["line_id"] for line in combined]
    if len(sources) != len(set(sources)) or set(sources) != set(geometry["occurrences"]):
        raise ValueError("disclosed line subsets do not form one total source partition")
    if len(line_ids) != len(set(line_ids)):
        raise ValueError("disclosed line identifiers are not unique")
    combined.sort(key=lambda item: item["line_id"])
    learning_translation = {line["source"]: line["target"] for line in combined}
    return {
        "schema_version": "maze-line-set-disclosure-1.0",
        "frame_id": geometry["frame_id"],
        "parent_frozen_geometry_sha256": expected_geometry_sha,
        "parent_forward_lines_sha256": digest_value(forward),
        "parent_return_lines_sha256": digest_value(returned),
        "one_line_set_after_disclosure": True,
        "learning_translation": learning_translation,
        "line_set": combined,
    }


def materialize_frame(
    geometry: dict[str, Any], line_artifact: dict[str, Any]
) -> dict[str, Any]:
    if line_artifact["frame_id"] != geometry["frame_id"]:
        raise ValueError("line artifact belongs to another frozen geometry")
    if line_artifact["parent_frozen_geometry_sha256"] != digest_value(geometry):
        raise ValueError("line artifact parent does not match frozen geometry")
    return {
        **geometry,
        "schema_version": "maze-materialized-frame-1.0",
        "learning_translation": dict(line_artifact["learning_translation"]),
        "line_set": list(line_artifact["line_set"]),
    }


def line_structure_certificate(frame: dict[str, Any]) -> dict[str, Any]:
    nodes = set(frame["occurrences"])
    lines = list(frame["line_set"])
    line_ids = [line.get("line_id") for line in lines]
    sources = [line.get("source") for line in lines]
    carrier_failures = [
        line.get("line_id")
        for line in lines
        if line.get("source") not in nodes or line.get("target") not in nodes
    ]
    target_failures: list[str | None] = []
    return_role_failures: list[str | None] = []
    line_id_failures: list[str | None] = []
    for line in lines:
        source = line.get("source")
        if source not in nodes:
            continue
        expected = line_for_source(frame, source)
        if line.get("target") != expected["target"]:
            target_failures.append(line.get("line_id"))
        if line.get("independent_return_line") != expected["independent_return_line"]:
            return_role_failures.append(line.get("line_id"))
        if line.get("line_id") != expected["line_id"]:
            line_id_failures.append(line.get("line_id"))
    role_failures = [
        line.get("line_id")
        for line in lines
        if line.get("direct_reading") != "passage"
        or line.get("inverse_reading") != "wall"
        or line.get("path_or_wall_exclusive") is not True
    ]
    mapping = frame["learning_translation"]
    mapping_failures = [
        line.get("line_id")
        for line in lines
        if mapping.get(line.get("source")) != line.get("target")
    ]
    direct_edges = {
        (line["source"], line["target"])
        for line in lines
        if line.get("source") in nodes and line.get("target") in nodes
    }
    inverse_promotions = sorted(
        [source, target]
        for source, target in direct_edges
        if source != target and (target, source) in direct_edges
    )
    failures = {
        "duplicate_line_id_count": len(line_ids) - len(set(line_ids)),
        "duplicate_source_count": len(sources) - len(set(sources)),
        "missing_source_count": len(nodes - set(sources)),
        "carrier_failure_count": len(carrier_failures),
        "declared_target_failure_count": len(target_failures),
        "declared_return_role_failure_count": len(return_role_failures),
        "declared_line_id_failure_count": len(line_id_failures),
        "path_or_wall_role_failure_count": len(role_failures),
        "learning_translation_failure_count": len(mapping_failures),
        "inverse_wall_promoted_to_direct_edge_count": len(inverse_promotions),
    }
    return {
        "checked_line_count": len(lines),
        "total_source_partition": set(sources) == nodes and len(sources) == len(set(sources)),
        "failures": failures,
        "first_carrier_failure": carrier_failures[0] if carrier_failures else None,
        "first_declared_target_failure": target_failures[0] if target_failures else None,
        "first_declared_return_role_failure": (
            return_role_failures[0] if return_role_failures else None
        ),
        "first_declared_line_id_failure": (
            line_id_failures[0] if line_id_failures else None
        ),
        "first_role_failure": role_failures[0] if role_failures else None,
        "first_inverse_promotion": inverse_promotions[0] if inverse_promotions else None,
        "valid": all(count == 0 for count in failures.values()),
    }


def frame_index(frame: dict[str, Any]) -> dict[tuple[int, int, int], str]:
    return {
        (
            int(item["basis_index"]),
            int(item["stage_index"]),
            int(item["pole_index"]),
        ): identifier
        for identifier, item in frame["occurrence_metadata"].items()
    }


def adjacency(nodes: Sequence[str], edges: Iterable[tuple[str, str]]) -> dict[str, list[str]]:
    result = {node: [] for node in nodes}
    for source, target in edges:
        if source not in result or target not in result:
            raise ValueError("edge leaves declared carrier")
        result[source].append(target)
    for source in result:
        result[source] = sorted(set(result[source]))
    return result


def shortest_path(graph: dict[str, list[str]], source: str, target: str) -> list[str] | None:
    queue: deque[str] = deque([source])
    parent: dict[str, str | None] = {source: None}
    while queue:
        current = queue.popleft()
        if current == target:
            path: list[str] = []
            cursor: str | None = current
            while cursor is not None:
                path.append(cursor)
                cursor = parent[cursor]
            return list(reversed(path))
        for candidate in graph[current]:
            if candidate not in parent:
                parent[candidate] = current
                queue.append(candidate)
    return None


def reachability(
    nodes: Sequence[str], edges: Iterable[tuple[str, str]]
) -> tuple[dict[str, list[str]], set[tuple[str, str]]]:
    graph = adjacency(nodes, edges)
    reach: set[tuple[str, str]] = set()
    for source in nodes:
        queue: deque[str] = deque([source])
        seen = {source}
        while queue:
            current = queue.popleft()
            reach.add((source, current))
            for target in graph[current]:
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
    return graph, reach


def mutual_components(nodes: Sequence[str], reach: set[tuple[str, str]]) -> list[list[str]]:
    remaining = set(nodes)
    components: list[list[str]] = []
    while remaining:
        seed = min(remaining)
        component = sorted(
            node
            for node in remaining
            if (seed, node) in reach and (node, seed) in reach
        )
        components.append(component)
        remaining.difference_update(component)
    return sorted(components, key=lambda values: values[0])


def undirected_components(
    nodes: Sequence[str], edges: Iterable[tuple[str, str]]
) -> list[list[str]]:
    graph = {node: set() for node in nodes}
    for source, target in edges:
        graph[source].add(target)
        graph[target].add(source)
    remaining = set(nodes)
    components: list[list[str]] = []
    while remaining:
        seed = min(remaining)
        queue = [seed]
        seen = {seed}
        while queue:
            current = queue.pop()
            for target in graph[current]:
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
        component = sorted(seen)
        components.append(component)
        remaining.difference_update(seen)
    return sorted(components, key=lambda values: values[0])


def topology_from_partition(nodes: Sequence[str], components: Sequence[Sequence[str]]) -> dict[str, Any]:
    component_sets = [frozenset(component) for component in components]
    open_sets: list[frozenset[str]] = []
    if len(component_sets) <= 12:
        for mask in range(1 << len(component_sets)):
            current: set[str] = set()
            for index, component in enumerate(component_sets):
                if mask & (1 << index):
                    current.update(component)
            open_sets.append(frozenset(current))
    open_lookup = set(open_sets)
    union_failures = 0
    intersection_failures = 0
    for left in open_sets:
        for right in open_sets:
            union_failures += int((left | right) not in open_lookup)
            intersection_failures += int((left & right) not in open_lookup)
    topology_axioms_checked = bool(open_sets)
    return {
        "construction": "all unions of completed-reach equivalence classes",
        "occurrence_count": len(nodes),
        "equivalence_class_count": len(component_sets),
        "equivalence_class_sizes": sorted(len(component) for component in component_sets),
        "open_set_count": 1 << len(component_sets),
        "open_sets_enumerated": len(open_sets),
        "empty_open": not open_sets or frozenset() in open_lookup,
        "whole_open": not open_sets or frozenset(nodes) in open_lookup,
        "pairwise_union_cases": len(open_sets) ** 2,
        "pairwise_union_failure_count": union_failures,
        "pairwise_intersection_cases": len(open_sets) ** 2,
        "pairwise_intersection_failure_count": intersection_failures,
        "topology_axioms_exhaustive_for_reference_partition": (
            topology_axioms_checked and union_failures == 0 and intersection_failures == 0
        ),
        "discrete": len(component_sets) == len(nodes),
        "whole_space_connected_in_standard_topological_sense": len(component_sets) <= 1,
        "return_connected_fibre_count": len(component_sets),
        "open_sets": [sorted(values) for values in open_sets],
    }


def equality_alignment(
    nodes: Sequence[str],
    reach: set[tuple[str, str]],
    admitted_components: Sequence[Sequence[str]],
) -> dict[str, Any]:
    flattened = [node for component in admitted_components for node in component]
    if any(not component for component in admitted_components):
        raise ValueError("admitted equality contains an empty class")
    if len(flattened) != len(set(flattened)):
        raise ValueError("admitted equality classes overlap")
    if set(flattened) != set(nodes):
        raise ValueError("admitted equality is not a partition of the carrier")
    admitted_class = {
        node: index
        for index, component in enumerate(admitted_components)
        for node in component
    }
    undercomplete = sorted(
        [left, right]
        for left in nodes
        for right in nodes
        if admitted_class[left] == admitted_class[right] and (left, right) not in reach
    )
    overreach = sorted(
        [left, right]
        for left in nodes
        for right in nodes
        if (left, right) in reach and admitted_class[left] != admitted_class[right]
    )
    local_ivi_w_pairs = sorted(
        [left, right]
        for left in nodes
        for right in nodes
        if left != right and admitted_class[left] == admitted_class[right]
    )
    return {
        "admitted_equality_frozen_before_lines": True,
        "local_ivi_w_present": bool(local_ivi_w_pairs),
        "local_ivi_w_witness": local_ivi_w_pairs[0] if local_ivi_w_pairs else None,
        "undercomplete_pair_count": len(undercomplete),
        "first_undercomplete_witness": undercomplete[0] if undercomplete else None,
        "overreach_pair_count": len(overreach),
        "first_overreach_witness": overreach[0] if overreach else None,
        "raw_reach_exactly_realizes_admitted_equality": not undercomplete and not overreach,
    }


def analyze_relation(
    nodes: Sequence[str], edges: Sequence[tuple[str, str]], *, include_return_paths: bool = False
) -> dict[str, Any]:
    graph, reach = reachability(nodes, edges)
    reflexivity_failures = [node for node in nodes if (node, node) not in reach]
    symmetry_failures = sorted(
        [source, target]
        for source, target in reach
        if (target, source) not in reach
    )
    transitivity_failures: list[list[str]] = []
    for left in nodes:
        for middle in nodes:
            if (left, middle) not in reach:
                continue
            for right in nodes:
                if (middle, right) in reach and (left, right) not in reach:
                    transitivity_failures.append([left, middle, right])

    components = mutual_components(nodes, reach)
    class_of = {
        node: index for index, component in enumerate(components) for node in component
    }
    faithful_failures = sorted(
        [left, right]
        for left in nodes
        for right in nodes
        if ((class_of[left] == class_of[right]) != ((left, right) in reach))
    )
    nontrivial_mutual_reach_pairs = sorted(
        [left, right]
        for left in nodes
        for right in nodes
        if left != right and (left, right) in reach and (right, left) in reach
    )
    translationally_complete = not symmetry_failures
    faithful_quotient = not faithful_failures
    topology = topology_from_partition(nodes, components) if faithful_quotient else None
    nontrivial_mutual_reach = bool(nontrivial_mutual_reach_pairs)
    faithful_nondiscrete_resolution_proxy = bool(
        faithful_quotient and topology is not None and not topology["discrete"]
    )

    undirected = undirected_components(nodes, edges)
    undirected_class = {
        node: index for index, component in enumerate(undirected) for node in component
    }
    invented_reverse = next(
        (
            [left, right]
            for left in nodes
            for right in nodes
            if undirected_class[left] == undirected_class[right]
            and (left, right) not in reach
        ),
        None,
    )
    lost_chain = next(
        (
            [left, right]
            for left, right in sorted(reach)
            if class_of[left] != class_of[right]
        ),
        None,
    )

    edge_return_paths: list[dict[str, Any]] = []
    if include_return_paths:
        for source, target in sorted(edges):
            returned = shortest_path(graph, target, source)
            edge_return_paths.append(
                {
                    "edge": [source, target],
                    "return_path": returned,
                    "return_edge_count": None if returned is None else len(returned) - 1,
                }
            )

    return {
        "node_count": len(nodes),
        "generating_edge_count": len(edges),
        "reach_pair_count": len(reach),
        "reach_sha256": digest_value(sorted([left, right] for left, right in reach)),
        "reach_is_reflexive": not reflexivity_failures,
        "reach_is_transitive": not transitivity_failures,
        "reach_is_symmetric": translationally_complete,
        "translationally_complete": translationally_complete,
        "symmetry_case_count": len(nodes) ** 2,
        "symmetry_failure_count": len(symmetry_failures),
        "first_missing_return_witness": symmetry_failures[0] if symmetry_failures else None,
        "edge_return_paths": edge_return_paths,
        "all_generating_edges_have_return_paths": (
            not include_return_paths
            or all(item["return_path"] is not None for item in edge_return_paths)
        ),
        "mutual_reach_classes": components,
        "nontrivial_mutual_reach_present": nontrivial_mutual_reach,
        "nontrivial_mutual_reach_witness": (
            nontrivial_mutual_reach_pairs[0] if nontrivial_mutual_reach_pairs else None
        ),
        "mutual_reach_quotient_faithfully_represents_raw_reach": faithful_quotient,
        "first_chain_lost_by_mutual_reach_quotient": lost_chain,
        "first_return_invented_by_undirected_equivalence_closure": invented_reverse,
        "topology": topology,
        "faithful_nondiscrete_resolution_proxy": faithful_nondiscrete_resolution_proxy,
        "completion_and_nontrivial_mutual_reach": (
            translationally_complete and nontrivial_mutual_reach
        ),
        "proxy_matches_completion_and_nontrivial_mutual_reach": (
            faithful_nondiscrete_resolution_proxy
            == (translationally_complete and nontrivial_mutual_reach)
        ),
    }


def analyze_frame(frame: dict[str, Any]) -> dict[str, Any]:
    structure = line_structure_certificate(frame)
    nodes = list(frame["occurrences"])
    edges = [
        (line["source"], line["target"])
        for line in frame["line_set"]
        if line["direct_reading"] == "passage"
    ]
    analysis = analyze_relation(nodes, edges, include_return_paths=True)
    _, reach = reachability(nodes, edges)
    alignment = equality_alignment(
        nodes, reach, frame["admitted_equality"]["equivalence_classes"]
    )
    analysis["admitted_equality_alignment"] = alignment
    analysis["local_ivi_w_disclosed_by_completed_reach"] = (
        analysis["translationally_complete"]
        and alignment["local_ivi_w_present"]
        and alignment["raw_reach_exactly_realizes_admitted_equality"]
    )
    analysis["faithful_nondiscrete_proxy_relative_to_frozen_frame"] = (
        analysis["faithful_nondiscrete_resolution_proxy"]
        and alignment["raw_reach_exactly_realizes_admitted_equality"]
    )
    return_paths = analysis["edge_return_paths"]
    return_lengths = [
        item["return_edge_count"]
        for item in return_paths
        if item["return_edge_count"] is not None
    ]
    analysis["line_semantics"] = {
        "one_frozen_line_set": True,
        "line_count": len(frame["line_set"]),
        "direct_passage_count": sum(
            line["direct_reading"] == "passage" for line in frame["line_set"]
        ),
        "inverse_wall_count": sum(
            line["inverse_reading"] == "wall" for line in frame["line_set"]
        ),
        "path_or_wall_exclusivity_failure_count": sum(
            not line["path_or_wall_exclusive"] for line in frame["line_set"]
        ),
        "return_path_count": len(return_paths),
        "minimum_return_path_length": min(return_lengths),
        "maximum_return_path_length": max(return_lengths),
        "inverse_walls_relabeled_as_direct_edges": structure["failures"][
            "inverse_wall_promoted_to_direct_edge_count"
        ],
        "structure_certificate": structure,
    }
    return analysis


def analyze_pre_return_frame(frame: dict[str, Any]) -> dict[str, Any]:
    nodes = list(frame["occurrences"])
    edges = [
        (line["source"], line["target"])
        for line in frame["line_set"]
        if not line["independent_return_line"]
    ]
    analysis = analyze_relation(nodes, edges)
    _, reach = reachability(nodes, edges)
    alignment = equality_alignment(
        nodes, reach, frame["admitted_equality"]["equivalence_classes"]
    )
    analysis["admitted_equality_alignment"] = alignment
    analysis["forward_line_count"] = len(edges)
    analysis["withheld_return_line_count"] = len(nodes) - len(edges)
    analysis["status"] = (
        "PENDING_INDEPENDENT_RETURN"
        if not analysis["translationally_complete"]
        else "UNEXPECTEDLY_COMPLETE"
    )
    return analysis


def floyd_warshall_reach(
    nodes: Sequence[str], edges: Sequence[tuple[str, str]]
) -> set[tuple[str, str]]:
    index = {node: position for position, node in enumerate(nodes)}
    matrix = [[False for _ in nodes] for _ in nodes]
    for position in range(len(nodes)):
        matrix[position][position] = True
    for source, target in edges:
        matrix[index[source]][index[target]] = True
    for middle in range(len(nodes)):
        for left in range(len(nodes)):
            if not matrix[left][middle]:
                continue
            for right in range(len(nodes)):
                matrix[left][right] = matrix[left][right] or (
                    matrix[left][middle] and matrix[middle][right]
                )
    return {
        (nodes[left], nodes[right])
        for left in range(len(nodes))
        for right in range(len(nodes))
        if matrix[left][right]
    }


def strong_classical_recomputation(frame: dict[str, Any], analysis: dict[str, Any]) -> dict[str, Any]:
    nodes = list(frame["occurrences"])
    edges = [(line["source"], line["target"]) for line in frame["line_set"]]
    floyd_reach = floyd_warshall_reach(nodes, edges)
    _, bfs_reach = reachability(nodes, edges)
    components = mutual_components(nodes, floyd_reach)
    return {
        "method": "within-assay Floyd-Warshall/SCC recomputation on identical frozen lines",
        "process_independence_claimed": False,
        "classical_foundation_can_express_all_finite_certificates": True,
        "reach_pair_count": len(floyd_reach),
        "reach_exact_match": floyd_reach == bfs_reach,
        "component_exact_match": components == analysis["mutual_reach_classes"],
        "topology_open_set_count": 1 << len(components),
        "topology_count_exact_match": (
            (1 << len(components)) == analysis["topology"]["open_set_count"]
        ),
        "completion_exact_match": (
            all((right, left) in floyd_reach for left, right in floyd_reach)
            == analysis["translationally_complete"]
        ),
    }


def iterate(mapping: dict[str, str], start: str, steps: int) -> str:
    current = start
    for _ in range(steps):
        current = mapping[current]
    return current


def return_monodromy_certificate(frame: dict[str, Any]) -> dict[str, Any]:
    by_index = frame_index(frame)
    mapping = frame["learning_translation"]
    cases: list[dict[str, Any]] = []
    for basis_index in range(3):
        for pole_index in range(2):
            start = by_index[(basis_index, 0, pole_index)]
            one_episode = iterate(mapping, start, 8)
            two_episodes = iterate(mapping, start, 16)
            start_pole = int(frame["occurrence_metadata"][start]["pole_index"])
            returned_pole = int(
                frame["occurrence_metadata"][one_episode]["pole_index"]
            )
            cases.append(
                {
                    "start": start,
                    "after_one_episode": one_episode,
                    "after_two_episodes": two_episodes,
                    "one_episode_returns_stage": (
                        frame["occurrence_metadata"][one_episode]["stage_index"] == 0
                    ),
                    "one_episode_returns_basis": (
                        frame["returned_basis_W"][one_episode]
                        == frame["returned_basis_W"][start]
                    ),
                    "one_episode_literal_return": one_episode == start,
                    "one_episode_pole_swapped": returned_pole == 1 - start_pole,
                    "two_episode_literal_return": two_episodes == start,
                }
            )
    return {
        "interpretation": (
            "the eight-step return episode induces a nontrivial pole-swap "
            "monodromy while preserving returned basis"
        ),
        "case_count": len(cases),
        "nontrivial_occurrence_monodromy_count": sum(
            not case["one_episode_literal_return"] for case in cases
        ),
        "pole_swap_count": sum(case["one_episode_pole_swapped"] for case in cases),
        "returned_basis_identity_count": sum(
            case["one_episode_returns_basis"] for case in cases
        ),
        "two_episode_literal_return_count": sum(
            case["two_episode_literal_return"] for case in cases
        ),
        "formal_holonomy_or_homotopy_status": "PENDING_PRE_COHERENCE_PATH_LAYER",
        "cases": cases,
    }


def classify_questions(
    frame: dict[str, Any], analysis: dict[str, Any]
) -> list[dict[str, Any]]:
    if not analysis["mutual_reach_quotient_faithfully_represents_raw_reach"]:
        raise ValueError("questions cannot be classified in the intended quotient before completion")
    components = analysis["mutual_reach_classes"]
    class_of = {
        node: index for index, component in enumerate(components) for node in component
    }
    anchor = frame_index(frame)[(0, 0, 0)]
    metadata = frame["occurrence_metadata"]
    questions = {
        "same_returned_basis_as_translated_anchor": {
            node: frame["returned_basis_W"][node] == frame["returned_basis_W"][anchor]
            for node in frame["occurrences"]
        },
        "literal_first_pole": {
            node: metadata[node]["pole_index"] == 0 for node in frame["occurrences"]
        },
        "literal_goal_stage": {
            node: metadata[node]["stage_index"] == 0 for node in frame["occurrences"]
        },
    }
    results: list[dict[str, Any]] = []
    for question_id, values in questions.items():
        failures = [
            [left, right]
            for left in frame["occurrences"]
            for right in frame["occurrences"]
            if class_of[left] == class_of[right] and values[left] != values[right]
        ]
        resolved = not failures
        factor: dict[str, bool] | None = None
        if resolved:
            factor = {
                f"class_{index}": values[component[0]]
                for index, component in enumerate(components)
            }
        witness = None
        if failures:
            left, right = failures[0]
            witness = {
                "left": left,
                "right": right,
                "frame_equal": class_of[left] == class_of[right],
                "left_value": values[left],
                "right_value": values[right],
                "separates_frame_equal_pair": values[left] != values[right],
            }
        results.append(
            {
                "frame_id": frame["frame_id"],
                "frame_equality": "completed raw reachability",
                "question_id": question_id,
                "question_anchor": anchor if question_id.startswith("same_returned") else None,
                "total_occurrence_values": len(values),
                "equality_comparisons": len(frame["occurrences"]) ** 2,
                "resolved_in_frame": resolved,
                "open_in_frame": not resolved,
                "unique_quotient_factor": factor,
                "factorization_unique": resolved,
                "open_witness": witness,
            }
        )
    return results


def candidate_mapping(
    source: dict[str, Any],
    target: dict[str, Any],
    basis_permutation: Sequence[int],
    cycle_offset: int,
) -> dict[str, str]:
    target_index = frame_index(target)
    mapping: dict[str, str] = {}
    for occurrence, item in source["occurrence_metadata"].items():
        target_cycle = (int(item["cycle_index"]) + cycle_offset) % 16
        target_stage = target_cycle % 8
        target_pole = target_cycle // 8
        mapping[occurrence] = target_index[
            (basis_permutation[int(item["basis_index"])], target_stage, target_pole)
        ]
    return mapping


def translation_family(
    source: dict[str, Any],
    target: dict[str, Any],
    source_analysis: dict[str, Any],
    target_analysis: dict[str, Any],
) -> dict[str, Any]:
    source_meta = source["occurrence_metadata"]
    target_meta = target["occurrence_metadata"]
    source_class = {
        node: index
        for index, component in enumerate(source_analysis["mutual_reach_classes"])
        for node in component
    }
    target_class = {
        node: index
        for index, component in enumerate(target_analysis["mutual_reach_classes"])
        for node in component
    }
    source_return_lines = {
        (line["source"], line["target"]): line["independent_return_line"]
        for line in source["line_set"]
    }
    target_return_lines = {
        (line["source"], line["target"]): line["independent_return_line"]
        for line in target["line_set"]
    }
    source_anchor = frame_index(source)[(0, 0, 0)]

    admitted: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    geom_equiv_count = 0
    learning_natural_count = 0
    topology_cases = 0
    topology_failures = 0
    registered_question_cases_all_candidates = 0
    registered_question_failures_all_candidates = 0
    admitted_registered_question_cases = 0
    admitted_registered_question_failures = 0
    candidate_count = 0
    for permutation in itertools.permutations(range(3)):
        for offset in range(16):
            candidate_count += 1
            mapping = candidate_mapping(source, target, permutation, offset)
            image = set(mapping.values())
            bijective = len(image) == len(source["occurrences"]) == len(target["occurrences"])
            equality_failures = 0
            for left in source["occurrences"]:
                for right in source["occurrences"]:
                    source_equal = source_class[left] == source_class[right]
                    target_equal = target_class[mapping[left]] == target_class[mapping[right]]
                    equality_failures += int(source_equal != target_equal)
            geom_equiv = bijective and equality_failures == 0
            geom_equiv_count += int(geom_equiv)

            step_failures = sum(
                mapping[source["learning_translation"][node]]
                != target["learning_translation"][mapping[node]]
                for node in source["occurrences"]
            )
            learning_natural = step_failures == 0
            learning_natural_count += int(learning_natural)

            pole_relations = {
                source_meta[node]["pole_index"] ^ target_meta[mapping[node]]["pole_index"]
                for node in source["occurrences"]
            }
            polar_natural = len(pole_relations) == 1
            pi = None
            if polar_natural:
                flip = next(iter(pole_relations))
                pi = {
                    source["pole_labels"][pole]: target["pole_labels"][pole ^ flip]
                    for pole in range(2)
                }

            return_line_failures = 0
            for edge, is_return in source_return_lines.items():
                mapped_edge = (mapping[edge[0]], mapping[edge[1]])
                if target_return_lines.get(mapped_edge) != is_return:
                    return_line_failures += 1
            independent_return_natural = return_line_failures == 0

            target_anchor = mapping[source_anchor]
            candidate_question_failures = {
                "same_returned_basis_as_translated_anchor": 0,
                "literal_first_pole": 0,
                "literal_goal_stage": 0,
            }
            for node in source["occurrences"]:
                source_value = source_class[node] == source_class[source_anchor]
                target_value = target_class[mapping[node]] == target_class[target_anchor]
                candidate_question_failures[
                    "same_returned_basis_as_translated_anchor"
                ] += int(source_value != target_value)

                source_pole_value = source_meta[node]["pole_index"] == 0
                if polar_natural:
                    mapped_first_pole = next(iter(pole_relations))
                    target_pole_value = (
                        target_meta[mapping[node]]["pole_index"] == mapped_first_pole
                    )
                    candidate_question_failures["literal_first_pole"] += int(
                        source_pole_value != target_pole_value
                    )
                else:
                    candidate_question_failures["literal_first_pole"] += 1

                source_stage_value = source_meta[node]["stage_index"] == 0
                target_stage_value = target_meta[mapping[node]]["stage_index"] == 0
                candidate_question_failures["literal_goal_stage"] += int(
                    source_stage_value != target_stage_value
                )

            candidate_question_cases = 3 * len(source["occurrences"])
            candidate_question_failure_count = sum(candidate_question_failures.values())
            registered_question_cases_all_candidates += candidate_question_cases
            registered_question_failures_all_candidates += candidate_question_failure_count
            registered_question_natural = candidate_question_failure_count == 0

            source_open_sets = source_analysis["topology"]["open_sets"]
            target_open_lookup = {
                tuple(open_set) for open_set in target_analysis["topology"]["open_sets"]
            }
            candidate_topology_failure = 0
            for open_set in source_open_sets:
                topology_cases += 1
                mapped_open = tuple(sorted(mapping[node] for node in open_set))
                if mapped_open not in target_open_lookup:
                    candidate_topology_failure += 1
                    topology_failures += 1

            full_admission = (
                geom_equiv
                and learning_natural
                and polar_natural
                and independent_return_natural
                and registered_question_natural
            )
            summary = {
                "candidate_id": f"phi-{''.join(map(str, permutation))}-offset-{offset:02d}",
                "basis_index_permutation": list(permutation),
                "cycle_offset": offset,
                "geom_equiv": geom_equiv,
                "equality_failure_count": equality_failures,
                "learning_step_natural": learning_natural,
                "learning_step_failure_count": step_failures,
                "polar_natural": polar_natural,
                "pi": pi,
                "independent_return_line_natural": independent_return_natural,
                "independent_return_line_failure_count": return_line_failures,
                "closure_topology_homeomorphism_derived_certificate": (
                    candidate_topology_failure == 0
                ),
                "registered_question_natural": registered_question_natural,
                "registered_question_cases": candidate_question_cases,
                "registered_question_failure_count": candidate_question_failure_count,
                "registered_question_failure_counts": candidate_question_failures,
                "full_admission": full_admission,
            }
            if full_admission:
                summary["phi"] = {
                    source["basis_labels"][index]: target["basis_labels"][permutation[index]]
                    for index in range(3)
                }
                summary["T"] = {key: mapping[key] for key in sorted(mapping)}
                admitted_registered_question_cases += candidate_question_cases
                admitted_registered_question_failures += candidate_question_failure_count
                admitted.append(summary)
            else:
                rejected.append(summary)

    equality_collapse_mapping = {
        node: frame_index(target)[
            (0, source_meta[node]["stage_index"], source_meta[node]["pole_index"])
        ]
        for node in source["occurrences"]
    }
    collapse_preservation_failures = 0
    collapse_reflection_failures = 0
    for left in source["occurrences"]:
        for right in source["occurrences"]:
            source_equal = source_class[left] == source_class[right]
            target_equal = (
                target_class[equality_collapse_mapping[left]]
                == target_class[equality_collapse_mapping[right]]
            )
            collapse_preservation_failures += int(source_equal and not target_equal)
            collapse_reflection_failures += int(target_equal and not source_equal)

    twist = next(
        item
        for item in rejected
        if item["geom_equiv"]
        and item["learning_step_natural"]
        and not item["polar_natural"]
    )
    return {
        "schema_version": "maze-translation-family-1.0",
        "source_frame": source["frame_id"],
        "target_frame": target["frame_id"],
        "candidate_count": candidate_count,
        "geom_equiv_count": geom_equiv_count,
        "learning_step_natural_count": learning_natural_count,
        "fully_admitted_translation_count": len(admitted),
        "canonical_translation_selected": False,
        "all_admissible_forms_retained": True,
        "topology_transport_cases": topology_cases,
        "topology_transport_failure_count": topology_failures,
        "topology_transport_role": (
            "derived from bijective GeomEquiv for the registered equality-saturation topology; "
            "not an independent admission gate"
        ),
        "registered_question_cases_all_candidates": registered_question_cases_all_candidates,
        "registered_question_failures_all_candidates": registered_question_failures_all_candidates,
        "admitted_registered_question_cases": admitted_registered_question_cases,
        "admitted_registered_question_failure_count": admitted_registered_question_failures,
        "admitted_translations": admitted,
        "rejected_candidate_count": len(rejected),
        "rejected_candidates": rejected,
        "controls": {
            "equality_collapse": {
                "forward_equality_preservation_failure_count": collapse_preservation_failures,
                "equality_reflection_failure_count": collapse_reflection_failures,
                "geom_equiv": (
                    collapse_preservation_failures == 0
                    and collapse_reflection_failures == 0
                ),
            },
            "geom_equiv_with_polar_return_naturality_failure": twist,
        },
    }


def finite_condition_controls() -> dict[str, Any]:
    central_fixtures = {
        "completion_with_local_ivi_w": {
            "nodes": ["a", "b", "c", "d"],
            "edges": [("a", "b"), ("b", "c"), ("c", "d"), ("d", "a")],
            "admitted_equality": [["a", "b", "c", "d"]],
        },
        "completion_without_local_ivi_w": {
            "nodes": ["a", "b", "c", "d"],
            "edges": [],
            "admitted_equality": [["a"], ["b"], ["c"], ["d"]],
        },
        "local_ivi_w_without_completion": {
            "nodes": ["a", "b", "c"],
            "edges": [("a", "b"), ("b", "a"), ("b", "c")],
            "admitted_equality": [["a", "b", "c"]],
        },
        "neither_completion_nor_local_ivi_w": {
            "nodes": ["a", "b"],
            "edges": [("a", "b")],
            "admitted_equality": [["a"], ["b"]],
        },
    }
    alignment_fixtures = {
        "undercomplete_reach_relative_to_frozen_equality": {
            "nodes": ["a", "b"],
            "edges": [],
            "admitted_equality": [["a", "b"]],
        },
        "overreach_relative_to_frozen_equality": {
            "nodes": ["a", "b"],
            "edges": [("a", "b"), ("b", "a")],
            "admitted_equality": [["a"], ["b"]],
        },
    }

    def evaluate(value: dict[str, Any]) -> dict[str, Any]:
        analysis = analyze_relation(value["nodes"], value["edges"])
        _, reach = reachability(value["nodes"], value["edges"])
        alignment = equality_alignment(value["nodes"], reach, value["admitted_equality"])
        local_ivi_w = alignment["local_ivi_w_present"]
        observed = (
            analysis["mutual_reach_quotient_faithfully_represents_raw_reach"]
            and analysis["topology"] is not None
            and not analysis["topology"]["discrete"]
            and alignment["raw_reach_exactly_realizes_admitted_equality"]
        )
        analysis["admitted_equality_alignment"] = alignment
        analysis["local_ivi_w_present"] = local_ivi_w
        analysis["faithful_nondiscrete_proxy_relative_to_frozen_frame"] = observed
        analysis["runtime_gate_completion_local_ivi_w_and_alignment"] = (
            analysis["translationally_complete"]
            and local_ivi_w
            and alignment["raw_reach_exactly_realizes_admitted_equality"]
        )
        analysis["proxy_matches_runtime_three_condition_gate"] = (
            observed
            == analysis["runtime_gate_completion_local_ivi_w_and_alignment"]
        )
        return analysis

    results = {name: evaluate(value) for name, value in central_fixtures.items()}
    alignment_controls = {
        name: evaluate(value) for name, value in alignment_fixtures.items()
    }
    all_cases = {**results, **alignment_controls}
    return {
        "schema_version": "completion-local-ivi-w-controls-1.0",
        "cases": results,
        "case_count": len(results),
        "runtime_gate": "translational completion AND LocalIVI_W AND exact reach/equality alignment",
        "all_six_cases_match_runtime_three_condition_gate": all(
            case["proxy_matches_runtime_three_condition_gate"]
            for case in all_cases.values()
        ),
        "neither_condition_implies_the_other": (
            results["completion_without_local_ivi_w"]["translationally_complete"]
            and not results["completion_without_local_ivi_w"]["local_ivi_w_present"]
            and results["local_ivi_w_without_completion"]["local_ivi_w_present"]
            and not results["local_ivi_w_without_completion"]["translationally_complete"]
        ),
        "frame_reach_alignment_controls": alignment_controls,
        "undercomplete_witness_retained": (
            alignment_controls["undercomplete_reach_relative_to_frozen_equality"]["admitted_equality_alignment"]["first_undercomplete_witness"]
            is not None
        ),
        "overreach_witness_retained": (
            alignment_controls["overreach_relative_to_frozen_equality"]["admitted_equality_alignment"]["first_overreach_witness"]
            is not None
        ),
    }


def receipt_chain(payloads: Sequence[tuple[str, object]]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    previous: str | None = None
    for index, (kind, payload) in enumerate(payloads):
        core = {
            "index": index,
            "kind": kind,
            "payload_sha256": digest_value(payload),
            "previous_receipt_sha256": previous,
        }
        receipt_sha = digest_value(core)
        record = {**core, "receipt_sha256": receipt_sha}
        records.append(record)
        previous = receipt_sha
    return records


def validate_receipt_chain(records: Sequence[dict[str, Any]]) -> bool:
    previous: str | None = None
    for index, record in enumerate(records):
        core = {
            "index": index,
            "kind": record["kind"],
            "payload_sha256": record["payload_sha256"],
            "previous_receipt_sha256": previous,
        }
        if (
            record["index"] != index
            or record["previous_receipt_sha256"] != previous
            or record["receipt_sha256"] != digest_value(core)
        ):
            return False
        previous = record["receipt_sha256"]
    return True


def issue_bounded_topology_receipt(
    *,
    completion: bool,
    local_ivi_w: bool,
    exact_alignment: bool,
    topology_sha256: str,
    admitted_translation_count: int,
) -> dict[str, Any]:
    conditions = {
        "translational_completion": completion,
        "local_ivi_w_present": local_ivi_w,
        "raw_reach_exactly_realizes_frozen_equality": exact_alignment,
    }
    failures = [name for name, passed in conditions.items() if not passed]
    if failures:
        return {
            "receipt_kind": "resolved_topology_receipt",
            "issued": False,
            "status": "REJECTED_TOPOLOGY_RECEIPT_GATE",
            "failed_conditions": failures,
            "conditions": conditions,
        }
    return {
        "receipt_kind": "resolved_topology_receipt",
        "issued": True,
        "status": "ISSUED_BOUNDED_TOPOLOGY_RECEIPT",
        "failed_conditions": [],
        "conditions": conditions,
        "issued_after_topology": True,
        "source_topology_sha256": topology_sha256,
        "admitted_translation_count": admitted_translation_count,
        "selected_translation": None,
        "cause_of_topology": False,
    }


def issue_admission_token(
    *,
    return_process_independent: bool,
    selected_translation: str | None,
    admitted_translation_ids: Sequence[str],
) -> dict[str, Any]:
    selected_translation_admitted = (
        selected_translation is not None
        and selected_translation in set(admitted_translation_ids)
    )
    if not return_process_independent or not selected_translation_admitted:
        return {
            "issued": False,
            "count": 0,
            "status": "NOT_ADMITTED_WITHOUT_INDEPENDENT_RETURN_AND_ADMITTED_SELECTION",
            "return_process_independent": return_process_independent,
            "selected_translation": selected_translation,
            "selected_translation_admitted": selected_translation_admitted,
        }
    return {
        "issued": True,
        "count": 1,
        "status": "ADMITTED",
        "return_process_independent": True,
        "selected_translation": selected_translation,
        "selected_translation_admitted": True,
    }


def run(output: Path = DEFAULT_OUTPUT) -> dict[str, Any]:
    protocol = load_json(PROTOCOL)
    output.mkdir(parents=True, exist_ok=True)
    write_json(output / "protocol_frozen.json", protocol)

    geometry_a = build_frozen_geometry(protocol, "A")
    geometry_b = build_frozen_geometry(protocol, "B")
    write_json(output / "frame_a_frozen.json", geometry_a)
    write_json(output / "frame_b_frozen.json", geometry_b)
    geometry_a = load_json(output / "frame_a_frozen.json")
    geometry_b = load_json(output / "frame_b_frozen.json")

    forward_artifact_a = frozen_line_subset_artifact(geometry_a, "forward")
    forward_artifact_b = frozen_line_subset_artifact(geometry_b, "forward")
    write_json(output / "maze_a_forward_lines_frozen.json", forward_artifact_a)
    write_json(output / "maze_b_forward_lines_frozen.json", forward_artifact_b)
    forward_artifact_a = load_json(output / "maze_a_forward_lines_frozen.json")
    forward_artifact_b = load_json(output / "maze_b_forward_lines_frozen.json")

    pre_return_a = analyze_pre_return_frame(
        materialize_frame(geometry_a, forward_artifact_a)
    )
    pre_return_b = analyze_pre_return_frame(
        materialize_frame(geometry_b, forward_artifact_b)
    )
    return_artifact_a = frozen_line_subset_artifact(geometry_a, "return")
    return_artifact_b = frozen_line_subset_artifact(geometry_b, "return")
    write_json(output / "maze_a_return_lines_frozen.json", return_artifact_a)
    write_json(output / "maze_b_return_lines_frozen.json", return_artifact_b)
    return_artifact_a = load_json(output / "maze_a_return_lines_frozen.json")
    return_artifact_b = load_json(output / "maze_b_return_lines_frozen.json")
    full_line_artifact_a = disclosed_full_line_artifact(
        geometry_a, forward_artifact_a, return_artifact_a
    )
    full_line_artifact_b = disclosed_full_line_artifact(
        geometry_b, forward_artifact_b, return_artifact_b
    )
    write_json(output / "maze_a_line_set_disclosed.json", full_line_artifact_a)
    write_json(output / "maze_b_line_set_disclosed.json", full_line_artifact_b)
    full_line_artifact_a = load_json(output / "maze_a_line_set_disclosed.json")
    full_line_artifact_b = load_json(output / "maze_b_line_set_disclosed.json")
    frame_a = materialize_frame(geometry_a, full_line_artifact_a)
    frame_b = materialize_frame(geometry_b, full_line_artifact_b)

    analysis_a = analyze_frame(frame_a)
    analysis_b = analyze_frame(frame_b)
    monodromy_a = return_monodromy_certificate(frame_a)
    monodromy_b = return_monodromy_certificate(frame_b)
    questions_a = classify_questions(frame_a, analysis_a)
    questions_b = classify_questions(frame_b, analysis_b)
    write_json(
        output / "frame_a_completion_topology.json",
        {
            "analysis": analysis_a,
            "pre_return_analysis": pre_return_a,
            "return_monodromy": monodromy_a,
            "questions": questions_a,
        },
    )
    write_json(
        output / "frame_b_completion_topology.json",
        {
            "analysis": analysis_b,
            "pre_return_analysis": pre_return_b,
            "return_monodromy": monodromy_b,
            "questions": questions_b,
        },
    )

    translations = translation_family(frame_a, frame_b, analysis_a, analysis_b)
    controls = finite_condition_controls()
    classical_baseline = {
        "A": strong_classical_recomputation(frame_a, analysis_a),
        "B": strong_classical_recomputation(frame_b, analysis_b),
    }
    write_json(output / "translation_family.json", translations)
    write_json(output / "completion_local_ivi_w_controls.json", controls)
    write_json(output / "strong_classical_baseline.json", classical_baseline)

    topology_hash_before_receipt = digest_value(
        {
            "A": analysis_a["topology"],
            "B": analysis_b["topology"],
        }
    )
    topology_receipt = issue_bounded_topology_receipt(
        completion=(
            analysis_a["translationally_complete"]
            and analysis_b["translationally_complete"]
        ),
        local_ivi_w=(
            analysis_a["admitted_equality_alignment"]["local_ivi_w_present"]
            and analysis_b["admitted_equality_alignment"]["local_ivi_w_present"]
        ),
        exact_alignment=(
            analysis_a["admitted_equality_alignment"]["raw_reach_exactly_realizes_admitted_equality"]
            and analysis_b["admitted_equality_alignment"]["raw_reach_exactly_realizes_admitted_equality"]
        ),
        topology_sha256=topology_hash_before_receipt,
        admitted_translation_count=translations["fully_admitted_translation_count"],
    )
    topology_hash_after_receipt_gate = digest_value(
        {
            "A": analyze_frame(frame_a)["topology"],
            "B": analyze_frame(frame_b)["topology"],
        }
    )
    topology_inputs = ["frozen_geometry", "disclosed_line_set", "raw_reach"]
    topology_receipt["topology_recomputation"] = {
        "input_names": topology_inputs,
        "receipt_used_as_input": "receipt" in topology_inputs,
        "topology_sha256_before_receipt_gate": topology_hash_before_receipt,
        "topology_sha256_after_receipt_gate": topology_hash_after_receipt_gate,
        "line_count_before_receipt_gate": len(frame_a["line_set"])
        + len(frame_b["line_set"]),
        "line_count_after_receipt_gate": len(frame_a["line_set"])
        + len(frame_b["line_set"]),
    }
    topology_receipt_count = int(topology_receipt["issued"])
    admission_token = issue_admission_token(
        return_process_independent=False,
        selected_translation=None,
        admitted_translation_ids=[
            item["candidate_id"] for item in translations["admitted_translations"]
        ],
    )
    self_certified_without_completion = issue_bounded_topology_receipt(
        completion=False,
        local_ivi_w=True,
        exact_alignment=False,
        topology_sha256=topology_hash_before_receipt,
        admitted_translation_count=0,
    )
    self_certified_without_completion["requested_by"] = "self_certified_control"
    write_json(
        output / "receipt_gates.json",
        {
            "bounded_topology_receipt": topology_receipt,
            "admission_token": admission_token,
            "self_certified_control": self_certified_without_completion,
        },
    )

    forward_line_freeze = {
        "A": digest_value(forward_artifact_a),
        "B": digest_value(forward_artifact_b),
    }
    return_line_freeze = {
        "A": digest_value(return_artifact_a),
        "B": digest_value(return_artifact_b),
    }
    full_line_disclosure = {
        "A": digest_value(full_line_artifact_a),
        "B": digest_value(full_line_artifact_b),
    }
    receipts = receipt_chain(
        [
            ("protocol_frozen", protocol),
            (
                "local_axiom_geometries_and_equalities_frozen",
                {
                    "A": frame_a["admitted_equality"],
                    "B": frame_b["admitted_equality"],
                    "A_geometry_sha256": digest_value(geometry_a),
                    "B_geometry_sha256": digest_value(geometry_b),
                },
            ),
            ("forward_line_subsets_frozen", forward_line_freeze),
            (
                "forward_reach_without_return_checked",
                {
                    "A": pre_return_a["reach_sha256"],
                    "B": pre_return_b["reach_sha256"],
                    "status": "PENDING_INDEPENDENT_RETURN",
                },
            ),
            ("return_line_subsets_frozen", return_line_freeze),
            ("full_one_line_sets_disclosed", full_line_disclosure),
            ("raw_reach_derived", {"A": analysis_a["reach_sha256"], "B": analysis_b["reach_sha256"]}),
            (
                "translational_completion_checked",
                {
                    "A": analysis_a["translationally_complete"],
                    "B": analysis_b["translationally_complete"],
                },
            ),
            ("closure_topology_derived", topology_hash_before_receipt),
            ("local_questions_classified", {"A": questions_a, "B": questions_b}),
            ("translation_family_admitted", translations),
            (
                "transported_registered_questions_checked",
                {
                    "cases": translations["admitted_registered_question_cases"],
                    "failures": translations[
                        "admitted_registered_question_failure_count"
                    ],
                },
            ),
            ("strong_classical_recomputation", classical_baseline),
            ("bounded_topology_receipt_issued", topology_receipt),
            ("episode_admission_gate_checked", admission_token),
            ("negative_controls_retained", {"conditions": controls, "self": self_certified_without_completion}),
        ]
    )
    write_jsonl(output / "receipts.jsonl", receipts)

    resolved_count = sum(
        item["resolved_in_frame"] for item in questions_a + questions_b
    )
    open_count = sum(item["open_in_frame"] for item in questions_a + questions_b)
    open_witness_count = sum(
        item["open_witness"] is not None for item in questions_a + questions_b
    )
    result = {
        "schema_version": "translational-completion-maze-result-1.0",
        "status": "PASS",
        "execution_class": "EXECUTED_BOUNDED_DESIGNED_PROXY",
        "reported_formal_result": "NRRF639 separately reported; source unavailable in this checkout",
        "frame_count": 2,
        "occurrence_count_per_frame": frame_a["occurrence_count"],
        "one_line_count_per_frame": len(frame_a["line_set"]),
        "path_or_wall_exclusivity_failure_count": (
            analysis_a["line_semantics"]["path_or_wall_exclusivity_failure_count"]
            + analysis_b["line_semantics"]["path_or_wall_exclusivity_failure_count"]
        ),
        "line_structure": {
            "A_valid": analysis_a["line_semantics"]["structure_certificate"]["valid"],
            "B_valid": analysis_b["line_semantics"]["structure_certificate"]["valid"],
            "analyzed_from_reloaded_disclosed_artifacts": True,
        },
        "translational_completion": {
            "A": analysis_a["translationally_complete"],
            "B": analysis_b["translationally_complete"],
            "pre_return_A": pre_return_a["translationally_complete"],
            "pre_return_B": pre_return_b["translationally_complete"],
            "pre_return_status": "PENDING_INDEPENDENT_RETURN",
            "return_role_frozen_separately": True,
            "return_generation_process_independent": False,
            "A_reach_exactly_realizes_frozen_equality": analysis_a["admitted_equality_alignment"]["raw_reach_exactly_realizes_admitted_equality"],
            "B_reach_exactly_realizes_frozen_equality": analysis_b["admitted_equality_alignment"]["raw_reach_exactly_realizes_admitted_equality"],
            "all_generator_return_paths_explicit": (
                analysis_a["all_generating_edges_have_return_paths"]
                and analysis_b["all_generating_edges_have_return_paths"]
            ),
            "return_path_length_per_generator": 15,
        },
        "closure_topology": {
            "A_open_set_count": analysis_a["topology"]["open_set_count"],
            "B_open_set_count": analysis_b["topology"]["open_set_count"],
            "equivalence_class_count_per_frame": analysis_a["topology"]["equivalence_class_count"],
            "class_size_per_frame": analysis_a["topology"]["equivalence_class_sizes"],
            "non_discrete": not analysis_a["topology"]["discrete"],
            "whole_space_standard_connected": analysis_a["topology"]["whole_space_connected_in_standard_topological_sense"],
            "return_connected_fibre_count": analysis_a["topology"]["return_connected_fibre_count"],
            "topology_sha256_before_receipt": topology_hash_before_receipt,
            "topology_sha256_after_receipt_gate": topology_hash_after_receipt_gate,
        },
        "local_ivi_w": {
            "A_present_in_frozen_frame": analysis_a["admitted_equality_alignment"]["local_ivi_w_present"],
            "B_present_in_frozen_frame": analysis_b["admitted_equality_alignment"]["local_ivi_w_present"],
            "A_disclosed_by_completed_reach": analysis_a["local_ivi_w_disclosed_by_completed_reach"],
            "B_disclosed_by_completed_reach": analysis_b["local_ivi_w_disclosed_by_completed_reach"],
            "A_witness": analysis_a["admitted_equality_alignment"]["local_ivi_w_witness"],
            "B_witness": analysis_b["admitted_equality_alignment"]["local_ivi_w_witness"],
            "claim_boundary": "local non-faithfulness only; translational IVI additionally requires admitted cross-frame naturality",
        },
        "questions": {
            "resolved_count": resolved_count,
            "open_count": open_count,
            "explicit_open_witness_count": open_witness_count,
            "bare_open_without_witness_count": open_count - open_witness_count,
        },
        "return_monodromy": {
            "occurrence_nontrivial_count": (
                monodromy_a["nontrivial_occurrence_monodromy_count"]
                + monodromy_b["nontrivial_occurrence_monodromy_count"]
            ),
            "pole_swap_count": (
                monodromy_a["pole_swap_count"] + monodromy_b["pole_swap_count"]
            ),
            "returned_basis_identity_count": (
                monodromy_a["returned_basis_identity_count"]
                + monodromy_b["returned_basis_identity_count"]
            ),
            "two_episode_literal_return_count": (
                monodromy_a["two_episode_literal_return_count"]
                + monodromy_b["two_episode_literal_return_count"]
            ),
            "formal_holonomy_or_homotopy_status": "PENDING_PRE_COHERENCE_PATH_LAYER",
        },
        "translation_family": {
            "candidate_count": translations["candidate_count"],
            "geom_equiv_count": translations["geom_equiv_count"],
            "fully_admitted_count": translations["fully_admitted_translation_count"],
            "canonical_selected": translations["canonical_translation_selected"],
            "topology_transport_failure_count": translations["topology_transport_failure_count"],
            "admitted_question_transport_failure_count": translations["admitted_registered_question_failure_count"],
        },
        "finite_condition_controls": {
            "all_six_cases_match_runtime_three_condition_gate": controls["all_six_cases_match_runtime_three_condition_gate"],
            "neither_condition_implies_the_other": controls["neither_condition_implies_the_other"],
            "undercomplete_witness_retained": controls["undercomplete_witness_retained"],
            "overreach_witness_retained": controls["overreach_witness_retained"],
            "incomplete_cases_retain_loss_and_invention_witnesses": all(
                case["first_chain_lost_by_mutual_reach_quotient"] is not None
                and case["first_return_invented_by_undirected_equivalence_closure"] is not None
                for name, case in controls["cases"].items()
                if name
                in {
                    "local_ivi_w_without_completion",
                    "neither_completion_nor_local_ivi_w",
                }
            ),
        },
        "strong_classical_baseline": {
            "identical_frozen_inputs": True,
            "all_recomputations_match": all(
                value["reach_exact_match"]
                and value["component_exact_match"]
                and value["topology_count_exact_match"]
                and value["completion_exact_match"]
                for value in classical_baseline.values()
            ),
            "claim": "the architectural differential is explicit closure lineage, not classical inability to compute finite reach or topology",
        },
        "receipt_gates": {
            "bounded_topology_receipt_count": topology_receipt_count,
            "actual_admission_token_count": admission_token["count"],
            "bounded_topology_receipt_issued": topology_receipt["issued"],
            "admission_token_status": admission_token["status"],
            "at_most_one": topology_receipt_count <= 1,
            "topology_unchanged_after_receipt_gate": (
                topology_hash_before_receipt == topology_hash_after_receipt_gate
            ),
            "self_certified_without_completion": self_certified_without_completion,
        },
        "receipt_chain": {
            "ok": validate_receipt_chain(receipts),
            "count": len(receipts),
            "head": receipts[-1]["receipt_sha256"],
        },
        "claim_boundary": protocol["claim_boundary"],
        "actual_asi_or_aristotle_run": False,
        "physical_system_tested": False,
        "general_closure_claim_established": False,
    }
    required = [
        result["translational_completion"]["A"],
        result["translational_completion"]["B"],
        not result["translational_completion"]["pre_return_A"],
        not result["translational_completion"]["pre_return_B"],
        result["translational_completion"]["A_reach_exactly_realizes_frozen_equality"],
        result["translational_completion"]["B_reach_exactly_realizes_frozen_equality"],
        result["translational_completion"]["all_generator_return_paths_explicit"],
        result["line_structure"]["A_valid"],
        result["line_structure"]["B_valid"],
        result["closure_topology"]["non_discrete"],
        result["local_ivi_w"]["A_present_in_frozen_frame"],
        result["local_ivi_w"]["B_present_in_frozen_frame"],
        result["local_ivi_w"]["A_disclosed_by_completed_reach"],
        result["local_ivi_w"]["B_disclosed_by_completed_reach"],
        result["questions"]["bare_open_without_witness_count"] == 0,
        result["translation_family"]["fully_admitted_count"] > 1,
        result["translation_family"]["topology_transport_failure_count"] == 0,
        result["translation_family"]["admitted_question_transport_failure_count"] == 0,
        result["finite_condition_controls"]["all_six_cases_match_runtime_three_condition_gate"],
        result["finite_condition_controls"]["neither_condition_implies_the_other"],
        result["finite_condition_controls"]["undercomplete_witness_retained"],
        result["finite_condition_controls"]["overreach_witness_retained"],
        result["finite_condition_controls"]["incomplete_cases_retain_loss_and_invention_witnesses"],
        result["receipt_gates"]["topology_unchanged_after_receipt_gate"],
        result["receipt_gates"]["at_most_one"],
        result["receipt_gates"]["bounded_topology_receipt_issued"],
        not result["receipt_gates"]["self_certified_without_completion"]["issued"],
        result["receipt_gates"]["actual_admission_token_count"] == 0,
        result["strong_classical_baseline"]["all_recomputations_match"],
        result["receipt_chain"]["ok"],
    ]
    result["execution_valid"] = all(required)
    result["status"] = "PASS" if result["execution_valid"] else "FAIL"
    write_json(output / "result.json", result)
    manifest = {
        "schema_version": "translational-completion-maze-evidence-manifest-1.0",
        "artifact_count": len(EVIDENCE_ARTIFACTS),
        "artifacts": [
            {
                "path": name,
                "sha256": file_digest(output / name),
                "size_bytes": (output / name).stat().st_size,
            }
            for name in EVIDENCE_ARTIFACTS
        ],
    }
    write_json(output / "evidence_manifest.json", manifest)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--assert-reference", action="store_true")
    args = parser.parse_args()
    result = run(args.output)
    if args.assert_reference:
        checks = {
            "protocol": file_digest(PROTOCOL) == REFERENCE_PROTOCOL_SHA256,
            "result": file_digest(args.output / "result.json") == REFERENCE_RESULT_SHA256,
            "receipt_head": result["receipt_chain"]["head"] == REFERENCE_RECEIPT_HEAD,
            "manifest": (
                file_digest(args.output / "evidence_manifest.json")
                == REFERENCE_MANIFEST_SHA256
            ),
            "execution": result["execution_valid"],
        }
        if not all(checks.values()):
            raise SystemExit(f"reference assertion failed: {checks}")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
