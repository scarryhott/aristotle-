"""Derive relative trading signals and leave the execution command open to closure.

This overlay removes the hand-authored PLUS/MINUS labels, fixed USD notionals, and the
price-to-ZMod phase rule from the executable signal path.  For every identified public-book
round it:

* derives the directed asset graph from the validated books;
* enumerates every simple closed route in that graph;
* derives one maximal zero-hair depth partition for each route;
* reads action potential, global hair, and completed flow as dimensionless relative returns;
* selects only a unique positive leader relative to every simultaneously derived route; and
* keeps the command OPEN because public observations do not contain private execution authority.

The raw observations, the declared fee translation, and execution authority are interface inputs.
They are not manufactured by the closure.  This program is a replay-only paper derivation and has
no order-submission operation.
"""

from __future__ import annotations

import argparse
import bisect
import json
from dataclasses import dataclass
from decimal import Decimal, localcontext
from pathlib import Path, PurePosixPath
from typing import Iterable, Mapping, Sequence

try:
    from experiments import nrrf767_live_paper_trading_bot as source_bot
except ModuleNotFoundError as import_error:
    if import_error.name != "experiments":
        raise
    import nrrf767_live_paper_trading_bot as source_bot


SCHEMA_VERSION = "nrrf805.relativistic_signal_open_command.v1"
RUN_KIND = "IMMUTABLE_RELATIVISTIC_SIGNAL_OPEN_COMMAND"
EVENT_KIND = "RELATIVISTIC_SIGNAL_ROUND"
ARITHMETIC_PRECISION = 180
ZERO = Decimal(0)
ONE = Decimal(1)
TEN_THOUSAND = Decimal(10_000)
IDENTITY_TOLERANCE = Decimal("1e-90")
PARTITION_DERIVATION = "MAXIMIZING_EQUIVALENCE_CLASS_OVER_ALL_OBSERVED_DEPTH_BREAKPOINTS"
SELECTION_DERIVATION = "UNIQUE_POSITIVE_MAXIMUM_OF_RELATIVE_COMPLETED_RETURNS"
EQUATION = "completed_return = action_potential_return - global_hair_return"
BOUNDARY = {
    "paper_derivation_only": True,
    "private_execution_authority_present": False,
    "orders_submitted": 0,
    "authenticated_fills": 0,
    "authenticated_settled_pnl": None,
    "profit_claimed": False,
}

SOURCE_BINDING_FIELDS = {
    "source_manifest_sha256",
    "source_events_sha256",
    "source_final_event_hash",
}
EDGE_FIELDS = {
    "edge_id",
    "input_asset",
    "output_asset",
    "market",
    "operation",
}
CANDIDATE_FIELDS = {
    "route_id",
    "route_class_id",
    "path",
    "reciprocal_route_id",
    "reciprocal_route_class_id",
    "partition_derivation",
    "start_asset",
    "start_amount",
    "edges",
    "zero_hair_final_amount",
    "cost_completed_final_amount",
    "action_potential_return",
    "global_hair_return",
    "completed_return",
    "completed_return_bps",
    "relative_gap_to_best_bps",
    "closure_identity_error",
    "full_depth_zero_hair",
    "full_depth_cost_completed",
}
COMMAND_FIELDS = {
    "state",
    "observation_closure",
    "topology_closure",
    "signal_closure",
    "selection_derivation",
    "selected_route_class_id",
    "selected_route_id",
    "selected_partition_start_amount",
    "execution_authority_closure",
    "missing_closures",
    "orders_submitted",
}
EVENT_FIELDS = {
    "schema_version",
    "event_kind",
    "round_index",
    "source_event_hash",
    "asset_graph",
    "candidates",
    "command",
    "boundary",
    "previous_event_hash",
    "event_hash",
}
MANIFEST_FIELDS = {
    "schema_version",
    "run_kind",
    "equation",
    "partition_derivation",
    "selection_derivation",
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


@dataclass(frozen=True)
class DirectedEdge:
    input_asset: str
    output_asset: str
    market: str
    operation: str
    book: source_bot.Book

    def __post_init__(self) -> None:
        if self.operation not in {"buy", "sell"}:
            raise ValueError("edge operation must be buy or sell")
        expected = (
            (self.book.quote, self.book.base)
            if self.operation == "buy"
            else (self.book.base, self.book.quote)
        )
        if (self.input_asset, self.output_asset) != expected:
            raise ValueError("edge assets do not match its book operation")

    @property
    def edge_id(self) -> str:
        return f"{self.input_asset}>{self.output_asset}@{self.market}:{self.operation}"

    def as_dict(self) -> dict[str, object]:
        value = {
            "edge_id": self.edge_id,
            "input_asset": self.input_asset,
            "output_asset": self.output_asset,
            "market": self.market,
            "operation": self.operation,
        }
        if set(value) != EDGE_FIELDS:
            raise AssertionError("edge schema drift")
        return value


@dataclass(frozen=True)
class EdgeCurve:
    """The exact piecewise-linear depth translation carried by one directed edge."""

    edge: DirectedEdge
    cumulative_input: tuple[Decimal, ...]
    cumulative_gross_output: tuple[Decimal, ...]
    output_per_input: tuple[Decimal, ...]

    @classmethod
    def derive(cls, edge: DirectedEdge) -> "EdgeCurve":
        inputs: list[Decimal] = []
        outputs: list[Decimal] = []
        slopes: list[Decimal] = []
        input_total = ZERO
        output_total = ZERO
        levels = edge.book.asks if edge.operation == "buy" else edge.book.bids
        with localcontext() as context:
            context.prec = ARITHMETIC_PRECISION
            for price, amount in levels:
                input_increment = price * amount if edge.operation == "buy" else amount
                output_increment = amount if edge.operation == "buy" else price * amount
                input_total += input_increment
                output_total += output_increment
                inputs.append(input_total)
                outputs.append(output_total)
                slopes.append(output_increment / input_increment)
        return cls(edge, tuple(inputs), tuple(outputs), tuple(slopes))

    @property
    def input_capacity(self) -> Decimal:
        return self.cumulative_input[-1]

    def gross_output(self, value: Decimal) -> tuple[Decimal, bool]:
        if value < 0:
            raise ValueError("edge input is negative")
        if value > self.input_capacity:
            return self.cumulative_gross_output[-1], False
        index = bisect.bisect_left(self.cumulative_input, value)
        previous_input = self.cumulative_input[index - 1] if index else ZERO
        previous_output = self.cumulative_gross_output[index - 1] if index else ZERO
        with localcontext() as context:
            context.prec = ARITHMETIC_PRECISION
            output = previous_output + (value - previous_input) * self.output_per_input[index]
        return output, True

    def input_for_gross_output_limit(self, output_limit: Decimal) -> Decimal:
        if output_limit < 0:
            raise ValueError("gross output limit is negative")
        if output_limit >= self.cumulative_gross_output[-1]:
            return self.input_capacity
        index = bisect.bisect_left(self.cumulative_gross_output, output_limit)
        previous_input = self.cumulative_input[index - 1] if index else ZERO
        previous_output = self.cumulative_gross_output[index - 1] if index else ZERO
        with localcontext() as context:
            context.prec = ARITHMETIC_PRECISION
            return previous_input + (output_limit - previous_output) / self.output_per_input[index]


def canonical_json_bytes(value: object) -> bytes:
    return source_bot.canonical_json_bytes(value)


def sha256_bytes(value: bytes) -> str:
    return source_bot.sha256_bytes(value)


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def decimal_text(value: Decimal) -> str:
    if not value.is_finite():
        raise ValueError("non-finite decimal")
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    return text or "0"


def parse_decimal(value: object) -> Decimal:
    if not isinstance(value, str):
        raise ValueError("expected decimal string")
    parsed = Decimal(value)
    if not parsed.is_finite():
        raise ValueError("non-finite decimal string")
    return parsed


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def read_json_object(path: Path) -> dict[str, object]:
    value = source_bot.strict_json_loads(path.read_bytes())
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def read_events(path: Path) -> list[dict[str, object]]:
    raw = path.read_bytes()
    if not raw or not raw.endswith(b"\n") or b"\n\n" in raw:
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


def source_binding(source_run: Path) -> dict[str, object]:
    source_bot.verify_run(source_run)
    manifest = read_json_object(source_run / "manifest.json")
    binding = {
        "source_manifest_sha256": sha256_file(source_run / "manifest.json"),
        "source_events_sha256": manifest["events_sha256"],
        "source_final_event_hash": manifest["final_event_hash"],
    }
    if set(binding) != SOURCE_BINDING_FIELDS:
        raise AssertionError("source binding schema drift")
    return binding


def safe_source_file(source_run: Path, relative: object) -> Path:
    if not isinstance(relative, str):
        raise ValueError("source raw file is not a string")
    pure = PurePosixPath(relative)
    if pure.is_absolute() or ".." in pure.parts or pure.as_posix() != relative:
        raise ValueError("unsafe source raw path")
    path = source_run.joinpath(*pure.parts)
    if not path.is_file():
        raise ValueError("source raw file is missing")
    return path


def books_from_event(
    event: Mapping[str, object], source_run: Path, config: source_bot.PaperConfig
) -> dict[str, source_bot.Book]:
    capture = event.get("capture")
    if not isinstance(capture, dict):
        raise ValueError("source capture is not an object")
    books: dict[str, source_bot.Book] = {}
    for name in source_bot.PAIR_ORDER:
        record = capture.get(name)
        if not isinstance(record, dict):
            raise ValueError("source capture record is missing")
        raw_file = record.get("raw_file")
        raw = safe_source_file(source_run, raw_file).read_bytes() if raw_file is not None else None
        receipt = source_bot.receipt_from_record(record, raw)
        book, _metadata = source_bot.parse_public_book(receipt, config)
        if book is not None:
            books[name] = book
    return books


def derive_edges(books: Mapping[str, source_bot.Book]) -> tuple[DirectedEdge, ...]:
    edges: list[DirectedEdge] = []
    for name in sorted(books):
        book = books[name]
        edges.extend(
            (
                DirectedEdge(book.quote, book.base, name, "buy", book),
                DirectedEdge(book.base, book.quote, name, "sell", book),
            )
        )
    return tuple(sorted(edges, key=lambda edge: edge.edge_id))


def enumerate_simple_cycles(edges: Sequence[DirectedEdge]) -> tuple[tuple[DirectedEdge, ...], ...]:
    """Return every rooted directed simple cycle, including two-edge spread loops."""

    assets = sorted({edge.input_asset for edge in edges} | {edge.output_asset for edge in edges})
    outgoing = {
        asset: tuple(sorted((edge for edge in edges if edge.input_asset == asset), key=lambda e: e.edge_id))
        for asset in assets
    }
    cycles: list[tuple[DirectedEdge, ...]] = []
    for root in assets:
        def visit(current: str, visited: frozenset[str], path: tuple[DirectedEdge, ...]) -> None:
            for edge in outgoing[current]:
                if edge.output_asset == root:
                    if len(path) + 1 >= 2:
                        cycles.append((*path, edge))
                elif edge.output_asset not in visited and len(visited) < len(assets):
                    visit(edge.output_asset, visited | {edge.output_asset}, (*path, edge))

        visit(root, frozenset({root}), ())
    unique = {tuple(edge.edge_id for edge in cycle): cycle for cycle in cycles}
    return tuple(unique[key] for key in sorted(unique))


def route_assets(route: Sequence[DirectedEdge]) -> tuple[str, ...]:
    if not route:
        raise ValueError("route must be nonempty")
    assets = [route[0].input_asset]
    for edge in route:
        if assets[-1] != edge.input_asset:
            raise ValueError("route edges are not composable")
        assets.append(edge.output_asset)
    if assets[0] != assets[-1]:
        raise ValueError("route is not closed")
    return tuple(assets)


def route_id(route: Sequence[DirectedEdge]) -> str:
    return ">".join(route_assets(route))


def reciprocal_route_id(route: Sequence[DirectedEdge]) -> str:
    assets = route_assets(route)
    return ">".join((assets[0], *reversed(assets[1:-1]), assets[0]))


def route_class_id_from_assets(assets: Sequence[str]) -> str:
    """Quotient a closed route by change of starting asset, preserving orientation."""

    if len(assets) < 3 or assets[0] != assets[-1]:
        raise ValueError("route class requires a closed route")
    core = tuple(assets[:-1])
    rotations = tuple(core[index:] + core[:index] for index in range(len(core)))
    representative = min(rotations)
    return ">".join((*representative, representative[0]))


def route_class_id(route: Sequence[DirectedEdge]) -> str:
    return route_class_id_from_assets(route_assets(route))


def reciprocal_route_class_id(route: Sequence[DirectedEdge]) -> str:
    assets = route_assets(route)
    reciprocal = (assets[0], *reversed(assets[1:-1]), assets[0])
    return route_class_id_from_assets(reciprocal)


def input_for_net_output_limit(
    curve: EdgeCurve, output_limit: Decimal, fee_rate: Decimal
) -> Decimal:
    """Largest edge input whose net output does not exceed ``output_limit``."""

    if output_limit < 0 or not output_limit.is_finite():
        raise ValueError("output limit must be finite and nonnegative")
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        retained = ONE - fee_rate
        if retained <= 0:
            raise ValueError("fee leaves no output")
        gross_limit = output_limit / retained
        return curve.input_for_gross_output_limit(gross_limit)


def route_capacity(curves: Sequence[EdgeCurve], fee_rate: Decimal = ZERO) -> Decimal:
    """Derive the maximal root input whose full route is covered by observed depth."""

    if not curves:
        raise ValueError("route must be nonempty")
    capacity = curves[-1].input_capacity
    for curve in reversed(curves[:-1]):
        capacity = min(
            curve.input_capacity,
            input_for_net_output_limit(curve, capacity, fee_rate),
        )
    if capacity <= 0:
        raise ValueError("derived route capacity is not positive")
    return capacity


def walk_edge(value: Decimal, curve: EdgeCurve, fee_rate: Decimal) -> tuple[Decimal, bool]:
    gross, full = curve.gross_output(value)
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        return gross * (ONE - fee_rate), full


def evaluate_route(
    curves: Sequence[EdgeCurve], start: Decimal, fee_rate: Decimal
) -> tuple[Decimal, bool]:
    current = start
    full = True
    for curve in curves:
        current, leg_full = walk_edge(current, curve, fee_rate)
        full = full and leg_full
        if not leg_full:
            break
    return current, full


def root_breakpoints(curves: Sequence[EdgeCurve], fee_rate: Decimal) -> set[Decimal]:
    """Pull every local depth boundary back to the root of a composed route."""

    points: set[Decimal] = set()
    for leg_index, curve in enumerate(curves):
        for local_input in curve.cumulative_input:
            root_input = local_input
            for prior_curve in reversed(curves[:leg_index]):
                root_input = input_for_net_output_limit(prior_curve, root_input, fee_rate)
            if root_input > 0:
                points.add(root_input)
    return points


def partition_points(curves: Sequence[EdgeCurve], fee_rate: Decimal) -> tuple[Decimal, ...]:
    # A common zero-hair domain ensures both presentations are evaluable at the same partition.
    common_capacity = route_capacity(curves, ZERO)
    points = root_breakpoints(curves, ZERO) | root_breakpoints(curves, fee_rate)
    points.add(common_capacity)
    return tuple(sorted(point for point in points if ZERO < point <= common_capacity))


def candidate_at_partition(
    route: Sequence[DirectedEdge],
    curves: Sequence[EdgeCurve],
    start: Decimal,
    fee_rate: Decimal,
) -> dict[str, object]:
    zero_hair_final, zero_full = evaluate_route(curves, start, ZERO)
    completed_final, cost_full = evaluate_route(curves, start, fee_rate)
    if not zero_full or not cost_full:
        raise ValueError("derived maximal partition did not close through observed depth")
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        action = zero_hair_final / start - ONE
        hair = (zero_hair_final - completed_final) / start
        completed = completed_final / start - ONE
        error = abs(completed - (action - hair))
    if hair < 0:
        raise ValueError("derived global hair is negative")
    if error > IDENTITY_TOLERANCE:
        raise ValueError("relative closure identity failed")
    value = {
        "route_id": route_id(route),
        "route_class_id": route_class_id(route),
        "path": list(route_assets(route)),
        "reciprocal_route_id": reciprocal_route_id(route),
        "reciprocal_route_class_id": reciprocal_route_class_id(route),
        "partition_derivation": PARTITION_DERIVATION,
        "start_asset": route[0].input_asset,
        "start_amount": decimal_text(start),
        "edges": [edge.as_dict() for edge in route],
        "zero_hair_final_amount": decimal_text(zero_hair_final),
        "cost_completed_final_amount": decimal_text(completed_final),
        "action_potential_return": decimal_text(action),
        "global_hair_return": decimal_text(hair),
        "completed_return": decimal_text(completed),
        "completed_return_bps": decimal_text(completed * TEN_THOUSAND),
        "relative_gap_to_best_bps": "0",  # completed after the whole field is known
        "closure_identity_error": decimal_text(error),
        "full_depth_zero_hair": zero_full,
        "full_depth_cost_completed": cost_full,
    }
    if set(value) != CANDIDATE_FIELDS:
        raise AssertionError("candidate schema drift")
    return value


def derive_candidates(route: Sequence[DirectedEdge], fee_rate: Decimal) -> list[dict[str, object]]:
    curves = tuple(EdgeCurve.derive(edge) for edge in route)
    points = partition_points(curves, fee_rate)
    if not points:
        raise ValueError("route has no derived depth partition")
    evaluated = [candidate_at_partition(route, curves, start, fee_rate) for start in points]
    best_return = max(parse_decimal(candidate["completed_return"]) for candidate in evaluated)
    leaders = [
        candidate
        for candidate in evaluated
        if parse_decimal(candidate["completed_return"]) == best_return
    ]
    return leaders


def integrate_relative_field(candidates: Sequence[Mapping[str, object]]) -> list[dict[str, object]]:
    if not candidates:
        return []
    returns = [parse_decimal(candidate["completed_return_bps"]) for candidate in candidates]
    best = max(returns)
    integrated: list[dict[str, object]] = []
    for candidate, completed in zip(candidates, returns):
        value = dict(candidate)
        value["relative_gap_to_best_bps"] = decimal_text(completed - best)
        integrated.append(value)
    return integrated


def derive_command(
    observation_closed: bool, candidates: Sequence[Mapping[str, object]]
) -> dict[str, object]:
    route_ids = {candidate["route_class_id"] for candidate in candidates}
    reciprocal_closed = bool(candidates) and all(
        candidate["reciprocal_route_class_id"] in route_ids for candidate in candidates
    )
    class_returns: dict[object, Decimal] = {}
    for candidate in candidates:
        class_id = candidate["route_class_id"]
        completed = parse_decimal(candidate["completed_return"])
        class_returns[class_id] = max(completed, class_returns.get(class_id, completed))
    positive = {class_id: value for class_id, value in class_returns.items() if value > 0}
    selected_class: object | None = None
    if positive:
        best = max(positive.values())
        leaders = [class_id for class_id, value in positive.items() if value == best]
        if len(leaders) == 1:
            selected_class = leaders[0]
    if selected_class is not None:
        signal_closure = "UNIQUE_POSITIVE_RELATIONAL_SIGNAL"
    elif positive:
        signal_closure = "NONUNIQUE_POSITIVE_RELATIONAL_SIGNAL"
    else:
        signal_closure = "NO_POSITIVE_RELATIONAL_SIGNAL"
    missing: list[str] = []
    if not observation_closed:
        missing.append("IDENTIFIED_PUBLIC_OBSERVATION")
    if not reciprocal_closed:
        missing.append("RECIPROCAL_TOPOLOGY")
    if selected_class is None:
        missing.append("UNIQUE_POSITIVE_RELATIONAL_SIGNAL")
    missing.append("AUTHENTICATED_PRESENTATION_AND_EXECUTION_AUTHORITY")
    value = {
        "state": "OPEN",
        "observation_closure": "CLOSED" if observation_closed else "OPEN",
        "topology_closure": "RECIPROCAL_CLOSED" if reciprocal_closed else "OPEN",
        "signal_closure": signal_closure,
        "selection_derivation": SELECTION_DERIVATION,
        "selected_route_class_id": selected_class,
        "selected_route_id": None,
        "selected_partition_start_amount": None,
        "execution_authority_closure": "OPEN",
        "missing_closures": sorted(missing),
        "orders_submitted": 0,
    }
    if set(value) != COMMAND_FIELDS:
        raise AssertionError("command schema drift")
    return value


def derive_event_payload(
    event: Mapping[str, object], source_run: Path, config: source_bot.PaperConfig
) -> dict[str, object]:
    observation = event.get("observation")
    observation_closed = (
        isinstance(observation, dict)
        and observation.get("state") == "IDENTIFIED_PUBLIC_BOOKS"
    )
    books = books_from_event(event, source_run, config)
    edges = derive_edges(books) if observation_closed else ()
    cycles = enumerate_simple_cycles(edges) if observation_closed else ()
    with localcontext() as context:
        context.prec = ARITHMETIC_PRECISION
        fee_rate = config.fee_bps_per_leg / TEN_THOUSAND
    candidates = integrate_relative_field(
        [
            candidate
            for route in cycles
            for candidate in derive_candidates(route, fee_rate)
        ]
    )
    asset_graph = {
        "assets": sorted({edge.input_asset for edge in edges} | {edge.output_asset for edge in edges}),
        "directed_edges": [edge.as_dict() for edge in edges],
        "simple_closed_routes": len(cycles),
        "derived_from_validated_public_books": True,
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "event_kind": EVENT_KIND,
        "round_index": event["round_index"],
        "source_event_hash": event["event_hash"],
        "asset_graph": asset_graph,
        "candidates": candidates,
        "command": derive_command(observation_closed, candidates),
        "boundary": BOUNDARY,
    }


def genesis_hash(binding: Mapping[str, object]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_version": SCHEMA_VERSION,
                "event_kind": "GENESIS",
                "source_binding": binding,
                "equation": EQUATION,
                "partition_derivation": PARTITION_DERIVATION,
                "selection_derivation": SELECTION_DERIVATION,
            }
        )
    )


def chain_events(payloads: Iterable[Mapping[str, object]], genesis: str) -> list[dict[str, object]]:
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
    candidates = [candidate for event in events for candidate in event["candidates"]]
    numeric = [parse_decimal(candidate["completed_return_bps"]) for candidate in candidates]
    errors = [parse_decimal(candidate["closure_identity_error"]) for candidate in candidates]
    positive = [value for value in numeric if value > 0]
    commands = [event["command"] for event in events]
    best = max(candidates, key=lambda item: parse_decimal(item["completed_return_bps"]), default=None)
    return {
        "schema_version": SCHEMA_VERSION,
        "rounds": len(events),
        "rounds_with_identified_observations": sum(
            command["observation_closure"] == "CLOSED" for command in commands
        ),
        "derived_asset_graphs": sum(bool(event["asset_graph"]["directed_edges"]) for event in events),
        "derived_candidates": len(candidates),
        "positive_candidates": len(positive),
        "unique_positive_relational_signals": sum(
            command["signal_closure"] == "UNIQUE_POSITIVE_RELATIONAL_SIGNAL"
            for command in commands
        ),
        "open_commands": sum(command["state"] == "OPEN" for command in commands),
        "closed_commands": sum(command["state"] == "CLOSED" for command in commands),
        "best_completed_return_bps": (
            best["completed_return_bps"] if best is not None else None
        ),
        "best_route_id": best["route_id"] if best is not None else None,
        "best_start_asset": best["start_asset"] if best is not None else None,
        "best_depth_derived_start_amount": best["start_amount"] if best is not None else None,
        "maximum_closure_identity_error": decimal_text(max(errors)) if errors else None,
        "all_relative_identities_close": all(error <= IDENTITY_TOLERANCE for error in errors),
        "orders_submitted": 0,
        "authenticated_fills": 0,
        "authenticated_settled_pnl": None,
        "profit_claimed": False,
        "boundary": BOUNDARY,
    }


def create_overlay(source_run: Path, output_dir: Path) -> dict[str, object]:
    binding = source_binding(source_run)
    source_manifest = read_json_object(source_run / "manifest.json")
    config = source_bot.PaperConfig.from_dict(source_manifest["configuration"])
    source_events = read_events(source_run / "events.jsonl")
    payloads = [derive_event_payload(event, source_run, config) for event in source_events]
    genesis = genesis_hash(binding)
    events = chain_events(payloads, genesis)
    summary = summarize(events)
    prepare_output_directory(output_dir)
    ledger = b"".join(canonical_json_bytes(event) + b"\n" for event in events)
    events_path = output_dir / "events.jsonl"
    summary_path = output_dir / "summary.json"
    manifest_path = output_dir / "manifest.json"
    events_path.write_bytes(ledger)
    write_json(summary_path, summary)
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "run_kind": RUN_KIND,
        "equation": EQUATION,
        "partition_derivation": PARTITION_DERIVATION,
        "selection_derivation": SELECTION_DERIVATION,
        "source_binding": binding,
        "genesis_hash": genesis,
        "event_count": len(events),
        "final_event_hash": events[-1]["event_hash"] if events else genesis,
        "events_file": "events.jsonl",
        "events_sha256": sha256_bytes(ledger),
        "summary_file": "summary.json",
        "summary_sha256": sha256_bytes((json.dumps(summary, indent=2, sort_keys=True) + "\n").encode()),
        "program": Path(__file__).name,
        "program_sha256": sha256_file(Path(__file__)),
        "boundary": BOUNDARY,
    }
    if set(manifest) != MANIFEST_FIELDS:
        raise AssertionError("manifest schema drift")
    write_json(manifest_path, manifest)
    return {"manifest": manifest, "summary": summary}


def verify_overlay(source_run: Path, overlay_dir: Path) -> dict[str, object]:
    binding = source_binding(source_run)
    manifest = read_json_object(overlay_dir / "manifest.json")
    if set(manifest) != MANIFEST_FIELDS:
        raise ValueError("manifest fields do not match protocol")
    if manifest.get("schema_version") != SCHEMA_VERSION or manifest.get("run_kind") != RUN_KIND:
        raise ValueError("manifest identity mismatch")
    if manifest.get("equation") != EQUATION:
        raise ValueError("manifest equation mismatch")
    if manifest.get("partition_derivation") != PARTITION_DERIVATION:
        raise ValueError("manifest partition derivation mismatch")
    if manifest.get("selection_derivation") != SELECTION_DERIVATION:
        raise ValueError("manifest selection derivation mismatch")
    if manifest.get("source_binding") != binding or manifest.get("boundary") != BOUNDARY:
        raise ValueError("manifest source or boundary mismatch")
    if manifest.get("program") != Path(__file__).name:
        raise ValueError("manifest program mismatch")
    if manifest.get("program_sha256") != sha256_file(Path(__file__)):
        raise ValueError("manifest program hash mismatch")
    events_path = overlay_dir / "events.jsonl"
    summary_path = overlay_dir / "summary.json"
    if manifest.get("events_file") != "events.jsonl" or manifest.get("summary_file") != "summary.json":
        raise ValueError("manifest paths mismatch")
    if manifest.get("events_sha256") != sha256_file(events_path):
        raise ValueError("events hash mismatch")
    if manifest.get("summary_sha256") != sha256_file(summary_path):
        raise ValueError("summary hash mismatch")
    source_manifest = read_json_object(source_run / "manifest.json")
    config = source_bot.PaperConfig.from_dict(source_manifest["configuration"])
    source_events = read_events(source_run / "events.jsonl")
    expected = chain_events(
        (derive_event_payload(event, source_run, config) for event in source_events),
        genesis_hash(binding),
    )
    actual = read_events(events_path)
    if actual != expected:
        raise ValueError("semantic replay mismatch")
    expected_summary = summarize(expected)
    if read_json_object(summary_path) != expected_summary:
        raise ValueError("summary semantic replay mismatch")
    if manifest.get("event_count") != len(expected):
        raise ValueError("event count mismatch")
    expected_final = expected[-1]["event_hash"] if expected else genesis_hash(binding)
    if manifest.get("genesis_hash") != genesis_hash(binding) or manifest.get("final_event_hash") != expected_final:
        raise ValueError("chain endpoint mismatch")
    return {"verified": True, "events": len(expected), "summary": expected_summary}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    create = sub.add_parser("create", help="derive an immutable overlay")
    create.add_argument("source_run", type=Path)
    create.add_argument("output_dir", type=Path)
    verify = sub.add_parser("verify", help="replay and verify an overlay")
    verify.add_argument("source_run", type=Path)
    verify.add_argument("overlay_dir", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "create":
        result = create_overlay(args.source_run, args.output_dir)
    else:
        result = verify_overlay(args.source_run, args.overlay_dir)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
