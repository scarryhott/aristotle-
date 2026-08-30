from __future__ import annotations

import json
from dataclasses import replace
from datetime import timedelta
from decimal import Decimal
from pathlib import Path

import pytest

from experiments import nrrf833_fee_pricing_closure_learning as sim


D = Decimal


def rules() -> sim.InstrumentRules:
    return sim.InstrumentRules(
        venue="TEST",
        symbol="BTC/USD",
        base_asset="BTC",
        quote_asset="USD",
        min_order_size=D("0.000000001"),
        min_trade_increment=D("0.000000001"),
        price_increment=D("0.000000001"),
        quote_increment=D("0.000000001"),
        verified_at_utc=sim.parse_time("2026-08-30T00:00:00Z"),
        source="test",
    )


def book(
    *,
    timestamp: str = "2026-08-30T17:00:00Z",
    bids: tuple[tuple[str, str], ...] = (("100", "5"), ("99", "5")),
    asks: tuple[tuple[str, str], ...] = (("101", "5"), ("102", "5")),
) -> sim.OrderBookSnapshot:
    return sim.OrderBookSnapshot(
        venue="TEST",
        symbol="BTC/USD",
        timestamp_utc=sim.parse_time(timestamp),
        bids=tuple(sim.Level(D(price), D(qty)) for price, qty in bids),
        asks=tuple(sim.Level(D(price), D(qty)) for price, qty in asks),
        source="test",
    )


def episode(*, signal: str = "100", budget: str = "20") -> sim.Episode:
    entry = book()
    exit_book = book(timestamp="2026-08-30T17:00:30Z")
    return sim.Episode(
        episode_id="TEST-EPISODE",
        entry_book=entry,
        exit_book=exit_book,
        signal_bps=D(signal),
        quote_budget=D(budget),
        regime="TEST",
    )


def test_fee_tier_boundary_and_next_day_activation() -> None:
    schedule = sim.alpaca_crypto_fee_schedule()
    assert schedule.tier_for(D("99999.999")).name == "TIER_1"
    assert schedule.tier_for(D("100000")).name == "TIER_2"

    day = sim.parse_time("2026-08-30T12:00:00Z").date()
    volume = sim.Rolling30DayVolume.seeded(day, D("99990"))
    volume.record(day, D("20"))
    assert volume.effective_volume(day) == D("99990")
    assert volume.effective_volume(day + timedelta(days=1)) == D("100010")
    assert schedule.tier_for(volume.effective_volume(day + timedelta(days=1))).name == "TIER_2"


def test_official_alpaca_flat_fee_floors_are_multiplicative() -> None:
    schedule = sim.alpaca_crypto_fee_schedule()
    tier = schedule.tier_for(D("0"))
    maker = tier.rate(sim.Liquidity.MAKER)
    taker = tier.rate(sim.Liquidity.TAKER)
    assert sim.flat_round_trip_fee_burden_bps(maker, maker) == D("29.9775")
    assert sim.flat_round_trip_fee_burden_bps(maker, taker) == D("39.9625")
    assert sim.flat_round_trip_fee_burden_bps(taker, taker) == D("49.9375")


def test_depth_walk_vwap_and_slippage_are_exact() -> None:
    depth_book = book(
        asks=(("101", "1"), ("102", "2")),
        bids=(("100", "3"), ("99", "3")),
    )
    fill = sim.execute_taker(
        book=depth_book,
        rules=rules(),
        side=sim.Side.BUY,
        quantity=D("2"),
        schedule=sim.alpaca_crypto_fee_schedule(),
        effective_30d_volume_usd=D("0"),
    )
    assert fill.gross_quote == D("203")
    assert fill.vwap == D("101.5")
    assert fill.depth_slippage_quote == D("1")
    assert fill.fee_asset == "BTC"
    assert fill.fee_amount == D("0.005")
    assert fill.base_delta == D("1.995")


def test_maker_queue_consumes_ahead_before_partial_fill() -> None:
    test_book = book()
    fill = sim.execute_post_only_maker(
        book=test_book,
        rules=rules(),
        side=sim.Side.BUY,
        quantity=D("1"),
        limit_price=D("100"),
        queue_ahead_quantity=D("1"),
        events=(sim.MakerEvent(0, sim.Side.SELL, D("100"), D("1.5")),),
        schedule=sim.alpaca_crypto_fee_schedule(),
        effective_30d_volume_usd=D("0"),
    )
    assert fill.filled_quantity == D("0.5")
    assert fill.unfilled_quantity == D("0.5")
    assert fill.vwap == D("100")
    assert "MAKER_TIMEOUT_UNFILLED" in fill.witnesses


def test_post_only_crossing_fails_closed() -> None:
    with pytest.raises(sim.SimulationError, match="remove liquidity"):
        sim.execute_post_only_maker(
            book=book(),
            rules=rules(),
            side=sim.Side.BUY,
            quantity=D("1"),
            limit_price=D("101"),
            queue_ahead_quantity=D("0"),
            events=(),
            schedule=sim.alpaca_crypto_fee_schedule(),
            effective_30d_volume_usd=D("0"),
        )


def test_stale_fee_schedule_fails_closed() -> None:
    schedule = sim.alpaca_crypto_fee_schedule()
    with pytest.raises(sim.SimulationError, match="stale"):
        schedule.rate(
            sim.Liquidity.TAKER,
            D("0"),
            sim.parse_time("2026-11-30T00:00:00Z"),
        )


def test_taker_round_trip_closes_cash_inventory_and_cost_identity() -> None:
    ep = episode(signal="100", budget="20")
    learner = sim.ClosureLearner()
    schedule = sim.alpaca_crypto_fee_schedule()
    decision = learner.decide(
        episode=ep,
        rules=rules(),
        schedule=schedule,
        effective_volume=D("0"),
        force_route=sim.Route.TAKER_TAKER,
    )
    receipt = sim.execute_episode(
        episode=ep,
        decision=decision,
        rules=rules(),
        schedule=schedule,
        effective_volume=D("0"),
        previous_receipt_hash="GENESIS",
    )
    assert receipt.state == "CLOSED_RETURN"
    assert receipt.final_base_inventory == 0
    assert receipt.cash_conservation_residual_quote == 0
    assert receipt.base_conservation_residual == 0
    assert receipt.closure_residual_quote == 0
    assert receipt.eligible_for_learning is True
    assert sim.verify_receipt_hash(receipt)
    assert receipt.realized_pnl_quote < 0


def test_quote_budget_is_hard_cap_even_with_depth() -> None:
    fixture = Path(__file__).parents[1] / "benchmarks" / "nrrf833_fee_pricing_closure_learning" / "alpaca_btcusd_orderbook_20260830T171345Z.json"
    captured_book, captured_rules = sim.load_book_fixture(fixture)
    schedule = sim.alpaca_crypto_fee_schedule()
    rate = schedule.tier_for(D("0")).rate(sim.Liquidity.TAKER)
    increment = sim.fee_compatible_increment(captured_rules.min_trade_increment, rate)
    quantity = sim.quantity_for_quote_budget(captured_book, D("100"), increment)
    fill = sim.execute_taker(
        book=captured_book,
        rules=captured_rules,
        side=sim.Side.BUY,
        quantity=quantity,
        schedule=schedule,
        effective_30d_volume_usd=D("0"),
    )
    assert fill.gross_quote <= D("100")
    assert fill.depth_slippage_quote > 0


def test_live_snapshot_audit_rejects_twenty_basis_point_target() -> None:
    fixture = Path(__file__).parents[1] / "benchmarks" / "nrrf833_fee_pricing_closure_learning" / "alpaca_btcusd_orderbook_20260830T171345Z.json"
    captured_book, captured_rules = sim.load_book_fixture(fixture)
    report = sim.live_snapshot_audit(
        book=captured_book,
        rules=captured_rules,
        notionals=(D("20"), D("100")),
    )
    assert report["declared_target_clears_maker_maker_fee_floor"] is False
    assert D(report["maker_flat_round_trip_fee_floor_bps"]) == D("29.9775")
    assert D(report["rows"][0]["realized_flat_round_trip_loss_bps"]) > D("49.9375")
    assert all(D(row["closure_residual_quote"]) == 0 for row in report["rows"])


def test_learner_updates_only_from_closed_receipts_and_expands_uncertainty() -> None:
    ep = episode(signal="100", budget="20")
    learner = sim.ClosureLearner()
    schedule = sim.alpaca_crypto_fee_schedule()
    decision = learner.decide(
        episode=ep,
        rules=rules(),
        schedule=schedule,
        effective_volume=D("0"),
        force_route=sim.Route.TAKER_TAKER,
    )
    receipt = sim.execute_episode(
        episode=ep,
        decision=decision,
        rules=rules(),
        schedule=schedule,
        effective_volume=D("0"),
        previous_receipt_hash="GENESIS",
    )
    before = learner.uncertainty_buffer_bps
    learner.update(decision, receipt)
    assert learner.closed_observations == 1
    assert learner.uncertainty_buffer_bps > before

    invalid = replace(receipt, eligible_for_learning=False, state="OPEN_INVENTORY")
    snapshot = learner.to_dict()
    learner.update(decision, invalid)
    assert learner.to_dict() == snapshot


def test_event_chain_detects_tampering() -> None:
    episodes = sim.synthetic_episodes(count=8, seed=833)
    runner = sim.ClosureSimulation(
        rules=sim.alpaca_btcusd_rules(),
        schedule=sim.alpaca_crypto_fee_schedule(),
        learner=sim.ClosureLearner(),
        rolling_volume=sim.Rolling30DayVolume.seeded(
            episodes[0].entry_book.timestamp_utc.date(), D("0")
        ),
    )
    events, summary = runner.run(episodes)
    raw = [event.to_dict() for event in events]
    assert summary["receipt_chain_verified"] is True
    assert sim.verify_event_chain(raw, summary["genesis_hash"])
    raw[3]["decision"]["route"] = "TAMPERED"
    assert not sim.verify_event_chain(raw, summary["genesis_hash"])


def test_deterministic_simulation_repeats_bit_for_bit() -> None:
    episodes_a = sim.synthetic_episodes(count=24, seed=833)
    episodes_b = sim.synthetic_episodes(count=24, seed=833)

    def run(items: list[sim.Episode]) -> tuple[list[dict[str, object]], dict[str, object]]:
        runner = sim.ClosureSimulation(
            rules=sim.alpaca_btcusd_rules(),
            schedule=sim.alpaca_crypto_fee_schedule(),
            learner=sim.ClosureLearner(),
            rolling_volume=sim.Rolling30DayVolume.seeded(
                items[0].entry_book.timestamp_utc.date(), D("0")
            ),
        )
        events, summary = runner.run(items)
        return [event.to_dict() for event in events], summary

    events_a, summary_a = run(episodes_a)
    events_b, summary_b = run(episodes_b)
    assert events_a == events_b
    assert summary_a == summary_b
    assert D(summary_a["maximum_closure_residual_quote"]) == 0


def test_run_files_are_hash_bound(tmp_path: Path) -> None:
    episodes = sim.synthetic_episodes(count=6, seed=17)
    runner = sim.ClosureSimulation(
        rules=sim.alpaca_btcusd_rules(),
        schedule=sim.alpaca_crypto_fee_schedule(),
        learner=sim.ClosureLearner(),
        rolling_volume=sim.Rolling30DayVolume.seeded(
            episodes[0].entry_book.timestamp_utc.date(), D("0")
        ),
    )
    events, summary = runner.run(episodes)
    output = tmp_path / "run"
    sim.write_run(output, events, summary)
    manifest = json.loads((output / "manifest.json").read_text())
    assert manifest["events_sha256"]
    assert manifest["summary_sha256"]
    assert len((output / "events.jsonl").read_text().splitlines()) == 6
    verification = sim.verify_run_directory(output)
    assert verification["verified"] is True
    assert verification["program_sha256_verified"] is True


def test_receipt_chain_link_tampering_is_detected() -> None:
    episodes = sim.synthetic_episodes(count=5, seed=101)
    runner = sim.ClosureSimulation(
        rules=sim.alpaca_btcusd_rules(),
        schedule=sim.alpaca_crypto_fee_schedule(),
        learner=sim.ClosureLearner(),
        rolling_volume=sim.Rolling30DayVolume.seeded(
            episodes[0].entry_book.timestamp_utc.date(), D("0")
        ),
    )
    events, summary = runner.run(episodes)
    raw = [event.to_dict() for event in events]
    raw[2]["receipt"]["previous_receipt_hash"] = "BROKEN_LINK"
    # Rehashing the enclosing event is not enough; the independently linked receipt chain fails.
    event_payload = dict(raw[2])
    event_payload.pop("event_hash")
    raw[2]["event_hash"] = sim.sha256_value(event_payload)
    assert not sim.verify_event_chain(raw, summary["genesis_hash"])


def test_crossed_order_book_is_rejected() -> None:
    with pytest.raises(sim.SimulationError, match="crossed or locked"):
        sim.OrderBookSnapshot(
            venue="TEST",
            symbol="BTC/USD",
            timestamp_utc=sim.parse_time("2026-08-30T17:00:00Z"),
            bids=(sim.Level(D("101"), D("1")),),
            asks=(sim.Level(D("101"), D("1")),),
            source="test",
        )


def test_insufficient_taker_depth_fails_closed() -> None:
    shallow = book(bids=(("100", "0.1"),), asks=(("101", "0.1"),))
    with pytest.raises(sim.SimulationError, match="cannot fill"):
        sim.execute_taker(
            book=shallow,
            rules=rules(),
            side=sim.Side.BUY,
            quantity=D("1"),
            schedule=sim.alpaca_crypto_fee_schedule(),
            effective_30d_volume_usd=D("0"),
        )


def test_fee_compatible_increment_closes_received_asset_quantity() -> None:
    increment = D("0.000000001")
    maker_rate = D("0.0015")
    compatible = sim.fee_compatible_increment(increment, maker_rate)
    assert compatible == D("0.000002")
    quantity = compatible * D("127")
    fee = quantity * maker_rate
    assert sim.quantize_down(fee, increment) == fee
    assert sim.quantize_down(quantity - fee, increment) == quantity - fee


def test_learner_rejects_tampered_closed_accounting() -> None:
    ep = episode(signal="100", budget="20")
    learner = sim.ClosureLearner()
    schedule = sim.alpaca_crypto_fee_schedule()
    decision = learner.decide(
        episode=ep,
        rules=rules(),
        schedule=schedule,
        effective_volume=D("0"),
        force_route=sim.Route.TAKER_TAKER,
    )
    receipt = sim.execute_episode(
        episode=ep,
        decision=decision,
        rules=rules(),
        schedule=schedule,
        effective_volume=D("0"),
        previous_receipt_hash="GENESIS",
    )
    tampered = replace(receipt, closure_residual_quote=D("0.01"), eligible_for_learning=True)
    with pytest.raises(sim.SimulationError, match="non-closing"):
        learner.update(decision, tampered)


def test_forced_execution_does_not_self_amplify_uncertainty() -> None:
    episodes = sim.synthetic_episodes(count=240, seed=833)
    runner = sim.ClosureSimulation(
        rules=sim.alpaca_btcusd_rules(),
        schedule=sim.alpaca_crypto_fee_schedule(),
        learner=sim.ClosureLearner(),
        rolling_volume=sim.Rolling30DayVolume.seeded(
            episodes[0].entry_book.timestamp_utc.date(), D("0")
        ),
        force_route=sim.Route.TAKER_TAKER,
    )
    _, summary = runner.run(episodes)
    final = summary["final_learner"]
    assert D(final["absolute_model_error_bps"]) < D("100")
    assert D(final["uncertainty_buffer_bps"]) < D("200")
    assert D(summary["maximum_closure_residual_quote"]) == 0
