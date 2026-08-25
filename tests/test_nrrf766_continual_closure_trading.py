import ast
import csv
import hashlib
import json
import shutil
import tempfile
import unittest
from datetime import datetime, timezone
from decimal import Decimal, localcontext
from pathlib import Path

from experiments.nrrf766_continual_closure_trading import (
    KNOWN_SNAPSHOT,
    PaperClosure,
    failure_close,
    run,
    verify_ledger,
)


ROOT = Path(__file__).parents[1]
LOCKED_RUN = ROOT / "runs" / "nrrf766_continual_closure_trading" / "bitstamp_hourly_oos"
MODULE = ROOT / "experiments" / "nrrf766_continual_closure_trading.py"


def unix(text: str) -> int:
    return int(datetime.fromisoformat(text).replace(tzinfo=timezone.utc).timestamp())


def write_pair(path: Path, symbol: str, rows: list[tuple[int, str, str, str]]) -> None:
    base, quote = symbol.split("/")
    lines = [
        "https://www.CryptoDataDownload.com",
        f"unix,date,symbol,open,high,low,close,Volume {base},Volume {quote}",
    ]
    for timestamp, open_, close, volume in sorted(rows, reverse=True):
        date = datetime.fromtimestamp(timestamp, timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
        high = str(max(Decimal(open_), Decimal(close)) * Decimal("1.1"))
        low = str(min(Decimal(open_), Decimal(close)) * Decimal("0.9"))
        lines.append(
            f"{timestamp},{date},{symbol},{open_},{high},{low},{close},{volume},{volume}"
        )
    path.write_text("\n".join(lines) + "\n")


class ContinualClosureTradingUnitTest(unittest.TestCase):
    def test_failure_close_retains_evidence_and_is_idempotent(self) -> None:
        proposed = PaperClosure("UNSET", Decimal("1.01"), Decimal("100"), ("EARLY",))
        held = failure_close(proposed, ("OHLCV_AGGREGATE_NOT_EXECUTABLE", "EARLY"))
        self.assertEqual(held.decision, "HOLD")
        self.assertEqual(held.returned_ratio, Decimal(1))
        self.assertEqual(held.returned_pnl_bps, Decimal(0))
        self.assertEqual(held.witnesses, ("EARLY", "OHLCV_AGGREGATE_NOT_EXECUTABLE"))
        self.assertEqual(held, failure_close(held, held.witnesses))

    def test_synthetic_run_is_deterministic_and_returns_gaps(self) -> None:
        t0 = unix("2024-01-01T00:00:00")
        times = [t0, t0 + 3600, t0 + 7200]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            btc = root / "BTCUSD.csv"
            eth = root / "ETHUSD.csv"
            cross = root / "ETHBTC.csv"
            write_pair(btc, "BTC/USD", [(t, "100", "100", "2") for t in times])
            write_pair(
                eth,
                "ETH/USD",
                [(times[0], "10", "10", "2"), (times[2], "10", "10", "2")],
            )
            write_pair(cross, "ETH/BTC", [(t, "0.1", "0.1", "2") for t in times])

            first = root / "first"
            second = root / "second"
            one = run(btc, eth, cross, first, start_utc="2024-01-01T00:00:00Z")
            two = run(btc, eth, cross, second, start_utc="2024-01-01T00:00:00Z")
            self.assertEqual(one, two)
            for filename in ("manifest.json", "stage_ledger.csv", "summary.json"):
                self.assertEqual((first / filename).read_bytes(), (second / filename).read_bytes())
            self.assertEqual(
                one["stages"]["state_counts"],
                {"IDENTIFIED_ACTIVE": 1, "OPEN_MISSING": 1, "PENDING_UNFINALIZED": 1},
            )
            self.assertEqual(
                one["candidate_layer"]["orientation_distribution"]["PLUS"]["defined"], 1
            )
            self.assertEqual(one["paper_closed_layer"]["aggregate_pnl_bps"], "0")
            self.assertIsNone(one["authenticated_settled_layer"]["pnl_usd"])
            self.assertEqual(verify_ledger(first / "stage_ledger.csv", first / "manifest.json")["rows"], 3)

    def test_module_has_no_network_or_execution_surface(self) -> None:
        source = MODULE.read_text()
        tree = ast.parse(source)
        imported = set()
        functions = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                functions.add(node.name)
        self.assertTrue(imported.isdisjoint({"http", "requests", "socket", "urllib", "websocket", "ccxt"}))
        self.assertTrue(
            functions.isdisjoint(
                {"place_order", "submit_order", "send_order", "cancel_order", "authenticate"}
            )
        )
        self.assertIn("gross_minus = (btc.close * cross.close) / eth.close", source)
        self.assertNotIn("gross_minus = Decimal(1) / gross_plus", source)


class LockedBitstampContinualClosureRunTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest_path = LOCKED_RUN / "manifest.json"
        cls.ledger_path = LOCKED_RUN / "stage_ledger.csv"
        cls.summary_path = LOCKED_RUN / "summary.json"
        if not all(path.is_file() for path in (cls.manifest_path, cls.ledger_path, cls.summary_path)):
            raise AssertionError("locked NRRF766 run artifacts are missing")
        cls.manifest = json.loads(cls.manifest_path.read_text())
        cls.summary = json.loads(cls.summary_path.read_text())

    def test_known_snapshot_hashes_rows_and_gaps(self) -> None:
        expected_gaps = {"BTC_USD": 204, "ETH_USD": 184, "ETH_BTC": 184}
        for name, known in KNOWN_SNAPSHOT.items():
            observed = self.manifest["inputs"][name]
            self.assertTrue(observed["known_snapshot_verified"])
            self.assertEqual(observed["sha256"], known["sha256"])
            self.assertEqual(observed["rows_parsed"], known["rows"])
            self.assertEqual(observed["unique_timestamp_rows"], known["rows"])
            self.assertEqual(observed["duplicate_timestamp_rows"], 0)
            self.assertEqual(observed["structurally_invalid_unique_rows"], 0)
            self.assertEqual(observed["internal_missing_hours"], expected_gaps[name])
        self.assertEqual(
            self.manifest["inputs"]["BTC_USD"]["recorded_download_utc"],
            "2026-08-24T10:41:41.981008Z",
        )
        self.assertIsNone(self.manifest["inputs"]["ETH_USD"]["recorded_download_utc"])
        self.assertIsNone(self.manifest["inputs"]["ETH_BTC"]["recorded_download_utc"])
        self.assertEqual(
            self.manifest["configuration"]["declared_bar_lag_status"],
            "REPLAY_CONVENTION_NOT_VERIFIED_HISTORICAL_PUBLICATION_TIME",
        )

    def test_every_oos_hour_is_returned_including_open_and_pending(self) -> None:
        self.assertEqual(self.summary["stages"]["declared"], 21_908)
        self.assertEqual(self.summary["stages"]["returned"], 21_908)
        self.assertEqual(
            self.summary["stages"]["state_counts"],
            {
                "IDENTIFIED_ACTIVE": 21_439,
                "INACTIVE": 264,
                "OPEN_MISSING": 204,
                "PENDING_UNFINALIZED": 1,
            },
        )
        witnesses = self.summary["stages"]["witness_counts"]
        self.assertEqual(witnesses["MISSING_BTC_USD"], 204)
        self.assertEqual(witnesses["MISSING_ETH_USD"], 184)
        self.assertEqual(witnesses["MISSING_ETH_BTC"], 184)
        self.assertEqual(witnesses["UNFINALIZED_PROVIDER_TAIL"], 1)

    def test_hash_chain_state_adjacency_and_manifest_receipt(self) -> None:
        verification = verify_ledger(self.ledger_path, self.manifest_path)
        self.assertEqual(verification["rows"], 21_908)
        self.assertEqual(
            verification["final_state_hash"],
            self.summary["continual_closure_checks"]["final_state_hash"],
        )
        self.assertEqual(
            verification["final_event_hash"],
            self.summary["continual_closure_checks"]["final_event_hash"],
        )
        self.assertEqual(
            hashlib.sha256(self.manifest_path.read_bytes()).hexdigest(),
            self.summary["manifest_sha256"],
        )
        self.assertEqual(
            hashlib.sha256(self.ledger_path.read_bytes()).hexdigest(),
            self.summary["stage_ledger_sha256"],
        )

    def test_a_changed_stage_is_rejected_by_the_hash_chain(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = root / "manifest.json"
            ledger = root / "stage_ledger.csv"
            shutil.copyfile(self.manifest_path, manifest)
            shutil.copyfile(self.ledger_path, ledger)

            rows = ledger.read_text().splitlines()
            fields = rows[1].split(",")
            fields[6] = "ADMIT"  # change the first paper decision without reauthoring hashes
            rows[1] = ",".join(fields)
            ledger.write_text("\n".join(rows) + "\n")

            with self.assertRaisesRegex(ValueError, "target state hash failed"):
                verify_ledger(ledger, manifest)

    def test_costs_reciprocal_equation_declared_lag_and_both_orientations(self) -> None:
        active = 0
        pending = 0
        with self.ledger_path.open(newline="") as source:
            for row in csv.DictReader(source):
                self.assertEqual(row["paper_decision"], "HOLD")
                self.assertEqual(row["paper_plus_closed_ratio"], "1")
                self.assertEqual(row["paper_minus_closed_ratio"], "1")
                self.assertEqual(row["paper_plus_closed_pnl_bps"], "0")
                self.assertEqual(row["paper_minus_closed_pnl_bps"], "0")
                self.assertEqual(row["settled_plus_pnl_usd"], "")
                self.assertEqual(row["settled_minus_pnl_usd"], "")
                self.assertEqual(row["plus_orientation"], "USD->BTC->ETH->USD")
                self.assertEqual(row["minus_orientation"], "USD->ETH->BTC->USD")
                if row["stage_state"] == "PENDING_UNFINALIZED":
                    pending += 1
                    self.assertEqual(row["declared_replay_decision_at_utc"], "")
                    continue
                self.assertEqual(
                    datetime.fromisoformat(
                        row["declared_replay_decision_at_utc"].replace("Z", "+00:00")
                    ).timestamp(),
                    int(row["stage_unix"]) + 3600,
                )
                if row["stage_state"] != "IDENTIFIED_ACTIVE":
                    self.assertEqual(row["gross_plus_candidate_ratio"], "")
                    continue
                active += 1
                gross_plus = Decimal(row["gross_plus_candidate_ratio"])
                gross_minus = Decimal(row["gross_minus_candidate_ratio"])
                net_plus = Decimal(row["net_plus_candidate_ratio"])
                net_minus = Decimal(row["net_minus_candidate_ratio"])
                expected_pair = Decimal(self.summary["candidate_layer"]["expected_net_pair_product"])
                with localcontext() as context:
                    context.prec = 110
                    self.assertLessEqual(abs(gross_plus * gross_minus - 1), Decimal("1e-70"))
                    self.assertLessEqual(abs(net_plus * net_minus - expected_pair), Decimal("1e-70"))
                self.assertEqual(Decimal(row["cost_factor_per_leg"]), Decimal("0.9975"))
        self.assertEqual(active, 21_439)
        self.assertEqual(pending, 1)
        self.assertEqual(
            self.summary["candidate_layer"]["reciprocal_equation_consistency_checks"], active
        )
        self.assertFalse(self.summary["candidate_layer"]["reciprocal_check_is_independent_evidence"])
        self.assertEqual(self.summary["candidate_layer"]["cost_product_checks"], active)

    def test_candidate_paper_and_settled_layers_are_not_conflated(self) -> None:
        candidate = self.summary["candidate_layer"]
        self.assertFalse(candidate["executable"])
        self.assertTrue(candidate["same_bar_relation_audit"])
        self.assertFalse(candidate["forward_return_performance_test"])
        plus = candidate["orientation_distribution"]["PLUS"]
        minus = candidate["orientation_distribution"]["MINUS"]
        self.assertEqual((plus["defined"], minus["defined"]), (21_439, 21_439))
        self.assertEqual((plus["net_positive"], minus["net_positive"]), (2, 6))
        self.assertEqual((plus["net_negative"], minus["net_negative"]), (21_437, 21_433))
        self.assertEqual((plus["clears_safety"], minus["clears_safety"]), (2, 5))
        self.assertEqual(
            [row["stage_utc"] for row in plus["net_positive_stages"]],
            ["2025-08-19T00:00:00Z", "2025-11-16T17:00:00Z"],
        )
        self.assertEqual(
            [row["net_candidate_pnl_bps"] for row in plus["net_positive_stages"]],
            [
                "11.900391697416584717431212625998301166974400906692391188913550754092968788044",
                "38.695154113099035429979607011577744314202101437648788585551927031320948010384",
            ],
        )
        self.assertEqual(
            [row["stage_utc"] for row in minus["net_positive_stages"]],
            [
                "2025-02-02T18:00:00Z",
                "2025-02-03T01:00:00Z",
                "2025-03-10T11:00:00Z",
                "2025-09-17T17:00:00Z",
                "2025-10-10T21:00:00Z",
                "2025-11-16T11:00:00Z",
            ],
        )
        self.assertEqual(
            [row["net_candidate_pnl_bps"] for row in minus["net_positive_stages"]],
            [
                "8.758975195983078830982548410231890987329667702605785321539564905570164953382",
                "42.896526488395599927719551861221539573545355981207083483917600289121792555114",
                "0.054114920050585864046634072959759308010530274539300488905603610379842045882",
                "78.388309774357487222497410726347548070428243346692484351780969964425631557617",
                "98.188824997804385933915045168064575566588504923180215403332264814342721997441",
                "10.163701868692552556535579282445785529544399495987797599310299091451687777704",
            ],
        )
        self.assertEqual(self.summary["paper_closed_layer"]["orientations_returned"], 43_816)
        self.assertEqual(self.summary["paper_closed_layer"]["aggregate_pnl_bps"], "0")
        self.assertFalse(self.summary["paper_closed_layer"]["hold_is_process_halting"])
        self.assertEqual(self.summary["authenticated_settled_layer"]["fill_receipts"], 0)
        self.assertEqual(self.summary["authenticated_settled_layer"]["settled_orientations"], 0)
        self.assertIsNone(self.summary["authenticated_settled_layer"]["pnl_usd"])

    def test_runtime_chain_does_not_claim_the_lean_receipt_bridge(self) -> None:
        boundary = self.summary["formal_boundary"]
        self.assertTrue(boundary["runtime_hash_chain_only"])
        self.assertFalse(boundary["lean_BoundaryMatches_instantiated"])
        self.assertFalse(boundary["lean_LocalTradeWitness_instantiated"])
        self.assertTrue(boundary["ReceiptBridge_required"])
        self.assertEqual(
            self.summary["continual_closure_checks"]["declared_bar_lag_or_pending"], 21_908
        )
        hold_reading = self.manifest["semantics"]["hold_continuation"]
        self.assertIn("identity/no-order runtime return", hold_reading)
        self.assertIn("not formal Interaction", hold_reading)


if __name__ == "__main__":
    unittest.main()
