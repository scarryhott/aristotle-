import ast
import hashlib
import json
import shutil
import socket
import tempfile
import unittest
from decimal import Decimal, localcontext
from pathlib import Path
from unittest import mock

from experiments import nrrf767_live_paper_trading_bot as bot


ROOT = Path(__file__).parents[1]
MODULE = ROOT / "experiments" / "nrrf767_live_paper_trading_bot.py"
LOCKED_RUN = (
    ROOT
    / "runs"
    / "nrrf767_live_paper_trading_bot"
    / "bitstamp_public_20260826T0221Z"
)
BASE_US = 1_700_000_000_500_000


def raw_book(
    *,
    bids: list[list[str]],
    asks: list[list[str]],
    exchange_us: int = BASE_US - 100_000,
) -> bytes:
    return bot.canonical_json_bytes(
        {
            "timestamp": str(exchange_us // 1_000_000),
            "microtimestamp": str(exchange_us),
            "bids": bids,
            "asks": asks,
        }
    )


def receipt(
    name: str,
    raw: bytes,
    *,
    start_us: int = BASE_US - 200_000,
    complete_us: int = BASE_US,
    failure: str | None = None,
    status: int | None = 200,
    content_type: str | None = "application/json",
    final_url: str | None = None,
    raw_complete: bool = True,
) -> bot.CaptureReceipt:
    return bot.CaptureReceipt(
        name=name,
        requested_url=bot.PUBLIC_BOOK_ENDPOINTS[name],
        final_url=final_url or bot.PUBLIC_BOOK_ENDPOINTS[name],
        request_started_unix_us=start_us,
        request_completed_unix_us=complete_us,
        duration_monotonic_us=max(0, complete_us - start_us),
        http_status=status,
        content_type=content_type,
        raw=raw,
        raw_complete=raw_complete,
        transport_failure=failure,
    )


def profitable_receipts() -> dict[str, bot.CaptureReceipt]:
    payloads = {
        "BTC_USD": raw_book(bids=[["99", "100"]], asks=[["100", "100"]]),
        "ETH_USD": raw_book(bids=[["11", "1000"]], asks=[["11.1", "1000"]]),
        "ETH_BTC": raw_book(bids=[["0.09", "1000"]], asks=[["0.1", "1000"]]),
    }
    return {
        name: receipt(
            name,
            payloads[name],
            start_us=BASE_US - 200_000 + index * 1000,
            complete_us=BASE_US + index * 1000,
        )
        for index, name in enumerate(bot.PAIR_ORDER)
    }


def neutral_books() -> dict[str, bot.Book]:
    return {
        "BTC_USD": bot.Book(
            "BTC_USD", "BTC", "USD", ((Decimal("99"), Decimal("100")),),
            ((Decimal("100"), Decimal("100")),)
        ),
        "ETH_USD": bot.Book(
            "ETH_USD", "ETH", "USD", ((Decimal("10"), Decimal("1000")),),
            ((Decimal("10.1"), Decimal("1000")),)
        ),
        "ETH_BTC": bot.Book(
            "ETH_BTC", "ETH", "BTC", ((Decimal("0.099"), Decimal("1000")),),
            ((Decimal("0.1"), Decimal("1000")),)
        ),
    }


class PublicPaperBotMathTest(unittest.TestCase):
    def test_plus_and_minus_use_the_declared_independent_sides(self) -> None:
        books = {
            "BTC_USD": bot.Book(
                "BTC_USD", "BTC", "USD", ((Decimal("99"), Decimal("100")),),
                ((Decimal("100"), Decimal("100")),)
            ),
            "ETH_USD": bot.Book(
                "ETH_USD", "ETH", "USD", ((Decimal("11"), Decimal("1000")),),
                ((Decimal("11.1"), Decimal("1000")),)
            ),
            "ETH_BTC": bot.Book(
                "ETH_BTC", "ETH", "BTC", ((Decimal("0.09"), Decimal("1000")),),
                ((Decimal("0.1"), Decimal("1000")),)
            ),
        }
        config = bot.PaperConfig(fee_bps_per_leg=Decimal(0), safety_bps=Decimal(0))
        plus = bot.evaluate_route("PLUS", Decimal("100"), books, config)
        minus = bot.evaluate_route("MINUS", Decimal("100"), books, config)
        self.assertEqual(Decimal(plus["candidate_final_usd"]), Decimal("110"))
        with localcontext() as context:
            context.prec = 80
            expected_minus = Decimal("100") / Decimal("11.1") * Decimal("0.09") * Decimal("99")
        self.assertEqual(Decimal(minus["candidate_final_usd"]), expected_minus)
        self.assertEqual(plus["decision"], "PAPER_SIGNAL")
        self.assertEqual(minus["decision"], "HOLD")
        self.assertEqual(plus["no_order_account_delta_usd"], "0")
        self.assertIsNone(plus["authenticated_settled_pnl_usd"])
        self.assertEqual(plus["orders_submitted"], 0)

    def test_three_declared_fees_compound_on_received_assets(self) -> None:
        config = bot.PaperConfig(fee_bps_per_leg=Decimal("25"), safety_bps=Decimal(0))
        result = bot.evaluate_route("PLUS", Decimal("100"), neutral_books(), config)
        expected = Decimal("100") * Decimal("0.9975") ** 3
        self.assertEqual(Decimal(result["candidate_final_usd"]), expected)
        self.assertEqual(result["decision"], "HOLD")

    def test_multilevel_depth_walk_and_exact_boundary(self) -> None:
        book = bot.Book(
            "X", "BASE", "QUOTE",
            ((Decimal("20"), Decimal("1")), (Decimal("10"), Decimal("2"))),
            ((Decimal("10"), Decimal("1")), (Decimal("20"), Decimal("2"))),
        )
        bought = bot.walk_buy_base(bot.Amount("QUOTE", Decimal("30")), book, Decimal(0))
        sold = bot.walk_sell_base(bot.Amount("BASE", Decimal("3")), book, Decimal(0))
        self.assertTrue(bought.full_depth_coverage)
        self.assertEqual(bought.output, bot.Amount("BASE", Decimal("2")))
        self.assertEqual(bought.levels_used, 2)
        self.assertTrue(sold.full_depth_coverage)
        self.assertEqual(sold.output, bot.Amount("QUOTE", Decimal("40")))
        self.assertEqual(sold.levels_used, 2)

    def test_incomplete_first_leg_stops_the_route(self) -> None:
        books = neutral_books()
        books["BTC_USD"] = bot.Book(
            "BTC_USD", "BTC", "USD", ((Decimal("99"), Decimal("1")),),
            ((Decimal("100"), Decimal("0.1")),)
        )
        result = bot.evaluate_route(
            "PLUS", Decimal("100"), books,
            bot.PaperConfig(fee_bps_per_leg=Decimal(0), safety_bps=Decimal(0)),
        )
        self.assertEqual(result["decision"], "HOLD")
        self.assertFalse(result["full_depth_coverage"])
        self.assertEqual(len(result["leg_trace"]), 1)
        self.assertIn("INSUFFICIENT_PUBLIC_DEPTH_USD_TO_BTC", result["witnesses"])
        self.assertIsNone(result["candidate_delta_usd"])

    def test_asset_mismatch_is_rejected(self) -> None:
        book = neutral_books()["BTC_USD"]
        with self.assertRaisesRegex(ValueError, "expected USD"):
            bot.walk_buy_base(bot.Amount("ETH", Decimal(1)), book, Decimal(0))
        with self.assertRaisesRegex(ValueError, "expected BTC"):
            bot.walk_sell_base(bot.Amount("ETH", Decimal(1)), book, Decimal(0))

    def test_signal_gate_is_strictly_above_safety(self) -> None:
        books = {
            "BTC_USD": bot.Book("BTC_USD", "BTC", "USD", ((Decimal("99"), Decimal(100)),), ((Decimal("100"), Decimal(100)),)),
            "ETH_USD": bot.Book("ETH_USD", "ETH", "USD", ((Decimal("11"), Decimal(1000)),), ((Decimal("11.1"), Decimal(1000)),)),
            "ETH_BTC": bot.Book("ETH_BTC", "ETH", "BTC", ((Decimal("0.09"), Decimal(1000)),), ((Decimal("0.1"), Decimal(1000)),)),
        }
        exact = bot.evaluate_route(
            "PLUS", Decimal(100), books,
            bot.PaperConfig(fee_bps_per_leg=Decimal(0), safety_bps=Decimal(1000)),
        )
        above = bot.evaluate_route(
            "PLUS", Decimal(100), books,
            bot.PaperConfig(fee_bps_per_leg=Decimal(0), safety_bps=Decimal("999.999")),
        )
        self.assertEqual(exact["decision"], "HOLD")
        self.assertIn("CANDIDATE_NOT_ABOVE_SAFETY_RESERVE", exact["witnesses"])
        self.assertEqual(above["decision"], "PAPER_SIGNAL")

    def test_higher_fees_never_improve_candidate_output(self) -> None:
        outputs = []
        for fee in (Decimal(0), Decimal(25), Decimal(100)):
            row = bot.evaluate_route(
                "PLUS", Decimal(100), neutral_books(),
                bot.PaperConfig(fee_bps_per_leg=fee, safety_bps=Decimal(0)),
            )
            outputs.append(Decimal(row["candidate_final_usd"]))
        self.assertGreater(outputs[0], outputs[1])
        self.assertGreater(outputs[1], outputs[2])

    def test_long_declared_fee_is_independent_of_ambient_decimal_context(self) -> None:
        config = bot.PaperConfig(
            fee_bps_per_leg=Decimal("0.1234567890123456789012345678901234567890123456789"),
            safety_bps=Decimal(0),
        )
        outputs = []
        for precision in (12, 28, 120):
            with localcontext() as context:
                context.prec = precision
                outputs.append(
                    bot.evaluate_route("PLUS", Decimal(100), neutral_books(), config)
                )
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(outputs[1], outputs[2])


class PublicReceiptValidationTest(unittest.TestCase):
    def config(self, **changes: object) -> bot.PaperConfig:
        values = {
            "fee_bps_per_leg": Decimal(0),
            "safety_bps": Decimal(0),
            "max_book_age_ms": Decimal(1000),
            "max_future_ms": Decimal(100),
            "max_cross_book_skew_ms": Decimal(100),
            "max_acquisition_span_ms": Decimal(1000),
            "max_request_start_skew_ms": Decimal(100),
        }
        values.update(changes)
        return bot.PaperConfig(**values)

    def test_valid_round_returns_six_evaluations_and_public_signal(self) -> None:
        result = bot.derive_round(profitable_receipts(), self.config())
        self.assertEqual(result["observation"]["state"], "IDENTIFIED_PUBLIC_BOOKS")
        self.assertEqual(len(result["evaluations"]), 6)
        self.assertEqual(result["selected_paper_signal"]["orientation"], "PLUS")
        self.assertEqual(result["boundary"]["evidence_grade"], "PUBLIC_REST_COUNTERFACTUAL")
        self.assertFalse(result["boundary"]["execution_authorized"])
        self.assertEqual(result["boundary"]["orders_submitted"], 0)
        self.assertIsNone(result["boundary"]["authenticated_settled_pnl_usd"])

    def test_invalid_root_duplicate_key_and_locked_book_totalize_to_hold(self) -> None:
        bad_roots = [
            b"[]",
            b'{"timestamp":"1","timestamp":"1","microtimestamp":"1000000","bids":[],"asks":[]}',
            raw_book(bids=[["100", "1"]], asks=[["100", "1"]]),
        ]
        expected = ("INVALID_ROOT_BTC_USD", "INVALID_JSON_BTC_USD", "LOCKED_OR_CROSSED_BOOK_BTC_USD")
        for bad, witness in zip(bad_roots, expected):
            with self.subTest(witness=witness):
                receipts = profitable_receipts()
                receipts["BTC_USD"] = receipt("BTC_USD", bad)
                result = bot.derive_round(receipts, self.config())
                self.assertEqual(result["observation"]["state"], "OPEN_PUBLIC_BOOKS")
                self.assertIn(witness, result["observation"]["witnesses"])
                self.assertTrue(all(row["decision"] == "HOLD" for row in result["evaluations"]))

    def test_stale_future_skew_and_acquisition_span_are_witnessed(self) -> None:
        cases: list[tuple[str, dict[str, bot.CaptureReceipt], bot.PaperConfig]] = []
        stale = profitable_receipts()
        stale["BTC_USD"] = receipt(
            "BTC_USD",
            raw_book(bids=[["99", "1"]], asks=[["100", "1"]], exchange_us=BASE_US - 2_000_000),
        )
        cases.append(("STALE_BOOK_BTC_USD", stale, self.config()))
        future = profitable_receipts()
        future["BTC_USD"] = receipt(
            "BTC_USD",
            raw_book(bids=[["99", "1"]], asks=[["100", "1"]], exchange_us=BASE_US + 200_000),
        )
        cases.append(("FUTURE_BOOK_BTC_USD", future, self.config()))
        skew = profitable_receipts()
        skew["ETH_BTC"] = receipt(
            "ETH_BTC",
            raw_book(bids=[["0.09", "1"]], asks=[["0.1", "1"]], exchange_us=BASE_US - 500_000),
        )
        cases.append(("CROSS_BOOK_TIMESTAMP_SKEW", skew, self.config(max_book_age_ms=Decimal(1000))))
        span = profitable_receipts()
        span["ETH_BTC"] = receipt(
            "ETH_BTC", span["ETH_BTC"].raw,
            start_us=BASE_US - 2_000_000, complete_us=BASE_US,
        )
        cases.append(("ACQUISITION_SPAN_EXCEEDED", span, self.config(max_request_start_skew_ms=Decimal(5000))))
        for expected, receipts, config in cases:
            with self.subTest(expected=expected):
                result = bot.derive_round(receipts, config)
                self.assertIn(expected, result["observation"]["witnesses"])
                self.assertTrue(all(row["decision"] == "HOLD" for row in result["evaluations"]))

    def test_transport_content_redirect_and_size_fail_closed(self) -> None:
        originals = profitable_receipts()
        variants = {
            "TRANSPORT_FAILURE_BTC_USD": receipt("BTC_USD", originals["BTC_USD"].raw, failure="timeout"),
            "UNEXPECTED_CONTENT_TYPE_BTC_USD": receipt("BTC_USD", originals["BTC_USD"].raw, content_type="text/html"),
            "UNEXPECTED_REDIRECT_BTC_USD": receipt("BTC_USD", originals["BTC_USD"].raw, final_url="https://example.invalid/"),
            "INCOMPLETE_RESPONSE_BTC_USD": receipt("BTC_USD", originals["BTC_USD"].raw, raw_complete=False),
        }
        for expected, changed in variants.items():
            with self.subTest(expected=expected):
                values = profitable_receipts()
                values["BTC_USD"] = changed
                result = bot.derive_round(values, self.config())
                self.assertIn(expected, result["observation"]["witnesses"])
                self.assertTrue(all(item["decision"] == "HOLD" for item in result["evaluations"]))

    def test_duplicate_prices_and_nonstring_exchange_fields_fail_closed(self) -> None:
        duplicates = raw_book(
            bids=[["99", "1"], ["99", "2"]],
            asks=[["100", "1"]],
        )
        numeric_levels = bot.canonical_json_bytes(
            {
                "timestamp": str((BASE_US - 100_000) // 1_000_000),
                "microtimestamp": str(BASE_US - 100_000),
                "bids": [[99, 1]],
                "asks": [[100, 1]],
            }
        )
        extreme_exponent = raw_book(
            bids=[["99", "1"]],
            asks=[["1e999999", "1"]],
        )
        excessive_precision = raw_book(
            bids=[["99", "1"]],
            asks=[["100.123456789012345678901234567890123456789012345678901", "1"]],
        )
        for raw, expected in (
            (duplicates, "DUPLICATE_BIDS_PRICE_BTC_USD"),
            (numeric_levels, "INVALID_BIDS_LEVEL_BTC_USD"),
            (extreme_exponent, "INVALID_ASKS_LEVEL_BTC_USD"),
            (excessive_precision, "INVALID_ASKS_LEVEL_BTC_USD"),
        ):
            with self.subTest(expected=expected):
                values = profitable_receipts()
                values["BTC_USD"] = receipt("BTC_USD", raw)
                result = bot.derive_round(values, self.config())
                self.assertIn(expected, result["observation"]["witnesses"])
                self.assertTrue(all(item["decision"] == "HOLD" for item in result["evaluations"]))

    def test_configuration_rejects_invalid_costs_and_limits(self) -> None:
        for kwargs in (
            {"fee_bps_per_leg": Decimal(10000)},
            {"fee_bps_per_leg": Decimal(-1)},
            {"safety_bps": Decimal(-1)},
            {"notionals_usd": (Decimal(0),)},
            {"notionals_usd": (Decimal(1), Decimal(1))},
            {"max_book_age_ms": Decimal(0)},
            {"max_future_ms": Decimal(-1)},
            {"max_response_bytes": 0},
            {"fee_bps_per_leg": Decimal("NaN")},
            {"safety_bps": Decimal("Infinity")},
        ):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                bot.PaperConfig(**kwargs)


class ReplayAndSafetyTest(unittest.TestCase):
    def capture_fixture(self, root: Path, rounds: int = 2) -> dict[str, object]:
        config = bot.PaperConfig(
            fee_bps_per_leg=Decimal(0),
            safety_bps=Decimal(0),
            max_book_age_ms=Decimal(1000),
            max_cross_book_skew_ms=Decimal(100),
            max_acquisition_span_ms=Decimal(1000),
            max_request_start_skew_ms=Decimal(100),
        )
        with mock.patch.object(bot, "capture_public_round", side_effect=lambda _config: profitable_receipts()):
            return bot.capture_run(root, rounds=rounds, interval_seconds=Decimal(0), config=config)

    def test_fixture_capture_is_byte_deterministic_and_replays_without_network(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first, second = root / "first", root / "second"
            self.capture_fixture(first)
            self.capture_fixture(second)
            for relative in ("events.jsonl", "summary.json", "manifest.json"):
                self.assertEqual((first / relative).read_bytes(), (second / relative).read_bytes())
            with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
                verifications = []
                for precision in (12, 28, 120):
                    with localcontext() as context:
                        context.prec = precision
                        verifications.append(bot.verify_run(first))
            self.assertEqual(verifications[0], verifications[1])
            self.assertEqual(verifications[1], verifications[2])
            verification = verifications[0]
            self.assertTrue(verification["verified"])
            self.assertEqual(verification["event_count"], 2)
            self.assertEqual(verification["summary"]["orders_submitted"], 0)
            self.assertEqual(verification["summary"]["no_order_account_delta_usd"], "0")
            self.assertIsNone(verification["summary"]["authenticated_settled_pnl_usd"])

    def test_raw_event_and_summary_tampering_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source"
            self.capture_fixture(source, rounds=1)
            for target_name, mutate, message in (
                (
                    "raw",
                    lambda target: next((target / "raw").glob("*")).write_bytes(b"{}"),
                    "raw receipt hash mismatch|manifest raw hash mismatch",
                ),
                (
                    "event",
                    lambda target: (target / "events.jsonl").write_bytes(
                        (target / "events.jsonl").read_bytes().replace(b'"decision":"PAPER_SIGNAL"', b'"decision":"HOLD"', 1)
                    ),
                    "events file hash mismatch",
                ),
                (
                    "summary",
                    lambda target: (target / "summary.json").write_text("{}\n"),
                    "summary hash mismatch",
                ),
            ):
                with self.subTest(target=target_name):
                    target = Path(directory) / target_name
                    shutil.copytree(source, target)
                    mutate(target)
                    with self.assertRaisesRegex(ValueError, message):
                        bot.verify_run(target)

    def test_nonempty_run_directory_is_never_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "keep.txt").write_text("mine")
            with self.assertRaises(FileExistsError):
                self.capture_fixture(root)
            self.assertEqual((root / "keep.txt").read_text(), "mine")

    def test_manifest_cannot_relabel_public_paper_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source"
            self.capture_fixture(source, rounds=1)

            def change_run_kind(value: dict[str, object]) -> None:
                value["run_kind"] = "LIVE_PRIVATE_REAL_MONEY"

            def change_boundary(value: dict[str, object]) -> None:
                value["boundary"]["orders_enabled"] = True
                value["boundary"]["orders_submitted"] = 999

            def change_source(value: dict[str, object]) -> None:
                value["source"]["venue"] = "invented"

            def change_program(value: dict[str, object]) -> None:
                value["program_sha256"] = "0" * 64

            def change_config_prose(value: dict[str, object]) -> None:
                value["configuration"]["transport"] = "authenticated POST"

            for name, mutation in (
                ("run_kind", change_run_kind),
                ("boundary", change_boundary),
                ("venue", change_source),
                ("program", change_program),
                ("configuration", change_config_prose),
            ):
                with self.subTest(name=name):
                    target = Path(directory) / name
                    shutil.copytree(source, target)
                    manifest_path = target / "manifest.json"
                    manifest = json.loads(manifest_path.read_text())
                    mutation(manifest)
                    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
                    with self.assertRaises(ValueError):
                        bot.verify_run(target)

    def test_module_has_only_public_get_and_no_execution_or_credentials_surface(self) -> None:
        source = MODULE.read_text()
        tree = ast.parse(source)
        imports: set[str] = set()
        functions: set[str] = set()
        attributes: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imports.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imports.add(node.module.split(".")[0])
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                functions.add(node.name)
            elif isinstance(node, ast.Attribute):
                attributes.add(node.attr)
        self.assertTrue(imports.isdisjoint({"ccxt", "keyring", "requests", "subprocess", "websocket"}))
        self.assertTrue(attributes.isdisjoint({"environ", "getenv"}))
        self.assertTrue(
            functions.isdisjoint(
                {"authenticate", "cancel_order", "place_order", "send_order", "submit_order"}
            )
        )
        self.assertEqual(set(bot.PUBLIC_BOOK_ENDPOINTS), set(bot.PAIR_ORDER))
        self.assertTrue(all(url.startswith("https://www.bitstamp.net/api/v2/order_book/") for url in bot.PUBLIC_BOOK_ENDPOINTS.values()))
        self.assertNotIn("Authorization", source)
        self.assertNotIn("X-Auth", source)
        self.assertNotIn('method="POST"', source)

    def test_fetch_request_is_bodyless_get_without_auth_headers(self) -> None:
        class Response:
            status = 200
            headers = {"Content-Type": "application/json"}

            def __enter__(self):
                return self

            def __exit__(self, *_args):
                return False

            def geturl(self):
                return bot.PUBLIC_BOOK_ENDPOINTS["BTC_USD"]

            def read(self, _limit):
                return profitable_receipts()["BTC_USD"].raw

        seen: list[object] = []

        def fake_urlopen(request, **_kwargs):
            seen.append(request)
            return Response()

        with mock.patch.object(bot.urllib.request, "urlopen", side_effect=fake_urlopen):
            captured = bot.fetch_public_book("BTC_USD", bot.PaperConfig())
        self.assertIsNone(captured.transport_failure)
        self.assertEqual(len(seen), 1)
        self.assertEqual(seen[0].get_method(), "GET")
        self.assertIsNone(seen[0].data)
        headers = {key.lower(): value for key, value in seen[0].header_items()}
        self.assertNotIn("authorization", headers)


class LockedBitstampPublicPaperRunTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest = json.loads((LOCKED_RUN / "manifest.json").read_text())
        cls.summary = json.loads((LOCKED_RUN / "summary.json").read_text())
        cls.events = [
            json.loads(line) for line in (LOCKED_RUN / "events.jsonl").read_text().splitlines()
        ]

    def test_locked_run_replays_from_exact_raw_receipts(self) -> None:
        verifications = []
        for precision in (12, 28, 120):
            with localcontext() as context:
                context.prec = precision
                verifications.append(bot.verify_run(LOCKED_RUN))
        self.assertEqual(verifications[0], verifications[1])
        self.assertEqual(verifications[1], verifications[2])
        verification = verifications[0]
        self.assertTrue(verification["verified"])
        self.assertEqual(verification["event_count"], 12)
        self.assertEqual(
            verification["configuration_sha256"],
            "544070bca366ea0c0dbc0d48e4e085ab88cd7cf90a391760d0dffa3a00689b33",
        )
        self.assertEqual(
            verification["final_event_hash"],
            "50755b3a49a0e40f33780792fd8c92456f298ca8b4d9eb689297e0d4e529a373",
        )
        self.assertEqual(
            verification["events_sha256"],
            "0669ec688688a4810ee61b4f6b18b5dee720eaa0e1a6ac5f140cd51128e4ac81",
        )
        self.assertEqual(
            hashlib.sha256(MODULE.read_bytes()).hexdigest(),
            self.manifest["program_sha256"],
        )

    def test_exact_counts_and_counterfactual_range(self) -> None:
        self.assertEqual(self.summary["rounds_returned"], 12)
        self.assertEqual(
            self.summary["observation_states"],
            {"IDENTIFIED_PUBLIC_BOOKS": 11, "OPEN_PUBLIC_BOOKS": 1},
        )
        self.assertEqual(self.summary["route_size_evaluations"], 72)
        self.assertEqual(self.summary["numeric_full_depth_evaluations"], 66)
        self.assertEqual(self.summary["paper_signals"], 0)
        self.assertEqual(
            self.summary["best_candidate"]["candidate_return_bps"],
            "-74.236782764430907445819961815005890238453101515213064142665637567534630539871",
        )
        self.assertEqual(
            self.summary["worst_candidate"]["candidate_return_bps"],
            "-81.3210716345897854849919621241267246076056242088958622338653878296555759793897",
        )
        self.assertEqual(
            self.summary["witness_counts"],
            {
                "CROSS_BOOK_TIMESTAMP_SKEW": 6,
                "NONPOSITIVE_CANDIDATE_AFTER_DECLARED_COSTS": 66,
                "PUBLIC_OBSERVATION_OPEN": 6,
            },
        )

    def test_every_locked_event_preserves_the_no_execution_boundary(self) -> None:
        self.assertEqual([event["round_index"] for event in self.events], list(range(12)))
        for event in self.events:
            self.assertIsNone(event["selected_paper_signal"])
            self.assertEqual(event["boundary"]["evidence_grade"], "PUBLIC_REST_COUNTERFACTUAL")
            self.assertFalse(event["boundary"]["execution_authorized"])
            self.assertEqual(event["boundary"]["orders_submitted"], 0)
            self.assertEqual(event["boundary"]["authenticated_fills"], 0)
            self.assertEqual(event["boundary"]["formal_receipt_admissions"], 0)
            self.assertEqual(event["boundary"]["no_order_account_delta_usd"], "0")
            self.assertIsNone(event["boundary"]["authenticated_settled_pnl_usd"])
            self.assertTrue(all(row["decision"] == "HOLD" for row in event["evaluations"]))
        self.assertEqual(len(self.manifest["raw_files"]), 23)
        self.assertEqual(self.manifest["boundary"]["orders_submitted"], 0)
        self.assertFalse(self.manifest["source"]["account_specific_fee_verified"])


if __name__ == "__main__":
    unittest.main()
