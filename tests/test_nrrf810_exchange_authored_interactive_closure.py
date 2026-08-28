import inspect
import json
import shutil
import socket
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from experiments import nrrf810_exchange_authored_interactive_closure as closure


ROOT = Path(__file__).parents[1]
RUN = (
    ROOT
    / "runs/nrrf810_exchange_authored_interactive_closure/bitstamp_live_20260828T155640Z"
)
MULTI = ROOT / "runs/nrrf810_exchange_authored_interactive_closure/multi_window_summary.json"


class ExchangeAuthoredInteractiveClosureTest(unittest.TestCase):
    def test_canonical_live_data_replays_offline(self) -> None:
        with mock.patch.object(socket, "socket", side_effect=AssertionError("network forbidden")):
            result = closure.verify_run(RUN)

        summary = result["summary"]
        self.assertTrue(result["verified"])
        self.assertEqual(summary["exchange_authored_events"], 9809)
        self.assertEqual(summary["natural_forms_unfolded"], 4897)
        self.assertEqual(summary["natural_forms_closed"], 4679)
        self.assertEqual(summary["natural_forms_open_at_capture_boundary"], 218)
        self.assertEqual(summary["partial_boundary_events"], 211)
        self.assertEqual(summary["inf_path_translations"], 22)
        self.assertEqual(summary["contradicted_forms"], 0)
        self.assertEqual(summary["source_chain_gaps"], 0)

    def test_multi_window_counts_are_exact_sums(self) -> None:
        value = json.loads(MULTI.read_text())
        runs = value["runs"]
        totals = value["totals"]

        self.assertEqual(value["run_count"], len(runs))
        self.assertEqual(totals["exchange_authored_events"], sum(r["event_count"] for r in runs))
        self.assertEqual(
            totals["natural_forms_unfolded"], sum(r["natural_forms_unfolded"] for r in runs)
        )
        self.assertEqual(
            totals["natural_forms_closed"], sum(r["natural_forms_closed"] for r in runs)
        )
        self.assertEqual(
            totals["natural_forms_open_at_capture_boundaries"],
            sum(r["natural_forms_open_at_capture_boundary"] for r in runs),
        )
        self.assertTrue(all(r["contradicted_forms"] == 0 for r in runs))
        self.assertTrue(all(r["source_chain_gaps"] == 0 for r in runs))

    def test_price_and_profit_are_not_natural_form_fields(self) -> None:
        source = inspect.getsource(closure.form_from_message)
        self.assertNotIn("price", source)
        self.assertNotIn("amount", source)
        self.assertNotIn("profit", source)
        self.assertEqual(
            closure.FORM_FIELDS,
            ("channel", "order_id", "order_type", "order_subtype"),
        )

    def test_raw_message_tampering_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            forged = Path(temporary) / "forged"
            shutil.copytree(RUN, forged)
            raw = forged / "raw_messages.jsonl"
            raw.write_bytes(raw.read_bytes().replace(b"order_created", b"order_changed", 1))
            with self.assertRaises(ValueError):
                closure.verify_run(forged)


if __name__ == "__main__":
    unittest.main()
