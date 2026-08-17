import tempfile
import unittest
from pathlib import Path

from experiments.closure_native_development_bridges import run


class ClosureNativeDevelopmentBridgesTest(unittest.TestCase):
    def test_recovery_is_blind_to_frozen_and_translating_rounds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = run(Path(directory))
        self.assertTrue(result["recovery_test_blind"])
        self.assertEqual(result["frozen_round"]["classification"], "FROZEN_OR_NONTRANSLATING")
        self.assertEqual(result["translating_round"]["classification"], "TRANSLATING")
        self.assertTrue(result["translating_round"]["moves_some_presentation"])

    def test_bridges_supply_the_missing_interlevel_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            bridge = run(Path(directory))["bridge_composition"]
        self.assertTrue(bridge["bridge01_injective"])
        self.assertTrue(bridge["bridge12_injective"])
        self.assertTrue(bridge["global_return_is_identity_on_earlier_level"])
        self.assertFalse(bridge["absolute_carrier_identity_claimed"])

    def test_assertion_is_not_translation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            syntax = run(Path(directory))["syntactic_axiometry"]
        self.assertFalse(syntax["asserted_axiom_is_derived_in_base"])
        self.assertFalse(syntax["identity_substitution_is_interpretation"])
        self.assertTrue(syntax["genuine_substitution_is_interpretation"])
