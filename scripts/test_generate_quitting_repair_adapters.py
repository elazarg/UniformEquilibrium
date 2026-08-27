from __future__ import annotations

import unittest

from scripts import generate_quitting_repair_adapters as adapters


class QuittingRepairAdapterTests(unittest.TestCase):
    def test_committed_adapter_data_is_fresh(self) -> None:
        self.assertEqual(adapters.check_adapter(), [])

    def test_stale_generated_block_is_rejected(self) -> None:
        actual = adapters.ADAPTER.read_text(encoding="utf-8")
        stale = actual.replace(
            "def value : Payoff Player := ![0, 0]",
            "def value : Payoff Player := ![0, 1]",
            1,
        )
        self.assertNotEqual(adapters.check_adapter_text(stale), [])

    def test_source_and_adapter_are_the_promoted_pair(self) -> None:
        self.assertTrue(adapters.TABLE.is_file())
        self.assertTrue(adapters.ADAPTER.is_file())
        self.assertEqual(adapters.TABLE.name, "cutoff_one_mixed.json")
        self.assertIn(
            adapters.ACTUAL_CUTOFF_FINGERPRINT,
            adapters.render_block(adapters.load_promoted_game()),
        )


if __name__ == "__main__":
    unittest.main()
