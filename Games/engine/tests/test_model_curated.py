"""Wire-format validation, hashing, and the curated table loader."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import curated, model  # noqa: E402


class WireFormats(unittest.TestCase):
    def setUp(self) -> None:
        self.table = model.seed_table()

    def test_table_round_trip(self) -> None:
        wire = model.table_to_wire(self.table)
        self.assertEqual(len(wire), 16)
        self.assertEqual(model.table_from_wire(wire), self.table)

    def test_label_round_trip(self) -> None:
        labels = model.table_to_labels(self.table)
        self.assertEqual(model.table_from_labels(labels), self.table)
        self.assertIn("{1,3}", labels)

    def test_label_format_matches_the_experiment(self) -> None:
        ref = reference.load_reference()
        self.assertEqual(
            model.table_to_labels(self.table), ref.table_to_json(ref.seed_table())
        )
        self.assertEqual(model.seed_table(), ref.seed_table())

    def test_table_rejects_bad_payloads(self) -> None:
        wire = model.table_to_wire(self.table)
        for broken in (
            wire[:-1],
            [row + [0.0] for row in wire],
            "not a table",
            [[0.0, 0.0, 0.0, 0.0]] * 15 + [["x", 0.0, 0.0, 0.0]],
        ):
            with self.assertRaises(model.ModelError):
                model.table_from_wire(broken)

    def test_table_rejects_a_nonzero_empty_row(self) -> None:
        wire = model.table_to_wire(self.table)
        wire[0][2] = 0.5
        with self.assertRaises(model.ModelError):
            model.table_from_wire(wire)

    def test_table_rejects_out_of_range_payoffs(self) -> None:
        wire = model.table_to_wire(self.table)
        wire[3][1] = 4.5
        with self.assertRaises(model.ModelError):
            model.table_from_wire(wire)

    def test_profile_round_trip(self) -> None:
        hazards = [[0.1, 0.2, 0.3, 0.4], [0.0, 0.0, 1.0, 0.5]]
        wire = model.hazards_to_wire(hazards)
        self.assertEqual(wire["period"], 2)
        self.assertEqual(model.hazards_from_wire(wire), hazards)

    def test_profile_rejects_bad_payloads(self) -> None:
        for broken in (
            {"period": 3, "hazards": [[0.0] * 4]},
            {"period": 1, "hazards": [[0.0] * 3]},
            {"period": 1, "hazards": [[1.5, 0.0, 0.0, 0.0]]},
            {"period": 1, "hazards": [[-0.1, 0.0, 0.0, 0.0]]},
            {"period": 0, "hazards": []},
            {"period": 9, "hazards": [[0.0] * 4] * 9},
            {"hazards": "no"},
            [0.1, 0.2],
        ):
            with self.assertRaises(model.ModelError):
                model.hazards_from_wire(broken)

    def test_profile_period_defaults_to_the_row_count(self) -> None:
        self.assertEqual(
            model.hazards_from_wire({"hazards": [[0.0] * 4] * 3}), [[0.0] * 4] * 3
        )

    def test_hashes_are_stable_and_discriminating(self) -> None:
        other = model.table_from_wire(model.table_to_wire(self.table))
        self.assertEqual(model.table_hash(self.table), model.table_hash(other))
        rows = [list(row) for row in model.table_to_wire(self.table)]
        rows[5][0] += 0.5
        self.assertNotEqual(
            model.table_hash(self.table), model.table_hash(model.table_from_wire(rows))
        )
        self.assertEqual(
            model.profile_hash([[0.25] * 4]), model.profile_hash([[0.25] * 4])
        )

    def test_validate_helpers_accept_and_reject(self) -> None:
        self.assertIsNone(model.validate_table(model.table_to_wire(self.table)))
        self.assertIsNone(
            model.validate_profile({"period": 1, "hazards": [[0.1, 0.2, 0.3, 0.4]]})
        )
        with self.assertRaises(model.ValidationError):
            model.validate_table([[0.0] * 4] * 15)
        with self.assertRaises(model.ModelError):
            model.validate_profile({"period": 2, "hazards": [[0.0] * 4]})
        self.assertIs(model.ValidationError, model.ModelError)
        self.assertTrue(issubclass(model.ModelError, ValueError))

    def test_json_safe_replaces_non_finite_floats(self) -> None:
        import json
        import math

        payload = {
            "score": math.inf,
            "rows": [1.0, -math.inf, float("nan"), "text", None, True],
            "nested": {"a": math.inf},
        }
        safe = model.json_safe(payload)
        # DESIGN.md's wire contract: inf -> 1e9, -inf -> -1e9, nan -> null,
        # and a consumer reads anything at or above NO_BOUND as "nothing
        # found by this attack" rather than as a score.
        self.assertEqual(safe["score"], model.NO_BOUND)
        self.assertEqual(
            safe["rows"], [1.0, -model.NO_BOUND, None, "text", None, True]
        )
        self.assertEqual(safe["nested"]["a"], model.NO_BOUND)
        self.assertGreater(model.NO_BOUND, model.EPS_KILL)

        def reject(token):
            raise AssertionError(token)

        json.loads(json.dumps(safe), parse_constant=reject)

    def test_masks_and_labels(self) -> None:
        self.assertEqual(model.mask_of([0, 2]), 5)
        self.assertEqual(model.members(5), (0, 2))
        self.assertEqual(model.mask_label(5), "{1,3}")
        self.assertEqual(model.solo(self.table, 1), 1.0)
        self.assertEqual(model.clamp_payoff(9.0), model.PAYOFF_HI)


class Curated(unittest.TestCase):
    def setUp(self) -> None:
        self.entries = curated.curated_tables()

    def test_seed_and_three_chain_bests_are_present(self) -> None:
        ids = [entry["id"] for entry in self.entries]
        self.assertEqual(ids[0], "solan_vieille_seed")
        self.assertEqual(sorted(ids[1:]), ["chain_40", "chain_41", "chain_42"])

    def test_entries_are_legal_wire_tables(self) -> None:
        for entry in self.entries:
            table = model.table_from_wire(entry["table"])
            self.assertEqual(len(table), 16)
            self.assertIsInstance(entry["note"], str)
            self.assertTrue(entry["note"])

    def test_seed_matches_the_model(self) -> None:
        self.assertEqual(
            model.table_from_wire(self.entries[0]["table"]), model.seed_table()
        )

    def test_known_scores_come_from_the_experiment(self) -> None:
        import json

        with curated.RESULTS_PATH.open(encoding="utf-8") as handle:
            results = json.load(handle)
        expected = {
            f"chain_{chain['seed']}": chain["best"]["deep_reattack"]["score"]
            for chain in results["chains"]
        }
        expected["solan_vieille_seed"] = results["seed_table"]["battery"]["score"]
        for entry in self.entries:
            self.assertEqual(entry["known_score"], expected[entry["id"]])
            # None of these survived the kill threshold, so nothing here may be
            # presented as a counterexample candidate.
            self.assertLess(entry["known_score"], model.EPS_KILL)

    def test_lookup_helpers(self) -> None:
        self.assertEqual(
            curated.curated_table("solan_vieille_seed"), model.seed_table()
        )
        self.assertIsNone(curated.curated_table("nope"))
        self.assertEqual(set(curated.curated_by_id()), {e["id"] for e in self.entries})

    def test_missing_results_file_degrades_to_the_seed(self) -> None:
        entries = curated.curated_tables(Path("/nonexistent/results.json"))
        self.assertEqual([entry["id"] for entry in entries], ["solan_vieille_seed"])
        self.assertIsNone(entries[0]["known_score"])


if __name__ == "__main__":
    unittest.main()
