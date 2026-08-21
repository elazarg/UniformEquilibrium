"""Battery levels, library replay, and the evidence-tier bookkeeping."""

from __future__ import annotations

import math
import sys
import time
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import attacks, battery, evaluator, library, model  # noqa: E402

#: A period-two profile that kills the Solan-Vieille seed: the known repair on
#: the pairs {1,3} and {2,4}, snapped to quarters.
SEED_KILLER = {
    "period": 2,
    "hazards": [[0.25, 0.0, 0.25, 0.0], [0.0, 0.25, 0.0, 0.25]],
}


class LibraryReplay(unittest.TestCase):
    def setUp(self) -> None:
        self.table = model.seed_table()

    def test_empty_library_is_the_identity_for_the_minimum(self) -> None:
        replay = library.replay_profiles(self.table, [])
        self.assertEqual(replay["exploitability"], math.inf)
        self.assertIsNone(replay["profile"])
        self.assertEqual(replay["tried"], 0)

    def test_replay_finds_the_best_profile(self) -> None:
        weak = {"period": 1, "hazards": [[0.5, 0.5, 0.5, 0.5]]}
        replay = library.replay_profiles(self.table, [weak, SEED_KILLER])
        self.assertEqual(replay["index"], 1)
        self.assertEqual(
            replay["exploitability"],
            evaluator.periodic_exploitability(self.table, SEED_KILLER["hazards"]),
        )
        self.assertLess(replay["exploitability"], model.EPS_KILL)

    def test_replay_accepts_records_and_bare_matrices(self) -> None:
        record = {"id": "p1", "profile": SEED_KILLER, "source": {"game": "sequencer"}}
        bare = SEED_KILLER["hazards"]
        expected = evaluator.periodic_exploitability(self.table, bare)
        for entry in (record, bare, SEED_KILLER):
            replay = library.replay_profiles(self.table, [entry])
            self.assertEqual(replay["exploitability"], expected)
        replay = library.replay_profiles(self.table, [record])
        self.assertEqual(
            replay["source"], {"id": "p1", "source": {"game": "sequencer"}}
        )

    def test_kills_lists_every_killing_profile(self) -> None:
        weak = {"period": 1, "hazards": [[0.5, 0.5, 0.5, 0.5]]}
        found = library.kills(self.table, [weak, SEED_KILLER])
        self.assertEqual([entry["index"] for entry in found], [1])

    def test_replay_is_pure(self) -> None:
        profiles = [dict(SEED_KILLER)]
        before = model.canonical_json(profiles)
        library.replay_profiles(self.table, profiles)
        self.assertEqual(model.canonical_json(profiles), before)

    def test_explain_matches_the_evaluator(self) -> None:
        detail = library.explain(self.table, SEED_KILLER)
        self.assertEqual(
            detail["exploitability"],
            evaluator.periodic_exploitability(self.table, SEED_KILLER["hazards"]),
        )
        self.assertEqual(detail["profile"], SEED_KILLER)


class BatteryLevels(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.table = model.seed_table()
        cls.timings: dict[str, float] = {}
        cls.results: dict[str, dict] = {}
        for level in ("replay", "quick", "standard"):
            started = time.perf_counter()
            cls.results[level] = battery.run_level(cls.table, level)
            cls.timings[level] = time.perf_counter() - started

    def test_response_shape(self) -> None:
        for level, result in self.results.items():
            self.assertEqual(result["level"], level)
            self.assertIn("score", result)
            self.assertIn("binding_attack", result)
            self.assertIn("elapsed", result)
            self.assertEqual(set(result["breakdown"]), set(battery.ATTACK_NAMES))
            for name, entry in result["breakdown"].items():
                if entry is not None:
                    self.assertIn("exploitability", entry)

    def test_replay_without_library_attacks_nothing(self) -> None:
        result = self.results["replay"]
        self.assertEqual(result["score"], math.inf)
        self.assertIsNone(result["binding_attack"])
        self.assertEqual(result["breakdown"]["library_replay"]["profiles_tried"], 0)
        for name in battery.ATTACK_NAMES[1:]:
            self.assertIsNone(result["breakdown"][name])
        self.assertEqual(
            battery.tier_for(result["score"], "replay"), "unattacked"
        )

    def test_replay_uses_the_library(self) -> None:
        result = battery.run_level(self.table, "replay", profiles=[SEED_KILLER])
        self.assertEqual(result["binding_attack"], "library_replay")
        self.assertLess(result["score"], model.EPS_KILL)
        self.assertEqual(battery.killing_profile(result), SEED_KILLER)

    def test_quick_runs_all_four_families(self) -> None:
        result = self.results["quick"]
        for name in battery.ATTACK_NAMES[1:]:
            self.assertIsNotNone(result["breakdown"][name])
        self.assertLess(result["score"], math.inf)

    def test_standard_reproduces_the_experiment_battery(self) -> None:
        full = battery.run_full_battery(self.table)
        self.assertEqual(self.results["standard"]["score"], full["score"])
        self.assertEqual(
            self.results["standard"]["binding_attack"], full["binding_attack"]
        )

    def test_standard_is_at_least_as_strong_as_quick(self) -> None:
        # More search can only lower the minimum found.
        self.assertLessEqual(
            self.results["standard"]["score"], self.results["quick"]["score"]
        )

    def test_levels_are_ordered_in_cost(self) -> None:
        self.assertLess(self.timings["replay"], self.timings["quick"])
        self.assertLess(self.timings["quick"], self.timings["standard"])

    def test_quick_is_interactive(self) -> None:
        # DESIGN.md budgets the quick level at under half a second; the bound
        # here is loose so an unrelated load spike does not fail the suite.
        self.assertLess(self.timings["quick"], 2.0)

    def test_early_abandon_skips_the_rest(self) -> None:
        result = battery.run_level(
            self.table, "standard", profiles=[SEED_KILLER], abandon_at=model.EPS_KILL
        )
        self.assertTrue(result["abandoned"])
        self.assertEqual(result["binding_attack"], "library_replay")
        for name in battery.ATTACK_NAMES[1:]:
            self.assertIsNone(result["breakdown"][name])

    def test_unknown_level_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            battery.run_level(self.table, "thorough")

    def test_summarize_reports_tier_and_killing_profile(self) -> None:
        summary = battery.summarize(self.results["standard"])
        self.assertTrue(summary["killed"])
        self.assertEqual(summary["tier"], "numerical-wide")
        self.assertIsNotNone(summary["killing_profile"])
        replay = library.replay_profiles(self.table, [summary["killing_profile"]])
        self.assertLessEqual(replay["exploitability"], model.EPS_KILL)

    def test_tier_thresholds(self) -> None:
        self.assertEqual(battery.tier_for(0.005, "standard"), "numerical-wide")
        self.assertEqual(battery.tier_for(0.015, "standard"), "numerical-narrow")
        self.assertEqual(
            battery.tier_for(model.EPS_KILL, "standard"), "numerical-narrow"
        )
        self.assertEqual(
            battery.tier_for(0.5 * model.EPS_KILL, "standard"), "numerical-narrow"
        )
        self.assertEqual(battery.tier_for(0.03, "quick"), "survivor-quick")
        self.assertEqual(battery.tier_for(0.03, "standard"), "survivor-standard")
        self.assertEqual(battery.tier_for(0.03, "deep"), "survivor-deep")
        self.assertEqual(battery.tier_for(0.03, "replay"), "unattacked")
        self.assertEqual(battery.tier_for(0.001, "quick", exact=True), "exact")

    def test_status_thresholds(self) -> None:
        self.assertEqual(battery.status_for(0.001, "deep"), "killed")
        self.assertEqual(battery.status_for(0.5, "deep"), "verified")
        self.assertEqual(battery.status_for(0.5, "quick"), "proposed")

    def test_killing_profile_is_none_when_nothing_killed(self) -> None:
        result = self.results["quick"]
        self.assertGreater(result["score"], model.EPS_KILL)
        self.assertIsNone(battery.killing_profile(result))

    def test_killing_profile_rejects_an_unreplayable_fine_block_kill(self) -> None:
        # Attack B's number is a fine-block-limit value; if the literal hazard
        # matrix does not also kill under the shared evaluator there is no
        # profile to hand to the library, and none must be handed over.
        result = {
            "score": 0.001,
            "binding_attack": "one_quitter_cyclic",
            "breakdown": {
                "one_quitter_cyclic": {
                    "exploitability": 0.001,
                    "profile": {"period": 1, "hazards": [[0.1, 0.0, 0.0, 0.0]]},
                    "profile_exploitability": 0.9,
                    "fine_block_limit": True,
                }
            },
        }
        self.assertIsNone(battery.killing_profile(result))
        result["breakdown"]["one_quitter_cyclic"]["profile_exploitability"] = 0.001
        self.assertIsNotNone(battery.killing_profile(result))


class ThreadSafety(unittest.TestCase):
    """The battery is called from the server's job threads.

    Every attack is a pure function of the table: the random starts come from
    ``random.Random`` instances created inside the call, never from the shared
    module-level generator, and nothing writes module state.  Concurrent calls
    must therefore return exactly what a serial call returns.
    """

    def test_concurrent_runs_match_serial_runs(self) -> None:
        from concurrent.futures import ThreadPoolExecutor

        from engine import curated

        tables = [
            model.table_from_wire(entry["table"])
            for entry in curated.curated_tables()
        ]
        serial = [battery.run_level(table, "quick")["score"] for table in tables]
        with ThreadPoolExecutor(max_workers=4) as pool:
            scores = pool.map(
                lambda table: battery.run_level(table, "quick")["score"], tables
            )
            concurrent = list(scores)
        self.assertEqual(concurrent, serial)

    def test_repeated_runs_are_deterministic(self) -> None:
        table = model.seed_table()
        first = battery.run_level(table, "quick")
        second = battery.run_level(table, "quick")
        self.assertEqual(first["score"], second["score"])
        self.assertEqual(first["binding_attack"], second["binding_attack"])


class DeepLevel(unittest.TestCase):
    @unittest.skipUnless(
        reference.slow_tests_enabled(),
        "the deep level takes about a minute; set GAMES_SLOW_TESTS=1",
    )
    def test_deep_matches_the_experiment_stress_test(self) -> None:
        table = model.seed_table()
        result = battery.run_level(table, "deep")
        deep = attacks.deep_reattack(table)
        self.assertEqual(result["score"], deep["score"])
        self.assertEqual(result["binding_attack"], deep["binding_attack"])
        self.assertEqual(result["level"], "deep")


if __name__ == "__main__":
    unittest.main()
