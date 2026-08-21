"""Attack parity: identical optimizer output, not merely a similar score.

Nelder-Mead is chaotic, so agreeing on the returned minimum to many digits is
only possible if every arithmetic step matches; these tests therefore compare
the reported rates, schedules and hazards as well as the exploitability.
"""

from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import attacks, battery  # noqa: E402


def parity_tables(ref) -> list:
    rng = random.Random(9001)
    base = ref.seed_table()
    return [base, ref.perturb(base, rng, 0.25, 0.6, 0.2)]


class NelderMeadParity(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ref = reference.load_reference()

    def test_nelder_mead_matches(self) -> None:
        rng = random.Random(12)
        for _ in range(40):
            size = rng.choice((1, 2, 4, 6))
            centre = [rng.uniform(-2.0, 2.0) for _ in range(size)]
            weights = [rng.uniform(0.2, 3.0) for _ in range(size)]

            def objective(z, centre=centre, weights=weights):
                return sum(
                    w * (z[k] - c) ** 2 for k, (c, w) in enumerate(zip(centre, weights))
                ) + 0.1 * sum(abs(v) for v in z)

            start = [rng.uniform(-1.0, 1.0) for _ in range(size)]
            self.assertEqual(
                attacks.nelder_mead(objective, start, step=1.5, max_iter=120),
                self.ref.nelder_mead(objective, start, step=1.5, max_iter=120),
            )

    def test_sigmoid_and_logit_match(self) -> None:
        rng = random.Random(13)
        for _ in range(500):
            z = rng.uniform(-80.0, 80.0)
            self.assertEqual(attacks.sigmoid(z), self.ref.sigmoid(z))
            x = rng.uniform(-0.5, 1.5)
            self.assertEqual(attacks.logit(x), self.ref.logit(x))

    def test_schedule_enumerations_match(self) -> None:
        self.assertEqual(attacks.CYCLIC_ORDERS, self.ref.CYCLIC_ORDERS)
        self.assertEqual(attacks.PAIR_SCHEDULES, self.ref.PAIR_SCHEDULES)
        self.assertEqual(attacks.DEEP_PAIR_SCHEDULES, self.ref.DEEP_PAIR_SCHEDULES)
        self.assertEqual(attacks.STATIONARY_GRID, self.ref.STATIONARY_GRID)
        self.assertEqual(attacks.DEEP_GRID, self.ref.DEEP_GRID)
        self.assertEqual(
            [name for name, _ in battery.ATTACK_ORDER],
            [name for name, _ in self.ref.ATTACK_ORDER],
        )


class AttackParity(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ref = reference.load_reference()
        cls.tables = parity_tables(cls.ref)

    def assertReportMatches(self, mine: dict, theirs: dict) -> None:
        for key, value in theirs.items():
            self.assertIn(key, mine)
            self.assertEqual(mine[key], value, msg=f"key {key}")

    def test_attack_stationary_matches(self) -> None:
        for table in self.tables:
            self.assertReportMatches(
                attacks.attack_stationary(table), self.ref.attack_stationary(table)
            )

    def test_attack_one_quitter_matches(self) -> None:
        for table in self.tables:
            self.assertReportMatches(
                attacks.attack_one_quitter(table), self.ref.attack_one_quitter(table)
            )

    def test_attack_general_periodic_matches(self) -> None:
        for table in self.tables:
            self.assertReportMatches(
                attacks.attack_general_periodic(table),
                self.ref.attack_general_periodic(table),
            )

    def test_attack_two_quitter_matches(self) -> None:
        table = self.tables[0]
        self.assertReportMatches(
            attacks.attack_two_quitter(table), self.ref.attack_two_quitter(table)
        )

    def test_full_battery_matches(self) -> None:
        table = self.tables[0]
        mine = battery.run_full_battery(table)
        theirs = self.ref.run_battery(table)
        self.assertEqual(mine["score"], theirs["score"])
        self.assertEqual(mine["binding_attack"], theirs["binding_attack"])
        self.assertEqual(mine["abandoned"], theirs["abandoned"])
        for name, entry in theirs["breakdown"].items():
            self.assertReportMatches(mine["breakdown"][name], entry)

    def test_battery_early_abandon_matches(self) -> None:
        table = self.tables[0]
        for abandon_at in (0.1, 0.05):
            mine = battery.run_full_battery(table, abandon_at)
            theirs = self.ref.run_battery(table, abandon_at)
            self.assertEqual(mine["score"], theirs["score"])
            self.assertEqual(mine["binding_attack"], theirs["binding_attack"])
            self.assertEqual(mine["abandoned"], theirs["abandoned"])
            self.assertTrue(theirs["abandoned"])
            for name, entry in theirs["breakdown"].items():
                if entry is None:
                    self.assertIsNone(mine["breakdown"][name])
                else:
                    self.assertReportMatches(mine["breakdown"][name], entry)

    def test_one_quitter_profile_is_reported_honestly(self) -> None:
        # Attack B scores in the fine-block limit; the literal hazard matrix
        # allows collisions, so the two numbers may differ and the report must
        # carry both rather than pass B's number off as the profile's.
        from engine import evaluator

        table = self.tables[0]
        report = attacks.attack_one_quitter(table)
        hazards = report["profile"]["hazards"]
        self.assertEqual(
            report["profile_exploitability"],
            evaluator.periodic_exploitability(table, hazards),
        )
        self.assertTrue(report["fine_block_limit"])

    @unittest.skipUnless(
        reference.slow_tests_enabled(),
        "deep re-attack parity takes about two minutes; set GAMES_SLOW_TESTS=1",
    )
    def test_deep_reattack_matches(self) -> None:
        table = self.tables[0]
        mine = attacks.deep_reattack(table)
        theirs = self.ref.deep_reattack(table)
        self.assertEqual(mine["score"], theirs["score"])
        self.assertEqual(mine["binding_attack"], theirs["binding_attack"])
        for name, entry in theirs["breakdown"].items():
            self.assertReportMatches(mine["breakdown"][name], entry)


if __name__ == "__main__":
    unittest.main()
