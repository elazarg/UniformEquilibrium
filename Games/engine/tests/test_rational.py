"""Exact rational re-evaluation and the snap-to-fractions hardening."""

from __future__ import annotations

import random
import sys
import unittest
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import evaluator, model, rational  # noqa: E402

SEED_KILLER_HAZARDS = [[0.25, 0.0, 0.25, 0.0], [0.0, 0.25, 0.0, 0.25]]


class ExactEvaluator(unittest.TestCase):
    def test_cyclic_solve_agrees_with_the_float_solve(self) -> None:
        rng = random.Random(71)
        for _ in range(200):
            period = rng.choice((1, 2, 3, 4, 6))
            constants = [Fraction(rng.randrange(-40, 41), 10) for _ in range(period)]
            hazards = [Fraction(rng.randrange(0, 101), 100) for _ in range(period)]
            exact = rational.cyclic_solve_exact(constants, hazards)
            approx = evaluator.cyclic_solve(
                [float(c) for c in constants], [float(h) for h in hazards]
            )
            for a, b in zip(exact, approx):
                self.assertAlmostEqual(float(a), b, delta=1e-9)

    def test_zero_absorption_is_the_never_absorbed_payoff(self) -> None:
        values = rational.cyclic_solve_exact([Fraction(3)] * 2, [Fraction(0)] * 2)
        self.assertEqual(values, [Fraction(0), Fraction(3)])

    def test_exploitability_agrees_with_the_float_evaluator(self) -> None:
        rng = random.Random(72)
        table = model.seed_table()
        exact_table = rational.rational_table(table)
        for _ in range(60):
            period = rng.choice((1, 2, 3))
            hazards = [
                [Fraction(rng.randrange(0, 21), 20) for _ in range(4)]
                for _ in range(period)
            ]
            exact = rational.exact_exploitability(exact_table, hazards)
            approx = evaluator.periodic_exploitability(
                table, [[float(v) for v in row] for row in hazards]
            )
            self.assertIsInstance(exact, Fraction)
            self.assertAlmostEqual(float(exact), approx, delta=1e-9)

    def test_exploitability_of_random_tables_agrees(self) -> None:
        rng = random.Random(73)
        for _ in range(30):
            table = reference.random_table(rng)
            period = rng.choice((1, 2, 3))
            hazards = [
                [Fraction(rng.randrange(0, 13), 12) for _ in range(4)]
                for _ in range(period)
            ]
            exact = rational.exact_exploitability(
                rational.rational_table(table), hazards
            )
            approx = evaluator.periodic_exploitability(
                table, [[float(v) for v in row] for row in hazards]
            )
            self.assertAlmostEqual(float(exact), approx, delta=1e-9)

    def test_exploitability_of_float_profile_helper(self) -> None:
        table = model.seed_table()
        value = rational.exact_exploitability_of(table, SEED_KILLER_HAZARDS)
        self.assertIsInstance(value, Fraction)
        self.assertAlmostEqual(
            float(value),
            evaluator.periodic_exploitability(table, SEED_KILLER_HAZARDS),
            delta=1e-12,
        )


class Hardening(unittest.TestCase):
    def setUp(self) -> None:
        self.table = model.seed_table()

    def test_snap_stays_in_the_unit_interval(self) -> None:
        self.assertEqual(rational.snap(-0.4, 4), Fraction(0))
        self.assertEqual(rational.snap(1.9, 4), Fraction(1))
        self.assertEqual(rational.snap(0.2538, 4), Fraction(1, 4))

    def test_harden_finds_an_exact_kill_of_the_seed(self) -> None:
        # The optimizer's period-two repair on the pairs {1,3} and {2,4} snaps
        # to quarters and still kills, with the margin computed exactly.
        floaty = [
            [0.25388513197428797, 0.0, 0.26542381285255384, 0.0],
            [0.0, 0.2538742308758058, 0.0, 0.26546169230486744],
        ]
        report = rational.harden(self.table, floaty)
        self.assertTrue(report["kills"])
        self.assertEqual(report["tier"], "exact")
        self.assertEqual(report["denominator"], 4)
        self.assertEqual(report["profile"]["hazards"], SEED_KILLER_HAZARDS)
        exact = Fraction(report["exploitability_exact"])
        self.assertEqual(exact, Fraction(128, 6475))
        self.assertLessEqual(exact, Fraction(model.EPS_KILL).limit_denominator(10**9))
        self.assertEqual(
            exact,
            rational.exact_exploitability(
                rational.rational_table(self.table),
                [
                    [Fraction(v).limit_denominator(4) for v in row]
                    for row in SEED_KILLER_HAZARDS
                ],
            ),
        )

    def test_harden_tries_smallest_denominators_first(self) -> None:
        report = rational.harden(self.table, SEED_KILLER_HAZARDS)
        tried = [attempt["denominator"] for attempt in report["attempts"]]
        self.assertEqual(tried, sorted(tried))
        self.assertEqual(tried[-1], report["denominator"])

    def test_harden_reports_failure_honestly(self) -> None:
        # Never quitting is nobody's equilibrium here, and no snapping of it
        # can kill, so the report must say so instead of returning a tier.
        report = rational.harden(self.table, [[0.0] * 4])
        self.assertFalse(report["kills"])
        self.assertIsNone(report["tier"])
        self.assertIsNotNone(report["exploitability_exact"])
        self.assertTrue(all(not a["kills"] for a in report["attempts"]))

    def test_harden_agrees_with_the_float_evaluator(self) -> None:
        report = rational.harden(self.table, SEED_KILLER_HAZARDS)
        snapped = report["profile"]["hazards"]
        self.assertAlmostEqual(
            report["exploitability"],
            evaluator.periodic_exploitability(self.table, snapped),
            delta=1e-9,
        )

    def test_harden_is_pure(self) -> None:
        hazards = [row[:] for row in SEED_KILLER_HAZARDS]
        rational.harden(self.table, hazards)
        self.assertEqual(hazards, SEED_KILLER_HAZARDS)


if __name__ == "__main__":
    unittest.main()
