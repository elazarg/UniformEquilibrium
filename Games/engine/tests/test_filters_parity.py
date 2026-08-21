"""Filter parity: identical pass/fail and identical detail, key for key."""

from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import filters, model  # noqa: E402

MARGINS = (0.0, 0.05, 0.1, 0.3)


class FilterParity(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ref = reference.load_reference()

    def tables(self, seed: int, trials: int):
        """Uniform random tables plus perturbations of the seed table.

        Uniform tables almost always die at filter 1, so they exercise only the
        rejection paths; perturbing the Solan-Vieille seed with the
        experiment's own kernel produces tables that reach filters 4, 5 and 6.
        """

        rng = random.Random(seed)
        base = self.ref.seed_table()
        yield base
        for trial in range(trials):
            if trial % 3 == 0:
                yield reference.random_table(rng)
            else:
                yield self.ref.perturb(base, rng, 0.25, 0.6, 0.2)

    def test_run_filters_matches(self) -> None:
        reached = set()
        for table in self.tables(seed=11, trials=150):
            for margin in MARGINS:
                mine = filters.run_filters(table, margin)
                theirs = self.ref.run_filters(table, margin)
                self.assertEqual(mine, theirs)
                for name in filters.FILTER_NAMES:
                    if mine[name]["pass"]:
                        reached.add(name)
        # Guard against a vacuous comparison: every filter must have passed at
        # least once across the corpus, so the pass branches are compared too.
        self.assertEqual(reached, set(filters.FILTER_NAMES))

    def test_first_failing_filter_matches(self) -> None:
        seen = set()
        for table in self.tables(seed=22, trials=150):
            for margin in MARGINS:
                mine = filters.first_failing_filter(table, margin)
                theirs = self.ref.first_failing_filter(table, margin)
                self.assertEqual(mine, theirs)
                seen.add(mine)
        self.assertIn(None, seen)

    def test_lcp_screen_matches(self) -> None:
        for table in self.tables(seed=33, trials=120):
            self.assertEqual(
                filters.lcp_simplex_screen(table),
                self.ref.lcp_simplex_screen(table),
            )

    def test_component_helpers_match(self) -> None:
        for table in self.tables(seed=44, trials=80):
            self.assertEqual(
                filters.iterated_normal_core(table),
                self.ref.iterated_normal_core(table),
            )
            self.assertEqual(
                filters.normalized_matrix(table), self.ref.normalized_matrix(table)
            )
            for margin in MARGINS:
                self.assertEqual(
                    filters.preemption_edges(table, margin),
                    self.ref.preemption_edges(table, margin),
                )
                self.assertEqual(
                    filters.viable_owners(table, margin),
                    self.ref.viable_owners(table, margin),
                )

    def test_solve_linear_matches(self) -> None:
        rng = random.Random(55)
        for _ in range(200):
            size = rng.choice((1, 2, 3, 4, 5))
            matrix = [
                [rng.uniform(-3.0, 3.0) for _ in range(size)] for _ in range(size)
            ]
            rhs = [rng.uniform(-3.0, 3.0) for _ in range(size)]
            self.assertEqual(
                filters.solve_linear(matrix, rhs), self.ref.solve_linear(matrix, rhs)
            )

    def test_api_report_shape(self) -> None:
        table = self.ref.seed_table()
        report = filters.api_report(table, model.MARGIN_G)
        # DESIGN.md settles the wire keys as the experiment's verbatim
        # FILTER_NAMES, so filter 6 travels only as "6_no_lcp_solution".
        self.assertEqual(set(report["filters"]), set(filters.FILTER_NAMES))
        self.assertIn("6_no_lcp_solution", report["filters"])
        checks = filters.run_filters(table, model.MARGIN_G)
        self.assertEqual(report["pass"], checks["all_1_to_6"])
        self.assertEqual(report["pass_1_to_5"], checks["all_1_to_5"])
        self.assertTrue(report["pass"])


if __name__ == "__main__":
    unittest.main()
