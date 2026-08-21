"""Evaluator parity against the original experiment script."""

from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import evaluator  # noqa: E402

TOLERANCE = 1e-9


class EvaluatorParity(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ref = reference.load_reference()

    def cases(self, seed: int, trials: int):
        rng = random.Random(seed)
        for trial in range(trials):
            table = reference.random_table(rng)
            period = rng.choice((1, 2, 3, 4, 6, 8))
            hazards = reference.random_hazards(rng, period, trial % 2 == 1)
            yield table, hazards

    def test_periodic_exploitability_matches(self) -> None:
        worst = 0.0
        for table, hazards in self.cases(seed=101, trials=120):
            mine = evaluator.periodic_exploitability(table, hazards)
            theirs = self.ref.periodic_exploitability(table, hazards)
            worst = max(worst, abs(mine - theirs))
            self.assertLessEqual(abs(mine - theirs), TOLERANCE)
        self.assertLessEqual(worst, TOLERANCE)

    def test_periodic_exploitability_is_bit_identical(self) -> None:
        # The port keeps the arithmetic operation for operation, so the two
        # implementations should agree exactly, not merely to 1e-9.
        for table, hazards in self.cases(seed=202, trials=60):
            self.assertEqual(
                evaluator.periodic_exploitability(table, hazards),
                self.ref.periodic_exploitability(table, hazards),
            )

    def test_cyclic_solve_matches(self) -> None:
        rng = random.Random(303)
        for trial in range(400):
            period = rng.choice((1, 2, 3, 4, 5, 8))
            constants = [rng.uniform(-4.0, 4.0) for _ in range(period)]
            tiny = trial % 3 == 0
            hazards = [
                10.0 ** rng.uniform(-20.0, 0.0) if tiny else rng.uniform(0.0, 1.0)
                for _ in range(period)
            ]
            if trial % 7 == 0:
                hazards[rng.randrange(period)] = 1.0
            if trial % 11 == 0:
                hazards = [0.0] * period
            mine = evaluator.cyclic_solve(constants, hazards)
            theirs = self.ref.cyclic_solve(constants, hazards)
            self.assertEqual(mine, theirs)

    def test_phase_data_matches(self) -> None:
        rng = random.Random(404)
        for trial in range(80):
            table = reference.random_table(rng)
            hazard = reference.random_hazards(rng, 1, trial % 2 == 1)[0]
            mine = evaluator.phase_data(table, hazard)
            theirs = self.ref.phase_data(table, hazard)
            self.assertEqual(mine.absorption, theirs.absorption)
            self.assertEqual(mine.absorbed, theirs.absorbed)
            self.assertEqual(mine.quit_now, theirs.quit_now)
            self.assertEqual(mine.others_absorbed, theirs.others_absorbed)
            self.assertEqual(mine.others_absorption, theirs.others_absorption)

    def test_stationary_closed_form_matches(self) -> None:
        rng = random.Random(505)
        for _ in range(80):
            table = reference.random_table(rng)
            rates = [rng.uniform(0.0, 1.0) for _ in range(4)]
            self.assertEqual(
                evaluator.stationary_closed_form(table, rates),
                self.ref.stationary_closed_form(table, rates),
            )

    def test_one_quitter_report_matches(self) -> None:
        from engine import attacks

        rng = random.Random(606)
        for trial in range(120):
            table = reference.random_table(rng)
            size = rng.choice((2, 3, 4))
            cycle = tuple(rng.sample(range(4), size))
            tiny = trial % 2 == 1
            rates = [
                10.0 ** rng.uniform(-20.0, 0.0) if tiny else rng.uniform(0.0, 1.0)
                for _ in range(size)
            ]
            self.assertEqual(
                attacks.one_quitter_report(table, cycle, rates),
                self.ref.one_quitter_report(table, cycle, rates),
            )

    def test_detail_agrees_with_scalar(self) -> None:
        for table, hazards in self.cases(seed=707, trials=60):
            detail = evaluator.evaluate(table, hazards)
            scalar = evaluator.periodic_exploitability(table, hazards)
            self.assertEqual(detail["exploitability"], scalar)
            self.assertEqual(max(detail["per_player"]), scalar)
            self.assertEqual(len(detail["best_deviations"]), 4)
            for entry in detail["best_deviations"]:
                self.assertEqual(len(entry["policy"]), len(hazards))

    def test_detail_deviation_value_matches_its_policy(self) -> None:
        # The reported policy must be the one attaining the reported value.
        for table, hazards in self.cases(seed=808, trials=40):
            period = len(hazards)
            data = [evaluator.phase_data(table, hazards[t]) for t in range(period)]
            detail = evaluator.evaluate(table, hazards)
            for entry in detail["best_deviations"]:
                i, phase = entry["player"], entry["phase"]
                constants, policy_hazards = [], []
                for t in range(period):
                    if entry["policy"][t]:
                        constants.append(data[t].quit_now[i])
                        policy_hazards.append(1.0)
                    else:
                        constants.append(data[t].others_absorbed[i])
                        policy_hazards.append(data[t].others_absorption[i])
                values = evaluator.cyclic_solve(constants, policy_hazards)
                self.assertEqual(values[phase], entry["value"])


if __name__ == "__main__":
    unittest.main()
