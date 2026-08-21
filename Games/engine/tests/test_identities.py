"""The experiment's evaluator self-check, run against the engine.

Four independent identities:

* the closed-form on-path recursion agrees with the decomposition of a phase
  into the deviator's own quit branch and continue branch;
* exploitability is never negative, since the deviator's pure-policy maximum
  dominates his on-path mixture;
* the same non-negativity holds for the separate one-quitter evaluator; and
* for period one the policy enumeration reproduces the stationary closed form
  ``max(quit-now value, never value) - on-path value``.

Half the trials draw hazards log-uniformly down to ``1e-20``, which is where
the cyclic solve's absorption term is delicate and where the reference's
hazard formulation earns its keep.  The stationary comparison deliberately
skips those trials: its reference form subtracts a product from one, so below
roughly ``1e-8`` the comparison would measure the reference's own error.

The loop mirrors the experiment's ``self_check`` step for step and draws from
the same seeded stream, so the resulting metrics are compared against it
exactly.
"""

from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import reference  # noqa: E402
from engine import attacks, evaluator  # noqa: E402
from engine.model import NONEMPTY, PAYOFF_HI, PAYOFF_LO, PLAYERS  # noqa: E402


def self_check(trials: int = 300, seed: int = 7) -> dict:
    rng = random.Random(seed)
    decomposition = 0.0
    negativity = 0.0
    cyclic_negativity = 0.0
    stationary_gap = 0.0
    stationary_trials = 0
    for trial in range(trials):
        rows = [[0.0] * 4 for _ in range(16)]
        for mask in NONEMPTY:
            for i in PLAYERS:
                rows[mask][i] = rng.uniform(PAYOFF_LO, PAYOFF_HI)
        table = tuple(tuple(row) for row in rows)
        period = rng.choice((1, 2, 3, 4))
        tiny = trial % 2 == 1

        def draw() -> float:
            if tiny:
                return 10.0 ** rng.uniform(-20.0, 0.0)
            return rng.uniform(0.0, 1.0)

        hazards = [[draw() for _ in PLAYERS] for _ in range(period)]
        cycle_size = rng.choice((2, 3, 4))
        cycle = tuple(rng.sample(PLAYERS, cycle_size))
        cyclic_value = attacks.one_quitter_report(
            table, cycle, [draw() for _ in range(cycle_size)]
        )[0]
        cyclic_negativity = max(cyclic_negativity, -cyclic_value)
        data = [evaluator.phase_data(table, hazards[t]) for t in range(period)]
        stage_hazards = [data[t].absorption for t in range(period)]
        on_path = [
            evaluator.cyclic_solve(
                [data[t].absorbed[j] for t in range(period)], stage_hazards
            )
            for j in PLAYERS
        ]
        for i in PLAYERS:
            for t in range(period):
                rate = hazards[t][i]
                follower = on_path[i][(t + 1) % period]
                branch = rate * data[t].quit_now[i] + (1.0 - rate) * (
                    data[t].others_absorbed[i]
                    + (1.0 - data[t].others_absorption[i]) * follower
                )
                decomposition = max(decomposition, abs(on_path[i][t] - branch))
        value = evaluator.periodic_exploitability(table, hazards)
        negativity = max(negativity, -value)
        if period == 1 and not tiny:
            stationary_trials += 1
            closed = evaluator.stationary_closed_form(table, hazards[0])
            stationary_gap = max(stationary_gap, abs(closed - value))
    return {
        "trials": trials,
        "rng_seed": seed,
        "on_path_decomposition_max_error": decomposition,
        "max_negative_exploitability": negativity,
        "max_negative_one_quitter_exploitability": cyclic_negativity,
        "stationary_closed_form_trials": stationary_trials,
        "stationary_closed_form_max_error": stationary_gap,
        "passed": (
            decomposition < 1e-9
            and negativity < 1e-9
            and cyclic_negativity < 1e-9
            and stationary_gap < 1e-9
        ),
    }


class SelfCheckIdentities(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.ref = reference.load_reference()
        cls.report = self_check(trials=300, seed=7)

    def test_identities_hold(self) -> None:
        self.assertTrue(self.report["passed"], self.report)
        self.assertLess(self.report["on_path_decomposition_max_error"], 1e-9)
        self.assertLess(self.report["max_negative_exploitability"], 1e-9)
        self.assertLess(self.report["max_negative_one_quitter_exploitability"], 1e-9)
        self.assertLess(self.report["stationary_closed_form_max_error"], 1e-9)
        self.assertGreater(self.report["stationary_closed_form_trials"], 0)

    def test_metrics_match_the_experiment(self) -> None:
        self.assertEqual(self.report, self.ref.self_check(trials=300, seed=7))

    def test_exploitability_non_negative_on_curated_tables(self) -> None:
        from engine import curated
        from engine.model import table_from_wire

        rng = random.Random(31337)
        for entry in curated.curated_tables():
            table = table_from_wire(entry["table"])
            for _ in range(20):
                period = rng.choice((1, 2, 3, 5, 8))
                hazards = reference.random_hazards(rng, period, rng.random() < 0.5)
                self.assertGreaterEqual(
                    evaluator.periodic_exploitability(table, hazards), -1e-12
                )

    def test_never_quitting_profile_values_are_zero(self) -> None:
        # With all hazards zero nothing is ever absorbed, so on-path values
        # are the never-absorbed payoff of zero, and the best deviation is to
        # quit alone: on the seed table every solo-self payoff is 1.
        table = self.ref.seed_table()
        detail = evaluator.evaluate(table, [[0.0] * 4] * 3)
        self.assertEqual(detail["on_path"], [0.0] * 4)
        self.assertEqual(detail["exploitability"], 1.0)
        for entry in detail["best_deviations"]:
            self.assertEqual(entry["value"], 1.0)
            self.assertTrue(any(entry["policy"]))


if __name__ == "__main__":
    unittest.main()
