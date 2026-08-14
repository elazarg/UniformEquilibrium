"""E23: adiabatic tracking for a two-state time-inhomogeneous Markov chain."""

from __future__ import annotations

import json
import math


def target(t: int) -> float:
    return 0.5 + 0.2 * math.sin(math.log(t + 10.0))


def run_schedule(gap_exponent: float, horizon: int, checkpoints: set[int]) -> dict:
    probability_one = 0.5
    error_bound = abs(probability_one - target(0))
    samples = []
    maximum_recursion_violation = 0.0
    for t in range(horizon):
        gap = (t + 10.0) ** (-gap_exponent)
        pi_t = target(t)
        pi_next = target(t + 1)
        previous_error = abs(probability_one - pi_t)
        probability_one = gap * pi_t + (1.0 - gap) * probability_one
        actual_error = abs(probability_one - pi_next)
        recursive_bound = (1.0 - gap) * previous_error + abs(pi_next - pi_t)
        maximum_recursion_violation = max(
            maximum_recursion_violation, actual_error - recursive_bound
        )
        error_bound = (1.0 - gap) * error_bound + abs(pi_next - pi_t)
        if t + 1 in checkpoints:
            variation = abs(pi_next - pi_t)
            samples.append(
                {
                    "time": t + 1,
                    "gap": gap,
                    "target": pi_next,
                    "actual": probability_one,
                    "tracking_error": actual_error,
                    "variation_over_gap": variation / gap,
                    "recursive_error_bound": error_bound,
                }
            )
    assert maximum_recursion_violation < 1e-14
    return {
        "gap_exponent": gap_exponent,
        "samples": samples,
        "final_error": samples[-1]["tracking_error"],
        "final_variation_over_gap": samples[-1]["variation_over_gap"],
    }


def run() -> dict:
    horizon = 1_000_000
    checkpoints = {100, 1_000, 10_000, 100_000, horizon}
    adiabatic = run_schedule(0.4, horizon, checkpoints)
    critical = run_schedule(1.0, horizon, checkpoints)

    assert adiabatic["final_variation_over_gap"] < 1e-4
    assert adiabatic["final_error"] < 1e-3
    assert critical["final_variation_over_gap"] > 0.01
    assert critical["final_error"] > 0.02

    return {
        "experiment": "E23",
        "status": "passed",
        "horizon": horizon,
        "adiabatic_schedule": adiabatic,
        "critical_schedule": critical,
        "conclusion": (
            "When target variation is small relative to the spectral gap, the "
            "inhomogeneous chain tracks its instantaneous invariant law; variation "
            "on the same scale as relaxation leaves a persistent phase lag."
        ),
        "limitation": (
            "This is a scalar uncontrolled chain.  Strategic use requires uniform "
            "tracking under every unilateral transition law and through support changes."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
