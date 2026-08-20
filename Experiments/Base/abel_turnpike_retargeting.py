"""E16: Abel boundary layer versus Cesaro turnpike target.

A live state absorbs with hazard c*lambda.  Its pre-absorption reward is r_live
and its absorbing reward is r_abs.  Discounting at lambda retains a positive
boundary-layer mass at the live state as lambda -> 0.  For every fixed positive
lambda, however, the long Cesaro occupation of the live state vanishes.
"""

from __future__ import annotations

import json
from fractions import Fraction


def abel_live_mass(lam: Fraction, coefficient: Fraction) -> Fraction:
    hazard = coefficient * lam
    return lam / (1 - (1 - lam) * (1 - hazard))


def expected_cesaro_live_mass(
    horizon: int, lam: Fraction, coefficient: Fraction
) -> Fraction:
    hazard = coefficient * lam
    if hazard == 0:
        return Fraction(1)
    survival_sum = (1 - (1 - hazard) ** horizon) / hazard
    return survival_sum / horizon


def run() -> dict:
    coefficient = Fraction(1, 2)
    live_reward = Fraction(1, 3)
    absorbing_reward = Fraction(5, 4)
    limiting_live_mass = 1 / (1 + coefficient)
    abel_endpoint = (
        limiting_live_mass * live_reward
        + (1 - limiting_live_mass) * absorbing_reward
    )
    sustainable_cesaro_target = absorbing_reward
    assert abel_endpoint != sustainable_cesaro_target

    samples = []
    for denominator in [10, 100, 1_000, 10_000]:
        lam = Fraction(1, denominator)
        live_mass = abel_live_mass(lam, coefficient)
        value = live_mass * live_reward + (1 - live_mass) * absorbing_reward
        samples.append(
            {
                "lambda": str(lam),
                "abel_live_mass": str(live_mass),
                "abel_value": str(value),
            }
        )
    final_live_mass = abel_live_mass(Fraction(1, 10_000), coefficient)
    assert abs(final_live_mass - limiting_live_mass) < Fraction(1, 10_000)

    fixed_lam = Fraction(1, 100)
    cesaro_samples = []
    previous = None
    for horizon in [100, 1_000, 10_000, 100_000]:
        mass = expected_cesaro_live_mass(horizon, fixed_lam, coefficient)
        if previous is not None:
            assert mass < previous
        previous = mass
        cesaro_samples.append([horizon, float(mass)])

    # Moving lambda with the horizon preserves a nonzero live fraction and is
    # therefore not a single uniform policy.
    moving_samples = []
    for horizon in [100, 1_000, 10_000]:
        lam = Fraction(1, horizon)
        mass = expected_cesaro_live_mass(horizon, lam, coefficient)
        moving_samples.append([horizon, float(mass)])
        assert mass > Fraction(3, 4)

    return {
        "experiment": "E16",
        "status": "passed",
        "abel_endpoint": str(abel_endpoint),
        "sustainable_fixed_policy_cesaro_target": str(sustainable_cesaro_target),
        "abel_samples": samples,
        "fixed_policy_cesaro_live_mass": cesaro_samples,
        "horizon_tuned_policy_live_mass": moving_samples,
        "conclusion": (
            "The discounted endpoint contains a persistent boundary-layer mixture, "
            "whereas every fixed positive-hazard policy has the absorbing reward as "
            "its Cesaro turnpike target.  Retargeting is mathematically mandatory."
        ),
        "limitation": "This is a Markov reward process, not an incentive-compatible game.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
