"""E14: approximate predictive-state compression under contraction.

A two-state mixing prediction map is affine with contraction coefficient rho.
Nearest-grid filtering therefore obeys e_{t+1} <= rho e_t + mesh/2 and has a
uniform error bound using only finitely many public memory states.  A separate
Bayes update shows why rare observations require an additional likelihood or
filter-stability hypothesis.
"""

from __future__ import annotations

import json
from fractions import Fraction


def nearest_grid(value: Fraction, denominator: int) -> Fraction:
    scaled_numerator = value.numerator * denominator
    scaled_denominator = value.denominator
    index = (2 * scaled_numerator + scaled_denominator) // (2 * scaled_denominator)
    index = min(denominator, max(0, index))
    return Fraction(index, denominator)


def prediction(value: Fraction, enter_one: Fraction, leave_one: Fraction) -> Fraction:
    return enter_one + (1 - enter_one - leave_one) * value


def bayes_positive(prior_one: Fraction, likelihood_one: Fraction, likelihood_zero: Fraction) -> Fraction:
    mass = prior_one * likelihood_one + (1 - prior_one) * likelihood_zero
    assert mass > 0
    return prior_one * likelihood_one / mass


def run() -> dict:
    enter_one = Fraction(1, 5)
    leave_one = Fraction(1, 4)
    rho = 1 - enter_one - leave_one
    assert rho == Fraction(11, 20)

    grid_denominator = 32
    mesh = Fraction(1, grid_denominator)
    theoretical_bound = mesh / (2 * (1 - rho))
    horizon = 500
    worst_error = Fraction(0)
    worst_average_error = Fraction(0)

    for initial_index in range(257):
        exact = Fraction(initial_index, 256)
        approximate = nearest_grid(exact, grid_denominator)
        cumulative_error = Fraction(0)
        for _ in range(horizon):
            exact = prediction(exact, enter_one, leave_one)
            approximate = nearest_grid(
                prediction(approximate, enter_one, leave_one), grid_denominator
            )
            error = abs(exact - approximate)
            cumulative_error += error
            worst_error = max(worst_error, error)
        worst_average_error = max(worst_average_error, cumulative_error / horizon)

    # Include the initial quantization error in the usual invariant estimate.
    assert worst_error <= theoretical_bound
    assert worst_average_error <= theoretical_bound

    # Rare-observation fence: a tiny prior discrepancy can be amplified by
    # nearly the reciprocal of the rare-event likelihood.
    prior_a = Fraction(0)
    prior_b = Fraction(1, 1_000_000)
    rare_likelihood_under_zero = Fraction(1, 1_000)
    posterior_a = bayes_positive(prior_a, Fraction(1), rare_likelihood_under_zero)
    posterior_b = bayes_positive(prior_b, Fraction(1), rare_likelihood_under_zero)
    amplification = abs(posterior_b - posterior_a) / abs(prior_b - prior_a)
    assert amplification > 900

    return {
        "experiment": "E14",
        "status": "passed",
        "contracting_filter": {
            "contraction": str(rho),
            "memory_states": grid_denominator + 1,
            "horizon_checked": horizon,
            "initial_beliefs_checked": 257,
            "theoretical_uniform_error_bound": str(theoretical_bound),
            "worst_observed_error": float(worst_error),
            "worst_observed_average_error": float(worst_average_error),
        },
        "rare_observation_fence": {
            "input_belief_gap": str(prior_b - prior_a),
            "output_belief_gap": str(posterior_b - posterior_a),
            "amplification": str(amplification),
        },
        "conclusion": (
            "Contractive prediction admits a finite epsilon-predictive quotient "
            "with horizon-independent error, but Bayes conditioning on rare "
            "signals can destroy contraction by an arbitrarily large factor."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
