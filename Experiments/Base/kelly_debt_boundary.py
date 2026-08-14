"""E07: Kelly/e-process information growth versus punishment debt.

For Bernoulli(1/2+p) observations tested against Bernoulli(1/2), the
log-optimal test martingale is the likelihood ratio.  Its expected logarithmic
growth under the alternative is the KL divergence, which is 2 p^2 + O(p^4).
The experiment compares this evidence budget with debts of order p^q.
"""

from __future__ import annotations

import json
import math


def bernoulli_kl(q: float, p: float) -> float:
    return q * math.log(q / p) + (1.0 - q) * math.log((1.0 - q) / (1.0 - p))


def expected_likelihood_ratio_under_null(horizon: int, alternative: float) -> float:
    """Binomial expansion of E_null[dQ/dP] for a fixed horizon."""
    null = 0.5
    total = 0.0
    for heads in range(horizon + 1):
        null_path_mass = math.comb(horizon, heads) * null**horizon
        likelihood_ratio = (alternative / null) ** heads * (
            (1.0 - alternative) / (1.0 - null)
        ) ** (horizon - heads)
        total += null_path_mass * likelihood_ratio
    return total


def run() -> dict:
    rows = []
    linear_ratios = []
    quadratic_ratios = []
    for p in [0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.001]:
        divergence = bernoulli_kl(0.5 + p, 0.5)
        linear_ratio = divergence / p
        quadratic_ratio = divergence / (p * p)
        linear_ratios.append(linear_ratio)
        quadratic_ratios.append(quadratic_ratio)
        rows.append(
            {
                "signal_bias": p,
                "kl_information_per_stage": divergence,
                "information_over_linear_debt": linear_ratio,
                "information_over_quadratic_debt": quadratic_ratio,
                "information_over_cubic_debt": divergence / p**3,
            }
        )

    assert all(linear_ratios[i + 1] < linear_ratios[i] for i in range(len(linear_ratios) - 1))
    assert abs(quadratic_ratios[-1] - 2.0) < 1e-4
    assert linear_ratios[-1] < 0.003

    martingale_checks = []
    for horizon in [1, 2, 5, 10, 25]:
        expectation = expected_likelihood_ratio_under_null(horizon, 0.57)
        assert abs(expectation - 1.0) < 1e-10
        martingale_checks.append([horizon, expectation])

    return {
        "experiment": "E07",
        "status": "passed",
        "rows": rows,
        "null_expectation_checks": martingale_checks,
        "asymptotic_boundary": {
            "debt_order_below_2": "information/debt tends to 0",
            "debt_order_equal_2": "information/debt tends to 2",
            "debt_order_above_2": "information/debt diverges",
        },
        "conclusion": (
            "The log-optimal evidence bankroll grows quadratically in a small "
            "detectable bias.  It cannot finance a uniformly linear credibility "
            "debt without another source of collateral."
        ),
        "limitation": (
            "This is the simple-iid information frontier; adaptive composite "
            "alternatives require conditional KL or a mixture e-process."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
