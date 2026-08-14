"""E26: nonequilibrium current, entropy production, and debt scaling."""

from __future__ import annotations

import json
import math


def entropy_production(delta: float) -> float:
    clockwise = 0.5 + delta
    reverse = 0.5 - delta
    return (clockwise - reverse) * math.log(clockwise / reverse)


def bernoulli_kl_from_fair(delta: float) -> float:
    clockwise = 0.5 + delta
    reverse = 0.5 - delta
    return clockwise * math.log(2.0 * clockwise) + reverse * math.log(2.0 * reverse)


def pressure(theta: float) -> float:
    # Fair clockwise/counterclockwise tilted transfer operator has row sum cosh(theta).
    return math.log(math.cosh(theta))


def run() -> dict:
    rows = []
    entropy_over_damage = []
    kl_over_damage = []
    for delta in [0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.001]:
        current_score = 2.0 * delta
        production = entropy_production(delta)
        information = bernoulli_kl_from_fair(delta)
        entropy_over_damage.append(production / current_score)
        kl_over_damage.append(information / current_score)
        theta = 0.5 * math.log((0.5 + delta) / (0.5 - delta))
        assert abs(math.tanh(theta) - current_score) < 1e-12
        assert abs((theta * math.tanh(theta) - pressure(theta)) - information) < 1e-12
        rows.append(
            {
                "delta": delta,
                "mean_oriented_current_score": current_score,
                "stationary_current_per_edge_on_three_cycle": current_score / 3.0,
                "entropy_production": production,
                "kl_rate_from_fair_chain": information,
                "tilt_theta": theta,
                "pressure": pressure(theta),
                "entropy_over_linear_damage": production / current_score,
                "kl_over_linear_damage": information / current_score,
            }
        )

    assert entropy_over_damage[-1] < 0.01
    assert kl_over_damage[-1] < 0.01

    # Pressure derivatives at zero: first derivative zero, second derivative one.
    step = 1e-5
    first_derivative = (pressure(step) - pressure(-step)) / (2.0 * step)
    second_derivative = (pressure(step) - 2.0 * pressure(0.0) + pressure(-step)) / step**2
    assert abs(first_derivative) < 1e-10
    assert abs(second_derivative - 1.0) < 1e-5

    return {
        "experiment": "E26",
        "status": "passed",
        "rows": rows,
        "pressure_derivatives_at_equilibrium": {
            "first": first_derivative,
            "second": second_derivative,
        },
        "conclusion": (
            "Near detailed balance, oriented payoff/current damage is linear in "
            "the bias while entropy production and KL information are quadratic. "
            "Thermodynamic evidence cannot by itself finance linear debt."
        ),
        "limitation": (
            "Branches whose payoff damage is quadratic or complementary may still "
            "admit an entropy-payment inequality; this experiment only rules out a universal linear one."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
