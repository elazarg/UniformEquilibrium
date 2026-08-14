"""E25: stationary logit selection in Big Match and Sorin's absorbing game.

For each discount lambda and temperature tau, player 2's logit response is an
explicit function of player 1's mixing probability.  The remaining scalar
fixed-point equation is solved by bisection.  The experiment follows three
temperature scales and records the selected payoff targets.

This is a numerical branch probe.  Logit fixed points are not Nash equilibria at
positive temperature, and bisection selects one root if several exist.
"""

from __future__ import annotations

import json
import math


def sigmoid(value: float) -> float:
    if value >= 0:
        exponential = math.exp(-min(value, 750.0))
        return 1.0 / (1.0 + exponential)
    exponential = math.exp(max(value, -750.0))
    return exponential / (1.0 + exponential)


def sorin_values(p_stop: float, q_left: float, lam: float) -> tuple[float, float]:
    denominator = 1.0 - (1.0 - p_stop) * (1.0 - lam)
    value1 = (
        p_stop * (1.0 - q_left) + (1.0 - p_stop) * q_left * lam
    ) / denominator
    value2 = (
        2.0 * p_stop * q_left
        + (1.0 - p_stop) * (1.0 - q_left) * lam
    ) / denominator
    return value1, value2


def sorin_response(p_stop: float, lam: float, temperature: float):
    player2_difference = 2.0 * p_stop - (1.0 - p_stop) * lam
    q_left = sigmoid(player2_difference / temperature)
    value1, value2 = sorin_values(p_stop, q_left, lam)
    top_value = 1.0 - q_left
    bottom_value = q_left * lam + (1.0 - lam) * value1
    player1_response = sigmoid((top_value - bottom_value) / temperature)
    return player1_response, q_left, (value1, value2)


def big_match_value(p_stop: float, q_left: float, lam: float) -> float:
    denominator = 1.0 - (1.0 - p_stop) * (1.0 - lam)
    return ((1.0 - p_stop) * (1.0 - q_left) * lam + p_stop * q_left) / denominator


def big_match_response(p_stop: float, lam: float, temperature: float):
    minimizer_left_utility_difference = (1.0 - p_stop) * lam - p_stop
    q_left = sigmoid(minimizer_left_utility_difference / temperature)
    value = big_match_value(p_stop, q_left, lam)
    continue_value = (1.0 - q_left) * lam + (1.0 - lam) * value
    stop_value = q_left
    player1_response = sigmoid((stop_value - continue_value) / temperature)
    return player1_response, q_left, (value, -value)


def solve(response, lam: float, temperature: float):
    def residual(p_stop: float) -> float:
        return response(p_stop, lam, temperature)[0] - p_stop

    lower = 0.0
    upper = 1.0
    lower_value = residual(lower)
    upper_value = residual(upper)
    assert lower_value >= 0 and upper_value <= 0
    for _ in range(180):
        middle = (lower + upper) / 2.0
        middle_value = residual(middle)
        if middle_value > 0:
            lower = middle
        else:
            upper = middle
    p_stop = (lower + upper) / 2.0
    player1_response, q_left, values = response(p_stop, lam, temperature)
    fixed_point_residual = abs(player1_response - p_stop)
    assert fixed_point_residual < 1e-8
    return {
        "p_stop": p_stop,
        "q_left": q_left,
        "payoff": list(values),
        "fixed_point_residual": fixed_point_residual,
    }


def path(response, exponent: float):
    rows = []
    for lam in [0.1, 0.03, 0.01, 0.003, 0.001, 0.0003]:
        temperature = lam**exponent
        solution = solve(response, lam, temperature)
        rows.append({"lambda": lam, "temperature": temperature, **solution})
    return rows


def run() -> dict:
    exponents = [0.5, 1.0, 2.0]
    big_match = {str(exponent): path(big_match_response, exponent) for exponent in exponents}
    sorin = {str(exponent): path(sorin_response, exponent) for exponent in exponents}

    # Cold selection recovers the known discounted stationary Nash targets.
    sorin_cold = sorin["2.0"][-1]["payoff"]
    assert abs(sorin_cold[0] - 0.5) < 0.01
    assert abs(sorin_cold[1] - 2.0 / 3.0) < 0.02
    big_match_cold = big_match["2.0"][-1]["payoff"][0]
    assert abs(big_match_cold - 0.5) < 0.01
    assert sorin["0.5"][-1]["payoff"][0] < 0.01
    assert big_match["0.5"][-1]["payoff"][0] < 0.01

    return {
        "experiment": "E25",
        "status": "passed",
        "temperature_exponents": exponents,
        "big_match": big_match,
        "sorin": sorin,
        "cold_sorin_target": sorin_cold,
        "conclusion": (
            "Temperature is a genuine arc-selection parameter: cold scaling "
            "recovers the discounted Nash germs, while warmer scalings select "
            "different full-support behaviors and payoff targets.  Warm selection "
            "does not automatically repair target sustainability."
        ),
        "limitation": (
            "The selected positive-temperature profiles are logit fixed points, "
            "not exact equilibria; sustainable-target and unilateral-uniformity "
            "properties require separate proofs."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
