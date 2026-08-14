"""E02: nonhomogeneous finite-chain hazard scheduling.

For a schedule alpha_t -> 0, an event with one-step hazard comparable to
alpha_t**k occurs eventually with probability one exactly when the cumulative
hazard diverges (under the independent one-step model).  A harmful event is
avoided with positive probability only when its cumulative hazard converges.

The script checks the resulting exponent separation for power schedules and
records two structural no-go phenomena: a nonvanishing irreversible leak, and
the strict logarithmic incompatibility -log(1-2x) > -2 log(1-x).
"""

from __future__ import annotations

import json
import math


def power_schedule(t: int, exponent: float, offset: int = 10) -> float:
    return (t + offset) ** (-exponent)


def cumulative_hazard(
    horizon: int, schedule_exponent: float, hazard_order: int, coefficient: float = 1.0
) -> float:
    return sum(
        coefficient * power_schedule(t, schedule_exponent) ** hazard_order
        for t in range(1, horizon + 1)
    )


def log_survival(
    horizon: int, schedule_exponent: float, hazard_order: int, coefficient: float = 1.0
) -> float:
    total = 0.0
    for t in range(1, horizon + 1):
        hazard = coefficient * power_schedule(t, schedule_exponent) ** hazard_order
        assert 0.0 <= hazard < 1.0
        total += math.log1p(-hazard)
    return total


def asymptotic_class(schedule_exponent: float, hazard_order: int) -> str:
    product = schedule_exponent * hazard_order
    if product < 1.0 - 1e-12:
        return "diverges-polynomially"
    if abs(product - 1.0) <= 1e-12:
        return "diverges-logarithmically"
    return "converges"


def separation_interval(good_order: int, bad_order: int) -> tuple[float, float] | None:
    """Power exponents a with sum alpha^good divergent, alpha^bad convergent."""
    lower = 1.0 / bad_order
    upper = 1.0 / good_order
    return (lower, upper) if lower < upper else None


def run() -> dict:
    horizon = 200_000
    exponent_rows = []
    for good_order, bad_order in [(1, 2), (2, 3), (2, 2), (3, 2)]:
        interval = separation_interval(good_order, bad_order)
        if interval is None:
            exponent_rows.append(
                {
                    "good_order": good_order,
                    "bad_order": bad_order,
                    "separating_power_schedule": None,
                }
            )
            continue
        exponent = (interval[0] + interval[1]) / 2.0
        good_class = asymptotic_class(exponent, good_order)
        bad_class = asymptotic_class(exponent, bad_order)
        assert good_class.startswith("diverges") and bad_class == "converges"
        exponent_rows.append(
            {
                "good_order": good_order,
                "bad_order": bad_order,
                "separating_power_schedule": exponent,
                "good_class": good_class,
                "bad_class": bad_class,
                "finite_horizon_good_hazard": cumulative_hazard(
                    horizon, exponent, good_order
                ),
                "finite_horizon_bad_hazard": cumulative_hazard(
                    horizon, exponent, bad_order
                ),
            }
        )

    # A leak bounded below by epsilon cannot be scheduled away: survival is at
    # most (1-epsilon)^T.
    leak = 0.002
    leak_survival = (1.0 - leak) ** 10_000
    assert leak_survival < 1e-8

    log_hazard_gaps = []
    for x in [1e-4, 1e-3, 1e-2, 0.1, 0.24, 0.49]:
        gap = -math.log1p(-2 * x) + 2 * math.log1p(-x)
        assert gap > 0
        log_hazard_gaps.append([x, gap])

    # Numerical survival sanity check: a=3/4 separates first-order access from
    # second-order damage.
    a = 0.75
    good_log_survival = log_survival(horizon, a, 1, coefficient=0.2)
    bad_log_survival = log_survival(horizon, a, 2, coefficient=0.2)
    assert good_log_survival < -5.0
    assert bad_log_survival > -1.0

    return {
        "experiment": "E02",
        "status": "passed",
        "horizon": horizon,
        "power_schedule_classification": exponent_rows,
        "first_vs_second_order_example": {
            "schedule_exponent": a,
            "good_event_probability": 1.0 - math.exp(good_log_survival),
            "bad_event_probability": 1.0 - math.exp(bad_log_survival),
        },
        "nonvanishing_leak_survival_after_10000": leak_survival,
        "strict_log_hazard_gaps": log_hazard_gaps,
        "conclusion": (
            "A scalar vanishing schedule separates useful and harmful hazards "
            "only when the harmful hazard has strictly higher asymptotic order."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
