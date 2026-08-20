"""E12: bounded potentials as finite collateral/escrow.

For cash-flow increments c_t, the least initial collateral that keeps every
prefix balance nonnegative is max(0, -min_n sum_{t<n} c_t).  If the cash flow is
the negative increment of a bounded potential, this collateral is at most the
potential's range.  Everything below is checked exhaustively on finite paths.
"""

from __future__ import annotations

import itertools
import json
from fractions import Fraction


def prefix_balances(initial: Fraction, cashflows: tuple[Fraction, ...]) -> list[Fraction]:
    balances = [initial]
    balance = initial
    for cashflow in cashflows:
        balance += cashflow
        balances.append(balance)
    return balances


def minimum_collateral(cashflows: tuple[Fraction, ...]) -> Fraction:
    balances = prefix_balances(Fraction(0), cashflows)
    return max(Fraction(0), -min(balances))


def run() -> dict:
    exhaustive_cashflows = 0
    for raw in itertools.product([-1, 0, 1], repeat=7):
        cashflows = tuple(Fraction(x) for x in raw)
        collateral = minimum_collateral(cashflows)
        assert min(prefix_balances(collateral, cashflows)) >= 0
        if collateral > 0:
            assert min(prefix_balances(collateral - 1, cashflows)) < 0
        exhaustive_cashflows += 1

    potential_values = [-2, -1, 0, 1, 2]
    potential_paths = 0
    worst_collateral = Fraction(0)
    for raw_path in itertools.product(potential_values, repeat=6):
        path = tuple(Fraction(x) for x in raw_path)
        # Cash received is Phi_{t+1}-Phi_t.  Collateral covers a downward move.
        cashflows = tuple(path[t + 1] - path[t] for t in range(len(path) - 1))
        collateral = minimum_collateral(cashflows)
        path_range = max(path) - min(path)
        assert collateral <= path_range <= 4
        worst_collateral = max(worst_collateral, collateral)
        potential_paths += 1

    assert worst_collateral == 4

    example = tuple(Fraction(x) for x in [2, 1, -2, 0, -1])
    example_cashflows = tuple(example[t + 1] - example[t] for t in range(len(example) - 1))
    example_collateral = minimum_collateral(example_cashflows)
    assert example_collateral == 4

    return {
        "experiment": "E12",
        "status": "passed",
        "cashflow_paths_checked": exhaustive_cashflows,
        "bounded_potential_paths_checked": potential_paths,
        "worst_collateral_for_potential_range_4": str(worst_collateral),
        "example": {
            "potential_path": [str(x) for x in example],
            "cashflows": [str(x) for x in example_cashflows],
            "minimum_collateral": str(example_collateral),
        },
        "conclusion": (
            "A bounded pathwise potential yields bounded escrow exactly through "
            "its maximum prefix drawdown; the universal bound is its oscillation."
        ),
        "limitation": (
            "Expected-drift certificates need not give pathwise solvency.  Turning "
            "them into contracts requires probabilistic collateral or default rules."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
