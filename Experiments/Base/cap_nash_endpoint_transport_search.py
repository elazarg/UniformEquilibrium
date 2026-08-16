"""Exact-rational regression checks for cap--Nash endpoint transport.

This does not search for a positive-global-debt quitting game (that would be a
counterexample to the target conjecture).  It checks the finite algebra used
by the proposed argument and exhibits a rational local game which saturates
every estimate except the global-infimum premise.
"""

import json
from fractions import Fraction as Q


def check_scalar_grid() -> int:
    checked = 0
    grid = [Q(k, 12) for k in range(1, 13)]
    for d_star in grid:
        for debt in grid:
            if debt < d_star:
                continue
            for survival in grid:
                if survival * debt < d_star:
                    continue
                for deleted_survival in grid:
                    if deleted_survival < survival:
                        continue
                    for loss in grid:
                        for average_loss in grid:
                            if average_loss > loss:
                                continue
                            gap = average_loss * (1 - deleted_survival) / deleted_survival
                            bound = loss * (debt - d_star) / d_star
                            assert gap <= bound
                            checked += 1
    return checked


def check_local_sharp_example() -> None:
    # Players 0 and 1.  Player 0 Continues surely; player 1 Continues with 1/2.
    # Player-0 rewards are r({0})=1, r({1})=0, r({0,1})=-1, and b_0=0.
    c = a0 = Q(1, 2)
    solo = Q(1)
    opponent_only = Q(0)
    collision = Q(-1)
    cap0 = Q(0)
    quit0 = a0 * solo + (1 - a0) * collision
    continue0 = a0 * cap0 + (1 - a0) * opponent_only
    assert quit0 == continue0 == 0
    joining_loss = opponent_only - collision
    gap = solo - cap0
    assert gap == joining_loss * (1 - a0) / a0

    # The suffix "both Quit" has u_0=-1, b_0=0 and total debt D=1.
    # Prefixing by this Nash row gives debt cD=1/2, so choosing the *formal*
    # lower bound D_*=1/2 saturates the transport estimate.
    debt = Q(1)
    formal_lower = Q(1, 2)
    assert c * debt == formal_lower
    assert gap == joining_loss * (debt - formal_lower) / formal_lower

    # This is only a local sharpness witness: the actual two-player game's
    # global debt infimum is zero (Quit alone is already debt-free).


def check_excess_budget_grid() -> int:
    checked = 0
    grid = [Q(k, 10) for k in range(0, 11)]
    for debt in grid[1:]:
        for collision_mass in grid:
            for singleton_mass in grid:
                if collision_mass + singleton_mass > 1:
                    continue
                survival = 1 - collision_mass - singleton_mass
                for shift in grid:
                    if shift > debt:
                        continue
                    prefixed_upper = survival * debt + singleton_mass * shift
                    for minimum in grid:
                        if minimum > prefixed_upper:
                            continue
                        charged = debt * collision_mass + singleton_mass * (debt - shift)
                        assert charged <= debt - minimum
                        checked += 1
    return checked


def run() -> dict[str, object]:
    check_local_sharp_example()
    scalar_cases = check_scalar_grid()
    budget_cases = check_excess_budget_grid()
    return {
        "experiment": "E34",
        "status": "passed",
        "scalar_cases": scalar_cases,
        "excess_budget_cases": budget_cases,
        "conclusion": (
            "The cap--Nash endpoint inequalities and auxiliary excess-budget "
            "bound pass exact rational grids; a two-player local witness "
            "saturates the transport estimate."
        ),
        "limitation": (
            "The witness is local only: the same game has a zero-debt carrier, "
            "so this does not establish a positive global minimum or a "
            "uniform-equilibrium construction."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
