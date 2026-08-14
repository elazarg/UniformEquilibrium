"""E05: exact 2x2 equilibrium-arc orientation toy model.

This does not compute the Kohlberg--Mertens index of a stochastic game.  It
checks the premise behind the proposed arc-improvement route: one analytic game
family can have several equilibrium arcs with different limiting supports, and
an interior arc has a computable local orientation proxy (the determinant of
the two indifference equations).
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Sequence

Matrix = Sequence[Sequence[Fraction]]


def pure_nash(a: Matrix, b: Matrix) -> list[tuple[int, int]]:
    equilibria = []
    for row in range(2):
        for col in range(2):
            row_best = a[row][col] >= a[1 - row][col]
            col_best = b[row][col] >= b[row][1 - col]
            if row_best and col_best:
                equilibria.append((row, col))
    return equilibria


def completely_mixed_equilibrium(a: Matrix, b: Matrix):
    d1 = a[0][0] - a[0][1] - a[1][0] + a[1][1]
    d2 = b[0][0] - b[0][1] - b[1][0] + b[1][1]
    if d1 == 0 or d2 == 0:
        return None
    q = (a[1][1] - a[0][1]) / d1  # probability of column 0
    p = (b[1][1] - b[1][0]) / d2  # probability of row 0
    if not (0 < p < 1 and 0 < q < 1):
        return None
    orientation_determinant = -d1 * d2
    return {
        "row0_probability": p,
        "column0_probability": q,
        "indifference_orientation_determinant": orientation_determinant,
    }


def coordination_family(t: Fraction) -> tuple[Matrix, Matrix]:
    # Both players receive 1 at (0,0), t at (1,1), and 0 off diagonal.
    matrix = [[Fraction(1), Fraction(0)], [Fraction(0), t]]
    return matrix, matrix


def run() -> dict:
    samples = []
    probabilities = []
    for denominator in [1, 2, 4, 8, 16, 64, 256]:
        t = Fraction(1, denominator)
        a, b = coordination_family(t)
        pure = pure_nash(a, b)
        mixed = completely_mixed_equilibrium(a, b)
        assert pure == [(0, 0), (1, 1)]
        assert mixed is not None
        expected = t / (1 + t)
        assert mixed["row0_probability"] == expected
        assert mixed["column0_probability"] == expected
        probabilities.append(expected)
        samples.append(
            {
                "t": str(t),
                "pure_arcs": pure,
                "mixed_arc": {key: str(value) for key, value in mixed.items()},
            }
        )

    assert all(probabilities[i + 1] < probabilities[i] for i in range(len(probabilities) - 1))
    assert probabilities[-1] < Fraction(1, 100)

    # At every t>0 there are three stationary equilibrium arcs.  Their endpoint
    # support behavior differs: two stay pure; the mixed arc is full-support for
    # each t>0 but collapses to action 1 as t -> 0.
    return {
        "experiment": "E05",
        "status": "passed",
        "samples": samples,
        "limiting_supports": {
            "pure_arc_00": [[0], [0]],
            "pure_arc_11": [[1], [1]],
            "mixed_arc_for_positive_t": [[0, 1], [0, 1]],
            "mixed_arc_limit": [[1], [1]],
        },
        "conclusion": (
            "Endpoint support data are arc-dependent even in a rational analytic "
            "one-state family; selecting an arc can change the leaf-facing support "
            "without changing the game family."
        ),
        "limitation": (
            "The determinant reported is only the local orientation of the 2x2 "
            "indifference map, not a proof that an index-selected arc closes an atlas leaf."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
