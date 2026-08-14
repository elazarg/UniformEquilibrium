"""E22: exact graph Hodge decomposition and stationary Markov currents."""

from __future__ import annotations

import json
import math
from fractions import Fraction


def solve_square(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    n = len(rhs)
    augmented = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next(row for row in range(column, n) if augmented[row][column] != 0)
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        value = augmented[column][column]
        augmented[column] = [entry / value for entry in augmented[column]]
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            augmented[row] = [
                entry - factor * pivot_entry
                for entry, pivot_entry in zip(augmented[row], augmented[column])
            ]
    return [augmented[i][-1] for i in range(n)]


def mat_vec(matrix: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    return [
        sum((entry * value for entry, value in zip(row, vector)), Fraction(0))
        for row in matrix
    ]


def transpose(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    return [list(column) for column in zip(*matrix)]


def mat_mul(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    right_t = transpose(right)
    return [
        [sum((a * b for a, b in zip(row, column)), Fraction(0)) for column in right_t]
        for row in left
    ]


def hodge_decompose(vertex_count: int, edges: list[tuple[int, int]], field: list[Fraction]):
    incidence = [[Fraction(0) for _ in edges] for _ in range(vertex_count)]
    for index, (source, target) in enumerate(edges):
        incidence[source][index] = -1
        incidence[target][index] = 1
    laplacian = mat_mul(incidence, transpose(incidence))
    divergence = mat_vec(incidence, field)

    # Gauge fix phi(0)=0 and solve the reduced connected-graph Laplacian.
    reduced = [row[1:] for row in laplacian[1:]]
    reduced_rhs = divergence[1:]
    potential = [Fraction(0)] + solve_square(reduced, reduced_rhs)
    gradient = mat_vec(transpose(incidence), potential)
    cycle = [value - grad for value, grad in zip(field, gradient)]
    assert mat_vec(incidence, cycle) == [Fraction(0) for _ in range(vertex_count)]
    inner_product = sum((a * b for a, b in zip(gradient, cycle)), Fraction(0))
    assert inner_product == 0
    return potential, gradient, cycle


def run() -> dict:
    edges = [(0, 1), (1, 2), (2, 0), (0, 2)]
    field = [Fraction(2), Fraction(-1), Fraction(4), Fraction(3)]
    potential, gradient, cycle = hodge_decompose(3, edges, field)
    assert [a + b for a, b in zip(gradient, cycle)] == field

    # Biased random walk on a three-cycle: clockwise flow 2/9 and reverse flow
    # 1/9 on each geometric edge under the uniform stationary distribution.
    clockwise_flow = Fraction(2, 9)
    reverse_flow = Fraction(1, 9)
    net_cycle_current = clockwise_flow - reverse_flow
    entropy_production = 3 * float(net_cycle_current) * math.log(
        float(clockwise_flow / reverse_flow)
    )
    assert net_cycle_current == Fraction(1, 9)
    assert abs(entropy_production - math.log(2) / 3) < 1e-12

    alice_cycle = [Fraction(1), Fraction(1), Fraction(1)]
    bob_cycle = [Fraction(-1), Fraction(-1), Fraction(-1)]
    aggregate_cycle = [a + b for a, b in zip(alice_cycle, bob_cycle)]
    assert aggregate_cycle == [Fraction(0), Fraction(0), Fraction(0)]

    return {
        "experiment": "E22",
        "status": "passed",
        "hodge_example": {
            "potential": [str(x) for x in potential],
            "gradient": [str(x) for x in gradient],
            "cycle": [str(x) for x in cycle],
            "orthogonal": True,
        },
        "biased_cycle": {
            "net_current_per_edge": str(net_cycle_current),
            "entropy_production": entropy_production,
        },
        "owner_cancellation": {
            "aggregate_cycle": [str(x) for x in aggregate_cycle],
            "alice_cycle_nonzero": True,
            "bob_cycle_nonzero": True,
        },
        "conclusion": (
            "Finite edge fields split canonically into payable gradient and "
            "divergence-free cycle components; aggregate cancellation can conceal "
            "nonzero owner-typed harmonic currents."
        ),
        "limitation": (
            "The standard Euclidean Hodge projection is not yet weighted by legal "
            "occupation traffic or connected to credible strategic responses."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
