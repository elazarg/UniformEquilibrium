"""E27: common reversible Dirichlet geometry for two finite kernels."""

from __future__ import annotations

import itertools
import json
from fractions import Fraction

Matrix = list[list[Fraction]]
Vector = list[Fraction]


def apply(kernel: Matrix, vector: Vector) -> Vector:
    return [
        sum((probability * value for probability, value in zip(row, vector)), Fraction(0))
        for row in kernel
    ]


def inner(left: Vector, right: Vector) -> Fraction:
    return sum((a * b for a, b in zip(left, right)), Fraction(0)) / len(left)


def centered(vector: Vector) -> Vector:
    mean = sum(vector, Fraction(0)) / len(vector)
    return [value - mean for value in vector]


def variance(vector: Vector) -> Fraction:
    value = centered(vector)
    return inner(value, value)


def dirichlet(kernel: Matrix, vector: Vector) -> Fraction:
    n = len(vector)
    return sum(
        (
            Fraction(1, 2 * n)
            * kernel[i][j]
            * (vector[j] - vector[i]) ** 2
            for i in range(n)
            for j in range(n)
        ),
        Fraction(0),
    )


def verify_reversible(kernel: Matrix) -> None:
    n = len(kernel)
    assert all(sum(row, Fraction(0)) == 1 for row in kernel)
    assert all(kernel[i][j] == kernel[j][i] for i in range(n) for j in range(n))


def run() -> dict:
    cycle_kernel: Matrix = [
        [Fraction(1, 2) if i == j else Fraction(1, 4) if (i - j) % 4 in {1, 3} else Fraction(0)
         for j in range(4)]
        for i in range(4)
    ]
    complete_kernel: Matrix = [
        [Fraction(3, 4) if i == j else Fraction(1, 12) for j in range(4)]
        for i in range(4)
    ]
    verify_reversible(cycle_kernel)
    verify_reversible(complete_kernel)

    gaps = [(cycle_kernel, Fraction(1, 2)), (complete_kernel, Fraction(1, 3))]
    functions_checked = 0
    for raw in itertools.product(range(-2, 3), repeat=4):
        vector = [Fraction(value) for value in raw]
        for kernel, gap in gaps:
            image = apply(kernel, vector)
            poisson_energy = inner(vector, [a - b for a, b in zip(vector, image)])
            energy = dirichlet(kernel, vector)
            assert energy == poisson_energy
            assert energy >= gap * variance(vector)
        functions_checked += 1

    # Arbitrary switching between the two kernels contracts every mean-zero
    # mode in the common uniform L2 geometry by at most 2/3 per step.
    vector = [Fraction(3), Fraction(-1), Fraction(2), Fraction(-4)]
    assert sum(vector, Fraction(0)) == 0
    initial_norm_sq = inner(vector, vector)
    contraction = Fraction(2, 3)
    schedule = [cycle_kernel, complete_kernel, complete_kernel, cycle_kernel] * 8
    norm_samples = []
    for time, kernel in enumerate(schedule, start=1):
        vector = apply(kernel, vector)
        norm_sq = inner(vector, vector)
        assert norm_sq <= contraction ** (2 * time) * initial_norm_sq
        norm_samples.append(float(norm_sq))

    return {
        "experiment": "E27",
        "status": "passed",
        "functions_checked": functions_checked,
        "shared_invariant_law": ["1/4", "1/4", "1/4", "1/4"],
        "spectral_gaps": {"lazy_cycle": "1/2", "lazy_complete": "1/3"},
        "switching_norm_squared_samples": norm_samples,
        "conclusion": (
            "Two distinct controlled kernels share an exact Dirichlet identity, "
            "a common coercive variance bound, and uniform L2 contraction under "
            "arbitrary switching.  Shared reversibility supplies a genuine common energy geometry."
        ),
        "limitation": (
            "General stochastic-game kernels need not share an invariant law, be "
            "reversible, or preserve the same action support under deviations."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
