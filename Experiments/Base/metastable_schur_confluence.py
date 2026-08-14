"""E24: exact confluence of finite effective-generator elimination.

Fast-state elimination for a continuous-time generator is a Schur complement.
When the eliminated blocks are invertible, joint elimination and either
sequential order give exactly the same reduced generator and effective reward.
"""

from __future__ import annotations

import json
from fractions import Fraction

Matrix = list[list[Fraction]]
Vector = list[Fraction]


def matrix(rows) -> Matrix:
    return [[Fraction(value) for value in row] for row in rows]


def inverse(value: Matrix) -> Matrix:
    n = len(value)
    augmented = [
        list(row) + [Fraction(int(i == j)) for j in range(n)]
        for i, row in enumerate(value)
    ]
    for column in range(n):
        pivot = next(row for row in range(column, n) if augmented[row][column] != 0)
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        pivot_value = augmented[column][column]
        augmented[column] = [entry / pivot_value for entry in augmented[column]]
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            augmented[row] = [
                entry - factor * pivot_entry
                for entry, pivot_entry in zip(augmented[row], augmented[column])
            ]
    return [row[n:] for row in augmented]


def transpose(value: Matrix) -> Matrix:
    return [list(column) for column in zip(*value)]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    right_t = transpose(right)
    return [
        [sum((a * b for a, b in zip(row, column)), Fraction(0)) for column in right_t]
        for row in left
    ]


def mat_vec(left: Matrix, right: Vector) -> Vector:
    return [sum((a * b for a, b in zip(row, right)), Fraction(0)) for row in left]


def subtract(left: Matrix, right: Matrix) -> Matrix:
    return [[a - b for a, b in zip(row_a, row_b)] for row_a, row_b in zip(left, right)]


def subvector(left: Vector, right: Vector) -> Vector:
    return [a - b for a, b in zip(left, right)]


def block(value: Matrix, rows: list[int], columns: list[int]) -> Matrix:
    return [[value[i][j] for j in columns] for i in rows]


def eliminate(
    labels: list[int], generator: Matrix, reward: Vector, eliminated_labels: set[int]
):
    eliminated = [i for i, label in enumerate(labels) if label in eliminated_labels]
    kept = [i for i, label in enumerate(labels) if label not in eliminated_labels]
    assert eliminated and kept
    a = block(generator, kept, kept)
    b = block(generator, kept, eliminated)
    c = block(generator, eliminated, kept)
    d_inv = inverse(block(generator, eliminated, eliminated))
    effective_generator = subtract(a, multiply(multiply(b, d_inv), c))
    effective_reward = subvector(
        [reward[i] for i in kept],
        mat_vec(multiply(b, d_inv), [reward[i] for i in eliminated]),
    )
    return [labels[i] for i in kept], effective_generator, effective_reward


def encode_matrix(value: Matrix):
    return [[str(entry) for entry in row] for row in value]


def run() -> dict:
    labels = [0, 1, 2, 3]
    generator = matrix(
        [
            [-3, 2, 0, 1],
            [3, -7, 4, 0],
            [0, 5, -11, 6],
            [2, 0, 1, -3],
        ]
    )
    reward = [Fraction(value) for value in [1, -2, 3, 4]]
    assert all(sum(row, Fraction(0)) == 0 for row in generator)

    joint = eliminate(labels, generator, reward, {1, 2})
    after_one = eliminate(labels, generator, reward, {1})
    sequential_12 = eliminate(*after_one, {2})
    after_two = eliminate(labels, generator, reward, {2})
    sequential_21 = eliminate(*after_two, {1})

    assert joint == sequential_12 == sequential_21
    reduced_labels, reduced_generator, reduced_reward = joint
    assert reduced_labels == [0, 3]
    assert all(sum(row, Fraction(0)) == 0 for row in reduced_generator)
    assert reduced_generator[0][1] > 0 and reduced_generator[1][0] > 0

    return {
        "experiment": "E24",
        "status": "passed",
        "original_generator": encode_matrix(generator),
        "eliminated_states": [1, 2],
        "reduced_labels": reduced_labels,
        "effective_generator": encode_matrix(reduced_generator),
        "effective_reward": [str(value) for value in reduced_reward],
        "orders_checked": ["joint", "1_then_2", "2_then_1"],
        "conclusion": (
            "Schur-complement reduction is exactly confluent for both generator "
            "and Poisson reward data in this finite fast-state model."
        ),
        "limitation": (
            "Controlled action choices, singular recurrent blocks, public observations, "
            "and strategic target inequalities are not covered by linear confluence."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
