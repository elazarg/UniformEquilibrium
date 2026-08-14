"""E11: exact reduced-Abel/continuous-time resolvent calculation.

For P_lam = I + lam A, normalized geometric discounting gives

  lam [I - (1-lam) P_lam]^{-1} g
    = [I - (1-lam) A]^{-1} g.

The endpoint is (I-A)^{-1}g, also the resolvent of the continuous-time
generator A under an independent rate-one exponential killing time.
"""

from __future__ import annotations

import json
from fractions import Fraction

Vector = tuple[Fraction, Fraction]
Matrix = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]


def mat_vec(matrix: Matrix, vector: Vector) -> Vector:
    return (
        matrix[0][0] * vector[0] + matrix[0][1] * vector[1],
        matrix[1][0] * vector[0] + matrix[1][1] * vector[1],
    )


def inverse_2x2(matrix: Matrix) -> Matrix:
    a, b = matrix[0]
    c, d = matrix[1]
    determinant = a * d - b * c
    assert determinant != 0
    return ((d / determinant, -b / determinant), (-c / determinant, a / determinant))


def identity_minus(scale: Fraction, generator: Matrix) -> Matrix:
    return (
        (1 - scale * generator[0][0], -scale * generator[0][1]),
        (-scale * generator[1][0], 1 - scale * generator[1][1]),
    )


def sub(left: Vector, right: Vector) -> Vector:
    return (left[0] - right[0], left[1] - right[1])


def run() -> dict:
    rate_01 = Fraction(2, 3)
    rate_10 = Fraction(1, 4)
    generator: Matrix = (
        (-rate_01, rate_01),
        (rate_10, -rate_10),
    )
    payoff: Vector = (Fraction(3, 2), Fraction(-2, 5))

    endpoint_operator = inverse_2x2(identity_minus(Fraction(1), generator))
    endpoint = mat_vec(endpoint_operator, payoff)
    # Resolvent equation for exponentially killed continuous-time dynamics.
    assert mat_vec(identity_minus(Fraction(1), generator), endpoint) == payoff

    samples = []
    previous_error = None
    for denominator in [2, 4, 8, 16, 32, 64, 128, 256]:
        lam = Fraction(1, denominator)
        reduced_abel = mat_vec(
            inverse_2x2(identity_minus(1 - lam, generator)), payoff
        )
        error = sub(reduced_abel, endpoint)
        error_norm = abs(error[0]) + abs(error[1])
        if previous_error is not None:
            assert error_norm < previous_error
        previous_error = error_norm
        samples.append(
            {
                "lambda": str(lam),
                "reduced_abel_value": [str(x) for x in reduced_abel],
                "l1_error_to_continuous_resolvent": str(error_norm),
            }
        )

    return {
        "experiment": "E11",
        "status": "passed",
        "generator": [[str(x) for x in row] for row in generator],
        "continuous_time_rate_one_resolvent": [str(x) for x in endpoint],
        "samples": samples,
        "conclusion": (
            "The reduced Abel endpoint is exactly a continuous-time resolvent "
            "for first-order transition germs, supporting a generator-level reformulation."
        ),
        "limitation": (
            "Resolvent equivalence transports occupation values, not equilibrium "
            "selection, deviation credibility, or a uniform strategy."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
