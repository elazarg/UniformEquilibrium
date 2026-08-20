"""E19: exact player permutation and distinguished-deviator decompositions."""

from __future__ import annotations

import itertools
import json
from fractions import Fraction

Vector = tuple[Fraction, ...]


def common_and_standard(vector: Vector) -> tuple[Vector, Vector]:
    mean = sum(vector, Fraction(0)) / len(vector)
    common = tuple(mean for _ in vector)
    standard = tuple(value - mean for value in vector)
    return common, standard


def deviator_decomposition(vector: Vector, deviator: int) -> tuple[Vector, Vector, Vector]:
    n = len(vector)
    opponents = [index for index in range(n) if index != deviator]
    opponent_mean = sum((vector[index] for index in opponents), Fraction(0)) / len(opponents)
    deviator_channel = tuple(vector[deviator] if i == deviator else Fraction(0) for i in range(n))
    opponent_average = tuple(Fraction(0) if i == deviator else opponent_mean for i in range(n))
    opponent_standard = tuple(
        Fraction(0) if i == deviator else vector[i] - opponent_mean for i in range(n)
    )
    return deviator_channel, opponent_average, opponent_standard


def add(*vectors: Vector) -> Vector:
    return tuple(sum((vector[i] for vector in vectors), Fraction(0)) for i in range(len(vectors[0])))


def permute(vector: Vector, permutation: tuple[int, ...]) -> Vector:
    return tuple(vector[permutation[i]] for i in range(len(vector)))


def reynolds_average(vector: Vector) -> Vector:
    permutations = list(itertools.permutations(range(len(vector))))
    return tuple(
        sum((permute(vector, permutation)[i] for permutation in permutations), Fraction(0))
        / len(permutations)
        for i in range(len(vector))
    )


def run() -> dict:
    vector: Vector = tuple(Fraction(value) for value in [7, -2, 5, 1, -6])
    common, standard = common_and_standard(vector)
    assert add(common, standard) == vector
    assert sum(standard, Fraction(0)) == 0
    assert reynolds_average(vector) == common

    dev, opp_average, opp_standard = deviator_decomposition(vector, 0)
    assert add(dev, opp_average, opp_standard) == vector
    assert opp_standard[0] == 0
    assert sum(opp_standard[1:], Fraction(0)) == 0

    # Every permutation fixing player zero leaves the first two channels fixed
    # and merely permutes the opponent-standard channel.
    for opponent_permutation in itertools.permutations(range(1, len(vector))):
        permutation = (0,) + opponent_permutation
        assert permute(dev, permutation) == dev
        assert permute(opp_average, permutation) == opp_average
        permuted_standard = permute(opp_standard, permutation)
        assert permuted_standard[0] == 0
        assert sum(permuted_standard[1:], Fraction(0)) == 0

    transfer_obstruction: Vector = (
        Fraction(1), Fraction(-1), Fraction(0), Fraction(0), Fraction(0)
    )
    transfer_common, transfer_standard = common_and_standard(transfer_obstruction)
    assert transfer_common == tuple(Fraction(0) for _ in transfer_obstruction)
    assert transfer_standard == transfer_obstruction

    systemic_obstruction: Vector = tuple(Fraction(3) for _ in range(5))
    systemic_common, systemic_standard = common_and_standard(systemic_obstruction)
    assert systemic_common == systemic_obstruction
    assert systemic_standard == tuple(Fraction(0) for _ in systemic_obstruction)

    return {
        "experiment": "E19",
        "status": "passed",
        "full_permutation_split": {
            "input": [str(x) for x in vector],
            "common": [str(x) for x in common],
            "standard": [str(x) for x in standard],
        },
        "distinguished_deviator_split": {
            "deviator": [str(x) for x in dev],
            "opponents_average": [str(x) for x in opp_average],
            "opponents_standard": [str(x) for x in opp_standard],
        },
        "conclusion": (
            "Player-space obstructions split canonically into systemic welfare, "
            "deviator, opponent-average, and redistribution channels; owner-transfer "
            "obstructions can be invisible in the trivial representation."
        ),
        "limitation": "The decomposition alone does not prove that a redistribution channel is harmless.",
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
