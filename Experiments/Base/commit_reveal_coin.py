"""E31: exact timing/resource audit for public coin flipping."""

from __future__ import annotations

from fractions import Fraction
from itertools import product
import json


def probability_one_for_strategy(strategy: tuple[int, int]) -> Fraction:
    """Honest first bit is uniform; last mover sees it and uses strategy[b]."""
    successes = sum((honest ^ strategy[honest]) == 1 for honest in (0, 1))
    return Fraction(successes, 2)


def bias(probability_one: Fraction) -> Fraction:
    return abs(probability_one - Fraction(1, 2))


def simultaneous_bias(deviator_bit: int) -> Fraction:
    probability_one = Fraction(sum((honest ^ deviator_bit) == 1 for honest in (0, 1)), 2)
    return bias(probability_one)


def aborting_open_probability(strategy: tuple[str, str], committed_bit: int, default: int) -> Fraction:
    successes = 0
    for honest_opening in (0, 1):
        decision = strategy[honest_opening]
        outcome = honest_opening ^ committed_bit if decision == "reveal" else default
        successes += outcome == 1
    return Fraction(successes, 2)


def run() -> dict[str, object]:
    sequential_strategies = list(product((0, 1), repeat=2))
    sequential_probabilities = [probability_one_for_strategy(strategy) for strategy in sequential_strategies]
    maximum_sequential_bias = max(bias(probability) for probability in sequential_probabilities)
    assert set(sequential_probabilities) == {Fraction(0), Fraction(1, 2), Fraction(1)}
    assert maximum_sequential_bias == Fraction(1, 2)

    simultaneous_biases = [simultaneous_bias(bit) for bit in (0, 1)]
    assert simultaneous_biases == [Fraction(0), Fraction(0)]

    # Ideal commitments with enforced or simultaneous opening reduce to the
    # simultaneous case: the deviator fixes its bit without seeing the honest bit.
    ideal_commit_biases = simultaneous_biases

    abort_strategies = list(product(("reveal", "abort"), repeat=2))
    abort_probabilities = [
        aborting_open_probability(strategy, committed_bit, default=0)
        for committed_bit in (0, 1)
        for strategy in abort_strategies
    ]
    assert Fraction(0) in abort_probabilities
    maximum_abort_bias = max(bias(probability) for probability in abort_probabilities)
    assert maximum_abort_bias == Fraction(1, 2)

    return {
        "experiment": "E31",
        "status": "passed",
        "maximum_bias": {
            "sequential_public_xor": str(maximum_sequential_bias),
            "simultaneous_public_xor": str(max(simultaneous_biases)),
            "ideal_commit_with_enforced_opening": str(max(ideal_commit_biases)),
            "commit_then_sequential_open_with_abort": str(maximum_abort_bias),
        },
        "conclusion": (
            "Simultaneous XOR is exactly robust to either one deviator, whereas a public last mover can fully bias sequential XOR.  Ideal binding and hiding repair timing only if opening is enforced or simultaneous; selective abort restores full bias."
        ),
        "limitation": (
            "Ideal commitments and enforced opening are additional resources.  The experiment does not implement them inside a stochastic game."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
