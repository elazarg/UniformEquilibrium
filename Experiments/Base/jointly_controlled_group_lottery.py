"""E01: exact finite-group jointly controlled lottery experiment.

The algebraic claim is elementary but strategically important.  If U is
uniform on a finite group G, then X + U is uniform for every independently
chosen law of X.  Thus two different players can contribute group elements;
under a unilateral deviation, the honest player's uniform action protects the
public signal.  The experiment also exhibits why equality of the signal law
does not protect a transition that depends on the raw action pair.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Callable, Dict

Distribution = Dict[int, Fraction]


def uniform(n: int) -> Distribution:
    return {x: Fraction(1, n) for x in range(n)}


def normalize(weights: list[int]) -> Distribution:
    total = sum(weights)
    assert total > 0
    return {i: Fraction(w, total) for i, w in enumerate(weights) if w}


def convolution_mod(left: Distribution, right: Distribution, n: int) -> Distribution:
    out = {z: Fraction(0) for z in range(n)}
    for x, px in left.items():
        for y, py in right.items():
            out[(x + y) % n] += px * py
    return out


def pushforward(law: Distribution, f: Callable[[int], int]) -> Distribution:
    out: Distribution = {}
    for x, p in law.items():
        out[f(x)] = out.get(f(x), Fraction(0)) + p
    return out


def encoded_rational_lottery(weights: list[int]) -> Distribution:
    """Map a uniform cyclic-group signal to weights/total exactly."""
    total = sum(weights)
    signal = uniform(total)
    cutoffs: list[int] = []
    running = 0
    for w in weights:
        running += w
        cutoffs.append(running)

    def outcome(z: int) -> int:
        return next(i for i, cutoff in enumerate(cutoffs) if z < cutoff)

    return pushforward(signal, outcome)


def hidden_transition_probability(
    left: Distribution, right: Distribution, predicate: Callable[[int, int], bool]
) -> Fraction:
    return sum(
        (px * py for x, px in left.items() for y, py in right.items() if predicate(x, y)),
        Fraction(0),
    )


def run() -> dict:
    exact_group_checks = 0
    for n in range(2, 10):
        honest = uniform(n)
        adversarial_laws = [
            {0: Fraction(1)},
            {(n - 1): Fraction(1)},
            normalize([i + 1 for i in range(n)]),
            normalize([1 if i % 2 == 0 else 3 for i in range(n)]),
        ]
        for adversarial in adversarial_laws:
            assert convolution_mod(adversarial, honest, n) == honest
            assert convolution_mod(honest, adversarial, n) == honest
            exact_group_checks += 2

    target_weights = [2, 3, 5, 7]
    encoded = encoded_rational_lottery(target_weights)
    target = normalize(target_weights)
    assert encoded == target

    # Both joint laws have a uniform XOR signal.  A transition that observes
    # the raw pair nevertheless distinguishes them perfectly.
    fair_bit = uniform(2)
    dev_zero = {0: Fraction(1)}
    dev_one = {1: Fraction(1)}
    xor_zero = convolution_mod(dev_zero, fair_bit, 2)
    xor_one = convolution_mod(dev_one, fair_bit, 2)
    assert xor_zero == xor_one == fair_bit
    raw_zero_probability = hidden_transition_probability(
        dev_zero, fair_bit, lambda left, _right: left == 0
    )
    raw_one_probability = hidden_transition_probability(
        dev_one, fair_bit, lambda left, _right: left == 0
    )
    assert raw_zero_probability == 1 and raw_one_probability == 0

    return {
        "experiment": "E01",
        "status": "passed",
        "exact_group_identities_checked": exact_group_checks,
        "encoded_lottery": {str(k): str(v) for k, v in encoded.items()},
        "factor_through_signal_counterexample": {
            "same_signal_law": True,
            "raw_transition_probabilities": [
                str(raw_zero_probability),
                str(raw_one_probability),
            ],
        },
        "conclusion": (
            "Finite-group addition supplies robust public randomness against one "
            "deviator, but only signal-measurable continuations inherit robustness."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
