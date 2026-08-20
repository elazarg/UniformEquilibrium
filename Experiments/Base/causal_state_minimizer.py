"""E08: exact causal-state/predictive-quotient experiment.

The first part performs exact Bayesian filtering in a three-state hidden Markov
chain and shows an unbounded family of pairwise predictively distinguishable
beliefs.  The second part computes shortest synchronizing words in the Cerny
automata, connecting finite observer memory with subset synchronization.
"""

from __future__ import annotations

import json
from collections import deque
from fractions import Fraction
from typing import Iterable

Belief = tuple[Fraction, ...]
Matrix = tuple[tuple[Fraction, ...], ...]


def predict(belief: Belief, transition: Matrix) -> Belief:
    n = len(belief)
    return tuple(
        sum((belief[i] * transition[i][j] for i in range(n)), Fraction(0))
        for j in range(n)
    )


def observe(predicted: Belief, labels: tuple[int, ...], symbol: int) -> Belief:
    mass = sum((p for p, label in zip(predicted, labels) if label == symbol), Fraction(0))
    if mass == 0:
        raise ValueError("impossible observation")
    return tuple(p / mass if label == symbol else Fraction(0) for p, label in zip(predicted, labels))


def next_symbol_probability(
    belief: Belief, transition: Matrix, labels: tuple[int, ...], symbol: int
) -> Fraction:
    return sum(
        (p for p, label in zip(predict(belief, transition), labels) if label == symbol),
        Fraction(0),
    )


def shortest_synchronizing_word(n: int) -> tuple[str, int]:
    """Breadth-first subset construction for the standard Cerny automaton."""
    start = frozenset(range(n))

    def action_a(state: int) -> int:
        return (state + 1) % n

    def action_b(state: int) -> int:
        return 0 if state == n - 1 else state

    queue = deque([(start, "")])
    seen = {start}
    while queue:
        subset, word = queue.popleft()
        if len(subset) == 1:
            return word, len(seen)
        for letter, action in [("a", action_a), ("b", action_b)]:
            successor = frozenset(action(state) for state in subset)
            if successor not in seen:
                seen.add(successor)
                queue.append((successor, word + letter))
    raise AssertionError("automaton did not synchronize")


def as_strings(values: Iterable[Fraction]) -> list[str]:
    return [str(value) for value in values]


def run() -> dict:
    # States a,b emit 0; c emits 1.  From a and b, survival under another zero
    # has different rates.  From c, the next zero initializes an equal mixture.
    p = Fraction(1, 2)
    q = Fraction(1, 3)
    transition: Matrix = (
        (p, Fraction(0), 1 - p),
        (Fraction(0), q, 1 - q),
        (Fraction(1, 2), Fraction(1, 2), Fraction(0)),
    )
    labels = (0, 0, 1)
    belief: Belief = (Fraction(0), Fraction(0), Fraction(1))

    posteriors = []
    next_one_probabilities = []
    for zero_count in range(1, 15):
        belief = observe(predict(belief, transition), labels, 0)
        expected_a = p ** (zero_count - 1) / (p ** (zero_count - 1) + q ** (zero_count - 1))
        assert belief[0] == expected_a
        next_one = next_symbol_probability(belief, transition, labels, 1)
        posteriors.append(belief)
        next_one_probabilities.append(next_one)

    assert len(set(posteriors)) == len(posteriors)
    assert len(set(next_one_probabilities)) == len(next_one_probabilities)

    synchronization = []
    for n in range(2, 8):
        word, reachable_subsets = shortest_synchronizing_word(n)
        assert len(word) == (n - 1) ** 2
        synchronization.append(
            {
                "states": n,
                "shortest_word": word,
                "length": len(word),
                "reachable_subsets_seen_by_bfs": reachable_subsets,
            }
        )

    return {
        "experiment": "E08",
        "status": "passed",
        "hidden_markov_chain": {
            "distinct_reachable_posteriors": len(posteriors),
            "posterior_on_a": [str(belief[0]) for belief in posteriors],
            "next_one_probabilities": as_strings(next_one_probabilities),
            "distinguished_by_one_step_prediction": True,
        },
        "cerny_synchronization": synchronization,
        "conclusion": (
            "Finite hidden state does not imply finite exact predictive memory; "
            "when a finite quotient does exist, observer-subset and synchronization "
            "complexity are natural lower-bound mechanisms."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
