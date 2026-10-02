#!/usr/bin/env python3
"""Exact sanity checks for the examples in this directory.

This is not numerical evidence for a theorem.  It prints exact deterministic
outcomes and Fraction-valued pure-time responses used in the notes.
"""

from fractions import Fraction

INF = None


def terminal(times):
    finite = [t for t in times.values() if t is not INF]
    if not finite:
        return frozenset()
    first = min(finite)
    return frozenset(i for i, t in times.items() if t == first)


def horizontal_no_go():
    source_a = {"j": INF, "p": INF, "k": 0}
    source_b = {"j": INF, "p": INF, "k": 2}
    target_a = dict(source_a, p=1)
    target_b = dict(source_b, p=1)

    reward_j = lambda coalition: 1 if coalition == frozenset({"p"}) else 0
    assert terminal(source_a) == terminal(source_b) == frozenset({"k"})
    assert reward_j(terminal(source_a)) == reward_j(terminal(source_b)) == 0
    assert reward_j(terminal(target_a)) == 0
    assert reward_j(terminal(target_b)) == 1
    return terminal(target_a), terminal(target_b)


def uniform_clock_values(size):
    # Opponent uniform on 1,...,size; solo=1, collision=opponent-first=0.
    values = []
    for deadline in range(size + 2):
        later = sum(1 for stop in range(1, size + 1) if stop > deadline)
        values.append(Fraction(later, size))
    return values


def spike_values(stop):
    # solo=1, collision=2, opponent-first=0.
    def value(deadline):
        if deadline < stop:
            return 1
        if deadline == stop:
            return 2
        return 0

    return value(stop - 1), value(stop), value(stop + 1)


if __name__ == "__main__":
    print("horizontal targets:", horizontal_no_go())
    print("uniform N=8:", uniform_clock_values(8))
    print("moving spike N=8:", spike_values(8))

