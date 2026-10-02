"""Independent exact tests for the canonical three-core support obstruction.

Run from math/: python experiments/CODEX_NOETHER_SUPPORT__CHECK_UNBOUNDED_CORE_SUPPORT.py
Standard library only; no file writes. These finite tests do not prove the
universal support-cardinality lower bound.
"""

from fractions import Fraction as F
from itertools import product


def reward(coalition):
    if not coalition:
        return (F(0),) * 4
    core = tuple(F(int(i in coalition) * (1 - 2 * int((i + 1) % 3 in coalition))
                   - int(i != 0)) for i in range(3))
    return core + (F(-int(3 in coalition and bool(coalition & {0, 1, 2}))),)


def outcome_law(laws):
    """Direct product enumeration; None denotes Never and has no date order."""
    result = {}
    for choices in product(*(tuple(law.items()) for law in laws)):
        times = tuple(item[0] for item in choices)
        mass = F(1)
        for _, probability in choices:
            mass *= probability
        finite = [time for time in times if time is not None]
        first = min(finite) if finite else None
        coalition = (frozenset(i for i, time in enumerate(times) if time == first)
                     if first is not None else frozenset())
        result[coalition] = result.get(coalition, F(0)) + mass
    assert sum(result.values()) == 1
    return result


def expected(laws):
    distribution = outcome_law(laws)
    return tuple(sum(prob * reward(coalition)[i]
                     for coalition, prob in distribution.items()) for i in range(4))


def complete_semantics(laws):
    """Every displayed date, intervening date, one late date, and Never."""
    cutoff = max((time for law in laws for time in law if time is not None), default=-1)
    responses = list(range(cutoff + 2)) + [None]
    caps = []
    for i in range(4):
        values = []
        for response in responses:
            changed = list(laws)
            changed[i] = {response: F(1)}
            values.append(expected(changed)[i])
        caps.append(max(values))
    prescribed = expected(laws)
    return prescribed, tuple(caps), max(caps[i] - prescribed[i] for i in range(4))


def root_regrets(q, continuation):
    """Compute endpoints from the entire table, independently of formula (3.1)."""
    regrets = []
    for i in range(4):
        others = [j for j in range(4) if j != i]
        quit_payoff = continue_payoff = F(0)
        for bits in product((0, 1), repeat=3):
            mass = F(1)
            coalition = set()
            for j, bit in zip(others, bits):
                mass *= q[j] if bit else 1 - q[j]
                if bit:
                    coalition.add(j)
            quit_payoff += mass * reward(coalition | {i})[i]
            continue_payoff += mass * (reward(coalition)[i] if coalition else continuation[i])
        regrets.append(max(quit_payoff, continue_payoff)
                       - q[i] * quit_payoff - (1 - q[i]) * continue_payoff)
        if i < 3:
            alpha = F(1)
            for j in others:
                alpha *= 1 - q[j]
            assert quit_payoff - continue_payoff == (
                1 - 2 * q[(i + 1) % 3] - alpha * (continuation[i] + int(i != 0)))
    return regrets


def check():
    for n in range(1, 7):
        law = {time: F(1, 2 ** (time + 1)) for time in range(n)}
        law[None] = F(1, 2**n)
        actual = [dict(law) for _ in range(3)] + [{None: F(1)}]
        prescribed, caps, exploitability = complete_semantics(actual)
        assert prescribed == (0, -1 + F(1, 8**n), -1 + F(1, 8**n), 0)
        assert caps == (F(1, 4**n), -1 + F(1, 4**n), -1 + F(1, 4**n), 0)
        assert exploitability == F(1, 4**n)

    compressed = [
        {0: F(4, 7), None: F(3, 7)},
        {0: F(1, 2), 1: F(1, 3), None: F(1, 6)},
        {0: F(1, 2), 1: F(1, 4), 2: F(1, 4)},
        {None: F(1)},
    ]
    distribution = outcome_law(compressed)
    positive = {coalition: mass for coalition, mass in distribution.items() if mass}
    assert len(positive) == 7
    assert all(coalition <= {0, 1, 2} and mass == F(1, 7)
               for coalition, mass in positive.items())
    prescribed, caps, exploitability = complete_semantics(compressed)
    assert prescribed == (0, -1, -1, 0)
    assert caps == (F(1, 24), -1, F(-11, 14), 0)
    assert exploitability == F(3, 14)

    # The analytic proof handles the continuum. This finite root/tail grid
    # separately tests the formula and its high-hazard conclusion.
    grid = tuple(F(k, 4) for k in range(5))
    checked = 0
    for q in product(grid, repeat=4):
        if max(q) < F(3, 4):
            continue
        for v in product((-1, 1), (-2, 0), (-2, 0), (-1, 0)):
            assert max(root_regrets(q, tuple(map(F, v)))) > F(1, 16)
            checked += 1
    assert checked == 8704
    print("PASS: six truncation profiles and all complete pure-response classes")
    print("PASS: identical seven-coalition law; different complete response caps")
    print("PASS:", checked, "exact root/tail checks (finite regression only)")


if __name__ == "__main__":
    check()
