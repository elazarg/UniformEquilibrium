"""Exact paired private-Never calibration checks. No files are written."""

from fractions import Fraction as F
from itertools import product


PAIRS = ({0, 2}, {1, 3})
PARTNER = (2, 3, 0, 1)
Q = F(1, 7)
A = 1 - Q
V = (F(8, 7), F(1, 3), F(1, 7), F(1, 3))


def reward(coalition):
    """A complete rational canonical reward table on all 15 coalitions."""
    result = []
    for i in range(4):
        own_pair = {i, PARTNER[i]}
        other_pair = set(range(4)) - own_pair
        if len(coalition) == 1:
            owner = next(iter(coalition))
            value = F(1) if owner == i else F(0) if owner == PARTNER[i] else F(127, 63)
        elif coalition == own_pair:
            value = F(2)
        elif coalition == other_pair:
            value = F(0)
        elif i in coalition:
            value = F(1)
        else:
            value = F(0)
        result.append(value if i == 0 else value - 1)
    return tuple(result)


def expectation(laws):
    result = [F(0)] * 4
    for atoms in product(*(tuple(law.items()) for law in laws)):
        probability = F(1)
        for _, mass in atoms:
            probability *= mass
        finite = [time for time, _ in atoms if time is not None]
        if not finite or probability == 0:
            continue
        first = min(finite)
        coalition = {i for i, (time, _) in enumerate(atoms) if time == first}
        values = reward(coalition)
        for i in range(4):
            result[i] += probability * values[i]
    return tuple(result)


def check(cycles):
    horizon = 2 * cycles
    laws = []
    for i in range(4):
        phase = 0 if i in PAIRS[0] else 1
        law = {2 * t + phase: Q * A**t for t in range(cycles)}
        law[None] = A**cycles
        laws.append(law)
    values = expectation(laws)
    xi = tuple(A ** (3 * cycles) * value for value in V)
    menu_regrets = []
    never_values = []
    for i in range(4):
        responses = {}
        for time in (*range(horizon), None):
            replacement = list(laws)
            replacement[i] = {time: F(1)}
            responses[time] = expectation(replacement)[i]
        assert values[i] == (1 - A ** (4 * cycles)) * V[i]
        assert responses[None] == (1 - A ** (3 * cycles)) * V[i]
        assert max(responses[time] for time in range(horizon)) == V[i]
        for time in laws[i]:
            if time is not None:
                assert responses[time] == V[i]
        auxiliary_cap = max(value + (xi[i] if time is None else 0) for time, value in responses.items())
        auxiliary_value = values[i] + laws[i][None] * xi[i]
        assert auxiliary_cap == auxiliary_value == V[i]
        menu_regrets.append(max(responses.values()) - values[i])
        never_values.append(responses[None])
    deleted_never = A ** (3 * cycles)
    late = never_values[0] + deleted_never - values[0]
    complete_error = max(max(menu_regrets), late)
    assert late <= deleted_never
    assert complete_error <= max(xi)
    print(f"K={cycles}: auxiliary regrets=0; E={complete_error}; L0={late}; max bonus={max(xi)}")


if __name__ == "__main__":
    for k in (1, 2, 3):
        check(k)
