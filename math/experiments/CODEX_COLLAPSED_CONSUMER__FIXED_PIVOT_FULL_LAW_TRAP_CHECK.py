"""Exact complete-law fixed-pivot trap and finite response-table producer.

All calculations use fractions. The pivot has an exact infinite geometric
law, never a truncated approximation. Observer calendars are finite only
for the bounded checks; the accompanying proof covers arbitrary laws.
"""

from fractions import Fraction as F
from itertools import product
import json

I, T, NEVER = range(4), (1, 2, 3), 99
h, s = F(9, 10), F(1, 10)
b = {1: F(1), 2: F(1), 3: F(-1)}
gamma = F(13, 25)
never_gap = {1: F(3, 5), 2: F(3, 5), 3: F(8, 5)}
Z = {}
for mask in range(1, 16):
    S = frozenset(i for i in I if mask & (1 << i))
    for i in I:
        if i == 0:
            value = 0 if S == {0} else (1 if 0 in S else 2)
        elif 0 in S:
            value = 2 if i in S else b[i]
        elif i in S:
            value = {1: 0, 2: -2, 3: -1}[len(S)]
        else:
            value = {1: -1, 2: 0}[len(S)]
        Z[i, S] = F(value)
assert len(Z) == 60
assert all(Z[i, frozenset({i})] == 0 for i in I)
assert all(any(Z[i, frozenset({j})] < 0 for i in I if i != j) for j in I)


def geometric_coefficient(times):
    """Exact expected reward at three deterministic observer dates."""
    first = min(times)
    if first == NEVER:
        return [Z[i, frozenset({0})] for i in I]
    S = frozenset(i for i, time in zip(T, times) if time == first)
    return [(1 - s ** first) * Z[i, frozenset({0})]
            + h * s ** first * Z[i, S | {0}]
            + s ** (first + 1) * Z[i, S] for i in I]


def pivot_response_coefficient(deadline, times):
    first = min(deadline, *times)
    if first == NEVER:
        return F(0)
    S = frozenset(i for i, time in zip(T, times) if time == first)
    if deadline == first:
        S |= {0}
    return Z[0, S]


def expected(laws):
    U = [F(0) for _ in I]
    for choices in product(*(tuple(law.items()) for law in laws)):
        times, masses = zip(*choices)
        mass = masses[0] * masses[1] * masses[2]
        values = geometric_coefficient(times)
        U = [u + mass * value for u, value in zip(U, values)]
    return U


def semantic_pair(laws, H):
    U, B = expected(laws), []
    pivot_values = []
    for deadline in (*range(H + 2), NEVER):
        value = F(0)
        for choices in product(*(tuple(law.items()) for law in laws)):
            times, masses = zip(*choices)
            value += (masses[0] * masses[1] * masses[2]
                      * pivot_response_coefficient(deadline, times))
        pivot_values.append(value)
    B.append(max(pivot_values))
    for i in T:
        responses = []
        for deadline in (*range(H + 2), NEVER):
            changed = list(laws)
            changed[i - 1] = {deadline: F(1)}
            responses.append(expected(changed)[i])
        B.append(max(responses))
    return U, B


dominance_checks = 0
for H in range(5):
    actions = (*range(H + 1), NEVER)
    for i in T:
        others = [j for j in T if j != i]
        for other_dates in product(actions, repeat=2):
            times = dict(zip(others, other_dates))
            times[i] = 0
            best = geometric_coefficient(tuple(times[j] for j in T))[i]
            for deadline in (*range(1, H + 2), NEVER):
                times[i] = deadline
                value = geometric_coefficient(tuple(times[j] for j in T))[i]
                assert best - value >= gamma
                if deadline == NEVER:
                    assert best - value >= never_gap[i]
                dominance_checks += 1

source = [{0: F(1)} for _ in T]
U, B = semantic_pair(source, 0)
assert U == [F(11, 10), F(17, 10), F(17, 10), F(17, 10)]
assert B == [F(2), F(17, 10), F(17, 10), F(17, 10)]

grid = []
for n0 in range(3):
    for n1 in range(3 - n0):
        grid.append({0: F(n0, 2), 1: F(n1, 2), NEVER: F(2 - n0 - n1, 2)})
law_checks = 0
for laws in product(grid, repeat=3):
    U, B = semantic_pair(laws, 1)
    debts = [cap - value for cap, value in zip(B, U)]
    nu = laws[0][NEVER] * laws[1][NEVER] * laws[2][NEVER]
    assert B[0] == 2 * (1 - nu)
    assert debts[0] >= h * (1 - nu)
    for i in T:
        assert debts[i] >= never_gap[i] * laws[i - 1][NEVER]
    assert debts[0] >= h - F(25, 16) * debts[1] * debts[2] * debts[3]
    law_checks += 1

# Exact absorbing Nash with pivot Never and only observer 1 stopping at zero.
equilibrium_coalition = frozenset({1})
equilibrium_payoff = [Z[i, equilibrium_coalition] for i in I]
for i in I:
    if i == 1:
        responses = [F(0)]
    else:
        responses = [Z[i, equilibrium_coalition | {i}], Z[i, equilibrium_coalition]]
    assert max(responses) == equilibrium_payoff[i]

print(json.dumps({
    "status": "PASS: exact infinite-pivot coefficients and full finite-calendar responses",
    "geometric_hazard": str(h),
    "source_payoff": [str(x) for x in semantic_pair(source, 0)[0]],
    "source_cap": [str(x) for x in semantic_pair(source, 0)[1]],
    "uniform_response_gap": str(gamma),
    "never_gaps": {str(i): str(x) for i, x in never_gap.items()},
    "dominance_coefficient_checks": dominance_checks,
    "mixed_law_checks": law_checks,
    "global_gap": "zero: explicit absorbing Nash with pivot Never and one observer Quit0",
    "scope": "fixed proper pivot law, unrestricted observer trap; no global minimum claim"
}, indent=2))
