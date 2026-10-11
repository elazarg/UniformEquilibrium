"""Exact support/endpoints for the K10 nonconvex cap-chamber candidate.

Run from math/: python notes/CODEX_EMMY_BOX__CAP_CHAMBER_SYMBOLIC_CHECK.py
SymPy and standard-library Fractions only. No numerical search.
"""

from fractions import Fraction
from itertools import combinations, product

import sympy as sp


def reward(mask):
    members = [i for i in range(4) if mask >> i & 1]
    n = len(members)
    if n == 0:
        return [0] * 4
    if n == 1:
        i = members[0]
        out = [0] * 4
        out[i], out[(i + 2) % 4] = 1, 4
        return out
    if n == 2:
        out = [0 if i in members else 1 for i in range(4)]
        for i in members:
            if (i + 1) % 4 in members:
                out[i], out[(i + 1) % 4] = -1, 2
        return out
    if n == 3:
        return [-1 if i in members else 10 for i in range(4)]
    return [9] * 4


q = sp.symbols("q0:4")
z = sp.symbols("z0:4")
Q, stop, alpha = [], [], []
for i in range(4):
    qi = bi = sp.S.Zero
    for mask in range(16):
        if mask >> i & 1:
            continue
        mass = sp.prod(q[j] if mask >> j & 1 else 1 - q[j]
                       for j in range(4) if j != i)
        qi += mass * reward(mask | 1 << i)[i]
        if mask:
            bi += mass * reward(mask)[i]
    Q.append(sp.expand(qi))
    stop.append(sp.expand(bi))
    alpha.append(sp.prod(1 - q[j] for j in range(4) if j != i))


def equal(x, y):
    assert sp.cancel(x - y) == 0, (x, y, sp.factor(x - y))


a, b, e = sp.symbols("a b e")
adj = dict(zip(q, [a, b, 0, 0]))
opp = dict(zip(q, [a, 0, b, 0]))
triple = dict(zip(q, [a, b, e, 0]))
equal(((Q[0] - stop[0]) / alpha[0]).subs(adj), (1 - 2*b)/(1-b))
equal(((Q[1] - stop[1]) / alpha[1]).subs(adj), (1 + a)/(1-a))
equal(((Q[0] - stop[0]) / alpha[0]).subs(opp), (1 - 5*b)/(1-b))
equal(((Q[2] - stop[2]) / alpha[2]).subs(opp), (1 - 5*a)/(1-a))
equal(Q[0].subs(triple), 1 - 2*b - e + b*e)
equal(stop[0].subs(triple), (4 - 3*b)*e)
equal(Q[2].subs(triple), 1 - a + b - 2*a*b)
equal(stop[2].subs(triple), (4 - 3*b)*a)
equal((Q[0] - stop[0]).subs(triple), 1 - 2*b - 5*e + 4*b*e)
equal((Q[2] - stop[2]).subs(triple), 1 - 5*a + b + a*b)
print("pair/triple raw endpoints and threshold numerators: exact")

odds_sub = {q[i]: z[i] / (1 + z[i]) for i in range(4)}
V = []
for i in range(4):
    x, y, w = z[(i - 1) % 4], z[(i + 2) % 4], z[(i + 1) % 4]
    T, triple_odds = x*y + x*w + y*w, x*y*w
    pi = 1 + 2*x - w - T + 9*triple_odds
    ni = 4*y + T + 10*triple_odds
    den = sp.prod(1 + z[j] for j in range(4) if j != i)
    equal(Q[i].subs(odds_sub) * den, pi)
    equal(stop[i].subs(odds_sub) * den, ni)
    equal(((Q[i] - stop[i]) / alpha[i]).subs(odds_sub), pi - ni)
    V.append(pi - ni)
E2z = sum(z[i]*z[j] for i, j in combinations(range(4), 2))
E3z = sum(sp.prod(z[i] for i in inds) for inds in combinations(range(4), 3))
equal(sum(V), 4 - 3*sum(z) - 4*E2z - E3z)
s = sum(q)
Aq = sum(q[i]*q[(i + 1) % 4] for i in range(4))
Oq = q[0]*q[2] + q[1]*q[3]
E3q = sum(sp.prod(q[i] for i in inds) for inds in combinations(range(4), 3))
equal(sum(Q) - 4, -2*s - Aq - 2*Oq + 12*E3q)
print("full-support odds cancellation and sum-Q polynomial: exact")

mass = [sp.prod(q[i] if mask >> i & 1 else 1 - q[i]
                for i in range(4)) for mask in range(16)]
P1 = sum(mass[m] for m in range(1, 16) if m.bit_count() == 1)
Padj = sum(mass[m] for m in [3, 6, 12, 9])
Popp = mass[5] + mass[10]
P3 = sum(mass[m] for m in range(16) if m.bit_count() == 3)
P4 = mass[15]
H = P1 - Padj - 2*Popp + 3*P3 + 32*P4
root_total = sum(mass[m] * sum(reward(m)) for m in range(1, 16))
equal(root_total - 4*(1 - mass[0]), H)
equal(H.subs(adj), a + b - 3*a*b)
equal(H.subs(opp), a + b - 4*a*b)
print("total-cap surplus and pair boundary formulas: exact")

laws = [
    [(None, Fraction(1))],
    [(0, Fraction(1, 2)), (None, Fraction(1, 2))],
    [(None, Fraction(1))],
    [(0, Fraction(1, 2)), (None, Fraction(1, 2))],
]


def payoff(i, response="prescribed"):
    own_laws = [list(law) for law in laws]
    if response != "prescribed":
        own_laws[i] = [(response, Fraction(1))]
    out = Fraction(0)
    for outcomes in product(*own_laws):
        dates = [pair[0] for pair in outcomes]
        prob = sp.prod(pair[1] for pair in outcomes)
        finite = [t for t in dates if t is not None]
        if finite:
            first = min(finite)
            mask = sum(1 << j for j in range(4) if dates[j] == first)
            out += prob * reward(mask)[i]
    return Fraction(out)


U = [payoff(i) for i in range(4)]
tests = [[payoff(i, response=t) for t in [0, 1, None]] for i in range(4)]
B = [max(row) for row in tests]
D = max(bi-ui for ui, bi in zip(U, B))
assert U == [Fraction(1, 4), Fraction(5, 4), Fraction(1, 4), Fraction(5, 4)]
assert B == [Fraction(1, 2), Fraction(5, 2), Fraction(1, 2), Fraction(5, 2)]
assert D == Fraction(5, 4)
assert sum(B) - 4 == Fraction(8, 5)*D
print("actual seed payoff:", U)
print("actual seed [Quit0, every positive deadline, Never]:", tests)
print("actual seed full caps:", B, "max full debt:", D)
print("ALL SYMBOLIC/RATIONAL CHECKS PASSED; no numerical root search used")
