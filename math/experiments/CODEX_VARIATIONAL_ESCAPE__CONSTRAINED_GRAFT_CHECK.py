"""Exact controls for constrained grafts; no positive-A game is asserted."""
from fractions import Fraction as F
from itertools import product, combinations
import sympy as sp


G = sp.Matrix([[0, -1, 1, 1], [2, 0, -1, -1],
               [-1, 2, 0, -1], [-1, 2, -1, 0]])
assert G.det() == 4
assert G.inv()[:, 0] == sp.ones(4, 1)
I = range(4)


def reward(i, coalition):
    """All sixty entries: participant zero, passive singleton sum."""
    if i in coalition:
        return F(0)
    return F(sum(int(G[i, j]) for j in coalition))


TABLE = {(i, tuple(C)): reward(i, C)
         for k in range(1, 5) for C in combinations(I, k) for i in I}
assert len(TABLE) == 60
assert all(TABLE[i, (i,)] == 0 for i in I)


def payoff(laws):
    answer = [F(0)] * 4
    for draws in product(*(tuple(law.items()) for law in laws)):
        prob = F(1)
        for _, weight in draws:
            prob *= weight
        finite = [date for date, _ in draws if date is not None]
        if not finite:
            continue
        first = min(finite)
        C = tuple(i for i in I if draws[i][0] == first)
        for i in I:
            answer[i] += prob * TABLE[i, C]
    return answer


def semantics(laws):
    last = max([0] + [date for law in laws for date in law
                      if date is not None])
    U = payoff(laws)
    B, e = [], []
    for i in I:
        values = []
        for date in list(range(last + 2)) + [None]:
            replaced = list(laws)
            replaced[i] = {date: F(1)}
            values.append(payoff(replaced)[i])
        B.append(max(values))
        e.append(values[-1])
    N = [law.get(None, F(0)) for law in laws]
    nu = F(1)
    for n in N:
        nu *= n
    return U, B, e, N, nu


def graft(prefix, tail):
    last = max([0] + [date for law in prefix for date in law
                      if date is not None])
    offset = last + 2
    out = []
    for i in I:
        law = {date: weight for date, weight in prefix[i].items()
               if date is not None}
        never = prefix[i].get(None, F(0))
        for date, weight in tail[i].items():
            newdate = None if date is None else offset + date
            law[newdate] = law.get(newdate, F(0)) + never * weight
        out.append(law)
    return out


root = [{0: F(1, 5), None: F(4, 5)} for _ in I]
U, B, e, N, nu = semantics(root)
assert U == [F(4, 25), 0, 0, 0]
assert B == e == [F(1, 5), 0, 0, 0]
assert nu == F(256, 625)
assert B[0] - U[0] + nu / 2 == F(153, 625) < F(1, 2)

# Full response classes include every occupied date, intervening date, a late
# date and Never. Native own zero makes all later dates equal to the last one.
prefixes = [
    [{None: F(1)} for _ in I],
    root,
    [{0: F(i + 1, 20), 2: F(1, 5), None: F(15 - i, 20)}
     for i in I],
]
for P in prefixes:
    pU, pB, pe, pN, pnu = semantics(P)
    qU, qB, qe, qN, qnu = semantics(root)
    nU, nB, ne, nN, nnu = semantics(graft(P, root))
    for i in I:
        H = F(1)
        for j in I:
            if j != i:
                H *= pN[j]
        assert nU[i] == pU[i] + pnu * qU[i]
        assert nB[i] == max(pB[i], pe[i] + H * qB[i])
        assert ne[i] == pe[i] + H * qe[i]
        assert nN[i] == pN[i] * qN[i]
        if i != 0:
            assert nU[i] == pU[i] and nB[i] == pB[i]
    assert nnu == pnu * qnu

# The exact exponential optimum has rational survival when v=(1,1,1,1)
# and r=1/2: T=log3, N_i=1/3. No floating comparison is used.
r, S, vh, k = F(1, 2), F(4), F(1), F(3)
b = (1 - F(1, 3) ** 3) / k
u = (1 - F(1, 3) ** 4) / S
phi = b - u + r * F(1, 3) ** 4
closed = vh / (S * k) * (1 - (1 + r * S) ** (-3))
assert phi == closed == F(13, 162)
assert r - phi == F(34, 81) > 0
assert F(1, 3) == 1 / (1 + r * S)

# Independent symbolic scalar derivative and optimum simplification.
y, ss, hh, rr, nn = sp.symbols('y ss hh rr nn', positive=True)
kk = ss - hh
tail_b = (1 - sp.exp(-kk * y)) / kk
tail_u = (1 - sp.exp(-ss * y)) / ss
cost = tail_b / nn - tail_u - rr * (1 - sp.exp(-ss * y))
assert sp.simplify(sp.diff(cost, y) - sp.exp(-ss * y) *
                   (sp.exp(hh * y) / nn - 1 - rr * ss)) == 0
ph = hh / (ss * kk) * (1 - (1 + rr * ss) ** (-kk / hh))
assert sp.simplify(sp.diff(ph, rr) -
                   (1 + rr * ss) ** (-ss / hh)) == 0

# Exact switched-cone state updates. The matching matrix has positive inverse,
# so its inverse columns and their sums are admissible positive-drift controls.
K = sp.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
               [-1, -1, 0, 3], [-1, -1, 3, 0]])
V = K.inv()
assert all(z > 0 for z in V)
assert K.T * sp.ones(4, 1) == sp.ones(4, 1)
surv = [F(1, 2)] * 4
joint = F(1, 16)
debt = [F(0)] * 4
objective = joint
controls = [V[:, 0], V[:, 2], V[:, 1] + V[:, 3], V[:, 0]]
for control in controls:
    a = K * control
    assert all(z >= 0 for z in a)
    den = int(sp.ilcm(*[z.q for z in control]))
    nums = [int(z * den) for z in control]
    total = sum(nums)
    x = [F(z, den) for z in nums]
    rate = sum(x)
    next_surv = [surv[i] * F(1, 2) ** nums[i] for i in I]
    next_joint = joint * F(1, 2) ** total
    next_debt = list(debt)
    for i in I:
        ai = F(a[i])
        inc_u = joint * ai * (1 - F(1, 2) ** total) / rate
        inc_b = (joint / surv[i]) * ai * (
            1 - F(1, 2) ** (total - nums[i])) / (rate - x[i])
        next_debt[i] += inc_b - inc_u
        assert next_debt[i] >= debt[i]
    next_objective = sum(next_debt) + next_joint
    assert next_objective >= objective
    # The invariant uses the INITIAL p=(1,1,1,1), whose pairing with Kx
    # equals sum x. Every current p_i=1/N_i-1 is at least its initial value.
    current_p = [1 / surv[i] - 1 for i in I]
    assert sum(current_p[i] * F(a[i]) for i in I) >= rate
    surv, joint, debt, objective = (
        next_surv, next_joint, next_debt, next_objective)

print('PASS: all60 literal rewards, complete finite-clock response classes,')
print('      exact observer-preserving grafts, scalar optimum and strict gap,')
print('      and switched positive-cone dynamics; no positive-A control claimed.')
