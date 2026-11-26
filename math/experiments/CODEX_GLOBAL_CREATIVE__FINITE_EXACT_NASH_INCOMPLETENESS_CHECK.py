"""Exact check for the finite-exact-Nash incompleteness control.

Run with Python and SymPy installed. The full arbitrary-calendar and root
censuses are proved in the associated note, not inferred from this bounded run.
"""
from itertools import combinations
from fractions import Fraction as F
import sympy as sp

I = range(4)
T = {0, 1, 2}
coalitions = [frozenset(S) for k in range(1, 5) for S in combinations(I, k)]

def reward(i, S):
    S = frozenset(S)
    if i == 3:
        return F(1, 2) if S & T and 3 in S else int(bool(S & T))
    if 3 in S:
        return 1 if i in S else -1
    nxt, prv = (i + 1) % 3, (i - 1) % 3
    if i not in S:
        return 2 if S == {nxt} or S == {nxt, prv} else -1
    A = S - {i}
    if not A:
        return 0
    return 4 if A == {nxt} else -2 if A == {prv} else 1

assert all(reward(i, {i}) == 0 for i in I)
assert len([(i, S, reward(i, S)) for S in coalitions for i in I]) == 60

def endpoints(i, q):
    opp = [j for j in I if j != i]
    P = Q = 0
    for mask in range(8):
        S = frozenset(opp[k] for k in range(3) if mask & (1 << k))
        prob = 1
        for j in opp:
            prob *= q[j] if j in S else 1 - q[j]
        if S:
            P += prob * reward(i, S)
        Q += prob * reward(i, S | {i})
    H = 1
    for j in opp:
        H *= 1 - q[j]
    return P, Q, H

q = sp.symbols('q0:4')
v = sp.symbols('v0:4')
for i in T:
    P, Q, H = endpoints(i, q)
    a, b = q[(i + 1) % 3], q[(i - 1) % 3]
    assert sp.expand((Q - P - H*v[i]).subs(q[3], 0) -
                     (2*a - b - 2*a*b - v[i]*(1-a)*(1-b))) == 0
P, Q, H = endpoints(3, q)
assert sp.expand(Q - P - H*v[3] + (1-H)/2 + H*v[3]) == 0

G = sp.Matrix([[reward(i, {j}) for j in I] for i in I])
assert G == sp.Matrix([[0, 2, -1, -1], [-1, 0, 2, -1],
                       [2, -1, 0, -1], [1, 1, 1, 0]])
minor_census = [(S, G.extract(S, S).det()) for k in (2, 3, 4)
               for S in combinations(I, k)]
assert all(d != 0 for S, d in minor_census)
assert all(any(G[i, j] < 0 for i in I) for j in I)
assert all(x > 0 for x in G*sp.Matrix([2, 2, 2, 1]))
solutions = []
for k in (1, 2, 3, 4):
    for S in combinations(I, k):
        B = G.extract(S, S)
        if B.det() == 0:
            assert k == 1
            continue
        x = sp.zeros(4, 1)
        z = B.inv()*sp.ones(k, 1)
        for i, zi in zip(S, z):
            x[i] = zi
        w = G*x - sp.ones(4, 1)
        if all(x[i] > 0 for i in S) and all(w[i] >= 0 for i in I):
            solutions.append((S, x, w, B.det()))
assert len(solutions) == 1
S, x, w, d = solutions[0]
assert S == (0, 1, 2) and x == sp.Matrix([1, 1, 1, 0])
assert w == sp.Matrix([0, 0, 0, 2]) and d == 7
assert G.extract((0, 1, 2), (0, 1, 2)).inv() == \
       sp.Matrix([[2, 1, 4], [4, 2, 1], [1, 4, 2]])/7
L = sp.Matrix([[0 if i == j else reward(i, {i, j})-reward(i, {j})
                for j in I] for i in I])
assert L == sp.Matrix([[0, 2, -1, 2], [-1, 0, 2, 2],
                       [2, -1, 0, 2], [-sp.Rational(1, 2)]*3+[0]])
assert all(L.extract(S, S).det() == d for S, d in minor_census)
assert all(any(-L[i, j] < 0 for i in I) for j in I)
Fcore = sp.Matrix([endpoints(i, q)[1]-endpoints(i, q)[0] for i in range(3)])
Jcore = Fcore.jacobian(q[:3]).subs(dict(zip(q, [sp.Rational(1, 2)]*3+[0])))
assert Jcore.det() == -7

# Complete cap recursion includes all finite replies and literal Never.
def prefix(q, U, B, N):
    new_u, new_b = [], []
    for i in I:
        P, Q, H = endpoints(i, q)
        new_u.append(q[i]*Q + (1-q[i])*(P + H*U[i]))
        new_b.append(max(Q, P + H*B[i]))
    return new_u, new_b, [(1-q[i])*N[i] for i in I]

zero = [F(0)]*4
one = [F(1)]*4
mixed = [F(1, 2)]*3 + [F(0)]
U, B, N = prefix(mixed, zero, zero, one)
assert U == B == [F(3, 4)]*3 + [F(7, 8)]
assert N == [F(1, 2)]*3 + [F(1)]

pair = [F(1, 2), F(1, 2), F(0), F(0)]
V = [F(2), F(-1), F(1), F(1)]
for i in I:
    P, Q, H = endpoints(i, pair)
    C = P + H*V[i]
    assert pair[i]*Q + (1-pair[i])*C == V[i]
    assert max(Q, C) == V[i]
assert [endpoints(i, pair) for i in I] == [
    (F(1), F(2), F(1, 2)),
    (F(-1, 2), F(-1), F(1, 2)),
    (F(3, 4), F(3, 4), F(1, 4)),
    (F(3, 4), F(3, 8), F(1, 4)),
]
U = zero[:]
B = zero[:]
N = one[:]
for K in range(1, 33):
    U, B, N = prefix(pair, U, B, N)
    e, f = F(1, 2**K), F(1, 4**K)
    assert U == [2*(1-f), -1+f, 1-f, 1-f]
    assert B == [F(2), -1+e, 1-f, 1-f]
    assert sum(B[i]-U[i] for i in I) == e+f
    assert N == [e, e, F(1), F(1)]

# Explicit root homotopy: t = x - x^2, p = x/(1+x).
x, t, p = sp.symbols('x t p')
assert sp.factor((2*p-p-2*p*p-t*(1-p)**2).subs(p, x/(1+x)) +
                 (t+x*x-x)/(x+1)**2) == 0
print('PASS: full60, root equations, R0/minors/degree1 census, actual inert source,')
print('      exact absorbing stationary cap equations, and 32 finite full-cap words.')
print('Principal minors:', minor_census)
