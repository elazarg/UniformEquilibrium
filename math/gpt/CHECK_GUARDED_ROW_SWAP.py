#!/usr/bin/env python3
"""Exact arithmetic checks for GUARDED_ROW_SWAP_DEGREE_ESCAPE.md.

Requires Python 3 and SymPy. Run: python CHECK_GUARDED_ROW_SWAP.py
This checks the finite fixture and its certificates, not the topological theorem.
No numerical equilibrium solver or floating-point calculation is used.
"""
from __future__ import annotations

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("This checker requires SymPy: python -m pip install sympy") from exc

if not __debug__:
    raise SystemExit("Run without -O: this certificate checker uses assertions.")

I = tuple(range(4))
# A coalition is its binary mask. Row zero is a bookkeeping Never payoff.
R = sp.Matrix([
    [0, 0, 0, 0],
    [1, 4, 0, 0],       # 0
    [4, 1, 0, 0],       # 1
    [-3, -3, 4, 2],     # 01
    [0, 0, 1, 4],       # 2
    [1, 4, 4, -1],      # 02
    [-3, 3, -3, 3],     # 12
    [-4, 3, -3, -2],    # 012
    [0, 0, 4, 1],       # 3
    [3, -1, 2, -1],     # 03
    [-2, 3, -2, 1],     # 13
    [-3, -3, -4, -1],   # 013
    [0, -2, 1, 1],      # 23
    [2, -3, 1, 0],      # 023
    [0, 3, 1, 1],       # 123
    [-1, -5, -4, 0],    # 0123
])
G = sp.Matrix([[R[1 << j, i] - R[1 << i, i] for j in I] for i in I])
expected_g = sp.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
                        [-1, -1, 0, 3], [-1, -1, 3, 0]])
assert G == expected_g
P = sp.eye(4)
P.row_swap(0, 1)
A = P * G
B = G.inv()
assert G.det() == 45 and A.det() == -45
assert B == sp.Matrix([[2, 7, 3, 3], [7, 2, 3, 3],
                       [3, 3, 2, 7], [3, 3, 7, 2]]) / 15
assert all(x > 0 for x in B) and all(x > 0 for x in A.inv())
assert A.inv() == B * P
assert B * sp.ones(4, 1) == sp.ones(4, 1)
print("Matrix determinants and strict inverse positivity: PASS")

for i, j in [(0, 1), (1, 0)]:
    assert G[i, j] == 3
    lo = min(R[(1 << i) | t, i] for t in (0, 4, 8, 12))
    hi = max(R[t, i] for t in (4, 8, 12))
    gaps = [R[(1 << j) | t, i] - R[3 | t, i] for t in (0, 4, 8, 12)]
    assert lo - hi == 1 and min(gaps) >= 1
    print(f"Player {i} guards: absent margin={lo-hi}; present margins={gaps}")


def endpoint_terms(i: int, q: list) -> tuple:
    """Return exact Quit reward, absorbing Continue contribution, and survival."""
    alpha = sp.prod(1 - q[j] for j in I if j != i)
    quit_reward = continue_reward = sp.Integer(0)
    for mask in range(16):
        if mask & (1 << i):
            continue
        probability = sp.prod(
            q[j] if mask & (1 << j) else 1 - q[j] for j in I if j != i
        )
        quit_reward += probability * R[mask | (1 << i), i]
        if mask:
            continue_reward += probability * R[mask, i]
    return tuple(map(sp.simplify, (quit_reward, continue_reward, alpha)))


def residuals(q: list) -> list:
    return [sp.simplify((1-a)*Q-H) for Q, H, a in
            (endpoint_terms(i, q) for i in I)]

half = [sp.Rational(1, 2)] * 4
half_residuals = residuals(half)
assert half_residuals == [-sp.Rational(5, 16), -sp.Rational(1, 32),
                          -sp.Rational(23, 32), -sp.Rational(17, 32)]
assert len(set(half_residuals)) == 4
# This point lies in EVERY block-constant subspace. Pairwise distinct
# residuals rule out every nondiscrete response-invariant partition at once.
print("No nondiscrete response-invariant partition: PASS", half_residuals)

# Exact strict Farkas certificates for the relaxed F,J child-extension LPs.
# Never inequalities are OMITTED, so infeasibility covers both variants.
certificates = {
    0: [("F", 4, 2), ("J", 6, 3), ("F", 8, 4), ("F", 14, 9)],
    1: [("J", 4, 1), ("F", 9, 1)],
    2: [("J", 1, 86), ("J", 2, 19), ("J", 3, 22)],
    3: [("J", 2, 5), ("F", 5, 7), ("F", 7, 2)],
}
expected_duals = {
    0: ([-12, -12, -12], 12),
    1: ([-1, -1, -1], 5),
    2: ([-133, -602, -133], 133),
    3: ([-25, -25, -28], 25),
}
for k, certificate in certificates.items():
    child = [i for i in I if i != k]
    vector = sp.zeros(3, 1)
    scalar = sp.Integer(0)
    for kind, mask, weight in certificate:
        assert mask and not mask & (1 << k) and weight > 0
        if kind == "F":
            row = [R[1 << i, i] - R[mask, i] for i in child]
            rhs = R[1 << k, k] - R[mask, k]
        else:
            row = [R[mask | (1 << i), i] - R[mask, i] for i in child]
            rhs = R[mask | (1 << k), k] - R[mask, k]
        vector += weight * sp.Matrix(row)
        scalar += weight * rhs
    assert (list(vector), scalar) == expected_duals[k]
    assert all(x < 0 for x in vector) and scalar > 0
    print(f"Delete {k}: V^T y={list(vector)}, b.y={scalar}: INFEASIBLE")

# Literal rational equilibrium. Players 2 and 3 are sure date-zero quitters.
q = [sp.Rational(5, 7), sp.Rational(2, 3), sp.Integer(1), sp.Integer(1)]
assert residuals(q) == [0, 0, sp.Rational(1, 21), sp.Rational(11, 21)]
values = []
caps = []
C = sp.prod(1-x for x in q)
for i in I:
    Q, H, alpha = endpoint_terms(i, q)
    assert alpha < 1
    value = sp.simplify((q[i]*Q + (1-q[i])*H)/(1-C))
    cap = max(Q, H/(1-alpha))
    assert value == cap
    values.append(value)
    caps.append(cap)
assert values == [0, -sp.Rational(19, 7), -sp.Rational(29, 21), sp.Rational(2, 7)]
print("Exact screened equilibrium: q=", q, "; U=B=", values)

# No pure coalition can be an equilibrium: a profitable membership toggle
# always has a nonempty alternative, so no hidden continuation is used.
for mask in range(1, 16):
    gains = [R[mask ^ (1 << i), i] - R[mask, i]
             for i in I if mask ^ (1 << i)]
    assert max(gains) >= 1
assert all(R[1 << i, i] == 1 for i in I)
# Uniform small stationary hazards have limiting surplus G*1/4 = 1/4.
assert G * sp.ones(4, 1) / 4 == sp.ones(4, 1) / 4
# Every principal triple has a negative inverse entry; no reciprocal edge
# has the opposite signs required for a singleton escort.
for k in I:
    child = [i for i in I if i != k]
    assert any(x < 0 for x in G.extract(child, child).inv())
for i in I:
    for j in I:
        if i != j:
            assert not (G[i, j] <= 0 <= G[j, i])
print("Pure, payoff-exclusion, triple-inverse, and escort comparisons: PASS")

# Sufficient arithmetic margins for the full reward neighborhood delta<1/1000.
delta = sp.Rational(1, 1000)
assert 6*delta < 1
assert 6*delta/(1-6*delta) < min(B)
assert 2*delta < 1
assert sp.Rational(7, 2)*delta < sp.Rational(3, 16)
for k, certificate in certificates.items():
    vector, scalar = expected_duals[k]
    error = 2*delta*sum(weight for _, _, weight in certificate)
    assert all(x + error < 0 for x in vector) and scalar-error > 0
assert 1-6*delta > 0
print("Full-dimensional neighborhood margins: PASS")
print("ALL FINITE CHECKS PASSED (not a Lean proof of the general theorem).")
