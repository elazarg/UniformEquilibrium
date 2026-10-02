#!/usr/bin/env python3
"""Exact finite checks for the half-ceiling crossed-response degree theorem.

Only the Python standard library is used. All calculations use Fraction;
there is no floating-point root search, LP solver, or external input.
This is an arithmetic verification, not a Lean check of the general proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from typing import Iterable

I = tuple(range(4))
# Coalition bitmasks; columns are payoff recipients 0,1,2,3.
RAW = {
    1: (1, 3, -1, -1),
    2: (4, 0, -1, -1),
    3: (5, 4, F(178, 7), 2),
    4: (0, -1, 0, 3),
    5: (F(7, 3), 0, 8, -1),
    6: (1, F(83, 91), -2, 2),
    7: (-5, -6, F(199, 7), -4),
    8: (0, -1, 3, 0),
    9: (2, 0, 4, -4),
    10: (1, 1, 3, 6),
    11: (-5, -6, 7, 0),
    12: (0, -1, 3, 0),
    13: (2, 0, -5, 7),
    14: (1, 1, 8, -3),
    15: (-5, -6, -3, -4),
}
r = {A: tuple(F(x) for x in row) for A, row in RAW.items()}
s = tuple(r[1 << i][i] for i in I)
assert s == (1, 0, 0, 0)


def prod(xs: Iterable[F]) -> F:
    answer = F(1)
    for x in xs:
        answer *= x
    return answer


def inverse_and_det(matrix: list[list[F]]) -> tuple[list[list[F]], F]:
    n = len(matrix)
    a = [row[:] + [F(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    det = F(1)
    for j in range(n):
        p = next((i for i in range(j, n) if a[i][j]), None)
        if p is None:
            raise ValueError("Singular matrix")
        if p != j:
            a[j], a[p] = a[p], a[j]
            det = -det
        d = a[j][j]
        det *= d
        a[j] = [x/d for x in a[j]]
        for i in range(n):
            if i != j:
                t = a[i][j]
                a[i] = [x-t*y for x, y in zip(a[i], a[j])]
    return [row[n:] for row in a], det


def endpoints(q: tuple[F, ...], i: int, table=None) -> tuple[F, F, F, F]:
    if table is None:
        table = r
    alpha = prod(1-q[j] for j in I if j != i)
    Q, H = F(0), F(0)
    for A in range(16):
        if A & (1 << i):
            continue
        w = prod(q[j] if A & (1 << j) else 1-q[j] for j in I if j != i)
        Q += w*table[A | (1 << i)][i]
        if A:
            H += w*table[A][i]
    return alpha, Q, H, (1-alpha)*Q-H


def delta(q: tuple[F, ...]) -> tuple[F, ...]:
    return tuple(endpoints(q, i)[3] for i in I)


def bernstein(i: int, table=None) -> list[list[F]]:
    """Degree-(2,2) coefficients of Delta_i at partner hazard exactly 1/2."""
    values = []
    for x in (F(0), F(1, 2), F(1)):
        row = []
        for y in (F(0), F(1, 2), F(1)):
            q = [F(0)]*4
            q[1-i], q[2], q[3] = F(1, 2), x, y
            row.append(endpoints(tuple(q), i, table)[3])
        values.append(row)
    # Univariate interpolation in y, then x.
    for a in range(3):
        values[a][1] = 2*values[a][1]-(values[a][0]+values[a][2])/2
    for b in range(3):
        values[1][b] = 2*values[1][b]-(values[0][b]+values[2][b])/2
    return values


G = [[r[1 << j][i]-s[i] for j in I] for i in I]
assert G == [[0, 3, -1, -1], [3, 0, -1, -1], [-1, -1, 0, 3], [-1, -1, 3, 0]]
B, detG = inverse_and_det(G)
assert detG == 45
assert B == [[F(x, 15) for x in row] for row in
             [[2, 7, 3, 3], [7, 2, 3, 3], [3, 3, 2, 7], [3, 3, 7, 2]]]
A = [G[1], G[0], G[2], G[3]]
AB, detA = inverse_and_det(A)
assert detA == -45 and all(x > 0 for row in AB for x in row)
assert AB == [[row[j] for j in (1, 0, 2, 3)] for row in B]
print("det(Gamma)=45; det(row-swap Gamma)=-45; both inverses strictly positive.")

external = (0, 4, 8, 12)
expected_coefficients = [
    [[-F(1, 2), -F(1, 8), -2], [-F(1, 12), -F(49, 48), -2],
     [-F(11, 6), -F(23, 12), -2]],
    [[-F(1, 2), -F(1, 8), -2], [-F(99, 728), -F(1563, 1456), -2],
     [-F(186, 91), -F(184, 91), -2]],
]
for i in (0, 1):
    lower_gap = min(r[T | (1 << i)][i] for T in external) - max(r[T][i] for T in external if T)
    assert lower_gap == 1
    coeff = bernstein(i)
    assert coeff == expected_coefficients[i]
    assert all(x < 0 for row in coeff for x in row)
    # The upper-at-one guard does NOT hold: pure-partner joining gains one.
    assert r[3][i]-r[1 << (1-i)][i] == 1
    print(f"Owner {i}: lower ranking gap {lower_gap}; half-ceiling Bernstein coefficients {coeff}.")
print("Pure-partner join gains are +1 for both owners: this is not the unit-ceiling guard class.")

# Each Bernstein coefficient has raw reward l1 coefficient norm at most 2.
coefficient_norms = [[F(0) for _ in range(3)] for _ in range(3)]
for coalition in range(1, 16):
    basis = {C: [F(0)]*4 for C in range(1, 16)}
    basis[coalition][0] = F(1)
    cs = bernstein(0, basis)
    for a in range(3):
        for b in range(3):
            coefficient_norms[a][b] += abs(cs[a][b])
assert coefficient_norms == [[1, F(3, 2), 2], [F(3, 2), F(7, 4), 2], [2, 2, 2]]
assert max(x for row in coefficient_norms for x in row) == 2
assert min(-x for cs in expected_coefficients for row in cs for x in row) == F(1, 12)
# Neumann estimate at reward perturbation radius 1/100.
assert F(6, 100)/(1-F(6, 100)) < F(2, 15)
assert 2*F(1, 100) < F(1, 12)
print("Reward radius 1/100 preserves all strict theorem hypotheses.")

q = (F(2, 9), F(1, 4), F(1, 3), F(0))
C = prod(1-x for x in q)
info = [endpoints(q, i) for i in I]
assert delta(q) == (0, 0, 0, -F(271, 1944))
U = tuple((q[i]*info[i][1]+(1-q[i])*info[i][2])/(1-C) for i in I)
caps = tuple(max(Q, H/(1-alpha)) for alpha, Q, H, _ in info)
assert U == caps == (F(3, 2), F(5, 13), F(53, 21), F(15, 22))
assert C == F(7, 18)
assert tuple(x[0] for x in info) == (F(1, 2), F(14, 27), F(7, 12), F(7, 18))
assert all(U[i] > s[i] for i in I)
M = max(abs(x) for row in r.values() for x in row)
assert M == F(199, 7)
assert 2*M/(1-F(7, 12)) == F(4776, 35)
print("Exact hazards:", q)
print("Stationary residuals:", delta(q))
print("Terminal payoff = full behavioral cap:", U)
print("Uniform horizon regret <= 4776/(35H); censored K-date regret <= (597/7)(7/12)^K.")

pure_witnesses = {}
for coalition in range(1, 16):
    choices = [i for i in I if (coalition ^ (1 << i)) and
               (coalition.bit_count() > 1 or not coalition & (1 << i)) and
               r[coalition ^ (1 << i)][i] > r[coalition][i]]
    assert choices
    i = choices[0]
    pure_witnesses[coalition] = (i, r[coalition ^ (1 << i)][i]-r[coalition][i])
assert s[0] > 0
print("Strict pure-coalition toggle witnesses:", pure_witnesses)


def partitions(items: tuple[int, ...]):
    if not items:
        yield []
        return
    for rest in partitions(items[1:]):
        yield [(items[0],)] + rest
        for k in range(len(rest)):
            yield rest[:k] + [(items[0],) + rest[k]] + rest[k+1:]


ps = list(partitions(I))
assert len(ps) == 15
ri_failures = []
for partition in ps:
    if len(partition) == 4:
        continue
    sums = [[sum(G[i][j] for j in block) for block in partition] for i in I]
    if any(sums[i] != sums[block[0]] for block in partition for i in block):
        ri_failures.append((partition, "first-order row sums"))
        continue
    witness = None
    for xs in product((F(0), F(1, 2), F(1)), repeat=len(partition)):
        point = tuple(xs[next(k for k, block in enumerate(partition) if i in block)] for i in I)
        ds = delta(point)
        for block in partition:
            for i in block:
                if ds[i] != ds[block[0]]:
                    witness = (point, block[0], i, ds[i]-ds[block[0]])
                    break
            if witness is not None:
                break
        if witness is not None:
            break
    assert witness is not None
    ri_failures.append((partition, witness))
assert len(ri_failures) == 14
print("Only the discrete partition is response-invariant. Nonlinear rejection witnesses:")
for partition, witness in ri_failures:
    if witness != "first-order row sums":
        print(" ", partition, witness)


def child_row(S: tuple[int, ...], k: int, kind: str, coalition: int):
    if kind == "N":
        return [s[i] for i in S], s[k]
    assert coalition and all(not coalition & (1 << i) for i in I if i not in S)
    if kind == "F":
        return [s[i]-r[coalition][i] for i in S], s[k]-r[coalition][k]
    if kind == "J":
        return [r[coalition | (1 << i)][i]-r[coalition][i] for i in S], \
            r[coalition | (1 << k)][k]-r[coalition][k]
    raise ValueError(kind)


# Exact dual inequalities V<=0, b>0, against V lambda>=b, lambda>=0.
certificates = {
    1: (1, [("J", 1, 1)]),
    3: (2, [("F", 1, 1)]),
    5: (1, [("J", 1, 1), ("F", 5, 2)]),
    7: (3, [("F", 5, 1)]),
    9: (1, [("J", 1, 1)]),
    11: (2, [("J", 3, 1)]),
    13: (1, [("J", 1, 1), ("F", 5, 2)]),
}
for mask in range(1, 15):
    S = tuple(i for i in I if mask & (1 << i))
    if 0 not in S:
        k, terms = 0, [("N", 0, 1)]
        assert all(s[i] == 0 for i in S)  # Positive-singleton relaxation unavailable.
    else:
        k, terms = certificates[mask]
    assert k not in S
    rows = [(weight, child_row(S, k, kind, coalition)) for kind, coalition, weight in terms]
    V = [sum(weight*row[0][j] for weight, row in rows) for j in range(len(S))]
    b = sum(weight*row[1] for weight, row in rows)
    assert all(x <= 0 for x in V) and b > 0
    print(f"Child {S}, outsider {k}: {terms}; V={V}, b={b} -> infeasible.")
print("All 14 proper-child raw domination tests fail, by exact dual certificates.")
print("PASS: all exact arithmetic checks. The general existence proof is not Lean-checked.")
