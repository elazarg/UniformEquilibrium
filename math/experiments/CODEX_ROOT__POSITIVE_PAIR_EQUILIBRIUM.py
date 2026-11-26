"""Exact checks for the positive-pair uniform equilibrium theorem. Requires NumPy and SymPy."""
from itertools import combinations, product
from math import comb, prod

import numpy as np
import sympy as sp


Z = [
    [0, 0, 0, 0], [0,-20,80,-20], [-20,0,-20,80], [-7,-16,140,-180],
    [80,-20,0,-100], [31,60,11,-80], [0,12,-50,60], [-100,-160,141,-140],
    [-20,80,-100,0], [20,20,0,-42], [-60,43,-160,7], [0,140,-160,-179],
    [-20,60,-43,-66], [-140,-40,-160,40], [60,140,-180,0], [20,0,100,-60],
]
owners = tuple(range(4))
x = sp.symbols("x0:4")
field = sp.Matrix([
    sum((Z[m | (1 << i)][i] - Z[m][i]) *
        prod(x[j] for j in owners if m & (1 << j))
        for m in range(1, 16) if not m & (1 << i))
    for i in owners
])
center = dict(zip(x, [sp.Rational(v, 10**8) for v in
                      (17854782,8451799,19554700,48393925)]))
inverse = field.jacobian(x).subs(center).inv()
assert max(sum(abs(v) for v in row) for row in inverse.tolist()) < sp.Rational(115, 1000)
assert max(abs(v) for v in inverse * field.subs(center)) < sp.Rational(21, 10**10)
Gamma = sp.Matrix([[sp.Rational(Z[1 << j][i], 20) for j in owners] for i in owners])
principal = [Gamma.extract(S, S).inv() for k in (2, 3, 4) for S in combinations(owners, k)]
assert max(sum(abs(a) for a in row) for M in principal for row in M.tolist()) == 3
floor = [max(min(Z[m][i] for m in range(16) if m & (1 << i)),
             min(Z[m][i] for m in range(16) if not m & (1 << i))) for i in owners]
assert floor == [-60,-40,-160,-179]


def coefficients(kind, mates=None):
    degree = 1 if kind == "sure" else 2
    fields = 8 if kind == "phases" else 4
    tensor = np.zeros((fields,) + (degree + 1,) * 4, dtype=object)
    for i in owners:
        rivals = [j for j in owners if j != i]
        totals = {}
        for b in product(range(2), repeat=3):
            mask = sum(v << j for j, v in zip(rivals, b))
            quit_pay = Z[mask | (1 << i)][i]
            samples = [()] if degree == 1 else product(range(2), repeat=3)
            for a in samples:
                exponent = b if degree == 1 else tuple(p+q for p,q in zip(a,b))
                if kind == "sure":
                    values = [quit_pay - Z[mask][i] - (floor[i] if mask == 0 else 0)]
                elif kind == "stationary":
                    values = [int(any(a)) * quit_pay - Z[mask][i]]
                else:
                    mate = mask & (1 << mates[i])
                    other = mask ^ mate
                    values = [int(any(a))*Z[mate | (1 << i)][i] - Z[mate or other][i],
                              int(any(a))*Z[other | (1 << i)][i] - Z[other or mate][i]]
                weight = 8 // prod(comb(degree,h) for h in exponent)
                for k, value in enumerate(values):
                    key = (exponent, k)
                    totals[key] = totals.get(key, 0) + weight * value
        for b in product(range(degree + 1), repeat=4):
            for k in range(fields // 4):
                tensor[(i+4*k,) + b] = totals[tuple(b[j] for j in rivals), k]
    return tensor


def children(data, coordinate):
    line = np.moveaxis(data, coordinate+1, -1)
    left, right = line[..., 0], line[..., -1]
    if line.shape[-1] == 2:
        halves = ((2*left,left+right),(left+right,2*right))
    else:
        mid = line[..., 1]
        shared = left+2*mid+right
        halves = ((4*left,2*(left+mid),shared),(shared,2*(mid+right),4*right))
    return [np.moveaxis(np.stack(h, axis=-1), -1, coordinate+1) for h in halves]


def tree(kind, sure=None, mates=None):
    # Coordinates are represented as integers on the common grid of spacing 2^-60.
    unit = 1 << 60
    low = [0]*4
    data = coefficients(kind, mates)
    free = [i for i in owners if i != sure]
    if sure is not None:
        low[sure] = unit
        data = np.take(data, [1,1], axis=sure+1)
    stack = [(low,[unit]*4,data,0)]
    count = near_origin = max_depth = 0
    while stack:
        low, high, data, depth = stack.pop()
        count += 1
        max_depth = max(max_depth, depth)
        if kind != "sure" and max(high)*512 <= unit:
            near_origin += 1
            continue
        lo = np.min(data, axis=(1,2,3,4))
        hi = np.max(data, axis=(1,2,3,4))
        if any(low[i]>0 and hi[i]<0 for i in owners):
            continue
        if kind == "phases" and any(value > 0 for value in lo):
            continue
        if kind != "phases" and any(high[i]<unit and lo[i]>0 for i in owners):
            continue
        j = free[depth % len(free)]
        assert (high[j] - low[j]) % 2 == 0 and high[j] > low[j]
        mid = (high[j]+low[j])//2
        left_high, right_low = high.copy(), low.copy()
        left_high[j] = right_low[j] = mid
        left, right = children(data, j)
        stack.extend([(low,left_high,left,depth+1),(right_low,high,right,depth+1)])
    return count, near_origin, max_depth


checks = [('stationary',{},(11747,1,52))]
checks += [('sure',{'sure':i},t) for i,t in enumerate(
    [(677,0,20),(269,0,15),(41,0,8),(45,0,9)])]
checks += [('phases',{'mates':m},(n,1,52)) for m,n in
           [((1,0,3,2),6511),((2,3,0,1),7787),((3,2,1,0),7573)]]
for kind, args, expected in checks:
    actual = tree(kind, **args)
    assert actual == expected, (kind, args, actual)
    print(kind, args, actual)


def period_phase(owner, actors):
    rivals = [j for j in actors if j != owner]
    passive = forced = 0
    for bits in product((0, 1), repeat=len(rivals)):
        mask = sum(b << j for j, b in zip(rivals, bits))
        weight = prod(x[j] if b else 1-x[j] for j, b in zip(rivals, bits))
        passive += weight * Z[mask][owner]
        forced += weight * Z[mask | (1 << owner)][owner]
    return passive, forced, prod(1-x[j] for j in rivals)


scheduled, quiet = [], []
for i in owners:
    p, q, h = period_phase(i, (0,))
    u, v, k = period_phase(i, (1,2,3))
    advantages = [(1-h*k)*q-p-h*u, (1-h*k)*v-u-k*p]
    scheduled.append(advantages[int(i != 0)])
    quiet.append(advantages[int(i == 0)])
F = sp.Matrix(scheduled)
a = dict(zip(x, (sp.Rational(n, 10**8) for n in (45680793,22187802,24501004,34745724))))
B = F.jacobian(x).subs(a).inv()
assert B.norm(sp.oo) < sp.Rational(83,1000) and (B*F.subs(a)).norm(sp.oo) < sp.Rational(41,10**10)
coefficient_norm = lambda g: sum(abs(v) for v in sp.Poly(g, x).coeffs())
assert max(coefficient_norm(f.diff(j,k)) for f in F for j in x for k in x) == 1457
assert max(sum(coefficient_norm(e.diff(j)) for j in x) for e in quiet) == 20404
assert all(100*e.subs(a) < -n for e,n in zip(quiet, (324,865,994,262)))
