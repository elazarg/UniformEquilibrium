#!/usr/bin/env python3
"""Exact regression checks for REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md.

These verify finite algebra and boundary cases, not the universal theorems.
Requirements: Python 3, SymPy. Run: python VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py
No network, repository writes, floating-point optimizers, or Lean claims.
"""
from __future__ import annotations
import itertools
import json
import random
from fractions import Fraction as F
from math import prod
from typing import Sequence
import sympy as S


def test_reflection_identity() -> int:
    rng = random.Random(19092026)
    count = 0
    for n in (2, 3, 4, 5):
        for _ in range(40):
            mat = [[F(rng.randrange(-7, 8), 3) for _ in range(n)] for _ in range(n)]
            h = [[mat[i][j] + mat[j][i] for j in range(n)] for i in range(n)]
            g = [F(rng.randrange(-9, 10), 5) for _ in range(n)]
            a = [F(rng.randrange(-12, 13), 4) for _ in range(n)]
            x = [F(rng.randrange(-12, 13), 4) for _ in range(n)]
            y = [2 * x[i] - a[i] for i in range(n)]
            def p(z: Sequence[F]) -> F:
                return sum(g[i] * z[i] for i in range(n)) + F(1, 2) * sum(
                    h[i][j] * z[i] * z[j] for i in range(n) for j in range(n))
            gradient = [g[i] + sum(h[i][j] * x[j] for j in range(n)) for i in range(n)]
            assert p(y) - p(a) == 2 * sum(gradient[i] * (x[i] - a[i]) for i in range(n))
            count += 1
    return count


def test_reflection_box() -> int:
    rng = random.Random(271828)
    count = 0
    for n in (2, 3, 4, 5):
        for _ in range(50):
            s = [F(rng.randrange(11), 10) for _ in range(n)]
            a = [s[i] + F(rng.randrange(1, 11), 10) * (3 - s[i]) for i in range(n)]
            b = [max(ai, F(1)) for ai in a]
            x = [s[i] + F(rng.randrange(11), 10) * (b[i] - s[i]) for i in range(n)]
            # Force an actual lower-face point without changing another coordinate's bound.
            j = rng.randrange(n)
            x[j] = s[j]
            assert all(s[i] < a[i] <= b[i] <= 3 for i in range(n))
            assert all(s[i] <= x[i] <= b[i] for i in range(n))
            y = [2*x[i]-a[i] for i in range(n)]
            assert all(-3 <= yi <= 3 for yi in y)
            count += 1
    # Exact limiting corner and a top side strictly greater than the reward bound.
    a = [F(3), F(1, 2), F(2), F(1, 4)]
    s = [F(0)] * 4
    b = [max(ai, F(1)) for ai in a]
    x = [F(0), b[1], b[2], b[3]]
    assert [2*x[i]-a[i] for i in range(4)] == [F(-3), F(3, 2), F(2), F(7, 4)]
    return count + 1


def test_multiaffine_corner_formula() -> int:
    rng = random.Random(314159)
    n = 4
    z = S.symbols('z0:4')
    count = 0
    for _ in range(12):
        c = {mask: S.Rational(rng.randrange(1, 25), rng.randrange(1, 8))
             for mask in range(1, 1 << n)}
        c[0] = S.Integer(0)
        p = sum(c[mask] * prod((3-z[j])/6 if mask & (1 << j) else (3+z[j])/6
                               for j in range(n)) for mask in range(1 << n))
        i = min(range(n), key=lambda j: c[1 << j])
        si = S.Rational(rng.randrange(5), 4)
        t = (3-si)/6
        point = {z[j]: si if j == i else 3 for j in range(n)}
        assert S.simplify(p.subs(point) - t*c[1 << i]) == 0
        for j in range(n):
            if j == i:
                continue
            expected = (t*c[1 << i] - (1-t)*c[1 << j] - t*c[(1 << i) | (1 << j)])/6
            assert S.simplify(S.diff(p, z[j]).subs(point) - expected) == 0
            assert expected < 0
            count += 1
    return count


def root_values(reward: dict[int, list[F]], v: list[F], q: list[F]):
    n = len(q)
    payoff = [F(0)] * n
    quit = [F(0)] * n
    cont = [F(0)] * n
    for mask in range(1 << n):
        prob = prod(q[j] if mask & (1 << j) else 1-q[j] for j in range(n))
        for i in range(n):
            payoff[i] += prob * (reward[mask][i] if mask else v[i])
    for i in range(n):
        for mask in range(1 << n):
            if mask & (1 << i):
                continue
            prob = prod(q[j] if mask & (1 << j) else 1-q[j]
                        for j in range(n) if j != i)
            quit[i] += prob * reward[mask | (1 << i)][i]
            cont[i] += prob * (reward[mask][i] if mask else v[i])
    return payoff, quit, cont


def test_collision_adjusted_probes() -> int:
    rng = random.Random(161803)
    count = 0
    n = 4
    for _ in range(30):
        reward = {mask: [F(rng.randrange(-10, 11), 10) for _ in range(n)]
                  for mask in range(1, 1 << n)}
        s = [F(rng.randrange(11), 10) for _ in range(n)]
        for i in range(n):
            reward[1 << i][i] = s[i]
        for i in range(n):
            x = [s[j] + F(rng.randrange(5), 4)*(3-s[j]) for j in range(n)]
            x[i] = s[i]
            d = [F(0)] * n
            for j in range(n):
                if j != i and x[j] < 3:
                    d[j] = max(reward[(1 << i) | (1 << j)][j]-reward[1 << i][j], F(0))
            h = F(1, 100)
            for j in range(n):
                if d[j] > 0:
                    gap = 3-x[j]
                    h = min(h, gap/(2*(d[j]+gap)))
            v = [x[j]+h*d[j]/(1-h) for j in range(n)]
            q = [F(0)] * n
            q[i] = h
            payoff, quit, cont = root_values(reward, v, q)
            assert all(-3 <= vj <= 3 for vj in v)
            assert all(payoff[j] == (1-h)*v[j]+h*reward[1 << i][j] for j in range(n))
            assert quit[i] == cont[i] == s[i]
            assert all(cont[j] >= quit[j] for j in range(n) if j != i)
            assert all(max(quit[j], cont[j])-payoff[j] == 0 for j in range(n))
            count += 1
    return count


def test_third_derivative_kernel() -> int:
    t = S.symbols('t', real=True)
    count = 0
    for k in range(11):
        f = t**k
        lhs = (f.subs(t, 2)-f.subs(t, 0))/2-S.diff(f, t).subs(t, 1)
        d3 = S.diff(f, t, 3)
        rhs = (S.integrate(t**2*d3, (t, 0, 1))
               +S.integrate((2-t)**2*d3, (t, 1, 2)))/4
        assert S.simplify(lhs-rhs) == 0
        count += 1
    return count


def test_face_only_indefinite_quadratic() -> dict[str, str | int]:
    y = S.symbols('y0:4', nonnegative=True)
    g = S.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
                  [-1, -1, 0, 3], [-1, -1, 3, 0]])/4
    p = -4*sum(y)+64*(y[0]*y[1]+y[2]*y[3])+16*(y[0]+y[1])*(y[2]+y[3])
    for i in range(4):
        partner = i ^ 1
        other = [j for j in range(4) if j not in (i, partner)]
        t, u, v = y[partner], y[other[0]], y[other[1]]
        drift = sum(S.diff(p, y[j])*(y[j]-g[j, i]) for j in range(4)).subs(y[i], 0)
        assert S.expand(drift-(1+4*t+32*t*(u+v)+128*u*v)) == 0
    hessian = S.hessian(p, y)
    assert hessian.eigenvals() == {S.Integer(96): 1, S.Integer(32): 1, S.Integer(-64): 2}
    # Original annotation v in [-3,3]^4, own singleton s=1/4, y=v-s.
    top = p.subs({yi: S.Rational(11, 4) for yi in y})
    mixed = p.subs({y[j]: S.Rational(11, 4) if j % 2 == 0 else S.Rational(-13, 4)
                   for j in range(4)})
    assert mixed < top
    return {'face_identities': 4, 'top_value': str(top), 'mixed_corner_value': str(mixed),
            'hessian_eigenvalues': '96, 32, -64, -64'}


def run_checks() -> dict:
    return {
        'quadratic_reflection_identities': test_reflection_identity(),
        'reflected_box_cases': test_reflection_box(),
        'multiaffine_derivative_identities': test_multiaffine_corner_formula(),
        'exact_collision_adjusted_Nash_probes': test_collision_adjusted_probes(),
        'third_derivative_kernel_monomials': test_third_derivative_kernel(),
        'indefinite_face_only_fixture': test_face_only_indefinite_quadratic(),
        'scope': 'Exact finite regressions, not a universal proof or a Lean check.'
    }


if __name__ == '__main__':
    print(json.dumps(run_checks(), indent=2))
