"""Exact rational certificate for the two expanding native equilibrium clocks."""
from itertools import combinations, permutations

import sympy as sp

players = tuple(range(4))
gamma = sp.Matrix([[0, -2, 3, -1], [-1, 0, -1, 3], [3, -1, 0, -1], [-1, 3, -1, 0]])
K = sp.Matrix([[0, 3, sp.Rational(5, 2), -2], [-sp.Rational(1, 5000), 0, 2, sp.Rational(1, 2)],
               [2, -2, 0, 6], [3, 10, -sp.Rational(1, 2), 0]])
symbol = sp.symbols("t")


def product_margins(word):
    prefix = sp.eye(4)
    margins = [sp.eye(4)]
    for support in word:
        outside = [i for i in players if i not in support]
        active = -K.extract(support, support).inv() * gamma.extract(support, players)
        increments = sp.zeros(4)
        for k, i in enumerate(support):
            increments[i, :] = active[k, :]
        quiet = (gamma + K * increments).extract(outside, players)
        margins.append(active.col_join(quiet) * prefix)
        prefix = (sp.eye(4) + increments) * prefix
    return prefix, sp.Matrix.vstack(*margins)


def enclosure(polynomial, lo, hi):
    lower = upper = 0
    for coefficient in sp.Poly(polynomial, symbol).all_coeffs():
        products = [a * b for a in (lower, upper) for b in (lo, hi)]
        lower, upper = min(products) + coefficient, max(products) + coefficient
    return lower, upper


word = [(0, 1)] + [(1, 2)]*5 + [(1, 2, 3)]*8 + [(0, 1, 3)] + [(0, 3)]*9 + [(0, 1, 3)]
matrix, margins = product_margins(word)
characteristic = matrix.charpoly(symbol).as_poly()
endpoints = [-1, 0, 1, 62855, 62856, 1169838, 1169839]
assert [sp.sign(characteristic.eval(t)) for t in endpoints] == [1, -1, 1, 1, -1, -1, 1]
coeff = margins * (symbol * sp.eye(4) - matrix).adjugate()[:, 0]
assert len(coeff) == 104
for lo, hi in [(62855, 62856), (1169838, 1169839)]:
    assert all(enclosure(p, lo, hi)[1] < 0 for p in coeff)

pairs = [[(0, j), tuple(i for i in players if i not in (0,j))] for j in (1,2,3)]
mixed = [[(p[2],p[3]), (p[0],p[2]), (p[0],p[1],p[3])] for p in permutations(players)]
for family, expected in [(pairs, 0), (mixed, 16)]:
    roots = 0
    for supports in family:
        matrix, margins = product_margins(supports)
        poly = matrix.charpoly(symbol).as_poly()
        assert poly.eval(1) != 0
        columns = margins[4:, :] * (symbol * sp.eye(4) - matrix).adjugate()
        for (lo, hi), multiplicity in poly.intervals(eps=sp.Rational(1, 10**30)):
            if hi <= 1:
                continue
            assert lo > 1 and multiplicity == 1
            roots += 1
            for col in range(4):
                signs = [enclosure(p, lo, hi) for p in columns[:, col]]
                if any(l > 0 for l, h in signs) and any(h < 0 for l, h in signs):
                    break
            else:
                raise ValueError("Expanding mode was not excluded")
    assert roots == expected
print("Two expanding eigenrays verified. Earlier tests reject 0 and 16 expanding modes.")
