"""Exact certificate for the positive pair-premium bridge.

Run from the repository root:
  python math/experiments/SIGNED_COLLISION_PARAMETER_POSITIVE_CHECK.py

This checks rational polynomial claims in the companion note. It does not
numerically sample parameters, certify the probability argument, or use Lean.
"""

from fractions import Fraction

import sympy as s


t, w, E = s.symbols("t w E")
LO, HI = s.Rational(7, 2000), s.Rational(9, 2000)
y = (1 - t) / 25
z = 2 * (1 - t) / (2419 + 106 * t)
T1 = -100 * z - 100 * w + 211 * z * w
X = (2 * t + (74 - t) * w) / 25
T3 = -z * (100 - 101 * y)
x = (101 * z + 97 * w - 200 * z * w) / ((1 - z) * (1 - w))
E2 = (s.Rational(2, 25) + 4 * w - (3 - t) * w / 25) / ((1 - y) * (1 - w))
T0 = (
    3 * y - z + 3 * w - 14 * y * z - 4 * y * w - 8 * z * w
    + 13 * y * z * w + (1 - y) * (1 - z) * (1 - w) * E
)
survival = 2 / ((2 + X) * (1 - T1))
collision = -survival * T1 * X * (1 - t) / (2 * (101 - 100 * t))
p_collision = -survival * T1 * X * t / (101 - 100 * t)
pi1 = (p_collision + survival * X) / 2
pi2 = 100 * collision - survival * T1
C0 = s.cancel(3 * pi1 - pi2 - 12 * collision + survival * T0)
C3 = s.cancel(-2 * pi1 + pi2 - 6 * collision + survival * T3)
ell, base = s.diff(C0, E), C0.subs(E, 0)
K0 = -s.Rational(9, 2) + 6 * x + s.Rational(27, 2) * E2
alpha = s.cancel(K0 * ell + s.Rational(7, 4) * C3 - s.Rational(3, 4))
beta = s.cancel(
    K0 * base + (-s.Rational(15, 2) + 3 * x + s.Rational(27, 4) * E2) * C3
    + 3 * x + s.Rational(27, 4) * E2
)
E0 = s.cancel(-beta / alpha)
F1 = (9 + 6 * x - 9 * E) * C0 + (6 + 3 * x - 5 * E) * C3 + 3 * x - 3 * E
F2 = (6 - 6 * E2 - 4 * E) * C0 + (6 - 3 * E2 - 3 * E) * C3 - 3 * E2 - E
assert s.cancel(F1 - s.Rational(9, 4) * F2 - alpha * E - beta) == 0
assert s.cancel(alpha * E0 + beta) == 0


def bernstein(poly):
    """Tensor Bernstein coefficients after mapping the rectangle to [0,1]^2."""
    u, v = s.symbols("u v")
    poly = s.Poly(poly.subs({t: u, w: LO + (HI - LO) * v}), u, v)
    nt, nw = poly.degree_list()
    coeff = [[poly.coeff_monomial(u**i * v**j) for j in range(nw + 1)] for i in range(nt + 1)]
    return [
        [
            sum(
                coeff[k][h] * s.binomial(i, k) * s.binomial(j, h)
                / (s.binomial(nt, k) * s.binomial(nw, h))
                for k in range(i + 1) for h in range(j + 1)
            )
            for j in range(nw + 1)
        ]
        for i in range(nt + 1)
    ]


def split_curve(coeff):
    triangle = [coeff]
    while len(triangle[-1]) > 1:
        previous = triangle[-1]
        triangle.append([(a + b) / 2 for a, b in zip(previous, previous[1:])])
    return [row[0] for row in triangle], [row[-1] for row in reversed(triangle)]


def split_tensor(coeff, dimension):
    if dimension == 0:
        left, right = split_tensor([list(row) for row in zip(*coeff)], 1)
        return [list(row) for row in zip(*left)], [list(row) for row in zip(*right)]
    pairs = [split_curve(row) for row in coeff]
    return [pair[0] for pair in pairs], [pair[1] for pair in pairs]


def certify_polynomial(poly, sign):
    stack = [(bernstein(poly), 0)]
    leaves = max_depth = 0
    while stack:
        coeff, depth = stack.pop()
        signed = [sign * value for row in coeff for value in row]
        if min(signed) > 0:
            leaves += 1
            max_depth = max(max_depth, depth)
            continue
        assert max(signed) > 0 and depth < 16, "Strict sign certificate failed"
        left, right = split_tensor(coeff, depth % 2)
        stack.extend([(left, depth + 1), (right, depth + 1)])
    return leaves, max_depth


def certify_positive(name, expression):
    numerator, denominator = s.fraction(s.cancel(expression))
    midpoint = {t: s.Rational(1, 2), w: (LO + HI) / 2}
    sign = s.sign(denominator.subs(midpoint))
    assert sign in (-1, 1)
    num_check = certify_polynomial(numerator, sign)
    den_check = certify_polynomial(denominator, sign)
    print(f"{name}: exact positive; numerator {num_check}, denominator {den_check}")


checks = {
    "-alpha": -alpha,
    "E0>29/50": E0 - s.Rational(29, 50),
    "C0>1/4": C0.subs(E, E0) - s.Rational(1, 4),
    "C3>3/20": C3 - s.Rational(3, 20),
    "C3<1": 1 - C3,
    "T0>29/50": T0.subs(E, E0) - s.Rational(29, 50),
    "x>1/3": x - s.Rational(1, 3),
    "x<53/100": s.Rational(53, 100) - x,
    "E2>9/100": E2 - s.Rational(9, 100),
    "E2<11/100": s.Rational(11, 100) - E2,
    "L>0": -T1,
    "L<27/50": s.Rational(27, 50) + T1,
    "X>0": X,
    "X<1/10": s.Rational(1, 10) - X,
    "T3+L>1/3": T3 - T1 - s.Rational(1, 3),
}
for name, expression in checks.items():
    certify_positive(name, expression)

root_numerator = s.fraction(s.cancel(F2.subs(E, E0)))[0]
assert s.Poly(root_numerator, t, w).degree_list() == (11, 7)
for endpoint, sign in [(LO, -1), (HI, 1)]:
    poly = s.Poly(root_numerator.subs(w, endpoint), t)
    degree = poly.degree()
    coeff = [
        sum(poly.nth(k) * s.binomial(j, k) / s.binomial(degree, k) for k in range(j + 1))
        for j in range(degree + 1)
    ]
    assert all(sign * value > 0 for value in coeff)
    print(f"Root endpoint {endpoint}: all {len(coeff)} Bernstein coefficients have sign {sign}")

F = Fraction
quiet0 = F(29, 50) * F(1000, 1617) - F(27, 77) - 12 * F(27, 101000)
quiet3 = F(1000, 4851) - F(2, 21) - F(27, 1050)
assert quiet0 == F(197273, 40829250) > 0
assert quiet3 == F(20663, 242550) > 0
assert F(97, 100)**43 < F(3, 11) < F(1, 4) + 3 * F(9, 100) / (4 * F(53, 100))
print("All root, guard, and repair arithmetic checks passed exactly.")
