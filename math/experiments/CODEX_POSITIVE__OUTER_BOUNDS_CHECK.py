"""Exact seven-box certificate for the pure3 outer return.

Run with Python and SymPy. All arithmetic is rational. This verifies the
polynomial bounds in the mathematical proof; it is not a game solver.
"""
from itertools import product
from sympy import Poly, Rational as R, binomial, diff, expand, symbols

L, a, b, T = symbols('L a b T')
Q = (35868*L**4*a*b - 7686*L**4*a + 26460*L**4*b**2
     - 1092*L**4*b - 981*L**4 - 25200*L**3*a*b + 645046*L**3*a
     - 33600*L**3*b**2 + 1542762*L**3*b - 458857*L**3
     - 961800*L**2*a - 662200*L**2*b - 1874690*L**2
     + 360000*L*a - 240000*L*b - 696500*L + 1500000)
f2 = -(108*L**3*a + 54*L**3*b + 27*L**3 + 2400*L**2*T*a
       + 1800*L**2*T*b + 300*L**2*T - 3600*L**2*a - 3600*L**2*b
       + 135*L**2 + 5700*L*T + 80000*T**2 - 100000*T)/100
N = -9*L*(1708*L**2*a + 854*L**2*b + 427*L**2 - 1200*L*a
          - 2000*L*b + 2135*L + 2000)
D = 100*(42*L**2*b - 9*L**2 + 5873*L - 4200)
AB = [(R(-7, 2), R(3, 2)), (R(-7, 3), R(1, 2))]
LAB = [(R(33, 50), R(7, 10))] + AB


def bernstein_bounds(expression, variables, box):
    ts = symbols('t:' + str(len(variables)))
    polynomial = Poly(expand(expression.subs({
        v: lo + (hi-lo)*t for v, t, (lo, hi) in zip(variables, ts, box)
    })), ts)
    degrees = [polynomial.degree(t) for t in ts]
    coefficients = []
    for k in product(*(range(n+1) for n in degrees)):
        value = R(0)
        for m, coefficient in polynomial.terms():
            if all(mi <= ki for mi, ki in zip(m, k)):
                factor = R(1)
                for ki, mi, di in zip(k, m, degrees):
                    factor *= binomial(ki, mi)/binomial(di, mi)
                value += coefficient*factor
        coefficients.append(value)
    return min(coefficients), max(coefficients)


checks = [
    ('Q lower', Q.subs(L, R(33, 50)), [a, b], AB, 1, R(7720523937, 125000)),
    ('Q upper', Q.subs(L, R(7, 10)), [a, b], AB, -1, R(-9337931, 200)),
    ('Q derivative', diff(Q, L), [L, a, b], LAB, -1,
     R(-38440944739, 12500)),
    ('f2 at 1', f2.subs(T, 1), [L, a, b], LAB, 1,
     R(11844461, 100000)),
    ('f2 at 5/4', f2.subs(T, R(5, 4)), [L, a, b], LAB, -1,
     R(-268792821, 6250000)),
    ('T lower', (N-D).subs(L, R(33, 50)), [a, b], AB, 1,
     R(193868991, 125000)),
    ('T upper', (N-R(5, 4)*D).subs(L, R(7, 10)), [a, b], AB, -1,
     R(-4917521, 500)),
]
for name, expression, variables, box, sign, expected in checks:
    low, high = bernstein_bounds(expression, variables, box)
    actual = low if sign == 1 else high
    assert actual == expected, (name, actual, expected)
    assert sign*actual > 0, (name, low, high)
print('PASS: seven exact Bernstein bounds; complete coefficient rectangle.')
