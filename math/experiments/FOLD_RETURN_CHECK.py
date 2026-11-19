"""Verify the finite inequalities for the nonperiodic matched saddle-node return.

All intervals use signed integers at scale 2**210 and outward rounding. The
Sturm isolation of the algebraic equilibrium is given in the accompanying
sharp two-date theorem. Run with Python and SymPy.
"""
from fractions import Fraction as Q
from itertools import permutations, combinations
from multiprocessing import Pool
import sympy as sy
if not __debug__:
    raise RuntimeError('Run without -O so every certificate is checked')
D = 1 << 210

class I:
    """A rational interval with integer endpoints on the fixed dyadic lattice."""

    def __init__(s, l, r):
        s.l = l
        s.r = r

    @classmethod
    def c(cls, x):
        x = Q(x)
        return cls(D * x.numerator // x.denominator, -(-D * x.numerator // x.denominator))

    def __neg__(s):
        return I(-s.r, -s.l)

    def __add__(s, t):
        if not isinstance(t, I):
            t = I.c(t)
        return I(s.l + t.l, s.r + t.r)
    __radd__ = __add__

    def __sub__(s, t):
        return s + -t

    def __rsub__(s, t):
        return -s + t

    def __mul__(s, t):
        if not isinstance(t, I):
            t = I.c(t)
        v = [s.l * t.l, s.l * t.r, s.r * t.l, s.r * t.r]
        return I(min(v) // D, -(-max(v) // D))
    __rmul__ = __mul__

    def __truediv__(s, t):
        if not isinstance(t, I):
            t = I.c(t)
        if t.l <= 0 <= t.r:
            raise ZeroDivisionError
        return s * I(D * D // t.r, -(-D * D // t.l))

    def __rtruediv__(s, t):
        return I.c(t) / s

    def abs(s):
        return Q(max(abs(s.r), abs(s.l)), D)

    def expand(s, r):
        return s + I(-I.c(r).r, I.c(r).r)
b = sy.symbols('b')
a = b * (8 * b * b - 13 * b + 6) / ((1 - b) ** 2 * (8 * b + 3))
H = sy.factor((a + b - a * (sy.Rational(1, 3) / (1 - a) + sy.Rational(8, 3) * (1 - a) * (1 - b))) / (a * b) - 2)
dH = sy.Poly(sy.fraction(sy.factor(sy.diff(H, b)))[0], b).all_coeffs()
lo, hi = (Q(53672, 100000), Q(53673, 100000))
dpoly = sy.Poly.from_list(dH, gens=b)
assert dpoly.count_roots(lo, hi) == 1 and dpoly.eval(lo) > 0 and (dpoly.eval(hi) < 0)
# The derivative polynomial identifies the isolated center hazard.
for _ in range(130):
    x = (lo + hi) / 2
    v = Q(0)
    for z in dH:
        v = x * v + int(z)
    if v > 0:
        lo = x
    else:
        hi = x
b = I(I.c(lo).l, I.c(hi).r)
a = b * (8 * b * b - 13 * b + 6) / ((1 - b) * (1 - b) * (8 * b + 3))
c = I.c(Q(1, 3))
M = 8 * c
t = (a + b - a * (c / (1 - a) + M * (1 - a) * (1 - b))) / (a * b) - 2
fixed = [M * b, M * a, -c * b / (1 - b), -c * a / (1 - a)]

def sq(x):
    return x * x

def det(p):
    n = len(p)
    s = I.c(0)
    for per in permutations(range(n)):
        sign = (-1) ** sum((i > j for k, i in enumerate(per) for j in per[k + 1:]))
        v = I.c(sign)
        for i, j in enumerate(per):
            v = v * p[i][j]
        s = s + v
    return s

def inverse(p):
    den = det(p)
    n = len(p)
    return [[det([[v for jj, v in enumerate(row) if jj != i] for ii, row in enumerate(p) if ii != j]) * (-1) ** (i + j) / den for j in range(n)] for i in range(n)]

def iv(x):
    return I.c(Q(str(x)))

def mv(p, x):
    return [sum((z * v for z, v in zip(row, x)), iv(0)) for row in p]
N = 8 * b * b - 13 * b + 6
L = (1 - b) * (1 - b) * (8 * b + 3)
ab = ((N + b * (16 * b - 13)) * L - b * N * (-2 * (1 - b) * (8 * b + 3) + 8 * sq(1 - b))) / sq(L)
u = [M, M * ab, -c / sq(1 - b), -c * ab / sq(1 - a)]
u = [v * iv('0.6912') / M for v in u]
# The first chart column is the exact branch tangent.
columns = [[-7856, 5838, 870], [-5647, -7337, 0], [2243, 441, -2464], [1165, -66, 2248]]
P = [[v] + [I.c(Q(j, 10000)) for j in row] for v, row in zip(u, columns)]
Pi = inverse(P)

def matmul(A, B):
    return [[sum((v * w for v, w in zip(row, col)), I.c(0)) for col in zip(*B)] for row in A]

def mid(i):
    m = (i.l + i.r) // 2
    return I(m, m)

def wid(i):
    return Q((i.r - i.l + 1) // 2, D)

def enlarge(x, r):
    return [v.expand(s) for v, s in zip(x, r)]

def project(v):
    return mv(Pi, v)

def deriv(V):
    """Jacobian of one complete matched date, in the center and three stable coordinates."""
    X = V[:2]
    Y = V[2:]
    p = [y / (y - c) for y in Y]
    f = [-c / sq(y - c) for y in Y]
    C = (1 - p[0]) * (1 - p[1])
    J = [[iv(0) for _ in range(4)] for _ in range(4)]
    for i in [0, 1]:
        J[i][i + 2] = M * f[i]
        J[i + 2][i] = C
        for j in [0, 1]:
            J[i + 2][j + 2] = f[j] * (-(1 - p[1 - j]) * (1 + X[i]) + (1 + (-1, t)[i]) * p[1 - j])
    return matmul(Pi, matmul(J, P))

def d2u(V):
    """Half of the map’s second directional derivative along its center column."""
    X = V[:2]
    Y = V[2:]
    p = [y / (y - c) for y in Y]
    f = [-c / sq(y - c) for y in Y]
    fp = [c / ((y - c) * sq(y - c)) for y in Y]
    dp = [f[j] * u[j + 2] for j in (0, 1)]
    ddp = [fp[j] * sq(u[j + 2]) for j in (0, 1)]
    dC = -dp[0] * (1 - p[1]) - dp[1] * (1 - p[0])
    ddC = -ddp[0] * (1 - p[1]) - ddp[1] * (1 - p[0]) + dp[0] * dp[1]
    ddD = ddp[0] * p[1] + ddp[1] * p[0] + dp[0] * dp[1]
    V = [M * ddp[0], M * ddp[1]] + [(1 + X[i]) * ddC + u[i] * dC + (1 + (-1, t)[i]) * ddD for i in (0, 1)]
    return mv(Pi, V)

def step(x, r):
    """One outward enclosure, using the mean-value form in the adapted coordinates."""
    physical = [sum((a.abs() * s for a, s in zip(row, r))) for row in P]
    h = x[:2]
    Y = x[2:]
    p = [y / (y - c) for y in Y]
    C = (1 - p[0]) * (1 - p[1])
    joint = p[0] * p[1]
    out = [M * p[0], M * p[1], -(1 - C) + C * h[0], -(1 - C) + (1 + t) * joint + C * h[1]]
    N = deriv(enlarge(x, physical))
    noise = [sum((a.abs() * wid(v) for a, v in zip(row, out))) for row in Pi]
    rad = [sum((z.abs() * s for z, s in zip(row, r))) + d for row, d in zip(N, noise)]
    rad = [Q(-(-D * u.numerator // u.denominator), D) for u in rad]
    return ([mid(z) for z in out], rad)

def orbit(y, n, tol):
    """Propagate a whole reset rectangle under a fixed starting solo rate."""
    y = I.c(y)
    r0 = I.c(Q('1.29507')).expand(tol)
    s0 = I.c(Q('.06628')).expand(tol)
    V = [3 * y + (1 - y) * s0, I.c(0), -y, (1 - y) * r0 - y]
    x = list(map(mid, V))
    r = [sum((z.abs() * wid(v) for z, v in zip(row, V))) for row in Pi]
    for _ in range(n):
        x, r = step(x, r)
    return [z.expand(v) for z, v in zip(project([a - b for a, b in zip(x, fixed)]), r)]

def guards(V, phase=None, floor=0, q_floor=0):
    p = [y / (y - c) for y in V[2:]]
    C = (1 - p[0]) * (1 - p[1])
    if not all((q.l > D * q_floor and q.r < D * (1 - q_floor) for q in p)):
        return False
    spread = p[0] - p[1]
    if phase is None:
        penalty = spread.abs() / 10
        return all(((C * v).l > D * (floor + penalty) for v in V[:2]))
    if phase % 2:
        spread = -spread
    return (C * V[0] - spread * Q(1, 10)).l > D * floor and (C * V[1] + spread * Q(1, 10)).l > D * floor

def local_checks():
    """Prove cone invariance, drift, and strip invariance at the critical table."""
    rad = Q(1, 1000)
    V = enlarge(fixed, [rad * sum((q.abs() for q in row)) for row in P])
    J = deriv(V)
    assert J[0][0].l > D * Q('.968') and sum((q.abs() for q in J[0][1:])) < Q('.049')
    assert max((row[0].abs() for row in J[1:])) < Q('.031')
    assert max((sum((q.abs() for q in row[1:])) for row in J[1:])) < Q('.781')
    assert guards(V)
    p = [y / (y - c) for y in V[2:]]
    par = project([iv(0), iv(0), iv(0), p[0] * p[1]])
    assert par[0].l > D * Q('-.77') and par[0].r < D * Q('-.75') and (max((v.abs() for v in par[1:])) < Q('.67'))
    h = d2u(enlarge(fixed, [rad * q.abs() for q in u]))
    assert h[0].l > D * Q('-.957') and h[0].r < D * Q('-.935') and (max((z.abs() for z in h[1:])) < Q('.419'))
    high_center = Q(-1)
    low_center = Q(0)
    stable = Q(0)
    for k in range(50):
        lo = Q(k, 2500)
        hi = Q(k + 1, 2500)
        z = I.c((lo + hi) / 2).expand((hi - lo) / 2)
        V = [v + w * z for v, w in zip(fixed, u)]
        h = d2u(V)
        high_center = max(high_center, Q(h[0].r, D))
        low_center = min(low_center, Q(h[0].l, D))
        stable = max(stable, max((v.abs() for v in h[1:])))
        V = enlarge(V, [4 * hi * hi * sum((q.abs() for q in row[1:])) for row in P])
        J = deriv(V)
        es = sum((q.abs() for q in J[0][1:]))
        ss = max((sum((q.abs() for q in row[1:])) for row in J[1:]))
        upper = -low_center + 4 * es
        assert -high_center - 4 * es > Q('.66') and 1 - upper * hi > 0
        assert stable + 4 * ss < 4 * (1 - upper * hi) ** 2 and guards(V)


def take(l, h, k=75):
    """Enclose 75 physical dates, retaining the shared parameter at the reset."""
    y0 = (l + h) / 2
    dy = (h - l) / 2
    dr = ds = Q(1, 100000)
    s0 = Q('.06628')
    r0 = Q('1.29507')
    x0 = [iv(3 * y0 + (1 - y0) * s0), iv(0), iv(-y0), iv((1 - y0) * r0 - y0)]
    cols = [[3 - s0, 0, -1, -1 - r0], [0, 0, 0, 1 - y0], [1 - y0, 0, 0, 0]]
    ex = [project([iv(z) for z in col]) for col in cols]
    x = [mid(z) for z in x0]
    R = [sum((z.abs() * q for z, q in zip([e[i] for e in ex], (dy, dr, ds)))) + sum((z.abs() * wid(v) for z, v in zip(row, x0))) + (row[3].abs() + row[0].abs()) * dy * dr for i, row in enumerate(Pi)]
    try:
        for n in range(k):
            V = enlarge(x, [sum((z.abs() * s for z, s in zip(row, R))) for row in P])
            p = [y / (y - c) for y in V[2:]]
            C = (1 - p[0]) * (1 - p[1])
            direction = p[0] - p[1]
            if n % 2:
                direction = -direction
            g = [C * V[0] - direction * Q(1, 10), C * V[1] + direction * Q(1, 10)]
            if any((z.l <= 0 or z.r >= D for z in p)) or min((v.l for v in g)) <= 0:
                return False
            x, R = step(x, R)
        out = [z.expand(s) for z, s in zip(project([a - b for a, b in zip(x, fixed)]), R)]
        u0 = Q(out[0].l, D)
        return 0 < u0 and out[0].r * 50 < D and (max((z.abs() for z in out[1:])) < 4 * u0 * u0)
    except ZeroDivisionError:
        return False

def tile(B):
    """Cover a closed interval of free solo hazards by certified entrance blocks."""
    l, h = B
    if take(l, h):
        return 1
    if h - l < Q(1, 2 ** 20):
        raise ArithmeticError('unverified entrance')
    m = (l + h) / 2
    return tile((l, m)) + tile((m, h))
UC = Q(-141216463603, 200000000000000)
ZR = Q(21, 10 ** 7)
RR = Q(4, 10 ** 8)

def exit_transfer(center, width, stable, tangents, check_guards):
    """Enclose 1500 joint dates and optionally transport the tangent cone and the exterior square."""
    initial = [v + w * I.c(center) for v, w in zip(fixed, u)]
    x = list(map(mid, initial))
    noise = [sum((a.abs() * wid(v) for a, v in zip(row, initial))) for row in Pi]
    radii = [r + d for r, d in zip([width, stable, stable, stable], noise)]
    pairs = list(combinations(range(4), 2))
    wedge = Q(1)
    speed = Q(1)
    tangent = [iv(1)] + [iv(0).expand(Q(1, 4)) for _ in range(3)]
    for k in range(1500):
        V = enlarge(x, [sum((a.abs() * r for a, r in zip(row, radii))) for row in P])
        if check_guards and (not guards(V, None, Q('.19'), Q('.20'))):
            raise ArithmeticError('infeasible exit step')
        N = deriv(V)
        if tangents:
            norm = max((sum(((N[i][a] * N[j][b] - N[i][b] * N[j][a]).abs() for a, b in pairs)) for i, j in pairs))
            w = wedge * norm
            wedge = Q(-(-D * w.numerator // w.denominator), D)
            v = mv(N, tangent)
            if v[0].l <= 0:
                raise ArithmeticError('lost transverse cone')
            w = speed * Q(v[0].l, D)
            speed = Q(D * w.numerator // w.denominator, D)
            tangent = [iv(1)] + [s / v[0] for s in v[1:]]
        ps = [y / (y - c) for y in x[2:]]
        C = (1 - ps[0]) * (1 - ps[1])
        joint = ps[0] * ps[1]
        out = [M * ps[0], M * ps[1], -(1 - C) + C * x[0], -(1 - C) + (1 + t) * joint + C * x[1]]
        ns = [sum((a.abs() * wid(v) for a, v in zip(row, out))) for row in Pi]
        rs = [sum((a.abs() * r for a, r in zip(row, radii))) + d for row, d in zip(N, ns)]
        radii = [Q(-(-D * w.numerator // w.denominator), D) for w in rs]
        x = list(map(mid, out))
    if tangents:
        assert wedge < Q(1, 10 ** 20) and speed > 1 and (mv(P, tangent)[2].r < -Q('.01') * D)
    return enlarge(x, [sum((a.abs() * r for a, r in zip(row, radii))) for row in P])

def exit_tile(k):
    rad = RR / 32
    center = UC - rad * (31 - 2 * k)
    exit_transfer(center, rad, ZR, True, True)
    return k

def fixed_checks():
    """Enclose the zero section, the reset values and the two-date phase lead."""
    upper = exit_transfer(UC - RR, 0, ZR, False, False)
    lower = exit_transfer(UC + RR, 0, ZR, False, False)
    assert upper[2].l > Q('.013') * D and lower[2].r < Q('-.014') * D
    a = Q(12, 10 ** 14)
    b = Q(17, 10 ** 14)
    assert exit_transfer(UC + a, 0, 0, False, False)[2].l > 0
    assert exit_transfer(UC + b, 0, 0, False, False)[2].r < 0
    V = exit_transfer(UC + (a + b) / 2, (b - a) / 2, 0, False, False)
    x = V[1] / (1 + V[1])
    r = 3 * x + (1 - x) * V[3]
    s = (1 - x) * V[0] - x
    assert r.l > D * Q('1.29506724') and r.r < D * Q('1.29506778')
    assert s.l > D * Q('.06627961') and s.r < D * Q('.06628006')
    assert x.l > D * Q('.43382544') and x.r < D * Q('.43382561')
    assert V[3].l > D * Q('-.0114') and V[3].r < D * Q('-.0112')
    low = orbit(Q('.57'), 1502, Q(1, 100000))
    high = orbit(Q('.80'), 1500, Q(1, 100000))
    difference = [a - b for a, b in zip(low, high)]
    assert difference[0].l > D * Q('0.000000795') and difference[0].r < D * Q('0.000000800')
    assert max((x.abs() for x in difference[1:])) < Q('0.00000000091')
    assert low[0].l > 0 and high[0].l > 0 and (max((x.abs() for x in low + high)) < Q('.000704'))
if __name__ == '__main__':
    local_checks()
    print('Verified the cone and invariant strips.', flush=True)
    with Pool(4) as pool:
        edges = [Q(57 + k, 100) for k in range(24)]
        counts = pool.map(tile, zip(edges, edges[1:]))
        print(f'Verified {sum(counts)} entrance intervals.', flush=True)
        assert set(pool.map(exit_tile, range(32))) == set(range(32))
        print('Verified 32 transverse exit tiles.', flush=True)
    fixed_checks()
    print('Verified the relative entrance phase and strict reinjection.', flush=True)
