"""Exact rational certificate for the literal unequal-high paired table.

No search or floating-point assertion occurs in this certificate. Reuses
Ival and fraction_matrix_inverse from the fully inspected repository
certifier, importing it without invoking its experiment main. Writes no
files. Run with PYTHONDONTWRITEBYTECODE=1.
"""

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PATH = Path(__file__).resolve().parents[2]/'Experiments/certsearch/krawczyk_cycle_certifier.py'
SPEC = importlib.util.spec_from_file_location('rational_interval_tools', PATH)
TOOLS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TOOLS)
Ival = TOOLS.Ival

ROWS = {
    0: (0, 0, 0, 0),
    1: (1, 4, 0, 0), 2: (4, 1, 0, 0),
    4: (0, 0, 1, 4), 8: (0, 0, 4, 1),
    3: (2, 2, 1, 1), 5: (Fr(8, 5), 1, 1, 0),
    9: (1, 0, 1, 2), 6: (0, 1, Fr(8, 5), 1),
    10: (1, 2, 0, 1), 12: (1, 1, 2, 2),
    7: (1, 0, 0, 0), 11: (0, 1, 0, 0),
    13: (0, 0, 0, 1), 14: (0, 0, 1, 0),
    15: (-1, -1, -1, -1),
}
ACTIVE = ((0, 0), (0, 2), (0, 3),
          (1, 0), (1, 1), (1, 2),
          (2, 0), (2, 1), (2, 3))
CENTER = tuple(map(Fr, (
    '.244039794253', '.112592757902', '.078794657233',
    '.015262871970', '.215678462758', '.243253107233',
    '.091437222715', '.100423595701', '.237451230261')))
RADIUS = Fr(1, 10**6)
DIM = len(ACTIVE)


class Jet:
    """Forward first derivatives, each enclosed by a rational interval."""
    def __init__(self, value, derivative=None):
        self.value = value if isinstance(value, Ival) else Ival(value)
        self.derivative = derivative if derivative is not None else [Ival(0)]*DIM

    @staticmethod
    def cast(x):
        return x if isinstance(x, Jet) else Jet(x)

    def __add__(self, other):
        y = Jet.cast(other)
        return Jet(self.value+y.value, [a+b for a, b in zip(self.derivative, y.derivative)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, [-a for a in self.derivative])

    def __sub__(self, other):
        return self + (-Jet.cast(other))

    def __rsub__(self, other):
        return Jet.cast(other) + (-self)

    def __mul__(self, other):
        y = Jet.cast(other)
        return Jet(self.value*y.value,
                   [a*y.value+self.value*b for a, b in zip(self.derivative, y.derivative)])

    __rmul__ = __mul__


def product(xs):
    p = Jet(1)
    for x in xs:
        p = p*x
    return p


def evaluate(box):
    q = [[Jet(0) for _ in range(4)] for _ in range(3)]
    for j, (phase, owner) in enumerate(ACTIVE):
        derivative = [Ival(int(j == k)) for k in range(DIM)]
        q[phase][owner] = Jet(box[j], derivative)
    G = []; survival = []; Q = []; H = []; deleted = []
    for row in q:
        probs = [product(row[j] if mask & (1 << j) else 1-row[j]
                         for j in range(4)) for mask in range(16)]
        G.append([sum((probs[mask]*ROWS[mask][i] for mask in range(1, 16)), Jet(0))
                  for i in range(4)])
        survival.append(probs[0])
        qr = []; hr = []; dr = []
        for i in range(4):
            masks = [mask for mask in range(16) if not mask & (1 << i)]
            pp = [product(row[j] if mask & (1 << j) else 1-row[j]
                          for j in range(4) if j != i) for mask in masks]
            qr.append(sum((prob*ROWS[mask | (1 << i)][i]
                           for mask, prob in zip(masks, pp)), Jet(0)))
            hr.append(sum((prob*ROWS[mask][i]
                           for mask, prob in zip(masks, pp)), Jet(0)))
            dr.append(pp[0])
        Q.append(qr); H.append(hr); deleted.append(dr)
    denominator = 1-product(survival)
    numerators = [[G[t][i]+survival[t]*G[(t+1) % 3][i]
                   +survival[t]*survival[(t+1) % 3]*G[(t+2) % 3][i]
                   for i in range(4)] for t in range(3)]
    gaps = [[denominator*(Q[t][i]-H[t][i])
             -deleted[t][i]*numerators[(t+1) % 3][i]
             for i in range(4)] for t in range(3)]
    active = [gaps[t][i] for t, i in ACTIVE]
    return active, gaps, denominator, numerators, deleted


def norm_interval(x):
    return max(abs(x.lo), abs(x.hi))


def certificate():
    center_box = [Ival(x) for x in CENTER]
    box = [Ival(x-RADIUS, x+RADIUS) for x in CENTER]
    assert all(Fr(1, 100) < x.lo < x.hi < Fr(1, 4) for x in box)
    active_center = evaluate(center_box)[0]
    residual = [x.value.to_fraction() for x in active_center]
    jac_center = [[a.to_fraction() for a in x.derivative] for x in active_center]
    inverse = TOOLS.fraction_matrix_inverse(jac_center)
    active_box, all_gaps, den, numerators, deleted = evaluate(box)
    jac_box = [x.derivative for x in active_box]
    correction = [sum((inverse[i][j]*residual[j] for j in range(DIM)), Fr(0))
                  for i in range(DIM)]
    err = [[Ival(int(i == j))-sum((jac_box[k][j]*inverse[i][k]
                                 for k in range(DIM)), Ival(0))
            for j in range(DIM)] for i in range(DIM)]
    lipschitz = max(sum((norm_interval(x) for x in row), Fr(0)) for row in err)
    displacement = max(abs(x) for x in correction)
    assert displacement < Fr(1, 10**9)
    assert lipschitz < Fr(1, 100)
    assert displacement+lipschitz*RADIUS < RADIUS/50
    assert Fr(7, 10) < den.value.lo < den.value.hi < Fr(4, 5)
    quiet = []
    for t in range(3):
        for i in range(4):
            if (t, i) not in ACTIVE:
                gap = all_gaps[t][i].value
                assert gap.hi < -Fr(1, 6)
                quiet.append((t, i, gap))
    assert all(d.value.hi < Fr(5, 6) for row in deleted for d in row)
    values = [[a.value/den.value for a in row] for row in numerators]
    assert all(1 < v.lo < v.hi < Fr(3, 2) for row in values for v in row)
    print('EXACT CERTIFICATE PASSED')
    print('||J(center)^(-1) F(center)||_infinity < 1/10^9')
    print('||Id-J(center)^(-1) J(box)||_infinity < 1/100')
    print('Newton image displacement < radius/50, radius=1/10^6')
    print('7/10 < actual absorption denominator < 4/5')
    print('Every one-row deleted survival < 5/6')
    print('All twelve cyclic values in (1,3/2)')
    print('DECIMAL LOCATORS ONLY', float(displacement), float(lipschitz))
    for t, i, gap in quiet:
        print('QUIET CLEARED GAP', (t, i), '< -1/6;', float(gap.lo), float(gap.hi))
    for t, row in enumerate(values):
        print('VALUE LOCATORS', t, [(float(v.lo), float(v.hi)) for v in row])
    return box, inverse


if __name__ == '__main__':
    certificate()
