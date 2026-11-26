"""Exact stationary exclusion at delta=1/8, epsilon=139/200.

Standard library only. Run from the repository root without -O.
The imported, hash-pinned periodic checker supplies the independently audited
raw payoff polynomials, dyadic intervals, automatic derivatives and a floating
inverse proposal. Floating values never decide exclusion.
The associated proof justifies discarding boxes with sum(q)<1/50000.
"""
if not __debug__:
    raise RuntimeError('Assertions are required; do not use -O.')
import hashlib
import importlib.util
import itertools
import time
from fractions import Fraction as F
from pathlib import Path

SOURCE = Path('math/experiments/CODEX_COORDINATOR__TWO_ROW_HIGH_PERIODIC.py')
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == (
    '5c02cd160f440388a6357e4d0b8756c36b6bffd403ed50c3412f420f178fe9eb')
spec = importlib.util.spec_from_file_location('two_row_certificate', SOURCE)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
DELTA, EPSILON = F(1, 8), F(139, 200)


def origin_audit():
    z = m.rewards(DELTA, EPSILON)
    assert len(z) == 60 and all(abs(x) <= 6 for x in z.values())
    gamma = [[F(0) if i == j else z[i, 1 << j] for j in range(4)]
             for i in range(4)]
    a = [row + [F(i == j) for j in range(4)]
         for i, row in enumerate(gamma)]
    for k in range(4):
        j = next(j for j in range(k, 4) if a[j][k])
        a[k], a[j] = a[j], a[k]
        pivot = a[k][k]
        a[k] = [x / pivot for x in a[k]]
        for i in range(4):
            if i != k:
                factor = a[i][k]
                a[i] = [x - factor*y for x, y in zip(a[i], a[k])]
    inv = [row[4:] for row in a]
    assert all(sum(gamma[i][k]*inv[k][j] for k in range(4)) == (i == j)
               for i in range(4) for j in range(4))
    assert all(x > F(1, 125) for row in inv for x in row)
    assert all(sum(row) < 5 for row in inv)
    assert all(sum(col) < 5 for col in zip(*inv))
    print('PASS EXACT ORIGIN CONSTANTS', flush=True)


def field(q):
    p, offer, h, _ = m.evaluate(q, [0]*4, DELTA, EPSILON)
    return [(1-h[i])*offer[i]-p[i] for i in range(4)]


def newton_excludes(status, box, q):
    free = [i for i, st in enumerate(status) if st == 2]
    if not free:
        return False
    jq = [m.Jet(x, [m.Iv(int(i == j)) for j in range(6)])
          for i, x in enumerate(q)]
    jf = field(jq)
    jac = [[jf[i].d[j] for j in free] for i in free]
    try:
        proposal = m.float_inverse(
            [[float(F(v.lo+v.hi, 2*m.D)) for v in row] for row in jac])
        c = [[F(x) for x in row] for row in proposal]
    except (AssertionError, ZeroDivisionError, ValueError, OverflowError):
        return False
    center = [(lo+hi)/2 for lo, hi in box]
    fc = field(center)
    for k, i in enumerate(free):
        image = m.Iv(center[i]-sum(c[k][v]*fc[j] for v, j in enumerate(free)))
        for l, j in enumerate(free):
            derivative = int(k == l)-sum(c[k][v]*jac[v][l] for v in range(len(free)))
            image += derivative*m.Iv.box(0, (box[j][1]-box[j][0])/2)
        if image.hi < m.Iv(box[i][0]).lo or image.lo > m.Iv(box[i][1]).hi:
            return True
    return False


def main():
    m.audit_horner()
    origin_audit()
    start = time.monotonic()
    stack = []
    for status in itertools.product((0, 1, 2), repeat=4):
        box = tuple((F(0), F(1)) if st == 2 else (F(st), F(st)) for st in status)
        stack.append((status, box))
    seen = signs = newton = origin = splits = 0
    while stack:
        assert time.monotonic()-start < 600 and seen < 1000000, 'Incomplete cover'
        status, box = stack.pop()
        seen += 1
        if sum(hi for lo, hi in box) < F(1, 50000):
            origin += 1
            continue
        q = [m.Iv.box((lo+hi)/2, (hi-lo)/2) for lo, hi in box]
        values = field(q)
        if any((st == 2 and not values[i].lo <= 0 <= values[i].hi)
               or (st == 0 and values[i].lo > 0)
               or (st == 1 and values[i].hi < 0) for i, st in enumerate(status)):
            signs += 1
            continue
        if newton_excludes(status, box, q):
            newton += 1
            continue
        k = max(range(4), key=lambda i: box[i][1]-box[i][0])
        lo, hi = box[k]
        assert hi > lo, ('Unexcluded pure profile', status)
        mid = (lo+hi)/2
        left, right = list(box), list(box)
        left[k], right[k] = (lo, mid), (mid, hi)
        stack.extend([(status, tuple(right)), (status, tuple(left))])
        splits += 1
    assert signs+newton+origin-splits == 81
    print('PASS COMPLETE STATIONARY EXCLUSION', 'boxes', seen, 'sign', signs,
          'Newton', newton, 'origin', origin, 'splits', splits,
          'seconds', time.monotonic()-start, flush=True)


if __name__ == '__main__':
    main()
