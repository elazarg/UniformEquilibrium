"""Exact local handoff failure on (a,a,2,2), separate from frozen proof.

Imports the frozen literal evaluator read-only; changes its DIM and table
only in this process to differentiate jointly in nine rates and raw a.
No numerical root enumeration or global branch assertion. Writes nothing.
"""

from fractions import Fraction as Fr
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PATH = Path(__file__).with_name('CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_CERTIFICATE.py')
SPEC = importlib.util.spec_from_file_location('frozen_polynomial_evaluator', PATH)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
M.DIM = 10
I = M.Ival
COLS = [0, 1, 2, 9, 4, 5, 6, 7, 8]
KEEP = [0, 1, 2, 4, 5, 6, 7, 8]
CENTER = list(map(Fr, (
    '.242380904838369', '.117097521503689', '.066981662274761',
    '1.734302259292673', '.208873697214118', '.224194672194819',
    '.094482875251960', '.095010892632442', '.239817592202553')))
RADIUS = Fr(1, 10**6)


def evaluate(box):
    raw_a = M.Jet(box[3], [I(int(k == 9)) for k in range(10)])
    M.ROWS[5] = (raw_a, 1, 1, 0)
    M.ROWS[6] = (0, 1, raw_a, 1)
    rates = list(box); rates[3] = I(0)
    return M.evaluate(rates)


def inverse_at_point(jac):
    return M.TOOLS.fraction_matrix_inverse([[x.to_fraction() for x in row] for row in jac])


def multiply(a, b):
    return [[sum((b[k][j]*a[i][k] for k in range(len(b))), I(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def norm_error(inverse, jac):
    ij = multiply(inverse, jac)
    err = [[I(int(i == j))-ij[i][j] for j in range(len(ij))] for i in range(len(ij))]
    return max(sum((M.norm_interval(x) for x in row), Fr(0)) for row in err)


def derivative_box(j0, jx, f0, fx):
    """Enclose every solution of J y = -f on the supplied small box."""
    inv = inverse_at_point(j0)
    center = [-sum((inv[i][j]*f0[j].to_fraction() for j in range(len(inv))), Fr(0))
              for i in range(len(inv))]
    residual = [-fx[i]-sum((jx[i][j]*center[j] for j in range(len(inv))), I(0))
                for i in range(len(inv))]
    norm = norm_error(inv, jx)
    assert norm < Fr(1, 100)
    bill = max(M.norm_interval(sum((residual[j]*inv[i][j]
                                   for j in range(len(inv))), I(0))) for i in range(len(inv)))
    error = bill/(1-norm)
    return [I(y-error, y+error) for y in center]


def four_phase_eval(box, raw):
    """The existing high-cycle equations, not an invented period grammar."""
    b = [M.Jet(x, [I(int(i == j)) for i in range(10)]) for j, x in enumerate(box)]
    d = [M.Jet(raw-1), M.Jet(raw-1), M.Jet(1), M.Jet(1)]

    def reciprocal(x):
        value = I(1)/x.value
        return M.Jet(value, [-g*value*value for g in x.derivative])

    xx = [1+d[j]*(1-b[(j+1) % 4]) for j in range(4)]
    aa = [reciprocal(xx[(j+1) % 4]) for j in range(4)]
    z2 = [(1-aa[(j+2) % 4])*(1+3*b[(j+3) % 4])+aa[(j+2) % 4]*b[(j+3) % 4]
          for j in range(4)]
    z1 = [4*aa[(j+1) % 4]*(1-b[(j+2) % 4])+aa[(j+1) % 4]*b[(j+2) % 4]*z2[j]
          for j in range(4)]
    residual = [xx[j]-b[(j+1) % 4]*z1[j] for j in range(4)]
    t1 = [aa[(j+1) % 4]*b[(j+2) % 4]+2*aa[(j+1) % 4]*(1-b[(j+2) % 4])
          +(1+d[j])*(1-aa[(j+1) % 4])*b[(j+2) % 4]
          +(1-aa[(j+1) % 4])*(1-b[(j+2) % 4]) for j in range(4)]
    quiet1 = [xx[j]*reciprocal(b[(j+1) % 4])-t1[j] for j in range(4)]
    quiet2sign = [1+b[(j+3) % 4]-2*aa[(j+2) % 4] for j in range(4)]
    return residual, quiet1, quiet2sign


def fixed_band_test():
    """One failed uniform box test; deliberately no subdivision or shrinking."""
    center = list(map(Fr, ('.756797160998065', '.788350570071128',
                          '.815835502748927', '.781314552938357')))
    point = [I(x) for x in center]
    radius = Fr(1, 100)
    box = [I(x-radius, x+radius) for x in center]
    raw_band = I(Fr(17, 10), Fr(7, 4))
    f0 = four_phase_eval(point, I(Fr(69, 40)))[0]
    inverse = inverse_at_point([[f.derivative[j] for j in range(4)] for f in f0])
    fr = four_phase_eval(point, raw_band)[0]
    fx, quiet1, quiet2 = four_phase_eval(box, raw_band)
    operator = norm_error(inverse, [[f.derivative[j] for j in range(4)] for f in fx])
    residual = max(M.norm_interval(sum((fr[j].value*inverse[i][j] for j in range(4)), I(0)))
                   for i in range(4))
    relative_image_bound = residual/radius+operator
    assert Fr(47, 100) < operator < Fr(49, 100)
    assert Fr(13, 1000) < residual < Fr(14, 1000)
    assert Fr(9, 5) < relative_image_bound < Fr(19, 10)
    assert all(q.value.lo > 0 for q in quiet1)
    assert all(quiet2[j].value.lo < 0 < quiet2[j].value.hi for j in (1, 2))
    print('FIXED FOUR-PHASE BAND TEST FAILED TO CERTIFY (not nonexistence)')
    print('Raw band [17/10,7/4] x {2}, hazard radius1/100')
    print('Natural interval image bound / radius in (9/5,19/10)')
    print('Two second-quiet sign enclosures contain zero; no subdivision attempted')


def main():
    point = [I(x) for x in CENTER]
    box = [I(x-RADIUS, x+RADIUS) for x in CENTER]
    f0 = evaluate(point)[0]
    fx, gaps, den, values, deleted = evaluate(box)
    j0 = [[f.derivative[j] for j in COLS] for f in f0]
    jx = [[f.derivative[j] for j in COLS] for f in fx]
    inv = inverse_at_point(j0)
    correction = max(abs(sum((inv[i][j]*f0[j].value.to_fraction()
                              for j in range(9)), Fr(0))) for i in range(9))
    norm = norm_error(inv, jx)
    assert correction < Fr(1, 10**9)
    assert norm < Fr(1, 100)
    assert correction+norm*RADIUS < RADIUS/50
    assert Fr(17, 10) < box[3].lo < box[3].hi < Fr(7, 4)
    assert all(0 < box[j].lo < box[j].hi < Fr(1, 4) for j in KEEP)
    assert Fr(7, 10) < den.value.lo < den.value.hi < Fr(4, 5)
    assert all(gaps[t][i].value.hi < -Fr(1, 6) for t, i in ((0, 1), (1, 3), (2, 2)))
    assert all(d.value.hi < Fr(5, 6) for row in deleted for d in row)
    # Nine-role analytic branch, with all nine rate coordinates free.
    rate_j0 = [[f.derivative[j] for j in range(9)] for f in f0]
    rate_jx = [[f.derivative[j] for j in range(9)] for f in fx]
    fa0 = [f.derivative[9] for f in f0]
    fax = [f.derivative[9] for f in fx]
    rate_derivative = derivative_box(rate_j0, rate_jx, fa0, fax)
    lost = rate_derivative[3]
    assert -Fr(1, 8) < lost.lo < lost.hi < -Fr(1, 12)
    # Eight-role branch: q10 stays zero, only the other active equations hold.
    eight0 = [[rate_j0[i][j] for j in KEEP] for i in KEEP]
    eightx = [[rate_jx[i][j] for j in KEEP] for i in KEEP]
    d8 = derivative_box(eight0, eightx, [fa0[i] for i in KEEP], [fax[i] for i in KEEP])
    quiet_derivative = fax[3]+sum((rate_jx[3][j]*d8[k] for k, j in enumerate(KEEP)), I(0))
    assert Fr(1, 5) < quiet_derivative.lo < quiet_derivative.hi < Fr(1, 4)
    print('EXACT CONTACT AND BOTH CROSSING SIGNS PASSED')
    print('Unique contact in center+[-10^-6,10^-6]^9; 17/10 < a* < 7/4')
    print('dq10/da at contact lies in (-1/8,-1/12)')
    print('Dropped-role cleared Quit gap derivative lies in (1/5,1/4)')
    print('DECIMAL LOCATORS ONLY', float(lost.lo), float(lost.hi),
          float(quiet_derivative.lo), float(quiet_derivative.hi))
    fixed_band_test()


if __name__ == '__main__':
    main()
