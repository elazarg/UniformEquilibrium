"""Verify a 1,212-date proper equilibrium on Simon's introductory table.

NumPy and SciPy propose a center and an approximate inverse. Every successful
certificate assertion uses rational arithmetic or checked, overflow-safe integer
arithmetic. The 12 interpolation knots are seeds and do not enter the proof.
"""
from fractions import Fraction
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import splu

N = 303
DIM = 4 * N
KNOTS = [0, 13, 14, 16, 25, 70, 150, 240, 298, 300, 301, 302]
SEED = [
    [64, 1, 9710, 136], [52, 2826, 4292, 5676], [52, 2975, 32, 6929],
    [49, 1878, 19, 8004], [41, 812, 8, 9041], [21, 426, 4, 9408],
    [6, 238, 2, 9584], [2, 116, 1, 9697], [0, 67, 1, 9743],
    [0, 66, 1, 9744], [0, 65, 0, 9746], [1, 64, 39, 9709],
]


def data(x, exact=False):
    hundredth = Fraction(1, 100) if exact else 0.01
    phases = []
    slacks = []
    for t in range(N):
        moving = [True, True, t >= 14, False]
        q = [x[4*t+i] if moving[i] else 0 for i in range(4)]
        rows = []
        for i in range(4):
            a, b, c = [(i+k) % 4 for k in (1, 2, 3)]
            joint_survival = (1-q[a])*(1-q[b])*(1-q[c])
            quit_offer = hundredth * (99-100*q[a]-98*joint_survival)
            payoff = quit_offer if moving[i] else x[4*t+i]
            if not moving[i]:
                slacks.append(payoff-quit_offer)
            survival_derivative = {}
            for j, first, second in [(a,b,c), (b,a,c), (c,a,b)]:
                if moving[j]:
                    survival_derivative[4*t+j] = -(1-q[first])*(1-q[second])
            if moving[i]:
                value_derivative = {
                    col: -98*hundredth*derivative
                    for col, derivative in survival_derivative.items()
                }
                if moving[a]:
                    value_derivative[4*t+a] -= 1
            else:
                value_derivative = {4*t+i: 1}
            rows.append((payoff, value_derivative, q[b], 4*t+b if moving[b] else None,
                         joint_survival, survival_derivative))
        phases.append(rows)

    function = []
    jacobian = []
    for t in range(N):
        for i in range(4):
            u, du, passive, mate_cell, survival, dh = phases[t][i]
            previous_i = i if t else (i+1) % 4
            w, dw = phases[(t-1) % N][previous_i][:2]
            function.append(u-passive-survival*w)
            row = dict(du)
            if mate_cell is not None:
                row[mate_cell] = row.get(mate_cell, 0)-1
            for col, derivative in dh.items():
                row[col] = row.get(col, 0)-w*derivative
            for col, derivative in dw.items():
                row[col] = row.get(col, 0)-survival*derivative
            jacobian.append(row)
    return function, jacobian, slacks


def sparse(rows, dtype, convert):
    values, columns, start = [], [], [0]
    for row in rows:
        for column, value in sorted(row.items()):
            columns.append(column)
            values.append(convert(value))
        start.append(len(values))
    return csr_matrix((np.asarray(values, dtype=dtype), columns, start), shape=(len(rows), len(rows)))


def candidate():
    coarse = np.asarray(SEED, dtype=float)/10000
    x = np.stack([np.interp(np.arange(N), KNOTS, coarse[:,i]) for i in range(4)], axis=1).ravel()
    for _ in range(35):
        f, j, _ = data(x)
        delta = splu(sparse(j, float, float).tocsc()).solve(-np.asarray(f))
        x += delta
        if np.max(np.abs(delta)) < 1e-13:
            break
    return [Fraction(round(float(v)*2**54), 2**54) for v in x]


def inverse_bound(rows):
    size = len(rows)
    bound = max(map(len, rows))
    exact_scale = 2**26
    coarse = sparse(rows, np.int64, lambda v: round(v*exact_scale))
    # The candidate inverse is floating point. Certification below only uses its
    # explicitly rounded integer entries, with no assumed floating-point accuracy.
    lu = splu(sparse(rows, float, float).tocsc())
    inverse_scale = 2**20
    proposed = np.rint(lu.solve(np.eye(size))*inverse_scale)
    assert np.isfinite(proposed).all() and np.max(np.abs(proposed)) < 2**32
    inverse = proposed.astype(np.int64)
    max_inverse = int(np.max(np.abs(inverse)))
    max_coarse = int(np.max(np.abs(coarse.data)))
    scale = exact_scale*inverse_scale
    assert bound*max_coarse*max_inverse + scale < 2**63-1
    residual = -(coarse @ inverse)
    diagonal = np.arange(size)
    residual[diagonal, diagonal] += scale
    assert size*int(np.max(np.abs(residual))) < 2**63-1
    assert size*max_inverse < 2**63-1
    inv_norm = Fraction(int(np.max(np.sum(np.abs(inverse), axis=1))), inverse_scale)
    residual_norm = Fraction(int(np.max(np.sum(np.abs(residual), axis=1))), scale)
    rho = residual_norm + Fraction(bound,2*exact_scale)*inv_norm
    assert inv_norm < 22000 and rho < Fraction(1,100)
    jac_inverse = inv_norm/(1-rho)
    assert jac_inverse < 23000
    return jac_inverse


def twisted_rows(rows, twist):
    # In chronological quarter coordinates only rows 0..3 use the last
    # four stored coordinates of the next physical quarter. All player permutations
    # have already been applied in data().
    if twist == -1:
        return [{col: -v if i < 4 and col >= DIM-4 else v for col, v in row.items()}
                for i, row in enumerate(rows)]
    # Realification of A + i B gives [[A,-B],[B,A]].
    out = [{} for _ in range(2*DIM)]
    for i, row in enumerate(rows):
        for col, value in row.items():
            if i < 4 and col >= DIM-4:
                out[i][DIM+col] = -value
                out[DIM+i][col] = value
            else:
                out[i][col] = value
                out[DIM+i][DIM+col] = value
    return out


def verify():
    center = candidate()
    f, rows, slacks = data(center, exact=True)
    radius = Fraction(1, 10**9)
    assert min(center) > 100*radius and max(center) < 1-100*radius
    assert min(slacks) > Fraction(3, 1000)
    defect = max(abs(v) for v in f)
    assert defect < Fraction(1, 2**48)
    jac_inverse = inverse_bound(rows)
    # The second-derivative entrywise sum of each equation is at most 48
    # on the unit cube. See the companion proof.
    contraction = 48*jac_inverse*radius
    assert contraction < Fraction(1,100) and jac_inverse*defect < radius/10
    print('quarter', N, 'physical period', 4*N, 'inputs', DIM)
    print('center defect', float(defect), 'quiet gap', float(min(slacks)))
    print('inverse upper bound', float(jac_inverse), 'radius', float(radius))
    print('contraction upper bound', float(contraction))
    for twist in (-1, 1j):
        twisted_inverse = inverse_bound(twisted_rows(rows, twist))
        assert 48*twisted_inverse*radius < 1
        print('twist', twist, 'inverse upper bound', float(twisted_inverse))


if __name__ == '__main__':
    verify()
