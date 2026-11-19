"""Exact parameter-cell checks for two guaranteed calendars in canonical matched games."""
from fractions import Fraction as Q
from itertools import product
from math import prod, ceil
from multiprocessing import Pool
import sys

import numpy as np
from scipy.optimize import root
from sympy import Matrix, eye

SIX = (((0,), (1,), (0, 2), (1, 3), (0, 2), (3,)),
       (.641, .592, .147, .544, .482, .591, .452, .689, .738))
FOUR = (((0, 2), (1, 3), (2,), (3,)), (.63, .06, .63, .06, .63, .63))
AXES = [(Q(-1), Q(-3, 4), 8)] * 2 + [(Q(1, 2), Q(2, 3), 6)] * 2
DIGITS = sum(1 << (2*j) for j in range(16))


class Polynomial(dict):
    """Sparse polynomials. The j-th pair of bits in a key records exponent j."""
    def __add__(self, other):
        result = Polynomial(self)
        terms = other if isinstance(other, Polynomial) else {0: other}
        for key, value in terms.items():
            result[key] = result.get(key, 0) + value
        return result

    __radd__ = __add__

    def __neg__(self):
        return Polynomial((key, -value) for key, value in self.items())

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return (-self) + other

    def __mul__(self, other):
        if not isinstance(other, Polynomial):
            return Polynomial((key, value * other) for key, value in self.items())
        result = Polynomial()
        for a, va in self.items():
            for b, vb in other.items():
                # A square may occur when the next mixing visit is today's date one period later.
                if ((a >> 1) & (b | b >> 1) | (b >> 1) & (a | a >> 1)) & DIGITS:
                    raise ArithmeticError('Exponent exceeds two')
                result[a+b] = result.get(a+b, 0) + va * vb
        return result

    __rmul__ = __mul__


def comparisons(groups, x, rewards, expanded):
    def coordinate(j, value):
        return Polynomial({0: value, 1 << (2*j): 1}) if expanded else value
    n, h = len(groups), len(x)
    T = [coordinate(h+i, value) for i, value in enumerate(rewards)]
    q = [[0]*4 for group in groups]
    slots = [(t,i) for t,g in enumerate(groups) for i in g]
    for j,(t,i) in enumerate(slots):
        q[t][i] = coordinate(j, x[j])
    M, d = (Q(8,3), Q(1,10)) if expanded else (8/3, .1)
    active, idle = [], []
    for t, group in enumerate(groups):
        for i in range(4):
            mate = (i+2) % 4
            u = (t+1) % n
            while i not in groups[u]:
                u = (u+1) % n
            value = M * q[u][mate]
            u = (u-1) % n
            while u != t:
                if i % 2 == u % 2:
                    z = q[u][mate]
                    value = 3*z + (1-z)*value
                else:
                    w, z = q[u][u % 2], q[u][u % 2+2]
                    value = -1 + (1-w)*(1-z)*(1+value) + (1+T[i])*w*z
                u = (u-1) % n
            if i % 2 == t % 2:
                z = q[t][mate]
                advantage = (3-M)*z + (1-z)*value
            else:
                w, z = q[t][(i+1) % 4], q[t][(i-1) % 4]
                advantage = (1-w)*(1-z)*value - d*(w-z)
            (active if i in group else idle).append(advantage)
    return active, idle


def round_matrix(matrix):
    return matrix.applyfunc(lambda v: Q(round(10**9 * v), 10**9))


def verify(calendar, cell, required_margin):
    groups, seed = calendar
    h = len(seed)
    T = [(lo+hi)/2 for lo,hi in cell]
    theta = Matrix([(hi-lo)/2 for lo,hi in cell])
    rewards = list(map(float, T))
    sample = root(lambda x: comparisons(groups, x, rewards, False)[0], seed, tol=1e-12).x
    if not np.all((sample>0)&(sample<1)):
        return False
    x = [Q(round(10**12 * v), 10**12) for v in sample]
    F, G = comparisons(groups, x, T, True)
    J = Matrix([[p.get(1 << (2*j), 0) for j in range(h)] for p in F])
    L = Matrix([[p.get(1 << (2*(h+j)), 0) for j in range(4)] for p in F])
    B = round_matrix(J.inv())
    X = round_matrix(-B*L)
    BF = [sum((Q(B[i,j])*p for j,p in enumerate(F)), Polynomial()) for i in range(h)]
    defect = abs(eye(h)-B*J)
    affine_error = abs(B*Matrix([p.get(0,0) for p in F])) + abs(B*(J*X+L))*theta
    predictor = abs(X)*theta
    keys = set().union(*BF, *G)
    exponents = {k: [(k >> (2*j)) & 3 for j in range(h+4)] for k in keys}
    high = sorted(k for k in keys if sum(exponents[k])>=2)
    powers = np.array([exponents[k] for k in high])
    coeff = np.array([[abs(p.get(k,0)) for k in high] for p in BF], dtype=float)
    def floats(mat):
        return np.array(mat, dtype=float).ravel()
    rad = np.full(h, 1e-10)
    for _ in range(60):
        if max(rad) > 1:
            return False
        scale = np.r_[floats(predictor)+rad, floats(theta)]
        terms = np.prod(scale ** powers, axis=1)
        error = floats(affine_error) + np.array(defect, dtype=float) @ rad + coeff @ terms
        if (rad > error).all():
            break
        rad = np.maximum(rad, error*1.02+1e-10)
    radius = Matrix([Q(ceil(10**11*v), 10**11) for v in rad])

    # All subsequent computations, including each inequality determining acceptance, are rational.
    scale = list(predictor+radius) + list(theta)
    weight = {k: prod(v**a for v,a in zip(scale, exps) if a) for k,exps in exponents.items()}
    error = affine_error + defect*radius
    for i,p in enumerate(BF):
        error[i] += sum(abs(p.get(k,0))*weight[k] for k in high)
    margin = min(p.get(0,0)-sum(abs(v)*weight[k] for k,v in p.items() if k) for p in G)
    return (all(r>e for r,e in zip(radius,error))
            and all(u<v<1-u for u,v in zip(scale,x)) and margin>required_margin)


def six_cell(index):
    cell = [(a+(b-a)*j/n, a+(b-a)*(j+1)/n) for j,(a,b,n) in zip(index,AXES)]
    return verify(SIX, cell, Q(1,100))


def upper_cell(index):
    cell = tuple((Q(j,6), Q(j+1,6)) for j in index)
    if any(all(cell[i][1]<=Q(1,3) for i in pair) for pair in [(0,2),(1,3)]):
        return True  # Existing paired-observer cylinder, including its boundary.
    return any(verify(FOUR, cell[k:]+cell[:k], Q(0)) for k in range(4))


if __name__=='__main__':
    with Pool(4) as pool:
        if all(pool.imap_unordered(upper_cell, product(range(4),repeat=4))):
            print('Upper [0,2/3]^4 certified, using its paired-observer cylinder and 144 checked cells.',flush=True)
        else:
            raise ArithmeticError('Uncertified upper cell')
        if 'upper' not in sys.argv:
            if not all(pool.imap_unordered(six_cell, product(*(range(n) for _,_,n in AXES)))):
                raise ArithmeticError('Uncertified six-date cell')
            print('All 2304 six-date cells certified with every idle advantage >1/100.',flush=True)
