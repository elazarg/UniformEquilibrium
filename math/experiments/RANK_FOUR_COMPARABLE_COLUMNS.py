"""Exact rank-four order certificates for every sign class with a comparable inverse column."""
from fractions import Fraction
from math import lcm
from itertools import product

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

from FIN4_SINGLETON_SIGN_CLASSES import EDGES, I, WITNESSES, axis_vertices, det
from RANK_FOUR_RECIPROCAL_CORE import graph, score

# Each hexadecimal digit is the bit mask of owners trained at that date.
SCHEDULES = (
    "ffff",
    "1fffe",
    "2fffd",
    "3fffc",
    "4fffb",
    "7fff8",
    "8fff7",
    "9fff6",
    "dfff2",
    "78778878",
    "d2dd22d2",
    "12c12121c2cc",
    "14a14141a4aa",
    "21c21212c1cc",
    "429424249299",
    "825828285255",
    "41284124812c128",
    "82148218421c214",
)

SCHEDULE_BY_ROW = {
    3: (4, 0, 11, 11),
    5: (0, 1, 6, 3),
    6: (0, 0, 6, 1),
    7: (4, 1, 10, 1),
    8: (0, 0, 6, 1),
    10: (0, 0, 6, 13),
    11: (0, 1, 1, 1),
    12: (0, 1, 1, 1),
    13: (0, 6, 11, 5),
    14: (0, 0, 17, 16),
    15: (14, 0, 0, 0),
    16: (0, 1, 2, 0),
    17: (2, 1, 0, 2),
    18: (0, 8, 7, 1),
    19: (0, 8, 7, 1),
    20: (4, 12, 15, 2),
    21: (0, 9, 7, 2),
}


def generator_scores(f, faces):
    # The two endpoint inequalities cover y_p / y_n in [20/21,21/20].
    return np.vstack([a*f[i,p]-b*f[i,n] for i,p,n in faces
                      for a,b in ((21,20),(20,21))])


def check_case(sign, axis, digits):
    # graph and score reserve 0 and 3 for a protected positive recipient/donor comparison.
    positive = next(p for p in I if sign[axis][p]>0)
    owners = (axis, *(i for i in I if i not in (axis,positive)), positive)
    schedule = tuple(tuple(i for i in I if int(digit,16) & (1<<owners[i])) for digit in digits)
    pos = [p for p in I if sign[axis][owners[p]]>0]
    faces = [(i,p,n) for i,p,n in product(I,repeat=3)
             if sign[owners[i]][owners[p]]>0>sign[owners[i]][owners[n]]]
    incidence,flow,edges,steps,hint = graph(schedule)
    bound = [(0,0) if j in pos and c[0]>0 and all(c[k]<4 for k in I if k not in (0,j))
             else (0,None) for _,c,j in steps]
    gain = sparse.csr_matrix(generator_scores(hint,faces))
    n,m = len(steps),gain.shape[0]
    problem = linprog([0]*n+[-1]*m, A_ub=sparse.hstack((-gain,sparse.eye(m))),
                      b_ub=np.zeros(m), A_eq=sparse.hstack((incidence,sparse.csr_matrix((len(flow),m)))),
                      b_eq=flow, bounds=bound+[(0,0.02)]*m, method="highs")
    assert problem.success
    x = problem.x[:n].copy()
    out = [[] for _ in flow]
    for a,(u,v) in enumerate(edges):
        out[u].append(a)
    words,weights = [],[]
    while max(x[out[0]])>1e-8:
        v = 0
        path = []
        while v!=len(flow)-1:
            e = max(out[v],key=lambda a:x[a])
            path.append(e)
            v = edges[e,1]
        mass = min(x[path])
        assert mass>0
        x[path] -= mass
        words.append(tuple(steps[e][2] for e in path))
        weights.append(mass)
    columns = []
    for word in words:
        f = score(schedule,word)
        assert all(min(f[0,p])>=0 for p in pos)
        columns.append(generator_scores(f,faces).ravel())
    scores = np.array(columns,dtype=np.int64).T
    for denominator in (10**6,10**12):
        integer = np.array([round(w*denominator) for w in weights],dtype=object)
        if sum(integer)>0 and min(scores@integer)>=0:
            return len(words),len(scores)
    # Recover tight payoff equalities on complete words before the final integer check.
    from scipy.linalg import qr
    from sympy import Matrix
    weights = np.array(weights)
    equations = np.vstack((np.ones(len(words),dtype=int),scores[abs(scores@weights)<1e-6]))
    _,r,pivots = qr(equations.T.astype(float),mode="economic",pivoting=True)
    rank = sum(abs(np.diag(r))>1e-8)
    rows = pivots[:rank]
    a = equations[rows]
    _,_,pivots = qr(a.astype(float),mode="economic",pivoting=True)
    dep,free = pivots[:rank],pivots[rank:]
    w = np.array([Fraction(round(v*10**12),10**12) for v in weights],dtype=object)
    w[dep] = [Fraction(x) for x in Matrix(a[:,dep]).inv()*Matrix((rows==0).astype(int)-a[:,free]@w[free])]
    denominator = lcm(*(v.denominator for v in w))
    integer = w*denominator
    assert min(integer)>=0 and sum(integer)>0 and min(scores@integer)>=0
    return len(words),len(scores)


if __name__=="__main__":
    cases = eligible = words = checks = 0
    for c,entries in enumerate(WITNESSES,1):
        sign = [[0]*4 for i in I]
        for (i,j),value in zip(EDGES,entries):
            sign[i][j] = 1 if value>0 else -1
        if max(sum(j>0 for j in r) for r in sign)==1:
            assert c not in SCHEDULE_BY_ROW
            continue
        for h in I:
            k = SCHEDULE_BY_ROW[c][h]
            eligible += max(map(det,axis_vertices(sign,h)))>0
            w,s = check_case(sign,h,SCHEDULES[k])
            cases += 1
            words += w
            checks += s
    assert (cases,eligible)==(68,60)
    print(cases,eligible,words,checks)
