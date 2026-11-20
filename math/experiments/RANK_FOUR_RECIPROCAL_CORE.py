"""Verify the entire reciprocal-core sign class at the fourth order level.

Vertex entries are homogeneous probability coordinates. The linear solver
proposes path weights. Complete paths with exact rational weights enter the
certificate, and payoff verification uses literal independent label draws.
"""
from fractions import Fraction
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import prod

import numpy as np
from scipy import sparse
from scipy.optimize import linprog

PLAYERS = tuple(range(4))
POSITIVE = (3, 3, 1, 1)
FACES = tuple((i,p,n) for i,p in enumerate(POSITIVE)
              for n in PLAYERS if n not in (i,p))
SAMPLES = np.array(list(product(range(4), repeat=4)))
PAIRS = tuple(combinations_with_replacement(PLAYERS, 2))

POINTS = [
    (0, 0, 0, 1),
    (0, 0, 1, 1),
    (0, 0, 3, 1),
    (0, 1, 1, 4),
    (0, 1, 3, 1),
    (0, 1, 0, 3),
    (0, 1, 1, 1),
    (0, 3, 3, 1),
    (0, 1, 0, 1),
    (0, 1, 0, 0),
    (1, 1, 1, 5),
    (1, 3, 3, 1),
    (1, 1, 3, 1),
    (3, 1, 9, 3),
    (1, 1, 1, 1),
    (3, 1, 3, 3),
    (3, 3, 3, 1),
    (3, 1, 3, 1),
]

SCHEDULES = [
    "1.3.2.0.1.3.2.0.1.3.2.0.1.3.2.0",
    "2.0123.0123.0123.013",
    "12.0123.0123.0123.03",
    "3.1.2.0.3.1.2.3.1.0.2.3.1.2.0.0",
    "3.1.2.0.3.1.3.2.1.0.3.2.1.0.2.0",
    "3.2.0.1.3.2.3.0.2.3.1.0.2.1.0.1",
    "3.2.1.0.3.2.1.3.0.2.1.3.2.0.1.0",
    "3.3.0123.0123.012.012",
    "23.23.0123.0123.01.01",
]

CELLS = [
    ((0, 1, 6, 14), 6),
    ((0, 1, 14, 15), 5),
    ((0, 3, 5, 10), 7),
    ((1, 2, 4, 12), 8),
    ((1, 2, 12, 13), 8),
    ((1, 4, 6, 12), 8),
    ((1, 6, 12, 14), 8),
    ((1, 12, 13, 15), 8),
    ((1, 12, 14, 15), 8),
    ((3, 6, 8, 10), 3),
    ((4, 6, 7, 11), 1),
    ((4, 6, 11, 12), 1),
    ((5, 3, 8, 10), 4),
    ((6, 7, 9, 11), 2),
    ((6, 8, 9, 14), 0),
    ((6, 9, 11, 14), 2),
    ((6, 11, 12, 14), 1),
    ((9, 11, 14, 16), 2),
    ((10, 6, 8, 14), 4),
    ((11, 12, 14, 16), 1),
    ((12, 13, 15, 17), 1),
    ((12, 14, 15, 17), 1),
    ((12, 14, 16, 17), 1),
]

@cache
def volume(rows):
    return sum((-1)**sum(p[a]>p[b] for a,b in combinations(PLAYERS,2))
               * prod(rows[i][p[i]] for i in PLAYERS) for p in permutations(PLAYERS))


def simplex_size(t):
    return Fraction(abs(volume(t)), prod(sum(v) for v in t))


def check_partition(tetrahedra,target_volume):
    assert all(simplex_size(t)>0 for t in tetrahedra)
    assert sum(simplex_size(t) for t in tetrahedra) == target_volume
    for left,right in combinations(tetrahedra,2):
        # A plane through three vertices separates the interiors.
        for face in combinations(set(left+right),3):
            l = [volume(face+(v,)) for v in left]
            r = [volume(face+(v,)) for v in right]
            if (min(l)>=0>=max(r) and max(l)>0>min(r)
                    or min(r)>=0>=max(l) and max(r)>0>min(l)):
                break
        else:
            raise AssertionError((left,right))



def check_cover():
    hull = ((0,1,0,0),(0,0,0,1),(0,0,3,1),(3,1,3,1))
    for a,b,c,d in POINTS:
        assert min(a,b,c,d) >= 0 and a <= c and a <= 3*b and c <= 3*d
    tetrahedra = [tuple(POINTS[i] for i in indices) for indices,_ in CELLS]
    check_partition(tetrahedra,simplex_size(hull))


@cache
def graph(schedule,late=None,protected=(3,), before=None):
    """Cut count graph excluding a protected second owner after a possible first 0."""
    training = (0,)*4
    states, edges, labels = [], [], []
    previous = {}
    for k,owners in enumerate(schedule+((),)):
        choices = [range(max(0,t-1), min(4,t+1)+1) for t in training]
        counts = list(product(*choices))
        index = {v: len(states)+i for i,v in enumerate(counts)}
        for c in sorted(index.keys() & previous.keys()):
            edges.append((previous[c],index[c]))
            labels.append((k-1,c,-1))
        for c in counts:
            for j in PLAYERS:
                v = tuple(x+(i==j) for i,x in enumerate(c))
                if before is not None and j==before[1] and c[before[0]]<4:
                    continue
                if j==late and any(c[r]<4 for r in PLAYERS if r!=late):
                    continue
                blocked = j in protected and c[0]>0 and all(
                    c[k]<4 for k in PLAYERS if k not in (0,j))
                if v in index and not blocked:
                    edges.append((index[c],index[v]))
                    labels.append((k,c,j))
        states.extend(counts)
        training = tuple(t+(i in owners) for i,t in enumerate(training))
        previous = index
    assert training==(4,4,4,4)
    out,inc = ([[] for _ in states] for _ in range(2))
    for a,(u,v) in enumerate(edges):
        out[u].append(a)
        inc[v].append(a)
    reach,back = {0},{len(states)-1}
    for i in range(len(states)):
        if i in reach:
            reach.update(edges[a][1] for a in out[i])
    for i in reversed(range(len(states))):
        if i in back:
            back.update(edges[a][0] for a in inc[i])
    kept = sorted(reach & back)
    index = {v:i for i,v in enumerate(kept)}
    arcs = [a for u in kept for a in out[u] if edges[a][1] in index]
    endpoints = np.array([(index[edges[a][0]],index[edges[a][1]]) for a in arcs])
    steps = [labels[a] for a in arcs]
    n = len(arcs)
    incidence = sparse.coo_matrix((np.tile([1.,-1.],n),
        (endpoints.ravel(),np.repeat(np.arange(n),2))),shape=(len(kept),n)).tocsr()
    flow = np.zeros(len(kept))
    flow[0],flow[-1] = 1,-1
    hint = np.zeros((4,4,len(schedule)+1,n),dtype=np.int16)
    for a,(k,c,j) in enumerate(steps):
        if j<0:
            continue
        for i in PLAYERS:
            if i!=j:
                f = prod(4-c[r] for r in PLAYERS if r not in (i,j))
                hint[i,j,:,a] = (4-c[i])*f
                hint[i,j,k:,a] -= 4*f
    return incidence,flow,endpoints,steps,hint


def balanced_gain(y, counts, row, positive, negative):
    """An integer weighted set of negative donors gives a restricted row generator."""
    if isinstance(negative, int):
        return y[negative] * counts[row, positive] - y[positive] * counts[row, negative]
    return sum(weight * (y[donor] * counts[row, positive] - y[positive] * counts[row, donor])
               for donor, weight in negative)


def guess(schedule,vertices,faces=FACES,late=None,protected=(3,), before=None):
    incidence,flow,endpoints,steps,hint = graph(schedule,late,protected,before)
    n = len(steps)
    blocks = []
    vertex_gains = []
    for v in vertices:
        y = np.array(v)/sum(v)
        vertex_gains.append(np.vstack([balanced_gain(y,hint,i,p,j) for i,p,j in faces]))
    for u,v in PAIRS:
        row = [sparse.csr_matrix(vertex_gains[0].shape) for _ in PLAYERS]
        row[u] += sparse.csr_matrix(vertex_gains[v])
        row[v] += sparse.csr_matrix(vertex_gains[u])
        blocks.append(sparse.hstack(row))
    gains = sparse.vstack(blocks)
    count = gains.shape[0]
    balance = sparse.block_diag([incidence]*4)
    eq = sparse.hstack((balance,sparse.csr_matrix((balance.shape[0],count)))).tocsr()
    sol = linprog([0]*(4*n)+[-1]*count,
                  A_ub=sparse.hstack((-gains,sparse.eye(count))).tocsr(), b_ub=np.zeros(count),
                  A_eq=eq,b_eq=np.tile(flow,4),bounds=[(0,None)]*(4*n)+[(0,.02)]*count,
                  method="highs")
    assert sol.success
    out = [[] for _ in flow]
    for a,(u,v) in enumerate(endpoints):
        out[u].append(a)
    priors = []
    for i in PLAYERS:
        x = sol.x[i*n:(i+1)*n].copy()
        prior = []
        while max(x[out[0]])>1e-8:
            node = 0
            path = []
            while node != len(flow)-1:
                a = max(out[node],key=lambda e:x[e])
                path.append(a)
                node = endpoints[a,1]
            weight = min(x[a] for a in path)
            assert weight>0
            x[path] -= weight
            prior.append((weight,tuple(steps[a][2] for a in path)))
        priors.append(prior)
    return priors


@cache
def score(schedule,word):
    """Count each of the 256 validation draws for assignment and each deletion."""
    training,validation = [0]*4,[0]*4
    dates = [[] for _ in PLAYERS]
    tests = []
    for time,j in enumerate(word):
        if j<0:
            for i in schedule[len(tests)]:
                training[i] += 1
            tests.append(time)
        else:
            validation[j] += 1
            dates[j].append(time)
        assert max(abs(u-v) for u,v in zip(training,validation))<=1
    assert training==validation==[4]*4 and len(tests)==len(schedule)
    picked = np.array(dates)[np.array(PLAYERS),SAMPLES]
    first = np.argmin(picked,axis=1)
    assigned = np.bincount(first,minlength=4)
    tests.append(len(word))
    f = np.empty((4,4,len(tests)),dtype=np.int64)
    for i in PLAYERS:
        rivals = picked.copy()
        rivals[:,i] = len(word)+1
        next_owner = np.argmin(rivals,axis=1)
        when = np.min(rivals,axis=1)
        for k,cut in enumerate(tests):
            f[i,:,k] = assigned-np.bincount(next_owner[when<cut],minlength=4)
    assert np.min(f[0,3])>=0
    return f


def rational_priors(priors,schedule,vertices,faces):
    """Restore numerically tight linear comparisons over the rationals."""
    from scipy.linalg import qr
    from sympy import Matrix
    starts = np.r_[0, np.cumsum(list(map(len,priors)))]
    paths = [p for prior in priors for _,p in prior]
    weights = np.array([w for prior in priors for w,_ in prior])
    basis = []
    for v in vertices:
        # Scores are integer columns indexed by complete order words.
        basis.append(np.array([balanced_gain(v,score(schedule,w),i,p,n)
                               for i,p,n in faces for w in paths],dtype=np.int64)
                     .reshape(len(faces),len(paths),-1).transpose(0,2,1)
                     .reshape(-1,len(paths)))
    equations = []
    for i in PLAYERS:
        r = np.zeros(len(paths),dtype=np.int64)
        r[starts[i]:starts[i+1]] = 1
        equations.append(r)
    for u,v in PAIRS:
        r = np.zeros_like(basis[0])
        for a,b in ((u,v),(v,u)):
            sl = slice(starts[a],starts[a+1])
            r[:,sl] += sum(vertices[a])*basis[b][:,sl]
        equations.extend(r[np.abs(r@weights)<1e-6])
    eq = np.array(equations)
    # A numerical pivot suggestion only. The final comparisons use all rows.
    _,r,indices = qr(eq.T.astype(float),mode="economic",pivoting=True)
    rank = sum(abs(np.diag(r))>1e-8)
    selected = indices[:rank]
    a = eq[selected,:]
    _,_,indices = qr(a.astype(float),mode="economic",pivoting=True)
    dep,free = indices[:rank],indices[rank:]
    x = np.array([Fraction(round(w*10**14),10**14) for w in weights],dtype=object)
    target = (selected<4).astype(int)
    rhs = target-a[:,free]@x[free]
    solution = Matrix(a[:,dep].tolist()).inv()*Matrix(rhs.tolist())
    for col,val in zip(dep,solution):
        x[col] = Fraction(val)
    return [x[starts[i]:starts[i+1]].tolist() for i in PLAYERS]

def check_cell(schedule,vertices,faces=FACES,late=None,protected=(3,), before=None):
    priors = guess(schedule,vertices,faces,late,protected,before)
    for prior in priors:
        for _,path in prior:
            assert all(np.min(score(schedule,path)[0,donor])>=0 for donor in protected)
            if before is not None:
                first, later = before
                assert path[:path.index(later)].count(first)==4
    if late is not None:
        for prior in priors:
            for _,path in prior:
                prefix = path[:path.index(late)]
                assert all(prefix.count(j)==4 for j in PLAYERS if j!=late)
    for scale in (10**4,10**8,None):
        corrections = rational_priors(priors,schedule,vertices,faces) if scale is None else None
        totals,counts = [],[]
        for i,prior in enumerate(priors):
            weights = corrections[i] if corrections else [int(round(w*scale)) for w,_ in prior]
            assert min(weights)>=0 and sum(weights)>0
            totals.append(sum(weights))
            counts.append(sum(w*score(schedule,path).astype(object) for w,(_,path) in zip(weights,prior)).astype(object))
        def cross(u,v):
            p = vertices[v]
            f = counts[u]
            return np.array([balanced_gain(p,f,i,j,n) for i,j,n in faces],dtype=object)
        for u,v in PAIRS:
            gain = (totals[v]*sum(vertices[u])*cross(u,v)
                    +totals[u]*sum(vertices[v])*cross(v,u))
            if np.min(gain)<0:
                break
        else:
            return sum(map(len,priors)), len(PAIRS)*len(faces)*(1+len(schedule))
    raise AssertionError((schedule,vertices))


if __name__=="__main__":
    check_cover()
    schedules = [tuple(tuple(map(int,s)) for s in row.split(".")) for row in SCHEDULES]
    words = inequalities = 0
    for ids,k in CELLS:
        a,b = check_cell(schedules[k], tuple(POINTS[i] for i in ids))
        words += a
        inequalities += b
    print(len(CELLS),"tetrahedra,",words,"weighted words,",inequalities,"exact Bernstein inequalities")
