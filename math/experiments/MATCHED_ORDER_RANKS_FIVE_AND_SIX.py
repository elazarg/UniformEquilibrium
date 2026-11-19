"""Search for and verify exact rank-five and rank-six certificates on the symmetric matched cone.

Requires NumPy and SciPy for witness discovery. Successful verification uses
integer counts on complete paths, independently checking every cut and gain.
"""
from itertools import product
from math import prod

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, hstack

# Endpoints use sixteenths of the mate reward in units of a unit crossed loss.
def staggered(rank, lead):
    return ".".join(["02"]*lead + ["0123"]*(rank-lead) + ["13"]*lead)


GROUPS = {
    5: [
        (staggered(5,1), [32,48]),
        (staggered(5,2), [48,64,80]),
        (staggered(5,3), [80,112,160,256])
    ],
    6: [
        (staggered(6,1), [32, 39]),
        ("02.02.13.02.02.02.13.02.13.13.13.13", [39, 46, 53, 60]),
        ("02.012.023.2.02.0.1.023.1.13.13.13.3",
         [60, 74, 88, 116, 144, 200, 256, 312, 368, 424, 480]),
    ]
}


def row_scores(n, path, schedule, endpoint):
    """Integer prescribed minus offered scores, scaled by 16 n^4."""
    current = [0]*4
    training = [0]*4
    offer = [0]*4
    assigned = [0]*4
    tested = []
    for token in path:
        if token == -1:
            for i in schedule[len(tested)]:
                training[i] += 1
            tested.append(offer.copy())
        else:
            i = token
            for j in range(4):
                if j == i:
                    continue
                gain = endpoint if j == (i ^ 1) else -16
                factor = prod(n-current[k] for k in range(4) if k not in (i,j))
                offer[j] += n*factor*gain
                assigned[j] += (n-current[j])*factor*gain
            current[i] += 1
        assert all(abs(current[i]-training[i]) <= 1 for i in range(4))
    assert len(tested) == len(schedule) and training == current == [n]*4
    return [assigned[i]-bound[i] for bound in tested+[offer] for i in range(4)]


def graph(n,schedule):
    count = [0]*4
    states = []
    for k, owners in enumerate([*schedule, ()]):
        choices = [range(max(0, x-1), min(n, x+1)+1) for x in count]
        states.extend((k,u) for u in product(*choices))
        for i in owners:
            count[i] += 1
    index = {state: j for j, state in enumerate(states)}
    arcs = []
    out = [[] for _ in states]
    for j, (k,u) in enumerate(states):
        ends = [(-1,(k+1,u))] + [
            (i,(k,tuple(x + (r == i) for r,x in enumerate(u)))) for i in range(4)]
        for player, end in ends:
            if end in index:
                out[j].append(len(arcs))
                arcs.append((j,index[end],player))
    ends = np.array([a[:2] for a in arcs])
    size = len(arcs)
    incidence = coo_matrix((np.r_[np.ones(size), -np.ones(size)],
                            (ends.T.ravel(), np.tile(np.arange(size),2))),
                           shape=(len(states),size)).tocsr()
    charge = np.zeros(len(states))
    charge[0] = 1
    charge[-1] = -1
    return states, arcs, out, incidence, charge


def prove(n,schedule, left, right, data):
    states, arcs, out, incidence, charge = data
    costs = np.zeros((2, len(schedule)+1, 4, len(arcs)))
    for h, (start,end,i) in enumerate(arcs):
        if i < 0:
            continue
        k,u = states[start]
        for j in range(4):
            if j != i:
                for bound,mate in enumerate((left,right)):
                    reward = mate if j == (i ^ 1) else -16
                    term = reward * prod(n-u[r] for r in range(4) if r not in (i,j))
                    costs[bound,:,j,h] -= (n-u[j])*term
                    costs[bound,k:,j,h] += n*term
    matrix = costs.reshape(-1,len(arcs))
    solution = linprog([0]*len(arcs)+[-1], A_eq=hstack((incidence,charge[:,None]*0)),
                       b_eq=charge, A_ub=np.column_stack((matrix,np.ones(len(matrix)))),
                       b_ub=np.zeros(len(matrix)), bounds=[(0,None)]*len(arcs)+[(None,None)],
                       method="highs")
    assert solution.success and solution.x[-1] > 0
    residual = solution.x[:-1].copy()
    witnesses = []
    while residual.max() > 1e-7:
        pos, trail = 0, []
        while pos != len(states)-1:
            h = max(out[pos], key=lambda edge: residual[edge])
            assert residual[h] > 1e-9
            trail.append(h)
            pos = arcs[h][1]
        mass = min(residual[trail])
        residual[trail] -= mass
        path = [arcs[h][2] for h in trail]
        scores = row_scores(n,path,schedule,left) + row_scores(n,path,schedule,right)
        witnesses.append((mass,scores))
    # Floating point ends with the suggestion of path weights. Integers prove the claim.
    for denominator in (1000, 10000, 100000, 1000000):
        weights = [round(denominator*m) for m,_ in witnesses]
        if min(weights) >= 0 and sum(weights) > 0 and all(
            sum(w*v for w,v in zip(weights,column)) > 0
            for column in zip(*(s for _,s in witnesses))):
            return
    raise ArithmeticError("No exactly verified strictly obedient mixture")


if __name__ == "__main__":
    for rank, groups in GROUPS.items():
        prev = 32
        for text, points in groups:
            assert points[0] == prev and all(a < b for a,b in zip(points,points[1:]))
            schedule = [tuple(map(int,x)) for x in text.split(".")]
            data = graph(rank,schedule)
            for a,b in zip(points,points[1:]):
                prove(rank,schedule,a,b,data)
            prev = points[-1]
        assert prev == 32*((rank-2)**2-1)
        print(f"Verified strict rank-{rank} mixtures throughout [2,{prev//16}].")
