"""Exact fourth-order test for the full three-cycle-and-dependent sign chamber."""
from fractions import Fraction
from itertools import combinations, product
from math import lcm

from RANK_FOUR_RECIPROCAL_CORE import PLAYERS, check_cell, check_partition
from FIN4_SINGLETON_SIGN_CLASSES import EDGES, WITNESSES, boundary_faces, canonical

AXIS2_RAW_POINTS = [(1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 0, 1), (1, 1, 1, 1), (1, 0, 0, 1), (1, 0, 1, 1), (0, 1, 0, 0), (0, 1, 0, 1), (0, 1, 1, 1), (0, 0, 0, 1), (0, 0, 1, 1), (2, 2, 2, 1), (2, 1, 2, 1), (2, 0, 2, 1), (1, 5, 1, 1), (1, 2, 2, 1), (0, 4, 1, 1), (0, 2, 2, 1), (1, 1, 2, 1), (1, 0, 2, 1), (0, 1, 2, 1), (0, 0, 2, 1)]
AXIS2_RAW_SCHEDULES = [(1, 2, 8, 4, 1, 2, 8, 1, 4, 2, 8, 1, 2, 4, 8, 4), (1, 8, 2, 4, 1, 8, 2, 1, 4, 8, 2, 1, 8, 4, 2, 4), (1, 15, 1, 15, 14, 14), (2, 1, 8, 4, 2, 1, 8, 2, 4, 1, 8, 2, 1, 4, 8, 4), (2, 8, 1, 4, 2, 8, 1, 2, 4, 8, 1, 2, 8, 4, 1, 4), (2, 8, 4, 1, 2, 8, 2, 4, 8, 2, 1, 4, 8, 4, 1, 1), (8, 1, 2, 8, 4, 1, 2, 8, 1, 4, 2, 8, 4, 1, 2, 4), (8, 1, 4, 2, 8, 1, 4, 2, 8, 1, 4, 2, 8, 1, 4, 2), (8, 2, 1, 8, 4, 2, 1, 8, 2, 4, 1, 8, 4, 2, 1, 4), (8, 2, 4, 1, 8, 8, 2, 8, 2, 4, 2, 4, 4, 1, 1, 1), (8, 15, 15, 15, 7), (1, 2, 4, 8, 1, 2, 1, 4, 2, 1, 8, 4, 2, 8, 4, 8), (1, 1, 15, 15, 14, 14), (2, 1, 4, 8, 2, 1, 2, 4, 1, 2, 8, 4, 1, 8, 4, 8), (3, 15, 15, 15, 12), (2, 13, 2, 2, 13, 13, 2, 13), (10, 15, 15, 15, 5), (2, 4, 8, 2, 1, 2, 4, 8, 1, 4, 8, 2, 1, 4, 8, 1), (2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8, 1, 2, 4, 8, 1), (2, 4, 8, 1, 2, 4, 8, 2, 4, 1, 8, 2, 4, 8, 1, 1), (15, 15, 15, 15), (1, 15, 15, 15, 14)]
AXIS2_RAW_CELLS = [((0, 1, 2, 3), 0), ((0, 4, 2, 3), 1), ((0, 4, 5, 3), 2), ((6, 1, 2, 3), 3), ((6, 7, 2, 3), 4), ((6, 7, 8, 3), 5), ((9, 4, 2, 3), 6), ((9, 4, 5, 3), 7), ((9, 7, 2, 3), 8), ((9, 7, 8, 3), 9), ((9, 10, 5, 3), 10), ((9, 10, 8, 3), 10), ((3, 11, 1, 0), 11), ((3, 11, 12, 0), 2), ((3, 5, 12, 0), 2), ((5, 12, 13, 0), 12), ((6, 3, 11, 1), 13), ((14, 15, 3, 11), 14), ((6, 15, 14, 11), 15), ((8, 14, 15, 3), 16), ((16, 6, 15, 14), 17), ((8, 16, 15, 14), 18), ((16, 17, 6, 15), 5), ((8, 17, 16, 15), 19), ((18, 3, 11, 12), 20), ((18, 19, 5, 12), 21), ((19, 5, 12, 13), 21), ((18, 3, 5, 12), 21), ((15, 18, 3, 11), 20), ((8, 15, 18, 3), 10), ((20, 8, 17, 15), 10), ((20, 8, 15, 18), 10), ((10, 18, 3, 5), 10), ((10, 18, 19, 5), 10), ((10, 21, 18, 19), 10), ((10, 8, 18, 3), 10), ((10, 20, 8, 18), 10), ((10, 21, 20, 18), 10)]

AXIS3_POINTS = [(2, 2, 2, 1), (1, 1, 1, 0), (1, 1, 0, 0), (1, 0, 0, 0), (2, 1, 2, 1), (1, 0, 1, 0), (2, 0, 2, 1), (0, 1, 0, 0), (0, 1, 1, 0), (1, 2, 2, 1), (0, 2, 2, 1), (0, 0, 1, 0), (1, 1, 2, 1), (1, 0, 2, 1), (0, 1, 2, 1), (0, 0, 2, 1), (1, 1, 7, 1), (1, 0, 6, 1), (0, 1, 6, 1)]
AXIS3_SCHEDULES = [(1, 3, 7, 15, 14, 12, 8), (5, 15, 5, 15, 10, 10), (5, 5, 15, 15, 10, 10), (2, 3, 7, 15, 13, 12, 8), (6, 15, 6, 15, 9, 9), (4, 1, 2, 8, 4, 1, 2, 4, 8, 1, 4, 2, 1, 8, 2, 8), (3, 15, 3, 15, 12, 12), (4, 1, 8, 2, 4, 1, 4, 8, 2, 1, 4, 8, 1, 2, 8, 2), (4, 2, 1, 8, 4, 2, 1, 4, 8, 2, 4, 1, 2, 8, 1, 8), (4, 2, 8, 1, 4, 2, 4, 8, 1, 2, 4, 8, 2, 1, 8, 1), (4, 8, 1, 2, 4, 4, 8, 1, 4, 8, 2, 1, 8, 2, 1, 2), (4, 8, 1, 2, 4, 4, 8, 4, 1, 8, 1, 8, 2, 1, 2, 2), (4, 8, 2, 1, 4, 4, 8, 2, 4, 8, 1, 2, 8, 1, 2, 1), (4, 8, 2, 1, 4, 4, 8, 4, 2, 8, 2, 8, 1, 2, 1, 1)]
AXIS3_CELLS = [((0, 1, 2, 3), 0), ((0, 4, 1, 3), 1), ((4, 1, 5, 3), 1), ((4, 6, 5, 3), 2), ((7, 0, 1, 2), 3), ((8, 7, 9, 1), 4), ((7, 9, 0, 1), 4), ((10, 8, 7, 9), 4), ((11, 12, 1, 5), 5), ((12, 4, 1, 5), 1), ((12, 0, 4, 1), 6), ((11, 12, 13, 5), 7), ((12, 13, 4, 5), 1), ((13, 4, 6, 5), 1), ((11, 8, 12, 1), 8), ((8, 9, 12, 1), 4), ((9, 12, 0, 1), 6), ((11, 14, 8, 12), 9), ((14, 8, 9, 12), 4), ((14, 10, 8, 9), 4), ((15, 16, 12, 13), 10), ((15, 17, 16, 13), 11), ((15, 11, 16, 17), 10), ((15, 16, 14, 12), 12), ((15, 18, 14, 16), 13), ((15, 11, 18, 16), 12)]

# Each key gives successive longest-edge bisections of the triangle.
FACE_SCHEDULES = {
    "01": (6,8,6,6,8,6,8,8),
    "11": (2,4,8,2,4,2,4,8,8,2,4,8),
    "000": (8,2,4,8,2,4,8,2,4,8,2,4),
    "001": (2,4,8,2,4,2,4,8,8,2,4,8),
    "100": (10,10,14,14,4,4),
    "101": (2,4,8,2,4,2,4,8,8,2,4,8),
}


def check_face():
    root = ((0,1,0,0), (0,1,2,0), (0,1,0,2))
    root = tuple(tuple(Fraction(x,sum(v)) for x in v) for v in root)
    assert sum(Fraction(1,2**len(k)) for k in FACE_SCHEDULES)==1
    assert not any(a!=b and b.startswith(a) for a in FACE_SCHEDULES for b in FACE_SCHEDULES)
    perm = (3,0,1,2)
    donors = (3,3,1,2)
    faces = tuple((i,perm.index(donors[j]),n) for i,j in enumerate(perm)
                  for n in range(4) if perm[n] not in (j,donors[j]))
    words = bounds = 0
    for address,marks in FACE_SCHEDULES.items():
        tri = root
        for bit in address:
            def distance(pair):
                u,v = (tri[j] for j in pair)
                return sum((a-b)**2 for a,b in zip(u,v))
            i,j = max(combinations(range(3),2),key=distance)
            mid = tuple((a+b)/2 for a,b in zip(tri[i],tri[j]))
            tri = tuple(mid if k==(i,j)[int(bit)] else v for k,v in enumerate(tri))
        vertices = [tuple(int(v[j]*lcm(*(x.denominator for x in v))) for j in perm) for v in tri]
        # A repeated vertex uses the same simplex and the standard four-control verifier.
        vertices.append(vertices[0])
        schedule = tuple(tuple(perm.index(i) for i in range(4) if mark&(1<<i))
                         for mark in (*marks,1,1,1,1))
        w,b = check_cell(schedule,vertices,faces,late=perm.index(0))
        words += w
        bounds += b
    return len(FACE_SCHEDULES),words,bounds



def check_axis(points,schedules,cells,axis):
    tetrahedra = [tuple(points[i] for i in indices) for indices,_ in cells]
    for y in points:
        assert min(y)>=0 and sum(y)>0
        assert (2*y[3]>=y[2]) if axis==2 else (2*y[3]<=y[2])
    check_partition(tetrahedra,Fraction(2 if axis==2 else 1,3))
    donors = (3,3,1,2)
    p = donors[axis]
    perm = (axis, *(i for i in PLAYERS if i not in (axis,p)), p)
    faces = tuple((i,perm.index(donors[j]),k) for i,j in enumerate(perm)
                  for k in PLAYERS if perm[k] not in (j,donors[j]))
    words = gains = 0
    for vertices,(_,s) in zip(tetrahedra,cells):
        schedule = tuple(tuple(perm.index(i) for i in PLAYERS if mark&(1<<i))
                         for mark in schedules[s])
        w,b = check_cell(schedule,tuple(tuple(v[i] for i in perm) for v in vertices),faces)
        words += w
        gains += b
    return len(cells),words,gains


def check_sign_counts():
    def mask(v):
        return canonical([[0 if i==j else v[EDGES.index((i,j))] for j in PLAYERS]
                          for i in PLAYERS])
    surviving = {mask(v) for v in WITNESSES}
    earlier = {(2,1,8,4),(2,1,1,2),(2,1,1,4)}
    new = (2,4,1,1)
    counts = []
    for zeros,faces in boundary_faces(surviving):
        own = covered = remaining = 0
        for face in faces:
            locations = [i for i,x in enumerate(face) if x==0]
            chambers = set()
            for signs in product((-1,1),repeat=zeros):
                v = list(face)
                for j,x in zip(locations,signs):
                    v[j] = x
                chambers.add(mask(v))
            own += new in chambers
            covered += bool(chambers & (earlier|{new}))
            remaining += not bool(chambers & (earlier|{new}))
        counts.append((own,covered,remaining))
    assert counts==[(1,4,17),(6,13,33),(10,22,17),(5,10,0)]
    return counts


if __name__=='__main__':
    print('axis 2',*check_axis(AXIS2_RAW_POINTS,AXIS2_RAW_SCHEDULES,AXIS2_RAW_CELLS,2),flush=True)
    print('axis 3',*check_axis(AXIS3_POINTS,AXIS3_SCHEDULES,AXIS3_CELLS,3),flush=True)
    print('core face',*check_face(),flush=True)
    print('signs',check_sign_counts())
