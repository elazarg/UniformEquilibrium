"""The fourth all-finite order test on the full asymmetric matched cone."""
from fractions import Fraction
from itertools import combinations
from math import gcd

from RANK_FOUR_RECIPROCAL_CORE import PLAYERS, check_cell, check_partition, simplex_size, volume

POINTS = [
    (0, 0, 1, 3),
    (0, 0, 1, 1),
    (0, 0, 3, 1),
    (0, 1, 1, 6),
    (0, 4, 7, 13),
    (0, 1, 3, 1),
    (0, 1, 1, 1),
    (0, 3, 3, 1),
    (1, 4, 4, 9),
    (1, 6, 6, 1),
    (1, 1, 1, 6),
    (1, 1, 6, 1),
    (1, 0, 6, 1),
    (1, 1, 2, 4),
    (13, 13, 13, 33),
    (1, 0, 1, 3),
    (1, 1, 1, 1),
    (1, 0, 1, 1),
]

SCHEDULES = [
    "2.1.3.0.2.1.3.2.0.1.3.2.0.1.3.0",
    "2.1.3.0.2.1.3.2.0.1.3.2.1.0.3.0",
    "2.1.3.0.2.1.3.2.0.1.3.02.1.3.0",
    "2.3.0.1.2.3.2.0.2.3.0.3.0.1.1.1",
    "2.3.0.1.2.3.2.0.3.2.1.0.3.1.0.1",
    "2.3.1.0.2.3.1.2.0.3.1.2.0.3.1.0",
    "2.3.1.0.2.3.1.2.0.3.1.2.3.0.1.0",
    "2.23.023.0123.013.01.1",
    "2.23.123.0123.013.01.0",
    "3.2.0.1.3.2.3.2.0.3.2.0.0.1.1.1",
    "3.2.0.1.3.2.3.2.0.3.12.0.1.0.1",
    "3.2.1.0.3.2.1.3.0.2.1.3.0.2.1.0",
    "3.2.1.0.3.2.1.3.2.0.1.3.2.0.1.0",
    "3.2.1.0.3.2.1.3.2.3.0.1.2.1.0.0",
    "3.2.1.3.0.2.1.3.2.0.1.3.0.2.1.0",
    "3.2.1.3.0.2.3.1.2.1.3.0.2.1.0.0",
    "3.2.01.3.2.3.2.3.01.2.01.01",
    "3.2.3.0.1.3.2.0.1.2.3.0.1.2.0.1",
    "123.0.123.123.0.0.123.0",
]

CELLS = [
    ((0, 1, 6, 16), 12),
    ((0, 1, 15, 16), 10),
    ((0, 3, 6, 10), 15),
    ((0, 4, 10, 13), 16),
    ((0, 10, 15, 13), 16),
    ((1, 2, 5, 11), 8),
    ((1, 2, 11, 12), 7),
    ((1, 5, 6, 16), 6),
    ((1, 5, 11, 16), 5),
    ((1, 11, 12, 17), 3),
    ((1, 11, 16, 17), 4),
    ((1, 15, 16, 17), 9),
    ((4, 6, 10, 13), 14),
    ((5, 6, 7, 9), 1),
    ((5, 6, 9, 16), 0),
    ((5, 9, 11, 16), 2),
    ((13, 6, 8, 14), 13),
    ((13, 6, 14, 16), 18),
    ((13, 8, 10, 14), 11),
    ((13, 10, 15, 16), 17),
]


def domain_size():
    """Build the vertices, facets and edges from the defining inequalities."""
    rows = [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1),(-1,0,0,1),
            (0,-1,1,0),(-1,0,1,0),(3,0,-1,3),(0,3,3,-1)]
    def dot(a,b):
        return sum(x*y for x,y in zip(a,b))
    def primitive(v):
        return tuple(x//gcd(*v) for x in v)
    vertices = set()
    for planes in combinations(rows,3):
        v = tuple(volume(planes+(tuple(int(k==i) for k in PLAYERS),)) for i in PLAYERS)
        if not any(v):
            continue
        if sum(v)<0:
            v = tuple(-x for x in v)
        if min(dot(r,v) for r in rows)>=0:
            vertices.add(primitive(v))
    assert all(min(dot(r,x) for r in rows)>=0 and sum(x)>0 for x in POINTS)
    facets = set()
    for normal in rows:
        facet = frozenset(v for v in vertices if dot(v,normal)==0)
        if len(facet)>=3:
            facets.add(facet)
    # Cone the polygonal facets from an interior point, and triangulate each
    # facet by joining its edges to the sum of its homogeneous vertices.
    center = tuple(map(sum,zip(*vertices)))
    total = Fraction(0)
    for face in facets:
        middle = tuple(map(sum,zip(*face)))
        for other in facets-{face}:
            edge = face & other
            assert len(edge)<=2
            if len(edge)==2:
                total += simplex_size((center,middle,*edge))
    return total


if __name__=="__main__":
    tetrahedra = [tuple(POINTS[i] for i in ids) for ids,k in CELLS]
    check_partition(tetrahedra,domain_size())
    schedules = [tuple(tuple(map(int,s)) for s in r.split(".")) for r in SCHEDULES]
    faces = tuple((i,p,n) for i,p in enumerate((3,2,1,0)) for n in PLAYERS if n not in (i,p))
    words = bounds = 0
    for (ids,k),vertices in zip(CELLS,tetrahedra):
        w,b = check_cell(schedules[k], vertices,faces)
        words += w
        bounds += b
    print(len(CELLS),"tetrahedra,",words,"weighted words,",bounds,"exact Bernstein inequalities")
