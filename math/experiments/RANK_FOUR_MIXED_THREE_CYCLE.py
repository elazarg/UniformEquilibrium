"""Exact fourth-order certificate for census witness 5's entire strict sign class."""
from fractions import Fraction
from itertools import combinations, product
from math import lcm

from FIN4_SINGLETON_SIGN_CLASSES import EDGES, WITNESSES, boundary_faces, canonical
from RANK_FOUR_RECIPROCAL_CORE import PLAYERS, check_cell, check_partition, simplex_size
from RANK_FOUR_THREE_CYCLE_TAIL import (
    AXIS2_RAW_CELLS, AXIS2_RAW_POINTS, AXIS3_CELLS, AXIS3_POINTS,
)

SCHEDULES = (
    (1, 2, 8, 4, 1, 2, 8, 1, 4, 2, 8, 1, 2, 4, 8, 4),
    (1, 8, 2, 4, 1, 8, 2, 1, 4, 8, 2, 1, 8, 4, 2, 4),
    (1, 15, 1, 15, 14, 14),
    (2, 1, 8, 4, 2, 1, 8, 2, 4, 1, 8, 2, 1, 4, 8, 4),
    (2, 1, 4, 8, 2, 1, 2, 4, 1, 2, 8, 4, 1, 8, 4, 8),
    (2, 8, 1, 4, 2, 8, 1, 2, 4, 8, 1, 2, 8, 4, 1, 4),
    (2, 8, 4, 1, 2, 8, 2, 4, 8, 2, 1, 4, 8, 4, 1, 1),
    (8, 1, 2, 8, 4, 1, 2, 8, 1, 4, 2, 8, 4, 1, 2, 4),
    (8, 1, 4, 2, 8, 1, 4, 2, 8, 1, 4, 2, 8, 1, 4, 2),
    (8, 2, 1, 8, 4, 2, 1, 8, 2, 4, 1, 8, 4, 2, 1, 4),
    (8, 2, 4, 1, 8, 8, 2, 8, 2, 4, 2, 4, 4, 1, 1, 1),
    (8, 15, 15, 15, 7),
    (1, 2, 4, 8, 1, 2, 1, 4, 2, 1, 8, 4, 2, 8, 4, 8),
    (1, 1, 15, 15, 14, 14),
    (2, 4, 8, 2, 1, 2, 4, 8, 1, 4, 8, 2, 1, 4, 8, 1),
    (15, 15, 15, 15),
    (1, 15, 15, 15, 14),
    (2, 4, 8, 1, 2, 4, 8, 2, 4, 1, 8, 2, 4, 8, 1, 1),
    (4, 8, 2, 1, 4, 8, 2, 1, 4, 8, 2, 1, 4, 8, 2, 1),
    (2, 4, 1, 8, 2, 4, 1, 2, 4, 8, 2, 1, 4, 8, 1, 8),
    (2, 4, 1, 8, 2, 4, 2, 1, 2, 4, 1, 8, 4, 1, 8, 8),
    (6, 15, 6, 15, 9, 9),
    (1, 4, 2, 1, 8, 4, 2, 1, 4, 8, 2, 1, 4, 8, 2, 8),
    (4, 8, 2, 1, 4, 4, 8, 2, 4, 8, 1, 2, 8, 1, 2, 1),
    (4, 1, 2, 8, 4, 1, 2, 4, 8, 1, 2, 8, 4, 1, 2, 8),
    (4, 2, 1, 8, 4, 2, 1, 4, 8, 2, 4, 1, 2, 8, 1, 8),
    (4, 1, 8, 4, 2, 1, 4, 8, 1, 2, 8, 4, 2, 1, 8, 2),
    (4, 1, 8, 2, 4, 1, 4, 8, 1, 2, 8, 4, 2, 1, 8, 2),
    (4, 2, 8, 1, 4, 2, 4, 8, 1, 2, 4, 8, 2, 1, 8, 1),
    (4, 8, 2, 1, 4, 4, 8, 4, 2, 8, 2, 8, 1, 2, 1, 1),
)

CERTIFICATES_2 = (
    0,
    1,
    2,
    (('0', 3), ('10', 3), ('11', 4)),
    (('0', 5), ('10', 5), ('11', 6)),
    (('0', 6), ('10', 6), ('11', 6)),
    7,
    8,
    9,
    10,
    11,
    10,
    12,
    2,
    2,
    13,
    (('0', 4), ('10', 4), ('11', 4)),
    3,
    14,
    5,
    14,
    5,
    14,
    5,
    15,
    16,
    16,
    16,
    15,
    6,
    17,
    17,
    11,
    11,
    11,
    18,
    18,
    18,
)

CERTIFICATES_3 = (
    0,
    0,
    0,
    0,
    (('00', 3), ('01', 12), ('100', 12), ('101', 12), ('11', 4)),
    19,
    20,
    21,
    (('0', 22), ('100', 22), ('101', 23), ('110', 23), ('111', 23)),
    24,
    25,
    (('00', 26), ('01', 26), ('10', 23), ('110', 23), ('111', 23)),
    (('00', 27), ('01', 23), ('1', 23)),
    (('00', 23), ('01', 23), ('1', 23)),
    25,
    25,
    21,
    28,
    25,
    21,
    23,
    23,
    23,
    23,
    29,
    23,
)

DUPLICATED_DONOR_SCHEDULES = (
    (1, 2, 8, 4, 1, 2, 8, 1, 4, 2, 8, 1, 2, 4, 8, 4),
    (1, 8, 2, 4, 1, 8, 2, 1, 4, 8, 2, 1, 8, 4, 2, 4),
    (8, 1, 2, 8, 4, 1, 2, 8, 1, 4, 2, 8, 4, 1, 2, 4),
    (8, 15, 15, 15, 7),
    (1, 2, 4, 8, 1, 2, 1, 4, 8, 2, 1, 4, 8, 2, 4, 8),
    (3, 12, 3, 3, 12, 12, 3, 12),
    (1, 14, 1, 1, 14, 14, 1, 14),
    (15, 15, 15, 15),
    (1, 3, 7, 15, 14, 12, 8),
    (5, 15, 5, 15, 10, 10),
    (4, 1, 2, 8, 4, 1, 2, 4, 8, 1, 4, 2, 1, 8, 2, 8),
    (3, 15, 3, 15, 12, 12),
    (4, 1, 8, 2, 4, 1, 4, 8, 2, 1, 4, 8, 1, 2, 8, 2),
    (4, 8, 1, 2, 4, 4, 8, 1, 4, 8, 2, 1, 8, 2, 1, 2),
    (4, 8, 1, 2, 4, 4, 8, 4, 1, 8, 1, 8, 2, 1, 2, 2),
)

DUPLICATED_DONOR_CERTIFICATES_2 = (
    (('0', 0), ('1', 0)),
    1,
    1,
    None,
    None,
    None,
    2,
    2,
    None,
    None,
    3,
    None,
    (('00', 4), ('01', 5), ('1', 0)),
    (('0', 6), ('1', 1)),
    1,
    1,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    7,
    1,
    1,
    1,
    None,
    None,
    None,
    None,
    3,
    3,
    3,
    None,
    None,
    None,
)

DUPLICATED_DONOR_CERTIFICATES_3 = (
    8,
    9,
    9,
    9,
    None,
    None,
    None,
    None,
    10,
    9,
    11,
    12,
    9,
    9,
    None,
    None,
    None,
    None,
    None,
    None,
    13,
    14,
    13,
    None,
    None,
    None,
)


def normalized(row):
    return tuple(Fraction(x, sum(row)) for x in row)


def subcell(vertices, address):
    for bit in address:
        points = tuple(map(normalized, vertices))
        def squared_length(edge):
            a, b = edge
            return sum((u-v)**2 for u,v in zip(points[a],points[b]))
        a,b = max(combinations(PLAYERS, 2), key=squared_length)
        mid = tuple((u+v)/2 for u,v in zip(points[a],points[b]))
        den = lcm(*(v.denominator for v in mid))
        vertex = tuple(int(den*v) for v in mid)
        vertices = tuple(vertex if j==(a,b)[int(bit)] else v for j,v in enumerate(vertices))
    return vertices


def check_domain(reference, points, cells, certificates, volumes, totals, duplicated=False):
    assert len(cells)==len(certificates)
    base = [tuple(points[j] for j in indices) for indices,_ in cells]
    check_partition(base, Fraction(2 if reference==2 else 1, 3))
    donors = ((3,), (3,), (0,1), (2,)) if duplicated else ((3,), (3,), (1,), (0,2))
    schedules = DUPLICATED_DONOR_SCHEDULES if duplicated else SCHEDULES
    for vertices,cert in zip(base, certificates):
        assert all(min(v)>=0 and sum(v)>0 for v in vertices)
        if reference==2:
            assert all(2*v[3]>=v[2] for v in vertices)
            axis=2
        else:
            assert all(2*v[3]<=v[2] for v in vertices)
            axis = 2 if all(v[0]>=v[2] for v in vertices) else 3
            if axis==3:
                assert all(v[0]<=v[2] for v in vertices)
        if duplicated:
            if all(v[0]<=v[1] for v in vertices):
                assert cert is None
                continue
            assert all(v[0]>=v[1] for v in vertices)
            axis=reference
        primary = 1 if axis==2 else 2
        perm = (axis, *(j for j in PLAYERS if j not in (axis,primary)), primary)
        faces = tuple((a,perm.index(p),perm.index(n)) for a,i in enumerate(perm)
                      for p in donors[i] for n in PLAYERS if n!=i and n not in donors[i])
        protected = tuple(perm.index(p) for p in donors[axis])
        leaves = (('',cert),) if isinstance(cert,int) else cert
        addresses = [v for v,_ in leaves]
        assert len(set(addresses))==len(addresses)
        assert all(set(v)<={'0','1'} for v in addresses)
        assert not any(x!=y and y.startswith(x) for x in addresses for y in addresses)
        assert sum(Fraction(1,2**len(v)) for v in addresses)==1
        volumes[axis] += simplex_size(vertices)
        for address,selector in leaves:
            sub = subcell(vertices,address)
            schedule = tuple(tuple(perm.index(j) for j in PLAYERS if m&(1<<j))
                             for m in schedules[selector])
            words, inequalities = check_cell(schedule,tuple(tuple(v[j] for j in perm) for v in sub),
                                            faces,protected=protected)
            for j,number in enumerate((1,words,inequalities)):
                totals[axis][j] += number


def check_sign_counts(index=5):
    def mask(values):
        matrix = [[0]*4 for _ in PLAYERS]
        for (i,j),v in zip(EDGES,values):
            matrix[i][j]=v
        return canonical(matrix)
    strict = {mask(w) for w in WITNESSES}
    previous = {mask(WITNESSES[n-1]) for n in ((1,2,4,9) if index==5 else (1,2,4,5,9))}
    new = mask(WITNESSES[index-1])
    results=[]
    for ties,forms in boundary_faces(strict):
        own=extra=all_five=0
        for form in forms:
            empty=[j for j,x in enumerate(form) if x==0]
            ancestors=set()
            for fill in product((-1,1), repeat=ties):
                v=list(form)
                for j,x in zip(empty,fill):v[j]=x
                ancestors.add(mask(v))
            own+=new in ancestors
            extra+=new in ancestors and not (previous & ancestors)
            all_five+=bool((previous|{new}) & ancestors)
        results.append((own,extra,all_five))
    assert results==([(1,1,5),(6,4,17),(10,3,25),(5,0,10)] if index==5
                     else [(1,1,6),(3,2,19),(6,2,27),(4,0,10)])
    return results


if __name__=='__main__':
    totals={2:[0,0,0],3:[0,0,0]}
    volumes={2:Fraction(0),3:Fraction(0)}
    check_domain(2,AXIS2_RAW_POINTS,AXIS2_RAW_CELLS,CERTIFICATES_2,volumes,totals)
    check_domain(3,AXIS3_POINTS,AXIS3_CELLS,CERTIFICATES_3,volumes,totals)
    assert volumes=={2:Fraction(23,30),3:Fraction(7,30)}
    print('axis 2, axis 3',totals)
    print('own, newly covered, all five',check_sign_counts())


    totals={2:[0,0,0],3:[0,0,0]}
    volumes={2:Fraction(0),3:Fraction(0)}
    check_domain(2,AXIS2_RAW_POINTS,AXIS2_RAW_CELLS,DUPLICATED_DONOR_CERTIFICATES_2,
                 volumes,totals,duplicated=True)
    check_domain(3,AXIS3_POINTS,AXIS3_CELLS,DUPLICATED_DONOR_CERTIFICATES_3,
                 volumes,totals,duplicated=True)
    assert volumes=={2:Fraction(1,3),3:Fraction(1,6)}
    print('duplicated donors, axes 2 and 3',totals)
    print('own, newly covered, all six',check_sign_counts(6))
