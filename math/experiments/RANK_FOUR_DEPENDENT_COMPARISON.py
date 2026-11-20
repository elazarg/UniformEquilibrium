"""Verify the fourth order test on the entire seventh singleton chamber."""
from fractions import Fraction
from itertools import combinations_with_replacement

from RANK_FOUR_RECIPROCAL_CORE import CELLS, PLAYERS, POINTS, check_cell, check_cover
from RANK_FOUR_MIXED_THREE_CYCLE import subcell


# Each hexadecimal digit records the owners at a training date.
SCHEDULES = (
    "8412848148214212",
    "8241824821482411",
    "ccff33",
    "cfcf33",
    "8241828421842141",
    "2481248214812481",
    "2841284218428141",
    "2481248214821481",
    "6fff9",
    "4fffb",
    "2184218421842184",
    "2148214821482148",
    "22ffdd",
    "1248121428142848",
    "1284128412841284",
    "1248121421842848",
    "1248124812481248",
    "2841284128412841",
    "8899336644",
    "8124881821124244",
)
CERTIFICATES = (
    (0, 0, 1, 2, 2, 3, 3, 3, 0, 1, 3, 3, 4, 5, 6, 7, 3, 8, 4, 9, 9, 9, 9),
    (10, 11, 12, [('', 13)], 13, [('', 13)], 14, 15, 16, 1, [('', 13)], [('', 10)], 4, [('00', 17), ('010', 18), ('0110', 19), ('01110', 19), ('01111', 17), ('1', 17)], [('0', 1), ('10', 1), ('11', 1)], [('', 1)], [('', 13)], [('', 0)], 4, [('', 13)], 9, 9, 9),
)


def price_cap(vertices):
    upper = Fraction(0)
    for u, v in combinations_with_replacement(vertices, 2):
        num = (3*u[1]-u[0])*v[2] + (3*v[1]-v[0])*u[2]
        den = (u[0]+u[1]+u[3])*v[0] + (v[0]+v[1]+v[3])*u[0]
        if den:
            upper = max(upper, Fraction(num, den))
        else:
            assert num == 0
    return upper / (1 + upper)


def check():
    check_cover()
    donors = ((3,), (3,), (0, 1), (1,))
    faces = tuple((i,p,n) for i in PLAYERS for p in donors[i]
                  for n in PLAYERS if n!=i and n not in donors[i])
    totals = [0, 0, 0]
    for reflected, table in enumerate(CERTIFICATES):
        assert len(table)==len(CELLS)
        for ((indices, _), cert) in zip(CELLS, table):
            cell = tuple(POINTS[k] for k in indices)
            if reflected:
                cell = tuple(tuple(v[i] for i in (2,3,0,1)) for v in cell)
            leaves = [('',cert)] if isinstance(cert,int) else cert
            addresses = [s for s,_ in leaves]
            assert len(set(addresses))==len(addresses)
            assert all(set(s)<={'0','1'} for s in addresses)
            assert not any(a!=b and b.startswith(a) for a in addresses for b in addresses)
            assert sum(Fraction(1,2**len(s)) for s in addresses)==1
            for s,w in leaves:
                vertices = subcell(cell,s)
                priced = faces
                if not isinstance(cert,int):
                    assert reflected
                    q = price_cap(vertices)
                    mixture = ((0,q.numerator), (2,q.denominator-q.numerator))
                    priced = tuple(f for f in faces if f[0]!=1) + ((1,3,2),(1,3,mixture))
                schedule = tuple(tuple(i for i in PLAYERS if int(m,16)&(1<<i))
                                 for m in SCHEDULES[w])
                words, gains = check_cell(schedule, vertices, priced)
                for i, value in enumerate((1,words,gains)):
                    totals[i] += value
    return totals


if __name__=="__main__":
    print("tetrahedra, weighted words, exact gains", check())
