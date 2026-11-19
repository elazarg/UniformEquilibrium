"""Exact axes forced by the strict singleton tests and their weak-face extensions."""
from collections import Counter
from itertools import permutations, product

from FIN4_SINGLETON_SIGN_CLASSES import (EDGES, I, WITNESSES, actual_axis, boundary_faces,
                                         calibrate, canonical, det, has_triangle, valid_matrix)


def matrix(entries):
    g = [[0]*4 for _ in I]
    for (i,j), v in zip(EDGES,entries):
        g[i][j] = v
    return g


def positive_axes(g):
    """Only the full support can supply degree +1 unless a surviving triple can."""
    selected = set(I)
    for i,h,j,o in permutations(I):
        if not (g[i][j]>0>g[j][i] and g[i][h]<0<g[j][h]):
            continue
        if max(g[h][i],g[h][j])<0 or max(g[o][i],g[o][h],g[o][j])<0:
            continue
        ordered = [g[o][t]>0 for t in (i,h,j)]
        if g[h][i]>0>g[h][j] and ordered==sorted(ordered):
            continue
        selected.discard(h)
    return selected


def prior_axes(g):
    axes = set()
    for u,v,a,b in permutations(I):
        if (max(g[u][v],g[v][u])<0 and min(g[u][b],g[v][b],g[b][a])>0>g[a][b]
                and min(g[u][a],g[v][a])<0):
            axes.add(a)
        if (g[u][v]*g[v][u]>0 and all(g[c][t]*g[u][v]<0 for c in (u,v) for t in (a,b))):
            axes.add(a)
        # The positive leaf 0 for witnesses 1 and 3, in any simultaneous relabeling.
        if (g[u][b]>0 and g[v][b]>0 and g[a][v]>0 and g[b][a]>0
                and max(g[u][v],g[u][a],g[v][u],g[v][a],g[a][u],g[a][b],g[b][u])<0):
            axes.add(u)
        # The reciprocal member b named by v on the two-step dependent chain.
        donors={u:b,v:b,a:v,b:u}
        if all((g[i][j]>0)==(j==donors[i]) for i,j in EDGES):
            axes.add(b)
    return axes


def column_numerators(g,h):
    return [(-1)**(h+i)*det([[g[r][c] for c in I if c!=i] for r in I if r!=h]) for i in I]


def strict_negative_columns(g):
    return {h for h in I if min(column_numerators(g,h))<0}


SUPPLEMENTARY = {
    3: (
        (-2, -4, 2, -3, -4, 1, -1, 4, -1, -4, 1, 4),
    ),
    5: (
        (-1, -4, 3, -3, -1, 4, -3, 3, -1, 2, -1, 4),
        (-1, -1, 3, -3, -2, 4, -2, 3, -2, 4, -4, 4),
    ),
    6: (
        (-2, -2, 4, -4, -3, 3, 3, 4, -1, -2, -2, 3),
    ),
    7: (
        (-1, -1, 3, -1, -4, 2, 2, 2, -2, -4, 2, -2),
    ),
    8: (
        (-4, -1, 3, -1, -4, 3, 4, 4, -2, -1, 3, 4),
    ),
    13: (
        (-4, -4, 3, -1, 4, -1, -2, 4, 1, 2, 1, -2),
    ),
    14: (
        (-1, -2, 2, -3, 4, -2, 2, 4, -1, 4, 1, -1),
    ),
    16: (
        (-3, -1, 2, -2, 1, 4, 3, -2, -1, -1, 2, 4),
    ),
    18: (
        (-2, -1, 4, -2, 2, 1, 4, 2, -2, -2, -4, 3),
    ),
    20: (
        (-1, -4, 4, -2, 4, 3, 2, 4, -4, 3, -2, -4),
    ),
    21: (
        (-1, -3, 3, -4, 3, 2, 3, 3, -2, 2, -2, 1),
        (-3, -3, 4, -3, 3, 4, 1, 2, -1, 1, -2, 3),
    ),
}


def refined_sets(face):
    zeros = [i for i,v in enumerate(face) if v==0]
    new, old = set(), set()
    for signs in product((-1,1), repeat=len(zeros)):
        values = list(face)
        for i,s in zip(zeros,signs):
            values[i] = s
        g = matrix(values)
        current, old_current = positive_axes(g), prior_axes(g)
        assert old_current<=current
        new |= current
        old |= old_current
    return new, old


def weak_sharpness(face,selected):
    _,_,g=calibrate(face)
    assert all(min(column_numerators(g,h))>0 for h in selected)
    absent=set(I)-selected-strict_negative_columns(g)
    if not absent:
        return
    pivot=min(selected)
    signs=matrix(face)
    for bound in (3,4):
        choices=[]
        for i in I:
            peers=[j for j in I if signs[i][j]]
            rows=[]
            for mags in product(range(1,bound+1),repeat=len(peers)):
                row=[0]*4
                for j,m in zip(peers,mags):
                    row[j]=signs[i][j]*m
                if (sum(row)>0 if i==pivot else sum(row)==0):
                    rows.append(row)
            choices.append(rows)
        for candidate in product(*choices):
            if det(candidate)<=0:
                continue
            losses={h for h in absent if min(column_numerators(candidate,h))<0}
            if losses and valid_matrix(candidate,pivot):
                assert all(min(column_numerators(candidate,h))>0 for h in selected)
                absent-=losses
                if not absent:
                    return
    raise AssertionError((face,absent))


def main():
    expected=('02','02','02','123','2','2','02','2','0123','023','013','013','13',
              '01','12','2','12','2','2','12','2')
    strict = set()
    for index,(row,word) in enumerate(zip(WITNESSES,expected),1):
        g=matrix(row)
        axes=positive_axes(g)
        assert axes==set(map(int,word))
        strict.add(canonical(g))
        excluded=set()
        for candidate in (row,*SUPPLEMENTARY.get(index,())):
            assert all(a*b>0 for a,b in zip(candidate,row))
            a=matrix(candidate)
            assert actual_axis(a,canonical(g)) and not has_triangle(a)
            excluded |= strict_negative_columns(a)
        assert excluded==set(I)-axes
    for zeros,faces in boundary_faces(strict):
        sizes=Counter(); new_owners=0; new_faces=0
        for face in faces:
            new,old=refined_sets(face)
            if zeros:
                weak_sharpness(face,new)
            sizes[len(new)]+=1
            new_owners += len(new-old)
            new_faces += new!=old
        summary=([sizes[n] for n in (1,2,3,4)],new_faces,new_owners)
        expected_summaries=(([7,9,4,1],6,8),([9,20,16,1],15,19),
                            ([3,15,18,3],11,13),([0,3,6,1],2,2))
        assert summary==expected_summaries[zeros]
        print(zeros,*summary)


if __name__=='__main__':
    main()
