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


def negative_axes(g, positive):
    """Classify negative and nonpositive inverse columns by cofactor interpolation."""
    strict, weak = set(), set()
    for pivot in positive:
        vertices = []
        for i in I:
            plus = [j for j in I if g[i][j]>0]
            minus = [j for j in I if g[i][j]<0]
            if i==pivot:
                minus.append(None)
            vertices.append([[int(j==p)-int(j==n) for j in I] for p in plus for n in minus])
        for h in set(I)-positive-strict:
            # Row h is deleted from each numerator in inverse column h.
            choices = [rows if i!=h else rows[:1] for i,rows in enumerate(vertices)]
            values = list(zip(*(column_numerators(rows,h) for rows in product(*choices))))
            if all(max(v)<=0 for v in values):
                weak.add(h)
                if all(min(v)<0 for v in values):
                    strict.add(h)
    return strict, weak-strict


def strict_negative_columns(g):
    return {h for h in I if min(column_numerators(g,h))<0}


SUPPLEMENTARY = {
    2: (
        (-2,-2,4,-1,-3,1,-1,4,-4,-4,1,-2),
    ),
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
    10: (
        (-1,-4,4,-2,4,-1,-1,3,-3,3,-1,3),
    ),
    15: (
        (-2,-3,3,-3,4,2,4,-1,-1,-1,-2,3),
    ),
    17: (
        (-4,-2,4,-1,4,2,4,-1,-1,1,-3,4),
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


def mixed(g,owners):
    return {h for h in owners if min(column_numerators(g,h))<0<max(column_numerators(g,h))}


def weak_sharpness(face,selected,negative):
    _,_,g=calibrate(face)
    assert all(min(column_numerators(g,h))>0 for h in selected)
    absent=set(I)-selected-strict_negative_columns(g)
    remaining = set(I)-negative-selected-mixed(g,I)
    if not (absent or remaining):
        return
    signs=matrix(face)
    for bound,pivot in product((3,4),sorted(selected)):
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
            gains=mixed(candidate,remaining)
            if (losses or gains) and valid_matrix(candidate,pivot):
                assert all(min(column_numerators(candidate,h))>0 for h in selected)
                absent-=losses
                remaining-=gains
                if not (absent or remaining):
                    return
    raise AssertionError((face,absent,remaining))


def main():
    expected=('02','02','02','123','2','2','02','2','0123','023','013','013','13',
              '01','12','2','12','2','2','12','2')
    strict = set()
    for index,(row,word) in enumerate(zip(WITNESSES,expected),1):
        g=matrix(row)
        axes=positive_axes(g)
        assert axes==set(map(int,word))
        strict.add(canonical(g))
        neg,weak=negative_axes(g,axes)
        assert not weak and neg==({1:{1},3:{1},4:{0},11:{2},12:{2}}.get(index,set()))
        excluded=set(); two_signs=set()
        for candidate in (row,*SUPPLEMENTARY.get(index,())):
            assert all(a*b>0 for a,b in zip(candidate,row))
            a=matrix(candidate)
            assert actual_axis(a,canonical(g)) and not has_triangle(a)
            excluded |= strict_negative_columns(a)
            two_signs |= mixed(a,I)
        assert excluded==set(I)-axes and two_signs==set(I)-neg-axes
    for zeros,faces in boundary_faces(strict):
        sizes=Counter(); new_owners=0; new_faces=0
        signed_sizes=Counter(); negative_count=0; weak_count=0
        for face in faces:
            new,old=refined_sets(face)
            neg,weak=negative_axes(matrix(face),new)
            assert len(neg|weak)<=1
            weak_count+=bool(weak)
            negative_count+=bool(neg)
            signed_sizes[len(new|neg)]+=1
            if zeros:
                weak_sharpness(face,new,neg|weak)
            sizes[len(new)]+=1
            new_owners += len(new-old)
            new_faces += new!=old
        summary=([sizes[n] for n in (1,2,3,4)],new_faces,new_owners)
        expected_summaries=(([7,9,4,1],6,8),([9,20,16,1],15,19),
                            ([3,15,18,3],11,13),([0,3,6,1],2,2))
        assert summary==expected_summaries[zeros]
        signed = ([signed_sizes[n] for n in (1,2,3,4)], negative_count)
        expected_signed=(([7,7,3,4],5),([9,11,13,13],21),([3,11,9,16],17),([0,3,3,4],3))
        assert signed==expected_signed[zeros] and weak_count==(0,0,8,6)[zeros]
        print(zeros,*summary,*signed,weak_count)


if __name__=='__main__':
    main()
