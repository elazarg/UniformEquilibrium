"""Exact matrix screening for strict singleton sign cones, with integer calibrations."""
from collections import Counter
from itertools import combinations, permutations, product
from math import prod
from fractions import Fraction

I = tuple(range(4))
EDGES = [(i,j) for i in I for j in I if i != j]
PERMS = list(permutations(I))
TERMS = {n: [(p, (-1)**sum(p[i]>p[j] for i,j in combinations(range(n),2)))
             for p in permutations(range(n))] for n in (2,3,4)}

def det(A):
    return sum(s * prod(row[k] for row,k in zip(A,p)) for p,s in TERMS[len(A)])

def canonical(G):
    return min(tuple(sum(1 << j for j in I if G[p[i]][p[j]]>0) for i in I) for p in PERMS)

def sign_matrix(mask):
    return [[0 if i==j else 1 if mask[i] & (1<<j) else -1 for j in I] for i in I]

def axis_vertices(G,h):
    options=[]
    for i in I:
        pos=[j for j in I if G[i][j]>0]
        neg=[j for j in I if G[i][j]<0]
        if i==h:
            options.append([tuple(int(k==pos[0]) for k in I)])
        else:
            options.append([tuple(int(k==p)-int(k==n) for k in I) for p in pos for n in neg])
    return list(product(*options))

def forbidden_pairs(G,h):
    return [(i,j) for i,j in combinations((k for k in I if k!=h),2)
            if G[i][j]==G[j][i]==-G[i][h]==-G[j][h]]

def levels(mask):
    G=sign_matrix(mask)
    tree=False
    for h in I:
        vertices=axis_vertices(G,h)
        D=[det(V) for V in vertices]
        if max(D)<=0:
            continue
        tree=True
        for i,j in forbidden_pairs(G,h):
            if G[h][i]==G[h][j]==1:
                break
            if sum(v>0 for v in G[h])==1 and G[h][i]!=G[h][j]:
                E=[-G[h][i]*abs(V[i][j]*V[j][h])-G[h][j]*abs(V[j][i]*V[i][h]) for V in vertices]
                if max(a+b for a,b in zip(D,E))<=0:
                    break
        else:
            return True,True
    return tree,False

def actual_axis(G,mask):
    if canonical(G)!=mask or det(G)<=0:
        return False
    triple={o:det([[G[i][j] for j in I if j!=o] for i in I if i!=o]) for o in I}
    if min(abs(z) for z in triple.values())==0:
        return False
    sign=[[int(v>0)-int(v<0) for v in row] for row in G]
    for h in I:
        if not all((-1)**(h+i)*det([[G[k][l] for l in I if l!=i] for k in I if k!=h])>0 for i in I):
            continue
        if all(triple[next(o for o in I if o not in (h,i,j))]>0 for i,j in forbidden_pairs(sign,h)):
            return True
    return False

def has_triangle(G):
    for p,q,r in permutations(I,3):
        if p!=min(p,q,r) or any(G[j][i]<=0 or G[i][j]>=0 for i,j in [(p,q),(q,r),(r,p)]):
            continue
        a=Fraction(-G[r][q],G[r][p]); c=Fraction(-G[p][q],G[p][r])
        rho=-G[q][r]*c/(G[q][p]*a)
        if rho>=1:
            continue
        o=6-p-q-r
        initial=a*G[o][p]+G[o][q]+c*G[o][r]
        if min(initial,initial-(1-rho)*a*G[o][p],initial-(1-rho)*(a*G[o][p]+G[o][q]))>=0:
            return True
    return False

# Off-diagonal entries in row-major order. Sign representatives are checked after relabeling.
WITNESSES = [
    (-1, -1, 3, -1, -1, 2, -1, 2, -1, -1, -1, 2),
    (-2, -1, 4, -1, -2, 3, -1, 2, -1, -3, 4, -1),
    (-1, -1, 2, -1, -1, 2, -1, 2, -1, -2, 1, 2),
    (-1, -2, 3, -2, -1, 3, -1, 3, -1, 3, -2, -1),
    (-1, -1, 2, -1, -1, 2, -1, 2, -1, 1, -2, 2),
    (-1, -1, 2, -1, -1, 2, 1, 1, -1, -1, -1, 2),
    (-2, -1, 3, -1, -2, 3, 1, 1, -1, -2, 3, -1),
    (-1, -1, 2, -1, -1, 2, 2, 1, -1, -2, 1, 1),
    (-1, -1, 3, -1, 2, -1, -1, 2, -1, 2, -1, -1),
    (-1, -1, 3, -1, 2, -1, -1, 2, -1, 1, -2, 1),
    (-1, -1, 3, -1, 2, -1, -2, 1, 1, -1, 2, -1),
    (-1, -2, 3, -1, 3, -1, -3, 1, 2, -3, 2, 1),
    (-1, -1, 2, -1, 2, -1, -2, 1, 1, 1, 1, -1),
    (-1, -2, 3, -1, 3, -2, 1, 3, -3, 2, 1, -3),
    (-1, -1, 2, -1, 1, 1, 2, -1, -1, -1, -1, 2),
    (-2, -1, 3, -3, 1, 2, 3, -1, -1, -3, 1, 2),
    (-1, -1, 2, -1, 1, 1, 2, -1, -1, 1, -2, 1),
    (-1, -1, 2, -2, 1, 2, 1, 1, -2, -1, -1, 2),
    (-2, -1, 3, -3, 1, 2, 1, 1, -1, -3, 1, 2),
    (-1, -1, 3, -2, 1, 1, 1, 1, -2, 2, -1, -1),
    (-1, -1, 2, -1, 2, 1, 1, 1, -2, 1, -2, 1),
]

def main():
    counts=Counter()
    for vals in product((-1,1),repeat=12):
        G=[[0]*4 for _ in I]
        for (i,j),v in zip(EDGES,vals):
            G[i][j]=v
        if not all(min(row)<0<max(row) for row in G) or not all(min(col)<0 for col in zip(*G)):
            continue
        if not any(G[i][j]==G[j][i]==-1 for i,j in EDGES):
            continue
        if any(all(G[p[k]][p[(k+1)%4]]>0>G[p[(k+1)%4]][p[k]] for k in I)
               and G[p[0]][p[2]]==G[p[2]][p[0]]==-1
               and max(G[p[1]][p[3]],G[p[3]][p[1]])>0 for p in PERMS):
            continue
        counts[canonical(G)]+=1
    assert (sum(counts.values()),len(counts))==(600,31)
    flags={m:levels(m) for m in counts}
    tree={m for m,(t,d) in flags.items() if t}
    degree={m for m,(t,d) in flags.items() if d}
    assert (sum(counts[m] for m in tree),len(tree))==(591,29)
    assert (sum(counts[m] for m in degree),len(degree))==(459,22)
    special=canonical([[0,-1,-1,1],[-1,0,1,-1],[1,-1,0,1],[1,1,-1,0]])
    assert special in degree
    surviving=degree-{special}
    assert (sum(counts[m] for m in surviving),len(surviving))==(435,21)
    witnessed=set()
    for vals in WITNESSES:
        G=[[0]*4 for _ in I]
        for (i,j),v in zip(EDGES,vals):
            G[i][j]=v
        mask=canonical(G)
        assert actual_axis(G,mask) and not has_triangle(G)
        assert not any(all(G[p[(k+1)%4]][p[k]]>0>G[p[k]][p[(k+1)%4]] for k in I) for p in PERMS)
        witnessed.add(mask)
    assert surviving==witnessed
    print('Exact labeled/unlabeled counts: 600/31, 591/29, 459/22, 435/21.')
    print('Surviving row masks:',sorted(surviving))

if __name__=='__main__':
    main()
