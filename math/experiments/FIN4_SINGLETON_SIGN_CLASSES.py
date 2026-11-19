"""Exact singleton sign and tie classification, with integer calibrations."""
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

def sign_orbit(entries):
    rows = [[0]*4 for _ in I]
    for (i,j), value in zip(EDGES, entries):
        rows[i][j] = value
    return {tuple(rows[p[i]][p[j]] for i,j in EDGES) for p in PERMS}

def boundary_faces(surviving):
    """A zero sign is allowed only if both strict refinements are allowed."""
    faces = set()
    for mask in surviving:
        rows = sign_matrix(mask)
        faces.update(sign_orbit(tuple(rows[i][j] for i,j in EDGES)))
    expected = [(435,21), (1104,46), (900,39), (240,10)]
    for zeros, counts in enumerate(expected):
        representatives = sorted({min(sign_orbit(face)) for face in faces})
        assert (len(faces), len(representatives)) == counts
        yield zeros, representatives
        next_faces = set()
        for face in faces:
            for k, value in enumerate(face):
                if value == 1 and face[:k] + (-1,) + face[k+1:] in faces:
                    next_faces.add(face[:k] + (0,) + face[k+1:])
        faces = next_faces
    assert not faces

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

TARGET=(19,97,877,2287)


def admits_positive_pair_kernel(G,i,j):
    """Check a homogeneous solution positive on a pair with both entries zero."""
    lower=Fraction(0)
    upper=None
    for k in I:
        if k in (i,j):
            continue
        a,b=G[k][i],G[k][j]
        if a==0:
            if b<0:
                return False
        elif a>0:
            lower=max(lower,Fraction(-b,a))
        else:
            bound=Fraction(-b,a)
            upper=bound if upper is None else min(upper,bound)
    return upper is None or (upper>0 and lower<=upper)


def valid_matrix(G,h):
    if det(G)<=0 or sum(G[h])<=0 or any(sum(G[i])!=0 for i in I if i!=h):
        return False
    if any(min(col)>=0 for col in zip(*G)) or any(row.count(0)>2 for row in G):
        return False
    # A positive triangle control needs opposite strict signs on each active row.
    # The row-zero bound excludes double-zero active rows. Two zero arc entries
    # cannot be used for switching, by the all-matrices path theorem.
    if has_triangle(G):
        return False
    for p in permutations(I):
        if all(G[i][j]<=0<=G[j][i] and G[i][j]!=G[j][i] for i,j in zip(p,p[1:]+p[:1])):
            return False
    for i,j in combinations(I,2):
        if G[i][j]==G[j][i]==0 and admits_positive_pair_kernel(G,i,j):
            return False
    index=0
    for size in (2,3,4):
        for S in combinations(I,size):
            block=[[G[i][j] for j in S] for i in S]
            d=det(block)
            # The only other possible nonzero homogeneous support is a triple
            # with zero determinant and with a zero or mixed-sign row at every i.
            if size==3 and d==0 and all(min(row)<0<max(row) or not any(row) for row in block):
                return False
            if any(max(G[i][j] for j in S)<=0 for i in I):
                continue  # positive target impossible on this support
            nums=[det([[TARGET[i] if k==j else G[i][k] for k in S] for i in S]) for j in S]
            if d==0:
                if not any(nums):
                    return False  # inconclusive range check
                continue
            if 0 in nums:
                return False  # require a regular, directly priced target
            if any(a*d<0 for a in nums):
                continue
            slacks=[(sum(G[i][j]*a for j,a in zip(S,nums))-d*TARGET[i])*d for i in I if i not in S]
            if 0 in slacks:
                return False
            if all(s>0 for s in slacks):
                index+=1 if d>0 else -1
    return index==1


def calibrate(pattern):
    sign=dict(zip(EDGES,pattern))
    for bound in (2,3):
        for h in I:
            choices=[]
            for i in I:
                cols=[j for j in I if i!=j and sign[i,j]]
                rows=[]
                for magnitudes in product(range(1,bound+1),repeat=len(cols)):
                    row=[0]*4
                    for j,m in zip(cols,magnitudes):
                        row[j]=sign[i,j]*m
                    if (sum(row)>0 if i==h else sum(row)==0):
                        rows.append(row)
                choices.append(rows)
            for G in product(*choices):
                if valid_matrix(G,h):
                    return bound,h,G
    raise ArithmeticError(f'No small calibration on {pattern}')


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
    for zeros, representatives in boundary_faces(surviving):
        if zeros:
            for pattern in representatives:
                bound, _, _ = calibrate(pattern)
                assert zeros < 3 or bound == 2
        print(f'{zeros} singleton ties: {len(representatives)} sign orbits.')
    print('Exact labeled/unlabeled counts: 600/31, 591/29, 459/22, 435/21.')
    print('Surviving row masks:',sorted(surviving))

if __name__=='__main__':
    main()
