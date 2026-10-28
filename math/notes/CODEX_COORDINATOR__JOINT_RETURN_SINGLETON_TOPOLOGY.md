# Singleton topology for the signed joint-return architecture

Owner: CODEX_COORDINATOR. Proved finite sign classification, ordinary mathematics, not Lean
checked. This concerns the prerequisites of one specified return architecture,
not equilibrium existence or an obstruction to more general joint/solo returns.
No higher-reward, physical-root, prefix or continuation guard is automatic.

## 1. Exact conclusions

Use the generic residual hypotheses and ten pointed observer templates of
`CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`, Sections 1–8. Thus every
column has a negative entry, Gamma is R0 of degree +1, det Gamma>0, its inverse
has a strictly positive column, there is a mutually negative reciprocal pair,
and no inverse-positive principal triple has a nonnegative outside inverse row.
The pointed form is H=[0,c;-r,B], with r=B1 and sum(c)=1.

A labeling has architecture A if

    beta=-Gamma02>0, f=Gamma20>0, k=Gamma03>0.

Architecture AG additionally requires g=-Gamma13>0, and AGH additionally
requires h=-Gamma23>0. Define AH by retaining h>0 and allowing g either sign.
No sign is imposed on e=Gamma32 or d=-Gamma30.

| Pointed observer template | A always | AG always | AGH always |
|---|---|---|---|
|1|yes|no|no|
|2|yes|no|no|
|3|no|no|no|
|4|yes|no|no|
|5|yes|yes|yes|
|6|yes|yes|no|
|7|yes|no|no|
|8|yes|yes|yes|
|9|yes|yes|no|
|10|yes|yes|no|

Here “always” quantifies over every numerical matrix in the indicated pointed
template satisfying the full residual restrictions, and allows every player
relabeling. Each “no” has an exact residual counterexample below.

More precisely, A and AH are equivalent on the residual class. They fail
exactly on the sign orbit consisting of two disjoint mutually positive pairs
and four mutually negative cross-pairs. In the printed template3 orientation,
this is precisely sign(r)=(-,+,+), sign(c)=(+,-,-). Thus allowing arbitrary g
repairs every other sign pattern while h>0 can be retained. Since the generic
stratum excludes g=0, only the two variants (g,h)=(+,+),(-,+) are needed.
The extra (-,+) variant is necessary, as the AG counterexamples demonstrate.

A small member of the exceptional sign orbit is

    Gamma=[0,3,-1,-1; 2,0,-1,-1; -1,-1,0,2; -1,-1,2,0].

It has det=4, inverse column0 equal to 1, and no opposite-sign reciprocal
pair. Consequently beta>0 and f>0 cannot hold together under any labeling.
This is only an obstruction to A: allowing other signs of beta or k can
produce legal joint/solo3 returns on particular higher-reward completions.

## 2. Finite proof and exact sharpness witnesses

The proof enumerates a conservative superset of possible sign data. For each
of the ten printed B sign words, assign signs to r and c. Reject only when:

- a same-sign B row forces the opposite row-sum sign;
- all r entries or all c entries are negative;
- H has a column with no negative entry or has no negative reciprocal pair;
- an eligible degree-test pair has both corresponding c entries positive;
- B is inverse-positive (template8) but every c entry is positive.

These are necessary consequences of the pointed form and residual conditions.
For the fourth test, both coefficients in D_ij are positive, so D_ij<0 forces
at least one of c_i,c_j to be negative. The last test follows from c B^-1
having a negative coordinate. No rejected sign assignment can be residual.
For every retained assignment test all 24 labelings directly.

The retained counts by template are (5,5,15,10,9,3,20,30,9,2); these count
formal sign assignments, not proven nonempty numerical cells. Zero failures
prove the universal entries in the table. Among all retained assignments,
A is equivalent to AH, and its sole failure is exactly the template3 sign
assignment displayed above. The following rational witnesses establish every
remaining negative entry. The six B coordinates are (12,13,21,23,31,32), and
H is reconstructed by r=B1 and H=[0,c;-r,B].

| Template | B coordinates | c | Failed architecture |
|---|---|---|---|
|1|(-1,-1,-1,-3,-1,4)|(-3,5,-1)|AG|
|2|(-1,-2,-2,-1,1,1)|(5,-3,-1)|AG|
|3|(-1,-1,-1,2,-1,2)|(3,-1,-1)|A|
|4|(-1,-1,-2,1,1,2)|(3,-1,-1)|AG|
|6|(-1,-1,1,-2,1,1)|(-1,3,-1)|AGH|
|7|(-2,1,-1,2,-1,3)|(3,1,-3)|AG|
|9|(-1,2,2,-1,1,1)|(-3,3,1)|AGH|
|10|(-1,2,3,1,1,1)|(-1,5,-3)|AGH|

Every witness has nonzero off-diagonal entries, nonzero principal determinants
of size at least two, and nonzero full inverse entries. Its determinant is
positive and inverse column0 is exactly 1. The exact verifier checks negative
columns, a negative pair, every eligible D_ij<0, and every passive-child test.
Principal nonsingularity and negative columns imply R0: a homogeneous support
of size at least two would give a principal kernel, and a singleton would
violate its negative column. The complete pointed degree formula then gives
degree +1. Thus the failures satisfy all the residual hypotheses, not merely
necessary sign approximations. Pivot0 is the least original strict pivot.

The following standalone standard-library code is the finite certificate.
It checks the entire sign census and all exact witnesses; no sampled or
floating-point calculation enters the proof.

```python
from itertools import product, permutations, combinations
from fractions import Fraction as Q

I = range(4)
P = list(permutations(I))
J = [(i, j) for i in range(3) for j in range(3) if i != j]
T = [(-1,-1,-1,-1,-1,1),(-1,-1,-1,-1,1,1),
     (-1,-1,-1,1,-1,1),(-1,-1,-1,1,1,1),
     (-1,-1,1,-1,1,-1),(-1,-1,1,-1,1,1),
     (-1,1,-1,1,-1,1),(-1,1,1,-1,-1,1),
     (-1,1,1,-1,1,1),(-1,1,1,1,1,1)]

def matrix(w):
    B = [[0]*3 for _ in range(3)]
    for (i,j), z in zip(J,w): B[i][j] = z
    return B

def det(A):
    n = len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
               * prod(A[i][p[i]] for i in range(n))
               for p in permutations(range(n)))

def prod(a):
    z = 1
    for t in a: z *= t
    return z

def sub(A,S): return [[A[i][j] for j in S] for i in S]
def inv(A):
    n = len(A); d = det(A)
    return [[Q((-1)**(i+j)*det([[A[a][b] for b in range(n) if b!=i]
                   for a in range(n) if a!=j]),d)
             for j in range(n)] for i in range(n)]

def kinds(H):
    a = [p for p in P if H[p[0]][p[2]]<0<H[p[2]][p[0]]
         and H[p[0]][p[3]]>0]
    g = [p for p in a if H[p[1]][p[3]]<0]
    gh = [p for p in g if H[p[2]][p[3]]<0]
    h = [p for p in a if H[p[2]][p[3]]<0]
    return tuple(map(bool,(a,g,gh,h)))

# Necessary sign filters only; they deliberately over-admit numerical data.
counts = []
for word in T:
    B = matrix(word); row = [0,0,0,0]
    for r,c in product(product((-1,1),repeat=3),repeat=2):
        if any(B[i][(i+1)%3]==B[i][(i+2)%3]!=r[i] for i in range(3)): continue
        if max(r)<0 or max(c)<0: continue
        H = [[0]+list(c)]+[[-r[i]]+B[i] for i in range(3)]
        if any(min(H[i][j] for i in I)>=0 for j in I): continue
        if not any(H[i][j]==H[j][i]==-1 for i,j in combinations(I,2)): continue
        eligible = [(i,j) for i,j in combinations(range(3),2)
                    if B[i][j]*B[j][i]>0 and r[i]==B[i][j] and r[j]==B[j][i]]
        if any(c[i]==c[j]==1 for i,j in eligible): continue
        # Only template8 has inverse-positive B; its failed passive row needs c<0 somewhere.
        if word==T[7] and min(c)>0: continue
        a,g,gh,h = kinds(H)
        row[0] += 1
        for j,z in enumerate((a,g,gh),1): row[j] += not z
        assert a == h
        if not a:
            assert word==T[2] and r==(-1,1,1) and c==(1,-1,-1)
            assert all(H[i][j]==H[j][i] for i,j in combinations(I,2))
            assert all(sum(H[i][j]>0 for j in I)==1 for i in I)
    counts.append(row)
assert counts == [[5,0,1,1],[5,0,2,2],[15,1,3,5],[10,0,2,2],
                  [9,0,0,0],[3,0,0,1],[20,0,7,9],[30,0,0,0],
                  [9,0,0,1],[2,0,0,1]]

# Exact residual counterexamples: (pointed template, observer word, outside row).
W = [(1,(-1,-1,-1,-3,-1,4),(-3,5,-1)),
     (2,(-1,-2,-2,-1,1,1),(5,-3,-1)),
     (3,(-1,-1,-1,2,-1,2),(3,-1,-1)),
     (4,(-1,-1,-2,1,1,2),(3,-1,-1)),
     (6,(-1,-1,1,-2,1,1),(-1,3,-1)),
     (7,(-2,1,-1,2,-1,3),(3,1,-3)),
     (9,(-1,2,2,-1,1,1),(-3,3,1)),
     (10,(-1,2,3,1,1,1),(-1,5,-3))]
for t,word,c in W:
    B=matrix(word); r=[sum(v) for v in B]
    H=[[0]+list(c)]+[[-r[i]]+B[i] for i in range(3)]
    assert tuple(1 if z>0 else -1 for z in word)==T[t-1]
    assert sum(c)==1 and all(r) and det(H)==det(B)>0
    assert all(H[i][j]!=0 for i in I for j in I if i!=j)
    assert all(det(sub(H,S))!=0 for n in (2,3,4) for S in combinations(I,n))
    V=inv(H)
    assert all(z!=0 for v in V for z in v) and all(V[i][0]==1 for i in I)
    assert all(any(H[i][j]<0 for i in I) for j in I)
    assert any(H[i][j]<0 and H[j][i]<0 for i,j in combinations(I,2))
    for i,j in combinations(range(3),2):
        D=Q(c[i]*r[j],B[j][i])+Q(c[j]*r[i],B[i][j])
        if B[i][j]*B[j][i]>0 and r[i]*B[i][j]>0 and r[j]*B[j][i]>0: assert D<0
    for S in combinations(I,3):
        U=inv(sub(H,S)); o=next(i for i in I if i not in S)
        if all(z>=0 for v in U for z in v):
            assert any(sum(H[o][S[i]]*U[i][j] for i in range(3))<0 for j in range(3))
    a,g,gh,h=kinds(H)
    assert not gh, (t,kinds(H))
    assert g == (t in (6,9,10))
    assert a == (t!=3)
print('PASS: exhaustive necessary sign census and all exact residual counterexamples.')
```

## 3. Scope, producer use, and previous obstructions

The positive-continuation direct-return proof can allow arbitrary g when its
literal prefix is legal and both quiet1 endpoint values are strictly positive:
all intermediate return annotations stay on their positive segment, and
subdivision makes every finite joining offer small enough. This explains the
role of the AH variant, but the topology theorem supplies neither positive
endpoints nor the required physical root. Any such producer must retain its
explicit raw guards. The finite-core construction with negative quiet1 values
may still use g>0 essentially; this census does not extend that construction.

The nearby complete-axis note already identifies a different template3 witness
with exactly one opposite-sign pair; it defeats the older two-opposite-pair
finite-core architecture but admits a signed-e direct return. The present
exception has no opposite-sign pair and survives every labeling of A itself.
The result is a full prerequisite classification, not a duplicate assertion
that the older architecture has one bad matrix. The residual partition's
one-pivot/no-child sign-orbit theorem is compatible with this classification;
its broader template7 also contains the multiple-pivot witness above.

Inspected sources: `CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`, Sections
1–8; its exact checker `CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py`;
`CODEX_COORDINATOR__COMPLETE_JOINING_EXCESS_AXIS.md`, Sections 3–4; and the
raw sign assumptions and comparison scope of the frozen
`CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`.
No Lean check is claimed.
