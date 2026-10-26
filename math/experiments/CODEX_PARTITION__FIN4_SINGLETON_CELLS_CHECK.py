"""Exact checks for the Fin4 pointed singleton-matrix partition. Stdlib only."""
from fractions import Fraction as Q
from itertools import combinations, permutations, product


def det(a):
 n=len(a)
 return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
            * prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))

def prod(xs):
 out=Q(1)
 for x in xs:out*=x
 return out

def inverse(a):
 n=len(a);v=[[Q(x) for x in row]+[Q(i==j) for j in range(n)] for i,row in enumerate(a)]
 for j in range(n):
  k=next(i for i in range(j,n) if v[i][j]);v[j],v[k]=v[k],v[j]
  z=v[j][j];v[j]=[x/z for x in v[j]]
  for i in range(n):
   if i!=j:
    z=v[i][j];v[i]=[x-z*y for x,y in zip(v[i],v[j])]
 return [row[n:] for row in v]

def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def submatrix(a,S):return [[a[i][j] for j in S] for i in S]
def flat(a):return tuple(x for row in a for x in row)
positions=[(i,j) for i in range(3) for j in range(3) if i!=j]
def matrix(word):
 a=[[Q(0)]*3 for _ in range(3)]
 for (i,j),v in zip(positions,word):a[i][j]=Q(v)
 return a

def canonical(word):
 a=matrix(word)
 return min(tuple(a[p[i]][p[j]] for i,j in positions) for p in permutations(range(3)))

expected=[(-1,-1,-1,-1,-1,1),(-1,-1,-1,-1,1,1),
 (-1,-1,-1,1,-1,1),(-1,-1,-1,1,1,1),(-1,-1,1,-1,1,-1),
 (-1,-1,1,-1,1,1),(-1,1,-1,1,-1,1),(-1,1,1,-1,-1,1),
 (-1,1,1,-1,1,1),(-1,1,1,1,1,1),(1,1,1,1,1,1)]
orbits={canonical(word) for word in product((-1,1),repeat=6)}
assert len(orbits)==16
positive_possible=sorted(w for w in orbits if max(w[0]*w[3]*w[4],w[1]*w[2]*w[5])>0)
assert positive_possible==expected

# One exact generic witness for each of the ten non-all-positive templates.
witnesses=[
 ((-1,-1,-2,-1,-2,3),(1,-1,1)),
 ((-1,-1,-1,-1,2,3),(1,-2,2)),
 ((-1,-1,-1,2,-2,3),(3,-3,1)),
 ((-1,-1,-2,1,1,2),(3,-1,-1)),
 ((-1,-1,1,-2,2,-1),(-1,1,1)),
 ((-1,-1,1,-2,1,1),(-1,3,-1)),
 ((-1,2,-1,2,-3,1),(1,1,-1)),
 ((-1,2,1,-2,-1,3),(-1,-1,3)),
 ((-1,2,1,-2,1,3),(-1,-1,3)),
 ((-1,2,3,1,1,1),(-1,5,-3)),
]
child_counts=[]
for expected_sign,(word,c) in zip(expected,witnesses):
 B=matrix(word);c=list(map(Q,c));r=[sum(row) for row in B];V=inverse(B)
 assert canonical(tuple(1 if x>0 else -1 for x in word))==expected_sign
 H=[[Q(0)]+c]+[[-r[i]]+B[i] for i in range(3)]
 assert sum(c)==1 and det(H)==det(B)>0
 assert [sum(row) for row in H]==[1,0,0,0]
 assert all(any(H[i][j]<0 for i in range(4)) for j in range(4))
 assert any(H[i][j]<0 and H[j][i]<0 for i,j in combinations(range(4),2))
 assert all(det(submatrix(H,S))!=0 for k in (2,3,4) for S in combinations(range(4),k))
 W=inverse(H);R=mul([c],V)[0]
 assert W==[[Q(1)]+[-x for x in R]]+[[Q(1)]+[V[i][j]-R[j] for j in range(3)] for i in range(3)]
 assert all(x!=0 for x in flat(W))
 for i,j in combinations(range(3),2):
  D=c[i]*r[j]/B[j][i]+c[j]*r[i]/B[i][j]
  assert det(submatrix(H,[0,i+1,j+1]))==-B[i][j]*B[j][i]*D
  slack=-r[3-i-j]+B[3-i-j][i]*r[j]/B[j][i]+B[3-i-j][j]*r[i]/B[i][j]
  assert slack==det(B)/(B[i][j]*B[j][i])
  eligible=B[i][j]*B[j][i]>0 and r[i]/B[i][j]>0 and r[j]/B[j][i]>0
  assert not eligible or D<0
 # Complete support census at offset -e0: exactly the full positive root.
 roots=[]
 for k in range(1,5):
  for S in combinations(range(4),k):
   T=submatrix(H,S)
   if not det(T):
    assert k==1
    continue # singleton impossible: target row0, or a negative column
   y=[[Q(i==0)] for i in S];z=[row[0] for row in mul(inverse(T),y)]
   if not all(x>0 for x in z):continue
   x=[Q(0)]*4
   for i,t in zip(S,z):x[i]=t
   w=[sum(H[i][j]*x[j] for j in range(4))-Q(i==0) for i in range(4)]
   if all(t>=0 for t in w):roots.append((S,x,w))
 assert roots==[((0,1,2,3),[Q(1)]*4,[Q(0)]*4)]
 good_children=[]
 for S in combinations(range(4),3):
  T=submatrix(H,S);Ti=inverse(T)
  if 0 in S:
   i,j=[k-1 for k in S if k!=0];a,b=B[i][j],B[j][i]
   D=c[i]*r[j]/b+c[j]*r[i]/a
   flag=a*b<0 and r[i]/a>0 and r[j]/b>0 and c[i]/a>0 and c[j]/b>0 and D>0
   assert flag==all(x>0 for x in flat(Ti))
  if not all(x>0 for x in flat(Ti)):continue
  o=next(i for i in range(4) if i not in S)
  outside=mul([[H[o][j] for j in S]],Ti)[0]
  assert any(x<0 for x in outside)
  if 0 in S:assert outside[S.index(0)]==-det(H)/det(T)
  good_children.append(S)
 child_counts.append(len(good_children))
assert {0,1,2}.issubset(child_counts)

# Small no-child witness with a unique positive full inverse column.
G=[[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]]
W=inverse(G)
assert det(G)==11
assert W==[[Q(x,11) for x in row] for row in [[3,-2,4,5],[1,3,5,-2],[-2,5,1,4],[5,4,3,1]]]
assert [j for j in range(4) if all(W[i][j]>0 for i in range(4))]==[2]
assert [det(submatrix(G,S)) for S in combinations(range(4),3)]==[1,1,3,3]
assert all(det(submatrix(G,S))!=0 for k in (2,3,4) for S in combinations(range(4),k))
assert all(any(G[i][j]<0 for i in range(4)) for j in range(4))
assert G[0][1]<0 and G[1][0]<0
assert not any(all(x>0 for x in flat(inverse(submatrix(G,S)))) for S in combinations(range(4),3))
v=[W[i][2] for i in range(4)];order=[2,0,1,3]
H=[[G[i][j]*v[j] for j in order] for i in order]
B=submatrix(H,[1,2,3]);r=[sum(row) for row in B]
assert B==[[Q(x,11) for x in row] for row in [[0,-5,6],[-4,0,3],[4,-5,0]]]
assert r==[Q(1,11),Q(-1,11),Q(-1,11)]
assert not any(B[i][j]*B[j][i]>0 and r[i]/B[i][j]>0 and r[j]/B[j][i]>0 for i,j in combinations(range(3),2))
roots=[]
for k in (2,3,4):
 for S in combinations(range(4),k):
  T=submatrix(G,S);z=[row[0] for row in mul(inverse(T),[[Q(i==2)] for i in S])]
  if not all(x>0 for x in z):continue
  x=[Q(0)]*4
  for i,t in zip(S,z):x[i]=t
  w=[sum(G[i][j]*x[j] for j in range(4))-Q(i==2) for i in range(4)]
  if all(t>=0 for t in w):roots.append((S,x,w))
assert roots==[((0,1,2,3),v,[Q(0)]*4)]

# Independent finite sign check of the analytic one-pivot lemma. Determinant
# signs are allowed independently whenever the two cycle monomials oppose;
# hence this is a conservative superset of realizable magnitude choices.
pos4=[(i,j) for i in range(4) for j in range(4) if i!=j]
triples=list(combinations(range(4),3));covered_cases=0
target=tuple(1 if G[i][j]>0 else -1 for i,j in pos4)
for word in product((-1,1),repeat=12):
 A=[[0]*4 for _ in range(4)]
 for (i,j),value in zip(pos4,word):A[i][j]=value
 if not any(A[i][j]<0 and A[j][i]<0 for i,j in combinations(range(4),2)):continue
 choices=[];adjugates=[]
 for i,j,k in triples:
  a,b,c,d,e,f=A[i][j],A[i][k],A[j][i],A[j][k],A[k][i],A[k][j]
  m1,m2=a*d*e,b*c*f
  choices.append((m1,) if m1==m2 else (-1,1))
  adjugates.append([[-d*f,b*f,a*d],[d*e,-b*e,b*c],[c*f,a*e,-a*c]])
 for signs in product(*choices):
  if any(all(s*x>0 for x in flat(adj)) for s,adj in zip(signs,adjugates)):continue
  covered=set()
  for S,s,adj in zip(triples,signs,adjugates):
   if s>0:covered.update(h for n,h in enumerate(S) if all(adj[m][n]>0 for m in range(3)))
  if len(covered)<3:continue
  covered_cases+=1
  assert len(covered)==3
  assert any(tuple(A[p[i]][p[j]] for i,j in pos4)==target
             and {h for h in range(4) if p[h] in covered}=={0,1,3}
             for p in permutations(range(4)))
assert covered_cases==48

# All four remaining genericity sign subcases occur in the iff chamber.
subcases=set()
for b,e,g in ((1,1,1),(1,3,1),(2,1,3),(1,1,3)):
 a=d=f=i=j=k=l=1;c=h=2
 A=[[0,-a,-b,c],[-d,0,e,f],[g,h,0,-i],[j,-k,l,0]]
 R=c*d*k-a*f*j;U=d*i*k-f*g*k-f*h*j
 V=a*i*l+b*i*k-c*h*l;W=b*d*i-b*f*g-c*e*g
 assert R>0 and U<0 and V<0 and W<0
 assert f*k*det(A)==(e*i*k+f*h*l)*R-(a*f*l+b*f*k+c*e*k)*U>0
 Ai=inverse(A)
 assert [n for n in range(4) if all(Ai[m][n]>0 for m in range(4))]==[2]
 assert all(x!=0 for x in flat(Ai))
 E=d*i*l+e*i*j-f*g*l;T=b*d*h-a*e*g
 assert det(submatrix(A,[0,1,2]))==T!=0
 assert Ai[1][0]==E/det(A) and Ai[3][3]==T/det(A)
 assert all(det(submatrix(A,S))!=0 for n in (2,3,4) for S in combinations(range(4),n))
 subcases.add((1 if E>0 else -1,1 if T>0 else -1))
assert subcases==set(product((-1,1),repeat=2))
print('PASS: exact 64-word / 16-orbit / 11-positive-possible sign classification')
print('PASS: ten generic normal-form witnesses; unique full root at -e0; complete passive-child failure')
print('PASS: Schur identities, triple root formulas, child counts 0/1/2, and exact no-child witness')
print('PASS: analytic one-pivot sign lemma cross-check; all 4096 words; 48 covered signatures in one orbit')


# Complete all-pivot refinement inside the twelve-sign orbit.
def adj(a):
 d=det(a)
 return [[d*x for x in row] for row in inverse(a)]

def matvec(a,v):return [sum(x*y for x,y in zip(row,v)) for row in a]

orbit_witnesses=[(1,2,1,1,2,1),(2,3,1,1,4,3),(2,2,1,1,1,1),(3,2,1,1,2,2),
           (1,4,2,1,3,5),(2,6,1,1,3,5),(1,3,2,1,1,3),(2,3,1,1,1,3)]
seen=set()
for b,c,e,g,h,i in orbit_witnesses:
 a=d=f=j=k=l=1
 G=[[0,-a,-b,c],[-d,0,e,f],[g,h,0,-i],[j,-k,l,0]]
 D=det(G);N=adj(G)
 R=c*d*k-a*f*j;U=d*i*k-f*g*k-f*h*j
 V=a*i*l+b*i*k-c*h*l;W=b*d*i-b*f*g-c*e*g
 assert R>0 and D>0
 assert N==[[e*i*k+f*h*l,V,a*f*l+b*f*k+c*e*k,-a*e*i+b*f*h+c*e*h],
 [d*i*l+e*i*j-f*g*l,b*i*j+c*g*l,b*f*j+c*d*l+c*e*j,W],
 [U,-a*i*j+c*g*k+c*h*j,R,-a*d*i+a*f*g+c*d*h],
 [d*h*l+e*g*k+e*h*j,a*g*l+b*g*k+b*h*j,a*d*l+a*e*j+b*d*k,b*d*h-a*e*g]]
 assert all(x!=0 for row in N for x in row)
 assert all(det(submatrix(G,S))!=0 for n in (2,3,4) for S in combinations(range(4),n))
 A=N[0][2];B=N[1][2];C=N[1][1];P=N[0][0];Q1=N[3][1]
 assert f*k*D==P*R-A*U
 assert B*N[2][1]==C*R+c*j*D
 assert B*N[0][3]==A*W+(b*f+c*e)*D
 assert B*N[2][3]==R*W+c*d*D
 assert C*N[3][3]==W*Q1+b*g*D
 pivots={p for p in range(4) if all(N[q][p]>0 for q in range(4))}
 assert pivots=={2}|({0} if U>0 else set())|({1} if V>0 else set())|({3} if W>0 else set())
 assert all(any(G[r][s]<0 for r in range(4)) for s in range(4))
 roots=[]
 for n in (2,3,4):
  for S in combinations(range(4),n):
   T=submatrix(G,S);dt=det(T);ad=adj(T)
   if n==3:assert not all(dt*x>0 for row in ad for x in row)
   target=[int(s==2) for s in S]
   x=[Q(z,dt) for z in matvec(ad,target)]
   if not all(z>0 for z in x):continue
   full=[Q(0)]*4
   for s,z in zip(S,x):full[s]=z
   if all(z-int(r==2)>=0 for r,z in enumerate(matvec(G,full))):roots.append(S)
 assert roots==[(0,1,2,3)]
 seen.add((U>0,V>0,W>0))
assert seen==set(product((False,True),repeat=3))
print('PASS: all eight U/V/W orthants; exact full cofactors and five identities; genericity; k=0; complete full positive-column sets; unique full root at -e2.')


# Raw necessary tests for a selected actual two-owner tail.
def _i2_cut(interval, constant, slope, strict=False):
    """Intersect (lo, hi, lo_closed, hi_closed) with constant+slope*x >= 0."""
    if interval is None:
        return None
    lo, hi, lc, hc = interval
    if slope == 0:
        return interval if constant > 0 or (constant == 0 and not strict) else None
    bound = -constant / slope
    if slope > 0:
        if bound > lo:
            lo, lc = bound, not strict
        elif bound == lo:
            lc = lc and not strict
    else:
        if bound < hi:
            hi, hc = bound, not strict
        elif bound == hi:
            hc = hc and not strict
    return (lo, hi, lc, hc) if lo < hi or (lo == hi and lc and hc) else None


def _i2_contains(interval, value):
    if interval is None:
        return False
    lo, hi, lc, hc = interval
    return (lo < value or (lc and lo == value)) and (value < hi or (hc and value == hi))


def i2_partner_screen(Z, p, i):
    """Exact necessary I2 test for rational native Z[4][16], under the generic
    positive-absorbing-gap actual source. A pass supplies no profile or UE claim.
    Returned intervals are (lower, upper, lower_closed, upper_closed), or None.
    """
    assert len(Z) == 4 and all(len(row) == 16 for row in Z)
    assert p in range(4) and i in range(4) and p != i
    Z = [[Q(x) for x in row] for row in Z]
    assert all(Z[j][1 << j] == 0 for j in range(4))
    G, A = Z[i][1 << p], Z[p][1 << i]
    J, C = Z[i][(1 << p) | (1 << i)], Z[p][(1 << p) | (1 << i)]
    result = dict(status="excluded", reason=None, rho=None, I=None, O=None, common_required=False)
    if not G or not A or J == G or C == A or G*C == A*J:
        return dict(result, status="outside_source", reason="nongeneric_pair")
    if not J or not 0 < G/J < 1:
        return dict(result, reason="contact_ratio")
    rho = G/J
    result["rho"] = rho
    if A-rho*C <= 0:
        return dict(result, reason="pair_margin")
    quiet = [j for j in range(4) if j not in (p, i)]
    a = {j: Z[j][1 << p]-rho*Z[j][(1 << j) | (1 << p)] for j in quiet}
    quiet.sort(key=lambda j: a[j])
    h, k = quiet
    if not a[h] < 0 < a[k]:
        return dict(result, reason="quiet_signs")
    b = {j: (Z[j][1 << i], -Z[j][(1 << j) | (1 << i)]) for j in quiet}
    interval = (rho, Q(1), True, False)
    for c, s, strict in [(A, -C, False), (*b[h], True), (-b[k][0], -b[k][1], True),
            (a[k]*b[h][0]-a[h]*b[k][0], a[k]*b[h][1]-a[h]*b[k][1], False)]:
        interval = _i2_cut(interval, c, s, strict)
    result.update(I=interval, quiet=(h, k))
    if interval is None:
        return dict(result, reason="quiet_interval")
    common = A < 0
    if A > 0:
        outer = (Q(0), rho, True, True) if J > 0 else (rho, Q(1), True, True)
        c = {j: (Z[j][1 << p], -Z[j][(1 << j) | (1 << p)]) for j in quiet}
        d = {j: Z[j][1 << i] for j in quiet}
        for j in quiet:
            if d[j] <= 0:
                outer = _i2_cut(outer, *c[j], strict=d[j] < 0)
        for j in quiet:
            for l in quiet:
                if d[j] < 0 < d[l]:
                    outer = _i2_cut(outer, d[l]*c[j][0]-d[j]*c[l][0],
                                   d[l]*c[j][1]-d[j]*c[l][1])
        result["O"] = outer
        common = outer is None
    result["common_required"] = common
    if common and not _i2_contains(interval, rho):
        return dict(result, reason="common_atom_rate")
    return dict(result, status="passes_necessary", reason="screen_passed")


def check_i2_screen():
    """Hand-derived interval and strict/weak endpoint controls, not gap examples."""
    Z = [[Q(0) for _ in range(16)] for _ in range(4)]
    G = [[0,3,-1,4],[2,0,1,-3],[2,-2,0,-1],[-1,-2,1,0]]
    for j in range(4):
        for l in range(4):
            Z[j][1 << l] = Q(G[j][l])
    for j, mask, value in [(1,3,4),(0,3,-2),(2,5,10),(3,9,-4),(2,6,-10),(3,10,Q(1,10))]:
        Z[j][mask] = Q(value)
    result = i2_partner_screen(Z,0,1)
    assert result["I"] == (Q(80,97),Q(1),True,False) and result["O"] is None
    assert result["reason"] == "common_atom_rate"
    W = [row[:] for row in Z]; W[3][9] = Q(-10); W[2][6] = Q(-4)
    result = i2_partner_screen(W,0,1)
    assert result["I"] == (Q(140,157),Q(1),True,False)
    assert result["O"] == (Q(1,10),Q(1,5),False,False) and result["status"] == "passes_necessary"
    W = [row[:] for row in Z]
    for j, mask, value in [(1,1,-1),(1,3,-2),(0,2,-1),(0,3,-3),(2,1,1),(2,5,4),
                           (3,1,3),(3,9,4),(2,2,3),(2,6,2),(3,2,2),(3,10,6)]:
        W[j][mask] = Q(value)
    result = i2_partner_screen(W,0,1)
    assert result["I"] == (Q(1,2),Q(5,8),True,True) and result["common_required"]
    assert result["status"] == "passes_necessary"
    W[2][2] = Q(2)
    result = i2_partner_screen(W,0,1)
    assert result["I"] == (Q(1,2),Q(1,2),True,True) and result["status"] == "passes_necessary"
    W[2][1] = Q(2)
    assert i2_partner_screen(W,0,1)["reason"] == "quiet_signs"
    W = [row[:] for row in Z]
    for j, mask, value in [(2,1,1),(2,5,4),(2,2,-1),(2,6,-4),
                           (3,1,-1),(3,9,-3),(3,2,1),(3,10,2)]:
        W[j][mask] = Q(value)
    result = i2_partner_screen(W,0,1)
    assert result["I"] == (Q(1,2),Q(1),False,False)
    assert result["O"] == (Q(0),Q(0),True,True) and result["status"] == "passes_necessary"
    assert _i2_cut((Q(0),Q(1),True,False), Q(-1), Q(1)) is None
    assert _i2_cut((Q(0),Q(1),True,True), Q(0), Q(-1)) == (Q(0),Q(0),True,True)
    assert _i2_cut((Q(0),Q(1),True,True), Q(0), Q(-1), True) is None


if __name__ == "__main__":
    check_i2_screen()
    print("PASS: exact I2 interval, common-atom and endpoint controls")
