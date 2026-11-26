# A stationary producer with a dominated row and an arbitrary row

This is ordinary mathematics with an exact finite certificate, not a new
Lean-checked theorem. Arbitrary four-player quitting games remain open.

Players are0,1,2,3. For a nonempty quitting coalition S, player i receives
r_i(S). The empty-coalition payoff is0. Put s_i=r_i({i}) and
W_i(S)=r_i(S)-s_i, so W_i({i})=0. All entries are finite real numbers.

The theorem below gives a stationary exact terminal Nash equilibrium and a
uniform-equilibrium payoff directly from raw reward inequalities. It leaves
one player's entire normalized reward row arbitrary and allows unbounded
one-sided changes throughout another row.

## 1. The reference table and the raw class

For delta,epsilon>=0 define

    A = [ 0       1      -6       -1/100 ]
        [ 1       0      -3/2     -2/5   ]
        [ -delta -3/5     0        1     ]
        [ -7/100 -epsilon 1        0     ].

Favorite pairs are01 and23. Set J_ij=1/100 on favorite directed edges.
On directed edges02,21,13,30 put J_ij=-(9/10)A_ij; on the remaining
crossing edges03,12,20,31 put J_ij=-(1/10)A_ij. With Gamma=A+J, set

    Z_i({i})=0, Z_i({j})=Gamma_ij, Z_i({i,j})=J_ij.

For opponent pairs B=01,02,03,12,13,23 use signs+1,-1,+1,+1,-1,-1.
The smaller outsider i has Delta_i(B) equal to that sign and the larger
outsider has its negative. Set

    Z_i(B)=max(0,-Delta_i(B)),
    Z_i(B union {i})=max(0,Delta_i(B)).

For each i put Z_i(N minus {i})=1 and Z_i(N)=0. These rules specify all
60 nonempty-coalition rewards. Write B=Z^(8/5,0).

**Theorem.** Suppose the normalized raw table W satisfies:

* W_0(S)=B_0(S) and W_1(S)=B_1(S) for every nonempty S;
* W_2(S)>=B_2(S) when2 belongs to S, and W_2(S)<=B_2(S) otherwise;
* W_3(S) is arbitrary.

Then r has a stationary exact terminal Nash equilibrium. Its actual terminal
payoff is a uniform-equilibrium payoff against all behavioral replacements.
No signs or bounds are imposed on s_i, on the arbitrary fourth row, or on the
magnitudes of the permitted changes in the third row.

In particular, every table Z^(delta,epsilon) with delta>=8/5 and epsilon>=0
satisfies the theorem: increasing delta lowers only Z_2({0})=-9delta/10 and
raises only Z_2({0,2})=delta/10. The fourth row may instead be replaced in its
entirety by any finite row, with any signs.

## 2. A strict lower-face certificate

For independent hazards q in[0,1]^4, let

    H_i=product_{j!=i}(1-q_j),
    P_i=E[W_i(T)], Q_i=E[W_i(T union {i})],
    F_i=(1-H_i)Q_i-P_i,

where T is the random coalition of opponents and W_i(empty)=0. Each F_i is
continuous and independent of q_i. Endpoint complementarity means

    q_i=0 => F_i<=0; 0<q_i<1 => F_i=0; q_i=1 => F_i>=0.       (1)

The exact certificate proves the following statement about the reference B:

    q2=7/50 and (1) for i=0,1  ==>  F_2^B(q)>0.              (2)

There is no condition on q3 or on player3's incentives. The three polynomials
F_0^B,F_1^B,F_2^B are computed directly from the raw table, with variables
(q0,q1,q3) and tensor degree(2,2,2). The checker covers the entire closed unit
cube by exact midpoint subdivision. A box is accepted if its Bernstein
coefficients prove F_2^B>0, or if for i=0 or1 either

    lower(q_i)>0 and F_i^B<0 throughout the box, or
    upper(q_i)<1 and F_i^B>0 throughout the box.

The latter alternatives contradict (1). There are977 nodes,489 leaves and
maximum depth24; no boundary boxes or exceptional origin region are omitted.
The polynomial convex-hull property makes every accepted box valid. The
checker generates the coefficients as exact rationals and uses integers for
every subdivision and sign test. It stores no leaf payload.

The raw domination in the theorem gives F_2^W>=F_2^B at every q: every
participant reward has coefficient (1-H_2)Pr(T)>=0 and every passive reward
has coefficient -Pr(T)<=0. Rows0 and1 are unchanged. Thus (2) also holds for
W, regardless of its fourth row.

## 3. The global producer

Consider the compact cube

    C=[0,1] x [0,1] x [7/50,1] x [0,1].

Define a continuous self-map by clipping q_i+F_i(q) to the corresponding
coordinate interval of C. Brouwer's fixed-point theorem gives a fixed point
q. Coordinates0,1,3 satisfy (1). If q2=7/50, fixedness of coordinate2 would
give F_2(q)<=0, contradicting the strict lower-face certificate. Consequently
q2>7/50. Coordinate2 therefore satisfies the ordinary condition (1), including
the allowed case q2=1,F_2>=0. All four players satisfy endpoint complementarity.

This is a producer of a complete stationary profile from the raw table.
It needs no root selector, continuation curve, prescribed face exit, or
conditional strategic witness. The arbitrary fourth row affects the
continuous self-map but never the lower-face exclusion.

## 4. Actual terminal payoffs, absorption and signed offsets

Deleting any owner other than2 leaves opponent2 with hazard greater than7/50.
Deleting owner2 also leaves some opponent with positive hazard. Otherwise
q0=q1=q3=0, while player1's unchanged row gives

    F_1(q)=q2(135+15q2)/100>0,

contradicting q1=0 and (1). For each produced profile, therefore, every
unilateral behavioral replacement has a geometric opponent-absorption bound.

The actual stationary terminal value U_i for W obeys

    U_i=q_i Q_i+(1-q_i)(P_i+H_i U_i).

With lambda_i=1-(1-q_i)H_i>0, the difference between quitting and continuing
at value U_i is

    Q_i-(P_i+H_i U_i)=F_i/lambda_i.

Thus (1) is exactly the prescribed-action best-response condition. Iterating
these one-step inequalities bounds every complete behavioral deviation by U_i;
the continuation remainder vanishes uniformly over deviations by opponent
absorption. This includes a deviator who never quits.

Adding s_i to every absorbing reward shifts every prescribed and deviating
terminal payoff by exactly s_i, since all such paths absorb. Hence the same
profile is terminal Nash for r. The uniform finite expected absorption bound
makes terminal and N-stage-average payoffs differ by O(1/N), uniformly over
all behavioral replacements. The actual terminal payoff U+s is consequently
a fixed uniform-equilibrium payoff. The witness is stationary, of period1.

Formalization target: from the raw row assumptions produce q satisfying the
stationary endpoint and opponent-contraction predicates, then apply
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
The finite Bernstein calculation supplies (2); Brouwer supplies q. No strategic
data are assumptions of the theorem. Both consumers are in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`; this new raw
producer and its finite certificate have not yet been formalized in Lean.

## 5. A larger half-plane inside the two-crossing family

For the literal family Z^(delta,epsilon), the conclusion extends to every
delta>=3/2 and epsilon>=0. Only the strip[3/2,8/5] needs an additional argument.
For y in[141/1000,17/100], put

    q0=1, q1=(7+93y)/(107+93y), q2=y, q3=1/[2(1-y)],
    D(y)=(50+7y+93y^2)/(50-100y).

At delta=D(y), literal expansion gives F1=F2=F3=0 for every epsilon. The
epsilon-dependent row3 coalitions{1},{1,3} cannot occur while player0 is sure.
The remaining field is

    F0=P(y)/[4(y-1)(93y+107)^2],
    P(y)=106020y^4+421140y^3-90131y^2-15828y+2799.

All degree4 Bernstein coefficients of P on that interval are negative. With
common denominator150000000000, their numerators are

    -328360936617, -16573543619040, -30702393497300,
    -42275053176000, -50840417370000.

Thus F0>0. Also D'(y)=-(186y^2-186y-107)/[50(2y-1)^2]>0, and

    D(141/1000)=52835933/35900000<3/2,
    D(17/100)=538777/330000>8/5.

Every delta in the strip has a unique such y by the IVT. The other three
hazards are proper, so every opponent-deleted profile absorbs. Section4
therefore applies, including arbitrary signed offsets. This overlaps the
global producer at delta=8/5 and closes the entire unbounded half-plane.

## 6. Exact tests on an unbounded subfamily

Take Z^(8/5,1/2), replace only Z_3(I) by -M, and put r_i(S)=1+Z_i(S),
where M>=216. Every such table satisfies the theorem. This subfamily permits
arbitrarily negative grand rewards while retaining its prescribed proper
coalitions. Its singleton matrix Gamma has

    det Gamma=351951137/500000000,
    min_(i,j)(Gamma^-1)_ij=2186650/351951137>0.

The following exact exclusions distinguish the stationary profiles produced
here from several restricted stationary constructions. They assert neither
absence of every stationary equilibrium nor absence of sure hazards.

### 6.1. Two large hazards

There is no stationary Nash profile with every hazard strictly below1 and
at least two hazards at least1/2. For the six choices of the two large
coordinates, cover the closed cube having those coordinates in[1/2,1] and
all others in[0,1]. At a candidate profile every F_i<=0, and q_i>0 requires
F_i=0. Consequently a box is rejected if F_i>0 for i=0,1,2, or if F_i<0
and the lower bound on q_i is positive. For row3 use only negative bounds at
M=216, because

    F_3^M=F_3^216-(M-216)(1-H_3)q0q1q2<=F_3^216.          (3)

Each field has tensor degree at most(2,2,2,2). Exact Bernstein subdivision
rejects every candidate in all six cubes. In pair order01,02,03,12,13,23,
the node counts are21,35,611,13,5,35, the leaf counts11,18,306,7,3,18,
and the maximum depths5,6,34,4,2,6. Boxes may include hazard1, but rejection
uses only the necessary inequalities for the stated strictly-below1 class.
Every pure pair also fails Nash: one outsider has joining gain exactly1.

### 6.2. Three proper active hazards

No stationary Nash profile has exactly three positive hazards, all below1.
For supports012 and123, respectively owners2 and1 lack their favorite. Both
passive singleton rewards in that support are negative, the passive pair
reward is zero, and every participant reward is nonnegative. Thus P_i<0,
Q_i>=0 and F_i>0, contradicting active mixing.

For supports023 and013, the checker covers their three-dimensional closed
hazard cubes. It rejects a box when an active field excludes zero, or the
inactive field is strictly positive. The respective certificates have
157 nodes/79 leaves/depth39 and1103 nodes/552 leaves/depth52. Each contains
one origin box of radius1/8192, handled as follows.

For active support S write F_S(q)=-Gamma_SS q_S+R_S(q_S). Each monomial of
R_S has total degree at least2. Let L=||Gamma_SS^-1||_infinity and let K be
the largest sum of absolute coefficients in a coordinate of R_S. For
0<t=||q_S||_infinity<=1, ||R_S(q_S)||_infinity<=K t^2. An active root would
therefore give1<=LKt. The exact pairs are

    (L,K)=(1935500/14443,30797/1000) for S=023,
    (L,K)=(146700/433,323/100) for S=013.

Both satisfy LK/8192<1, excluding every nonzero root in the origin box.
The grand penalty does not affect these two restricted fields, since their
omitted owner is1 or2 and the additional term in(3) vanishes.

### 6.3. All hazards at most one half

No stationary Nash profile has every hazard at most1/2. A singleton support
fails because some quiet recipient receives a negative native singleton
reward, while quitting immediately guarantees a nonnegative native reward.
For a two-player support{i,j},

    F_i=q_j[Z_i({i,j})q_j-Gamma_ij].

Every pair premium is positive. Either Gamma_ij<0 or Gamma_ij exceeds its
pair premium, so this field cannot vanish at proper positive hazards.
Three-player supports were excluded above. AllNever is not Nash in r,
because every own singleton pays1.

For full support in[0,1/2]^4, the necessary conditions are F0=F1=F2=0 and
F3^216>=0, by(3). Exact Bernstein signs reject every remaining box except
one origin box of radius1/16384:1155 nodes,578 leaves, maximum depth59.
For that last box define

    F^216(q)=-Gamma q+R216(q),
    L=||Gamma^-1||_infinity=2381845750/351951137,
    K=max_i sum of absolute coefficients of R216_i=1527679/1000.

Every remainder monomial has degree at least2. At an actual full root for
M>=216, positivity of Gamma^-1 and(3) imply

    q=Gamma^-1 R216(q)-(M-216)(1-H3)q0q1q2 Gamma^-1 e3
       <=Gamma^-1 R216(q).

Thus0<t=||q||_infinity<=1 would imply t<=LKt^2. The exact inequality
LK/16384<1 excludes the nonzero origin box. This proves the assertion for
all supports, uniformly in M. All the data, coefficients, subdivision rules
and origin estimates are reproduced by the complete checker below.

## 7. Complete exact checker

Save the following block as `check.py` and run `python check.py` with SymPy
installed. It reconstructs the raw table once and uses a shared exact integer
Bernstein kernel. It reads no external data and saves no subdivision payload.

```python
"""Exact audit of the raw stationary producer and its geometric boundary tests.
Requires SymPy. No numerical candidate, tolerance, imported packet, or saved tree.
"""
import itertools
from fractions import Fraction as Q
import sympy as s
R=s.Rational
q=s.symbols('q0:4');d,e=s.symbols('delta epsilon');I=range(4)
A=s.Matrix([[0,1,-6,-R(1,100)],[1,0,-R(3,2),-R(2,5)],[-d,-R(3,5),0,1],[-R(7,100),-e,1,0]])
Z={(i,0):s.S.Zero for i in I}
for i in I:
 Z[i,1<<i]=s.S.Zero
 for j in I:
  if j==i:continue
  J=R(1,100) if j==(i^1) else -A[i,j]*(R(9,10) if (i,j) in ((0,2),(2,1),(1,3),(3,0)) else R(1,10))
  Z[i,1<<j]=A[i,j]+J;Z[i,(1<<i)|(1<<j)]=J
for pair,sign in zip(itertools.combinations(I,2),(1,-1,1,1,-1,-1)):
 mask=sum(1<<j for j in pair);outs=[j for j in I if j not in pair]
 for i,v in zip(outs,(sign,-sign)):
  Z[i,mask]=s.Integer(max(0,-v));Z[i,mask|(1<<i)]=s.Integer(max(0,v))
for i in I:Z[i,15^(1<<i)]=s.S.One;Z[i,15]=s.S.Zero
assert len(Z)==64
H=[];F=[]
for i in I:
 h=s.prod(1-q[j] for j in I if j!=i);p=v=0
 for mask in range(16):
  if mask>>i&1:continue
  w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
  p+=w*Z[i,mask];v+=w*Z[i,mask|(1<<i)]
 H.append(h);F.append(s.expand((1-h)*v-p))
assert s.expand(s.diff(F[2],d)-(1-H[2]/10)*q[0]*(1-q[1])*(1-q[3]))==0
assert all(s.diff(F[i],d)==0 for i in (0,1,3))
assert all(s.diff(F[i],q[i])==0 for i in I)

# Analytic sure0 strip, with exact Bernstein coefficients for its last inequality.
y=s.symbols('y');D=(50+7*y+93*y*y)/(50-100*y)
qs={q[0]:1,q[1]:(7+93*y)/(107+93*y),q[2]:y,q[3]:1/(2*(1-y)),d:D}
P=106020*y**4+421140*y**3-90131*y*y-15828*y+2799
assert all(s.cancel(F[i].subs(qs))==0 for i in (1,2,3))
assert s.cancel(F[0].subs(qs)-P/(4*(y-1)*(93*y+107)**2))==0
assert s.cancel(s.diff(D,y)+(186*y*y-186*y-107)/(50*(2*y-1)**2))==0
u=s.symbols('u');pp=s.Poly(s.expand(P.subs(y,R(141,1000)+(R(17,100)-R(141,1000))*u)),u)
strip=[sum(v*s.binomial(a,m[0])/s.binomial(4,m[0]) for m,v in pp.terms() if m[0]<=a) for a in range(5)]
assert [v*150000000000 for v in strip]==[-328360936617,-16573543619040,-30702393497300,-42275053176000,-50840417370000]
assert all(v<0 for v in strip)
assert D.subs(y,R(141,1000))<R(3,2) and D.subs(y,R(17,100))>R(8,5)

# Deleting player2 still leaves some positive opponent hazard at every produced root.
assert s.expand(F[1].subs({q[0]:0,q[1]:0,q[3]:0})-q[2]*(135+15*q[2])/100)==0

# Shared exact tensor-Bernstein kernel, dimension3 for the theorem and4 for scope.
def coefficients(polys,variables):
 n=len(variables);raw=[]
 for p in polys:
  p=s.Poly(s.expand(p),*variables)
  assert all(p.degree(v)<=2 for v in variables)
  for a in itertools.product(range(3),repeat=n):
   raw.append(sum(v*s.prod(s.binomial(a[j],m[j])/s.binomial(2,m[j])for j in range(n)) for m,v in p.terms() if all(m[j]<=a[j]for j in range(n))))
 den=int(s.ilcm(*(s.denom(v)for v in raw)))
 return [int(v*den)for v in raw]
def split(b,axis,n):
 left=b.copy();right=b.copy();stride=3**(n-1-axis)
 for base in range(len(b)):
  if (base//stride)%3:continue
  a0,a1,a2=[b[base+k*stride]for k in range(3)];mid=a0+2*a1+a2
  for k,v in enumerate((4*a0,2*(a0+a1),mid)):left[base+k*stride]=v
  for k,v in enumerate((mid,2*(a1+a2),4*a2)):right[base+k*stride]=v
 return left,right
def cover(b,n,lo,mode,hi=None,origin_radius=Q(0),active=()):
 stack=[(lo,[Q(1)]*n if hi is None else hi,b,0)];nodes=leaves=depthmax=origins=0;size=3**n
 while stack:
  lo,hi,b,depth=stack.pop();nodes+=1;depthmax=max(depthmax,depth)
  mins=[min(b[i:i+size])for i in range(0,len(b),size)];maxs=[max(b[i:i+size])for i in range(0,len(b),size)]
  if origin_radius and max(hi)<=origin_radius:origins+=1;leaves+=1;continue
  if mode=='producer':
   bad=mins[2]>0 or any((lo[i]>0 and maxs[i]<0)or(hi[i]<1 and mins[i]>0)for i in (0,1))
  elif mode=='proper_triple':
   bad=any(mins[i]>0 or maxs[i]<0 for i in active) or any(mins[i]>0 for i in range(4)if i not in active)
  elif mode=='small_full':
   bad=any(mins[i]>0 or maxs[i]<0 for i in (0,1,2)) or maxs[3]<0
  else:
   assert mode=='proper_two_high'
   # All hazards are below1. F3 decreases with M: use only its negative sign.
   bad=any(mins[i]>0 or(lo[i]>0 and maxs[i]<0)for i in (0,1,2)) or(lo[3]>0 and maxs[3]<0)
  if bad:leaves+=1;continue
  assert nodes<10000 and depth<80,('unexcluded box',lo,hi)
  widths=[hi[i]-lo[i]for i in range(n)];choices=[i for i in range(n)if widths[i]==max(widths)];axis=choices[0] if origin_radius else choices[depth%len(choices)]
  left,right=split(b,axis,n);mid=(lo[axis]+hi[axis])/2;low=lo.copy();low[axis]=mid;high=hi.copy();high[axis]=mid
  stack.append((low,hi,right,depth+1));stack.append((lo,high,left,depth+1))
 assert nodes==2*leaves-1
 return (nodes,leaves,depthmax,origins) if origin_radius else (nodes,leaves,depthmax)
X=[q[0],q[1],q[3]]
polys=[F[i].subs({q[2]:R(7,50),d:R(8,5)})for i in (0,1,2)]
result=cover(coefficients(polys,X),3,[Q(0)]*3,'producer')
assert result==(977,489,24)
print('PASS raw algebra, sure0 strip, and unrestricted-row3 producer:',result)

# Exact fixture for the geometric boundary tests.
G=s.Matrix(4,4,lambda i,j:0 if i==j else Z[i,1<<j])
zz={key:value.subs({d:R(8,5),e:R(1,2)})for key,value in Z.items()}
gg=G.subs({d:R(8,5),e:R(1,2)})
assert gg.det()==R(351951137,500000000)
assert min(gg.inv())==R(2186650,351951137)>0

# Uniform M>=216: exclude every all-proper stationary profile with two large hazards.
# F3^M=F3^216-(M-216)(1-H3)q0q1q2. Other fields do not change.
fixture=F.copy();fixture[3]-=216*(1-H[3])*q[0]*q[1]*q[2]
base=coefficients([f.subs({d:R(8,5),e:R(1,2)})for f in fixture],q)
expected=((21,11,5),(35,18,6),(611,306,34),(13,7,4),(5,3,2),(35,18,6))
for pair,want in zip(itertools.combinations(I,2),expected):
 b=base.copy();lo=[Q(0)]*4
 for j in pair:b=split(b,j,4)[1];lo[j]=Q(1,2)
 result=cover(b,4,lo,'proper_two_high');assert result==want
 print('PASS uniform M>=216 all-proper/two-large-hazard exclusion',pair,result)
# No nonzero stationary profile with all hazards<=1/2, uniformly M>=216.
# One/two supports have a strict singleton incentive. For triples012/123,
# the no-favorite owner has negative passive singleton rewards and zero passive pair.
for owner in I:
 assert any(gg[j,owner]<0 and zz[j,(1<<j)|(1<<owner)]>=0 for j in I if j!=owner)
for i,j in itertools.permutations(I,2):
 premium=zz[i,(1<<i)|(1<<j)]
 assert premium>0 and (gg[i,j]<0 or gg[i,j]>premium)
for inactive,owner in ((0,1),(3,2)):
 S=[i for i in I if i!=inactive];opp=[i for i in S if i!=owner]
 assert all(gg[owner,j]<0 for j in opp) and zz[owner,sum(1<<j for j in opp)]==0
 assert all(zz[owner,mask]>=0 for mask in range(1,16)if mask>>owner&1 and not mask>>inactive&1)
fixture_fields=[s.expand(f.subs({d:R(8,5),e:R(1,2)}))for f in fixture]
for inactive,want,Lwant,Kwant in ((1,(157,79,39,1),R(1935500,14443),R(30797,1000)),(2,(1103,552,52,1),R(146700,433),R(323,100))):
 S=[i for i in I if i!=inactive];variables=[q[i]for i in S]
 expr=[s.expand(f.subs(q[inactive],0))for f in fixture_fields]
 assert s.expand(((1-H[3])*q[0]*q[1]*q[2]).subs(q[inactive],0))==0
 inv=gg.extract(S,S).inv();LL=max(sum(abs(v)for v in inv.row(i))for i in range(3))
 K=max(sum(abs(v)for m,v in s.Poly(expr[i],*variables).terms()if sum(m)>=2)for i in S)
 assert (LL,K)==(Lwant,Kwant) and LL*K/8192<1
 result=cover(coefficients(expr,variables),3,[Q(0)]*3,'proper_triple',origin_radius=Q(1,8192),active=S)
 assert result==want;print('PASS proper triple support, inactive',inactive,result,'L',LL,'K',K)
# At a full-support root: q=Gamma^-1 R216-(M-216)c Gamma^-1 e3.
# Here c=(1-H3)q0q1q2>=0. Positive inverse gives ||q||<=L K ||q||^2.
inv=gg.inv();assert all(v>0 for v in inv)
LL=max(sum(v for v in inv.row(i))for i in I)
remainders=[s.Poly(s.expand(fixture_fields[i]+sum(gg[i,j]*q[j]for j in I)),*q)for i in I]
assert all(sum(m)>=2 for p in remainders for m,v in p.terms()if v)
K=max(sum(abs(v)for m,v in p.terms())for p in remainders)
assert (LL,K)==(R(2381845750,351951137),R(1527679,1000)) and LL*K/16384<1
b=base.copy()
for j in I:b=split(b,j,4)[0]
result=cover(b,4,[Q(0)]*4,'small_full',hi=[Q(1,2)]*4,origin_radius=Q(1,16384))
assert result==(1155,578,59,1)
print('PASS full-support small-hazard cube, all M>=216:',result,'L',LL,'K',K)
# Pure pair exits also fail: one outsider's joining gain is exactly+1.
for pair in itertools.combinations(I,2):
 mask=sum(1<<j for j in pair)
 assert any(zz[i,mask|(1<<i)]-zz[i,mask]==1 for i in I if i not in pair)
print('PASS complete combined checker')
```
