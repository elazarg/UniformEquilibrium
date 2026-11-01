# Uniform equilibria on an entire complex-spectrum reward ray

This is ordinary mathematics with a finite exact interval certificate, not a
new Lean-checked result. It closes the explicitly specified ray below for
EVERY nonnegative parameter. Arbitrary positive-collision games and Fin4
remain open.

## 1. Raw table, quantifiers and conclusion

Four players I={0,1,2,3} independently choose Continue or Quit at one live
state. The first nonempty quitting coalition D absorbs permanently at r(D).
Live play and literal Never pay zero. A unilateral deviation may replace
one player's complete history-dependent randomized behavioral strategy.

Let delta>=0 and define

    A=[0       1       -6       -1/100]
      [1       0       -3/2     -2/5  ]
      [-delta -3/5      0        1    ]
      [-7/100 -1/25     1        0    ].

Favorite partners are f=(1,0,3,2). Put J_ii=0 and J_i,f(i)=1/100. On
crossing edges02,21,13,30 put J_ij=-(9/10)A_ij; on03,12,20,31 put
J_ij=-(1/10)A_ij. Set Gamma=A+J and

    Z_i({i})=0, Z_i({j})=Gamma_ij, Z_i({i,j})=J_ij  (i!=j).

For opponent pairs B=01,02,03,12,13,23 assign signs+1,-1,+1,+1,-1,-1.
The smaller outsider receives this sign as Delta_i(B), the larger its
negative. Define

    Z_i(B)=max(0,-Delta_i(B)),
    Z_i(B union {i})=max(0,Delta_i(B)),
    Z_i(I minus {i})=1,       Z_i(I)=0.

These rules specify all60 native rewards. Every proper nonsingleton reward
vector is coordinatewise nonnegative. Only Z_2({0})=-9delta/10 and
Z_2({0,2})=delta/10 vary. For arbitrary finite signed s_i, define
r_i(D)=s_i+Z_i(D) for every nonempty D.

**Theorem.** Every such game has an exact terminal Nash profile repeating a
calendar of length at most64. The profile is independent of s. Its actual
terminal payoff is one fixed uniform-equilibrium target: for every epsilon>0,
the SAME profile delivers that target within epsilon and caps every complete
unilateral deviation for every sufficiently long finite horizon.

The producer covers three overlapping closed regions:

- 0<=delta<=7/5: certified periodic return maps, including the junction1/1000;
- 7/5<=delta<=12: a connected stationary-root curve and an intermediate-value argument;
- delta>=12: one explicit fixed stationary hazard vector.

No continuation values, roots, cycles or strategic certificates are inputs.
The finite checks below construct the first two regions from the raw table.

## 2. Literal Nash root maps

For independent hazards q and native continuation b, let T be the product
opponent coalition and put

    H_i=product_(j!=i)(1-q_j),
    P_i=E[Z_i(T)], Q_i=E[Z_i(T union {i})], C_i=P_i+H_i b_i,

where Z_i(empty)=0. Active owners mix only when Q_i=C_i; an omitted owner
continues when Q_i<C_i. The payoff map returns Q on active owners and C
on omitted owners, so these comparisons are exact Nash comparisons at b.

For a triple S={i,j,k}, set the omitted hazard to zero. For active a with
active opponents u,v, write

    c_a=-b_a, a_a=b_a-A_au, b'_a=b_a-A_av,
    d_a=Delta_a({u,v})+A_au+A_av-b_a.

Then Q_a-C_a=c_a+a_a q_u+b'_a q_v+d_a q_u q_v. With z=q_k put
Nx=-c_j-b'_j z, Dx=a_j+d_j z, Ny=-c_i-b'_i z, Dy=a_i+d_i z.
Set q_i=Nx/Dx and q_j=Ny/Dy. The remaining equation has numerator

    c_k Dx Dy+a_k Nx Dy+b'_k Ny Dx+d_k Nx Ny=e0+e1 z+e2 z^2.

The low-parameter maps use z=(-e1+sqrt(e1^2-4e2e0))/(2e2). The checker
keeps the discriminant positive and every denominator nonzero. Substitution
proves the active equalities exactly, rather than inferring equality from
an interval which merely contains zero.

Middle-region maps use odds x_i=q_i/(1-q_i). Active indifference becomes
b_i=-A_iu x_u-A_iv x_v+Delta_i({u,v})x_u x_v. Set
X=2gamma/[beta+sqrt(beta^2+4alpha gamma)]. The following branches specify
all three active odds; the omitted odds are zero. Here d=delta.

    012: X=x0,
      alpha=b0+6-2d,
      beta=18/5-9b0/10+(6-d)b1+2b2+3d/2,
      gamma=9b0/10-b1b2-18b1/5+3b2/2,
      x1=(b2-dX)/(3/5+X), x2=(b1+X)/(3/2-X).
    023: X=x0,
      alpha=b0+21/50-2d/25,
      beta=21/50+d/100+2b2/25+db3-6b3,
      gamma=b0+b2b3+b2/100+6b3,
      x2=(7X/100-b3)/(1-X), x3=(dX-b2)/(1+X).
    123: X=x1,
      alpha=51/250+b1,
      beta=3/10-11b2/25+9b3/10,
      gamma=b1+2b2/5+3b3/2-b2b3,
      x2=(X/25-b3)/(1+X), x3=(3X/5-b2)/(1-X).

Substitution reduces each active equation to zero modulo
alpha X^2+beta X-gamma; the displayed X solves that quadratic. Literal
endpoints can be evaluated either by product probabilities or as

    C_i=[b_i+sum_(nonempty B subset I\{i}) Z_i(B) product_(j in B)x_j]
          /product_(j!=i)(1+x_j),
    Q_i=[sum_(B subset I\{i}) Z_i(B union {i}) product_(j in B)x_j]
          /product_(j!=i)(1+x_j).

All denominator, square-root, hazard and quiet-gap tests concern entire
parameter/fibre boxes. Write T_S for the resulting exact Nash payoff map.

## 3. A finite periodic cover of[0,7/5]

The following consecutive integer endpoints are divided by10^6. The first
segment uses backward word013^4,012^60. Every later segment uses backward
word012^n,023^p,123^2 with the indicated n,p.

| Left | Right | n | p |
| ---: | ---: | ---: | ---: |
| 0 | 1000 | low | low |
| 1000 | 19075 | 20 | 3 |
| 19075 | 23246 | 12 | 8 |
| 23246 | 36642 | 11 | 8 |
| 36642 | 52323 | 10 | 8 |
| 52323 | 71820 | 9 | 8 |
| 71820 | 96650 | 8 | 8 |
| 96650 | 125022 | 7 | 8 |
| 125022 | 158551 | 6 | 8 |
| 158551 | 189481 | 5 | 8 |
| 189481 | 205098 | 4 | 8 |
| 205098 | 213382 | 4 | 7 |
| 213382 | 247722 | 5 | 8 |
| 247722 | 380209 | 4 | 8 |
| 380209 | 616719 | 3 | 8 |
| 616719 | 1191180 | 2 | 8 |
| 1191180 | 1277319 | 1 | 7 |
| 1277319 | 1283705 | 1 | 6 |
| 1283705 | 1290123 | 1 | 5 |
| 1290123 | 1400000 | 1 | 6 |

Reverse the backward word to obtain physical chronology. Thus the low
return is F=T012^60 composed with T013^4 and the middle return is
F=T123^2 composed with T023^p composed with T012^n. Every physical word
has length at most64.

The finite certificate below subdivides each segment into closed cells,
using its literal rational step rule and halving failed attempts. A step
of zero fails validation. Accepted positive steps exhaust every segment.
For a cell[l,u], put d=(l+u)/2, h=(u-l)/2, and r=h/5 in the low region
or r=h/10 otherwise. The program constructs rational vectors c,v and checks
F on every fibre B_delta={c+v(delta-d)+e: ||e||_infinity<=r}.
Eight floating candidate iterations suggest c; exact midpoint derivatives,
a rational linear solve and rational rounding suggest v. No accuracy,
convergence or branch identity of the floating suggestion is assumed.

Exact outward interval assertions establish throughout each tube

    active hazards in(1/10^8,999/1000), omitted gaps <-1/10^6,
    L=sup ||D_bF||_infinity<9/10,
    R=max_i[|F_d(c)_i-c_i|+h sup|(D_bF v+partial_delta F)_i-v_i|],
    R+Lr<r.                                                   (2)

Along the affine center, the residual derivative is D_bF v+partial_delta F-v.
The mean-value theorem bounds its displacement by R; the b-Lipschitz bound
then proves F(B_delta) lies strictly inside B_delta. Banach contraction
produces a fixed point for EVERY delta in the closed cell. Fixed points
chosen in adjacent cells need not be identified for this existence claim.

For completeness, each interval operation rounds outward to multiples of
2^(-512). Propagate derivatives in the five initial coordinates(e,delta-d),
starting with[I|v]. At each phase compute the local derivative
[D_bT|partial_delta T] on the current enclosure and the full parameter cell;
chain it with the previous derivative and add its last column to the
parameter column. Recenter the value at the separately enclosed midpoint
orbit plus this derivative enclosure applied to[-r,r]^4 times[-h,h]. The
mean-value theorem on the convex initial box proves the enclosure by induction.
Both varying reward entries and A20=-delta are retained at every phase.
All acceptance comparisons are integer or rational comparisons.

## 4. A connected stationary curve covers[7/5,12]

Put h=product_i(1-q_i). For positive absorption, stationary payoff is
U_i=[q_i Q_i+(1-q_i)P_i]/(1-h). Define the stationary field

    F_i=(1-H_i)Q_i-P_i.

Then Q_i-(P_i+H_i U_i)=F_i/(1-h), so stationary Nash requires F_i=0
on proper active owners, F_i<=0 on quiet owners and F_i>=0 on sure owners.
Only F2 depends on delta. Fix z=q2 and x=(q0,q1,q3), and let
f(x,z)=(F0,F1,F3), evaluated at delta0. The coefficient of delta in F2 is

    C(x)=(1-H2/10)q0(1-q1)(1-q3)>0.

Thus any proper zero of f becomes full stationary Nash at
D(x,z)=-F2(x,z;0)/C(x). This scalar function is continuous on the proper cube.

The certificate partitions[1/10000,3/50] into643 closed cells by repeatedly
setting u=min(101*l/100,3/50). For each cell define m=(l+u)/2,h=(u-l)/2.
Rational candidate Newton steps construct c,s, positive radii r_i=c_i/1000
and an invertible rational matrix B. On the WHOLE tube
x=c+s(z-m)+e, |e_i|<=r_i, l<=z<=u, interval tests verify proper hazards and

    K=I-B D_xf, v=-B(D_xf s+partial_z f),
    R_i=|(B f(c,m))_i|+h sup|v_i|,
    M_i=sum_j sup|K_ij|r_j,
    max_i M_i/r_i<1/4,       R_i+M_i/4<r_i/4.                 (3)

Arithmetic uses the same outward interval operations. Candidate accuracy is never
assumed. For fixed z the map x->x-Bf(x,z) contracts in the weighted infinity
norm determined by r. Its center residual is bounded by R, so(3) makes the
INNER cube |e_i|<=r_i/4 invariant. Its root is unique in the outer cube and
continuous in z. At each shared endpoint, the checker also verifies

    |c_left(z)-c_right(z)|_i+r_left,i/4<r_right,i.             (4)

The left root then belongs to the right outer cube and equals its unique
root. These are therefore one continuous proper curve x(z), not unrelated
roots at sampled parameters. Endpoint evaluation over the inner root boxes
proves exactly

    D(x(1/10000),1/10000)>12,
    D(x(3/50),3/50)<7/5.                                    (5)

The IVT supplies every delta in[7/5,12], without assuming monotonicity of D.
All four hazards are proper and all stationary fields vanish at the produced
root. Invertibility of B makes a fixed point of x-Bf equivalent to f=0.

## 5. One fixed stationary profile covers[12,infinity)

Let t=(15-sqrt(205))/20 and

    q0=1/[2(1-t)], q1=t, q2=1, q3=(6-5t)/(7-5t).

Here0<t<1/20, 20t^2-30t+1=0, and the other three hazards are proper.
Since q2=1, H_i=0 for i!=2. Literal expansion gives F0=F3=0 and
F1=(20t^2-30t+1)/[4(t-1)(5t-7)]=0. Reducing the remaining field gives

    F2=[18000 delta t-26820 delta-211532 t+303811]
          /[8000(t-1)(5t-7)^2].                            (6)

Its denominator and its numerator's delta coefficient are negative. At
delta=12 its numerator is4468t-18029<0. Hence F2>0 for every delta>=12.
This is one stationary Nash vector for that entire unbounded interval.

## 6. Full behavioral, uniform-payoff and source correspondence

The periodic fixed-point annotations obey exact prescribed payoff recursion.
Their bounded continuation remainders vanish because absorption is geometric,
so they ARE the actual terminal payoffs. The stationary formula in Section4
has the same property. At each periodic phase, after deleting any one owner,
at least two scheduled opponents still quit with hazards greater than10^(-8).
For each fixed stationary-curve profile all opponents have positive hazards.
For the explicit sure profile, deleting owner2 leaves q0>1/2, and deleting
another owner leaves owner2 sure. Thus every unilateral replacement has a
geometric opponent-absorption bound, including literal Never replacements.

Iterating the exact root inequalities bounds every complete behavioral
deviation by the prescribed value; the unresolved continuation term vanishes
uniformly over the deviator. Adding signed s_i shifts every such terminal
payoff by exactly s_i, since all prescribed and deviating paths absorb.
The same profiles are consequently exact terminal Nash for the original table.
With finite reward bound M, uniform finite expected absorption time bounds
the terminal versus N-stage-average difference by O(M/N), uniformly over all
replacements. Each fixed profile's actual terminal payoff is the fixed UE
target. The endpoints and overlaps0,1/1000,7/5 and12 leave no missing boundary case.

The actual data supply the hypotheses of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`), and of
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`). These existing
consumers were inspected; the new contribution is the raw-table producer,
not another conditional consumer. No new Lean implementation is claimed.

The formalization target is: from delta>=0 and s, produce K with1<=K<=64,
a cycle and value satisfying the periodic compiler's hpolicy, hnash and
hcontracts; the stationary pieces use K=1. First implement the raw table,
algebraic branches and rational interval bounds, then the parametric Banach
and seam/IVT producers, and apply the existing compilers. None of these
strategic data is assumed as a theorem input.

## 7. Uniform raw-neighborhood corollary

There is eta>0 such that EVERY raw table satisfying
|r_i(D)-s_i-Z_i^delta(D)|<eta for some delta>=0 and finite signed s has an
exact terminal equilibrium of period at most64 and a fixed UE payoff.

For the periodic region, smooth active root branches have nonsingular active
probability Jacobians: differentiation in active continuation coordinates
gives a right inverse because their continuation Jacobian is diagonal -H_i.
The return Jacobian I-D_bF is invertible by(2). Thus the IFT and the strict
hazard/quiet margins preserve each cycle; compactness of[0,7/5] gives a
uniform raw radius. For[7/5,12], all finitely many strict Newton-tube and seam
inequalities persist under small raw perturbations. They supply the same
continuous opponent-equilibrium curve; F2 has uniformly opposite strict
signs at its endpoints by(5) and C>0. The IVT persists without requiring
D'(z)!=0. For the sure tail, the Jacobian of(F0,F1,F3) in(q0,q1,q3) at the
explicit root is -sqrt(205) in determinant. The IFT preserves this proper
opponent root independently of delta. The remaining field is delta*C(q)+B(q),
with C(q)>0 and strictly positive field at12. Both signs persist uniformly
under small raw changes, covering every delta>=12. Take the minimum of the
three radii. Opponent absorption persists throughout, so arbitrary row offsets
preserve the conclusions. The radius is existential; no common payoff target
or horizon threshold for different reward tables is asserted.

## 8. Standalone exact certificate

The following Python3 program uses only the standard library. It contains
the entire raw table, branch formulas, parameter segments, candidate routines,
and exact acceptance tests used above. Its successful finite execution is
the computational input to Sections3 and4; no generated data files are inputs.

```python
"""Exact finite certificates for the complex-spectrum family on its entire ray.
Python 3 standard library only. Floats choose candidate centers; every
acceptance test uses outward integer intervals. No external data is read.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import time
BITS=512;D=1<<BITS
class Iv:
 def __init__(self,lo,hi=None,raw=False):
  if raw:self.lo,self.hi=lo,hi;return
  x=F(lo);self.lo=x.numerator*D//x.denominator;self.hi=-((-x.numerator*D)//x.denominator)
 @classmethod
 def box(cls,c,r):
  a=cls(F(c)-F(r));b=cls(F(c)+F(r));return cls(a.lo,b.hi,True)
 def __add__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);return Iv(self.lo+o.lo,self.hi+o.hi,True)
 __radd__=__add__
 def __neg__(self):return Iv(-self.hi,-self.lo,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);xs=[a*b for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(xs)//D,-((-max(xs))//D),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not o.lo<=0<=o.hi,('zero denominator',o.lo,o.hi)
  pairs=[(a*D,b)for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(a//b for a,b in pairs),max(-((-a)//b)for a,b in pairs),True)
 def __rtruediv__(self,o):return iv(o)/self
 def sqrt(self):
  assert self.lo>0
  a=isqrt(self.lo*D);b=isqrt(self.hi*D)
  return Iv(a,b+(b*b<self.hi*D),True)
 def absupper(self):return max(-self.lo,self.hi)
 def lower(self):return float(F(self.lo,D))
 def upper(self):return float(F(self.hi,D))
 def __repr__(self):return str((self.lower(),self.upper()))
def iv(x):return x if isinstance(x,Iv)else Iv(x)
class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*5 if d is None else d
 def __add__(self,o):
  o=jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return Jet(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-jet(o)
 def __rsub__(self,o):return jet(o)+-self
 def __mul__(self,o):
  o=jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=jet(o);v=self.v/o.v
  return Jet(v,[(a-v*b)/o.v for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return jet(o)/self
 def sqrt(self):
  v=self.v.sqrt();return Jet(v,[a/(2*v)for a in self.d])
def jet(x):return x if isinstance(x,Jet)else Jet(x)

A=[[F(x)for x in row]for row in[[0,1,-6,'-.01'],[1,0,'-1.5','-.4'],[0,'-.6',0,1],['-.07','-.04',1,0]]]
J=[[F(x)for x in row]for row in[[0,'.01','5.4','.001'],['.01',0,'.15','.36'],[0,'.54',0,'.01'],['.063','.004','.01',0]]]
Z={}
for i in range(4):
 Z[i,1<<i]=F(0)
 for j in range(4):
  if i!=j:Z[i,1<<j]=A[i][j]+J[i][j];Z[i,(1<<i)|(1<<j)]=J[i][j]
for pair,sg in zip(combinations(range(4),2),(1,-1,1,1,-1,-1)):
 mask=sum(1<<j for j in pair);outside=[i for i in range(4)if i not in pair]
 for n,i in enumerate(outside):
  delta=sg*(-1 if n else 1);Z[i,mask]=F(max(0,-delta));Z[i,mask|(1<<i)]=F(max(0,delta))
for i in range(4):Z[i,15^(1<<i)]=F(1);Z[i,15]=F(0)
assert len(Z)==60

def coeff(a,u,v,b):
 delta=Z[a,(1<<a)|(1<<u)|(1<<v)]-Z[a,(1<<u)|(1<<v)]
 return -b[a],b[a]-A[a][u],b[a]-A[a][v],delta+A[a][u]+A[a][v]-b[a]
def mul(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
def probability_step(b,S):
 i,j,k=map(int,S)
 ci,ai,bi,di=coeff(i,j,k,b);cj,aj,bj,dj=coeff(j,i,k,b);ck,ak,bk,dk=coeff(k,i,j,b)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 terms=[mul(dx,dy),mul(nx,dy),mul(ny,dx),mul(nx,ny)]
 cc=[sum(t[l]*a for t,a in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 disc=cc[1]*cc[1]-4*cc[2]*cc[0]
 zz=(-cc[1]+disc.sqrt())/(2*cc[2]);q=[Jet(0)]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 out=[];gs=[]
 for a in range(4):
  opp=[l for l in range(4)if l!=a];P=Jet(0);Q=Jet(0);H=Jet(1)
  for l in opp:H*=1-q[l]
  for bits in range(8):
   mask=0;wt=Jet(1)
   for ii,l in enumerate(opp):
    if bits>>ii&1:mask|=1<<l;wt*=q[l]
    else:wt*=1-q[l]
   if mask:P+=wt*Z[a,mask]
   Q+=wt*Z[a,mask|(1<<a)]
  out.append(Q if a in (i,j,k) else P+H*b[a]);gs.append(Q-(P+H*b[a]))
 return out,q,gs
from math import sqrt, prod
import sys
m=sys.modules[__name__]
I=range(4);WORD=['013']*4+['012']*60
C0=[.0041188900253007926,.0001243482175163462,.000041907755608047286,.36900861598844355]

def setparam(p):
 A[2][0]=-p;Z[2,1]=-F(9,10)*p;Z[2,5]=p/10

def floating_step(b,S,aa,zz):
 i,j,k=map(int,S)
 def cf(a,u,v):
  dd=zz[a,(1<<a)|(1<<u)|(1<<v)]-zz[a,(1<<u)|(1<<v)]
  return -b[a],b[a]-aa[a][u],b[a]-aa[a][v],dd+aa[a][u]+aa[a][v]-b[a]
 ci,ai,bi,di=cf(i,j,k);cj,aj,bj,dj=cf(j,i,k);ck,ak,bk,dk=cf(k,i,j)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 terms=[mul(dx,dy),mul(nx,dy),mul(ny,dx),mul(nx,ny)]
 cc=[sum(t[l]*a for t,a in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 z=(-cc[1]+sqrt(cc[1]*cc[1]-4*cc[2]*cc[0]))/(2*cc[2]);q=[0.]*4
 q[i]=(nx[0]+nx[1]*z)/(dx[0]+dx[1]*z);q[j]=(ny[0]+ny[1]*z)/(dy[0]+dy[1]*z);q[k]=z
 out=[]
 for a in I:
  opp=[l for l in I if l!=a];P=Q=0.;H=prod(1-q[l]for l in opp)
  for bits in range(8):
   mask=sum(1<<l for ii,l in enumerate(opp)if bits>>ii&1)
   w=prod(q[l]if bits>>ii&1 else 1-q[l]for ii,l in enumerate(opp))
   if mask:P+=w*zz[a,mask]
   Q+=w*zz[a,mask|(1<<a)]
  out.append(Q if a in(i,j,k)else P+H*b[a])
 return out

def solve_linear(a,b):
 rows=[list(row)+[rhs]for row,rhs in zip(a,b)]
 for j in I:
  pivot=next(i for i in range(j,4)if rows[i][j])
  rows[j],rows[pivot]=rows[pivot],rows[j]
  z=rows[j][j];rows[j]=[x/z for x in rows[j]]
  for i in I:
   if i!=j:
    z=rows[i][j];rows[i]=[x-z*y for x,y in zip(rows[i],rows[j])]
 return [row[-1]for row in rows]

def pointjets(c,d):
 setparam(Jet(d,[Iv(0)]*4+[Iv(1)]))
 b=[Jet(v,[Iv(int(i==j))for j in range(5)])for i,v in enumerate(c)]
 for S in WORD:b,_,_=step(b,S)
 return b

def center(d):
 setparam(d);aa=[[float(x)for x in row]for row in A];zz={k:float(v)for k,v in Z.items()}
 c=C0[:]
 for _ in range(8):
  for S in WORD:c=floating_step(c,S,aa,zz)
 c=[F(str(x))for x in c];jets=pointjets(c,d)
 mid=lambda v:F(v.lo+v.hi,2*D)
 L=[[F(i==j)-mid(jets[i].d[j])for j in I]for i in I]
 z=[mid(x.d[4])for x in jets];slope=solve_linear(L,z)
 slope=[F((v.numerator*10**20)//v.denominator,10**20)for v in slope]
 return c,slope
def odds_step(b,S):
 b0,b1,b2,b3=b;d=-m.A[2][0];S=tuple(map(int,S))
 if S==(0,1,2):
  aa=b0+6-2*d;bb=F(18,5)-F(9,10)*b0+(6-d)*b1+2*b2+F(3,2)*d;cc=F(9,10)*b0-b1*b2-F(18,5)*b1+F(3,2)*b2
  x=2*cc/(bb+(bb*bb+4*aa*cc).sqrt());y=(b2-d*x)/(F(3,5)+x);z=(b1+x)/(F(3,2)-x)
  odds=[x,y,z,m.Jet(0)]
 elif S==(0,2,3):
  aa=b0+F(21,50)-F(2,25)*d;bb=F(21,50)+d/100+F(2,25)*b2+d*b3-6*b3;cc=b0+b2*b3+b2/100+6*b3
  x=2*cc/(bb+(bb*bb+4*aa*cc).sqrt());y=(F(7,100)*x-b3)/(1-x);z=(d*x-b2)/(1+x)
  odds=[x,m.Jet(0),y,z]
 elif S==(1,2,3):
  aa=F(51,250)+b1;bb=F(3,10)-F(11,25)*b2+F(9,10)*b3;cc=b1+F(2,5)*b2+F(3,2)*b3-b2*b3
  x=2*cc/(bb+(bb*bb+4*aa*cc).sqrt());y=(x/25-b3)/(1+x);z=(F(3,5)*x-b2)/(1-x)
  odds=[m.Jet(0),x,y,z]
 else:raise ValueError(S)
 out=[];g=[]
 for i in range(4):
  cn=b[i];qn=m.Jet(0);den=m.Jet(1)
  for j in range(4):
   if i!=j:den*=1+odds[j]
  for mask in range(16):
   if mask>>i&1:continue
   w=m.Jet(1)
   for j in range(4):
    if mask>>j&1:w*=odds[j]
   if mask:cn+=m.Z[i,mask]*w
   qn+=m.Z[i,mask|(1<<i)]*w
  C,Q=cn/den,qn/den
  out.append(Q if i in S else C);g.append(Q-C)
 return out,[x/(1+x)for x in odds],g

LOW=True
def step(b,S):return probability_step(b,S)if LOW else odds_step(b,S)
def verify(left,right):
 d=(left+right)/2;h=(right-left)/2;r=h/(5 if LOW else 10);c,slope=center(d)
 point=[m.Jet(x)for x in c]
 b=[m.Jet(m.Iv.box(c[i],r+abs(slope[i])*h),[m.Iv(int(i==j))for j in I]+[m.Iv(slope[i])])for i in I]
 radii=[m.Iv.box(0,r)]*4+[m.Iv.box(0,h)]
 minq=m.D;maxq=0;maxgap=-100*m.D
 for t,S in enumerate(m.WORD):
  m.setparam(d);point,_,_=m.step(point,S)
  old=[x.d[:]for x in b]
  local=[m.Jet(x.v,[m.Iv(int(i==j))for j in I]+[m.Iv(0)])for i,x in enumerate(b)]
  m.setparam(m.Jet(m.Iv.box(d,h),[m.Iv(0)]*4+[m.Iv(1)]))
  b,q,g=m.step(local,S)
  active=list(map(int,S));omitted=next(i for i in I if i not in active)
  assert all(q[i].v.lo>0 and q[i].v.hi<m.D for i in active),(t,'hazard')
  assert g[omitted].v.hi<0,(t,'gap')
  minq=min(minq,*(q[i].v.lo for i in active));maxq=max(maxq,*(q[i].v.hi for i in active));maxgap=max(maxgap,g[omitted].v.hi)
  for x in b:
   ld=x.d[:]
   x.d=[sum((ld[j]*old[j][c]for j in I),m.Iv(0))+(ld[4]if c==4 else m.Iv(0))for c in range(5)]
  for i in I:b[i].v=point[i].v+sum((radii[c]*b[i].d[c]for c in range(5)),m.Iv(0))
 lip=max(sum(F(x.absupper(),m.D)for x in row.d[:4])for row in b)
 residual=max(F((point[i].v-c[i]).absupper(),m.D)+h*F((b[i].d[4]-slope[i]).absupper(),m.D)for i in I)
 assert residual+lip*r<r,('selfmap',float(residual/r),float(lip))
 assert lip<F(9,10),('lip',float(lip))
 assert minq*10**8>m.D and maxq*1000<999*m.D and maxgap*10**6<-m.D,('margin')
 return [float(F(minq,m.D)),float(F(maxq,m.D)),float(F(maxgap,m.D)),float(lip),float(residual/r)]


# Exact parameter endpoints are these integers divided by10^6.
SEGMENTS=[
 (0, 1000, 0, 0),
 (1000, 19075, 20, 3),
 (19075, 23246, 12, 8),
 (23246, 36642, 11, 8),
 (36642, 52323, 10, 8),
 (52323, 71820, 9, 8),
 (71820, 96650, 8, 8),
 (96650, 125022, 7, 8),
 (125022, 158551, 6, 8),
 (158551, 189481, 5, 8),
 (189481, 205098, 4, 8),
 (205098, 213382, 4, 7),
 (213382, 247722, 5, 8),
 (247722, 380209, 4, 8),
 (380209, 616719, 3, 8),
 (616719, 1191180, 2, 8),
 (1191180, 1277319, 1, 7),
 (1277319, 1283705, 1, 6),
 (1283705, 1290123, 1, 5),
 (1290123, 1400000, 1, 6),
]

def run_periodic():
 global LOW,WORD,C0
 start=time.time();count=0;previous=0;bounds=[1.,0.,-100.,0.,0.]
 for left,right,n,p in SEGMENTS:
  assert left==previous and left<right
  LOW=(n==0);WORD=['013']*4+['012']*60 if LOW else ['012']*n+['023']*p+['123']*2
  C0=([.0041188900253007926,.0001243482175163462,.000041907755608047286,.36900861598844355]if LOW else
      [.6032426876986211,.1316536363074683,.3158582125684314,.0018524455688325833])
  a=left;segment_count=0
  while a<right:
   size=10 if LOW else max(1,a//(400 if a>=1200000 else 200 if a>=200000 else 50))
   size=min(size,right-a)
   while True:
    try:stats=verify(F(a,10**6),F(a+size,10**6));break
    except (AssertionError,ValueError,ZeroDivisionError,StopIteration):
     size//=2
     if size==0:raise
   a+=size;count+=1;segment_count+=1
   bounds=[min(bounds[0],stats[0])]+[max(bounds[i],stats[i])for i in range(1,5)]
  previous=right
  print('PASS segment',left,right,'word',n,p,'cells',segment_count,flush=True)
 assert previous==1400000
 print('PASS entire delta[0,7/5]:',count,'closedcells;',len(SEGMENTS),'wordsegments')
 print('Everyactiveq>1e-8,<.999; everyquietgap<-1e-6; returnLipschitz<.9; exactselfmaps.')
 print('Diagnostics only:',bounds,'seconds',time.time()-start)

R=F;SA=[0,1,3];SI=range(3)
def stationary_fields(x,z):
 q=[x[0],x[1],z,x[2]];out=[]
 for a in range(4):
  opp=[i for i in range(4)if i!=a];H=m.Jet(1);P=m.Jet(0);Q=m.Jet(0)
  for i in opp:H*=1-q[i]
  for mask in range(16):
   if mask>>a&1:continue
   w=m.Jet(1)
   for i in opp:w*=q[i]if mask>>i&1 else 1-q[i]
   if mask:P+=w*Z[a,mask]
   Q+=w*Z[a,mask|(1<<a)]
  out.append((1-H)*Q-P)
 return out

def stationary_solve(a,b):
 rows=[list(v)+[w]for v,w in zip(a,b)]
 for j in SI:
  k=next(k for k in range(j,3)if rows[k][j]);rows[j],rows[k]=rows[k],rows[j]
  t=rows[j][j];rows[j]=[u/t for u in rows[j]]
  for k in SI:
   if k==j:continue
   t=rows[k][j];rows[k]=[u-t*v for u,v in zip(rows[k],rows[j])]
 return [row[-1]for row in rows]

def stationary_candidate(z,seed):
 c=[R(str(v))for v in seed]
 mid=lambda v:R(v.lo+v.hi,2*m.D)
 for _ in range(4):
  ff=stationary_fields([m.Jet(v,[m.Iv(int(i==j))for j in range(5)])for i,v in enumerate(c)],m.Jet(z,[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)]))
  jj=[[mid(ff[a].d[j])for j in SI]for a in SA]
  cor=stationary_solve(jj,[mid(ff[a].v)for a in SA])
  c=[R(((v-e).numerator*10**24)//(v-e).denominator,10**24)for v,e in zip(c,cor)]
 ff=stationary_fields([m.Jet(v,[m.Iv(int(i==j))for j in range(5)])for i,v in enumerate(c)],m.Jet(z,[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)]))
 jj=[[mid(ff[a].d[j])for j in SI]for a in SA];pz=[mid(ff[a].d[3])for a in SA]
 cols=[stationary_solve(jj,[R(int(i==j))for i in SI])for j in SI]
 B=[[cols[j][i]for j in SI]for i in SI]
 s=stationary_solve(jj,[-v for v in pz]);s=[R((v.numerator*10**24)//v.denominator,10**24)for v in s]
 return c,s,B

def stationary_verify(l,u,previous=None):
 mid=(l+u)/2;h=(u-l)/2
 seed=[R('.00951132'),R('.00103676'),R('.10453273')]if previous is None else[x+ss*(mid-previous['mid'])for x,ss in zip(previous['c'],previous['s'])]
 c,s,B=stationary_candidate(mid,seed);r=[x/1000 for x in c]
 x=[m.Jet(m.Iv.box(v,rr+abs(ss)*h),[m.Iv(int(i==j))for j in range(5)])for i,(v,rr,ss)in enumerate(zip(c,r,s))]
 z=m.Jet(m.Iv.box(mid,h),[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)])
 for v in x:assert 0<v.v.lo<v.v.hi<m.D
 ff=stationary_fields(x,z);pp=stationary_fields([m.Jet(v)for v in c],m.Jet(mid))
 K=[[m.Iv(int(i==j))-sum((B[i][k]*ff[SA[k]].d[j]for k in SI),m.Iv(0))for j in SI]for i in SI]
 # All comparisons below use exact fractions, never these diagnostics.
 a=[R(sum((-B[i][k]*pp[SA[k]].v for k in SI),m.Iv(0)).absupper(),m.D)for i in SI]
 v=[sum((-B[i][k]*(ff[SA[k]].d[3]+sum((ff[SA[k]].d[j]*s[j]for j in SI),m.Iv(0)))for k in SI),m.Iv(0))for i in SI]
 Rr=[a[i]+h*R(v[i].absupper(),m.D)for i in SI]
 Mr=[sum(R(K[i][j].absupper(),m.D)*r[j]for j in SI)for i in SI]
 lip=max(Mr[i]/r[i]for i in SI)
 assert lip<R(1,4),('lip',float(l),float(lip))
 assert all(Rr[i]+Mr[i]/4<r[i]/4 for i in SI),('inner',float(l),[float((Rr[i]+Mr[i]/4)/r[i])for i in SI])
 if previous:
  cc=[c[i]+s[i]*(l-mid)for i in SI];pc=[previous['c'][i]+previous['s'][i]*(l-previous['mid'])for i in SI]
  assert all(abs(cc[i]-pc[i])+previous['r'][i]/4<r[i]for i in SI),('seam',float(l))
 return dict(c=c,s=s,r=r,mid=mid,l=l,u=u,lip=lip)

def stationary_delta_at(cell,z):
 cc=[m.Jet(m.Iv.box(cell['c'][i]+cell['s'][i]*(z-cell['mid']),cell['r'][i]/4))for i in SI]
 f=stationary_fields(cc,m.Jet(z))[2].v
 H=(1-cc[0].v)*(1-cc[1].v)*(1-cc[2].v)
 coef=(1-H/10)*cc[0].v*(1-cc[1].v)*(1-cc[2].v)
 return -f/coef

def run_stationary():
 setparam(F(0))
 start=time.time();l=R(1,10000);stop=R(3,50);previous=None;count=0;first=None;ml=R(0)
 ratio=R(101,100)
 while l<stop:
  u=min(l*ratio,stop);cell=stationary_verify(l,u,previous);first=first or cell;previous=cell;ml=max(ml,cell['lip']);l=u;count+=1
  if count%50==0:print('PASSCELLS',count,'z',float(u),'maxlip',float(ml),flush=True)
 low=stationary_delta_at(first,R(1,10000));high=stationary_delta_at(previous,R(3,50))
 assert low.lo>12*m.D,(low,'lowdelta')
 assert high.hi*5<7*m.D,(high,'highdelta')
 print('PASS ENTIRE STATIONARY CURVE',count,'cells;deltaendpoints',low,high,'seconds',time.time()-start,flush=True)

if __name__=='__main__':
 run_periodic()
 run_stationary()
 print('PASS finite periodic cover and continuous stationary bridge; combine with analytic sure tail.')
```
