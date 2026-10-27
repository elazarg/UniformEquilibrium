# An absorbing native Nash limit and uniform equilibrium for the M14 quitting table

## 1. Exact table and conclusions

There are four players, indexed0,1,2,3. At the unique live state each privately
chooses Continue or Quit. The first nonempty quitter coalition D absorbs;
live play and literal AllNever pay zero. Define native rewards Z by

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0],
    J=[0,-5,13,-5; 13,0,-5,-5; -5,-5,0,13; -5,13,-5,0].

For singleton{j}, Z_i({j})=Gamma_ij, including own singleton0. For a pair
{i,j}, its participant reward to i is J_ij. Every passive nonsingleton reward
is0. Every participant reward in a coalition of size at least3 is-5. These
rules specify all60 native reward coordinates. The original absorbing table
is r_i(D)=4+Z_i(D).

**Theorem.** There are actual finite independent-hazard profiles, followed by
literal Never, whose native full unilateral debts tend to0 and whose joint
Never probabilities tend to0. Consequently the augmented native semantic
carrier contains an absorbing full Nash point. In particular its absorbing
zero-observer-debt face at pivot2 has minimum pivot debt0.

The original table r has a uniform-equilibrium payoff

    w=4*1+b_*e2, for some b_* in I=[4/5,9/10].

The target is fixed before the accuracy. For every positive accuracy an
actual finite private independent-hazard word followed by Never delivers w
and controls every unilateral behavioral deviation on all sufficiently long
finite horizons. The proof constructs the words from the displayed table.
It does not assume an equilibrium continuation, a realized semantic minimum,
a positive-gap source, or any strategic witness beyond the raw rewards.

This closes the positive absorbing-gap obligation for this table directly,
including its actual and nonrealized source alternatives. It is a result for
the specified table, not a proof of the arbitrary four-player conjecture.

## 2. Finite proxy words and their closure

At a root let q_i in[0,1) be the independently chosen quitting probabilities,
x_i=q_i/(1-q_i), H_i=prod_(j!=i)(1-q_j), and c=prod_i(1-q_i). Write P_i for
the passive expected reward when i Continues and at least one opponent quits,
and Q_i for the immediate-Quit payoff. For this table, with L=J-Gamma,

    L=[0,-4,14,-7;14,0,-6,-6;-6,-7,0,14;-6,14,-6,0],
    C_i(x)=L_i x-5[sum_(j<k;j,k!=i)x_j x_k+prod_(j!=i)x_j],
    P_i=H_i Gamma_i x, Q_i=P_i+H_i C_i(x).

A finite word is a finite list of such product roots, with a terminal payoff
annotation u and terminal response-cap annotation v. The exact recursions are

    u'_i=q_i Q_i+(1-q_i)P_i+c u_i,
    v'_i=max(Q_i,P_i+H_i v_i).                              (1)

These annotations need not be the values of an actual continuation. A root
is Nash against a diagonal annotation u=v precisely when

    C_i(x)<=v_i for all i, with equality whenever x_i>0.     (2)

Then its payoff and cap outputs are equal. The cap is the full finite-word
cap: it prices every quitting deadline within the word and Continue to the
terminal annotation. Mixing these responses does not improve their maximum.

For a fixed root, each map in(1) is 1-Lipschitz in its own terminal annotation
for the sup norm. The same holds for a fixed finite word. Track also the
four marginal survivals N_i and joint survival nu=prod_i N_i.

For a fixed diagonal seed v let H_v be the closure of all tuples(U,B,N)
produced by arbitrary finite words with terminal annotation(v,v) and initial
terminal survival(1,1,1,1). Payoffs and caps are bounded by the largest native
reward or seed magnitude, so H_v is compact. Every fixed finite root-prefix
map preserves H_v by continuity: prefix it to the finite words approximating
any given point. If that point is diagonal and the new root satisfies(2),
its image is diagonal too.

Thus a sequence of exact Nash prefixes at diagonal points, whose value
vectors converge and whose survival coordinates converge, has its diagonal
limit in H_v. Several such limits may be composed by this same closure
argument. This is never an instruction to execute a continuation after
infinitely many dates. Every final point of H_v has finite-word approximants,
with both payoff and full cap converging. Those approximants need not be
exact Nash: their vanishing payoff-cap difference is what is consumed below.

All prefix operations below are described in BACKWARD order: each new root
is prepended to the existing continuation. A final finite chronological word
therefore lists the added roots in the reverse order.

## 3. Three singleton phases and eight finite atoms

Start with native diagonal seed b e2, b in I. If only owner j quits, with
odds x>=0, the root is Nash when

    v_j=0, L_ij x<=v_i for i!=j.                           (3)

Its incoming values are v'_j=0 and
v'_i=(v_i+Gamma_ij x)/(1+x), and its joint survival is1/(1+x).

For owner3 use x=v2/14. The quiet inequalities are
-7x<=v0, -6x<=v1, 14x<=v2; every current coordinate is nonnegative.
The pivot value follows v2'=13v2/(14+v2), tending geometrically to0.
The affine recursion gives the exact limit and survival

    (0,0,b,0) -> (2b/(1+b), b/(1+b),0,0),
    survival=1/(1+b).

Next, for owner2 use x=v0/14. Its quiet inequalities are
14x<=v0, -6x<=v1, -6x<=v3. The same recurrence reduces v0 to0, giving

    -> (0,3b/(1+3b),0,2b/(1+3b)),
    phase survival=(1+b)/(1+3b).

For owner0 use x=v1/14. Its quiet inequalities are
14x<=v1, -6x<=v2, -6x<=v3. Reducing v1 to0 gives

    S=(0,0,3c0,5c0), c0=b/(1+6b),
    phase survival=(1+3b)/(1+6b).                          (4)

The three phases together have survival1/(1+6b). Their limits and switches
are justified in H_(b e2) by Section2, without exact finite attainment of an
intermediate zero value. Every active coordinate is0 and every displayed
quiet inequality holds at every finite root of its phase.

After cumulative owner1 quitting probability a, owner1-only prefixes of S
have state

    v(a)=(-a,0,3c0+(2-3c0)a,5c0-(1+5c0)a).                (5)

A further owner1 root with odds x is Nash exactly when

    x>=a/4, 14x<=5c0-(1+5c0)a.                           (6)

The pivot comparison is automatic since its continuation is positive and
its joining increment is-7. Owner1's value0 makes it indifferent. The
smallest legal odds x=a/4 sends a to5a/(4+a); in coordinates y=a/(1-a) this
is y ->(5/4)y. It is permitted precisely when

    a<=a_*=10c0/(9+10c0), equivalently y<=10c0/9.

Starting at a=0, take one root with odds
x_first=(4/5)^6(10c0/9). It is admissible since
(4/5)^6=4096/15625<9/28, hence x_first<5c0/14. Its outgoing y equals
x_first. Follow it by SIX roots with smallest legal odds a/4; they reach
y=10c0/9 and a=a_* exactly. Use ONE MORE root with odds a_*/4, at which
both quiet0 and quiet3 are tied. This is exactly eight finite roots.

Their final cumulative a is25c0/(18+25c0). Substituting in(5) yields

    v=lambda(-25,0,104,65),
    lambda=b/(18+133b) in[2/311,1/153].                   (7)

The survival of the three phases and eight atoms together is

    18/(18+133b)<=45/311=:theta<1.                        (8)

The negative v0 is legitimate: inequality x>=a/4 prices its response at
every atom. No propagation of positive conditional caps is assumed.

## 4. The three-observer return from the explicit ray

We now prepend roots whose active support is O=(0,1,3), with pivot2 quiet.
In this section a three-vector x uses the order O; denote its coordinates
by x0,x1,x3. The relevant matrices and odds equations are

    G=[[0,-1,2],[-1,0,1],[1,-1,0]],
    J0=[[0,-5,-5],[13,0,-5],[-5,13,0]],
    L0=J0-G=[[0,-4,-7],[14,0,-6],[-6,14,0]],
    C0(x)=L0 x-R0(x), (R0)_i=5 prod_(j!=i)x_j,
    Q0_i(x)=[(J0 x)_i-(R0)_i(x)]/prod_(j!=i)(1+x_j).

Given current observer values v and pivot value beta, choose a positive
solution C0(x)=v. Its new observer values are Q0(x). Its pivot value is

    beta'=H(x)[beta+x0+2x1-x3], H(x)=prod_(j in O)(1+x_j)^-1.

This is a full Nash root, including the quiet pivot, exactly when

    beta>=C2(x),
    C2(x)=-6x0-7x1+14x3
                  -5(x0x1+x0x3+x1x3+x0x1x3).             (9)

### 4.1. A finite rational interval certificate

The fully specified verifier in Appendix A performs305 such prefixes for
EVERY input b in I. It covers I by the ten rational closed intervals
[k/100,(k+1)/100], k=80,...,89. The initial values are exactly(7), using
monotonicity of lambda=b/(18+133b) to enclose its input interval.

To control interval wrapping it tracks the observer coordinate z=T^-1 v,
where the fixed rational matrix is

    T=[[1000,876,-550],[398,-774,-1000],[89,-1000,960]].

Its inverse is computed exactly. At each stage a numerical Newton iteration
only nominates a rational center x_c and rational preconditioner B. No
floating assertion is used as evidence. The verifier encloses a positive
root box X, extends the input z box to contain T^-1 C0(x_c), and checks,
uniformly over the resulting observer-value box,

    ||I-B DC0(X)||_infinity=kappa<1,
    |B(C0(x_c)-v)|+|I-B DC0(X)| radius(X)<radius(X).

These exact inequalities prove that x ->x-B(C0(x)-v) is a strict self-map
and contraction on X for every permitted v. Thus a unique actual root
exists in X; an approximate numerical residual alone would not suffice.
Every X has all coordinates in(0,1/10), and(9) is checked strictly at
every stage, uniformly over the pivot interval.

The inverse enclosure follows from DC0^-1=(I-E)^-1 B, E=I-B DC0:

    |(DC0^-1-B)_ij|<=kappa/(1-kappa) max_k |B_kj|.

The output z is transported by T^-1 DQ0 DC0^-1 T. The pivot derivative
with respect to x is

    H(x)[(1,2,-1)_j-(beta+x0+2x1-x3)/(1+x_j)],

and its derivative with respect to beta is H(x). Mean-value transport is
taken from the VERIFIED center input C0(x_c), not the nominated midpoint.
The extended box contains every connecting segment. All interval operations
use rational outward rounding on the80-bit dyadic grid.

For every input tile the final odds box X and pivot interval BETA satisfy

    0<t:=sup X1<1/100000,
    inf X0>(3/5)sup X1, sup X0<(9/10)inf X1,
    inf X3>(2/5)sup X1, sup X3<(4/5)inf X1,
    BETA+[-640t,640t] subset (849/1000,861/1000).            (10)

Appendix A gives the complete algorithm and all raw rational inputs needed
to verify these finite inequalities; it stores no sampled root table. Its
finite tests assert(10) directly, not a numerical tolerance or a plot.

### 4.2. A uniform analytic cone closes the infinite tail

Put

    B0=L0^-1 J0
       =[[697/758,27/379,-35/758],
         [14/379,727/758,-15/758],
         [-8/379,63/379,275/379]].

Suppose x is positive with x1=t<=1/100000 and

    3/5<=x0/t<=9/10, 2/5<=x3/t<=4/5.                     (11)

We construct the next observer Nash root y from C0(y)=Q0(x). The maximum
absolute row sum of J0 is18, and each nonlinear row R0 is5 times a product
of two coordinates. Since x_i<=t and
1-prod_(j!=i)(1+x_j)^-1<=2t, one has

    ||Q0(x)-J0 x||_infinity<=41t^2<42t^2.

The exact norms satisfy ||L0^-1||_infinity=69/379 and
||B0||_infinity<26/25. On the box |y-B0x|_infinity<=12t^2, one has
|y|_infinity<=2t and |R0(y)|_infinity<=20t^2. Consequently

    y -> L0^-1[Q0(x)+R0(y)]

maps that box strictly into itself because (69/379)(42+20)<12. Its
Lipschitz constant is at most(69/379)20t<1. Hence its unique fixed point
is a positive exact root and satisfies |y-B0x|_infinity<=12t^2.

The four cone inequalities and y1<(99/100)t follow from checking the four
corners (x0/t,x3/t) in{3/5,9/10}x{2/5,4/5}. For example the two x0
inequalities require

    (B0x)_0-(3/5)(B0x)_1>12(8/5)t^2,
    (9/10)(B0x)_1-(B0x)_0>12(19/10)t^2.

The other two have factors7/5 and9/5. Each left side is affine in the two
ratios, so corner verification is complete. Appendix A verifies these exact
strict inequalities at t=1/100000, and the component positivity and shrink
bound there; smaller t only improves them. Thus(11) is invariant and the
successive t values decrease geometrically with ratio99/100.

For |beta|<=1 the pivot update at root y obeys

    |beta'-beta|<=|y0+2y1-y3|+|beta|sum_j y_j
                    <=(32/5)y1.

The total change on all later roots is therefore at most640t. Starting
from(10), this bound bootstraps every pivot value into[4/5,9/10]: any first
exit would violate the same partial-sum bound, which is valid while
|beta|<=1. In particular the uniform bound[7/10,1] remains valid. The
quiet comparison(9) holds strictly because

    C2(y)<=14y3<=14(4/5)/100000<7/10.

All observer roots stay positive and proper. Their values Q0(y) tend to0,
while beta has a limit b' in(849/1000,861/1000) subset I. The accumulated
survival coordinates converge since they are monotone; the tail hazard sum
is finite by the geometric estimate. The closure argument in Section2
therefore gives a diagonal endpoint b'e2, as a limit of finite proxy words.
No actual continuation after infinitely many dates is used.

Combining Sections3 and4 proves: for every b in I there is b' in I such
that, for every eta>0, some finite word W satisfies

    ||T_W^U(b e2)-b'e2||_infinity<=eta,
    ||T_W^B(b e2)-b'e2||_infinity<=eta,
    c(W)<=theta+eta, theta=45/311.                        (12)

The same b' is used at every accuracy for that b. Its existence is proved
from the raw table; no continuity or single-valued choice of the return map
is needed below. Later013 roots cannot increase the survival bound(8).

## 5. Actual profiles, a fixed target, and native absorption

Choose b0 in I and successively choose bj in I returned from b_(j-1) by(12).
For a fixed K choose finite words Wj with accuracy eta at these ideal inputs.
Put WK before W_(K-1) before ... before W1 and use terminal native proxy
annotation b0 e2. Nonexpansiveness of(1) gives its proxy outputs U*,B* and
joint survival c_total with

    ||U*-bK e2||_infinity<=K eta,
    ||B*-bK e2||_infinity<=K eta,
    c_total<=(theta+eta)^K.                               (13)

Every word is chosen against its ideal diagonal input. A preceding finite
approximation may have a different annotation, but its entire payoff/cap
error increases by at most eta at the next step. Thus(13) justifies all
finite switches, rather than assuming a finite phase reaches a zero cap
exactly. All words and their lengths are selected before play begins.

For the original table give the same word terminal proxy payoff and cap
w0=4*1+b0 e2. Adding4 to all native absorbing rewards and to the terminal
annotation adds exactly4 to both finite-word outputs. The proxy outputs
are4*1+U* and4*1+B*.

Now prescribe the same finite independent hazards and literal Never after
the word in the actual original game. Its prescribed tail payoff is0; its
FULL tail response cap is4, since a lone deviator may Quit later for its
own singleton4. Since w0>=4*1, root-cap monotonicity and the exact payoff
recursion give

    U_actual=4*1+U*-c_total w0,
    B_actual<=4*1+B*,
    0<=d_actual,i<=2K eta+(49/10)(theta+eta)^K.             (14)

Only joint survival is required: the terminal proxy cap majorizes the true
postword cap. Every behavioral deviation is covered. Along the unique live
history, private random bits determine a first Quit date or Never; the root
maxima price all dates in the finite word, and the true postword cap prices
all later choices. Averaging complete responses cannot improve their supremum.

Given any positive terminal accuracy, first choose K large and then eta
small in(14). This supplies actual terminal approximate Nash at every error.
For a fixed target, choose one infinite orbit bj and a sequence eta_K with
K eta_K->0 and(theta+eta_K)^K->0. Compactness of I gives a subsequence with
bK->b_* in I. Along this subsequence, actual payoffs tend to
w=4*1+b_*e2 and all full debts tend to0. The target is selected once, before
the requested accuracy, not independently for each error.

The SAME finite words prove the native assertion. Replace native terminal
proxy b0e2 by actual native Never, whose payoff and full cap are both0.
This is legitimate because own native singleton rewards are0. Then

    U_native=U*-c_total b0e2, B_native<=B*,
    0<=d_native,i<=2K eta+(9/10)(theta+eta)^K,
    nu_native=c_total->0.                                (15)

Bounded augmented payoff/cap/Never tuples have a convergent subsequence.
Its limit is absorbing and has zero debt for every player. Thus the native
absorbing observer-feasible minimum pivot debt is0; the conclusion is not
inferred from original UE by an unproved converse normalization.

## 6. Uniform finite horizons

For one finite profile just constructed, let T be its last possible
prescribed Quit date. Original rewards lie in[-1,17]. Prescribed absorption
occurs by T or never, so its H-stage average payoff differs from its terminal
payoff by at most17(T+1)/H. Against any unilateral behavioral deviation, if
an opponent quits then absorption occurs by T. Otherwise only the deviator
can quit after T, receiving positive own-singleton4, or Never for0. Delaying
this positive payment cannot increase its finite average above its terminal
payoff. Hence its H-stage payoff is at most its terminal payoff plus
17(T+1)/H, uniformly over all behavioral deviations. Every H-stage gain is
therefore at most

    max_i d_i+34(T+1)/H.

Choose one profile making terminal target error and debt small, then one
horizon threshold making this last remainder small. The same profile works
for every larger horizon. This proves the uniform payoff claim with its
fixed target w and unrestricted behavioral deviations.

## 7. Boundary checks, source correspondence and handoff

The singleton phases and the eight atoms check every quiet player's root
comparison, including the negative intermediate observer0 values. The final
return certificate verifies all305 finite quiet-pivot comparisons on each
of ten complete input intervals; the analytic cone proves all later ones.
The uniform return interval is strictly inside the starting interval, and
the survival bound is strictly below1. No inference is drawn merely from
small numerical residuals, a finite search, or a selected local minimum.

The artificial terminal proxy need not be an actual payoff. Using a proxy
below the actual postword cap would invalidate(14); the displayed w0 is
above that cap coordinatewise. Likewise, repeated exact Nash roots at
improperly switched finite phase boundaries are not assumed. Closure and
the uniform nonexpansiveness in Section2 are essential to(12)-(13).

The new contribution is an actual all-errors producer from the complete raw
table and, independently, the native absorbing zero-debt limit(15). It does
not merely verify a supplied return or impose another necessary condition on
a hypothetical minimum. Stationary, finite-root, cap-region and local-tail
restrictions do not supply the return constructed here. The proof uses no
stationary or finite-period completeness assertion.

The proxy calculus agrees with quittingTerminalSemanticPrefix and
quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. The latter is an
algebraic diagonal-annotation identity and does not require an actual tail.
Literal splicing is quittingTerminalSemanticPair_rootThenContinuation there.
The full behavioral cap recursion is
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean.

The stopping-law interfaces are
quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff and
quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue,
with their canonical law-realization counterparts, in
UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean.
The fixed-target semantic consumer is
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto in
UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.
These supply existing semantics, not a Lean proof of the new raw producer.

A formalization should encode the raw table, prove the finite proxy-pair
closure/nonexpansiveness lemmas, verify the singleton and eight-atom algebra,
verify the rational interval certificate and analytic cone, and then consume
the constructed finite words by(14)-(15) and the fixed-target theorem.
The artificial seed, negative intermediate values, and finite approximation
at every phase switch must be retained. No source realization, return
strategy, or improving profile should be introduced as an assumed field.
The present proof is ordinary mathematics with an exact finite certificate;
no new Lean compilation or formalization seal is claimed.

## Appendix A. Complete exact certificate reconstruction

The following standalone Python program needs only NumPy and SymPy. NumPy
is used solely to nominate rational centers and preconditioners. Every
acceptance test is a rational identity or a rational outward interval
inclusion. A poor nomination makes the program fail; it cannot turn a false
inclusion into a pass. The default invocation checks all ten tiles. No
external data, stored root centers, generated lookup tables, or other proof
files are required.

```python
"""M14 return certificate. Exact rational outward intervals verify every claim.
NumPy only nominates Newton centers; SymPy verifies fixed rational identities.
No external files or numerical tolerance can make an inclusion test pass.
"""
from fractions import Fraction as F
BITS=80; SCALE=1<<BITS
def down(x):return F(x.numerator*SCALE//x.denominator,SCALE)
def up(x):return -down(-x)
class I:
 def __init__(self,a,b=None):
  self.lo=down(F(a));self.hi=up(F(a if b is None else b))
 def __add__(a,b):
  b=co(b);return I(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo)
 def __sub__(a,b):return a+-co(b)
 def __rsub__(a,b):return co(b)+-a
 def __mul__(a,b):
  b=co(b);v=[x*y for x in(a.lo,a.hi) for y in(b.lo,b.hi)];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(a,b):
  b=co(b);assert b.lo*b.hi>0;return a*I(1/b.hi,1/b.lo)
 def __rtruediv__(a,b):return co(b)/a
 def __pow__(a,k):
  out=I(1)
  for _ in range(k):out=out*a
  return out
 def abs(a):return max(abs(a.lo),abs(a.hi))
 def mid(a):return (a.lo+a.hi)/2
 def rad(a):return (a.hi-a.lo)/2
 def __repr__(a):return f'[{float(a.lo):.12g},{float(a.hi):.12g}]'
def co(x):return x if isinstance(x,I) else I(x)
def matmul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def mv(a,v):return [sum(a[i][j]*v[j] for j in range(len(v))) for i in range(len(a))]
def norm(a):return max(sum(v.abs() for v in row) for row in a)
def prod(xs):
 out=I(1)
 for x in xs:out*=x
 return out
import numpy as np
import sympy as sp
L=[[0,-4,-7],[14,0,-6],[-6,14,0]]
J=[[0,-5,-5],[13,0,-5],[-5,13,0]]
G=[[0,-1,2],[-1,0,1],[1,-1,0]]
Ln=np.array(L,dtype=float)
T=[[1000,876,-550],[398,-774,-1000],[89,-1000,960]]
Ti=[[F(z.p,z.q) for z in row] for row in sp.Matrix(T).inv().tolist()]
Tn=np.array(T,dtype=float);Tin=np.linalg.inv(Tn)
def ci(x):
 return [sum(L[i][j]*x[j] for j in range(3))-5*prod([x[j] for j in range(3) if j!=i]) for i in range(3)]
def di(x):
 return [[I(0) if i==j else L[i][j]-5*x[3-i-j] for j in range(3)] for i in range(3)]
def cn(x):return Ln@x-np.array([5*np.prod(np.delete(x,i)) for i in range(3)])
def dn(x):return np.array([[0 if i==j else L[i][j]-5*x[3-i-j] for j in range(3)] for i in range(3)])
def nominate(v):
 x=np.linalg.solve(Ln,v)
 for k in range(40):
  e=cn(x)-v
  if max(abs(e))<1e-13*max(max(abs(v)),1e-12):return x
  x-=np.linalg.solve(dn(x),e)
 raise AssertionError('nomination failed')
def qi(x):
 H=[prod([1/(1+x[j]) for j in range(3) if j!=i]) for i in range(3)]
 inner=[sum(J[i][j]*x[j] for j in range(3))-5*prod([x[j] for j in range(3) if j!=i]) for i in range(3)]
 Q=[H[i]*inner[i] for i in range(3)]
 Qx=[[I(0) if i==j else H[i]*(J[i][j]-5*x[3-i-j]-inner[i]/(1+x[j])) for j in range(3)] for i in range(3)]
 return Q,Qx
def step(z,bp):
 vo=mv(T,z);vm=np.array([float(x.mid()) for x in vo]);xn=nominate(vm)
 xc=[F(float(x)) for x in xn];B=[[I(F(float(v))) for v in row] for row in np.linalg.inv(dn(xn))]
 cx=ci(list(map(I,xc)));zc=mv(Ti,cx)
 zext=[I(min(z[i].lo,zc[i].lo),max(z[i].hi,zc[i].hi)) for i in range(3)]
 vext=mv(T,zext)
 residual=mv(B,[cx[i]-vext[i] for i in range(3)])
 rad=[max(2*r.abs(),F(1,10**21)) for r in residual]
 for k in range(10):
  xb=[I(x-r,x+r) for x,r in zip(xc,rad)]
  assert min(a.lo for a in xb)>0 and max(a.hi for a in xb)<F(1,10),('positive small root',xb)
  E=[[I(int(i==j))-v for j,v in enumerate(row)] for i,row in enumerate(matmul(B,di(xb)))]
  kap=norm(E);assert kap<1,('Newton contraction',float(kap))
  need=[residual[i].abs()+sum(E[i][j].abs()*rad[j] for j in range(3)) for i in range(3)]
  if all(need[i]<rad[i] for i in range(3)):break
  rad=[max(rad[i],F(3,2)*need[i]) for i in range(3)]
 else:raise AssertionError('selfmap failed')
 inv=[[B[i][j]+I(-kap/(1-kap)*max(B[k][j].abs() for k in range(3)),kap/(1-kap)*max(B[k][j].abs() for k in range(3))) for j in range(3)] for i in range(3)]
 Q,Qx=qi(xb);Qc=qi(list(map(I,xc)))[0]
 Zc=mv(Ti,Qc);Dz=matmul(matmul(matmul(Ti,Qx),inv),T)
 delta=[z[i]-zc[i] for i in range(3)]
 zn=[Zc[i]+v for i,v in enumerate(mv(Dz,delta))]
 # Pivot is quiet. Its full prescribed/cap value uses the same root cap.
 H=prod([1/(1+x) for x in xb]);a=xb[0]+2*xb[1]-xb[2]
 C2=-6*xb[0]-7*xb[1]+14*xb[2]-5*(xb[0]*xb[1]+xb[0]*xb[2]+xb[1]*xb[2]+prod(xb))
 assert bp.lo>C2.hi,('quiet pivot',bp,C2)
 bmid=bp.mid();hc=prod([1/(1+I(x)) for x in xc]);ac=I(xc[0])+2*I(xc[1])-I(xc[2])
 bcenter=hc*(ac+bmid)
 ep_x=[[H*(g-(a+bp)/(1+x)) for g,x in zip([1,2,-1],xb)]]
 ep_z=matmul(matmul(ep_x,inv),T)[0]
 bn=bcenter+sum(ep_z[i]*delta[i] for i in range(3))+H*(bp-bmid)
 return zn,bn,xb
def verify(lo,hi,n=305):
 t=I(lo/(18+133*lo),hi/(18+133*hi))
 bp=104*t;z=[sum(Ti[i][j]*v for j,v in enumerate([-25,0,65]))*t for i in range(3)]
 maxkap=0
 for k in range(n):
  z,bp,x=step(z,bp)
  if k in [0,49,99,199,304] and hi-lo>F(1,100):print(k,bp,x,flush=True)
 assert x[1].hi<F(1,100000),(lo,hi,x)
 assert x[0].lo>F(3,5)*x[1].hi and x[0].hi<F(9,10)*x[1].lo,('cone0',x)
 assert x[2].lo>F(2,5)*x[1].hi and x[2].hi<F(4,5)*x[1].lo,('cone3',x)
 err=640*x[1].hi
 assert bp.lo-err>F(849,1000) and bp.hi+err<F(861,1000),(lo,hi,bp,float(err))
 return I(bp.lo-err,bp.hi+err)
def prefix_certificate():
 s=sp;b=s.symbols('b',positive=True);c=b/(1+6*b)
 G=s.Matrix([[0,-1,-1,2],[-1,0,1,1],[1,2,0,-1],[1,-1,1,0]])
 L=s.Matrix([[0,-4,14,-7],[14,0,-6,-6],[-6,-7,0,14],[-6,14,-6,0]])
 state=s.Matrix([0,0,b,0]);surv=s.Integer(1)
 for j,p in [(3,b/(1+b)),(2,2*b/(1+3*b)),(0,3*b/(1+6*b))]:
  assert state[j]==0
  state=((1-p)*state+p*G[:,j]).applyfunc(s.factor);surv=s.factor(surv*(1-p))
 assert state==s.Matrix([0,0,3*c,5*c]) and s.factor(surv-1/(1+6*b))==0
 ystar=10*c/9;astar=ystar/(1+ystar)
 assert s.Rational(4,5)**6<s.Rational(9,28)
 for k in range(8):
  a=-state[0];odds=s.Rational(4,5)**6*ystar if k==0 else a/4
  assert s.factor(state[1])==0
  gaps=[s.factor(state[i]-L[i,1]*odds) for i in (0,2,3)]
  if k==0:
   assert s.factor(gaps[2]-c*(5-s.Rational(140,9)*s.Rational(4,5)**6))==0
  else:
   assert gaps[0]==0
   assert s.factor(gaps[2]-(s.Rational(9,2)+5*c)*(astar-a))==0
   if k<7:assert s.factor(a/(1-a)-ystar*s.Rational(4,5)**(7-k))==0
   else:assert s.factor(a-astar)==0
  state=((state+odds*G[:,1])/(1+odds)).applyfunc(s.factor);surv=s.factor(surv/(1+odds))
 lam=b/(18+133*b)
 assert (state-lam*s.Matrix([-25,0,104,65])).applyfunc(s.factor)==s.zeros(4,1)
 assert s.factor(surv-18/(18+133*b))==0
 assert lam.subs(b,s.Rational(4,5))==s.Rational(2,311)
 assert lam.subs(b,s.Rational(9,10))==s.Rational(1,153)
 assert surv.subs(b,s.Rational(4,5))==s.Rational(45,311)
 print('PASS exact singleton-flow and eight-atom prefix identities.',flush=True)
def tail_certificate():
 s=sp;Q=s.Rational;Lm=s.Matrix(L);Jm=s.Matrix(J);B=Lm.inv()*Jm
 assert max(sum(abs(a) for a in Lm.inv().row(i)) for i in range(3))==Q(69,379)
 assert max(sum(abs(a) for a in B.row(i)) for i in range(3))<Q(26,25)
 assert max(sum(abs(a) for a in Jm.row(i)) for i in range(3))==18
 t=Q(1,100000)
 assert Q(26,25)+12*t<2 and Q(69,379)*(42+20)<12
 assert Q(69,379)*20*t<1
 for r in [Q(3,5),Q(9,10)]:
  for u in [Q(2,5),Q(4,5)]:
   w=B*s.Matrix([r,1,u])
   assert min(w)>12*t and w[1]+12*t<Q(99,100)
   assert w[0]-Q(3,5)*w[1]>12*Q(8,5)*t
   assert Q(9,10)*w[1]-w[0]>12*Q(19,10)*t
   assert w[2]-Q(2,5)*w[1]>12*Q(7,5)*t
   assert Q(4,5)*w[1]-w[2]>12*Q(9,5)*t
 assert Q(32,5)/(1-Q(99,100))==640
 assert 14*Q(4,5)*t<Q(7,10)
 print('PASS analytic positive-cone contraction and uniform pivot-tail remainder.',flush=True)
if __name__=='__main__':
 prefix_certificate();tail_certificate()
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--tiles',type=int,default=10);a=p.parse_args()
 for k in range(a.tiles):
  lo=F(4,5)+F(k,10*a.tiles);hi=F(4,5)+F(k+1,10*a.tiles)
  out=verify(lo,hi);print('PASS tile',k,'input',float(lo),float(hi),'return',out,flush=True)
```
