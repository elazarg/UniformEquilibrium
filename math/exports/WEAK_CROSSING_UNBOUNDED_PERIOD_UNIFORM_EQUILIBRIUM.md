# Weak-crossing uniform equilibria selected by an unbounded number of triple phases

This packet produces an equilibrium for every sufficiently small positive
parameter in an explicit sixty-reward family, and for a full-dimensional raw
neighborhood of each such table. It selects a finite period from the raw
parameter by a geometric scale rule; it does not assume a supplied finite
cycle. The selected periods tend to infinity at the boundary, without any
claim that all equilibria require long periods. The general four-player
quitting-game uniform-equilibrium conjecture remains open.

Every table in the whole comparison interval [0,1/1000] has a uniform positive
exploitability gap within the stationary and fixed-disjoint-pair two-phase
architectures, no sure-first root with any behavioral tail, and no available
response-quotient degree escape. Further complete raw-condition exclusions
are proved below. The family producer's threshold is existential; no claim
that it covers the entire comparison interval is inferred. No statement bounds the validity neighborhood of any other local
construction around parameter1/1000, or rules out its continuation to a
smaller parameter.

All claims are ordinary mathematics, with exact finite interval and integer
certificates embedded in Appendices A--C. No new Lean formalization seal is
claimed. Private independent action randomization is the only randomization
used. Prescribed and deviating strategies are evaluated in the actual game
with zero live and Never rewards, and the uniform target is fixed before
accuracy is chosen.

## 1. Raw family and conclusion

There are four players0,1,2,3, independent private randomization, one live
state, permanent absorption by every nonempty quitter coalition, and zero
live and Never rewards. Write actual absorbing rewards as r=1+Z. For a real
parameter delta put

```
A(delta) = [ 0       1       -6       -1/100 ]
           [ 1       0       -3/2     -2/5   ]
           [-delta  -3/5      0        1     ]
           [-7/100  -1/25     1        0     ],

J(delta) = [ 0       1/1000   2        9/1000]
           [ 1/10    0       13/10     3/10  ]
           [ delta/2 9/20     0        1/100 ]
           [ 1/200   1/1000   1/10     0     ].
```

Own singleton rewards Z_i({i}) are zero. For i distinct from j let
Z_i({j})=(A+J)_ij and Z_i({i,j})=J_ij. For opponent pairs
B=01,02,03,12,13,23 assign signs +1,-1,+1,+1,-1,-1. The smaller of the
two owners outside B receives this sign as Delta_i(B), and the larger
receives its negative. Set

```
Z_i(B)=max(0,-Delta_i(B)),
Z_i(B union{i})=max(0,Delta_i(B)).
```

For the opponent triple set the passive reward to1 and the grand-coalition
reward to0. These rules specify all sixty coordinates. The reference table has delta=1/1000. Only two native entries vary along this family:
Z_2({0})=-delta/2 and Z_2({0,2})=delta/2.

**Theorem.** There exists delta*>0 such that every0<delta<delta* has an
exact proper periodic terminal Nash profile against all behavioral deviations,
with physical support word

```
123 repeated n(delta) times, then023,023,012.
```

The same profile witnesses a uniform-equilibrium payoff at its fixed terminal
target. One can choose

```
n(delta) = log(1/delta)/(-log lambda) + O(1),
```

where lambda is the unique root in(83/100,84/100) of

```
300000 lambda^3 - 388900 lambda^2 + 99765 lambda + 13513 = 0.
```

Thus the producer uses unbounded periods as delta tends to zero. This is not
a lower bound on the periods of all equilibria of these games. For every
sufficiently small fixed positive delta, a full sixty-dimensional open
neighborhood of its raw table also has an exact proper periodic terminal
Nash profile with the selected finite support word and a uniform payoff.

For small positive delta, A and Gamma=A+J have strictly positive inverses,
strict favorite-matching signs with favorites01,23, and strictly positive
off-diagonal J. At delta=0 their inverses are still strictly positive:

```
min(A(0)^-1)=40/773,
min(Gamma(0)^-1)=327470/51639171.
```

Continuity gives the asserted positive-parameter regime. This statement
does not assert delta*>=1/1000. No finite-cycle calibration is required
for the all-small-parameter conclusion.

## 2. Root maps in odds and the boundary reset

For a support S, q_i=x_i/(1+x_i) for i in S and q_i=0 otherwise. A cap root
at native continuation b satisfies Q_i=P_i+H_i b_i for active owners and
Q_i<=P_i+H_i b_i for inactive owners. Its output is C=P+Hb. For a triple
with active opponents u,v, own singleton zero, division by the positive
opponent Continue mass gives the particularly useful active equation

```
b_i = -A_iu x_u - A_iv x_v + Delta_i({u,v}) x_u x_v.       (1)
```

Let T denote the support123 branch below, and let R_delta be the three-root
prefix reset012,023,023. Thus the prefix return is

```
F_n,delta = T^n composed with R_delta.                    (2)
```

A fixed point of(2) gives the reversed physical word in the theorem.

At delta=0 and b=(s,0,0,0), put t=s/6 and h=3t/[2(1+t)]. The first012
root has odds(x0,x1,x2)=(h,0,t), with output

```
b0=2t/(1+t),
b1=(h/10+13t/10)/[(1+h)(1+t)],
b2=0,
b3=(-13h/200+11t/10)/[(1+h)(1+t)].                       (3)
```

Each subsequent023 root, at a vector b with b2=0, has

```
a=b0/6, k=(b3+a)/(7/100+a),
(x0,x2,x3)=(k,a,0),
```

and output

```
b0'=2a/(1+a),
b1'=(b1+11k/10-a/5+ka)/[(1+k)(1+a)],
b2'=0,
b3'=(k/200+a/10+ka)/[(1+k)(1+a)].                        (4)
```

Equations(3)--(4) are rational functions of s and define R_0(s e0).
At this boundary some scheduled hazards vanish; this boundary word is not
the asserted proper equilibrium.

The reset root branches remain smooth in all cap coordinates and delta near
these boundary points. Indeed, for012 the equations are

```
b0=-x1+6x2+x1x2,
b1=-x0+(3/2)x2-x0x2,
b2=delta x0+(3/5)x1+x0x1.
```

At(h,0,t), the active Jacobian determinant is
-6(1+t)(3/5+h), which is nonzero. For023 the equations are

```
b0=6x2+x3/100-x2x3,
b2=delta x0-x3-x0x3,
b3=(7/100)x0-x2+x0x2.
```

At(k,a,0), the determinant is -6(1+k)(7/100+a), again nonzero.
The implicit function theorem therefore supplies the actual root maps
without a division by a small scheduled hazard. On the compact interval of
s used below, finitely many such charts give one consistent local branch.

## 3. The repeated triple is independent of delta

The map T uses support123, so prescribed player0 never quits in that phase.
Neither changed reward entry is queried in the prescribed recursion or in
any root comparison. Thus T is exactly independent of delta, including its
inactive owner0 comparison.

Write z=(b1,b2,b3). The support123 odds(x,y,w) for owners1,2,3 solve

```
b1=(3/2)y+(2/5)w+yw,
b2=(3/5)x-w+xw,
b3=x/25-y-xy.
```

Set

```
a=51/250+b1,
d=3/10-(11/25)b2+(9/10)b3,
c=b1+(2/5)b2+(3/2)b3-b2b3.
```

The small root is given by

```
x = 2c/[d+sqrt(d^2+4ac)],
y = (x/25-b3)/(1+x),
w = ((3/5)x-b2)/(1-x).                                (5)
```

This expression is smooth near z=0, including signed z. Its denominator is
positive at zero, so no differentiability assertion depends on positive
hazards at the limit. Define T(b0,z)=(h0(z)b0+p0(z),G(z)), where

```
h0(z)=1/[(1+x)(1+y)(1+w)],
p0(z)=[(1001/1000)x-4y-w/1000+xw+yw+xyw]
       /[(1+x)(1+y)(1+w)],

G1=(13y/10+3w/10+yw)/[(1+y)(1+w)],
G2=(9x/20+w/100+xw)/[(1+x)(1+w)],
G3=(x/1000+y/10)/[(1+x)(1+y)].                         (6)
```

The inactive owner0 gap has numerator

```
-x+6y+w/100+xy-xw-yw-xyw-b0,                          (7)
```

with the same positive denominator as h0.

The transverse derivative at zero is

```
M=DG(0)=-J_123 A_123^-1
 = [58/75  7/750  -7/50]
   [38/25 299/500 57/25]
   [ 1/60  1/150  -3/40].                            (8)
```

Its characteristic polynomial is the one in Section1, divided by300000.
Sign changes on the three disjoint intervals

```
(-1/10,-9/100), (56/100,57/100), (83/100,84/100)
```

account for all three roots. They are distinct; lambda is positive and
strictly dominant in modulus. In particular(9/10)^2<lambda.

## 4. Uniform exact entry, invariant cone, and contraction bounds

All finite claims in this section are reproduced by the complete standalone
checker in AppendixA.
It uses exact outward integer intervals at scale2^512 and no external data.
It supplies no numerical finite-cycle center. The domains, formulas,
cone and all interval-enclosure rules used in the proof are included.

Let

```
I=[1493/2000,1497/2000]=[.7465,.7485],
v_weight=(7/50,1,11/1000),
||z||_w=max(|z1|/(7/50),|z2|,|z3|/(11/1000)).
```

The exact checks establish the following facts.

1. For every s in I, the three boundary reset roots(3)--(4) have positive
   odds for owners0,2 and inactive gap less than -1/20. The remaining
   scheduled hazards are identically zero and satisfy active equality.
2. The next sixty T steps have all three hazards in(0,1) and inactive
   owner0 gap less than -1/4. Write their final value as
   B(s)=T^60 R_0(s e0). Then

   ```
   .7476 < B0(s) < .7477,
   ||B_123(s)||_w < 6/10^6,
   |B0'(s)| < 1/125,
   ||B_123'(s)||_w < 1/10^6.                          (9)
   ```

3. The cone

   ```
   K={z=(rt,t,ut): 0<t<=1/10000,
       13/100<=r<=3/20, 9/1000<=u<=11/1000}
   ```

   is mapped into itself by G. More precisely, the output ratios are
   strictly inside these ratio bounds and
   (4/5)t<G2(z)<(87/100)t. All three odds in(5) are positive on K.
   Every B_123(s) lies in the strict interior of K.
4. On the entire signed ball ||z||_w<=1/10000, formula(5) is smooth and

   ```
   ||DG(z)||_w < 9/10.                               (10)
   ```

   For b0 in[.74,.76], the weighted norm of the z-derivative of the first
   coordinate of T is less than1/2, and the inactive gap(7) is less than
   -7/10. The matrix norm in(10) is the induced weighted maximum norm.

For transparency, the cone check cancels the common scale t before interval
evaluation. With z=(rt,t,ut), set x=tY, y=tV, w=tW. Equation(5) becomes

```
Y=2[r+2/5+(3/2)u-ut]
  /[d+sqrt(d^2+4(51/250+rt)t(r+2/5+(3/2)u-ut))],
d=3/10-(11/25)t+(9/10)ut,
V=(Y/25-u)/(1+Yt), W=((3/5)Y-1)/(1-Yt).
```

The three quantities G_i/t are then rational expressions in Y,V,W,t.
Dividing their first and third entries by the second gives the new ratios.
The checker partitions only the two ratio intervals into16 equal pieces
each, keeps the full closed t-interval[0,1/10000], and certifies every box.
No box is accepted because it is small. The displayed output bounds are
approximately(.131406,.147205),(.0097255,.0100626),(.815858,.851232).

For the sixty-step entry calculation, values are enclosed together with
their derivatives with respect to s. At each step a local four-by-four
Jacobian is enclosed first, multiplied by the previous derivative enclosure,
and then the value enclosure is tightened by the mean-value bound about the
exact central evaluation s=299/400. This tightening is justified inductively
on the same entire interval I; it is not a sampled derivative or an assumed
enclosure. All comparisons are integer comparisons. The signed-ball test
uses one interval box and gives maximum weighted row bounds below.895.

## 5. The boundary return has a strict scalar fixed point

For z in the signed ball, (10) and G(0)=0 give
||G^k(z)||_w <=(9/10)^k||z||_w. Since h0(0)=1 and p0(0)=0,
the triangular recurrence(6) has a limit

```
T^k(b0,z) -> (Pi(b0,z),0).                            (11)
```

The convergence is uniform C1 on sufficiently small neighborhoods of the
entry points in(9). Here is a direct justification. The series of absolute
differences |h0(G^kz)-1| and |p0(G^kz)| converge uniformly. Hence the product
of h0 factors and the affine sum of p0 terms converge uniformly. Their
derivatives also converge uniformly: the chain derivative of G^k is bounded
by(9/10)^k, and the derivatives of h0,p0 are bounded on the ball. The products
of h0 factors remain uniformly bounded. Differentiating the finite affine
recursions and summing these geometric bounds proves the C1 assertion.
This argument permits signed nearby coordinates; it does not assume they
are legal roots.

On the positive cone, all odds are positive, so0<h0<=1. Starting at B(s),
the total outside-coordinate displacement is at most

```
(1/2)/(1-9/10) * ||B_123(s)||_w < 3/10^5.             (12)
```

This bound keeps b0 in[.74,.76], so its use of the derivative bound is
self-consistent, for instance by induction on finite prefixes. The same
calculation for the s-derivative gives

```
|d/ds Pi(B(s))| < 1/125+5/10^6 = .008005.             (13)
```

The scalar return H(s)=Pi(R_0(s e0)) equals Pi(B(s)). By(9) and(12) it
maps I into(.74757,.74773), strictly inside I; by(13) it is a contraction.
It has a unique fixed point s0 in I.

## 6. Uniform leading scale for the repeated triple

There is a positive eigenvector v of M for lambda, normalized by v2=1,
inside the cone ratios of Section4. One way to see this without a numerical
eigenvector is to take the linear limit of the strict cone invariance and
then use the simple dominant eigenvalue of(8). A left eigenvector ell can
be chosen strictly positive on the whole cone, despite one negative
coordinate. The checker verifies this last statement directly by taking
ell1=1, solving the first two left-eigenvector equations, and bounding
ell.(r,1,u)>0 over the full cone and lambda interval(83/100,84/100).
Normalize ell further so ell.v=1.

For every initial point z whose orbit enters the strict cone, sufficiently
near the compact entry set in(9), there exists a continuous positive
amplitude C(z) with

```
lambda^(-n) G^n(z) -> C(z)v,                          (14)
```

uniformly on a neighborhood of that compact set and its fixed finite
preimages used here. A short proof supplies the required uniformity.
Write G(z)=Mz+E(z), with ||E(z)||=O(||z||^2). After entry into the ball,
||z_n||=O(mu^n), mu=9/10. Therefore

```
lambda^(-n-1)ell.z_(n+1)-lambda^(-n)ell.z_n
      = lambda^(-n-1)ell.E(z_n)
```

has a uniformly summable bound because mu^2<lambda. It follows that the
left-hand normalized coordinate converges uniformly to a continuous C.
On the cone ell.z is bounded below by a positive constant times ||z||.
Hence

```
(ell.z_(n+1))/(lambda ell.z_n)=1+O(||z_n||).
```

The factors are positive and their deviations from1 are summable, so their
infinite product is strictly positive. This proves C>0, not merely C>=0.

On the complementary invariant subspace, the eigenvalues have modulus below
.57. Choose an operator bound C0(.6)^k for its kth linear iterate. The
variation-of-constants formula bounds the normalized complementary
component by sums of (.6/lambda)^(n-1-k)(mu^2/lambda)^k, which tend uniformly
to zero. This proves(14). A fixed finite number of pre-entry iterates merely
changes the amplitude by a positive power of lambda. No derivative
asymptotic for C is needed below.

## 7. Fixed points for all large n and small delta

The reset branches are smooth near the compact axis interval by Section2.
By the strict finite entry conditions in Section4, there are a neighborhood
U of s0 e0 and delta0>0 on which R_delta and the next sixty T steps are
defined smoothly; their transverse output lies inside the invariant cone
and the local contraction ball. This is a neighborhood of the cap vector,
not a requirement that every reset root there have positive hazards.

Equations(11)--(13) imply, uniformly C1 on a smaller neighborhood,

```
F_n,delta(b) -> F_infinity,delta(b)
             := e0 Pi(R_delta(b))                   (15)
```

as n tends to infinity, uniformly for small delta. At(delta,b)=(0,s0e0),
the derivative of F_infinity has only its first row nonzero. Its sole
possibly nonzero eigenvalue is H'(s0), whose absolute value is below.01.
Choose a weighted maximum norm making that row's contribution from the
other three coordinates small. By continuity, in a fixed small cap ball and
for small delta the limiting map has derivative norm below1/4. By(15),
all sufficiently large finite-n maps have derivative norm below1/2 there.
Their center errors tend uniformly to zero as delta tends to zero and n
tends to infinity. Shrinking delta0 and increasing N therefore makes each
F_n,delta a strict self-map and contraction of that fixed ball.

Consequently, for every n>=N and every sufficiently small |delta| there is
a unique fixed point b_n,delta in the ball. Moreover

```
b_n,delta -> s0e0  whenever n->infinity and delta->0.  (16)
```

This is an unscaled local fixed-point argument. It requires no uniform
division by delta and no C1 asymptotic for the leading amplitude.

Let

```
C*=C((R_0(s0e0))_123)>0.
```

Uniform(14), continuity of R_delta and C, and(16) give

```
(b_n,delta)_123 = C* lambda^n (v+o(1))                (17)
```

uniformly along n->infinity,delta->0. The fixed-point equation is essential
here: its left side is precisely the transverse coordinate after n T
steps from R_delta(b_n,delta). All these reset outputs lie in the common
basin neighborhood used in(14).

## 8. A strict reset window and selection of n

The remaining issue is positivity of the three reset hazards which vanished
on the axis. Write b=(s,delta z1,delta z2,delta z3), with s near s0 and
the z coordinates bounded. Let t=s/6 and h=3t/[2(1+t)] as before. For the
first012 reset, equation(1) gives exactly

```
b2=delta x0+(3/5)x1+x0x1.
```

Thus

```
x1 = delta A + O(delta^2),
A=(z2-h)/(3/5+h).                                   (18)
```

After this root, its output coordinate2 is delta V+O(delta^2), where

```
V=[h/2+(9/20+h)A]/(1+h).                             (19)
```

For the first023 reset let a=t/[3(1+t)],

```
k = t(2320t+1603)/[2(5t+2)(121t+21)].
```

Then its owner3 odds have expansion

```
x3 = delta B + O(delta^2), B=(k-V)/(1+k).             (20)
```

Together(18)--(20) require precisely the leading strict window

```
h < z2 < U(t),
U(t)=t(18418t^2+16602t+3269)
     /[2(t+1)(13t+3)(121t+21)].                      (21)
```

The checker proves h<.17 and U(t)>1.8 for every s in I. The third reset
also has positive owner3 odds. Indeed, let

```
a2=a/[3(1+a)],
k2=[(k/200+a/10+ka)/((1+k)(1+a))+a2]/(7/100+a2).
```

Its first-order coefficient is

```
[k2-(k/2+B/100)/(1+k)]/(1+k2).                       (22)
```

When(21) holds, V>0 and0<B<k/(1+k). The numerator of(22) is therefore
at least

```
k2-k/[2(1+k)]-k/[100(1+k)^2] > 3/20,                 (23)
```

again an exact bound uniform for s in I. These expansions follow from the
smooth root branches in Section2 and are uniform for bounded z and s in a
neighborhood of s0. In particular there is no assertion of a uniform
positive lower bound on these hazards as delta tends to zero.

For sufficiently small positive delta choose n to be the least integer at
least N for which C*lambda^n<=delta. Then n tends to infinity and

```
lambda < C*lambda^n/delta <= 1.
```

Equation(17) and v2=1 imply, for all sufficiently small delta,

```
.8 < (b_n,delta)_2/delta < 1.1.                     (24)
```

This lies a fixed positive distance inside(21). The other two normalized
transverse coordinates remain bounded by(17). Equations(18)--(23) now make
all three formerly zero reset hazards strictly positive. Every other reset
hazard remains proper by continuity, and the three inactive comparisons
remain strict. All of the first sixty repeated-triple phases remain proper
by the strict entry certificate; every later one remains proper by cone
invariance and(7). This proves that the fixed point is an actual root Nash
cycle, not merely a smooth algebraic cycle outside the hazard cube.

Taking logarithms in the defining inequality for n gives the period estimate
in Section1. The bounded window of feasible repeat counts at the literal
delta=1/1000 is explained by the same two competing inequalities: increasing
n lowers the incoming coordinate2. Too few repetitions violate the first023
owner3 test; too many violate the initial012 owner1 test. The asymptotic
window at s approximately.7476 is approximately(.1662,1.8692) for b2/delta.
That observation is explanatory; the proof uses the exact margins in(21)
and(24), not a numerical census of finite-n solutions.

## 9. Actual equilibrium, openness, and scope

At every selected fixed point, reverse the prefix root list. Its cyclic
native values satisfy exact prescribed Bellman equality and both-action
root optimality at every phase. All four players have positive hazards
somewhere in the finite cycle. After deleting any player, opponents still
have a positive absorption chance per period. Hence the prescribed survival
and every opponent-deleted survival tend to zero geometrically.

Iterating the Bellman inequalities against any complete behavioral replacement
leaves a bounded remainder times opponent-deleted survival. It tends to zero
uniformly over the replacement. Prescribed play attains the cyclic value,
so this is exact terminal Nash against all behavioral deviations, including
Never and arbitrary deadline laws. Every such replacement absorbs almost
surely, which makes the shift r=1+Z legitimate without shifting the zero
Never payoff.

The geometric opponent tail supplies a finite expected absorption-time bound
uniform over deviations for this selected finite cycle. Terminal payoff and
T-stage average payoff differ by at most a constant times that bound divided
by T. Thus the same profile is epsilon Nash for every sufficiently large
horizon, at the single fixed initial target1+b_n,delta. The target does not
vary with epsilon. Constants may depend on delta, which is permitted.

For each fixed small delta, the construction has proper hazards, strict
inactive inequalities, and a return-map derivative with norm below1/2.
The active root branches are regular at every phase. This follows at the
three reset phases from the nonzero boundary Jacobians and continuity; at
the repeated phases from the smooth explicit small-root formula and its
nonzero active Jacobian in the basin. The latter also follows directly by
eliminating y,w in(5): d+2ax=sqrt(d^2+4ac)>0 and1+x,1-x are nonzero.

Therefore independent perturbations of all sixty raw entries preserve the
finite smooth return map, its strict self-map and contraction, its proper
hazards, and its inactive inequalities on a sufficiently small neighborhood.
Perturbed own singleton entries are allowed: the general contact-corner
root equations, rather than the specialized zero-own formula(1), give this
continuation. The same absorbing consumer applies. No uniform reward radius
as delta tends to zero is asserted.

The producer gives a parameter interval accumulating at a boundary table and
chooses the number of phases from the parameter. It neither establishes a
minimal period nor excludes other equilibrium constructions for this family.
The precise complete earlier-condition comparisons are Sections10--13.
No separation from unspecified maximal neighborhoods of an earlier local
theorem is claimed. The mathematical increment is the analytic scale-selection argument, with one
uniform basin and no supplied finite-cycle center for any small delta.

The relevant semantic contracts were inspected in `IsεQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`),
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`). They agree with
the ordinary consumer above; no instance of those declarations is claimed
formalized here.

### 9.1. The boundary table also has a fixed uniform payoff

The table at delta=0 has the uniform-equilibrium target

    v0=(1+s0,1,1,1),

where s0 is the unique scalar boundary fixed point from Section5. Indeed,
Section7 gives b_n,delta->s0 e0 along the selected cycles. Thus their actual
uniform targets v_delta=1+b_n,delta tend to v0. The largest change in any
raw reward between the delta and zero tables is delta/2. For any fixed
prescribed profile, any unilateral behavioral replacement and any finite
horizon, this changes expected average payoff by at most delta/2: the
transition law is the same, only the absorbing reward changes.

Given epsilon>0, choose a sufficiently small positive delta so that
delta<epsilon/4 and ||v_delta-v0||_infinity<epsilon/4. Use the selected
delta-cycle and a horizon beyond its uniform epsilon/4 threshold from
Section9. In the zero table, its prescribed payoffs are within
epsilon/4+delta/2+epsilon/4<epsilon of v0. Every deviating payoff is at
most v_delta,i+epsilon/2+delta/2<v0,i+epsilon; its gain over prescribed
play is at most epsilon/4+delta<epsilon if the threshold is also chosen
for the epsilon/4 Nash comparison. The same profile and threshold work at
every larger horizon. This proves the fixed-target contract at delta=0.

The selected profile may depend on epsilon, which is permitted. This
corollary asserts neither an exact finite-period terminal Nash profile nor
a full raw neighborhood at the boundary table.

## 10. Uniform stationary and response-quotient comparison

This section uses d for the same raw parameter delta as Section1 and covers
the entire closed interval0<=d<=1/1000, independently of the existential
producer threshold. Every participant native reward is nonnegative. Both
Gamma and A have positive determinants and strictly positive inverses on this
whole interval: only their (2,0) entry varies, so their determinants and every
adjugate entry are affine in d; AppendixB checks positivity at both endpoints.
In particular det Gamma(0)=51639171/50000000. No principal-block
nonsingularity is assumed at d=0.

### 10.1. Exact stationary field and terminal meaning

For a stationary hazard vector q in [0,1]^4, put

    H_i=PRODUCT_(j!=i)(1-q_j),
    P_i=E Z_i(B), Q_i=E Z_i(B union{i}),
    F_i=(1-H_i)Q_i-P_i,

where B is the opponents' independent quitter coalition and Z_i(empty)=0
only in the passive expectation. Each F_i is independent of q_i, affine in
d, and has degree at most two in every hazard coordinate. Its constant term
is zero and its linear part is -Gamma q.

The zero-discount field computed from the actual rewards 1+Z is exactly the
same F: the passive expectation gains 1-H_i and the Quit expectation gains
one, which cancel. A recipient scaling multiplies its F row by the same
positive factor; an added constant to all absorbing rewards of one recipient
does not change that row.

For q nonzero the stationary law absorbs surely. Let
D=1-PRODUCT_i(1-q_i)>0 and V_i be its native terminal payoff. Direct algebra
gives

    V_i=[q_i Q_i+(1-q_i)P_i]/D,
    Q_i-V_i=(1-q_i)F_i/D,
    P_i+H_i V_i-V_i=-q_i F_i/D.                    (1)

The two expressions are gains from immediate Quit and from one-date Continue
followed by the prescribed stationary profile. Their actual gains coincide
with these native differences because absorption remains almost sure.
Consequently exact stationary terminal Nash requires

    q_i F_i>=0 and (1-q_i)F_i<=0, for every i.      (2)

We prove that the only solution of (2) is q=0, uniformly over d. At q=0 the
actual payoff is zero and immediate Quit gives one, so this remaining point
is not a terminal Nash profile either.

### 10.2. Uniform analytic origin exclusion

Put h=1/256. Suppose 0<||q||_infinity<=h and (2) holds. Every positive
hazard is strictly below one, so its owner must have F_i=0. Let S be the
positive support.

For singleton support {a}, choose an inactive owner i with Gamma_ia<0 at
both parameter endpoints. Such an owner exists for each a; in particular
use owner 3 when a=0, avoiding the vanishing entry Gamma_20. The exact
one-opponent formula is

    F_i=q_a[J_ia q_a-Gamma_ia]>0,

contradicting its inactive condition in (2).

For pair support {i,j}, choose i<j. All six corresponding entries Gamma_ij
are independent of d. For a crossing pair Gamma_ij<0; for a favorite pair
Gamma_ij>J_ij>0. The same one-opponent formula gives respectively F_i>0
or F_i<0 because q_j<1, contradicting the active equality.

For triple support choose its unique owner i whose favorite is absent.
Write the other two active owners as j,k, b_j=-Gamma_ij, b_k=-Gamma_ik,
and p=Z_i({j,k}). Here b_j,b_k are nonnegative, b_j+b_k is positive,
and p is nonnegative. Participant nonnegativity gives Q_i>=0, hence

    F_i>=-P_i
       =q_j q_k[b_j/q_k+b_k/q_j-(b_j+b_k+p)]
       >=q_j q_k[(b_j+b_k)/h-(b_j+b_k+p)]>0.       (3)

The strict final inequality follows from these complete four cases:

| S | i | b_j+b_k | p |
| --- | --- | --- | --- |
| 012 | 2 | 3/20+d/2 | 0 |
| 013 | 3 | 13/125 | 1 |
| 023 | 0 | 4001/1000 | 1 |
| 123 | 1 | 3/10 | 0 |

For full support write F=-Gamma q+R. The coefficients of R have total
degree at least two. Their absolute row sums are bounded uniformly by

    K=1913/50.

Indeed each coefficient is affine in d, and its absolute value is convex,
so the maximum of their sums occurs at a parameter endpoint. Likewise

    ||Gamma(d)^-1||_infinity<=L=59425126500/10327361611.

Every inverse entry is positive, so each row sum is an affine numerator
divided by a positive affine determinant. Such a quotient is monotone or
constant; its maximum on the interval is an endpoint value. The checker
computes both endpoints exactly. All four equations F_i=0 now imply

    ||q||_infinity<=LK||q||_infinity^2,
    LKh=1136802669945/1321902286208<1,

a contradiction. This covers every support in the entire origin box,
including d=0 where the principal block Gamma_{02,02} is singular.

### 10.3. Complete parameter-uniform Bernstein certificate

AppendixB is a complete standalone checker.
It reconstructs the literal table and all eight endpoint fields F_i at d=0
and d=1/1000. It first asserts degree at most two in every hazard coordinate
and degree at most one in the parameter. It converts the fields to tensor
Bernstein coefficients of degree (2,2,2,2), with one positive common integer
denominator.

Every intermediate-parameter coefficient is the corresponding convex blend
of its two endpoint coefficients. Therefore a sign witness using ALL
coefficients at BOTH endpoints proves the sign uniformly in d on that box.
The recursion subdivides only the four hazard coordinates. A degree-two
slice (a0,a1,a2) splits at its midpoint into the integer numerator arrays

    left =(4a0,2(a0+a1),a0+2a1+a2),
    right=(a0+2a1+a2,2(a1+a2),4a2),

at four times the parent's positive denominator. Both children are closed
and both are retained. A box is closed only if it lies in the analytically
handled origin cube, or some row i has all endpoint coefficients strictly
negative and lower q_i>0, or all endpoint coefficients strictly positive and
upper q_i<1. These tests contradict (2) on the entire closed box. They retain
all zero/sure faces, partial supports, and shared subdivision boundaries.

The deterministic exact run terminates with 175585 nodes, 87793 leaves,
maximum depth 62, and exactly one origin leaf. The identity
175585=2*87793-1 is checked. Any unresolved box at the finite budget raises
an exception. All proof arithmetic is rational or Python integer-object
arithmetic, without solver tolerance, sampled acceptance, or external data.
The reproducible recursion itself supplies every strict leaf witness; no
large retained leaf file is needed. This proves (2) has no nonzero solution
throughout the closed parameter interval.

### 10.4. One positive stationary exploitability gap for the whole interval

Let E(d,q) be the largest terminal gain available to any player through an
arbitrary behavioral replacement, when the prescribed law is stationary q.
Then

    inf_{0<=d<=1/1000, q in [0,1]^4} E(d,q)>0.      (4)

For q nonzero, the maximum of the nonnegative parts of the eight gains in
(1) is continuous in (d,q), bounded above by E, and strictly positive by
Section10.3. It has a positive minimum on compact subsets away from q=0.
At q=0, E>=1. It remains to rule out sequences d_n->d*, q_n->0 with
E(d_n,q_n)->0. Put t_n=SUM_i q_ni and pass to a normalized limit
q_n/t_n->w in the unit simplex. The prescribed actual payoff tends to
1+Gamma(d*)w, whereas immediate Quit tends to one. Thus

    y=Gamma(d*)w>=0.

Write B=Gamma(d*)^-1>0. Since w is nonzero, y is nonzero. The identity
w=By then forces every w_i strictly positive. In particular 0<w_i<1 for
each i. Against these opponents, literal Never absorbs almost surely and
its actual payoff tends to 1+y_i/(1-w_i). Its limiting gain is
w_i y_i/(1-w_i), which vanishing exploitability forces to zero. Thus y=0,
contradicting w=By with SUM_i w_i=1. This proves (4).

This compactification uses only the full positive inverse, not nonsingularity
of every principal block. Immediate Quit, one-date Continue followed by prescribed play, and literal
Never are legal full behavioral deviations. The conclusion still restricts
the prescribed profiles to stationary ones; it cannot establish a Fin4
counterexample.

### 10.5. All response partitions and recipient scalings

For a set partition restrict F to block-constant hazard vectors. Two owners
merged into one block could have identical response rows after constant
positive recipient scaling only if their coefficient vectors were
proportional. A nonzero two-by-two coefficient minor excludes this. The
following table covers all fourteen nondiscrete partitions. The displayed
block order determines the monomial exponent order; entries are the exact
minor at d=0.

| Partition | Rows | Monomials | Minor at zero |
| --- | --- | --- | --- |
| 01\|2\|3 | 0,1 | 001,010 | -1999/5000 |
| 1\|02\|3 | 0,2 | 001,010 | 101/25 |
| 1\|2\|03 | 0,3 | 001,010 | -2611/10000 |
| 0\|12\|3 | 1,2 | 001,010 | 217/1000 |
| 012\|3 | 0,1 | 01,10 | -188/625 |
| 12\|03 | 1,2 | 01,10 | 13/250 |
| 0\|2\|13 | 1,3 | 001,010 | -589/5000 |
| 02\|13 | 0,2 | 01,10 | 86/25 |
| 2\|013 | 0,1 | 01,10 | 19/5 |
| 0\|1\|23 | 2,3 | 001,010 | 12561/100000 |
| 01\|23 | 0,1 | 01,10 | -2563/625 |
| 1\|023 | 0,2 | 01,10 | -20543/50000 |
| 0\|123 | 1,2 | 01,10 | -473/500 |
| 0123 | 0,1 | 1,2 | 3881/250 |

Each minor m(d) has degree at most two. The checker derives the full
polynomial and verifies

    SUM_{k>=1} |[d^k]m| (1/1000)^k < |m(0)|.

Every minor therefore stays nonzero on the entire closed parameter interval.
This excludes every nondiscrete response-invariant quotient under every
positive recipient scaling, including parameter-dependent choices of those
scales. Recipient constant absorbing offsets cancel from F as explained in
Section10.1.

The only remaining partition is discrete. Its singleton matrix is Gamma,
which has R0 degree +1. Here is a direct justification not relying on
principal minors. If x>=0, y=Gamma x>=0, and x_i y_i=0 for all i, then
x=By with B>0. A nonzero y would force x strictly positive, hence y=0;
if y=0, invertibility forces x=0. Thus the homogeneous complementarity
problem has only its origin root: Gamma is R0.

For a sufficiently small positive t perturb to
y=Gamma x-t1>=0, x>=0, and x_i y_i=0. The identity
x=B(t1+y)>0 forces y=0, so its unique root is x=tB1. Near that root the
minimum-map equation min(x,Gamma x-t1)=0 is the linear second branch, with
Jacobian Gamma and positive determinant. R0 isolation allows this small
perturbation without a boundary zero, proving degree +1. Positive row
scaling preserves positivity of the inverse and the determinant, so the
same argument holds after every compatible scaling. No partition supplies
the response-quotient degree hypothesis degree different from one.

## 11. Uniform punishment and all sure-first faces

Every actual participant reward is at least1 throughout the closed parameter
interval. Immediate Quit therefore guarantees1 against every opponent law.
Opponents choosing Never hold the complete response cap to exactly1. Thus
all true actual punishment values equal1, and every arbitrary off-path
continuation has full cap at least1. Native punishment values are zero.

For current hazards q, let g_i(q) be native forced-Quit minus forced-Continue
payoff when all-Continue has value0. A root with a sure owner h requires

```
q_i>0 ⇒ g_i≥0,       q_i<1 ⇒ g_i≤0.                 (1)
```

For i≠h, a sure opponent makes the continuation irrelevant. For h, an
arbitrary actual continuation cap b_h≥1 makes its exact Quit-minus-Continue
cap comparison g_h−H_h(b_h−1)≤g_h. Consequently (1) is necessary even
for arbitrary behavioral tails. The following four analyses exhaust the
closed sure boundary.

### 11.1. Sure owner0

Write x=q1,y=q2,z=q3 and a=δ+(1−δ)x. The opponent gaps are

```
g1=−1+2z(1−y),
g2=a−(1+a)z,
g3=[7−107x+93y(1−x)]/100.                           (2)
```

On the parameter interval0≤a≤1. If y>0, g2≥0 gives z≤a/(1+a)≤1/2.
Then g1<0 forces x=0. Formula(2) makes g3>0, forcing z=1, a
contradiction. Hence y=0. The two remaining opponent gaps are 2z−1 and
(7−107x)/100. Their boundary signs force x,z to be proper, so
x=7/107,z=1/2. At this unique opponent equilibrium,

```
g2=50(δ−1)/107<0,      g0=−13/214<0.
```

Thus the sure owner would withdraw.

### 11.2. Sure owner1

Write x=q0,y=q2,z=q3. None of the face's gaps depends on δ, because
owner1's sure action prevents the only two changed coalitions from occurring.
The relevant formulas are

```
g0=−1+2y(1−z),
g2=[−12xz+2x+2z+3]/5,
g3=[26(1−x)(1−y)−25]/25.                            (3)
```

If z>0, g3≥0 forces x,y≤1/26. Then g0<0 gives x=0 and g2>0 gives
y=1, contradiction. Hence z=0. Now g2>0 gives y=1, and g0=1 gives
x=1. At this unique opponent equilibrium g1=−1<0.

### 11.3. Sure owner2

Write x=q0,y=q1,z=q3. All three opponent gaps are independent of δ:

```
g0=6−5y−7z+5yz,
g1=[3−5x−z+xz]/2,
g3=−1+2x(1−y).                                     (4)
```

If x=0, the signs force y=1,z=0, then g0=1 contradicts x=0. If x=1,
they force y=0,z=1, then g0=−1 contradicts x=1. Thus x is proper and
g0=0 yields z=(6−5y)/(7−5y)∈[1/2,6/7]. This makes z proper; g3=0
yields x=1/[2(1−y)] and y<1/2. The case y=0 would give x=1/2,z=6/7
and g1=1/28>0. Hence all three are proper. The remaining equation is
20y²−30y+1=0, with unique admissible root

```
x=(−5+√205)/18, y=(15−√205)/20, z=(22−√205)/9.
```

The sure owner's gap has derivative x(1−y)(1−z)≥0 with respect to δ.
Its maximum on the parameter interval is therefore its value at1/1000:

```
g2≤(170187−12919√205)/18000<0,
12919²·205−170187²=5251000036>0.
```

Thus this owner also withdraws, uniformly across the interval.

### 11.4. Sure owner3

Write x=q0,y=q1,z=q2. Again every face gap is independent of δ. The
opponent formulas are

```
g0=[101(1−y)(1−z)−100]/100,
g1=[−13xz+3x+3z+2]/5,
g2=−1+2y(1−x).                                     (5)
```

If x>0, g0≥0 gives y,z≤1/101. Then g2<0 forces z=0 and g1>0 forces
y=1, contradiction. Hence x=0; then g1>0 forces y=1 and g2=1 forces
z=1. At this unique opponent equilibrium g3=−1<0.

The four arguments cover every zero, proper and sure opponent pattern.
AppendixC verifies all δ-dependent identities and monotonicity;
(3)--(5) for the opponents are the unchanged literal polynomial expansions.
The compact parameter interval times the four closed sure faces has no point
satisfying(1). The continuous maximum one-date regret consequently has a
strictly positive minimum there. Every complete actual root with a behavioral
tail has at least this regret, since its relevant continuation cap is≥1.
Raw payoff perturbations preserve that strict exclusion by continuity and
the immediate-Quit cap bound1−η. This also excludes every singleton-base
certificate using true punishment, regardless of its free carrier.

## 12. Complete fixed-disjoint-pair comparison

### 12.1. Proper fixed-pair equations and the uniform exact cover

Fix a mate involution m, one of01|23,02|13,03|12. At each repeated phase
only one assigned pair can quit, using its fixed hazards q_i. Assume first
0<q_i<1 for all four owners. Set p_i=J_i,m and c_i=J_i,m−Γ_i,m=−A_i,m.
At its active phase, owner i's value is p_i q_m. At its opposite inactive
phase, active indifference and the passive reward at its own phase give

```
W_i=c_i q_m/(1−q_m).
```

For the opposite pair{j,k}, let D=(1−q_j)(1−q_k). Its prescribed Continue
and forced-Quit values at that opposite phase are

```
C_i=Γ_ij q_j(1−q_k)+Γ_ik q_k(1−q_j)
    +Z_i({j,k})q_jq_k+p_i q_m D,
Q_i=J_ij q_j(1−q_k)+J_ik q_k(1−q_j)+Z_i({i,j,k})q_jq_k.
```

Necessary equations and inactive inequalities are

```
E_i=(1−q_m)C_i−c_i q_m=0,
H_i=(1−q_m)Q_i−c_i q_m≤0.                           (6)
```

For favorite schedule01|23, c_i=−1. Then W_i<0 while forced Quit has
nonnegative native reward, immediately excluding that proper schedule.

For either crossing schedule, E=Γδ q+Rδ(q). The inverse has positive
entries throughout the whole parameter interval. Its determinant and
adjugate entries are affine in δ, with strictly positive endpoint values.
Each positive inverse row sum is a fractional linear function of δ, hence
its maximum is at an endpoint. This gives

```
||Γδ^-1||∞≤L=59425126500/10327361611.
```

Every coefficient of every E_i,H_i is affine in δ. The sums of absolute
nonlinear E coefficients are convex in δ, so endpoint bounds give

```
||Rδ(q)||∞≤K||q||∞²,
K=15 for02|13, K=121/10 for03|12,       L K/256<1.
```

Thus E=0 inside[0,1/256]^4 forces q=0, uniformly in δ.

Away from this origin box, tensor Bernstein subdivision gives a complete
closed-cube exclusion. Every E_i and H_i has coordinatewise degree at most2.
For each hazard box store its exact integer Bernstein arrays for BOTH
parameter endpoints0 and1/1000. Affine parameter dependence makes every
interior-parameter coefficient a convex combination of the corresponding
endpoint coefficients. Reject a box if one E row has the same strict sign
at all coefficients and both endpoints, or if one H row is strictly positive
at all coefficients and both endpoints. Retain both closed children of every
midpoint split; exact de Casteljau subdivision multiplies the common positive
denominator by4. No floating-point or stopping-budget acceptance is used.

The uniform deterministic certificate finishes as follows:

| Schedule | Nodes | Leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| 02|13 | 103 | 52 | 32 |
| 03|12 | 689 | 345 | 39 |

Therefore on the ENTIRE hazard cube, for every δ∈[0,1/1000],
E=0,H≤0 implies q=0. This is stronger than exclusion of proper roots.
AppendixC supplies the literal table, fields, affine-parameter
checks, inverse bounds, exact Bernstein conversion and complete subdivision.

### 12.2. Zero and sure hazards, including the endpoint exception

A positive-probability reached continuation of an exact Nash profile is exact
Nash: a profitable continuation replacement gives a profitable original
replacement scaled by the positive history probability. Therefore any sure
hazard in a repeated pair profile is excluded by Section11 at its first
reached occurrence. Assume all hazards are below1.

If both phases are nonempty and some assigned hazard is zero, at least one
phase is solo. Its sole proper mixing owner i quits alone at native reward0
and sees no current opponent hazard. Indifference forces its next-phase
value to be0. If any owner j at that opposite phase has J_ij>0, immediate
Quit there has strictly positive value: the event that exactly j quits has
positive probability and all other participant rewards are nonnegative.
This is a contradiction.

The only possible exception is δ=0,i=2, with the opposite active set
exactly{0}, since J_20 is the sole zero off-diagonal premium. But then owner0
is itself the sole mixer of that opposite phase, and its corresponding
next-phase immediate-Quit value is strictly positive by J_02=2. Applying the
same argument to owner0 gives the contradiction. Thus the vanishing premium
at the endpoint creates no omitted zero-rate case.

If one phase is empty, a proper two-owner active pair i,j must satisfy
J_ij q_j=Γ_ij for both owners. A favorite pair has Γ_ij=J_ij+1>J_ij,
so this is impossible. A crossing pair has at least one direction with
Γ_ij<0≤J_ij, including pair02 atδ=0 by choosing i=0,j=2, so it too is
impossible. A single active owner j eventually quits alone; some fixed
crossing observer i has Γ_ij<0 throughout the interval, while immediate
Quit guarantees1. The observer gains. AllNever pays0 and immediate Quit
pays1. These exhaust all remaining boundary patterns.

### 12.3. One uniform full-response gap across the parameter interval

Suppose parameters δ_n in the compact interval and fixed-pair profiles q_n
had full behavioral terminal exploitability tending to0. Pass to limits
δ_n→δ* and q_n→q*, fixing the finite schedule choice on a subsequence.

If q* has at least two positive coordinates, every opponent-deleted period
survival is below1. Both the prescribed payoff and full response cap vary
continuously with δ and q there. Indeed if H_i is opponent period survival,
N_i is literal Never value and L_i(t) is the deadline value at first-period
phase t, the corresponding deadline in period k has value

```
(1−H_i^k)N_i+H_i^k L_i(t).
```

Every behavioral stopping law is a mixture of deadlines and Never, so the
full cap is exactly max(N_i,L_i(0),L_i(1)). A zero limiting gap would give
an exact fixed-pair Nash atδ*, contrary to Sections12.1--12.2.

If q* has only one positive coordinate j, choose a negative crossing observer
whose Γ_ij is fixed across δ. Its prescribed value tends to1+Γ_ij<1,
while immediate Quit guarantees1. Again the gap cannot vanish.

Finally suppose q*=0. Put h_n=sum_i q_ni>0 and take w_n=q_n/h_n→w in
the unit simplex. Uniform bounded rewards and the fixed two-phase period give
singleton first-exit masses q_nj+O(h_n²), total collision mass O(h_n²), and
total absorption h_n+O(h_n²). Prescribed actual values therefore tend to
1+(Γδ* w)_i. Immediate Quit≥1 implies y=Γδ* w≥0. A singleton support
is excluded by the preceding fixed negative crossing. Thus every w_i<1.
For w_i>0 the actual Never response tends to
1+y_i/(1−w_i). Vanishing debt and y_i≥0 force y_i=0 on the positive support.
Hence w≥0,y≥0,w_i y_i=0.

This is impossible solely from Γδ*^-1>0. If y=0, invertibility gives w=0.
If y≠0, strict inverse positivity gives w=Γδ*^-1 y strictly positive in
EVERY coordinate, and complementarity then forces y=0. Both contradict
sum_i w_i=1. This argument deliberately avoids assuming the principal02
block is nonsingular atδ=0.

Every possible limiting case is excluded, proving one positive gap d over
the whole closed parameter interval and entire fixed-pair family. Changing
raw rewards by at mostη changes every prescribed and deviating terminal
payoff by at mostη, uniformly over every profile; the literal Never payoff
stays0. Thus exploitability changes by at most2η. A uniform raw tube of
radius below d/2 retains a positive fixed-pair gap. For each fixed strategy,
finite-horizon averages converge to terminal payoffs by bounded convergence,
so this gap also prevents arbitrary-accuracy uniform witnesses within the
fixed-pair architecture.

## 13. Complete earlier raw-condition comparisons

Every native normalization with zero own singleton rewards has the form
lambda_i Z_i, lambda_i>0, in recipient row i. Relabeling only permutes the
unique favorite matching and the finitely enumerated partitions. The
comparisons quantify over every choice of the parameters stated in each
criterion; they are not failed solver searches. The direct strict-sign
comparisons below apply to every0<delta<=1/1000. The architecture and
quotient comparisons include delta=0.

### 13.1. Stationary, sure-first, and fixed-pair outputs

Sections10--12 exclude every stationary output, every sure-first
punishment-tail output, and every fixed disjoint-pair two-phase output.
These conclusions apply to all existential choices inside any producer of
those profiles. In particular they cover stationary large-coalition reward
productions regardless of the chosen reward ratios, bounded remainders,
coalition sizes or unspecified sufficiently-large thresholds: the final
produced nonzero vector would satisfy the stationary complementarity already
excluded in Section10. They do not attempt to guess such thresholds from the
size of a few reward entries.

For two-phase inverse-cone, signed-column and bounded-inverse producers,
Section12 excludes the actual strategy output for all partitions, all proper
hazards and both phase orders, even when a sufficient raw bound happens to
be weak. Section11 covers the full induced sure-first game and the true
punishment continuation, so testing stationary repetition alone is not used
to dismiss a punishment-tail producer.

### 13.2. All positive odds and polynomial row weights

This comparison includes arbitrary positive constant or polynomial weights,
rather than one tested linear program. Choose any odds factors ρ_j>0 and
positive C¹ row factors m_i on the cube. Define

```
ψ_j(u)=ρ_j u_j/[1+(ρ_j−1)u_j],
D_j(u)=1+(ρ_j−1)u_j,
G_i(u)=m_i(u) ∏_{j≠i}D_j(u)² F_i(ψ(u)).
```

The usual positive multiaffine weights, with all sixteen vertex values
positive, are included. Choose either one favorite pair or both, orient each
chosen pair as preferred i and partner k, and let K be the cube with u_i≥u_k
for each oriented pair. The relevant wall guards imply

```
G_i(u)≥G_k(u) whenever u_i=u_k and u∈K.               (W)
```

No such choices exist for any table in the closed parameter interval. Here is a direct proof,
independent of any particular sufficient Bernstein representation of(W).
Suppose they existed. Put v_i=2 for preferred owners and v_j=1 otherwise.
For η>0, Brouwer gives a fixed point of the continuous map
u↦projection_K(u+G(u)+ηv). At a tied interior pair, (W) gives a strictly
positive difference between the preferred and partner displacement; an order
constraint cannot support the fixed-point normal in the opposite direction.
At a tied lower cube corner, the preferred displacement is nonpositive and
larger than the partner displacement, so both are nonpositive; at a tied
upper corner, the partner displacement is nonnegative and smaller than the
preferred displacement, so both are nonnegative. At an untied pair the order
constraint is inactive. These normal-cone facts show ordinary coordinate
cube complementarity for G+ηv at the fixed point. Equivalently they follow
by writing the normal of u_k−u_i≤0 as a nonnegative multiple of(−1,1),
plus the coordinate cube normals. The two chosen pairs are disjoint, so the
argument covers their intersection.

Let η tend to zero and take a convergent subsequence. If the limit is nonzero,
positive factors and ψ transfer complementarity to a nonzero q for F,
contrary to Section10. Suppose instead the fixed points u_η tend to zero.
At zero,

```
DG(0)=−M,       M=diag(m(0)) Γ diag(ρ).
```

Normalize by a_η=max(||u_η||∞,η), obtaining limits w=u_η/a_η and
τ=η/a_η, with w∈K, τ≥0 and max(||w||∞,τ)=1. For small η no upper
cube boundary is active. The coordinate complementarity and first-order
expansion consequently give

```
Mw≥τv,                  w_i[(Mw)_i−τv_i]=0.          (L)
```

If τ=0, put y=Mw>=0. Positive diagonal factors preserve strict inverse
positivity, so M^-1>0. If y is nonzero then w=M^-1 y is strictly positive
in every coordinate, and the complementarity in(L) forces y=0, a
contradiction. If y=0 then invertibility gives w=0, contradicting the
normalization. Thus τ cannot be zero. This covers the singular principal
02 block at delta=0 without any limiting principal-inverse estimate.

Choose any oriented pair i,k. Differentiating(W) at zero gives
(Mw')_i≤(Mw')_k for every ordered nonnegative w' tied on that pair.
For an arbitrary w∈K, decrease w_i to w_k to obtain such a w'. Restoring
w_i subtracts M_ki(w_i−w_k)≥0 from the row difference, since the diagonal
is zero and the favorite coefficient M_ki is positive. Therefore
(Mw)_i≤(Mw)_k throughout K. If w_k>0, also w_i>0 and(L) gives the
opposite strict difference τ(v_i−v_k)=τ>0. If w_k=0, row i has only
nonpositive crossing contributions, so (Mw)_i≤0<τv_i, again a contradiction.
The collapsing limit is impossible. This proves the claimed exclusion of
all odds, all positive row factors, all orientations and both selected-pair
counts. Additional positive recipient scalings are absorbed into m.

### 13.3. Direct finite sign, core, and cap obstructions

The following raw requirements also fail for every relabeling and admissible
positive row scale.

1. **Proper premium cores of size at most three.** A premium trap is a
   nonempty set S such that every i∈S has a coalition C⊆S containing i
   with r_i(C)>r_i({i}). Since every J_ij>0, the whole four-player set is
   already a trap, witnessed by any pair containing each owner. Its greatest
   premium core is therefore all four players. Any criterion requiring a
   greatest core of size two or three, including a joining-attractive or
   mixed-sign three-owner core, fails before its further sign tests.
2. **Negative-premium chamber or rotating-pair templates.** Every participant
   pair premium is strictly positive. The passive-triple chamber requires
   negative participant pair premiums, and the rotating-pair templates require
   a directed pair premium −b/2 with b>0. These strict contradictions hold
   under every labeling and persist under small raw perturbations. No
   neighborhood claim here relies on zero participant triple entries.
3. **Signed inverse-column inactive caps.** The inverse Γ⁻¹ is strictly
   positive, forcing all column signs to be positive. The required inactive
   joining caps have the form J_ij≤−B_i with B_i≥0 for a nonempty opposite
   pair. Each J_ij>0 contradicts them, for every schedule and free radius.
4. **Triple collision boxes.** Such a box requires
   c_ij=J_ij−Γ_ij>0 for all six directed pairs in a selected triple.
   Every triple contains a favorite pair and both favorite c entries are−1.
   Thus all four triple choices, all scale parameters, and all relabelings
   fail this necessary guard.
5. **Joint positive passive triples.** Their singleton guard requires two
   distinct recipients in one column to have positive Γ entries. Each column
   of the matching Γ has exactly one positive off-diagonal entry. This is
   impossible for every choice of three-owner block and outside owner.
6. **Finite-calendar participant caps.** Choose any two unmarked owners,
   any ordered partition of the remaining marked owners, and any positive
   marked weights. For a marked i and an unmarked j, the coalition{i,j}
   meets its first marked block only at i. The required weighted participant
   cap would read λ_i J_ij≤0, contrary to strict positivity. This covers
   every ordered partition, marking and positive weight selection before
   any calendar-polytope funding inequality is considered.
7. **Bounded inverse-corner joining caps.** Write B=Γ⁻¹. These bounds require
   inactive pair premiums≤ell_i, where
   ell_i=c_i κ r_min/2, κ≤1/4,
   r_min≤1/(32 U Q), Q≥3c_i, and U bounds every inverse entry above.
   Therefore ell_i≤1/(768 U). Under recipient scale λ, U≥B_ii/λ_i.
   At recipient1, every pair premium is at least λ_1/10, and

   ```
   det Gamma=(51639171-2362945 delta)/50000000,
   det Gamma * [(1/10)B_11-1/768]
     =(956744829+4474945 delta)/38400000000>0.
   ```

   This contradicts the required cap for any role of that recipient and any
   positive scaling, independently of every corner-selection parameter.
8. **Opposite-row order.** On favorite pair01, choosing0 preferred forces
   the row-scale ratio to be at least Γ_13/Γ_03=100 and at most
   Γ_10/Γ_01=1100/1001. Choosing1 preferred forces its reciprocal to be
   at least Γ_02/Γ_12=20 and at most Γ_01/Γ_10=1001/1100. Both are
   impossible. These inequalities are among the literal singleton passive
   comparisons and exclude every two-pair orientation. Section13.2 also
   excludes the larger one-pair polynomial-weight selection.

### 13.4. Product-low and all trap-leaver selections

A product-low requirement asks that every absorbing independent product root
have some active owner whose forced-Quit payoff does not exceed its own solo
reward. The pure root on pair03 has active premiums J_03=9/1000 and J_30=1/200,
both strictly positive. It refutes that requirement exactly.

Every two-player set is a premium trap. On trap03, the joining differences
from the other owner's singleton are −A_03=1/100 and −A_30=7/100, both
positive. Neither endpoint can be even a weak leaver of this trap. Thus no
support-specific leaver selection works, regardless of its protected-set
choice. A common leaver would have to belong to every trap, whereas every
owner is omitted by some two-player trap. Finally, a weighted trap-leaver
condition requires strictly positive weights on the trap and nonpositive
weighted joining sums on every proper nonempty subset. On trap03 and
coalition{3}, that sum is w_0/100>0. This excludes every weight selection,
including any version with a strict improvement requirement. All these
witnesses retain their strict signs under small raw perturbations and
positive recipient scaling.

### 13.5. No-harm owners and singleton escorts

A no-harm singleton owner j requires Γ_ij≥0 for every recipient i.
Every column here has a negative crossing entry, so no owner qualifies.
A singleton escort edge i→j requires Γ_ij≤0≤Γ_ji. Every unordered
pair has the same strict sign in both directions, so this directed graph
has no edges. Any balanced singleton-cycle certificate would force an
escort cycle of length at least two: after erasing zero phases and merging
consecutive copies of the same owner, each transition must have just those
two opposite weak signs. Thus this excludes all such singleton-cycle
certificates, including repeated-owner or zero-phase presentations.
These strict sign obstructions persist nearby and under positive scaling.

### 13.6. Every literal child, including withdrawal-security rows

Let C be any nonempty proper child set and h an outside owner. A literal
advance-only certificate requires nonnegative weights a_i, i∈C, and,
for every nonempty S⊆C, the necessary future and joining rows

```
−Z_h(S) ≤ Σ_(i∈C) a_i[−Z_i(S)],                         (F)
Z_h(S∪{h})−Z_h(S)
       ≤ Σ_(i∈C) a_i[Z_i(S∪{i})−Z_i(S)].              (J)
```

Own singleton levels are zero in this difference notation. The same formulas
come from actual rewards by subtracting each recipient's own singleton.
They are necessary even when the separate Never row is omitted.

First consider a singleton child{j}. Choose the fixed crossing outsider h
by0→3,1→2,2→0,3→1. In(J)
at S={j}, the left side is −A_hj>0 and the right side is zero. For a
two-owner child, take S=C and choose the outsider by

```
01→2, 02→3, 03→1, 12→0, 13→2, 23→1.
```

The left side is1, while every summand on the right is zero. For triple
children, the following selected joining rows suffice:

| C | h | S | Necessary row |
| --- | --- | --- | --- |
| 012 | 3 | 02 | 1≤−a_1 |
| 013 | 2 | 01 | 1≤−a_3 |
| 023 | 1 | 23 | 1≤−a_0 |

For C=123,h=0, future rows S=12 and S={2} are

```
0 ≤ −(13/10)a_1−(9/20)a_2−a_3,
4 ≤ (1/5)a_1−(11/10)a_3.
```

Their sum reads 4≤−(11/10)a_1−(9/20)a_2−(21/10)a_3≤0.
This completes all fourteen child choices, including all nonnegative weights.

Stronger deadline certificates add nonnegative withdrawal weights d_i and
replace the right side of(J) by

```
Σ_(i∈C) {a_i[Z_i(S∪{i})−Z_i(S)]+d_i W_i(S)}.         (JW)
```

Here W_i(S)=0 for i∉S. For |S|≥2 and i∈S it is the exact withdrawal
difference Z_i(S\{i})−Z_i(S). For S={i}, it is γ_i−r_i({i}),
where γ_i is the selected actual security floor. All the raw zero-floor,
evaluated-security and untruncated terminal-security versions obey
γ_i≤r_i({i})=1. For the untruncated version this follows directly from
the singleton row in its security linear program; its additional zero floor
is at most zero. Taking their maximum, or truncating it at zero, preserves
the upper bound. Hence singleton withdrawal contributions are nonpositive.
No supplied security strategy or numerical linear-program conclusion is used.

For singleton children the same crossing outsider contradicts(JW). For
crossing two-player children02,03,12,13 use the same full-child joining
rows as above. Both withdrawal coefficients are the corresponding negative
A entries, so they cannot help. For favorite child01, take h=2,S={1}:

```
3/5 ≤ −a_0+d_1(γ_1−1) ≤ 0.
```

For favorite child23, take h=1,S={2}:

```
3/2 ≤ −a_3+d_2(γ_2−1) ≤ 0.
```

For triple children choose the following crossing coalitions instead:

| C | h | S | Necessary row |
| --- | --- | --- | --- |
| 012 | 3 | 02 | 1≤−a_1−6d_0−delta d_2 |
| 013 | 2 | 13 | 1≤−a_0−(2/5)d_1−(1/25)d_3 |
| 023 | 1 | 03 | 1≤−a_2−(1/100)d_0−(7/100)d_3 |

All right sides are nonpositive. For C=123,h=0 the two future rows
already contradict each other, independently of every withdrawal weight.
Thus even these stronger security-enhanced deadline certificates fail for
every child, every outsider-family selection, and every nonnegative pair
of weight vectors. This includes the advance-only certificates as d=0.

Positive recipient scaling is harmless: divide each outsider inequality by
its positive scale and absorb child scales into its nonnegative weights.
For each fixed positive delta, the strict crossing withdrawal and advance
coefficients in the selected rows persist under small raw perturbations. Coefficients that vanish because
an owner already belongs to S vanish identically for every reward table.
The singleton bound γ_i≤r_i({i}) persists while own rewards stay positive.
Finally the summed future-row contradiction has all three advance
coefficients strictly negative and left side4. These facts prove robust
failure without assuming bounded weights or continuity of optimal weights.

The algebraic contradictions in this subsection hold also at delta=0.
The open-neighborhood conclusion just stated is for each fixed positive
delta; the zero coefficient -delta d_2 is not used to infer robustness
at the endpoint with unbounded withdrawal weights.

### 13.7. Extent and robustness of the comparison

These are failures of precisely stated conditions and prescribed architectures,
not failures of equilibrium existence. The new producer gives exact equilibria
while those conditions remain unavailable. The stationary and fixed-pair
positive gaps remain positive under a sufficiently small raw perturbation:
every prescribed or deviating terminal payoff changes by at most the largest
reward perturbation, so exploitability changes by at most twice that amount.
The stationary gap is uniform over the closed parameter interval, as is the
fixed-pair gap. The sure-first comparison is robust by compactness of the
root cube and its continuation-cap bound. A raw perturbation of size eta
leaves every actual continuation cap at least1-eta; any new sure root in a
convergent perturbation sequence would limit to one of the excluded original
faces. All fourteen quotient minors, inverse positivity and determinant signs
remain strict on a small raw tube around the parameter interval.

For every fixed positive parameter, the strict matching signs and all direct
raw obstructions persist on a sufficiently small neighborhood of that table.
The all-weight ordered-wall argument uses the stationary gap and positive
inverse plus the matching singleton signs, so it still applies nearby.
The child contradictions remain valid with unbounded weights for the reasons
in Section13.6; boundedness of a search box of weights is never assumed.
Intersect these neighborhoods with the full60 producer neighborhood in
Section9 to obtain open raw classes having the asserted equilibrium and
comparisons.

No statement here bounds the maximal validity neighborhood of another
local construction around delta=1/1000, or rules out another solution branch
with a fixed thirty-three-phase word. The result is analytic production for every sufficiently small positive raw
parameter, with a common boundary basin and an integer selected from that
parameter. No finite-cycle center is supplied for those parameters. No bound
on the minimal period of an equilibrium, universal periodic architecture,
or unrestricted positive exploitability gap is asserted.

## 14. Source correspondence, reproduction, and handoff

AppendixA verifies the raw boundary inverses, exact cubic coefficients,
spectral intervals and dual-cone positivity, all boundary reset guards, the
whole interval of sixty-step entries and derivatives, the invariant cone,
the signed-ball contraction, the passive derivative bound, and the strict
reset window. The infinite-limit, uniform fixed-point, scale-selection and
behavioral arguments are Sections5--9; they are not inferred merely from a
program's PASS line. AppendixB supplies the complete uniform stationary cube,
all-support origin, parameter positivity and all fifteen quotient checks.
AppendixC supplies all changed sure-face identities and both complete fixed
pair Bernstein cubes. Their semantic boundary and full-response arguments
are Sections10--12.

Each appendix is a complete standalone Python3 program, with no repository
imports, external data file, numerical optimization oracle or retained leaf
dump required. AppendixA uses only the standard library; AppendicesB--C use
SymPy and NumPy. NumPy arrays contain Python integer objects. Saving each
code block as its own file and running it reproduces the exact finite proof
checks. Decimal output from interval displays is only explanatory; all
acceptance inequalities use outward integer endpoints or exact fractions.

The existing declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) consume a finite
root cycle, its policy recursion, exact local root Nash and strict opponent
survival per cycle. Those are the data produced here. The root equation
corresponds to `IsεQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`). The stationary field
correspondence is `stationaryQuittingGain_complementarity_iff_endpoints`
(`UniformEquilibrium/Quitting/Stationary/Gain.lean`). Literal response
invariance is `QuittingResponseInvariantOnUnitCube`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`),
and the degree computation agrees with
`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`). These named
sources were inspected; this packet supplies no checked instance in Lean.

The complete sure-first argument excludes `QuittingSingletonBaseCertificate`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`)
for every induced free carrier. The raw child rows are those of
`DeadlineWithdrawalRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`),
`DeadlineSecurityRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedRaw.lean`),
and `DeadlineSecurityTerminalRewardCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean`).
The singleton security upper bound is
`deadlineWithdrawalSecurityValue_le_singleton`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`).
No literature theorem or unverified security optimization is being substituted
for a raw inequality.

A formal producer would encode the raw family and exact interval bounds,
prove the triangular boundary projection and uniform Perron asymptotic,
produce fixed points by the uniform contraction argument, and select an
integer through the strict geometric reset window. Its theorem must output
the cycle from the raw parameter, rather than assume the cycle as certificate
data. The ordinary comparison proofs and finite Bernstein checks can be
formalized separately. No stronger claim about formalization or general
Fin4 closure follows from the current packet.

## Appendix A. Complete analytic boundary-reset checker

```python
"""Exact analytic boundary-reset certificate for a weak-crossing family.

A 512-bit outward integer interval engine certifies a whole interval of
boundary resets, an invariant cone, and uniform local derivatives.
No center for a finite periodic cycle is supplied or verified here.
"""
from fractions import Fraction as F
from math import isqrt
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
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*4 if d is None else d
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


def reset(s):
 t=s/6;h=F(3,2)*t/(1+t)
 b=[2*t/(1+t),(F(1,10)*h+F(13,10)*t)/((1+h)*(1+t)),0,(-F(13,200)*h+F(11,10)*t)/((1+h)*(1+t))]
 for _ in range(2):
  a=b[0]/6;k=(b[3]+a)/(F(7,100)+a);D=(1+k)*(1+a)
  b=[2*a/(1+a),(b[1]+F(11,10)*k-F(1,5)*a+k*a)/D,0,(F(1,200)*k+F(1,10)*a+k*a)/D]
 return b

def tail(b):
 b0,b1,b2,b3=b
 A=F(51,250)+b1;B=F(3,10)-F(11,25)*b2+F(9,10)*b3;C=b1+F(2,5)*b2+F(3,2)*b3-b2*b3
 disc=B*B+4*A*C
 sqrt=disc.sqrt()
 x=2*C/(B+sqrt);y=(x/25-b3)/(1+x);z=(F(3,5)*x-b2)/(1-x)
 d=(1+x)*(1+y)*(1+z)
 out=[(b0+F(1001,1000)*x-4*y-z/1000+x*z+y*z+x*y*z)/d,
      (F(13,10)*y+F(3,10)*z+y*z)/((1+y)*(1+z)),
      (F(9,20)*x+z/100+x*z)/((1+x)*(1+z)),
      (x/1000+y/10)/((1+x)*(1+y))]
 gap=(-x+6*y+z/100+x*y-x*z-y*z-x*y*z-b0)/d
 return out,[x/(1+x),y/(1+y),z/(1+z)],gap

def taylor_compose(mid,width,n=40):
 p=reset(Jet(Iv(mid)))
 b=reset(Jet(Iv.box(mid,width),[Iv(1),Iv(0),Iv(0),Iv(0)]))
 p=[x if isinstance(x,Jet)else Jet(x)for x in p]
 b=[x if isinstance(x,Jet)else Jet(x)for x in b]
 rad=Iv.box(0,width)
 qmin=Iv(1).lo;gmax=Iv(-1).hi
 for stage in range(n):
  p,_,_=tail(p)
  old_derivative=[x.d[0] for x in b]
  local=[Jet(x.v,[Iv(int(i==j)) for j in range(4)]) for i,x in enumerate(b)]
  b,qq,g=tail(local)
  for x in b:x.d=[sum((x.d[j]*old_derivative[j] for j in range(4)),Iv(0))]+[Iv(0)]*3
  assert all(q.v.lo>0 and q.v.hi<D for q in qq)
  assert g.v.hi*4 < -D
  qmin=min(qmin,min(q.v.lo for q in qq));gmax=max(gmax,g.v.hi)
  for i in range(4):b[i].v=p[i].v+rad*b[i].d[0]
 return b,F(qmin,D),F(gmax,D)

def cone(r,s,t):
 A=F(51,250)+r*t;B=F(3,10)-F(11,25)*t+F(9,10)*s*t;C=r+F(2,5)+F(3,2)*s-s*t
 y=2*C/(B+(B*B+4*A*t*C).sqrt())
 v=(y/25-s)/(1+y*t);w=(F(3,5)*y-1)/(1-y*t)
 u1=(F(13,10)*v+F(3,10)*w+v*w*t)/((1+v*t)*(1+w*t))
 u2=(F(9,20)*y+w/100+y*w*t)/((1+y*t)*(1+w*t))
 u3=(y/1000+v/10)/((1+y*t)*(1+v*t))
 return u1/u2,u3/u2,u2,[y,v,w]

def cone_check(n=16):
 lowr,hir=F(13,100),F(3,20);lows,his=F(9,1000),F(11,1000)
 extrema=[1,0,1,0,1,0]
 for i in range(n):
  r=Iv.box(lowr+(hir-lowr)*F(2*i+1,2*n),(hir-lowr)/(2*n))
  for j in range(n):
   s=Iv.box(lows+(his-lows)*F(2*j+1,2*n),(his-lows)/(2*n));t=Iv.box(F(1,20000),F(1,20000))
   rr,ss,tt,qs=cone(r,s,t)
   assert F(rr.lo,D)>lowr and F(rr.hi,D)<hir,('r',i,j,rr)
   assert F(ss.lo,D)>lows and F(ss.hi,D)<his,('s',i,j,ss)
   assert F(tt.lo,D)>F(4,5) and F(tt.hi,D)<F(87,100)
   assert all(x.lo>0 for x in qs)
   for k,x in enumerate([rr,ss,tt]):
    extrema[2*k]=min(extrema[2*k],F(x.lo,D));extrema[2*k+1]=max(extrema[2*k+1],F(x.hi,D))
 return [float(x)for x in extrema]

def rational(x):
 return F(x,D)

def absolute(x):
 return rational(x.absupper())

def verify_boundary_resets():
 # At delta=0, only recipient2's singleton0 and participant02 rewards change.
 rows={
  1:[0,F(11,10),0,-F(13,200)],
  2:[F(1001,1000),0,-F(3,20),-F(39,1000)],
  4:[-4,-F(1,5),0,F(11,10)],
  8:[-F(1,1000),-F(1,10),F(101,100),0],
  3:[F(1,1000),F(1,10),0,1],
  5:[2,1,0,0], 9:[F(9,1000),0,1,F(1,200)],
  6:[0,F(13,10),F(9,20),1],
  10:[1,F(3,10),0,F(1,1000)],
  12:[1,0,F(1,100),F(1,10)],
  7:[1,0,1,1], 11:[0,1,1,0], 13:[0,1,0,1],
  14:[1,1,1,0], 15:[0,0,0,0]}
 s=Iv.box(F(299,400),F(1,1000))
 b=[s,Iv(0),Iv(0),Iv(0)]
 t=s/6;h=F(3,2)*t/(1+t)
 q=[h/(1+h),Iv(0),t/(1+t),Iv(0)]
 for stage,support in enumerate([(0,1,2),(0,2,3),(0,2,3)]):
  if stage:
   a=b[0]/6;k=(b[3]+a)/(F(7,100)+a)
   q=[k/(1+k),Iv(0),a/(1+a),Iv(0)]
  for owner in (0,2):
   assert q[owner].lo>0 and q[owner].hi<D
  output=[]
  for owner in range(4):
   opp=[j for j in range(4)if j!=owner]
   p,qq,H=Iv(0),Iv(0),Iv(1)
   for j in opp:H*=1-q[j]
   for bits in range(8):
    mask=0;w=Iv(1)
    for n,j in enumerate(opp):
     if bits&(1<<n):mask|=1<<j;w*=q[j]
     else:w*=1-q[j]
    if mask:p+=w*rows[mask][owner]
    qq+=w*rows[mask|(1<<owner)][owner]
   output.append(p+H*b[owner])
   gap=qq-output[-1]
   if owner not in support:assert gap.hi*20 < -D
   else:assert gap.lo<=0<=gap.hi
  # Exact active identities give these rational outputs; using them also
  # preserves the identically zero recipient2 value without interval wrapping.
  if stage==0:
   b=[2*t/(1+t),(F(1,10)*h+F(13,10)*t)/((1+h)*(1+t)),Iv(0),
      (-F(13,200)*h+F(11,10)*t)/((1+h)*(1+t))]
  else:
   DD=(1+k)*(1+a)
   b=[2*a/(1+a),(b[1]+F(11,10)*k-F(1,5)*a+k*a)/DD,Iv(0),
      (F(1,200)*k+F(1,10)*a+k*a)/DD]
 # Asymptotic reset band and third reset guard, uniformly in the same s interval.
 a=t/(3*(1+t))
 v3=(-F(13,200)*h+F(11,10)*t)/((1+h)*(1+t))
 k=(v3+a)/(F(7,100)+a)
 upper=h+(F(3,5)+h)/(F(9,20)+h)*((1+h)*k-h/2)
 a2=a/(3*(1+a))
 v33=(k/200+a/10+k*a)/((1+k)*(1+a))
 k2=(v33+a2)/(F(7,100)+a2)
 third=k2-k/(2*(1+k))-k/(100*(1+k)*(1+k))
 assert rational(h.hi)<F(17,100)
 assert rational(upper.lo)>F(9,5)
 assert rational(third.lo)>F(3,20)

def verify_local_derivatives():
 weights=[F(7,50),F(1),F(11,1000)]
 b=[Jet(Iv.box(F(3,4),F(1,100)),[Iv(1),Iv(0),Iv(0),Iv(0)])]
 b += [Jet(Iv.box(0,w/10000),[Iv(int(i+1==j))for j in range(4)])
       for i,w in enumerate(weights)]
 out,_,gap=tail(b)
 assert rational(gap.v.hi)<-F(7,10)
 for i in range(1,4):
  norm=sum(absolute(out[i].d[j+1])*weights[j]/weights[i-1]for j in range(3))
  assert norm<F(9,10)
 coupling=sum(absolute(out[0].d[j+1])*weights[j]for j in range(3))
 assert coupling<F(1,2)
 return weights

def verify_entry(weights):
 out,_,_=taylor_compose(F(299,400),F(1,1000),60)
 assert rational(out[0].v.lo)>F(1869,2500)  # .7476
 assert rational(out[0].v.hi)<F(7477,10000)
 assert absolute(out[0].d[0])<F(1,125)
 for i,w in enumerate(weights):
  assert absolute(out[i+1].v)/w < F(6,10**6)
  assert absolute(out[i+1].d[0])/w < F(1,10**6)
 r=out[1].v/out[2].v;s=out[3].v/out[2].v
 assert F(13,100)<rational(r.lo) and rational(r.hi)<F(3,20)
 assert F(9,1000)<rational(s.lo) and rational(s.hi)<F(11,1000)

def verify_spectrum():
 def inverse(a):
  n=len(a);c=[[F(x)for x in row]+[F(int(i==j))for j in range(n)]
              for i,row in enumerate(a)]
  for j in range(n):
   pivot=next(i for i in range(j,n)if c[i][j])
   c[j],c[pivot]=c[pivot],c[j]
   scale=c[j][j];c[j]=[x/scale for x in c[j]]
   for i in range(n):
    if i==j:continue
    scale=c[i][j];c[i]=[x-scale*y for x,y in zip(c[i],c[j])]
  return [row[n:]for row in c]
 A=[[0,1,-6,-F(1,100)],[1,0,-F(3,2),-F(2,5)],
    [0,-F(3,5),0,1],[-F(7,100),-F(1,25),1,0]]
 J=[[0,F(1,1000),2,F(9,1000)],[F(1,10),0,F(13,10),F(3,10)],
    [0,F(9,20),0,F(1,100)],[F(1,200),F(1,1000),F(1,10),0]]
 Gamma=[[A[i][j]+J[i][j]for j in range(4)]for i in range(4)]
 assert min(x for row in inverse(A)for x in row)==F(40,773)
 assert min(x for row in inverse(Gamma)for x in row)==F(327470,51639171)
 inverseA3=inverse([row[1:]for row in A[1:]])
 M=[[-sum(J[i+1][k+1]*inverseA3[k][j]for k in range(3))
     for j in range(3)]for i in range(3)]
 assert M==[[F(58,75),F(7,750),-F(7,50)],
             [F(38,25),F(299,500),F(57,25)],
             [F(1,60),F(1,150),-F(3,40)]]
 trace=sum(M[i][i]for i in range(3))
 traceSquare=sum(M[i][j]*M[j][i]for i in range(3)for j in range(3))
 det=(M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
      -M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
      +M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
 assert trace==F(388900,300000)
 assert (trace*trace-traceSquare)/2==F(99765,300000)
 assert -det==F(13513,300000)
 # Signs at three disjoint intervals account for all roots of the cubic.
 def p(x):return 300000*x**3-388900*x**2+99765*x+13513
 for a,b in [(F(-1,10),F(-9,100)),(F(56,100),F(57,100)),
             (F(83,100),F(84,100))]:
  assert p(a)*p(b)<0
 assert F(9,10)**2<F(83,100)
 # A left eigenvector l(lambda), obtained from two rows of M^T-lambda I.
 # The signs below certify l.(r,1,s)>0 throughout the invariant cone.
 lam=Iv.box(F(167,200),F(1,200))
 # Set l0=1; row0 and row1 equations determine l1,l2.
 den=F(38,25)*F(1,150)-F(1,60)*(F(299,500)-lam)
 l1=((lam-F(58,75))*F(1,150)+F(1,60)*F(7,750))/den
 l2=(-F(38,25)*F(7,750)-(F(299,500)-lam)*(lam-F(58,75)))/den
 r=Iv.box(F(14,100),F(1,100));s=Iv.box(F(1,100),F(1,1000))
 assert (r+l1+l2*s).lo>0

if __name__=='__main__':
 verify_boundary_resets()
 print('PASS: boundary reset branches, strict inactive margins, and uniform reset band.')
 verify_spectrum()
 print('PASS: dominant positive cubic root in (.83,.84), dual positivity on the cone.')
 print('PASS: invariant cone (display bounds only):',cone_check())
 weights=verify_local_derivatives()
 verify_entry(weights)
 print('PASS: signed-ball contraction <.9; passive coupling <.5; full interval enters in60 steps.')
 print('Consequences: boundary projection self-map and derivative <.008005; no finite cycle center used.')
```

## Appendix B. Complete uniform stationary and quotient checker

```python
"""Uniform stationary and response-quotient audit for the weak-crossing family.

Python 3, SymPy, NumPy. Standalone: no external source/data imports.
The literal family has actual rewards 1+Z, live and Never reward zero.
Every arithmetic exclusion uses rational numbers or Python integer objects.
Both closed children of every split are retained; endpoint coefficient tests
cover every delta in [0,1/1000] by affine interpolation. Budget exhaustion
raises an error, never a proof result. No unrestricted UE obstruction claimed.
"""
import argparse
import itertools
from fractions import Fraction
import numpy as np
import sympy as s

I=tuple(range(4))
Q=Fraction
q=s.symbols('q0:4')
FAVORITE=(1,0,3,2)

def table(delta):
    R=s.Rational
    A=s.Matrix([[0,1,-6,-R(1,100)], [1,0,-R(3,2),-R(2,5)],
        [-delta,-R(3,5),0,1], [-R(7,100),-R(1,25),1,0]])
    J=s.Matrix([[0,R(1,1000),2,R(9,1000)], [R(1,10),0,R(13,10),R(3,10)],
        [delta/2,R(9,20),0,R(1,100)], [R(1,200),R(1,1000),R(1,10),0]])
    Gamma=A+J
    z={(i,0):s.S.Zero for i in I}
    for i in I:
        z[i,1<<i]=s.S.Zero
        for j in I:
            if j!=i:
                z[i,1<<j]=Gamma[i,j]
                z[i,(1<<i)|(1<<j)]=J[i,j]
    for pair,sign in zip(itertools.combinations(I,2),(1,-1,1,1,-1,-1)):
        mask=sum(1<<j for j in pair)
        outside=[i for i in I if not mask>>i&1]
        for order,i in enumerate(outside):
            delta=sign*(-1 if order else 1)
            z[i,mask]=s.sympify(max(0,-delta))
            z[i,mask|(1<<i)]=s.sympify(max(0,delta))
    for i in I:
        z[i,15^(1<<i)]=s.S.One
        z[i,15]=s.S.Zero
    assert len(z)==64
    return z

def fields(z):
    H=[];P=[];QQ=[]
    for i in I:
        pp=qq=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            pp+=z[i,mask]*w
            qq+=z[i,mask|1<<i]*w
        H.append(s.prod(1-q[j] for j in I if j!=i))
        P.append(s.expand(pp));QQ.append(s.expand(qq))
    F=[s.Poly(s.expand((1-H[i])*QQ[i]-P[i]),*q)for i in I]
    g=[s.expand(QQ[i]-P[i])for i in I]
    return H,F,g

def coefficients(polys):
    assert len(polys)==8
    assert all(poly.degree(q[j])<=2 for poly in polys for j in I)
    raw=[]
    for poly in polys:
        for alpha in itertools.product(range(3),repeat=4):
            value=sum(v*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                        for j in I) for mon,v in poly.terms()
                        if all(mon[j]<=alpha[j] for j in I))
            raw.append(s.sympify(value))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(8,3,3,3,3)
    return denominator,arr

def split_coefficients(b,axis):
    # Both child arrays represent their exact polynomials at FOUR TIMES
    # the parent's positive common denominator. Thus all sign tests below
    # use integers only; no interval rounding or tolerance is involved.
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    middle=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),middle),axis=-1)
    right=np.stack((middle,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(polys,max_nodes=200000,max_depth=120):
    denominator,b=coefficients(polys)
    stack=[([Q(0)]*4,[Q(1)]*4,b,0)]
    nodes=leaves=depthmax=origin=0
    while stack:
        lo,hi,b,depth=stack.pop()
        nodes+=1;depthmax=max(depthmax,depth)
        if max(hi)<=Q(1,256):
            leaves+=1;origin+=1;continue
        witness=False
        for i in I:
            # Rows i and i+4 are the two parameter endpoints. Each
            # intermediate Bernstein coefficient is their convex blend.
            row=np.concatenate((b[i].flatten(),b[i+4].flatten()))
            if (lo[i]>0 and max(row)<0) or (hi[i]<1 and min(row)>0):
                witness=True;break
        if witness:
            leaves+=1;continue
        if nodes>=max_nodes or depth>=max_depth:
            raise RuntimeError('Unexcluded box after budget: '+str({
                'nodes':nodes,'depth':depth,'lo':lo,'hi':hi}))
        widths=[hi[i]-lo[i]for i in I]
        choices=[i for i in I if widths[i]==max(widths)]
        axis=choices[depth%len(choices)]
        left,right=split_coefficients(b,axis)
        middle=(lo[axis]+hi[axis])/2
        lower=lo.copy();lower[axis]=middle
        upper=hi.copy();upper[axis]=middle
        stack.append((lower,hi,right,depth+1))
        stack.append((lo,upper,left,depth+1))
    assert nodes==2*leaves-1
    assert (nodes,leaves,depthmax,origin)==(175585,87793,62,1)
    print('PASS: uniform entire stationary cube;175585 nodes,87793 leaves,depth62')

def partitions(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for part in partitions(rest):
        yield ((first,),)+part
        for j,block in enumerate(part):
            yield part[:j]+((first,)+block,)+part[j+1:]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--origin-only',action='store_true')
    parser.add_argument('--max-nodes',type=int,default=200000)
    parser.add_argument('--max-depth',type=int,default=120)
    args=parser.parse_args()
    d=s.Symbol('delta',real=True);dmax=s.Rational(1,1000)
    z=table(d);H,F,g=fields(z)
    assert len(z)==64
    assert z[2,1]==-d/2 and z[2,5]==d/2
    assert all(not value.has(d)for key,value in z.items()if key not in((2,1),(2,5)))
    assert all(s.Poly(f.as_expr(),d).degree()<=1 for f in F)
    Gamma=s.Matrix([[z[i,1<<j]for j in I]for i in I])
    J=s.Matrix([[z[i,(1<<i)|(1<<j)]if i!=j else 0 for j in I]for i in I])
    A=Gamma-J
    endpoints=[]
    for dd in (s.S.Zero,dmax):
        zz={key:value.subs(d,dd)for key,value in z.items()}
        FF=[s.Poly(f.as_expr().subs(d,dd),*q)for f in F]
        GG=Gamma.subs(d,dd);JJ=J.subs(d,dd)
        assert all(zz[i,m]>=0 for i in I for m in range(1,16)if m>>i&1)
        assert all(FF[i].coeff_monomial(1)==0 for i in I)
        assert all(FF[i].coeff_monomial(q[j])==-GG[i,j]for i in I for j in I)
        KK=max(sum(abs(v)for mon,v in f.terms()if sum(mon)>=2)for f in FF)
        BB=GG.inv();LL=max(sum(BB.row(i))for i in I)
        assert min(BB)>0
        endpoints.append((zz,FF,GG,JJ,KK,LL))
    # Determinant and every adjugate entry are affine in delta and
    # strictly positive at both endpoints, hence throughout the interval.
    for matrix in (Gamma,A):
        det=s.expand(matrix.det());adj=matrix.adjugate()
        assert s.Poly(det,d).degree()<=1
        assert all(s.Poly(v,d).degree()<=1 for v in adj)
        assert all(det.subs(d,dd)>0 and min(adj.subs(d,dd))>0 for dd in (0,dmax))
    assert Gamma.subs(d,0).det()==s.Rational(51639171,50000000)
    assert min(Gamma.subs(d,0).inv())==s.Rational(327470,51639171)
    assert min(A.subs(d,0).inv())==s.Rational(40,773)
    K=max(e[4]for e in endpoints);L=max(e[5]for e in endpoints)
    # Coefficient absolute sums are convex in delta. Each inverse row
    # sum is a positive affine/affine quotient, monotone or constant.
    assert K==s.Rational(1913,50)
    assert L==s.Rational(59425126500,10327361611)
    assert K*L/256==s.Rational(1136802669945,1321902286208)<1
    for owner in I:
        other=next(i for i in I if all(e[2][i,owner]<0 for e in endpoints))
        for zz,FF,GG,JJ,KK,LL in endpoints:
            t=s.Symbol('t')
            got=FF[other].as_expr().subs({q[i]:t if i==owner else 0 for i in I})
            assert s.expand(got-t*(JJ[other,owner]*t-GG[other,owner]))==0
            assert JJ[other,owner]>0
    for i,j in itertools.combinations(I,2):
        for zz,FF,GG,JJ,KK,LL in endpoints:
            assert GG[i,j]<0 or GG[i,j]>JJ[i,j]>0
            t=s.Symbol('t')
            got=FF[i].as_expr().subs({q[h]:t if h==j else 0 for h in I})
            assert s.expand(got-t*(JJ[i,j]*t-GG[i,j]))==0
    for support in itertools.combinations(I,3):
        owner=next(i for i in support if FAVORITE[i]not in support)
        j,k=[h for h in support if h!=owner]
        for zz,FF,GG,JJ,KK,LL in endpoints:
            cross=-GG[owner,j]-GG[owner,k];passive=zz[owner,(1<<j)|(1<<k)]
            assert GG[owner,j]<=0 and GG[owner,k]<=0 and passive>=0
            assert (cross+passive)/256<cross
    print('PASS: uniform all-support origin; K=',K,'L=',L,'KL/256=',K*L/256)
    print('PASS: Gamma and A inverses strictly positive throughout [0,1/1000]')
    expected=[-s.Rational(1999,5000),s.Rational(101,25),-s.Rational(2611,10000),
        s.Rational(217,1000),-s.Rational(188,625),s.Rational(13,250),
        -s.Rational(589,5000),s.Rational(86,25),s.Rational(19,5),
        s.Rational(12561,100000),-s.Rational(2563,625),-s.Rational(20543,50000),
        -s.Rational(473,500),s.Rational(3881,250)]
    count=0;invariant=[]
    for part in partitions(list(I)):
        ts=s.symbols('t:'+str(len(part)))
        sub={q[i]:ts[j]for j,block in enumerate(part)for i in block}
        polys=[s.Poly(ff.as_expr().subs(sub),*ts)for ff in F]
        witness=None
        for block in part:
            for i,j in itertools.combinations(block,2):
                monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),key=lambda a:(sum(a),a))
                for aa,bb in itertools.combinations(monoms,2):
                    minor=s.expand(polys[i].coeff_monomial(aa)*polys[j].coeff_monomial(bb)
                        -polys[i].coeff_monomial(bb)*polys[j].coeff_monomial(aa))
                    if minor.subs(d,0)!=0:
                        witness=(i,j,aa,bb,minor);break
                if witness:break
            if witness:break
        if witness:
            minor=s.Poly(witness[-1],d);constant=minor.coeff_monomial(1)
            assert constant==expected[count]
            # This simple exact perturbation bound rules out a zero on
            # the WHOLE closed parameter interval, not only near zero.
            remainder=sum(abs(c)*dmax**mon[0]for mon,c in minor.terms()if mon[0]>0)
            assert remainder<abs(constant)
            count+=1
        else:
            invariant.append(part)
    assert count==14 and invariant==[((0,),(1,),(2,),(3,))]
    print('PASS: all15 partitions;all14 nondiscrete coefficient minors nonzero uniformly')
    print('PASS: discrete Gamma has positive inverse/determinant;R0 degree+1')
    if not args.origin_only:
        certify(endpoints[0][1]+endpoints[1][1],args.max_nodes,args.max_depth)
    print('SCOPE: stationary prescribed profiles and response quotients only;no UE gap claim')

if __name__=='__main__':main()
```

## Appendix C. Complete uniform sure-face and fixed-pair checker

```python
"""Uniform exact proper alternating-pair exclusion for the weak-crossing family.

Python 3, SymPy, NumPy. All proof arithmetic is rational or Python integer.
All sixty rewards and proof rules are supplied here; no data files are read.
Optional --write-certificate PATH records every exact dyadic leaf.
This excludes proper four-owner two-pair Nash, not arbitrary equilibria.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=range(4)
delta_parameter=s.symbols("delta_parameter",real=True)
A=s.Matrix([[0,1,-6,-s.Rational(1,100)],
 [1,0,-s.Rational(3,2),-s.Rational(2,5)],
 [-delta_parameter,-s.Rational(3,5),0,1],
 [-s.Rational(7,100),-s.Rational(1,25),1,0]])
J=s.Matrix([[0,s.Rational(1,1000),2,s.Rational(9,1000)],
 [s.Rational(1,10),0,s.Rational(13,10),s.Rational(3,10)],
 [delta_parameter/2,s.Rational(9,20),0,s.Rational(1,100)],
 [s.Rational(1,200),s.Rational(1,1000),s.Rational(1,10),0]])
Gamma=A+J
q=s.symbols('q0:4')
SIGNS={(0,1):1,(0,2):-1,(0,3):1,(1,2):1,(1,3):-1,(2,3):-1}

def table():
    z={}
    for i in I:
        for mask in range(1,16):
            opp=[j for j in I if mask>>j&1 and j!=i]
            if not opp:
                value=0
            elif len(opp)==1:
                value=J[i,opp[0]] if mask>>i&1 else Gamma[i,opp[0]]
            elif len(opp)==2:
                outside=[j for j in I if j not in opp]
                delta=SIGNS[tuple(opp)]*(1 if i==outside[0] else -1)
                value=max(0,delta) if mask>>i&1 else max(0,-delta)
            else:
                value=0 if mask>>i&1 else 1
            z[i,mask]=s.sympify(value)
    return z

def fields(z,mate):
    equations=[];gaps=[]
    for i in I:
        j,k=[a for a in I if a not in(i,mate[i])]
        m=mate[i];p=J[i,m];c=-A[i,m]
        passive=z[i,(1<<j)|(1<<k)]
        joining=z[i,(1<<i)|(1<<j)|(1<<k)]
        D=(1-q[j])*(1-q[k])
        C=(Gamma[i,j]*q[j]*(1-q[k])+Gamma[i,k]*q[k]*(1-q[j])
           +passive*q[j]*q[k]+p*q[m]*D)
        Q=J[i,j]*q[j]*(1-q[k])+J[i,k]*q[k]*(1-q[j])+joining*q[j]*q[k]
        equations.append(s.Poly(s.expand((1-q[m])*C-c*q[m]),*q))
        gaps.append(s.Poly(s.expand((1-q[m])*Q-c*q[m]),*q))
    for i in I:
        assert equations[i].total_degree()<=4
        assert equations[i].coeff_monomial(1)==0
        for j in I:
            assert equations[i].coeff_monomial(q[j])==Gamma[i,j]
    assert all(p.degree(variable)<=2 for p in equations+gaps for variable in q)
    return equations,gaps

def coefficients(polys):
    raw=[]
    for p in polys:
        for alpha in itertools.product(range(3),repeat=4):
            raw.append(sum(value*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                           for j in I)for mon,value in p.terms()
                           if all(mon[j]<=alpha[j]for j in I)))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(16,3,3,3,3)
    return denominator,arr

def split(b,axis):
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    mid=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),mid),axis=-1)
    right=np.stack((mid,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(z,mate):
    equations,gaps=fields(z,mate)
    assert all(s.Poly(p.as_expr(),delta_parameter).degree()<=1 for p in equations+gaps)
    ends=[s.S.Zero,s.Rational(1,1000)]
    # Every inverse entry has a positive affine numerator and one common
    # positive affine denominator. Each row sum is fractional linear, so
    # its supremum on this parameter interval is at an endpoint.
    determinant=s.expand(Gamma.det());adjugate=Gamma.adjugate()
    assert s.Poly(determinant,delta_parameter).degree()<=1
    assert all(s.Poly(v,delta_parameter).degree()<=1 for v in adjugate)
    assert all(determinant.subs(delta_parameter,d)>0 for d in ends)
    assert all(v.subs(delta_parameter,d)>0 for v in adjugate for d in ends)
    L=max(sum(Gamma.subs(delta_parameter,d).inv().row(i))for d in ends for i in I)
    # Coefficient absolute-value sums are convex in the parameter.
    K=max(sum(abs(v.subs(delta_parameter,d))for mon,v in p.terms()if sum(mon)>=2)
          for p in equations for d in ends)
    origin_radius=Fraction(1,256)
    assert L*K/256<1
    endpoints=[s.Poly(p.as_expr().subs(delta_parameter,d),*q)
               for d in ends for p in equations+gaps]
    den,b=coefficients(endpoints)
    stack=[(b,(Fraction(0),)*4,(Fraction(1),)*4,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        b,lo,hi,path=stack.pop();nodes+=1;maxdepth=max(maxdepth,len(path))
        reason=None;bound=None;index=None
        if max(hi)<=origin_radius:
            reason='analytic_origin'
        else:
            flat=b.reshape(16,-1)
            mins=[min(min(flat[i]),min(flat[8+i]))for i in range(8)]
            maxs=[max(max(flat[i]),max(flat[8+i]))for i in range(8)]
            for i in I:
                if mins[i]>0:
                    reason,index,bound='equation_positive',i,int(mins[i]);break
                if maxs[i]<0:
                    reason,index,bound='equation_negative',i,int(maxs[i]);break
            if reason is None:
                for i in I:
                    if mins[4+i]>0:
                        reason,index,bound='inactive_gap_positive',i,int(mins[4+i]);break
        if reason is not None:
            leaves.append({'path':path,'reason':reason,'index':index,'integer_bound':bound,
                           'denominator':den*4**len(path),'lo':list(map(str,lo)),
                           'hi':list(map(str,hi))})
            continue
        if len(path)>=100 or nodes>1000000:
            raise RuntimeError('Unresolved box: no proof accepted at a stopping budget')
        axis=max(I,key=lambda i:hi[i]-lo[i]);mid=(lo[axis]+hi[axis])/2
        left,right=split(b,axis)
        lo1=list(lo);lo1[axis]=mid
        hi0=list(hi);hi0[axis]=mid
        stack.append((right,tuple(lo1),hi,path+'1'))
        stack.append((left,lo,tuple(hi0),path+'0'))
    assert nodes==2*len(leaves)-1
    return {'mate':mate,'L':str(L),'K':str(K),'origin_radius':str(origin_radius),
            'nodes':nodes,'maxdepth':maxdepth,'leaves':leaves}

def sure_faces(z):
    gaps=[]
    for i in I:
        value=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            value+=(z[i,mask|(1<<i)]-(z[i,mask] if mask else 0))*w
        gaps.append(s.factor(value))
    x,y,w=s.symbols('x y w')
    f0=[s.expand(g.subs(dict(zip(q,(1,x,y,w)))))for g in gaps]
    assert s.expand(f0[1]-(-1+2*w*(1-y)))==0
    a=delta_parameter+(1-delta_parameter)*x
    assert s.expand(f0[2]-(a-(1+a)*w))==0
    assert s.expand(f0[3]-(7-107*x+93*y*(1-x))/100)==0
    assert s.simplify(f0[0].subs({x:s.Rational(7,107),y:0,w:s.Rational(1,2)}))==-s.Rational(13,214)
    assert s.simplify(f0[2].subs({x:s.Rational(7,107),y:0,w:s.Rational(1,2)}))==(50*delta_parameter-50)/107
    for owner in (1,3):
        assert all(s.diff(g.subs(q[owner],1),delta_parameter)==0 for g in gaps)
    assert all(s.diff(g.subs(q[2],1),delta_parameter)==0 for i,g in enumerate(gaps)if i!=2)
    radical=s.sqrt(205)
    point={q[0]:(-5+radical)/18,q[1]:(15-radical)/20,q[2]:1,q[3]:(22-radical)/9}
    upper=s.simplify(gaps[2].subs(point).subs(delta_parameter,s.Rational(1,1000)))
    assert s.simplify(upper-(170187-12919*radical)/18000)==0
    assert 12919**2*205-170187**2>0
    assert s.expand(s.diff(gaps[2],delta_parameter)-q[0]*(1-q[1])*(1-q[3]))==0
    print('PASS all parameter-dependent sure-face identities; remaining faces unchanged')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-certificate')
    args=parser.parse_args();z=table();sure_faces(z)
    friendly=(1,0,3,2)
    assert all(-A[i,friendly[i]]==-1 for i in I)
    records=[certify(z,mate)for mate in ((2,3,0,1),(3,2,1,0))]
    if args.write_certificate:
        with open(args.write_certificate,'w')as out:json.dump(records,out,indent=2)
    for r in records:
        print('PASS uniform delta[0,1/1000]',r['mate'],r['nodes'],'nodes',len(r['leaves']),'leaves',
              'depth',r['maxdepth'],'K',r['K'],'L',r['L'])
    print('PASS complete proper two-pair parameter cube; semantic zero/sure cases require the accompanying proof')

if __name__=='__main__':main()
```

