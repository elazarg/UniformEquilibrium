# Two-row continuation in the four-player test family

Owner: CODEX_ROOT. The stationary construction is by crossfield_global_algebra;
the periodic construction is by crossfield_switched_control.

Status: rigorous ordinary mathematics with exact computational certificates,
not a new Lean result. These are internal steps toward covering one explicit
two-parameter family. Arbitrary Fin4 and the whole family remain open.

## Current coverage and next question

All parameters below satisfy delta,epsilon>=0, and all claims allow arbitrary
fixed signed offsets in the four reward rows. The raw table is specified in
the stationary section below.

| Region | Justification |
| --- | --- |
| delta>=3/2, every epsilon>=0 | [Global dominated-row producer](../exports/DOMINATED_ROW_ARBITRARY_ROW_STATIONARY_UNIFORM_EQUILIBRIUM.md) |
| 0<=delta<=38/25, .737+.06delta<=epsilon<=2 | The stationary producer below; two independent full checks |
| epsilon>=10201/5400, every delta>=0 | The singleton obstruction below |
| epsilon=.04, every delta>=0 | [Complete complex-spectrum ray](../exports/COMPLETE_COMPLEX_SPECTRUM_RAY_UNIFORM_EQUILIBRIUM.md) |
| 0<=delta<=10^-5, .34<=epsilon<=.36 | The periodic support-change band below; independent full check |

Consequently any still-uncovered parameter of this family lies in

    0<=delta<3/2,   0<=epsilon<.737+.06delta,

with the known ray, band, and their established neighborhoods removed. This
is a containing region for the unfinished work, not an exact description of
all parameters without a known equilibrium. It is not a constraint on an
arbitrary Fin4 counterexample. In particular no stationary nonexistence claim
is being made for the remaining region.

The next question is whether actual periodic Nash continuation can cover this
entire lower region, including every support change and parameter boundary.
A contracting cycle at a sample point alone does not answer it. The band
below supplies continuous legal selectors on cells where an optional player
may activate. It does not identify one cycle across different cells.

## A singleton obstruction outside the finite region

For the raw table below the projective singleton matrix is Gamma=A+J;
signed row offsets cancel. If there were no uniform-equilibrium payoff,
`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
would supply w>=0, sum_i w_i=1, with Gamma w strictly positive.
Rows0 and3 then imply

    (101/100)w1 > (3/5)w2+(9/1000)w3,
    (101/100)w2 > (7/1000)w0+(9epsilon/10)w1.

In particular w1>0 and

    w1 > (60/101)w2 > (5400epsilon/10201)w1.

This is impossible for epsilon>=10201/5400. The cited declaration has no
own-reward-sign, invertibility, normality, or strategy-certificate hypothesis.
Its declaration and the definition `quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` were inspected;
no Lean command ran for this application.

## Affine stationary producer

### Claim and data

Players are I={0,1,2,3}. The native own-singleton reward is zero. Set

```
       [ 0       1       -6       -1/100 ]
 A  =  [ 1       0       -3/2     -2/5   ],
       [ -delta  -3/5    0        1      ]
       [ -7/100  -epsilon 1       0      ]

       [ 0       1/100   27/5     1/1000    ]
 J  =  [ 1/100   0       3/20     9/25      ].
       [ delta/10 27/50  0        1/100     ]
       [ 63/1000 epsilon/10 1/100 0         ]
```

The following rules specify every one of the sixty nonempty-coalition
native rewards Z_i(S), without referring to another family:

* Z_i({i})=0.
* For j!=i, Z_i({j})=A_ij+J_ij and Z_i({i,j})=J_ij.
* For B in ({0,1},{0,2},{0,3},{1,2},{1,3},{2,3}), let
  s(B) be respectively (1,-1,1,1,-1,-1). For each i outside B, put
  Delta_i(B)=s(B) if i is the smaller of the two outsiders, and
  Delta_i(B)=-s(B) if i is the larger. Set
  Z_i(B)=max(0,-Delta_i(B)) and
  Z_i(B union {i})=max(0,Delta_i(B)).
* Z_i(I minus {i})=1 and Z_i(I)=0.

These assignments are disjoint and exhaustive. The four parameter-dependent
entries are exactly

```
 Z2({0})=-9delta/10, Z2({0,2})=delta/10,
 Z3({1})=-9epsilon/10, Z3({1,3})=epsilon/10.
```

The original game may have any signed row offsets c_i in R:
r_i(S)=c_i+Z_i(S) for nonempty S. Live play and Never give zero. There is no
restriction on these offsets; the produced hazard vector is independent of them.

**Claim.** For every delta in [0,38/25] and

 epsilon in [737/1000+(3/50)delta, 2],

the specified game has a proper stationary exact terminal Nash equilibrium
against every complete behavioral deviation, and its payoff is one fixed
uniform-equilibrium payoff. The stationary profile may depend on delta and
epsilon but can be used for every accuracy.

### Global recovery geometry

Write q=(a,b,x,y), x=q2. For each opponent subset B contained in I minus {i},
put pi_i(B)=product_(j in B)q_j product_(j outside B+i)(1-q_j), and define

 H_i=pi_i(empty),
 P_i=sum_(nonempty B) pi_i(B) Z_i(B),
 Q_i=sum_(all B) pi_i(B) Z_i(B union {i}),
 F_i=(1-H_i)Q_i-P_i.

Here P_i omits the empty opponent subset, whose continuation is accounted for
separately by H_i.

For positive absorption A=1-product_i(1-q_i), actual stationary payoff is
U_i=[q_i Q_i+(1-q_i)P_i]/A and
Q_i-(P_i+H_i U_i)=F_i/A. Thus F=0 at proper q gives every stationary Bellman
indifference. Neither virtual continuation nor an artificial cap is supplied.

Use t=q2+(3/100)delta, so x=q2=t-(3/100)delta. Fix delta and t.
Solve the three exact equations F0=F1=F2=0 for v=(a,b,y).
These equations are independent of epsilon. The row3 equation is affine:

 F3(delta,epsilon)=F3(delta,0)+epsilon C,
 C=(1-H3/10)b(1-a)(1-x)>0.

Hence recover E(delta,t)=-F3(delta,0)/C. It suffices to construct one
continuous proper root v(delta,t), for each fixed delta, on
t in [11/100,2/5], with

 E(delta,11/100)<737/1000+(3/50)delta, E(delta,2/5)>2.

The intermediate value theorem then gives every prescribed epsilon in the
claimed interval. No monotonicity or nonvanishing Jacobian of E is assumed.

### Exact two-parameter fibre certificate

The companion checker works on closed rectangles
[t_left,t_right] times [delta_left,delta_right]. Write centers tm,dm and
halfwidths ht,hd. For each rectangle it proposes rational c, columns St,Sd,
an invertible rational B, and positive rational radius r. Its affine center is

 c(t,delta)=c+St(t-tm)+Sd(delta-dm).

On the entire outer tube |v_i-c_i(t,delta)|<=r_i, interval arithmetic proves
all hazards proper and bounds the derivative of T(v)=v-B f(v,t,delta),
f=(F0,F1,F2), by K=I-B D_v f. Put

 M_i=sum_j sup|K_ij|r_j.

For theta=(theta1,theta2) in [-1,1]^2, form the literal polynomial vector

 G(theta)=-B f(c+St ht theta1+Sd hd theta2,
              tm+ht theta1,dm+hd theta2).

The checker expands these three bivariate polynomials using exact rational
coefficient arithmetic. Let R_i be the sum of the absolute values of ALL
coefficients of G_i. Then |G_i(theta)|<=R_i on the whole square, including
the constant and any residual linear terms. This retains cancellation before
taking absolute values. No sampled residual or floating error estimate is used.

The checked inequalities are

 max_i M_i/r_i<1/2,       R_i+M_i/4<r_i/4.

The map is a contraction on each fixed-parameter outer cube and preserves
its inner radius-r/4 cube. It has a unique outer-cube root, which lies in
the inner cube and varies continuously with both parameters. B is invertible
because it is constructed as the exact inverse of a rational midpoint
Jacobian with nonzero pivots. Thus a fixed point is an exact zero of f.

At adjacent t-cells within the SAME delta slab, the checker verifies

 |c_right(t_edge,dm)-c_left(t_edge,dm)|_i
 +|(Sd_right-Sd_left)_i| hd+r_left,i/4 < r_right,i.

For every delta in that closed slab, the previous inner root therefore
belongs to the next outer cube. Uniqueness glues the roots at the entire
shared edge. A continuous root curve is obtained for every fixed delta.
Different delta slabs need not select the same root at their shared edge:
this theorem needs existence for each delta, not a globally selected sheet.

At t=2/5, evaluate E on the certified inner root box, including the full
delta-slab width, and prove E>2. The sharp left endpoint uses extra closed
delta intervals of width at most 1/500. At fixed t=11/100, solve f=0 again by
the same contraction test with a smaller error box. The checker proves that
this refined inner root belongs to the main first cell's outer box for every
delta in the refinement interval; uniqueness identifies the roots. It then
verifies

 upper_bound E < 737/1000+(3/50)delta_left
                <=737/1000+(3/50)delta.

The root identification uses the difference of the two affine centers at the
refinement midpoint, plus the difference of their Sd columns times the
refinement halfwidth, plus the refined inner radius. Every coordinate must
be strictly below the main outer radius. Thus the global endpoint comparison
concerns the SAME continuous curve, not a reselected root. All bounds concern
closed rectangles and seams; samples do not establish coverage.

### Behavioral and uniform consumer

Every produced hazard is strictly between zero and one. With q fixed,
opponents alone therefore absorb geometrically after deleting any one
owner, uniformly over that owner's complete behavioral replacement.
Iterating Bellman equality/inequality leaves a bounded continuation term
which tends to zero under every replacement. This gives exact terminal Nash
against all finite deadlines, Never, and all behavioral mixtures thereof.

All prescribed and deviating paths absorb almost surely. A signed row offset
therefore adds the same constant to the prescribed and every deviating
terminal payoff. The profile remains exact terminal Nash in the original
game. For each i, the probability h_i=1-H_i of an opponent quit in any live round
is strictly positive and independent of i's strategy. Thus every unilateral
replacement has expected absorption time at most 1/h_i. If M bounds all
absolute original terminal rewards, the difference between its expected
terminal payoff and N-round average payoff is at most M/(N h_i), under either
usual convention for counting the absorbing round. The prescribed profile
has the same bound. Hence its possible N-round deviation gain is at most
2M/(N min_i h_i), tending to zero uniformly over complete behavioral
replacements. Its N-round payoff converges to its exact terminal payoff.
This yields one fixed uniform-equilibrium target and a profile usable at every
accuracy.

### Implementation and scope

The final companion is [CODEX_COORDINATOR__TWO_ROW_AFFINE_FRONTIER.py](../experiments/CODEX_COORDINATOR__TWO_ROW_AFFINE_FRONTIER.py)
(253 lines). It has no external data files and requires Python 3, SymPy, NumPy,
and SciPy. From the repository root, run

```sh
python -u math/experiments/CODEX_COORDINATOR__TWO_ROW_AFFINE_FRONTIER.py
```

Do not use `python -O`: acceptance tests are Python assertions.
Candidate floats only select rational centers; all acceptance, properness,
contraction, seam and endpoint tests use outward dyadic integer intervals.
The exact stationary fields are rebuilt from the sixty-entry construction
given above, so the checker does not assume symbolic field identities supplied
in a separate file. Its adaptive search can vary in its rational proposals
across numerical-library versions; only a successful final `PASS_ALL` verifies
all obligations. A failed proposal or incomplete run is not a proof.

The complete standalone run passed **9644 main rectangles and 760 refined
left-endpoint rectangles**, including every seam and boundary. The final output
was

```
PASS_ALL 9644 endpointcells 760 maxlip 0.49999113070776946
 epsilon_offset_upper 0.7362824945238263 right_lower 2.602016547818325
```

These printed decimal diagnostics are rounded summaries. The actual acceptance
uses exact comparisons with 1/2, 737/1000+(3/50)delta_left, and 2 as described
above. The run took approximately eleven minutes in the available environment.
The standalone checker SHA256 is
`d1695483f9210cd76c5703d9d98a8791cc02eec316bfb38bdd89c3a7203e1e8b`.

No Lean command ran. This is an internal two-parameter bridge for this specified family,
not a closure of arbitrary positive-collision games. It can be combined with
separately proved low-parameter periodic regions and high-delta producer
regions only after their endpoint intervals are checked to overlap.

The existing named consumers inspected are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean. They consume the
actual stationary data above; no new Lean implementation or check is claimed.

This stationary producer does not cover epsilon below the affine frontier,
delta above 38/25, or epsilon above 2. It does not show the frontier is optimal, classify
all stationary roots, or decide any of those remaining regions. The role of
the computation is a finite exact proof of this one connected stationary
producer; its discovery and floating candidates alone carry no conclusion.

## Periodic continuation allowing a support change

**Claim.** For every delta in[0,10^-5] and epsilon in[.34,.36], the native reward
table above has a64-period equilibrium with positive absorption against every
unilateral behavioral deviation. Consequently it has a uniform equilibrium.
Arbitrary fixed signed row offsets may be added to all rewards of each owner.

### Period and common raw table

Use exactly the sixty rewards specified in the stationary section above.

The backward support word is013^4 followed by012^60. At its first012 stage,
owner3 may also quit. In physical time the order is59 ordinary012 stages,
one012-or0123 stage, then four013 stages. The program chooses continuous Nash
branches within each certified parameter cell; different cells need not select
a single globally identified branch.

### Implicit roots and the support seam

For continuation b let g_i=Q_i-P_i-H_i b_i, with Q the quit payoff, P the
absorbing contribution when continuing, and H the probability all opponents
continue. The program uses512-bit outward integer intervals. Floats merely
propose rational root centers, inverse matrices and affine slopes.

For active set S, a rational preconditioner C and hazard rectangle X about qhat
are accepted only if, on the entire input and hazard boxes,

    |C g_S(qhat)|_i + sum_j |(I-C Dqg_S)_ij| r_j < r_i,
    ||I-C Dqg_S||_infinity < .9.

Thus q -> q-Cg_S maps X strictly into itself and contracts. The second bound
implies C and Dqg_S are invertible, so its unique fixed point is an implicit
root, unique within X. Strict containment gives local C1 dependence. Interval
Gaussian elimination on C Dqg_S encloses the inverse; every pivot is checked
positive. The implicit derivative is -(Dqg_S)^-1 times the direct input
derivative of g_S. No global uniqueness among all possible roots is assumed.

At the optional-owner stage, a uniformly negative quiet gap selects012. A
uniformly positive quiet gap and a physical full root select0123. Otherwise
both the quiet root and a signed full root are certified. A third uniform
Newton check solves the persistent012 equations with owner3's hazard y ranging
between zero and the signed full root y*. Its uniqueness tube contains both
persistent-root tubes. The reduced gap f(y)=g_3(psi(y),y) has derivative

    f_y = D_y g_3 - D_x g_3 (D_x g_012)^-1 D_y g_012 < 0.

Since f(y*)=0, f(0) and y* have the same sign. Choose the quiet branch for
y*<=0 and the full branch for y*>0. These branches agree at y*=0 by tube
uniqueness. The selector is continuous and piecewise C1; its derivative is
bounded by the hull of the two branch derivatives. Intermediate signed bridge
hazards need not be physical; the two selected branches have the required
physical probabilities. All other stages have strict active-probability and
quiet-gap checks.

### Return certificate and finite cover

In each cell, with parameter midpoint p0 and half-widths h, use the moving cap
fiber c+V(p-p0)+E, where |E_i|<=r_i and

    r=(1/20000, 3/2000000, 1/1000000, 1/200).

Six derivative columns track four raw cap-error coordinates E_i and both reward
parameters. They start as[I|V]. The reward parameters keep their own unit
columns, so all direct parameter dependence remains in the stage chain rule.
A parallel point computation encloses the orbit at the exact rational c,p0.
Every point root tube is checked inside the corresponding full-domain
uniqueness tube; the point and domain computations therefore use the same
implicit branches. After each stage reset its value enclosure to the point
orbit enclosure plus

    sum_j sup|D_Ej U_i| r_j + sum_k sup|D_pk U_i| h_k.

This is an inductive mean-value enclosure on the original convex input box.
The locally Lipschitz seam selector obeys the same bound across its boundary.
At return define

    L_i = sum_j sup|D_Ej F_i| r_j/r_i,
    R_i = sup|F_p0(c)_i-c_i| + sum_k h_k sup|D_pk F_i-V_ik|.

The checker proves L_i+R_i/r_i<1, as well as the stronger global bounds
L_i<7/40 and R_i/r_i<2/5. Hence the return maps every moving fiber into itself
and contracts in its weighted infinity norm. Banach's theorem gives a periodic
cap fixed point for each parameter in the cell.

The complete run certifies exactly the20 closed cells

    [0,10^-5] times[k/1000,(k+1)/1000], k=340,...,359.

Their union is the claimed band, with no sampled-coverage assumption. Run
`python math/experiments/CODEX_COORDINATOR__TWO_ROW_SUPPORT_BAND.py`
from the repository root; it uses the Python standard library only
and reads no external data. The author and an independent reviewer each ran all20 cells successfully.
Do not use `python -O`: acceptance checks are assertions. The stated
bounds are integer-interval assertions, not floating diagnostics.

### Behavioral and uniform conclusion

At the cap fixed point, active owners are indifferent and quiet owners weakly
prefer Continue. These Bellman inequalities cap arbitrary behavioral stopping
deviations. The checker proves q0,q1>3/40000 at every phase on every selected
branch. Therefore each owner's opponents absorb with a uniform geometric tail,
even if that owner never quits. Iterating the Bellman inequalities leaves no
terminal remainder; the same tail bounds finite-horizon average payoff errors
and deviation gains uniformly as the horizon grows. Fixed signed row offsets
add the same amount to every terminal payoff of that owner because every
unilateral deviation absorbs almost surely. This proves the stated UE claim.

## Absorption cannot vanish along periodic Nash profiles

This supporting lemma concerns periodic profiles whose actual continuation
values satisfy Nash endpoint conditions at every phase. It does not produce
such a profile. On the entire closed parameter rectangle

    0<=delta<=38/25,    0<=epsilon<=4141/5000,

every absorbing profile of this kind has total hazard per period
eta=sum_(t,i)q_i^t>=10^-10. Its absorption probability per period is greater
than1/(2*10^10), and after deleting any player it is greater than1/(2*10^13).
The period may be arbitrarily large. These are bounds per period, not per
date. Arbitrary signed original row offsets cancel from the phase endpoint
equations after subtracting them from the actual continuation values.

Here is a general estimate behind the claim. Suppose native own rewards are0
and all native rewards are bounded in absolute value by M. Put s_t=sum_i q_i^t,
a_t=1-product_i(1-q_i^t), and let R_i(q^t) be the unconditional reward in
one round, with0 on survival. For eta>0 define
w_i=sum_t q_i^t/eta. Independence gives

    |a_t-s_t|<=s_t^2/2,
    |R_i(q^t)-sum_j Gamma_ij q_j^t|<=(3M/2)s_t^2.

Actual continuation values have absolute value at most M. Each Bellman step
changes a coordinate by at most2M s_t, so any two phases differ by at most
2M eta. Summing the Bellman equations over the cycle, using
sum_t s_t^2<=eta^2, gives for any reference phase b

    |(Gamma w)_i-b_i|<=4M eta.                            (B)

If eta<1, every positive hazard is proper. At each phase Nash value is at least its
immediate-Quit offer, hence b_i>=-M eta. If w_i>0, the player mixes at some
phase, where value equals its Quit offer; comparison with b gives
|b_i|<=3M eta. Thus

    (Gamma w)_i>=-5M eta,
    |(Gamma w)_i|<=7M eta whenever w_i>0.                 (C)

In particular a zero-eta limit would produce a simplex vector w with
Gamma w>=0 and w_i(Gamma w)_i=0. For this family's delta,epsilon>=0,
Gamma w>=0 and w>=0 nonzero force every coordinate positive: w0=0 forces
w2=w3=0 by row1 and then w1=0 by row2; w1=0 is similar using rows0,3;
w2=0 forces w0=0 by row3; w3=0 forces w1=0 by row2. Such a complementary
vector would therefore satisfy Gamma w=0.

For an explicit bound, the determinant and every adjugate entry of Gamma
are affine in each parameter separately. Exact evaluation at the four
corners of the stated rectangle gives

    66306785663/125000000000 <= det Gamma <= 515204117/500000000,
    21/1250000 <= every adjugate entry <= 475407/250000.

Consequently K=Gamma inverse has 1/100000<K_ij<4. The raw rewards satisfy
M<=6. If 0<eta<10^-10, set z=Gamma w and r=54eta. By(C), z_i>=-r and
|z_i|<=r on the support of w. Since1=sum_(i,j)K_ij z_j,
sum_j max(z_j,0)>=1/16. Therefore

    w_i>1/(100000*16)-16r>0.

All four coordinates are active, so z_i<=r for every i; this contradicts
1=sum_(i,j)K_ij z_j<64r<1. Thus eta>=10^-10. The elementary inequality

    A=1-product_(t,i)(1-q_i^t)>=eta/(1+eta)

gives the asserted absorption bound.

Every own-involving native reward is nonnegative on this rectangle, so every
Nash continuation payoff is nonnegative. For each possible sole quitter j,
some other player i has Gamma_ij<=-7/1000. If p is the terminal probability
of a coalition other than{j}, nonnegative value and the reward bound6 force
p>=7/6007. Let A_-j be the probability of an opponent of j quitting in one
period. Summing survival over periods gives p<=A_-j/A. Hence
A_-j>=7A/6007>1/(2*10^13), as claimed.

The exact corner calculation is reproducible with Python and SymPy:

```python
import sympy as s
from itertools import product
d,e=s.symbols('d e'); R=s.Rational
G=s.Matrix([[0,R(101,100),-R(3,5),-R(9,1000)],
 [R(101,100),0,-R(27,20),-R(1,25)],
 [-R(9,10)*d,-R(3,50),0,R(101,100)],
 [-R(7,1000),-R(9,10)*e,R(101,100),0]])
vertices=[{d:x,e:y} for x,y in product([0,R(38,25)],[0,R(4141,5000)])]
polys=[s.expand(G.det())]+list(G.adjugate())
assert all(s.Poly(p,d,e).degree(d)<=1 and
           s.Poly(p,d,e).degree(e)<=1 for p in polys)
bounds=[(min(p.subs(v) for v in vertices),
         max(p.subs(v) for v in vertices)) for p in polys]
assert bounds[0]==(R(66306785663,125000000000),R(515204117,500000000))
assert min(a for a,b in bounds[1:])==R(21,1250000)
assert max(b for a,b in bounds[1:])==R(475407,250000)
assert R(21,1250000)/bounds[0][1]>R(1,100000)
assert R(475407,250000)/bounds[0][0]<4
r=R(54,10**10)
assert R(1,1600000)-16*r>0 and 64*r<1
assert R(7,6007*2*10**10)>R(1,2*10**13)
print('PASS exact inverse and absorption bounds')
```

For a fixed period the full absorbing Nash system over this parameter
rectangle is compact: the payoff and endpoint equations are closed, values
are bounded, and the uniform absorption bounds prevent an escaping limit
at zero joint or opponent-deleted absorption. Hazards reaching1 remain valid
points of that system. This removes one possible failure of continuation;
it does not determine the total fixed-point index or exclude two branches
meeting and disappearing inside the absorbing region. No new UE region
follows from this helper alone.
