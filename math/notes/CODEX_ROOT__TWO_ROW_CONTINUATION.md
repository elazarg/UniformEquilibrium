# Two-row continuation in the four-player test family

Owner: CODEX_ROOT. The stationary construction is by crossfield_global_algebra;
the periodic constructions are by crossfield_switched_control,
positive_collision_literature, and product_cover_fresh_review.

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
| delta in [0,.002], [.099,.101], or [.98,1.02], every epsilon>=0 | The three periodic rectangles below, combined with the stationary and singleton results; independent full checks |

Consequently any still-uncovered parameter of this family lies in

    delta in (.002,.099) union (.101,.98) union (1.02,1.5),
    0<=epsilon<.737+.06delta,

with the known ray and other established neighborhoods removed. This
is a containing region for the unfinished work, not an exact description of
all parameters without a known equilibrium. It is not a constraint on an
arbitrary Fin4 counterexample. In particular no stationary nonexistence claim
is being made for the remaining region.

The next question is whether actual periodic Nash continuation can cover this
entire lower region, including every support change and parameter boundary.
A contracting cycle at a sample point alone does not answer it. The rectangles
below supply continuous legal selectors on cells where an optional player
may activate. Different calendars can cover each other's weak support seams;
the proof needs overlapping parameter coverage, not one cycle selected across
all cells.

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

## Three periodic regions with changing supports

Use the sixty native rewards already defined above. Every parameter in each
closed rectangle below has an exact equilibrium for terminal absorption payoffs,
and the same periodic profile and its terminal payoff vector give uniform
eta-equilibria for every eta>0. All claims allow arbitrary fixed signed offsets
added to every absorbing reward in each recipient row.

| Region | Exact parameter rectangle | Backward support calendar | Period |
| --- | --- | --- | --- |
| Corner | [0,1/500] x [0,1843/2500] | 013^4, 012^60 | 64 |
| Upper | [49/50,51/50] x [0,81/100] | 013^2, 012^2, 023^12 | 16 |
| Middle | [99/1000,101/1000] x [0,93/125] | 013^2, 012^8, 023^p, p=24 or 28 | at most 38 |

Every listed 012 phase allows owner 3 to enter, producing support 0123.
Physical time reverses the displayed backward calendar. The middle calendar
uses p=28 on epsilon in [3467/5000,1389/2000]; the other initial cells use p=24.
Cell boundaries are included. Different cells may use different equilibria;
their cyclic fixed points need not be identified across parameter cells.

Their upper edges exceed the affine stationary threshold .737+.06delta:
the respective maximum thresholds are .73712, .7982 and .74306. Together
with the stationary producer and singleton obstruction above, these rectangles
therefore cover every epsilon>=0 for delta in the three displayed intervals.

**Verification status.** All three frozen checkers have passed independent
complete runs. These are ordinary mathematical certificates,
not new Lean proofs or a closure of arbitrary Fin4.

### Stage roots on continuation graphs

For independent hazards q, let Q_i be owner i's expected reward from quitting,
P_i the absorbing contribution from nonempty opponent quitting sets when i
continues, and H_i=product_(j!=i)(1-q_j). At continuation cap b put

    g_i(q,b)=Q_i(q)-P_i(q)-H_i(q)b_i.

An active mixed owner satisfies g_i=0; a quiet owner satisfies g_i<=0. The
updated cap is Q_i on active coordinates and Q_i-g_i on quiet coordinates.
All selected active hazards are strictly between zero and one. In particular
the selected native updated caps are nonnegative, since all participant rewards
in this raw family are nonnegative.

Each parameter cell uses the original convex six-dimensional latent box X:
four initial-cap errors u_i with |u_i|<=r_i, and two parameter displacements
of half-widths h_k. Its initial cap is c+V(p-p0)+u. The programs propagate
continuation values, their six derivative columns, and a certified orbit at
the exact centre (u,p-p0)=0.

For an active support S, fix rational qhat and a rational preconditioner C.
The residual rho=Cg_S(qhat,b(x),p(x)) is enclosed both by ordinary interval
evaluation and by its own certified centre value plus
sum_j sup|partial_j rho| times the latent half-widths. Intersecting these
enclosures preserves every residual on the continuation graph. Preconditioning
occurs before absolute values. If a bridge hazard y varies independently, its
whole interval remains in BOTH the centre residual and derivative evaluations;
the estimate is uniform in y, with y held fixed during latent variation.

On a hazard box qhat+[-a,a], the programs enclose M=I-C D_qg_S and verify

    sup|rho_i| + sum_j sup|M_ij| a_j < a_i.

They also check a contraction bound below 9/10, using the a-weighted maximum
norm in the corner/middle programs and the ordinary maximum norm in the upper
program. Banach gives a unique root for every original latent input on the
graph, uniformly in any bridge hazard. Existence for unrelated cap/parameter
combinations in the surrounding rectangular enclosure is not asserted.

The Newton image is intersected with its original uniqueness box. Nonsingularity
of the active Jacobian gives the local implicit derivative
-(D_qg_S)^(-1) D_(b,p)g_S, which is multiplied by the incoming six-column
derivative enclosure. A centre root must lie in its domain uniqueness tube;
the quiet centre root is checked even when only the full mode is selected.
Quiet gaps and updated caps are intersected with their own centre value plus
the six mean-value radii. Thus every anchor refers to the same local root.

### Support seams and the two ways of propagating derivatives

A strictly negative quiet gap selects 012. A strictly positive quiet gap and
positive full hazard select 0123. Otherwise both the quiet root and a signed
full root are certified. A persistent-owner bridge solves the 012 equations
for every optional hazard y between zero and the signed full hazard y*.
Its uniqueness tube contains both endpoint roots. The reduced optional gap has

    d/dy g_3(psi(y),y)
      = D_y g_3 - D_x g_3 (D_x g_012)^(-1) D_y g_012 < 0.

Since this gap vanishes at y*, the quiet gap and y* have the same sign.
Select quiet for nonpositive gap and full for positive gap. At zero they agree
by uniqueness. All other quiet inequalities and physical hazard bounds are
checked. Signed hazards on unused counterfactual extensions are not strategies.

The upper checker propagates ONE locally Lipschitz selected continuation graph.
At a seam it takes interval hulls of the two branch derivatives. Local implicit
charts and the negative-Schur selector justify these derivative bounds almost
everywhere. Their mean-value consequence on convex X follows from the standard
W^(1,infinity) estimate, by mollification in the interior and continuity at the
boundary. This does not integrate an ambient almost-everywhere bound along a
possibly exceptional line. Point/domain root containment identifies its selected
centre orbit at every stage. It has no complete-history compatibility test.

The corner and middle checkers instead retain separate smooth counterfactual
histories on ALL of X, including where a history is not selected. Each keeps
its own point orbit and derivative columns. At each phase, convex-hull tests
||I-C D_qg_S||<1 identify same-support roots from different histories whenever
their incoming caps agree. Every quiet chart is included, even from full-only
histories. At mixed-mode phases the full uniqueness hull also contains the
quiet endpoints with optional hazard zero. These tests need injectivity only;
root existence was already proved on the individual history graphs.

Thus their selected return is a continuous finite selection of smooth returns
F_h. It inherits any common Lipschitz bound: near a point continuity excludes
branches with a different value there, and the remaining branches agree at that
point and obey the bound. Continue along a segment in X. No convexity of the
selected-history regions or finite number of switches is assumed.

### Return contraction

For a smooth history, or the upper selected graph with its derivative hulls, put

    U_hi = sum_j r_j sup|D_uj F_hi|,
    P_hi = sum_k h_k sup|D_pk F_hi - V_ik|.

The corner requires |F_h(0)_i-c_i|+U_hi+P_hi<r_i for every history and row.
The upper program checks the same inequality for its selected centre orbit and
selected derivative enclosures. Both give a strict self-map and cap contraction
on every affine fibre c+V(p-p0)+[-r,r].

The middle program uses a sharper final anchor. It tracks all histories still
possibly selected at the central point: a strictly negative central quiet gap
retains quiet, a strictly positive gap retains full, and an unresolved sign
retains both. Let C_i be the largest |F_h(0)_i-c_i| among these possible central
histories. The exact final tests are

    max_(h,i) U_hi/r_i < 1,
    C_i + max_h(U_hi+P_hi) < r_i  for every i.

Apply finite-selection Lipschitz gluing to F_h-V(p-p0), anchored at the actual
selected centre value, to obtain the self-map bound. Holding parameters fixed
gives cap contraction. This final tightening does not replace any history's
own stage anchors. Banach now supplies cyclic Nash continuation equations for
each parameter in the accepted cell.

### Complete covers and reproduction

The standalone checkers use the Python standard library, outward-rounded
integer intervals with denominator 2^512, and no external candidate data.
Floats only propose rational centres, slopes and inverse matrices; all mathematical
acceptance is by exact interval inequalities. An exact vertex audit verifies the
Horner payoff/gap formulas against the raw table: the polynomials are multiaffine
in hazards and parameters and affine in the cap vector. Hazard/parameter vertices
and the zero plus four cap basis vectors therefore suffice. Do not use python -O.

The corner starts with four strips [n/2000,(n+1)/2000] x [0,1843/2500],
n=0,1,2,3. On rejection it bisects delta when epsilon-width<delta-width/5,
and epsilon otherwise. The upper starts with 81 slabs of full delta width and
epsilon in [j/100,(j+1)/100], j=0,...,80; it bisects delta when delta-width
is at least five times epsilon-width, and epsilon otherwise.

The middle starts with full delta width and epsilon intervals [j/50,(j+1)/50],
j=0,...,33, followed by [.68,.6934], [.6934,.6945], [.6945,.70], [.70,.72],
[.72,.74], [.74,.744]. These decimals are exact rationals. Only [.6934,.6945]
uses p=28. Rejections bisect delta when delta-width is at least twice epsilon-width,
and epsilon otherwise. Both closed children must finish in every program.
Depth, cell, attempt or time limits abort with failure; a partial cover cannot
produce the final success marker. No cross-cell branch agreement is needed.

Run these commands from the repository root. The complete-check counts are:

| Region | Command | Final marker and current status |
| --- | --- | --- |
| Corner | `python math/experiments/CODEX_COORDINATOR__TWO_ROW_CORNER_PERIODIC.py` | `PASS_COMPLETE_CORNER`; independent full run accepts 255 cells and 251 rejected parents |
| Upper | `python math/experiments/CODEX_COORDINATOR__TWO_ROW_UPPER_PERIODIC.py` | `PASS COMPLETE GRAPH BLOCK`; author and independent runs both accept 238 cells, 157 rejected parents, 502 attempts |
| Middle | `python math/experiments/CODEX_COORDINATOR__TWO_ROW_MIDDLE_PERIODIC.py` | `PASS COMPLETE MIDDLE RECTANGLE`; author and independent runs both accept 78 cells, 38 rejected parents, 206 attempts |

Frozen checker SHA256 values, in this order:

    a7ca99c74294ff248292722745e46335b5460a4c0a0df7728bb8792b7e023a70
    3ff4fd8b598cb15078cf6055f8829c479e8dda9be8a43f4d72eb9fc9c557424f
    55af0e0c2d7f8bdf430aeab08af3a8e21c2d2635726f095f49bc2977493fdb83

### Full behavioral and uniform conclusion

At the cyclic fixed point, the stage Nash inequalities make continuation caps
a supermartingale under every unilateral behavioral deviation and a martingale
under prescribed play. Every selected phase retains at least two proper owners
with strictly positive hazards; the corner and middle explicitly bound the
relevant persistent hazards below by 10^-7. Finitely many strict interval checks
give a positive lower bound beta for the upper block as well. After deleting
any one deviator, an opponent retains this bound, so survival past t dates is
at most (1-beta)^t uniformly over all unilateral history-dependent deviations.

For each fixed game, rewards and caps are bounded. Truncation and the geometric
tail therefore remove the terminal remainder in the Bellman inequalities and
identify caps with actual terminal values. The expected preabsorption time is
bounded, so finite-average payoffs approach terminal payoffs uniformly over all
deviations. This proves the stated uniform equilibria with a fixed payoff target.
Absorption remains certain under every deviation; signed recipient offsets
therefore shift that owner's terminal reward by exactly the offset. The same
tail argument proves the finite-horizon conclusion for every fixed choice of
offsets, without claiming a uniform reward bound over unbounded offsets.

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
