# Uniform equilibria on the entire two-crossing parameter family

This is ordinary mathematics with exact finite computational certificates.
It is not a new Lean theorem. Arbitrary four-player quitting games remain open.

## Exact statement and game model

There are four players I={0,1,2,3}. At each live date they simultaneously choose
Continue or Quit, using independent private randomization. The first nonempty
quitting coalition S absorbs the game and gives every player i the constant
payoff r_i(S) thereafter. Live play and a path that never absorbs give zero.
Actions and the absorbing coalition are publicly observed. A unilateral
behavioral replacement may depend on the complete observed history and all
of the deviator's private randomization; no public correlation is supplied.

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
restriction on these offsets. On the constructive regions below, the produced
profile is independent of them.

**Theorem.** For every delta,epsilon>=0 and every four finite real offsets
c_i, the game just defined has a uniform-equilibrium payoff. Explicitly, there
is one vector v such that for every eta>0 there are a behavioral profile sigma
and N0 with, for every N>=N0, the expected N-date average payoff of sigma
within eta of v coordinatewise, and every unilateral behavioral replacement
improving its owner's N-date payoff by at most eta. The target v is fixed
before eta; the profile and horizon bound may depend on eta.

On every periodic or stationary region explicitly constructed below, the
same profile works for all accuracies and is exact Nash for terminal
absorption payoffs. The large-epsilon contradiction supplies UE existence;
it does not assert an exact terminal profile or a period bound there.

## Conjecture-facing change and strategic inputs

The complete quadrant of this explicit raw family is ruled out as a source
of Fin4 counterexamples. In particular the point(delta,epsilon)=(1/8,139/200)
is covered despite a positive terminal exploitability gap over every
stationary profile when at least one own-singleton offset is positive; the
complete exclusion proof is given below. Thus producing this point requires
more than any choice within an exact or asymptotically exact stationary
producer. This does not assert that every nonstationary architecture fails.

No strategy, cap, hazard, phase word, root, preconditioner or continuation
selector is an assumption of the theorem. The finite algorithms construct
and verify these objects from the two parameters on compact regions. The
high-delta region uses a compact fixed-point producer, and large epsilon
uses the existing bare-no-UE singleton consequence. Supplied-object endpoint
and periodic consumers alone do not produce these raw-data witnesses.

## Source correspondence

`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`
says that absence of a UE payoff for any Fin4 reward table produces a
nonnegative weight vector of sum one whose image under the actual projective
singleton matrix is strictly positive in every coordinate. No own-reward-sign,
normality, invertibility or strategy-certificate hypothesis is required.
`quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` subtracts each
recipient's own singleton, so it is precisely Gamma=A+J here.

`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` consumes
an actual stationary fixed point, endpoint Nash inequalities and strict
opponent-deletion absorption. These are supplied below, not assumed.
The general semantic equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
likewise consumes terminal approximate Nash profiles at every positive error.
The proof below gives the stronger fixed-profile uniform conclusion in its
constructive regions directly. The new mathematical content is the explicit
raw-data production and complete coverage; no new checked Lean implementation
is asserted.

## Proof: large epsilon

For the raw table in the statement the projective singleton matrix is Gamma=A+J;
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
The definition `quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` gives Gamma directly.

## Proof: the high-delta half-plane

### A strict lower-face certificate

Write W=Z^(delta,epsilon) for the native table and s_i=c_i for its row offsets.
For independent hazards q in[0,1]^4, let

    H_i=product_{j!=i}(1-q_j),
    P_i=E[W_i(T)], Q_i=E[W_i(T union {i})],
    F_i=(1-H_i)Q_i-P_i,

where T is the random coalition of opponents and W_i(empty)=0. Each F_i is
continuous and independent of q_i. Endpoint complementarity means

    q_i=0 => F_i<=0; 0<q_i<1 => F_i=0; q_i=1 => F_i>=0.       (1)

Put B=Z^(8/5,0). The exact certificate proves:

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

For W=Z^(delta,epsilon) with delta>=8/5, raw domination gives F_2^W>=F_2^B at every q: every
participant reward has coefficient (1-H_2)Pr(T)>=0 and every passive reward
has coefficient -Pr(T)<=0. Rows0 and1 are unchanged. Thus (2) also holds for
W, regardless of its fourth row.

### The compact fixed-point producer

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

### Actual payoffs and signed offsets

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
data are assumptions of the theorem. The consumers are in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`; this raw
producer and its finite certificate have not yet been formalized in Lean.

### The strip from3/2 to8/5

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
hazards are proper, so every opponent-deleted profile absorbs. The preceding behavioral and uniform argument
therefore applies, including arbitrary signed offsets. This overlaps the
global producer at delta=8/5 and closes the entire unbounded half-plane.

Only the producer and strip calculations are needed here. They are included
in `dominated.py`, which uses SymPy and exact integer/rational arithmetic.

## Proof: the affine stationary region

**Affine stationary lemma.** For every delta in [0,38/25] and

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

The complete exact calculation accepts9644 main rectangles and760 refined
left-endpoint rectangles. Run `python affine.py`; successful completion prints
`PASS_ALL`. Its floated diagnostics do not replace the exact comparisons above.
The code requires SymPy, NumPy and SciPy; candidates depend on numerical
library versions but only exact interval acceptance proves a cell.

## Periodic regions with changing supports

Use the sixty native rewards defined in the statement. Every parameter in each
closed parameter region below has an exact equilibrium for terminal absorption payoffs,
and the same periodic profile and its terminal payoff vector give uniform
eta-equilibria for every eta>0. All claims allow arbitrary fixed signed offsets
added to every absorbing reward in each recipient row.

| Region | Exact parameter region | Backward support calendar | Period |
| --- | --- | --- | --- |
| Corner | [0,1/500] x [0,1843/2500] | 013^4, 012^60 | 64 |
| Upper | delta in [7/10,6/5], 0<=epsilon<=737/1000+3delta/50+1/2000 | 013^2, 012^2, 023^12 | 16 |
| Middle | delta in [3/25,7/10], 0<=epsilon<=369/500+3delta/50 | 013^h, 012^n, 023^p, h in {1,2,3}, with (n,p) below | at most 33 |
| Low | delta in [1/500,3/25], 0<=epsilon<=737/1000+3delta/50+1/10000 | 013^h, 012^n, 023^p, with the finite portfolios below | at most 64 |
| High | delta in [6/5,3/2], 0<=epsilon<=737/1000+3delta/50+1/10000 | 013^2, 012^n, 023^p, n in {1,2}, p in {8,...,14} | at most 18 |

Every listed 012 phase allows owner 3 to enter, producing support 0123.
Physical time reverses the displayed backward calendar. Middle uses these six
parameter bands, with h chosen from {1,2,3} separately for each accepted cell:

| Closed delta band | (n,p) |
| --- | --- |
| [3/25,17/100] | (6,24) |
| [17/100,1/4] | (5,24) |
| [1/4,17/50] | (5,20) |
| [17/50,23/50] | (4,16) |
| [23/50,16/25] | (3,16) |
| [16/25,7/10] | (2,14) |

At a shared band endpoint either neighboring calendar family may be used.
Cell boundaries are included. Different cells may use different equilibria;
their cyclic fixed points need not be identified across parameter cells.

The corner upper edge exceeds the maximum affine stationary threshold .73712
on its delta interval. Low, middle, upper and high exceed that threshold by at least
1/10000, 1/1000, 1/2000 and 1/10000, respectively. Together with the stationary producer
and large-epsilon obstruction, they cover every epsilon>=0 on each displayed
delta interval. The corner, low, middle, upper, high and dominated-row intervals join to
cover every delta>=0, epsilon>=0. This whole-family conclusion is UE existence;
the singleton argument does not construct an exact terminal Nash profile or
a globally bounded-period producer.

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
norm in the corner/low/middle/high programs and the ordinary maximum norm in the upper
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

The low, middle, upper and high checkers permit signed persistent hazards
in the unused quiet chart
when its optional gap is strictly positive throughout the input graph and all
four full-root hazards are proper. The selected root is then full everywhere.
Quiet point containment remains mandatory. The checkers using complete
histories also retain every common-link uniqueness test.
Mixed-mode graphs retain both physical persistent charts and all bridge,
endpoint and negative-Schur checks. Only the unused extension is relaxed.

The upper checker propagates ONE locally Lipschitz selected continuation graph.
At a seam it takes interval hulls of the two branch derivatives. Local implicit
charts and the negative-Schur selector justify these derivative bounds almost
everywhere. Their mean-value consequence on convex X follows from the standard
W^(1,infinity) estimate, by mollification in the interior and continuity at the
boundary. This does not integrate an ambient almost-everywhere bound along a
possibly exceptional line. Point/domain root containment identifies its selected
centre orbit at every stage. It has no complete-history compatibility test.

The corner, low, middle and high checkers instead retain separate smooth counterfactual
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

The low, middle and high programs use a sharper final anchor. They track all histories still
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
and the zero plus four cap basis vectors therefore suffice. Low, middle and high
also compare every explicit hazard-Jacobian entry with exact raw-gap finite
differences on that grid. Multiaffinity proves these derivative identities;
Low and middle use private
floating polynomial evaluators, calendar ranking and coordinate-radius adjustments to
choose rational proposals; the exact evaluators and acceptance tests are
unchanged by these accelerations. Do not use python -O.

The corner starts with four strips [n/2000,(n+1)/2000] x [0,1843/2500],
n=0,1,2,3. On rejection it bisects delta when epsilon-width<delta-width/5,
and epsilon otherwise. The upper starts with 25 closed delta slabs
[j/50,(j+1)/50], j=35,...,59. Each has epsilon ceiling
737/1000+(3/50)(j+1)/50+1/2000, partitioned into intervals of width at most
1/100 with the final interval clipped exactly at the ceiling. These are
2000 initial rectangles. It bisects delta when delta-width is at least five
times epsilon-width, and epsilon otherwise.

Middle uses 58 closed delta slabs [j/100,(j+1)/100], j=12,...,69, with
ceiling 369/500+(3/50)(j+1)/100. The first four delta slabs use epsilon
intervals of width 1/100. On the remaining slabs, epsilon widths are 1/25 below
8/25, 1/50 from 8/25 through 3/5, and 1/100 above 3/5, with the last interval
clipped at the exact ceiling. The steps divide both scheduling boundaries
exactly. This gives 300 initial rectangles in the prefix and 2099 in the suffix.
At each cell, numerical active-Jacobian inverse norms and selected physical
margins rank the three h choices. Proposed rational coordinate radii may be
enlarged after a failed return test; every new proposal receives a fresh exact
verification. Rejections bisect delta when its width is at least twice the
epsilon width, and epsilon otherwise.

The completed middle cover has3433 accepted cells and1034 rejected
parents. Its2399 initial rectangles are the300 prefix rectangles and2099
suffix rectangles described above. The exact local tests and recursion in
`middle.py` produce both parts.

Both closed children must finish in every program. Depth, cell, attempt or
time limits abort with failure; a partial cover cannot produce a whole-region
success marker. No cross-cell branch agreement is needed.

The high starts with 30 closed delta tiles of width 1/100 from 6/5 to 3/2.
Each has ceiling 737/1000+(3/50)delta_right+1/10000. Its epsilon intervals
have width 1/50 below 7/25 and 1/100 above it, ending at that exact ceiling:
2051 initial rectangles in total. At each cell it numerically ranks the finite
calendar portfolio and tries its best three candidates, then uses the middle
bisection rule on rejection. All acceptance remains exact; ranking can only
omit candidates. Both children must complete and failure cannot issue success.

The complete covers have these exact subdivision sizes:

| Region | Initial rectangles | Accepted cells | Rejected parents |
| --- | ---: | ---: | ---: |
| Corner |4|255|251|
| Low |481|5364|4883|
| Middle |2399|3433|1034|
| Upper |2000|2764|764|
| High |2051|2249|198|

Each row satisfies accepted cells minus rejected parents equals initial
rectangles. This count identity supplements the closed subdivision induction;
it is not a substitute for any local interval inequality.

### Low delta: finite calendars and the closed range union

This part targets

    1/500 <= delta <= 3/25,
    0 <= epsilon <= 737/1000+(3/50)delta+1/10000.

The exact closed cover has5364 accepted leaves and4883 rejected parents,
so the481 initial rectangles are completely discharged.

The backward calendar is `013^h,012^n,023^p`; physical time reverses this
order. Every012 phase allows optional owner3 through the common checked
selector. The initial closed delta bands and primary `(n,p)` are exactly:

| Band | Lower delta | Upper delta | n | p |
| --- | --- | --- | --- | --- |
| 0 | 2/25 | 3/25 | 8 | 24 |
| 1 | 29/500 | 2/25 | 9 | 24 |
| 2 | 1/25 | 29/500 | 12 | 24 |
| 3 | 4/125 | 1/25 | 13 | 24 |
| 4 | 3/125 | 4/125 | 16 | 24 |
| 5 | 2/125 | 3/125 | 19 | 16 |
| 6 | 21/2000 | 2/125 | 21 | 16 |
| 7 | 1/125 | 21/2000 | 27 | 12 |
| 8 | 3/500 | 1/125 | 30 | 12 |
| 9 | 3/625 | 3/500 | 34 | 8 |
| 10 | 1/250 | 3/625 | 39 | 8 |
| 11 | 2/625 | 1/250 | 42 | 8 |
| 12 | 1/500 | 2/625 | 48 | 8 |

The canonical Low checker has two proposal modes; both use h=1,2,3,4.
Baseline mode (`--baseline-proposals`) retains the original executed ranker:
first score the four primary words, then, only when

    du-dl < dc/20 and eu-el < 1/250,    dc=(dl+du)/2,

score the neighbors `(n-1,p),(n+1,p),(n,p+4)` in that order for each h.
Default V4 mode scores only the primary words when `ec=(el+eu)/2<3/5`.
At `ec>=3/5`, for each h it instead scores the seven separate families

    (n-2,p),(n-1,p),(n,p),(n+1,p),(n+2,p),(n,p-4),(n,p+4),

skipping n<1 or p<0. These are separate neighbors, not a Cartesian
expansion. The same caught scoring failures, reverse `(score,word)` sorting,
and up-to-four ranked calendar attempts are retained. Both modes have the
uniform period bound64, including the baseline mode used for band0.
Mode selection changes only the ranker. Floating helpers, rational center
and slope conversion, radius proposals/retries, the cache, and every exact
acceptance condition are shared unchanged. A numerical score never accepts
a parameter cell.

For a band `[dl,du]`, initial epsilon edges are `j/50`, j=0,...,36, followed
by `737/1000+(3/50)du+1/10000`. Thus there are37 closed initial rectangles
per band and481 overall. This right-edge ceiling dominates the target
sloped ceiling throughout its band. Rejection splits delta when
`du-dl>=2dc(eu-el)` and epsilon otherwise; both closed children must finish.
Finite induction on completed subdivisions proves each claimed rectangle.
The closed adjacent delta bands then cover the desired delta interval.

Apply the common periodic continuation proof unchanged: outward-rounded
exact intervals, the raw-table/Jacobian identities, graph roots and their
implicit derivatives, point/domain anchors, mixed-support bridges and Schur
tests, complete-history uniqueness links, the selected-center return anchor,
and final contraction/self-map tests. Low uses the strict-full rule already
specified for High; it introduces no further acceptance relaxation. The
Low checker's persistent-hazard lower bound10^-7 gives geometric absorption even
after any unilateral behavioral deviation. The same Bellman and finite-
average argument therefore supplies one fixed uniform payoff target for
each accepted parameter pair and permits arbitrary fixed signed row offsets.

The thirteen closed bands join at every endpoint and cover[1/500,3/25].
The completed subdivisions discharge all37 initial epsilon rectangles in each
band. Different cells may select different equilibria at a shared boundary.
The upper ceiling of band12 is184323/250000; its last two epsilon rectangles
are[7/10,18/25] and[18/25,184323/250000], so the narrow final strip is included.

The canonical checker supports single-band and closed band-index ranges.
The reproduction commands below split the work to stay inside its resource
budgets. A calendar attempt may contain up to four exact radius trials;
calendar-attempt totals are not counts of verifier calls. Resource exhaustion
aborts and never certifies a partial region.

### Full behavioral and uniform conclusion

At the cyclic fixed point, the stage Nash inequalities make continuation caps
a supermartingale under every unilateral behavioral deviation and a martingale
under prescribed play. Every selected phase retains at least two proper owners
with strictly positive hazards; the corner, low, middle and high explicitly bound the
relevant persistent hazards below by 10^-7. For upper, a strictly positive
integer lower endpoint is at least 2^-512, so beta=2^-512 works uniformly
without retaining floating minimum diagnostics. After deleting
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


## Complete coverage and positive boundary tests

Let L(delta)=737/1000+3delta/50. For0<=delta<=3/2, the five closed periodic
regions cover0<=epsilon<=L(delta), with positive overlap above their required
upper frontier. The affine stationary region coversL(delta)<=epsilon<=2
because3/2<38/25. The large-epsilon argument coversepsilon>=10201/5400,
and10201/5400<2, so these two upper regions overlap. Finallydelta>=3/2
is entirely covered by the high-delta producer. The shared boundariesdelta
=1/500,3/25,7/10,6/5,3/2 are closed and occur in both adjacent regions.
No unhandled axis, seam, infinite-parameter limit, or equality case remains.

Atdelta=0,epsilon=0, the Corner construction applies, including its axis.
Atdelta=3/2 the periodic/high-delta constructions meet. At the affine upper
join,epsilon=2 lies inside the stationary certificate and above10201/5400.
The strict overlap margins are1/10000 or larger on Low/Middle/Upper/High;
Corner reaches.7372, above maxL=.73712 on its whole delta interval.
All these checks concern exact rational endpoints.

## Boundary test: a positive gap for all stationary profiles

Fix the native table specified above at delta=1/8, epsilon=139/200.
Let original absorbing rewards be r_i(S)=s_i+Z_i(S), with arbitrary fixed
signed s_i, live/Never payoff zero, and at least one s_i>0. This game has
a strictly positive lower bound on terminal exploitability over ALL
stationary profiles. In particular it has neither an exact stationary
terminal Nash equilibrium nor stationary terminal approximate Nash profiles
at every positive accuracy. This is an ordinary mathematical exclusion,
not a Lean theorem or a counterexample to uniform-equilibrium existence.
It does not exclude periodic strategies or a punishment construction using
a different continuation.

### Necessary stationary conditions

For a stationary hazard vector q, put a=1-product_i(1-q_i). If q is nonzero,
the prescribed profile absorbs almost surely, and its native payoff is

    u_i=[q_i Q_i+(1-q_i)P_i]/a.

The original payoff is s_i+u_i. Each deviation at just the first date followed
by the prescribed stationary strategy also absorbs almost surely. Thus the
signed offsets cancel from its comparison. The forced Quit-minus-Continue
gap is

    g_i=Q_i-P_i-H_i u_i=F_i/a,
    F_i=(1-H_i)Q_i-P_i.

Exact Nash therefore requires F_i<=0 at q_i=0, F_i=0 at 0<q_i<1,
and F_i>=0 at q_i=1. These are necessary conditions even if a more general
deviation can improve. The zero vector is not Nash: a player with s_i>0
can quit alone immediately instead of receiving the Never payoff zero.

### A punctured neighborhood of zero is impossible

Let t=sum_i q_i. All native rewards have absolute value at most6, own
singleton rewards are zero, and the singleton matrix is

    Gamma=[0,101/100,-3/5,-9/1000;
           101/100,0,-27/20,-1/25;
           -9/80,-3/50,0,101/100;
           -7/1000,-1251/2000,101/100,0].

Exact rational inversion verifies that K=Gamma^-1 has every entry>1/125
and every row and column sum<5. Write

    F=-Gamma q+E.

For each i, |Q_i|<=6t and 1-H_i<=t. The difference between a singleton
opponent's exact probability and q_j is at most q_j sum_(k!=i,j)q_k.
The probability of at least two quitting opponents is at most
sum_(j<k,j,k!=i)q_j q_k<=t^2/2. Consequently

    |P_i-(Gamma q)_i|<=9t^2,    |E_i|<=15t^2.

Suppose 0<t<1/50000 and the stationary conditions hold. All q_i<1, so
f=-F>=0 and q_i f_i=0. The identity q=Kf+KE holds. If f is nonzero,
choose an index i with f_i>0, hence q_i=0. Positivity of K and its row
bound give

    ||f||_1/125 <= (Kf)_i = -(KE)_i <=75t^2.

The same resulting inequality ||f||_1<=9375t^2 holds when f=0.
Using the column bound on K and ||E||_1<=60t^2 now gives

    t<=5||f||_1+300t^2<=47175t^2,

contradicting 0<t<1/50000. No limiting-root assumption is used.

### Exact exclusion on the remaining cube

The checker starts with all 3^4 status vectors. Status0 fixes q_i=0,
status1 fixes q_i=1, and status2 allows q_i in the closed interval[0,1]
while imposing the necessary equality F_i=0 for a proper mixed owner.
Using closed boxes overcovers each proper-support stratum and preserves
every boundary. Each box is discharged in one of three ways:

1. Its maximum sum of hazards is strictly below1/50000; use the preceding
   argument for nonzero hazards, and the positive-own-singleton test at zero.
2. An outward interval for some F_i violates the required sign or equality.
3. An exact interval Newton image excludes a simultaneous zero of the
   status2 equations.

For the third test, fix the endpoint coordinates, let x denote the free
coordinates, and let x0 be their exact box center. The code encloses the
Jacobian J of the selected F coordinates throughout the box by automatic
differentiation of the audited polynomial. Any rational matrix C is allowed.
Every zero x in the box must lie in

    x0-C F(x0)+(I-C J(box))(box-x0).

This follows from the mean-value integral on the convex box. A coordinate
of this outward enclosure disjoint from its box interval proves that there
is no zero. A floating inverse only proposes C, which is converted to exact
rationals; no inverse accuracy, nonsingularity, or floating sign test is
needed for soundness. Failure to obtain a proposal merely omits this test.

If none of the three tests succeeds, the longest free interval is replaced
by both closed midpoint children. Every initial status box must finish.
Time and node budgets abort with failure; success is printed only after
the stack is empty. The leaf-minus-split identity must equal81. No raw leaf
payload is needed to reproduce the certificate.

The standalone checker imports the hash-pinned high periodic
checker only for its audited raw polynomials, exact interval arithmetic,
automatic derivatives and numerical inverse proposal. It reruns the exact
raw/Horner/Jacobian identity audit and independently verifies the rational
origin constants before the cube cover. It uses the Python standard library
and must be run without optimization flags that disable assertions.

The complete run visited12199 boxes:2757 sign exclusions,3367 Newton
exclusions,16 origin boxes and6059 splits. Thus2757+3367+16-6059=81.
Run `python stationary.py` beside the emitted `high.py` to reproduce this
calculation. The latter supplies its hash-pinned interval and raw-polynomial
kernel; both complete files are contained in the appendix.

No partial execution establishes the exclusion.

### A positive gap for every stationary profile

The exclusion also rules out stationary approximation at arbitrarily small
terminal Nash error, even though terminal values are discontinuous at q=0.
Fix the four signed offsets and suppose, for contradiction, that stationary
profiles q^n have terminal exploitability at most eta_n, with eta_n tending
to zero. Compactness gives a subsequence converging to q*. If q* is nonzero,
the prescribed payoff and the one-date deviation comparisons above are
continuous near q*. Their limiting endpoint Nash conditions contradict the
exact cube exclusion. Hence q*=0.

The zero profile itself has exploitability at least max_i s_i>0, so we may
assume all q^n are nonzero. Set t_n=sum_i q_i^n and, after another subsequence,
q^n/t_n tending to v>=0 with sum_i v_i=1. Since a(q^n)=t_n+O(t_n^2),
P_i(q^n)=(Gamma q^n)_i+O(t_n^2), and Q_i(q^n)=O(t_n), the native prescribed
payoff u_i(q^n) tends to y_i=(Gamma v)_i. Immediate Quit has native payoff
Q_i(q^n) tending to zero. The approximate Nash inequalities therefore give
y>=0. Invertibility implies y is nonzero; K>0 then gives v=Ky>0 in every
coordinate. In particular 0<v_i<1 for every i.

Now let i deviate to Never. For all sufficiently large n, at least one
opponent has positive hazard, so this deviation absorbs almost surely and
its original payoff is

    s_i + P_i(q^n)/(1-H_i(q^n)).

Its native part tends to y_i/(1-v_i). Approximate Nash consequently gives

    y_i >= y_i/(1-v_i).

Together with y_i>=0 and 0<v_i<1 this forces y_i=0 for every i, a
contradiction. Therefore the infimum of terminal exploitability over
stationary profiles is strictly positive for each fixed offset choice.
No uniform constant over unbounded offsets is claimed.

This also prevents stationary profiles from realizing uniform equilibria
at arbitrarily small errors: for any fixed stationary profile and any fixed
behavioral deviation, bounded finite-average payoffs converge to their
terminal/Never payoffs as the horizon tends to infinity. Thus uniform
finite-horizon Nash inequalities for that profile imply the corresponding
terminal approximate Nash inequalities. The argument is about stationary
profiles, not arbitrary behavioral profiles.

### Scope of the producer comparison

For each fixed offset choice with at least one s_i>0, every theorem that
produces exact stationary terminal Nash or stationary terminal approximations
at every accuracy fails to apply at this fixture,
regardless of its existential choices or an unspecified large-reward threshold. This includes stationary constructions
with arbitrary recipient/coalition choices; it is stronger than testing one
selected root or comparing stated parameter ranges. It does not exclude a
producer whose approximate profiles are nonstationary, a periodic producer,
or a punishment-tail equilibrium. Those require their own comparisons.

## Boundary test: a common obstruction to adaptive nonnegative ledgers

At the same fixture with offsets one, let a be any nonnegative vector with
sum_i a_i=1 and a^T Gamma>=0. For a nonempty proper coalition B define

    J_a(B)=sum_(i outside B) a_i[Z_i(B union {i})-Z_i(B)],
    f_a(z)=sum_(nonempty B proper) (product_(j in B)z_j)J_a(B).

There is one strictly positive odds vector z for which f_a(z)>0 for EVERY
such a. Thus even adaptive selection among all admissible nonnegative ledgers
cannot enforce f_a(z)<=0 throughout the positive odds orthant. This is an
exact obstruction to that stated sufficient criterion, not to arbitrary
nonstationary equilibrium constructions.

Use the matrix Gamma displayed in the stationary test and K=Gamma^-1. Its
positive entries and row sums less than5 were established there. Put
h^T=a^T Gamma>=0. Then a^T=h^T K, so

    1=h^T K1<5 ||h||_1.

Exact multiplication verifies Gamma rho=-A[:,2], where

    rho=(75679478400,87911025000,44769477730,13652082000)
                        /10300929979.

Every entry of rho is greater than one, and rho=-K A[:,2]. Hence

    J_a({2})=-a^T A[:,2]=h^T rho>||h||_1>1/5.

Take z=(eta,eta,1,eta), eta=1/200. Each singleton joining coefficient has
absolute value at most6, and each pair or triple joining coefficient has
absolute value at most1, directly from the raw table and sum_i a_i=1.
Every term other than singleton2 therefore has total absolute value at most

    18eta+3eta+6eta^2+eta^3<1/5.

It follows that f_a(z)>0 simultaneously for all admissible a. Nonzero
unscaled a reduce to this normalization; permutations or positive recipient
scalings merely relabel or rescale the effective weights. The argument
therefore excludes the entire weight-selection set of this criterion, not
only one numerical choice.

## Complete exact checkers

Save the Python block below as `bundle.py` and run `python bundle.py checkers`.
It contains all source code and finite input constants, with shared readable
source fragments stored once. It reconstructs eight complete Python files;
the extraction hashes guarantee literal reconstruction, not mathematical
correctness. Mathematical correctness is the interval, polynomial and
subdivision argument above. No external candidate, saved cell, run log or
conference file is read.

Use a working directory containing the emitted files. Never use `python -O`.
The five periodic checkers and stationary exclusion use the standard library.
The affine checker also requires SymPy, NumPy and SciPy; the dominated-row
checker requires SymPy. Their floating operations only propose exact rational
candidates. Every acceptance or exclusion is an exact algebraic or outward
interval inequality. Only a completed cover establishes the corresponding
region; failed proposals and resource-limited executions establish no whole
region claim.

Run `python dominated.py`, `python affine.py`, `python corner.py`,
`python upper.py`, `python middle.py`, `python high.py`, and
`python stationary.py`. The Low commands are:

    PYTHON low.py --baseline-proposals --band 0
    PYTHON low.py --band 1
    PYTHON low.py --start-band 2 --end-band 3
    PYTHON low.py --start-band 4 --end-band 5
    PYTHON low.py --band 6
    PYTHON low.py --start-band 7 --end-band 10
    PYTHON low.py --start-band 11 --end-band 12

For the recorded Low subdivision counts, PYTHON is CPython3.12.14 on the
first two commands and PyPy8.0.1(Python3.12.15) on the last five. Mathematical
acceptance is interpreter-independent; floating proposals and subdivision
counts can vary. The default all-band Low command may exhaust its20000
calendar-attempt limit; the split commands state the reproducible cover.

```python
"""Self-contained exact checkers for the two-parameter quitting family.
Save as bundle.py; run python bundle.py DIRECTORY to extract eight checkers.
Shared source fragments are stored once, as readable Python text. Concatenation
reconstructs each complete checker. No mathematical code is generated or rewritten.
The extractor does not execute a certificate. Run the emitted checkers as stated.
"""
from pathlib import Path
import hashlib
import sys

BLOCKS = {
0: r'''"""Exact closed corner in the two-row complex-spectrum quitting family.
0 <= delta <=1/500, 0 <= epsilon <=1843/2500. Standard library only.
Complete smooth histories, graph-aware Newton residuals, and convex-hull
uniqueness certify the continuous Nash selector through support changes.
Floats propose data; every acceptance is exact outward interval arithmetic.
Run ordinary Python, never python -O (checks use assertions).
"""
''',
1: r'''from fractions import Fraction as F
''',
2: r'''from itertools import combinations
from math import isqrt
''',
3: r'''import time
''',
4: r'''BITS=512;D=1<<BITS
''',
5: r'''class Iv:
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
''',
6: r'''class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*6 if d is None else d
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
''',
7: r'''def jet(x):return x if isinstance(x,Jet)else Jet(x)
''',
8: r'''
''',
9: r'''A=[[F(x)for x in row]for row in[[0,1,-6,'-.01'],[1,0,'-1.5','-.4'],[0,'-.6',0,1],['-.07','-.04',1,0]]]
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
''',
10: r'''

''',
11: r'''I=range(4);N=6
''',
12: r'''def float_inverse(a):
 n=len(a);v=[list(row)+[float(i==j)for j in range(n)]for i,row in enumerate(a)]
 for k in range(n):
  j=max(range(k,n),key=lambda j:abs(v[j][k]));v[k],v[j]=v[j],v[k]
  piv=v[k][k];assert abs(piv)>1e-16;v[k]=[x/piv for x in v[k]]
  for i in range(n):
   if i!=k:
    fac=v[i][k];v[i]=[x-fac*y for x,y in zip(v[i],v[k])]
 return[row[n:]for row in v]
''',
13: r'''def float_gap_jac(q,b,d,e):
 g=gaps(q,b,d,e);A=[]
 for j in I:
  q0=q[:];q1=q[:];q0[j]=0.;q1[j]=1.
  v0=gaps(q0,b,d,e);v1=gaps(q1,b,d,e)
  A.append([y-x for x,y in zip(v0,v1)])
 return g,list(map(list,zip(*A)))
''',
14: r'''def float_newton(S,q,b,d,e):
 q=q[:]
 for _ in range(12):
  g,A=float_gap_jac(q,b,d,e);C=float_inverse([[A[i][j]for j in S]for i in S])
  err=mv(C,[g[i]for i in S])
  for i,x in zip(S,err):q[i]-=x
  if max(abs(x)for x in err)<1e-14:break
 assert max(abs(gaps(q,b,d,e)[i])for i in S)<1e-10
 return q,C
''',
15: r'''def float_triple(b,S,d,e):
 i,j,k=S;aa=[[float(x)for x in row]for row in A];aa[2][0]=-d;aa[3][1]=-e;z=rewards(d,e)
 def cf(a,u,v):
  dd=float(z[a,(1<<a)|(1<<u)|(1<<v)]-z[a,(1<<u)|(1<<v)])
  return-b[a],b[a]-aa[a][u],b[a]-aa[a][v],dd+aa[a][u]+aa[a][v]-b[a]
 ci,ai,bi,di=cf(i,j,k);cj,aj,bj,dj=cf(j,i,k);ck,ak,bk,dk=cf(k,i,j)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 def mul2(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
 terms=[mul2(dx,dy),mul2(nx,dy),mul2(ny,dx),mul2(nx,ny)]
 cc=[sum(t[l]*x for t,x in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 from math import sqrt
 zz=(-cc[1]+sqrt(cc[1]*cc[1]-4*cc[2]*cc[0]))/(2*cc[2]);q=[0.]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 return q
''',
16: r'''def float_center(d,e,c=None):
 c=[.0041188900253007926,.0001243482175163462,.000041907755608047286,.36900861598844355]if c is None else c[:]
 for _ in range(8):
  seeds=[]
  for t in range(64):
   S=[0,1,3]if t<4 else[0,1,2];q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
   if t>=4 and g[3]>0:
    q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
   c=[Q[i]if i in S else Q[i]-g[i]for i in I];seeds.append(q)
 return c,seeds
''',
17: r'''mid=lambda x:F(x.lo+x.hi,2*D)
mag=lambda x:F(x.absupper(),D)
''',
18: r'''def hull(a,b):return Iv(min(a.lo,b.lo),max(a.hi,b.hi),True)
def around(a,r):return Iv(a.lo-Iv(r).hi,a.hi+Iv(r).hi,True)
def mm(a,b):return[[sum(x*y for x,y in zip(row,col))for col in zip(*b)]for row in a]
def mv(a,b):return[sum(x*y for x,y in zip(row,b))for row in a]
def eye(n):return[[Iv(int(i==j))for j in range(n)]for i in range(n)]
def inv_pre(a,c):
 n=len(a);v=[r+s for r,s in zip(mm(c,a),[[Iv(x)for x in r]for r in c])]
 for k in range(n):
  piv=v[k][k];assert piv.lo>0;v[k]=[x/piv for x in v[k]]
  for i in range(n):
   if i!=k:
    fac=v[i][k];v[i]=[x-fac*y for x,y in zip(v[i],v[k])]
 return[r[n:]for r in v]
''',
19: r'''def rewards(delta,eps):
 z=dict(Z);z[2,1]=-F(9,10)*delta;z[2,5]=delta/10;z[3,2]=-F(9,10)*eps;z[3,10]=eps/10
 return z
''',
20: r'''def raw_evaluate(q,b,delta,eps):
 z=rewards(delta,eps);pp=[];qq=[];hh=[];gg=[]
 for i in I:
  opp=[j for j in I if j!=i];P=0;Q=0;H=1
  for j in opp:H*=1-q[j]
  for mask0 in range(8):
   mask=0;w=1
   for k,j in enumerate(opp):
    if mask0>>k&1:mask|=1<<j;w*=q[j]
    else:w*=1-q[j]
   if mask:P+=w*z[i,mask]
   Q+=w*z[i,mask|(1<<i)]
  pp.append(P);qq.append(Q);hh.append(H);gg.append(Q-P-H*b[i])
 return pp,qq,hh,gg
''',
21: r'''C_193_100=F(193,100)
''',
22: r'''C_1_10=F(1,10)
''',
23: r'''C_1_100=F(1,100)
''',
24: r'''C_1_1000=F(1,1000)
C_23_50=F(23,50)
C_27_5=F(27,5)
C_27_50=F(27,50)
''',
25: r'''C_2_5=F(2,5)
C_3_2=F(3,2)
''',
26: r'''C_3_20=F(3,20)
''',
27: r'''C_3_5=F(3,5)
''',
28: r'''C_4411_1000=F(4411,1000)
C_49_100=F(49,100)
''',
29: r'''C_501_100=F(501,100)
''',
30: r'''C_63_100=F(63,100)
C_63_1000=F(63,1000)
''',
31: r'''C_7_100=F(7,100)
C_7_5=F(7,5)
C_8_5=F(8,5)
''',
32: r'''C_927_1000=F(927,1000)
C_9_20=F(9,20)
C_9_25=F(9,25)
''',
33: r'''C_m107_100=F(-107,100)
C_m11_10=F(-11,10)
''',
34: r'''C_m11_1000=F(-11,1000)
''',
35: r'''C_m12_5=F(-12,5)
C_m1_100=F(-1,100)
''',
36: r'''C_m29_20=F(-29,20)
C_m37_25=F(-37,25)
''',
37: r'''C_m3_2=F(-3,2)
''',
38: r'''C_m441_100=F(-441,100)
C_m4_25=F(-4,25)
C_m5401_1000=F(-5401,1000)
C_m63_1000=F(-63,1000)
''',
39: r'''C_m701_100=F(-701,100)
''',
40: r'''C_m927_1000=F(-927,1000)
''',
41: r'''C_m93_100=F(-93,100)
C_m9_10=F(-9,10)
''',
42: r'''def evaluate(q,b,delta,eps):
 q0,q1,q2,q3=q
 t0=(C_1_100 * q3)
 t1=(C_1_10 * delta)
 t2=(C_1_10 * eps)
 t3=(1 + (-q1))
 t4=(1 + (-q2))
 t5=(1 + (-q3))
 t6=(t4 * t5)
 t7=(1 + (-q0))
 t8=(t3 * t7)
 Q0=((C_1_1000 * q3) + (q1 * (C_1_100 + (C_m11_1000 * q3) + (q2 * (C_m441_100 + (C_4411_1000 * q3))))) + (q2 * (C_27_5 + (C_m5401_1000 * q3))))
 D0=(t0 + (q1 * (-1 + (-t0) + (q2 * (-4 + (C_501_100 * q3))))) + (q2 * (6 + (C_m701_100 * q3))))
 Q1=((C_1_100 * q0) + (q2 * (C_3_20 + (C_m4_25 * q0) + (q3 * (C_49_100 + (C_m37_25 * q0))))) + (q3 * (C_9_25 + (C_63_100 * q0))))
 D1=((-q0) + (q2 * (C_3_2 + (C_m3_2 * q0) + (q3 * (C_m9_10 + (C_m11_10 * q0))))) + (q3 * (C_2_5 + (C_8_5 * q0))))
 Q2=(t0 + (q0 * (t1 + (q1 * (C_23_50 + (-t1) + (q3 * (C_m29_20 + t1)))) + (q3 * (C_m1_100 + (-t1))))) + (q1 * (C_27_50 + (C_9_20 * q3))))
 D2=((-q3) + (q0 * (delta + (q1 * (C_2_5 + (-delta) + (q3 * (C_m12_5 + delta)))) + (-delta * q3))) + (q1 * (C_3_5 + (C_7_5 * q3))))
 Q3=((C_1_100 * q2) + (q0 * (C_63_1000 + (C_927_1000 * q2))) + (q1 * (t2 + (q0 * (C_m63_1000 + (-t2) + (q2 * (C_m927_1000 + t2)))) + (q2 * (C_m1_100 + (-t2))))))
 D3=((-q2) + (q0 * (C_7_100 + (C_193_100 * q2))) + (q1 * (eps + (q0 * (C_m107_100 + (-eps) + (q2 * (C_m93_100 + eps)))) + (-eps * q2))))
 H0=(t3 * t6)
 H1=(t6 * t7)
 H2=(t5 * t8)
 H3=(t4 * t8)
 Q=[Q0,Q1,Q2,Q3]; DD=[D0,D1,D2,D3]; H=[H0,H1,H2,H3]
 g=[v-h*x for v,h,x in zip(DD,H,b)]
 return [v-w for v,w in zip(Q,DD)],Q,H,g
''',
43: r'''


''',
44: r'''def gaps(q,b,delta,eps):
 q0,q1,q2,q3=q
 t0=(1 + (-q1))
 t1=(1 + (-q2))
 t2=(1 + (-q3))
 t3=(t1 * t2)
 t4=(1 + (-q0))
 t5=(t0 * t4)
 D0=((-q1) + (q2 * (6 + (-4 * q1) + (q3 * (C_m701_100 + (C_501_100 * q1))))) + (q3 * (C_1_100 + (C_m1_100 * q1))))
 H0=(t0 * t3)
 D1=((-q0) + (q2 * (C_3_2 + (C_m3_2 * q0) + (q3 * (C_m9_10 + (C_m11_10 * q0))))) + (q3 * (C_2_5 + (C_8_5 * q0))))
 H1=(t3 * t4)
 D2=((-q3) + (q0 * (delta + (q1 * (C_2_5 + (-delta) + (q3 * (C_m12_5 + delta)))) + (-delta * q3))) + (q1 * (C_3_5 + (C_7_5 * q3))))
 H2=(t2 * t5)
 D3=((-q2) + (q0 * (C_7_100 + (C_193_100 * q2))) + (q1 * (eps + (q0 * (C_m107_100 + (-eps) + (q2 * (C_m93_100 + eps)))) + (-eps * q2))))
 H3=(t1 * t5)
 return [D0-H0*b[0],D1-H1*b[1],D2-H2*b[2],D3-H3*b[3]]
''',
45: r'''def qjac(q,b,d,e):
 qj=[Jet(x,[Iv(int(i==j))for j in range(N)])for i,x in enumerate(q)]
 g=gaps(qj,[Jet(x)for x in b],Jet(d),Jet(e))
 return[[x.d[j]for j in I]for x in g]
''',
46: r'''def proposal(S,b,d,e,seed,fixed):
 bb=[float(mid(x))for x in b];dd=float(mid(d));ee=float(mid(e));q=[float(mid(x))for x in fixed]
 for i in S:q[i]=float(seed[i])
 q,C=float_newton(S,q,bb,dd,ee)
 return[F(str(x))for x in q],[[F(str(x))for x in row]for row in C]
''',
47: r'''def rootbox(S,b,d,e,seed,fixed=None,must=None,graph=None):
 S=list(S);fixed=[Iv(0)]*4 if fixed is None else fixed
 qhat,C=proposal(S,b,d,e,seed,fixed)
 bm=[Iv(mid(x))for x in b];dm=Iv(mid(d));em=Iv(mid(e))
 for _ in range(4):
  qp0=[Iv(x)if i in S else Iv(mid(fixed[i]))for i,x in enumerate(qhat)]
  correction=mv(C,[mid(gaps(qp0,bm,dm,em)[i])for i in S])
  for i,x in zip(S,correction):
   z=qhat[i]-x;qhat[i]=F(z.numerator*10**60//z.denominator,10**60)
 qp=[Iv(x)if i in S else fixed[i]for i,x in enumerate(qhat)]
 resid=mv(C,[gaps(qp,b,d,e)[i]for i in S])
 if graph is not None:
  bg,dg,eg,bp,dp,ep,widths=graph
  # qhat is constant in the six ORIGINAL latent variables. Independent fixed
  # bridge hazards remain intervals at the point anchor AND in derivatives.
  gj=gaps([Jet(x)for x in qp],bg,dg,eg)
  rhoj=mv(C,[gj[i]for i in S])
  gp=gaps(qp,[x.v for x in bp],dp.v,ep.v)
  rhop=mv(C,[gp[i]for i in S])
  rg=[around(a,sum(mag(v)*w for v,w in zip(z.d,widths)))for a,z in zip(rhop,rhoj)]
  resid=[Iv(max(a.lo,z.lo),min(a.hi,z.hi),True)for a,z in zip(resid,rg)]
  assert all(z.lo<=z.hi for z in resid), 'empty graph residual intersection'
 rr=[2*mag(x)+F(1,10**55)for x in resid]
 if must:
  for k,i in enumerate(S):rr[k]=max(rr[k],mag(must[i]-qhat[i])*F(11,10))
 for attempt in range(20):
  qb=qp[:]
  for i,r in zip(S,rr):qb[i]=Iv.box(qhat[i],r)
  G=qjac(qb,b,d,e);A=[[G[i][j]for j in S]for i in S];M=[[Iv(int(i==j))-x for j,x in enumerate(row)]for i,row in enumerate(mm(C,A))]
  lip=max(sum(mag(x)*r for x,r in zip(row,rr))/rr[i]for i,row in enumerate(M))
  if lip<F(9,10) and all(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))<r0 for z,row,r0 in zip(resid,M,rr)):
   qs=qb[:]
   for k,i in enumerate(S):qs[i]=Iv(qhat[i])-resid[k]+sum(a*Iv.box(0,r)for a,r in zip(M[k],rr))
   for i in S:
    qs[i]=Iv(max(qs[i].lo,qb[i].lo),min(qs[i].hi,qb[i].hi),True)
    assert qs[i].lo<=qs[i].hi,('empty Newton image intersection',i)
   Gs=qjac(qs,b,d,e);As=[[Gs[i][j]for j in S]for i in S]
   return(qb if must is not None else qs),Gs,inv_pre(As,C),float(lip)
  rr=[max(old,F(5,4)*(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))))for old,z,row in zip(rr,resid,M)]
  if lip>F(9,10):break
 raise AssertionError(('stage Newton failed',S,float(lip),[float(x)for x in rr]))
''',
48: r'''def branch(S,b,d,e,seed,fixed=None,graph=None):
 context=None if graph is None else (b,d,e,*graph)
 qb,G,inverse,lip=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,graph=context)
 bl=[Jet(x.v,[Iv(int(i==j))for j in range(6)])for i,x in enumerate(b)]
 dl=Jet(d.v,[Iv(0)]*4+[Iv(1),Iv(0)]);el=Jet(e.v,[Iv(0)]*5+[Iv(1)])
 direct=gaps([Jet(x)for x in qb],bl,dl,el)
 deriv=mm(inverse,[[-x for x in direct[i].d]for i in S]);qj=[Jet(x)for x in qb]
 for i,der in zip(S,deriv):qj[i]=Jet(qb[i],der)
 P,Q,H,g=evaluate(qj,bl,dl,el);out=[Q[i]if i in S else Q[i]-g[i]for i in I]
 inputs=[x.d for x in b]+[d.d,e.d];od=mm([x.d for x in out],inputs);gd=mm([x.d for x in g],inputs)
 return[Jet(x.v,z)for x,z in zip(out,od)],qb,[Jet(x.v,z)for x,z in zip(g,gd)],G,lip
''',
49: r'''def candidate(dc,ec):
 c,seeds=float_center(float(dc),float(ec));v=[]
 for k in range(2):
  us=[]
  for sign in[-1,1]:
   dd=float(dc)+(sign*1e-8 if k==0 else 0);ee=float(ec)+(sign*1e-8 if k==1 else 0)
   us.append(float_center(dd,ee,c)[0])
  v.append([F(str((y-x)/2e-8))for x,y in zip(*us)])
 return[F(str(x))for x in c],list(zip(*v)),seeds
''',
50: r'''def alternatives(b,bp,d,e,dp,ep,seed,S,optional,widths):
 graph=(bp,dp,ep,widths)
 oq,qq,gq,Gq,lq=branch(S,b,d,e,seed,graph=graph);op,qp,gp,_,_=branch(S,bp,dp,ep,seed)
 assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,qq)), 'quiet graph anchor linkage'
 for i in I:
  rg=around(gp[i].v,sum(mag(z)*w for z,w in zip(gq[i].d,widths)))
  gq[i].v=Iv(max(gq[i].v.lo,rg.lo),min(gq[i].v.hi,rg.hi),True)
  assert gq[i].v.lo<=gq[i].v.hi
 if not optional or gq[3].v.hi<0:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S)
  assert all(gq[i].v.hi<0 for i in I if i not in S)
  modes=[(oq,op,qq,qp,'q')]
 else:
  of,qf,gf,Gf,lf=branch([0,1,2,3],b,d,e,seed,graph=graph);ofp,qfp,_,_,_=branch([0,1,2,3],bp,dp,ep,seed)
  assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S)
  assert qf[3].hi<D
  if gq[3].v.lo>0 and qf[3].lo>0:modes=[(of,ofp,qf,qfp,'f')]
  else:
   y=hull(Iv(0),qf[3]);fixed=[Iv(0)]*3+[y]
   bridge,Gb,ib,lb=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,[hull(x,y)for x,y in zip(qq,qf)],graph=(b,d,e,*graph))
   assert all(bridge[i].lo<=qf[i].lo and qf[i].hi<=bridge[i].hi for i in S)
   schur=Gb[3][3]-sum(Gb[3][i]*x for i,x in zip(S,mv(ib,[Gb[i][3]for i in S])))
   assert schur.hi<0,('bad Schur',schur)
   modes=[(oq,op,qq,qp,'q'),(of,ofp,qf,qfp,'f')]
 for _,_,q,qp,_ in modes:assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,q))
 return modes
''',
51: r'''def union(boxes):
 return[Iv(min(row[i].lo for row in boxes),max(row[i].hi for row in boxes),True)for i in I]
''',
52: r'''def common_link(parents,children,d,e,seed,S,optional,dp,ep,widths):
 """Uniqueness on convex hulls, using existence already certified historywise.
 Every incoming history's QUIET chart is included, even if full is selected.
 At mixed selected modes, full uniqueness includes quiet tubes to identify seams.
 """
 if len(parents)==1 and len(children)==1:return(0,0)
 bb=union([[x.v for x in b]for b,bp,word in parents])
 quiet=[]
 for b,bp,word in parents:
  choices=[rec[2]for rec in children if rec[5]==word and rec[4]=='q']
  quiet.append(choices[0]if choices else branch(S,b,d,e,seed,graph=(bp,dp,ep,widths))[1])
 groups={tuple(S):quiet}
 full=[rec[2]for rec in children if rec[4]=='f']
 if full:
  mixed=any(rec[4]=='q'for rec in children)
  groups[(0,1,2,3)]=full+quiet if mixed else full
 maxlip=0
 for support,boxes in groups.items():
  qh=union(boxes);G=qjac(qh,bb,d.v,e.v)
  A=[[G[i][j]for j in support]for i in support]
  C=[[F(str(x))for x in row]for row in float_inverse([[float(mid(x))for x in row]for row in A])]
  E=[[Iv(int(i==j))-z for j,z in enumerate(row)]for i,row in enumerate(mm(C,A))]
  lip=max(sum(mag(z)for z in row)for row in E)
  assert lip<F(1),('common uniqueness',support,float(lip))
  maxlip=max(maxlip,float(lip))
 return(len(groups),maxlip)
''',
53: r'''def verify(dl,du,el,eu,r,verbose=True):
 dc=(dl+du)/2;ec=(el+eu)/2;hd=(du-dl)/2;he=(eu-el)/2;c,v,seeds=candidate(dc,ec);widths=r+[hd,he]
 b=[Jet(Iv.box(c[i],r[i]+abs(v[i][0])*hd+abs(v[i][1])*he),[Iv(int(i==j))for j in I]+[Iv(x)for x in v[i]])for i in I]
 bp=[Jet(x)for x in c];d=Jet(Iv.box(dc,hd),[Iv(0)]*4+[Iv(1),Iv(0)]);e=Jet(Iv.box(ec,he),[Iv(0)]*5+[Iv(1)])
 dp=Jet(dc);ep=Jet(ec);paths=[(b,bp,'')];minq=1;links=0;maxlinklip=0
 for t in range(64):
  S=[0,1,3]if t<4 else[0,1,2];records=[]
  for b,bp,word in paths:
   try:modes=alternatives(b,bp,d,e,dp,ep,seeds[t],S,t>=4,widths)
   except Exception as ex:raise AssertionError(('branch failure at phase',t,word,str(ex)))from ex
   for out,op,q,qp,mode in modes:
    support=[0,1,2,3]if mode=='f'else S
    records.append((out,op,q,qp,mode,word,support))
  try:
   nl,ll=common_link(paths,records,d,e,seeds[t],S,t>=4,dp,ep,widths);links+=nl;maxlinklip=max(maxlinklip,ll)
  except Exception as ex:raise AssertionError(('link failure at phase',t,str(ex)))from ex
  new=[]
  for out,op,q,qp,mode,word,support in records:
   assert min(q[0].lo,q[1].lo)*10**7>D, 'uniform opponent hazard lower bound'
   minq=min(minq,q[0].lower(),q[1].lower())
   for i in I:
    rad=sum(mag(out[i].d[j])*r[j]for j in I)+mag(out[i].d[4])*hd+mag(out[i].d[5])*he
    rg=around(op[i].v,rad)
    out[i].v=Iv(max(out[i].v.lo,rg.lo),min(out[i].v.hi,rg.hi),True)
    assert out[i].v.lo<=out[i].v.hi
   new.append((out,op,word+mode))
  paths=new;assert len(paths)<=16,('too many histories',len(paths))
  if verbose and(t in(4,5,6,7,15,31,63)or len(records)>1 and t<12):print('PHASE',t,'histories',len(paths),'links',links,'maxlinklip',maxlinklip,flush=True)
 stats=[]
 for b,bp,word in paths:
  L=[sum(mag(x)*r[j]for j,x in enumerate(row.d[:4]))/r[i]for i,row in enumerate(b)]
  R=[mag(bp[i].v-c[i])+mag(b[i].d[4]-v[i][0])*hd+mag(b[i].d[5]-v[i][1])*he for i in I]
  assert all(x*rr+y<rr for x,y,rr in zip(L,R,r)),('return failure',word,[float(x)for x in L],[float(x/rr)for x,rr in zip(R,r)])
  stats.append((float(max(L)),float(max(x/rr for x,rr in zip(R,r)))))
 print('PASS',float(dl),float(du),float(el),float(eu),'histories',len(paths),'stats',stats,'q01',minq,'commonlinks',links,'maxlinklip',maxlinklip,flush=True)
 return stats,minq,len(paths),links,maxlinklip
''',
54: r'''def audit_horner():
 # All expressions are visibly multiaffine in q,b,delta,epsilon. The full
 # hazard/parameter vertex grid and b=0 plus four coordinate directions
 # therefore prove equality of the two exact polynomial evaluators.
 from itertools import product
 for q in product((F(0),F(1)),repeat=4):
  for d,e in product((F(0),F(1)),repeat=2):
   for k in range(5):
    b=[F(int(i==k))for i in I]
    old=raw_evaluate(q,b,d,e);new=evaluate(q,b,d,e)
    assert old==new
    assert old[3]==gaps(q,b,d,e)
 print('PASS exact raw-table/Horner polynomial identities',flush=True)
''',
55: r'''import contextlib,io,time
COUNT=0;FAILS=0;START=time.time();MAX_CELLS=2000
def cover(dl,du,el,eu,depth=0):
 global COUNT,FAILS
 assert COUNT<MAX_CELLS,('cell budget',COUNT,FAILS)
 dw=du-dl;ew=eu-el
 scale=max(F(3),120000000*dw*dw,3000*ew)
 rad=[F(x)*scale for x in ['1.8e-6','5.4e-8','3.6e-8','6e-5']]
 try:
  with contextlib.redirect_stdout(io.StringIO()):stats=verify(dl,du,el,eu,rad,False)
  COUNT+=1
  if COUNT%10==0:print('ACCEPT',COUNT,'fails',FAILS,'cell',*[float(x)for x in(dl,du,el,eu)],'maxL',max(x[0]for x in stats[0]),'maxR',max(x[1]for x in stats[0]),'seconds',int(time.time()-START),flush=True)
  return
 except AssertionError as ex:
  FAILS+=1
  if depth>=24:raise AssertionError(('depth',dl,du,el,eu,str(ex)))from ex
  # Balance parameter widths; no failure type is allowed to starve a side.
  if dw>0 and ew<dw/5:
   dm=(dl+du)/2;cover(dl,dm,el,eu,depth+1);cover(dm,du,el,eu,depth+1)
  else:
   em=(el+eu)/2;cover(dl,du,el,em,depth+1);cover(dl,du,em,eu,depth+1)
if __name__=='__main__':
 audit_horner()
 for n in range(4):
  cover(F(n,2000),F(n+1,2000),F(0),F(1843,2500))
  print('STRIP_COMPLETE',n+1,COUNT,FAILS,int(time.time()-START),flush=True)
 print('PASS_COMPLETE_CORNER',COUNT,FAILS,time.time()-START,flush=True)
''',
56: r'''"""Exact support-seam certificate; standard library only. Floats propose; integer intervals certify."""
''',
57: r'''I=range(4);N=6;SEAM_INFO=[]
''',
58: r'''def rootbox(S,b,d,e,seed,fixed=None,must=None,graph=None):
 S=list(S);fixed=[Iv(0)]*4 if fixed is None else fixed
 qhat,C=proposal(S,b,d,e,seed,fixed)
 bm=[Iv(mid(x))for x in b];dm=Iv(mid(d));em=Iv(mid(e))
 for _ in range(4):
  qp0=[Iv(x)if i in S else Iv(mid(fixed[i]))for i,x in enumerate(qhat)]
  correction=mv(C,[mid(gaps(qp0,bm,dm,em)[i])for i in S])
  for i,x in zip(S,correction):
   z=qhat[i]-x;qhat[i]=F(z.numerator*10**60//z.denominator,10**60)
 qp=[Iv(x)if i in S else fixed[i]for i,x in enumerate(qhat)]
 resid=mv(C,[gaps(qp,b,d,e)[i]for i in S])
 if graph is not None:
  bg,dg,eg,bp,dp,ep,widths=graph
  # qhat is constant in the six ORIGINAL latent variables. Independent fixed
  # bridge hazards remain intervals at the point anchor AND in derivatives.
  gj=gaps([Jet(x)for x in qp],bg,dg,eg)
  rhoj=mv(C,[gj[i]for i in S])
  gp=gaps(qp,[x.v for x in bp],dp.v,ep.v)
  rhop=mv(C,[gp[i]for i in S])
  rg=[around(a,sum(mag(v)*w for v,w in zip(z.d,widths)))for a,z in zip(rhop,rhoj)]
  resid=[Iv(max(a.lo,z.lo),min(a.hi,z.hi),True)for a,z in zip(resid,rg)]
  assert all(z.lo<=z.hi for z in resid), 'empty graph residual intersection'
 rr=[2*mag(x)+F(1,10**55)for x in resid]
 if must:
  for k,i in enumerate(S):rr[k]=max(rr[k],mag(must[i]-qhat[i])*F(11,10))
 for attempt in range(20):
  qb=qp[:]
  for i,r in zip(S,rr):qb[i]=Iv.box(qhat[i],r)
  G=qjac(qb,b,d,e);A=[[G[i][j]for j in S]for i in S];M=[[Iv(int(i==j))-x for j,x in enumerate(row)]for i,row in enumerate(mm(C,A))]
  lip=max(sum(mag(x)for x in row)for row in M)
  if lip<F(9,10) and all(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))<r0 for z,row,r0 in zip(resid,M,rr)):
   qs=qb[:]
   for k,i in enumerate(S):qs[i]=Iv(qhat[i])-resid[k]+sum(a*Iv.box(0,r)for a,r in zip(M[k],rr))
   for i in S:
    qs[i]=Iv(max(qs[i].lo,qb[i].lo),min(qs[i].hi,qb[i].hi),True)
    assert qs[i].lo<=qs[i].hi,('empty Newton image intersection',i)
   Gs=qjac(qs,b,d,e);As=[[Gs[i][j]for j in S]for i in S]
   return(qb if must is not None else qs),Gs,inv_pre(As,C),float(lip)
  rr=[max(old,F(5,4)*(mag(z)+sum(mag(a)*r for a,r in zip(row,rr))))for old,z,row in zip(rr,resid,M)]
  if lip>F(9,10):break
 raise AssertionError(('stage Newton failed',S,float(lip),[float(x)for x in rr]))
''',
59: r'''def local_branch(S,b,d,e,seed,fixed=None,graph=None):
 context=None if graph is None else (b,d,e,*graph)
 qb,G,inverse,lip=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,graph=context)
 bl=[Jet(x.v,[Iv(int(i==j))for j in range(6)])for i,x in enumerate(b)]
 dl=Jet(d.v,[Iv(0)]*4+[Iv(1),Iv(0)]);el=Jet(e.v,[Iv(0)]*5+[Iv(1)])
 direct=gaps([Jet(x)for x in qb],bl,dl,el)
 deriv=mm(inverse,[[-x for x in direct[i].d]for i in S]);qj=[Jet(x)for x in qb]
 for i,der in zip(S,deriv):qj[i]=Jet(qb[i],der)
 P,Q,H,g=evaluate(qj,bl,dl,el);out=[Q[i]if i in S else Q[i]-g[i]for i in I]
 inputs=[x.d for x in b]+[d.d,e.d];od=mm([x.d for x in out],inputs);gd=mm([x.d for x in g],inputs)
 return[Jet(x.v,z)for x,z in zip(out,od)],qb,[Jet(x.v,z)for x,z in zip(g,gd)],G,lip
''',
60: r'''def center(d,e,n,p,prefer_pair=True):
 word=[[0,1,3]]*2+[[0,1,2]]*n+[[0,2,3]]*p
 c=[.0041188900253,.0001243482175,.0000419077556,.3690086159]
 for it in range(10):
  rows=[]
  for S in word:
   S=S[:];q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
   if S==[0,1,3]and prefer_pair:
    pair=[c[3]/(c[3]+.07),0.,0.,c[0]/(c[0]+.01)]
    pp,qq,hh,gg=evaluate(pair,c,d,e)
    if gg[1]<=0 and gg[2]<=0:S=[0,3];q=pair;P,Q,H,g=pp,qq,hh,gg
   if S==[0,1,2]and g[3]>0:
    q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
   b=[Q[i]if i in S else Q[i]-g[i]for i in I];rows.append((q,g,S,c,b));c=b
 return c,rows
''',
61: r'''N0,P0=2,12
''',
62: r'''WORD=[[0,1,3]]*2+[[0,1,2]]*N0+[[0,2,3]]*P0
''',
63: r'''def candidate(dc,ec):
 c,rows=center(float(dc),float(ec),N0,P0,False)
 assert all(r[2]==S or (S==[0,1,2] and r[2]==[0,1,2,3]) for r,S in zip(rows,WORD))
 vv=[]
 for j in range(2):
  us=[]
  for sg in(-1,1):
   dd=float(dc)+sg*1e-7*(j==0);ee=float(ec)+sg*1e-7*(j==1)
   us.append(center(dd,ee,N0,P0,False)[0])
  vv.append([F(str((y-x)/2e-7))for x,y in zip(*us)])
 return[F(str(x))for x in c],list(zip(*vv)),[r[0]for r in rows]
''',
64: r'''def stage(b,d,e,seed,S,seam=False,point=False,graph=None):
 assert not seam or S==[0,1,2]
 quiet=local_branch(S,b,d,e,seed,graph=graph);oq,qq,gq,Gq,lq=quiet
 if graph is not None:
  bp,dp,ep,widths=graph
  _,qp,gp,_,_=local_branch(S,bp,dp,ep,seed)
  # Required even when only the full branch is selected later.
  assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,qq)), 'quiet graph-anchor root identity'
  for i in I:
   rg=around(gp[i].v,sum(mag(z)*w for z,w in zip(gq[i].d,widths)))
   gq[i].v=Iv(max(gq[i].v.lo,rg.lo),min(gq[i].v.hi,rg.hi),True)
   assert gq[i].v.lo<=gq[i].v.hi, 'empty graph-gap intersection'
 if not seam:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S),('bad hazard',S,qq)
  assert all(gq[i].v.hi<0 for i in I if i not in S)
  return oq,min(float(qq[i].lower())for i in S),lq,[qq]
 if gq[3].v.hi<0:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S)
  if not point:SEAM_INFO.append((gq[3].v,'quiet','strict'))
  return oq,min(qq[i].lower()for i in S),lq,[qq]
 full=local_branch([0,1,2,3],b,d,e,seed,graph=graph);of,qf,gf,Gf,lf=full
 if gq[3].v.lo>0 and qf[3].lo>0:
  assert all(qf[i].lo>0 and qf[i].hi<D for i in I)
  if not point:SEAM_INFO.append((gq[3].v,qf[3],'full'))
  return of,min(qf[i].lower()for i in S),max(lq,lf),[qq,qf]
 assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S)
 assert qf[3].hi<D
 y=hull(Iv(0),qf[3]);fixed=[Iv(0)]*3+[y]
 bridge,Gb,ib,lb=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,[hull(x,y)for x,y in zip(qq,qf)],graph=None if graph is None else (b,d,e,*graph))
 assert all(bridge[i].lo<=qf[i].lo and qf[i].hi<=bridge[i].hi for i in S)
 schur=Gb[3][3]-sum(Gb[3][i]*x for i,x in zip(S,mv(ib,[Gb[i][3]for i in S])))
 assert schur.hi<0,('bad Schur',schur)
 if not point:SEAM_INFO.append((gq[3].v,qf[3],schur))
 if point:
  if gq[3].v.hi<0:out=oq
  elif gq[3].v.lo>0:
   assert qf[3].lo>0;out=of
  else:raise AssertionError('point on seam')
 else:out=[Jet(hull(x.v,y.v),[hull(a,c)for a,c in zip(x.d,y.d)])for x,y in zip(oq,of)]
 return out,min(min(qq[i].lower(),qf[i].lower())for i in S),max(lq,lf,lb),[qq,qf]
''',
65: r'''def verify(dl,du,el,eu,r,verbose=False):
 SEAM_INFO.clear()
 dc=(dl+du)/2;ec=(el+eu)/2;hd=(du-dl)/2;he=(eu-el)/2;c,v,seeds=candidate(dc,ec)
 b=[Jet(Iv.box(c[i],r[i]+abs(v[i][0])*hd+abs(v[i][1])*he),[Iv(int(i==j))for j in I]+[Iv(x)for x in v[i]])for i in I]
 bp=[Jet(x)for x in c];d=Jet(Iv.box(dc,hd),[Iv(0)]*4+[Iv(1),Iv(0)]);e=Jet(Iv.box(ec,he),[Iv(0)]*5+[Iv(1)])
 dp=Jet(dc);ep=Jet(ec);minq=1.;newton=0
 for phase,S in enumerate(WORD):
  seam=S==[0,1,2]
  prior=bp
  bp,_,_,pc=stage(bp,dp,ep,seeds[phase],S,seam,True)
  b,mq,lip,bc=stage(b,d,e,seeds[phase],S,seam,graph=(prior,dp,ep,r+[hd,he]));newton=max(newton,lip);minq=min(minq,mq)
  assert len(pc)<=len(bc) and all(y.lo<=x.lo and x.hi<=y.hi for pr,br in zip(pc,bc)for x,y in zip(pr,br)),('center root outside domain',phase)
  # stage() checks strict positivity of the selected branch's common owners.
  # The unused quiet extension may have negative hazards in a strict full cell.
  for i in I:
   rad=sum(mag(b[i].d[j])*r[j]for j in I)+mag(b[i].d[4])*hd+mag(b[i].d[5])*he
   centered=around(bp[i].v,rad)
   b[i].v=Iv(max(b[i].v.lo,centered.lo),min(b[i].v.hi,centered.hi),True)
   assert b[i].v.lo<=b[i].v.hi, 'empty output-range intersection'
 L=[sum(mag(x)*r[j]for j,x in enumerate(row.d[:4]))/r[i]for i,row in enumerate(b)]
 R=[mag(bp[i].v-c[i])+mag(b[i].d[4]-v[i][0])*hd+mag(b[i].d[5]-v[i][1])*he for i in I]
 if verbose:print('RETURN L',list(map(float,L)),'R/r',[float(x/rr)for x,rr in zip(R,r)],flush=True)
 assert all(x*rr+y<rr for x,y,rr in zip(L,R,r)),('return selfmap',list(map(float,L)),[float(x/rr)for x,rr in zip(R,r)])
 assert max(L)<1
 assert all(len(S)>=2 for S in WORD)
 return float(max(L)),float(max(x/rr for x,rr in zip(R,r))),minq,newton
''',
66: r'''
# Complete-cover driver. A budget abort is a failure, never partial coverage.
BASE=[F(2,100000),F(2,10000),F(2,100000),F(2,100000)]
CELLS=0;FAILS=0;ATTEMPTS=0;START=0;NODE_LIMIT=40000;SECOND_LIMIT=7200
''',
67: r'''def visit(dl,du,el,eu,depth=0):
 global CELLS,FAILS,ATTEMPTS
 scale=max(F(1),(du-dl)/F(1,500),(eu-el)/F(1,500));factor=(scale.numerator+scale.denominator-1)//scale.denominator
 stats=None;reason=''
 for k in [factor,2*factor]:
  ATTEMPTS+=1
  assert ATTEMPTS<=NODE_LIMIT and time.monotonic()-START<=SECOND_LIMIT,('budget limit',ATTEMPTS,time.monotonic()-START,dl,du,el,eu)
  try:stats=verify(dl,du,el,eu,[k*x for x in BASE]);break
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError)as ex:
   reason=str(ex)
   if not(isinstance(ex,AssertionError)and ex.args and isinstance(ex.args[0],tuple)and ex.args[0][0]=='return selfmap'):break
 if stats is None:
  FAILS+=1;assert depth<18,('subdivision limit',dl,du,el,eu,reason[:300])
  if du-dl>=5*(eu-el):
   dm=(dl+du)/2;visit(dl,dm,el,eu,depth+1);visit(dm,du,el,eu,depth+1)
  else:
   em=(el+eu)/2;visit(dl,du,el,em,depth+1);visit(dl,du,em,eu,depth+1)
  return
 CELLS+=1
 if CELLS%25==0:print('CELLS',CELLS,'attempts',ATTEMPTS,'failed parents',FAILS,'front',float(du),float(eu),'seconds',time.monotonic()-START,flush=True)
''',
68: r'''if __name__=='__main__':
 START=time.monotonic();audit_horner()
 for i in range(25):
  dl=F(7,10)+F(i,50);du=dl+F(1,50)
  top=F(737,1000)+F(3,50)*du+F(1,2000)
  j=0
  while F(j,100)<top:
   visit(dl,du,F(j,100),min(F(j+1,100),top))
   j+=1
  print('DELTA_SLAB_COMPLETE',dl,du,'epsilon_top',top,'initial_slabs',j,'cells',CELLS,'failed parents',FAILS,'attempts',ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
 print('PASS COMPLETE BROAD GRAPH COVER delta[.7,1.2], epsilon[0,.737+.06delta+.0005]',CELLS,'closed cells',FAILS,'failed parents',ATTEMPTS,'attempts','seconds',time.monotonic()-START,flush=True)
''',
69: r'''"""Exact complete-history certificates for a three-calendar middle portfolio.
Target delta [.12,.7], epsilon [0,.738+.06delta], period at most 33.
Only the final full-run success marker verifies the complete target cover.
Standard library only. Floats propose; all acceptance uses exact intervals.
"""
''',
70: r'''if not __debug__:raise RuntimeError('Assertions are required; do not use -O.')
import sys,time
''',
71: r'''def qjac(q,b,d,e):
 # Explicit hazard derivative of gaps(). Diagonals vanish because g_i is
 # independent of q_i. The cap contribution is b_i prod_(k!=i,j)(1-q_k).
 q0,q1,q2,q3=q
 h0,h1,h2,h3=1-q0,1-q1,1-q2,1-q3
 s01=h2*h3;s02=h1*h3;s03=h1*h2
 s12=h0*h3;s13=h0*h2;s23=h0*h1
 z=0*q0
 a01=-1+q2*(-4+C_501_100*q3)+C_m1_100*q3+b[0]*s01
 a02=6-4*q1+q3*(C_m701_100+C_501_100*q1)+b[0]*s02
 a03=C_1_100+C_m1_100*q1+q2*(C_m701_100+C_501_100*q1)+b[0]*s03
 a10=-1+q2*(C_m3_2+C_m11_10*q3)+C_8_5*q3+b[1]*s01
 a12=C_3_2+C_m3_2*q0+q3*(C_m9_10+C_m11_10*q0)+b[1]*s12
 a13=C_2_5+C_8_5*q0+q2*(C_m9_10+C_m11_10*q0)+b[1]*s13
 t2=C_2_5-d+q3*(C_m12_5+d)
 a20=d+q1*t2-d*q3+b[2]*s02
 a21=C_3_5+C_7_5*q3+q0*t2+b[2]*s12
 a23=-1+q0*(-d+q1*(C_m12_5+d))+C_7_5*q1+b[2]*s23
 t3=C_m107_100-e+q2*(C_m93_100+e)
 a30=C_7_100+C_193_100*q2+q1*t3+b[3]*s03
 a31=e+q0*t3-e*q2+b[3]*s13
 a32=-1+C_193_100*q0+q1*(-e+q0*(C_m93_100+e))+b[3]*s23
 return [[z,a01,a02,a03],[a10,z,a12,a13],[a20,a21,z,a23],[a30,a31,a32,z]]
''',
72: r'''def center(d,e,h,n,p,prefer_pair=True):
 word=[[0,1,3]]*h+[[0,1,2]]*n+[[0,2,3]]*p
 c=[.0041188900253,.0001243482175,.0000419077556,.3690086159]
 for it in range(10):
  rows=[]
  for S in word:
   S=S[:];q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
   if S==[0,1,3]and prefer_pair:
    pair=[c[3]/(c[3]+.07),0.,0.,c[0]/(c[0]+.01)]
    pp,qq,hh,gg=evaluate(pair,c,d,e)
    if gg[1]<=0 and gg[2]<=0:S=[0,3];q=pair;P,Q,H,g=pp,qq,hh,gg
   if S==[0,1,2]and g[3]>0:
    q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
   b=[Q[i]if i in S else Q[i]-g[i]for i in I];rows.append((q,g,S,c,b));c=b
 return c,rows
def alternatives(b,bp,d,e,dp,ep,seed,S,optional,widths):
 graph=(bp,dp,ep,widths)
 oq,qq,gq,Gq,lq=branch(S,b,d,e,seed,graph=graph);op,qp,gp,_,_=branch(S,bp,dp,ep,seed)
 assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,qq)), 'quiet graph anchor linkage'
 for i in I:
  rg=around(gp[i].v,sum(mag(z)*w for z,w in zip(gq[i].d,widths)))
  gq[i].v=Iv(max(gq[i].v.lo,rg.lo),min(gq[i].v.hi,rg.hi),True)
  assert gq[i].v.lo<=gq[i].v.hi
 if not optional or gq[3].v.hi<0:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S),('quiet physical',S,qq)
  assert all(gq[i].v.hi<0 for i in I if i not in S),('quiet gaps',S,[gq[i].v for i in I if i not in S])
  modes=[(oq,op,qq,qp,'q')]
 else:
  of,qf,gf,Gf,lf=branch([0,1,2,3],b,d,e,seed,graph=graph);ofp,qfp,_,_,_=branch([0,1,2,3],bp,dp,ep,seed)
  assert qf[3].hi<D,('full optional upper',qf)
  if gq[3].v.lo>0 and qf[3].lo>0:
   assert all(qf[i].lo>0 and qf[i].hi<D for i in S),('strict full physical',qf)
   modes=[(of,ofp,qf,qfp,'f')]
  else:
   assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S),('seam persistent physical',qq,qf)
   y=hull(Iv(0),qf[3]);fixed=[Iv(0)]*3+[y]
   bridge,Gb,ib,lb=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,[hull(x,y)for x,y in zip(qq,qf)],graph=(b,d,e,*graph))
   assert all(bridge[i].lo<=qf[i].lo and qf[i].hi<=bridge[i].hi for i in S)
   schur=Gb[3][3]-sum(Gb[3][i]*x for i,x in zip(S,mv(ib,[Gb[i][3]for i in S])))
   assert schur.hi<0,('bad Schur',schur)
   modes=[(oq,op,qq,qp,'q'),(of,ofp,qf,qfp,'f')]
 for _,_,q,qp,_ in modes:assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,q))
 return modes
''',
73: r'''H0=2;N0=6;P0=24
WORD=[[0,1,3]]*H0+[[0,1,2]]*N0+[[0,2,3]]*P0
''',
74: r'''BASE=[F(1,10**5),F(1,10**4),F(1,10**6),F(1,10**5)]
''',
75: r'''def candidate(dc,ec):
 c,rows=center(float(dc),float(ec),H0,N0,P0,False);v=[]
 assert all(row[2]==S or(S==[0,1,2]and row[2]==[0,1,2,3])for row,S in zip(rows,WORD))
 for k in range(2):
  us=[]
  for sg in(-1,1):
   dd=float(dc)+sg*1e-7*(k==0);ee=float(ec)+sg*1e-7*(k==1)
   us.append(center(dd,ee,H0,N0,P0,False)[0])
  v.append([F(str((y-x)/2e-7))for x,y in zip(*us)])
 return[F(str(x))for x in c],list(zip(*v)),[row[0]for row in rows]
''',
76: r'''def verify(dl,du,el,eu,r=BASE,verbose=True):
 dc=(dl+du)/2;ec=(el+eu)/2;hd=(du-dl)/2;he=(eu-el)/2;c,v,seeds=candidate(dc,ec);widths=r+[hd,he]
 b=[Jet(Iv.box(c[i],r[i]+abs(v[i][0])*hd+abs(v[i][1])*he),[Iv(int(i==j))for j in I]+[Iv(x)for x in v[i]])for i in I]
 bp=[Jet(x)for x in c];d=Jet(Iv.box(dc,hd),[Iv(0)]*4+[Iv(1),Iv(0)]);e=Jet(Iv.box(ec,he),[Iv(0)]*5+[Iv(1)])
 dp=Jet(dc);ep=Jet(ec);paths=[(b,bp,'')];selected={''};minq=D;links=0;maxlinklip=0
 for phase,S in enumerate(WORD):
  optional=S==[0,1,2];records=[];next_selected=set()
  for b,bp,history in paths:
   try:modes=alternatives(b,bp,d,e,dp,ep,seeds[phase],S,optional,widths)
   except Exception as ex:raise AssertionError(('branch failure',phase,history,str(ex)))from ex
   if history in selected:
    possible={z[4]for z in modes}
    if len(possible)>1:
     _,_,gp,_,_=branch(S,bp,dp,ep,seeds[phase])
     if gp[3].v.hi<0:possible={'q'}
     elif gp[3].v.lo>0:possible={'f'}
    next_selected.update(history+mode for mode in possible)
   for out,op,q,qp,mode in modes:records.append((out,op,q,qp,mode,history,I if mode=='f'else S))
  nl,ll=common_link(paths,records,d,e,seeds[phase],S,optional,dp,ep,widths);links+=nl;maxlinklip=max(maxlinklip,ll)
  new=[]
  for out,op,q,qp,mode,history,support in records:
   # Three persistent owners remain physical, including on signed full extensions.
   assert min(q[i].lo for i in S)*10**7>D
   minq=min(minq,*(q[i].lo for i in S))
   for i in I:
    rad=sum(mag(out[i].d[j])*r[j]for j in I)+mag(out[i].d[4])*hd+mag(out[i].d[5])*he
    rg=around(op[i].v,rad);out[i].v=Iv(max(out[i].v.lo,rg.lo),min(out[i].v.hi,rg.hi),True)
    assert out[i].v.lo<=out[i].v.hi
   new.append((out,op,history+mode))
  paths=new;selected=next_selected;assert selected;assert len(paths)<=16
  if verbose and(phase in(2,3,4,9,17,33)or len(records)>1 and phase<12):print('PHASE',phase,'histories',len(paths),'links',links,'link lip',maxlinklip,flush=True)
 # Only the actual selected centre return anchors the final glued return.
 # Unselected histories retain their own anchors in every preceding stage.
 cap=[];param=[]
 for b,bp,history in paths:
  cap.append([sum(mag(x)*r[j]for j,x in enumerate(row.d[:4]))for row in b])
  param.append([mag(b[i].d[4]-v[i][0])*hd+mag(b[i].d[5]-v[i][1])*he for i in I])
 central=[max(mag(bp[i].v-c[i])for b,bp,h in paths if h in selected)for i in I]
 L=[max(z[i]for z in cap)/r[i]for i in I]
 B=[max(a[i]+z[i]for a,z in zip(cap,param))for i in I]
 R=[central[i]+max(z[i]for z in param)for i in I]
 assert max(L)<1
 assert all(central[i]+B[i]<r[i]for i in I),('selected return failure',list(map(float,L)),[float(x/rr)for x,rr in zip(R,r)], [float((central[i]+B[i])/r[i])for i in I])
 stats=[(max(L),max(x/rr for x,rr in zip(R,r)))]
 print('PASS',dl,du,el,eu,'histories',len(paths),'possible centre histories',len(selected),'stats',[(float(a),float(b))for a,b in stats],'persistent q>',float(F(minq,D)),'links',links,'maxlinklip',maxlinklip,flush=True)
 return stats,F(minq,D),len(paths),links,maxlinklip
''',
77: r'''def setword(h,n,p):
 global H0,N0,P0,WORD
 H0=h;N0=n;P0=p;WORD=[[0,1,3]]*h+[[0,1,2]]*n+[[0,2,3]]*p
''',
78: r'''def audit_qjac():
 from itertools import product
 for q0 in product((F(0),F(1)),repeat=4):
  for d,e in product((F(0),F(1)),repeat=2):
   for k in range(5):
    b=[F(int(i==k))for i in I];actual=qjac(q0,b,d,e)
    for j in I:
     q=list(q0);q[j]=F(0);lo=raw_evaluate(q,b,d,e)[3]
     q[j]=F(1);hi=raw_evaluate(q,b,d,e)[3]
     assert [actual[i][j]for i in I]==[y-x for x,y in zip(lo,hi)]
 print('PASS exact raw-table hazard-Jacobian identity',flush=True)
''',
79: r'''def ranking(dc,ec,n,p):
 ranked=[]
 for h in (1,2,3):
  try:
   c,rows=center(float(dc),float(ec),h,n,p,False)
   physical=min([q[i]for q,g,S,b,bo in rows for i in S]+[1-q[i]for q,g,S,b,bo in rows for i in S]+[-g[i]for q,g,S,b,bo in rows for i in I if i not in S])
   if physical<=0:continue
   invnorm=0.
   for q,g,S,b,bo in rows:
    gg,AA=float_gap_jac(q,b,float(dc),float(ec));C=float_inverse([[AA[i][j]for j in S]for i in S])
    invnorm=max(invnorm,max(sum(abs(x)for x in row)for row in C))
   score=invnorm*(1+.001/physical)
   ranked.append((score,h,physical,invnorm))
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError):continue
 return sorted(ranked)
''',
80: r'''COUNT=FAILS=ATTEMPTS=0
''',
81: r'''START=time.monotonic()
''',
82: r'''SEARCH_BASE=[BASE[0],BASE[1],5*BASE[2],BASE[3]]
''',
83: r'''def attempt(dl,du,el,eu,n,p):
 global ATTEMPTS
 import contextlib,io
 scale=max((du-dl)/F(1,500),(eu-el)/F(1,100));rank=ranking((dl+du)/2,(el+eu)/2,n,p)
 reasons=[]
 for score,h,physical,invnorm in rank:
  setword(h,n,p);r=[4*scale*x for x in SEARCH_BASE]
  for k in range(3):
   ATTEMPTS+=1
   assert ATTEMPTS<100000 and time.monotonic()-START<14400,('budget',ATTEMPTS,COUNT)
   try:
    with contextlib.redirect_stdout(io.StringIO()):result=verify(dl,du,el,eu,r,False)
    return result,(h,n,p),r,reasons
   except(AssertionError,ValueError,ZeroDivisionError,OverflowError)as ex:
    reason=ex.args[0] if ex.args else ''
    reasons.append((h,str(reason)))
    if isinstance(reason,tuple)and reason[0]=='selected return failure':
     # Floating diagnostics only propose larger rational coordinate radii.
     r=[rr*max(F(1),F(str(1.5*ratio)))for rr,ratio in zip(r,reason[3])]
    else:break
 return None,None,None,reasons
''',
84: r'''def cover(dl,du,el,eu,n,p,depth=0):
 global COUNT,FAILS
 result,word,r,reasons=attempt(dl,du,el,eu,n,p)
 if result is not None:
  COUNT+=1
  print('ACCEPT',COUNT,'fails',FAILS,'cell',*[str(x)for x in(dl,du,el,eu)],'word',word,'histories',result[2],'maxL',float(max(z[0]for z in result[0])),'maxR',float(max(z[1]for z in result[0])),'seconds',int(time.monotonic()-START),flush=True)
  return
 FAILS+=1
 print('REJECT',FAILS,'depth',depth,'cell',*[str(x)for x in(dl,du,el,eu)],'reasons',reasons,flush=True)
 assert depth<24,('subdivision limit',dl,du,el,eu,reasons)
 if du-dl>=2*(eu-el):
  dm=(dl+du)/2;cover(dl,dm,el,eu,n,p,depth+1);cover(dm,du,el,eu,n,p,depth+1)
 else:
  em=(el+eu)/2;cover(dl,du,el,em,n,p,depth+1);cover(dl,du,em,eu,n,p,depth+1)
''',
85: r'''def np_for(dl):
 if dl<F('.17'):return 6,24
 if dl<F('.25'):return 5,24
 if dl<F('.34'):return 5,20
 if dl<F('.46'):return 4,16
 if dl<F('.64'):return 3,16
 return 2,14
''',
86: r'''
# Candidate-only floating clones. None of these helpers accepts a certificate.
from types import FunctionType
_FLOAT_GLOBALS=dict(globals())
for _name,_value in list(_FLOAT_GLOBALS.items()):
 if _name.startswith('C_'):_FLOAT_GLOBALS[_name]=float(_value)
_FLOAT_A=[[float(x)for x in row]for row in A]
_FLOAT_DD={}
for _S in ((0,1,3),(0,1,2),(0,2,3)):
 for _a in _S:
  _u,_v=[x for x in _S if x!=_a];_mask=(1<<_u)|(1<<_v)
  _FLOAT_DD[_a,_u,_v]=float(Z[_a,_mask|(1<<_a)]-Z[_a,_mask])
''',
87: r'''def _float_triple_fast(b,S,d,e):
 i,j,k=S
 def cf(a,u,v):
  au=-d if(a,u)==(2,0)else(-e if(a,u)==(3,1)else _FLOAT_A[a][u])
  av=-d if(a,v)==(2,0)else(-e if(a,v)==(3,1)else _FLOAT_A[a][v])
  dd=_FLOAT_DD[a,min(u,v),max(u,v)]
  return-b[a],b[a]-au,b[a]-av,dd+au+av-b[a]
 ci,ai,bi,di=cf(i,j,k);cj,aj,bj,dj=cf(j,i,k);ck,ak,bk,dk=cf(k,i,j)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 def mul2(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
 terms=[mul2(dx,dy),mul2(nx,dy),mul2(ny,dx),mul2(nx,ny)]
 cc=[sum(t[l]*x for t,x in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 from math import sqrt
 zz=(-cc[1]+sqrt(cc[1]*cc[1]-4*cc[2]*cc[0]))/(2*cc[2]);q=[0.]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 return q
''',
88: r'''for _name in ('evaluate','gaps','float_gap_jac','float_newton','center'):
 _original=_FLOAT_GLOBALS[_name]
 _FLOAT_GLOBALS[_name]=FunctionType(_original.__code__,_FLOAT_GLOBALS,_name,_original.__defaults__)
''',
89: r'''_FLOAT_GLOBALS['float_triple']=_float_triple_fast
center=_FLOAT_GLOBALS['center']
float_gap_jac=_FLOAT_GLOBALS['float_gap_jac']
float_newton=_FLOAT_GLOBALS['float_newton']
''',
90: r'''if __name__=='__main__':
 import hashlib
 START=time.monotonic()
 print('SOURCE_SHA256',hashlib.sha256(open(__file__,'rb').read()).hexdigest(),flush=True)
 audit_horner();audit_qjac()
 if '--pilot' in sys.argv:
  passed=0;count=0
  for dl in map(F,('.12','.2','.3','.4','.5','.6','.68')):
   n,p=np_for(dl)
   for el,eu in ((F(0),F('.01')),(F('.3'),F('.31')),(F('.68'),F('.69')),(F('.69'),F('.70')),(F('.70'),F('.71')),(F('.738')+F('.06')*dl-F('.01'),F('.738')+F('.06')*(dl+F('.01')))):
    count+=1;res,word,r,reasons=attempt(dl,dl+F('.01'),el,eu,n,p);passed+=res is not None
    print('PILOT',count,'PASS'if res is not None else'FAIL',*[str(x)for x in(dl,dl+F('.01'),el,eu)],'word',word,'reasons',reasons,flush=True)
  print('PILOT_COMPLETE',passed,count,'attempts',ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
 else:
  assert sys.argv[1:] in ([],['--continue-16']),'No undocumented run mode'
  first=16 if sys.argv[1:]==['--continue-16']else 12
  for j in range(first,70):
   dl=F(j,100);du=F(j+1,100);top=F('.738')+F('.06')*du;n,p=np_for(dl)
   el=F(0)
   while el<top:
    if j<16:step=F('.01')
    elif el<F('.32'):step=F('.04')
    elif el<F('.60'):step=F('.02')
    else:step=F('.01')
    eu=min(el+step,top);cover(dl,du,el,eu,n,p);el=eu
   print('PASS_SLAB',dl,du,'epsilon 0 to',top,'cells',COUNT,'fails',FAILS,'attempts',ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
  print('PASS COMPLETE MIDDLE SEGMENT','delta',F(first,100),F(7,10),'epsilon[0,.738+.06delta]',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
''',
91: r'''"""Exact graph certificates for the high two-row region; period at most18.
Target delta[6/5,3/2], epsilon[0,737/1000+3 delta/50+1/10000].
A completed full-cover run is required; partial/pilot runs prove only their cells.
Standard library only. Floats propose; all acceptance uses exact intervals.
"""
''',
92: r'''def alternatives(b,bp,d,e,dp,ep,seed,S,optional,widths):
 graph=(bp,dp,ep,widths)
 oq,qq,gq,Gq,lq=branch(S,b,d,e,seed,graph=graph);op,qp,gp,_,_=branch(S,bp,dp,ep,seed)
 assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,qq)), 'quiet graph anchor linkage'
 for i in I:
  rg=around(gp[i].v,sum(mag(z)*w for z,w in zip(gq[i].d,widths)))
  gq[i].v=Iv(max(gq[i].v.lo,rg.lo),min(gq[i].v.hi,rg.hi),True)
  assert gq[i].v.lo<=gq[i].v.hi
 if not optional or gq[3].v.hi<0:
  assert all(qq[i].lo>0 and qq[i].hi<D for i in S)
  assert all(gq[i].v.hi<0 for i in I if i not in S)
  modes=[(oq,op,qq,qp,'q')]
 else:
  of,qf,gf,Gf,lf=branch([0,1,2,3],b,d,e,seed,graph=graph);ofp,qfp,_,_,_=branch([0,1,2,3],bp,dp,ep,seed)
  if gq[3].v.lo>0 and qf[3].lo>0:
   # Strict full selection needs physicality only for its selected full root.
   # The auxiliary quiet root retains its anchor and uniqueness obligations.
   assert all(qf[i].lo>0 and qf[i].hi<D for i in I)
   modes=[(of,ofp,qf,qfp,'f')]
  else:
   assert all(min(qq[i].lo,qf[i].lo)>0 and max(qq[i].hi,qf[i].hi)<D for i in S)
   assert qf[3].hi<D
   y=hull(Iv(0),qf[3]);fixed=[Iv(0)]*3+[y]
   bridge,Gb,ib,lb=rootbox(S,[x.v for x in b],d.v,e.v,seed,fixed,[hull(x,y)for x,y in zip(qq,qf)],graph=(b,d,e,*graph))
   assert all(bridge[i].lo<=qf[i].lo and qf[i].hi<=bridge[i].hi for i in S)
   schur=Gb[3][3]-sum(Gb[3][i]*x for i,x in zip(S,mv(ib,[Gb[i][3]for i in S])))
   assert schur.hi<0,('bad Schur',schur)
   modes=[(oq,op,qq,qp,'q'),(of,ofp,qf,qfp,'f')]
 for _,_,q,qp,_ in modes:assert all(y.lo<=x.lo and x.hi<=y.hi for x,y in zip(qp,q))
 return modes
''',
93: r'''def audit_horner():
 # All expressions are visibly multiaffine in q,b,delta,epsilon. The full
 # hazard/parameter vertex grid and b=0 plus four coordinate directions
 # therefore prove equality of the two exact polynomial evaluators.
 from itertools import product
 for q in product((F(0),F(1)),repeat=4):
  for d,e in product((F(0),F(1)),repeat=2):
   for k in range(5):
    b=[F(int(i==k))for i in I]
    old=raw_evaluate(q,b,d,e);new=evaluate(q,b,d,e)
    assert old==new
    assert old[3]==gaps(q,b,d,e)
    jac=qjac(q,b,d,e)
    for j in I:
     qlo=list(q);qhi=list(q);qlo[j]=F(0);qhi[j]=F(1)
     glo=raw_evaluate(qlo,b,d,e)[3];ghi=raw_evaluate(qhi,b,d,e)[3]
     assert [jac[i][j]for i in I]==[y-x for x,y in zip(glo,ghi)]
 print('PASS exact raw-table/Horner and hazard-Jacobian polynomial identities',flush=True)
''',
94: r'''N0=1;P0=8
''',
95: r'''BASE=[F(1,10**5),F(1,10**4),F(1,10**5),F(1,10**5)]
CALENDARS=[(n,p)for n in(1,2)for p in range(8,15)if 2+n+p<=18]
''',
96: r'''def setword(n,p):
 global N0,P0,WORD
 N0=n;P0=p;WORD=[[0,1,3]]*2+[[0,1,2]]*n+[[0,2,3]]*p
''',
97: r'''def ranked_calendars(dc,ec):
 candidates=[]
 for n,p in CALENDARS:
  try:
   c,rows=center(float(dc),float(ec),n,p,False)
   margins=[]
   for q,g,S,b,out in rows:
    margins.extend(min(q[i],1-q[i])for i in S)
    margins.extend(-g[i]for i in I if i not in S)
   residual=max(abs(x-y)for x,y in zip(rows[0][3],c))
   if min(margins)>0 and residual<1e-10:
    candidates.append((min(margins),n,p))
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError):pass
 return[(n,p)for margin,n,p in sorted(candidates,reverse=True)[:3]]
''',
98: r'''def candidate(dc,ec):
 c,rows=center(float(dc),float(ec),N0,P0,False);v=[]
 assert all(row[2]==S or(S==[0,1,2]and row[2]==[0,1,2,3])for row,S in zip(rows,WORD))
 for k in range(2):
  us=[]
  for sg in(-1,1):
   dd=float(dc)+sg*1e-7*(k==0);ee=float(ec)+sg*1e-7*(k==1)
   us.append(center(dd,ee,N0,P0,False)[0])
  v.append([F(str((y-x)/2e-7))for x,y in zip(*us)])
 return[F(str(x))for x in c],list(zip(*v)),[row[0]for row in rows]
''',
99: r'''MAX_PERIOD=0
''',
100: r'''def cover(dl,du,el,eu,depth=0):
 global COUNT,FAILS,ATTEMPTS,MAX_PERIOD
 scale=max((du-dl)/F(1,500),(eu-el)/F(1,100))
 result=None;reason='no numerically viable calendar'
 for n,p in ranked_calendars((dl+du)/2,(el+eu)/2):
  setword(n,p)
  for k in(1,4,16,64):
   ATTEMPTS+=1
   assert ATTEMPTS<=30000 and time.monotonic()-START<5400,('budget',ATTEMPTS,COUNT,dl,du,el,eu)
   try:
    import contextlib,io
    with contextlib.redirect_stdout(io.StringIO()):result=verify(dl,du,el,eu,[k*scale*x for x in BASE],False)
    break
   except(AssertionError,ValueError,ZeroDivisionError,OverflowError)as ex:
    reason=str(ex)
    if not ('return failure' in reason):break
  if result is not None:break
 if result is not None:
  COUNT+=1;MAX_PERIOD=max(MAX_PERIOD,len(WORD))
  print('ACCEPT',COUNT,'fails',FAILS,'cell',*[float(x)for x in(dl,du,el,eu)],'calendar',N0,P0,'histories',result[2],'maxL',float(max(z[0]for z in result[0])),'maxR',float(max(z[1]for z in result[0])),'seconds',int(time.monotonic()-START),flush=True)
  return
 FAILS+=1
 if depth>=24:raise AssertionError(('subdivision limit',dl,du,el,eu,reason))
 if du-dl>=2*(eu-el):
  dm=(dl+du)/2;cover(dl,dm,el,eu,depth+1);cover(dm,du,el,eu,depth+1)
 else:
  em=(el+eu)/2;cover(dl,du,el,em,depth+1);cover(dl,du,em,eu,depth+1)
''',
101: r'''def tile(k):
 dl=F(120+k,100);du=F(121+k,100)
 # The slab's right-edge ceiling dominates the sloped target on the whole tile.
 top=F(737,1000)+F(3,50)*du+F(1,10000)
 edges=[F(j,50)for j in range(15)]
 edges.extend(F(j,100)for j in range(29,84)if F(j,100)<top)
 edges.append(top)
 for el,eu in zip(edges,edges[1:]):cover(dl,du,el,eu)
 print('TILE',k,'complete',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
''',
102: r'''if __name__=='__main__':
 START=time.monotonic();audit_horner()
 for k in range(30):tile(k)
 print('PASS COMPLETE HIGH REGION delta[1.2,1.5], epsilon[0,.737+.06delta+.0001]',COUNT,FAILS,ATTEMPTS,'maximum period',MAX_PERIOD,'seconds',time.monotonic()-START,flush=True)
''',
103: r'''"""Low-delta exact graph continuation pilots; inherited complete-history kernel.
Target delta [.002,.12] below the stationary frontier.
A completed full-cover run is required; partial/pilot runs prove only their cells.
Standard library only. Floats propose; all acceptance uses exact intervals.
"""
''',
104: r'''def float_gap_jac(q,b,d,e):
 return gaps(q,b,d,e),qjac(q,b,d,e)
''',
105: r'''H0=2;N0=8;P0=24
WORD=[[0,1,3]]*2+[[0,1,2]]*8+[[0,2,3]]*P0
''',
106: r'''_CANDIDATE_KEY=None
_CANDIDATE_VALUE=None
def candidate(dc,ec):
 global _CANDIDATE_KEY,_CANDIDATE_VALUE
 key=(H0,N0,P0,dc,ec)
 if key==_CANDIDATE_KEY:return _CANDIDATE_VALUE
 c,rows=center(float(dc),float(ec),H0,N0,P0,False);v=[]
 assert all(row[2]==S or(S==[0,1,2]and row[2]==[0,1,2,3])for row,S in zip(rows,WORD))
 for k in range(2):
  us=[]
  for sg in(-1,1):
   dd=float(dc)+sg*1e-7*(k==0);ee=float(ec)+sg*1e-7*(k==1)
   us.append(center(dd,ee,H0,N0,P0,False)[0])
  v.append([F(str((y-x)/2e-7))for x,y in zip(*us)])
 _CANDIDATE_KEY=key
 _CANDIDATE_VALUE=([F(str(x))for x in c],list(zip(*v)),[row[0]for row in rows])
 return _CANDIDATE_VALUE
''',
107: r'''def verify(dl,du,el,eu,r=BASE,verbose=True):
 dc=(dl+du)/2;ec=(el+eu)/2;hd=(du-dl)/2;he=(eu-el)/2;c,v,seeds=candidate(dc,ec);widths=r+[hd,he]
 b=[Jet(Iv.box(c[i],r[i]+abs(v[i][0])*hd+abs(v[i][1])*he),[Iv(int(i==j))for j in I]+[Iv(x)for x in v[i]])for i in I]
 bp=[Jet(x)for x in c];d=Jet(Iv.box(dc,hd),[Iv(0)]*4+[Iv(1),Iv(0)]);e=Jet(Iv.box(ec,he),[Iv(0)]*5+[Iv(1)])
 dp=Jet(dc);ep=Jet(ec);paths=[(b,bp,'')];selected={''};minq=D;links=0;maxlinklip=0
 for phase,S in enumerate(WORD):
  optional=S==[0,1,2];records=[];next_selected=set()
  for b,bp,history in paths:
   try:modes=alternatives(b,bp,d,e,dp,ep,seeds[phase],S,optional,widths)
   except Exception as ex:raise AssertionError(('branch failure',phase,history,str(ex)))from ex
   if history in selected:
    possible={z[4]for z in modes}
    if len(possible)>1:
     _,_,gp,_,_=branch(S,bp,dp,ep,seeds[phase])
     if gp[3].v.hi<0:possible={'q'}
     elif gp[3].v.lo>0:possible={'f'}
    next_selected.update(history+mode for mode in possible)
   for out,op,q,qp,mode in modes:records.append((out,op,q,qp,mode,history,I if mode=='f'else S))
  nl,ll=common_link(paths,records,d,e,seeds[phase],S,optional,dp,ep,widths);links+=nl;maxlinklip=max(maxlinklip,ll)
  new=[]
  for out,op,q,qp,mode,history,support in records:
   # Three persistent owners remain physical, including on signed full extensions.
   assert min(q[i].lo for i in S)*10**7>D
   minq=min(minq,*(q[i].lo for i in S))
   for i in I:
    rad=sum(mag(out[i].d[j])*r[j]for j in I)+mag(out[i].d[4])*hd+mag(out[i].d[5])*he
    rg=around(op[i].v,rad);out[i].v=Iv(max(out[i].v.lo,rg.lo),min(out[i].v.hi,rg.hi),True)
    assert out[i].v.lo<=out[i].v.hi
   new.append((out,op,history+mode))
  paths=new;selected=next_selected;assert selected;assert len(paths)<=16
  if verbose and(phase in(2,3,4,9,17,33)or len(records)>1 and phase<12):print('PHASE',phase,'histories',len(paths),'links',links,'link lip',maxlinklip,flush=True)
 # Only the actual selected centre return anchors the final glued return.
 # Unselected histories retain their own anchors in every preceding stage.
 cap=[];param=[]
 for b,bp,history in paths:
  cap.append([sum(mag(x)*r[j]for j,x in enumerate(row.d[:4]))for row in b])
  param.append([mag(b[i].d[4]-v[i][0])*hd+mag(b[i].d[5]-v[i][1])*he for i in I])
 central=[max(mag(bp[i].v-c[i])for b,bp,h in paths if h in selected)for i in I]
 L=[max(z[i]for z in cap)/r[i]for i in I]
 B=[max(a[i]+z[i]for a,z in zip(cap,param))for i in I]
 R=[central[i]+max(z[i]for z in param)for i in I]
 assert max(L)<1,('return contraction',list(map(float,L)),[float((central[i]+B[i])/r[i])for i in I])
 assert all(central[i]+B[i]<r[i]for i in I),('selected return failure',list(map(float,L)),[float(x/rr)for x,rr in zip(R,r)], [float((central[i]+B[i])/r[i])for i in I])
 stats=[(max(L),max(x/rr for x,rr in zip(R,r)))]
 print('PASS',dl,du,el,eu,'histories',len(paths),'possible centre histories',len(selected),'stats',[(float(a),float(b))for a,b in stats],'persistent q>',float(F(minq,D)),'links',links,'maxlinklip',maxlinklip,flush=True)
 return stats,F(minq,D),len(paths),links,maxlinklip
''',
108: r'''def float_return(c,d,e):
 c=list(c)
 for S in WORD:
  q=float_triple(c,S,d,e);P,Q,H,g=evaluate(q,c,d,e)
  if S==[0,1,2]and g[3]>0:
   q,_=float_newton([0,1,2,3],q,c,d,e);S=[0,1,2,3];P,Q,H,g=evaluate(q,c,d,e)
  c=[Q[i]if i in S else Q[i]-g[i]for i in I]
 return c
''',
109: r'''def proposed_radii(dl,du,el,eu):
 # Only proposes positive rational radii. All acceptance remains in verify().
 dc=(dl+du)/2;ec=(el+eu)/2;c,v,seeds=candidate(dc,ec)
 cf=list(map(float,c));vf=[list(map(float,row))for row in v]
 columns=[]
 for j in I:
  step=max(abs(cf[j])*1e-5,1e-9);lo=cf[:];hi=cf[:]
  lo[j]-=step;hi[j]+=step
  fl=float_return(lo,float(dc),float(ec));fh=float_return(hi,float(dc),float(ec))
  columns.append([(y-x)/(2*step)for x,y in zip(fl,fh)])
 derivative=list(map(list,zip(*columns)))
 error=[1e-12]*4
 for dd in(dl,du):
  for ee in(el,eu):
   affine=[cf[i]+vf[i][0]*float(dd-dc)+vf[i][1]*float(ee-ec)for i in I]
   returned=float_return(affine,float(dd),float(ee))
   error=[max(a,abs(x-y))for a,x,y in zip(error,affine,returned)]
 inverse=float_inverse([[float(i==j)-abs(derivative[i][j])for j in I]for i in I])
 radius=mv(inverse,error)
 assert all(x>0 for x in radius),('radius proposal',radius)
 return [F(str(max(2*x,1e-11)))for x in radius]
''',
110: r'''def numerical_score(h,n,p,dc,ec):
 setword(h,n,p)
 c,rows=center(float(dc),float(ec),h,n,p,False)
 assert max(abs(x-y)for x,y in zip(rows[0][3],c))<1e-10
 margins=[];condition=0
 for q,g,S,b,out in rows:
  margins.extend(min(q[i],1-q[i])for i in S)
  margins.extend(-g[i]for i in I if i not in S)
  jac=qjac(q,b,float(dc),float(ec))
  inv=float_inverse([[jac[i][j]for j in S]for i in S])
  condition=max(condition,max(sum(abs(x)for x in row)for row in inv))
 assert min(margins)>0,('numerical physical',min(margins))
 return min(margins)/max(condition,1)
''',
111: r'''def exact_attempt(cell,word):
 import contextlib,io
 setword(*word)
 radius=proposed_radii(*cell)
 for k in range(4):
  try:
   with contextlib.redirect_stdout(io.StringIO()):
    result=verify(*cell,radius,False)
   return result,radius,k+1
  except AssertionError as ex:
   info=ex.args[0]if ex.args else None
   if isinstance(info,tuple)and info[0]in('selected return failure','return contraction'):
    ratios=info[-1]
    radius=[max(r,F(str(1.3*x))*r)for r,x in zip(radius,ratios)]
   else:raise
 raise AssertionError(('radius retries',word,list(map(float,radius)),info))

# Finite initial delta partition, in descending order. The extra h choices
# alter only the proposal calendar; every selected phase is checked exactly.
BANDS=[(F(a),F(b),n,p)for a,b,n,p in[
 ('.08','.12',8,24),('.058','.08',9,24),('.04','.058',12,24),('.032','.04',13,24),
 ('.024','.032',16,24),('.016','.024',19,16),('.0105','.016',21,16),
 ('.008','.0105',27,12),('.006','.008',30,12),('.0048','.006',34,8),
 ('.004','.0048',39,8),('.0032','.004',42,8),('.002','.0032',48,8)]]
COUNT=FAILS=ATTEMPTS=MAX_PERIOD=0
START=0
MIN_PERSISTENT=F(1)
MAX_CONTRACTION=F(0)
MAX_RETURN_RATIO=F(0)
MAX_HISTORIES=1
LAST_REPORT=0
''',
112: r'''def ranked_calendars(dc,ec,n,p,extended=False):
 # Candidate-only neighbors at every scale, without a Cartesian n/p expansion.
 families=[(n,p)]if ec<F(3,5)else[(n-2,p),(n-1,p),(n,p),(n+1,p),(n+2,p),(n,p-4),(n,p+4)]
 ranked=[]
 for h in(1,2,3,4):
  for nn,pp in families:
   if nn<1 or pp<0:continue
   word=(h,nn,pp)
   try:ranked.append((numerical_score(*word,dc,ec),word))
   except(AssertionError,ValueError,ZeroDivisionError,OverflowError):pass
 return[word for score,word in sorted(ranked,reverse=True)]
''',
113: r'''def cover(dl,du,el,eu,n,p,depth=0):
 global COUNT,FAILS,ATTEMPTS,MAX_PERIOD,MIN_PERSISTENT,MAX_CONTRACTION,MAX_RETURN_RATIO,MAX_HISTORIES,LAST_REPORT
 assert time.monotonic()-START<7200 and ATTEMPTS<20000,('budget',COUNT,FAILS,ATTEMPTS)
 dc=(dl+du)/2;ec=(el+eu)/2
 extended=(du-dl)<dc/20 and(eu-el)<F(1,250)
 words=ranked_calendars(dc,ec,n,p,extended)
 result=None;reason='no numerically viable calendar'
 for word in words[:4]:
  ATTEMPTS+=1
  try:
   result,radius,tries=exact_attempt((dl,du,el,eu),word)
   break
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError)as ex:reason=str(ex)
 if result is not None:
  COUNT+=1;MAX_PERIOD=max(MAX_PERIOD,len(WORD));MIN_PERSISTENT=min(MIN_PERSISTENT,result[1])
  MAX_CONTRACTION=max(MAX_CONTRACTION,result[0][0][0]);MAX_RETURN_RATIO=max(MAX_RETURN_RATIO,result[0][0][1]);MAX_HISTORIES=max(MAX_HISTORIES,result[2])
  if time.monotonic()-LAST_REPORT>=30:
   print('PROGRESS',COUNT,FAILS,ATTEMPTS,'max_period',MAX_PERIOD,'max_histories',MAX_HISTORIES,'seconds',int(time.monotonic()-START),flush=True);LAST_REPORT=time.monotonic()
  return
 FAILS+=1
 assert depth<24,('subdivision limit',dl,du,el,eu,n,p,reason)
 # Rescale delta by its positive center when choosing only the split axis.
 # Both closed children are always verified, so this does not alter coverage.
 if(du-dl)>=2*dc*(eu-el):
  dm=(dl+du)/2;cover(dl,dm,el,eu,n,p,depth+1);cover(dm,du,el,eu,n,p,depth+1)
 else:
  em=(el+eu)/2;cover(dl,du,el,em,n,p,depth+1);cover(dl,du,em,eu,n,p,depth+1)
''',
114: r'''def band(k):
 dl,du,n,p=BANDS[k]
 top=F(737,1000)+F(3,50)*du+F(1,10000)
 edges=[F(j,50)for j in range(37)]+[top]
 assert edges[-2]<top
 print('BEGIN_BAND',k,str(dl),str(du),'epsilon_top',str(top),flush=True)
 for j,(el,eu)in enumerate(zip(edges,edges[1:])):
  cover(dl,du,el,eu,n,p)
  print('PASS_CLOSED_EPSILON_SLICE',k,j,str(dl),str(du),str(el),str(eu),'cumulative',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
 print('PASS_CLOSED_BAND',k,str(dl),str(du),'epsilon_top',str(top),'cumulative',COUNT,FAILS,ATTEMPTS,'seconds',time.monotonic()-START,flush=True)
''',
115: r'''for _name in ('evaluate','gaps','qjac','float_gap_jac','float_newton','center'):
 _original=_FLOAT_GLOBALS[_name]
 _FLOAT_GLOBALS[_name]=FunctionType(_original.__code__,_FLOAT_GLOBALS,_name,_original.__defaults__)
''',
116: r'''
# Original frozen proposal order, selected only by --baseline-proposals.
def _baseline_ranked_calendars(dc,ec,n,p,extended=False):
 words=[(h,n,p)for h in(1,2,3,4)]
 if extended:
  words.extend((h,nn,pp)for h in(1,2,3,4)for nn,pp in[(n-1,p),(n+1,p),(n,p+4)])
 ranked=[]
 for word in words:
  try:ranked.append((numerical_score(*word,dc,ec),word))
  except(AssertionError,ValueError,ZeroDivisionError,OverflowError):pass
 return[word for score,word in sorted(ranked,reverse=True)]
''',
117: r'''if __name__=='__main__':
 import argparse,hashlib
 parser=argparse.ArgumentParser();group=parser.add_mutually_exclusive_group()
 group.add_argument('--band',type=int,default=None);group.add_argument('--start-band',type=int,default=0)
 parser.add_argument('--end-band',type=int,default=None)
 parser.add_argument('--baseline-proposals',action='store_true',help='use the original frozen calendar ranking (for baseline band 0)')
 args=parser.parse_args()
 if args.baseline_proposals:ranked_calendars=_baseline_ranked_calendars
 START=LAST_REPORT=time.monotonic()
 print('SOURCE_SHA256',hashlib.sha256(open(__file__,'rb').read()).hexdigest(),flush=True)
 print('PROPOSAL_MODE','baseline'if args.baseline_proposals else 'v4',flush=True)
 audit_horner()
 assert BANDS[0][1]==F(3,25)and BANDS[-1][0]==F(1,500)
 assert all(a[0]==b[1]for a,b in zip(BANDS,BANDS[1:]))
 if args.band is not None:
  assert args.end_band is None
  assert 0<=args.band<len(BANDS);band(args.band)
  print('PASS SINGLE LOW BAND ONLY',args.band,flush=True)
 else:
  end_band=12 if args.end_band is None else args.end_band
  assert 0<=args.start_band<=end_band<len(BANDS)
  for k in range(args.start_band,end_band+1):band(k)
  marker='PASS COMPLETE LOW REGION'if(args.start_band,end_band)==(0,12)else 'PASS LOW BANDS '+str(args.start_band)+'..'+str(end_band)
  scope='delta['+str(BANDS[end_band][0])+','+str(BANDS[args.start_band][1])+'], epsilon[0,.737+.06delta+.0001]'
  print(marker,scope,COUNT,FAILS,ATTEMPTS,'maximum period',MAX_PERIOD,'minimum persistent hazard',float(MIN_PERSISTENT),'max contraction',float(MAX_CONTRACTION),'max return ratio',float(MAX_RETURN_RATIO),'max histories',MAX_HISTORIES,'seconds',time.monotonic()-START,flush=True)
''',
118: r'''"""Exact affine stationary frontier for the two-row complex-spectrum family.
Proves delta in [0,38/25], epsilon in [737/1000+3delta/50,2].
Python3 plus SymPy, NumPy, SciPy. No external data files.
Floats only propose rational candidates. Every acceptance uses exact rational
coefficients or outward dyadic integer intervals.
"""
''',
119: r'''BITS=256;D=1<<BITS
''',
120: r'''class Jet:
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
''',
121: r'''import sys
m=sys.modules[__name__]
R=F
I=range(3)
''',
122: r'''def fields(v,x,delta):
 q=[v[0],v[1],x,v[2]];out=[]
 for a in range(4):
  opp=[i for i in range(4)if i!=a];H=m.Jet(1);P=m.Jet(0);Q=m.Jet(0)
  for i in opp:H*=1-q[i]
  for mask in range(16):
   if mask>>a&1:continue
   w=m.Jet(1)
   for i in opp:w*=q[i]if mask>>i&1 else 1-q[i]
   pv=m.Z.get((a,mask),R(0));qv=m.Z[a,mask|(1<<a)]
   if a==2 and mask==1:pv=-R(9,10)*delta;qv=delta/10
   # epsilon=0 base, rather than original epsilon=1/25.
   if a==3 and mask==2:pv=0;qv=0
   if mask:P+=w*pv
   Q+=w*qv
  out.append((1-H)*Q-P)
 return out
''',
123: r'''def solve(a,b):
 rows=[list(v)+[w]for v,w in zip(a,b)]
 for j in I:
  k=next(k for k in range(j,3)if rows[k][j]);rows[j],rows[k]=rows[k],rows[j]
  t=rows[j][j];rows[j]=[u/t for u in rows[j]]
  for k in I:
   if k==j:continue
   t=rows[k][j];rows[k]=[u-t*v for u,v in zip(rows[k],rows[j])]
 return [row[-1]for row in rows]
''',
124: r'''def ev(c,x,d):
 return fields([m.Jet(v,[m.Iv(int(i==j))for j in range(5)])for i,v in enumerate(c)],m.Jet(x,[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)]),m.Jet(d,[m.Iv(0)]*4+[m.Iv(1)]))
def roundrat(v):return R((v.numerator*10**24)//v.denominator,10**24)
# Floating solves propose rational candidates only; interval tests establish every claim.
import numpy as np
from scipy.optimize import root
import sympy as sy
_p0,_p1,_xx,_yy,_dd,_ee=sy.symbols('p0 p1 x y D E')
_qq=[_p0,_p1,_xx,_yy]
_zz={key:sy.Rational(value.numerator,value.denominator)for key,value in Z.items()}
_zz[2,1]=-sy.Rational(9,10)*_dd;_zz[2,5]=_dd/10
_zz[3,2]=-sy.Rational(9,10)*_ee;_zz[3,10]=_ee/10
_sf=[]
for _i in range(4):
 _op=[_j for _j in range(4)if _j!=_i]
 _H=sy.prod(1-_qq[_j]for _j in _op);_P=sy.Rational(0);_Q=sy.Rational(0)
 for _mask in range(16):
  if _mask>>_i&1:continue
  _weight=sy.prod(_qq[_j]if _mask>>_j&1 else 1-_qq[_j]for _j in _op)
  _P+=_weight*_zz.get((_i,_mask),sy.Rational(0))
  _Q+=_weight*_zz[_i,_mask|(1<<_i)]
 _sf.append(sy.expand((1-_H)*_Q-_P))
_ctx={'F':_sf,'p0':_p0,'p1':_p1,'x':_xx,'y':_yy,'D':_dd,'E':_ee}
''',
125: r'''_sf=_ctx['F'];_p0=_ctx['p0'];_p1=_ctx['p1'];_xx=_ctx['x'];_yy=_ctx['y'];_dd=_ctx['D'];_ee=_ctx['E']
_recovered=sy.Matrix(_sf[:3]).subs(_ee,0).subs(_xx,_xx-sy.Rational(3,100)*_dd)
_nf=sy.lambdify((_p0,_p1,_yy,_xx,_dd),_recovered,'numpy')
_nj=sy.lambdify((_p0,_p1,_yy,_xx,_dd),_recovered.jacobian([_p0,_p1,_yy]),'numpy')
# Exact Horner evaluation of the literal stationary polynomials.
def _horner(expr,variables):
 if not variables:
  a=sy.Rational(expr);return 'R(%d,%d)'%(a.p,a.q)
 var=variables[0];poly=sy.Poly(expr,var);out=None
 for coefficient in poly.all_coeffs():
  ss=_horner(coefficient,variables[1:])
  if out is None:out=ss
  else:out='('+out+'*'+str(var)+'+'+ss+')'
 return out
_horner_functions=[]
for _expr in _sf:
 _code=_horner(_expr.subs(_ee,0),[_p0,_p1,_xx,_yy,_dd])
 _horner_functions.append(eval('lambda p0,p1,x,y,D: '+_code,{'R':R}))
_fields_literal=fields
def fields(v,x,delta):
 return [ff(v[0],v[1],x-R(3,100)*delta,v[2],delta)for ff in _horner_functions]
''',
126: r'''def candidate(x,d,seed):
 so=root(lambda v:np.array(_nf(*v,float(x),float(d))).ravel(),[float(v)for v in seed],jac=lambda v:_nj(*v,float(x),float(d)),tol=1e-11)
 c=[R(str(v))for v in so.x]
 mid=lambda v:R(v.lo+v.hi,2*m.D)
 ff=ev(c,x,d);jj=[[mid(ff[a].d[j])for j in I]for a in I]
 cols=[solve(jj,[R(int(i==j))for i in I])for j in I]
 B=[[cols[j][i]for j in I]for i in I]
 S=[solve(jj,[-mid(ff[a].d[3+k])for a in I])for k in range(2)]
 S=[[roundrat(v)for v in col]for col in S]
 return c,S,B
''',
127: r'''class Poly2:
 def __init__(self,v):self.c={k:R(a)for k,a in v.items()if a}if isinstance(v,dict)else({(0,0):R(v)}if v else{})
 def __add__(self,o):
  o=o if isinstance(o,Poly2)else Poly2(o);d=self.c.copy()
  for k,v in o.c.items():d[k]=d.get(k,R(0))+v
  return Poly2(d)
 __radd__=__add__
 def __neg__(self):return Poly2({k:-v for k,v in self.c.items()})
 def __sub__(self,o):return self+-o
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  o=o if isinstance(o,Poly2)else Poly2(o);d={}
  for (i,j),a in self.c.items():
   for (k,l),b in o.c.items():d[i+k,j+l]=d.get((i+k,j+l),R(0))+a*b
  return Poly2(d)
 __rmul__=__mul__
 def absbound(self):return sum(abs(v)for v in self.c.values())
''',
128: r'''def verify(l,u,dl,du,prev=None,radius=R(1,200)):
 xm=(l+u)/2;hx=(u-l)/2;dm=(dl+du)/2;hd=(du-dl)/2
 assert 0<l-R(3,100)*du<=u-R(3,100)*dl<1
 seed=[R('.14'),R('.2'),R('.1')+dm/10]if prev is None else[prev['c'][i]+prev['S'][0][i]*(xm-prev['xm'])for i in I]
 c,S,Br=candidate(xm,dm,seed);B=[[m.Iv(t)for t in row]for row in Br];weights=[R(1,10)+abs(S[0][i])+abs(S[1][i])for i in I];r=[radius*w/max(weights)for w in weights]
 v=[m.Jet(m.Iv.box(c[i],r[i]+abs(S[0][i])*hx+abs(S[1][i])*hd),[m.Iv(int(i==j))for j in range(5)])for i in I]
 for a in v:assert 0<a.v.lo<a.v.hi<m.D,('proper',float(l),float(dl),c)
 ff=fields(v,m.Jet(m.Iv.box(xm,hx),[m.Iv(0)]*3+[m.Iv(1),m.Iv(0)]),m.Jet(m.Iv.box(dm,hd),[m.Iv(0)]*4+[m.Iv(1)]))
 K=[[m.Iv(int(i==j))-sum((B[i][k]*ff[k].d[j]for k in I),m.Iv(0))for j in I]for i in I]
 pc=[Poly2({(0,0):c[i],(1,0):S[0][i]*hx,(0,1):S[1][i]*hd})for i in I]
 pf=fields(pc,Poly2({(0,0):xm,(1,0):hx}),Poly2({(0,0):dm,(0,1):hd}))
 RR=[sum((-Br[i][k]*pf[k]for k in I),Poly2(0)).absbound()for i in I]
 MM=[sum(R(K[i][j].absupper(),m.D)*r[j]for j in I)for i in I]
 lip=max(MM[i]/r[i]for i in I)
 assert lip<R(1,2),('lip',float(l),float(dl),float(lip))
 assert all(RR[i]+MM[i]/4<r[i]/4 for i in I),('inner',float(l),float(dl),[float((RR[i]+MM[i]/4)/r[i])for i in I])
 if prev:
  gap=[abs(c[i]+S[0][i]*(l-xm)-prev['c'][i]-prev['S'][0][i]*(l-prev['xm']))+abs(S[1][i]-prev['S'][1][i])*hd+prev['r'][i]/4 for i in I]
  assert all(gap[i]<r[i]for i in I),('seam',float(l),float(dl))
 return dict(c=c,S=S,B=B,r=r,xm=xm,dm=dm,hx=hx,hd=hd,dl=dl,du=du,l=l,u=u,lip=lip)
''',
129: r'''def epsilon_at(cell,x):
 v=[m.Jet(m.Iv.box(cell['c'][i]+cell['S'][0][i]*(x-cell['xm']),cell['r'][i]/4+abs(cell['S'][1][i])*cell['hd']))for i in I]
 f=fields(v,m.Jet(x),m.Jet(m.Iv.box(cell['dm'],cell['hd'])))[3].v
 qx=m.Iv(x)-R(3,100)*m.Iv.box(cell['dm'],cell['hd'])
 H=(1-v[0].v)*(1-v[1].v)*(1-qx)
 coef=(1-H/10)*v[1].v*(1-v[0].v)*(1-qx)
 assert coef.lo>0
 return -f/coef
''',
130: r'''def refined_left(first):
 dl=first['dl'];du=first['du'];worst=R(0);count=0
 while dl<du:
  end=min(du,dl+R(1,500));tiny=verify(R(11,100),R(11,100),dl,end,None,R(1,100000))
  dm=tiny['dm'];hd=tiny['hd']
  for i in I:
   parent=first['c'][i]+first['S'][0][i]*(R(11,100)-first['xm'])+first['S'][1][i]*(dm-first['dm'])
   gap=abs(tiny['c'][i]-parent)+abs(tiny['S'][1][i]-first['S'][1][i])*hd+tiny['r'][i]/4
   assert gap<first['r'][i],('endpoint_identification',float(dl))
  el=epsilon_at(tiny,R(11,100));target=R(737,1000)+R(3,50)*dl
  assert R(el.hi,m.D)<target,('sharp_left',float(dl),el,float(target))
  worst=max(worst,R(el.hi,m.D)-R(3,50)*dl);dl=end;count+=1
 return worst,count
''',
131: r'''if __name__=='__main__':
 start=time.time();count=0;finecount=0;dl=R(0);top=R(38,25);worst=R(0);maxleft=R(-10);minright=R(100)
 while dl<top:
  dd=R(1,50)if dl<R(1)else(R(1,100)if dl<R(7,5)else R(1,500))
  du=min(top,dl+dd);l=R(11,100);prev=None;first=None;slabcount=0
  while l<R(2,5):
   dx=R(1,200);passed=False
   while not passed:
    u=min(R(2,5),l+dx)
    for radius in [R(1,100),R(1,200),R(1,400),R(1,800),R(1,1600),R(1,3200)]:
     try:
      cell=verify(l,u,dl,du,prev,radius);passed=True;break
     except AssertionError:pass
    if not passed:
     dx/=2
     assert dx>=R(1,102400),('excessive refinement',float(l),float(dl))
   prev=cell;first=first or cell;l=u;count+=1;slabcount+=1;worst=max(worst,cell['lip'])
  el,nn=refined_left(first);finecount+=nn;er=epsilon_at(prev,R(2,5))
  assert er.lo>2*m.D,('right_eps',float(dl),er)
  maxleft=max(maxleft,el);minright=min(minright,R(er.lo,m.D))
  print('PASS_SLAB',float(dl),float(du),'cells',slabcount,count,'eps_offset_upper',float(el),'right',er,'seconds',time.time()-start,flush=True)
  dl=du
 print('PASS_ALL',count,'endpointcells',finecount,'maxlip',float(worst),'epsilon_offset_upper',float(maxleft),'right_lower',float(minright),'seconds',time.time()-start)
''',
132: r'''"""Exact audit of the raw stationary producer and its geometric boundary tests.
Requires SymPy. No numerical candidate, tolerance, imported packet, or saved tree.
"""
''',
133: r'''import itertools
''',
134: r'''from fractions import Fraction as Q
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
''',
135: r'''"""Exact stationary exclusion at delta=1/8, epsilon=139/200.

Standard library only. Run without -O; high.py must be in the same directory.
The imported, hash-pinned periodic checker supplies the independently audited
raw payoff polynomials, dyadic intervals, automatic derivatives and a floating
inverse proposal. Floating values never decide exclusion.
The associated proof justifies discarding boxes with sum(q)<1/50000.
"""
if not __debug__:
    raise RuntimeError('Assertions are required; do not use -O.')
import hashlib
import importlib.util
''',
136: r'''from pathlib import Path
''',
137: r'''SOURCE = Path(__file__).with_name('high.py')
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == (
    '5c02cd160f440388a6357e4d0b8756c36b6bffd403ed50c3412f420f178fe9eb')
spec = importlib.util.spec_from_file_location('two_row_certificate', SOURCE)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
DELTA, EPSILON = F(1, 8), F(139, 200)
''',
138: r'''def origin_audit():
    z = m.rewards(DELTA, EPSILON)
    assert len(z) == 60 and all(abs(x) <= 6 for x in z.values())
    gamma = [[F(0) if i == j else z[i, 1 << j] for j in range(4)]
             for i in range(4)]
    a = [row + [F(i == j) for j in range(4)]
         for i, row in enumerate(gamma)]
    for k in range(4):
        j = next(j for j in range(k, 4) if a[j][k])
        a[k], a[j] = a[j], a[k]
        pivot = a[k][k]
        a[k] = [x / pivot for x in a[k]]
        for i in range(4):
            if i != k:
                factor = a[i][k]
                a[i] = [x - factor*y for x, y in zip(a[i], a[k])]
    inv = [row[4:] for row in a]
    assert all(sum(gamma[i][k]*inv[k][j] for k in range(4)) == (i == j)
               for i in range(4) for j in range(4))
    assert all(x > F(1, 125) for row in inv for x in row)
    assert all(sum(row) < 5 for row in inv)
    assert all(sum(col) < 5 for col in zip(*inv))
    print('PASS EXACT ORIGIN CONSTANTS', flush=True)
''',
139: r'''def field(q):
    p, offer, h, _ = m.evaluate(q, [0]*4, DELTA, EPSILON)
    return [(1-h[i])*offer[i]-p[i] for i in range(4)]
''',
140: r'''def newton_excludes(status, box, q):
    free = [i for i, st in enumerate(status) if st == 2]
    if not free:
        return False
    jq = [m.Jet(x, [m.Iv(int(i == j)) for j in range(6)])
          for i, x in enumerate(q)]
    jf = field(jq)
    jac = [[jf[i].d[j] for j in free] for i in free]
    try:
        proposal = m.float_inverse(
            [[float(F(v.lo+v.hi, 2*m.D)) for v in row] for row in jac])
        c = [[F(x) for x in row] for row in proposal]
    except (AssertionError, ZeroDivisionError, ValueError, OverflowError):
        return False
    center = [(lo+hi)/2 for lo, hi in box]
    fc = field(center)
    for k, i in enumerate(free):
        image = m.Iv(center[i]-sum(c[k][v]*fc[j] for v, j in enumerate(free)))
        for l, j in enumerate(free):
            derivative = int(k == l)-sum(c[k][v]*jac[v][l] for v in range(len(free)))
            image += derivative*m.Iv.box(0, (box[j][1]-box[j][0])/2)
        if image.hi < m.Iv(box[i][0]).lo or image.lo > m.Iv(box[i][1]).hi:
            return True
    return False
''',
141: r'''def main():
    m.audit_horner()
    origin_audit()
    start = time.monotonic()
    stack = []
    for status in itertools.product((0, 1, 2), repeat=4):
        box = tuple((F(0), F(1)) if st == 2 else (F(st), F(st)) for st in status)
        stack.append((status, box))
    seen = signs = newton = origin = splits = 0
    while stack:
        assert time.monotonic()-start < 600 and seen < 1000000, 'Incomplete cover'
        status, box = stack.pop()
        seen += 1
        if sum(hi for lo, hi in box) < F(1, 50000):
            origin += 1
            continue
        q = [m.Iv.box((lo+hi)/2, (hi-lo)/2) for lo, hi in box]
        values = field(q)
        if any((st == 2 and not values[i].lo <= 0 <= values[i].hi)
               or (st == 0 and values[i].lo > 0)
               or (st == 1 and values[i].hi < 0) for i, st in enumerate(status)):
            signs += 1
            continue
        if newton_excludes(status, box, q):
            newton += 1
            continue
        k = max(range(4), key=lambda i: box[i][1]-box[i][0])
        lo, hi = box[k]
        assert hi > lo, ('Unexcluded pure profile', status)
        mid = (lo+hi)/2
        left, right = list(box), list(box)
        left[k], right[k] = (lo, mid), (mid, hi)
        stack.extend([(status, tuple(right)), (status, tuple(left))])
        splits += 1
    assert signs+newton+origin-splits == 81
    print('PASS COMPLETE STATIONARY EXCLUSION', 'boxes', seen, 'sign', signs,
          'Newton', newton, 'origin', origin, 'splits', splits,
          'seconds', time.monotonic()-start, flush=True)
''',
142: r'''if __name__ == '__main__':
    main()
''',
}

SOURCES = {
'corner.py': (
    (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 8, 12, 8, 13, 8, 14, 8, 15, 8, 16, 8, 17, 8, 18, 8, 19, 8, 20, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 8, 42, 43, 44, 10, 45, 8, 46, 8, 47, 10, 48, 8, 49, 10, 50, 8, 51, 8, 52, 8, 53, 10, 54, 10, 55),
    'a7ca99c74294ff248292722745e46335b5460a4c0a0df7728bb8792b7e023a70'),
'upper.py': (
    (56, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 57, 8, 12, 8, 13, 8, 14, 8, 15, 8, 17, 8, 18, 8, 19, 8, 20, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 8, 42, 10, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 8, 44, 10, 45, 8, 46, 10, 58, 8, 59, 8, 60, 8, 61, 62, 63, 8, 64, 8, 65, 8, 54, 66, 8, 67, 8, 68),
    'ef2eec38bd2213f7368208e8e5a1af9334302f8ff73ecea199c2a377c3de37b5'),
'middle.py': (
    (69, 70, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 8, 12, 8, 13, 8, 14, 8, 15, 8, 17, 8, 18, 8, 19, 8, 20, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 8, 42, 43, 44, 10, 71, 10, 46, 8, 47, 10, 48, 8, 72, 8, 51, 8, 52, 8, 54, 10, 73, 74, 8, 75, 8, 76, 8, 77, 43, 78, 8, 79, 8, 80, 81, 82, 8, 83, 8, 84, 8, 85, 86, 8, 87, 8, 88, 89, 8, 90),
    '2eb5aa22e2f612bbdce35837aee77d1947862c45688e78b26dea86dc5ac8abf7'),
'high.py': (
    (91, 70, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 8, 12, 8, 13, 8, 14, 8, 15, 8, 17, 8, 18, 8, 19, 8, 20, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 8, 42, 43, 44, 10, 71, 8, 46, 8, 47, 10, 48, 8, 60, 92, 8, 51, 8, 52, 8, 93, 10, 94, 62, 95, 10, 96, 10, 97, 10, 98, 8, 76, 8, 80, 99, 81, 8, 100, 8, 101, 8, 102),
    '5c02cd160f440388a6357e4d0b8756c36b6bffd403ed50c3412f420f178fe9eb'),
'low.py': (
    (103, 70, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 8, 12, 8, 104, 8, 14, 8, 15, 8, 17, 8, 18, 8, 19, 8, 20, 8, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 8, 42, 43, 44, 10, 71, 8, 46, 8, 47, 10, 48, 8, 72, 8, 51, 8, 52, 8, 93, 10, 105, 74, 8, 106, 8, 107, 8, 77, 8, 108, 8, 109, 8, 110, 8, 111, 8, 112, 8, 113, 8, 114, 86, 8, 87, 8, 115, 89, 116, 8, 117, 8),
    '1e2fd801e32a4d060d39b1d1831fd1ba01de88299721f64dba34f73ce6de5e8f'),
'affine.py': (
    (118, 1, 2, 3, 119, 5, 120, 7, 8, 9, 10, 121, 8, 122, 8, 123, 8, 124, 8, 125, 8, 126, 8, 127, 8, 128, 8, 129, 8, 130, 8, 131),
    'd1695483f9210cd76c5703d9d98a8791cc02eec316bfb38bdd89c3a7203e1e8b'),
'dominated.py': (
    (132, 133, 134, 8),
    '184ed1ab596a5b55f3ba07bcd2af9f054e104d5f78d7cace74aacd6c7c9cd4bc'),
'stationary.py': (
    (135, 133, 3, 1, 136, 8, 137, 10, 138, 10, 139, 10, 140, 10, 141, 10, 142),
    '0484f4023f40ddc58bee60a14486ecf8e5eade4ebe562eea6108f4be25722e44'),
}

def extract(destination):
    destination.mkdir(parents=True, exist_ok=True)
    for name, (pieces, digest) in SOURCES.items():
        source = ''.join(BLOCKS[piece] for piece in pieces).encode('utf-8')
        assert hashlib.sha256(source).hexdigest() == digest
        target = destination / name
        if target.exists() and target.read_bytes() != source:
            raise RuntimeError('Refusing to overwrite different file: ' + str(target))
        target.write_bytes(source)
    print('Extracted eight complete checkers into', destination)

if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: python bundle.py DIRECTORY')
    extract(Path(sys.argv[1]))
```

## Adapter, consumer and Lean handoff

The actual-data adapter is the explicit sixty-entry reward formula with four
row offsets. The certificate obligations are exact polynomial identities,
closed interval inequalities, complete binary subdivision, graph-root
uniqueness and a strict return contraction. A formalization should first
separate the candidate-producing floating search from these rational checks.
It can then formalize a parameter-cell validator and its finite cover fold,
with a soundness theorem producing actual cyclic endpoint-Nash data.
No desired equilibrium conclusion should be included as an input field.

For the stationary regions, feed the produced hazards and actual fixed payoff
into the stationary endpoint consumer named above. For periodic regions,
formalize the finite phase Bellman equations and opponent-deletion absorption;
the supermartingale/truncation argument proves exact terminal Nash against
all behavioral replacements. Its bounded absorption time gives one fixed
uniform payoff directly, or exact terminal Nash may be supplied at every
positive error to the existing terminal-to-uniform equivalence. Large epsilon
uses the named bare-no-UE singleton theorem and the two-row contradiction.

## Scope and nonclaims

The theorem covers the explicit family, not all Fin4 reward tables or all
positive-collision games. It does not classify every stationary root, supply
a globally continuous equilibrium selector over the parameter quadrant, or
bound the period of a witness outside the displayed constructive regions.
It allows arbitrary fixed signed offsets, but gives no common payoff or horizon
bound over unbounded reward magnitudes. The stationary boundary test excludes
stationary strategies only and is compatible with the periodic UE constructed
at the same point. Qualitative existence of unspecified neighborhoods around
other tables does not by itself certify membership of this whole family;
no geometric disjointness from every such neighborhood is claimed.
