# Positive inverse and sparse triple rewards produce stationary equilibrium

Status: ordinary mathematical theorem and proof, not Lean-checked.
Sections1--8 give a four-player triple-reward
producer; Section10 proves its arbitrary-finite-player extension, including
different coalition sizes with their corresponding reward scales. The
construction is global in the singleton data and positive jackpot ratios.
It requires neither a supplied strategic witness nor a nonsingular zero
of the limiting nonlinear field.

## 1. Self-contained question and raw-table theorem

There are four players I={0,1,2,3}. At each live date their private seeds
are independent. The first nonempty simultaneous quitting coalition S
pays the finite vector r(S); live payoff and Never are zero. A unilateral
deviation replaces the player's COMPLETE behavioral law, including any
finite deadline, Never and their arbitrary private mixtures. All payoffs
and caps below are in expectation.

Fix arbitrary finite singleton rows. Write s_i=r_i({i}) and

    Gamma_ii=0,    Gamma_ij=r_i({j})-s_i  for j!=i.

Assume Gamma is invertible and EVERY entry of A=Gamma^(-1) is strictly
positive. No sign restriction is imposed on the singleton rows themselves.
Fix a mate involution m=(0 1)(2 3), put C_i=I\{i,m(i)} and
J_i=I\{m(i)}. Thus J_i contains recipient i and exactly two opponents.
Fix any four strictly positive numbers a_i.

Question. Does this matrix condition alone, with no local reference matrix
or limiting-root regularity assumption, produce stationary Nash when only
the four rewards r_i(J_i) grow at these prescribed positive ratios?

Theorem. For EVERY such singleton table, EVERY a in(0,infinity)^4 and
EVERY finite R>=0, there is a finite threshold M0 such that for EVERY
M>M0 and EVERY original reward table with those singleton rows and

    r_i(J_i)=M*a_i+c_i,       |c_i|<=R,
    |r_i(S)|<=R for every other nonsingleton coordinate(S,i),

there is an actual full-support stationary terminal Nash profile against
ALL complete unilateral behavioral replacements. Its actual payoff is
one fixed original-game uniform-equilibrium payoff; the SAME profile
works at every positive accuracy and all sufficiently long horizons.
The four hazards have the form q_i=z_i/sqrt(M), with z in a positive
compact set depending only on the singleton rows and a, not on M or the
bounded nonsingleton parameters. Neither M nor the reward table varies
with the requested equilibrium accuracy.

Uniform version. If the singleton rows and a range over ANY compact
subset of the displayed open conditions A_ij>0 and a_i>0, one threshold
M0 works for that entire compact set and the entire bounded reward box.

The four large coordinates are (023,0),(123,1),(012,2),(013,3).
They are recipient-specific; no other coordinate of these triples is
required to be large or even nonnegative.

## 2. Actual values and the exact finite-M polynomial

For q in(0,1)^4 and A_opp subset I\{i}, let p_i(A_opp) be its product
opponent coalition probability. Define

    alpha_i=p_i(empty),
    Q_i=sum_Aopp p_i(A_opp) r_i(A_opp+i),
    B_i=sum_(Aopp nonempty) p_i(A_opp) r_i(A_opp),
    H_i=(1-alpha_i)Q_i-B_i.

The actual stationary policy value is

    U_i=[q_i Q_i+(1-q_i)B_i]/[1-(1-q_i)alpha_i].       (1)

Its pure-Quit-minus-Continue difference is exactly

    Q_i-B_i-alpha_i U_i=H_i/[1-(1-q_i)alpha_i].       (2)

Put t=M^(-1/2), q_i=t z_i and let d denote the forty-four bounded
nonsingleton parameters. Recipient i's sole unbounded Q_i term is

    p_i(C_i)(M*a_i+c_i)
      =a_i z_j z_k(1-t z_mate(i))
        +t^2 c_i z_j z_k(1-t z_mate(i)),  C_i={j,k}. (3)

Thus Q_i is polynomial through t=0. No jackpot enters B_i, since its
only unbounded recipient coordinate contains i while B_i samples
coalitions absent i. Both B_i and1-alpha_i are divisible by t.
Consequently Phi_i=H_i/t extends polynomially through t=0, with

    Phi_i(0,z)=a_i P_i(z)-(Gamma z)_i,
    P_i(z)=(sum_(j!=i) z_j) product_(j in C_i) z_j.    (4)

All bounded nonsingleton parameters disappear from this leading field.
There is therefore an EXACT polynomial E, not merely an asymptotic
remainder, such that

    Phi(t,z,d)=diag(a)P(z)-Gamma z+t E(t,z,d).          (5)

E also depends continuously on the fixed singleton rows and a. Define

    F_(t,d)(z)=A[diag(a)P(z)+t E(t,z,d)].              (6)

Because A=Gamma^(-1), a fixed point of(6) is equivalent to Phi=0.
The task is to produce this fixed point of the EXACT perturbed field.

## 3. A compact interior direction cone

Let b=min_(i,j) A_ij>0 and B=max_(i,j) A_ij, and put

    kappa=b/(8B),
    K={x in R^4: sum_i x_i=1 and x_i>=kappa for every i}.

Since0<kappa<=1/8, K is nonempty, compact and convex. For ANY nonzero
coordinatewise nonnegative vector w, every coordinate of A w is at
least b*sum_j w_j, while its total mass is at most4B*sum_j w_j. Hence

    (A w)_i / sum_l(A w)_l >= b/(4B)=2kappa.          (7)

Thus normalized positive images lie in K, even in its strict inner part.
This is the only use of strict inverse positivity. It is a uniform
geometric fact, not a selected limiting eigenvector.

Each P_i is homogeneous of degree3. It is strictly positive on K because
all its three factors are positive. Therefore

    g(x)=sum_i [A diag(a)P(x)]_i

has finite extrema0<g_min<=g_max on K. Choose0<ell<u so that

    ell^2*g_max<1/2,       u^2*g_min>2.               (8)

Such radii exist by taking ell small and u large. The shell

    Z={rho*x: x in K, ell<=rho<=u}

is compact and contained in the positive orthant. At t=0, homogeneity
gives sum_i F_(0,d)(rho*x)_i=rho^3*g(x), independently of d. Thus
the field strictly compresses mass on the inner radius and strictly
expands it on the outer radius.

## 4. The perturbation keeps the entire shell and radial barriers

On Z every coordinate of diag(a)P(z) has a positive minimum. For
example P_i(z)>=3*kappa^3*ell^3. E is uniformly bounded on

    [0,1] x Z x [-R,R]^44.

It follows that for EVERY sufficiently small t>=0, uniformly over ALL
d in the cube, the vector

    w(t,z,d)=diag(a)P(z)+t E(t,z,d)

is strictly positive for every z in Z. Equation(7) then gives

    F_(t,d)(rho*x) / sum_i F_(t,d)(rho*x)_i in K.      (9)

Uniform continuity on the same compact set and the strict margins in(8)
also give, after choosing a common smaller t0>0,

    sum_i F_(t,d)(ell*x)_i < ell,
    sum_i F_(t,d)(u*x)_i > u                         (10)

for every x in K, every d in the cube and every0<=t<t0. The same t0
ensures t*u<1. No positivity of E, cancellation of a signed error or
convexity of the attainable product-law set is assumed.

## 5. An exact global fixed point, with no regularity hypothesis

Fix0<t<t0 and any d in the bounded cube. For x in K and rho in[ell,u]
write f=F_(t,d)(rho*x) and h=sum_i f_i>0. Let clip denote continuous
projection to the interval[ell,u]. Define the continuous map

    T(x,rho)=(f/h, clip(2rho-h))                     (11)

from the compact convex set K x[ell,u] to itself, using(9). Brouwer
gives a fixed point(x,rho). It cannot have rho=ell: by(10), h<ell, so
2ell-h>ell, and its clipped value is still strictly above ell. Nor can
rho=u: then h>u, so2u-h<u, and its clipped value is strictly below u.
Hence ell<rho<u. The equality clip(2rho-h)=rho at an interior point
forces2rho-h=rho, so h=rho. The direction equation f/h=x now gives

    F_(t,d)(rho*x)=rho*x.

Putting z=rho*x proves Phi(t,z,d)=0 and therefore H(t z)=0. Moreover

    kappa*ell <= z_i <= u,
    0<t*kappa*ell <= q_i=t z_i <1.                   (12)

This is an actual joint private-hazard producer for every permitted
finite table. No limiting root, nonsingular derivative, uniqueness or
degree cancellation assumption was used.

Set M0=t0^(-2), enlarged to5 if desired for the explicit family below.
This proves the stated quantifiers. For the uniform version, continuous
matrix inversion on the supplied compact parameter set gives common
positive b and finite B; a_i also have a common positive minimum and
finite maximum. The same K, uniform positive g_min and finite g_max,
shell and polynomial bounds then supply a common t0. This does not
claim uniformity as an inverse entry or jackpot coefficient tends to0.

## 6. Complete agency and one fixed uniform payoff

For each produced table and profile, (1)--(2) and H=0 imply

    U_i=Q_i=B_i+alpha_i U_i.

All opponents have positive stationary hazards, so alpha_i<1. Every
pure deadline has expected payoff U_i, by iterating this equality, and
Never has payoff B_i/(1-alpha_i)=U_i. An arbitrary complete replacement
law is a private mixture of deadlines and Never on the unique continuing
history, so it cannot improve. Equivalently, Bellman iteration for any
behavioral replacement leaves a bounded remainder times alpha_i^N,
which tends to0 uniformly over that replacement. This proves exact
terminal Nash, not merely restricted stationary Nash.

For the finite-horizon uniform contract, every replacement still faces
the opponents' geometric absorption tail alpha_i^N. If the fixed table's
absolute reward bound is C, the expected finite-average/terminal payoff
discrepancy is bounded by a constant times C times the opponents'
expected absorption time divided by the horizon. This tends uniformly
to0. Prescribed payoff delivery has the same property. Thus the actual
vector U is a fixed original-game uniform-equilibrium target, with no
accuracy-dependent table or strategy needed.

The checked semantic consumers matching these inputs are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
The raw-data production in Sections2--5 is ordinary mathematics here.

## 7. Exact positive and negative tests

The paired singleton example

    r(0)=(1,4,0,0), r(1)=(4,1,0,0),
    r(2)=(0,0,1,4), r(3)=(0,0,4,1)

has

    Gamma=[0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0],
    A=(1/15)[2,7,3,3; 7,2,3,3; 3,3,2,7; 3,3,7,2].

Direct multiplication gives Gamma*A=identity. In particular this strict
positive-inverse example is not a favorable all-positive singleton
matrix. With a=(1,1,1,1), z=(1,1,1,1)/sqrt(3) solves(4). The global
proof also permits arbitrary positive a, such as(1,2,3,4), without
assuming that a chosen cubic root is simple or supplying one.

For a negative test, suppose all own singleton values are1 and every
other singleton value is0. Then Gamma has off-diagonal entries-1.
For ANY positive z and positive a, each coordinate of

    diag(a)P(z)-Gamma z

is strictly positive. Thus there is NO positive root of the leading
field at all. On any fixed positive compact shell the exact small-t
field has no root for small enough t. This falsifies dropping the matrix
hypothesis while keeping this particular positive bounded-z scale; it
does not prove nonexistence of equilibrium at other scales or strategies.

The extension at t=0 is not a physical all-Never equilibrium. In the
positive reference test all-Never earns0 and a singleton deviation earns1.
Only t>0 profiles are produced. Finite bounded R, strict A_ij>0, strictly
positive a_i and a sufficiently large but FIXED finite M are substantive
hypotheses. The proof does not cover large passive-recipient rewards,
which would enter B_i and change its leading field.

## 8. An explicit uncovered subfamily and bounded source comparisons

Use the displayed reference singletons and a_i=1. Let the directed
cross-cycle be succ:0->2->1->3->0. Every pair pays5 to outsiders.
Mate pairs pay-1 to both participants. A directed cross pair
{i,succ(i)} pays-1 to i and2 to succ(i). Triple J_i pays M to i,
-1 to its other two participants and5 to its outsider. The grand row
is(-100,-101,-102,-103). These rules specify all fifteen reward rows.
They belong to the theorem with R=103 and c_i=0 for all sufficiently
large M. Only one recipient in each triple has a large reward.

There is NO exact root Nash with ANY sure quitter and ANY continuation.
With player0 sure, mate1's joining rewards are-1 or its negative grand
coordinate, versus Continue4 or5; thus1 Continues. Then predecessor3
joins for-1 versus Continue0 or5, so3 Continues. Successor2 joins for2
versus Continue0, so2 Quits. Owner0 then withdraws for0 rather than-1,
a contradiction. Rotate along succ for every sure owner. This covers
the whole nonempty persistent-base/free selection, not a chosen free
Nash witness. The actual sure-base preservation adapter is
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

Every nonempty proper child C has an UNSAFE EXACT child equilibrium.
Choose d in C with succ(d) outside C, set d=Quit0 and all other child
players=Never. Owner d gets1 versus0; other child members get0 or4
and joining gives-1. Thus all child debts and joint Never mass vanish.
Outside successor succ(d) gains exactly2 by joining. This excludes
whole-profile quiet certificates bounding outsider debt by weighted
child debts plus joint-Never slack, including the full five-operation
withdrawal/future-join family consumed by
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
It does not exclude favorable selected child profiles without such a
certificate.

The actual insertion-charge condition also fails on the full premium
trap: every player gets2>own1 in its predecessor pair. On mate pair01,
the ABSENT players2 and3 have insertion gains M-5 each. Thus

    quittingTrapLeaveSum(r,I,01)=2(M-5)>0  for M>5.

This contradicts `QuittingTrapChargeCoefficients.leave_nonpos` and
`HasBoxedQuittingNashCharges` in respectively
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
and `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.
The definition of the sum is `quittingWeightedLeaveSum` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`.
For a nonnegative supportwise upper-average alternative put
X=w0+w1,Y=w2+w3. The two mate-pair tests force
(M-1)Y<=2X and(M-1)X<=2Y, hence all weights0 for M>3.

EVERY ordered recipient/partner lower face fails as well. Set the
recipient and partner hazards0 and a sole outsider hazard1. If the
partner is not its mate, choose the mate outsider: H_i=-1-4=-5.
If the partner is its mate, choose successor outsider: H_i=-1-0=-1.
This violates even the broader nonnegative polynomial lower guard,
independently of M and of the ceiling height. Actual definitions are
`QuittingCrossedSourceGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`,
`QuittingHalfWeakPolynomialGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

At all-sure hazards, full response residuals are-105-i, all distinct.
Thus no noninjective block map satisfies
`QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
Every pair has a participant reward-1, so every raw pair-phase premise
requiring both participants positive fails under every relabeling.
Every triple contains a mate pair with both ordered joining gaps-5,
so no selected triple has six positive pair joins.

The existing constant-positive-inverse two-pair odds source is genuinely
different: `exists_positive_odds_of_positive_inverse` in
`MathUE/LinearProgramming/PositiveInverseTwoPairOdds.lean` also requires
nonnegative scheduled participant premiums and nonpositive passive
increments. Every selected pair here contains a participant premium-2;
strict positive inverse alone does NOT meet that source's hypotheses.
The signed inverse-column criterion has, for EACH candidate pair
partition with partner p(i), the necessary conditions

    sigma_i in{-1,1},
    Gamma^(-1)diag(sigma)>0 entrywise,
    sigma_i*[r_i({i,p(i)})-s_i]>=0 for every i.

These cannot hold here: every column of the displayed inverse is strictly
positive, so its sign condition forces sigma_i=+1 for all i. Every
selected pair has a participant premium-1-1=-2, violating the last
necessary inequality. No additional cap or auxiliary-radius choice can
repair the failure of these conditions.

There is also an exact WHOLE-ARCHITECTURE exclusion for the positive
singleton word0,2,1,3 and its mate-preserving relabelings. Each owner's
mate occurs two phases later. For chronological Continue probabilities
u_l in(0,1), the four owner-indifference equations are

    E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0,

with cyclic indices. Put a=u0-u2 and b=u1-u3. Opposite differences give

    E0-E2=4(1-u1)a-u2(4-u0)b,
    E1-E3=u3(4-u1)a+4(1-u2)b.

The determinant is16(1-u1)(1-u2)+u2u3(4-u0)(4-u1)>0, so a=b=0.
Writing u0=u2=x and u1=u3=y, the remaining difference is
(4+xy)(x-y)=0. The common equation factors as

    (u-1)(u^2-3u+1)=0,

whose only root in(0,1) is u=(3-sqrt(5))/2. Thus EVERY positive proper
owner solution of this named word has this common Continue probability,
not only its locally continued branch. Put p=1-u. At an owner's root,
the next nonmate's prescribed value is u and the preceding nonmate's
is1; evaluate the singleton continuation paths using u(4p+u^2)=1.
Either nonmate's immediate-Quit value is u+p*r_i({i,owner}). Hence its
necessary pair cap is respectively0 or1. Every actual cross pair has
a participant reward2, violating a necessary inactive inequality for
either word orientation. This excludes the ENTIRE named positive
singleton-word architecture at the exact singleton rows, including any
positive root selected by an implicit-function theorem with an
unspecified radius. It is not an exclusion of arbitrary calendars.

These are bounded actual-source comparisons, not a universal novelty
survey or a claim that every known supplied-root verifier fails. Any
sound stationary-root verifier may consume the root newly produced here.

## 9. Tracked dependencies and narrow implementation target

The native topological operation in Section5 is already represented by
`Math.exists_fixedPoint_of_normalized_radial_map` in
`MathUE/Topology/NormalizedRadialFixedPoint.lean`, whose exact compact
convex direction, positive mass, normalized image and radial boundary
hypotheses were inspected. That generic result is not new. The new
mathematics is the actual reward-table polynomial field, its invariant
positive-inverse cone, uniform exact-perturbation bounds and unrestricted
game consumer. The nearby positive-coordinate helper and the two-pair
odds source were checked to avoid confusing a reusable topological lemma
with an earlier raw triple-reward producer.

The actual-data implementation target is the exact pole cancellation in
(3)--(6), the positive inverse-entry bounds, common interior simplex,
uniform signed-polynomial perturbation bounds on the compact shell and
the two radial boundary exclusions. These instantiate the named generic
normalized-radial theorem and output an actual positive finite-t root.
Equations(1)--(2) then supply actual value, endpoint equalities and
playerwise deleted contraction to the named semantic consumers. For
Section10 the same implementation uses arbitrary finite products and
the indicated coalition-dependent pole powers; no new topological
theorem is required. No implementation or Lean-checked raw producer is
claimed here.

## 10. Arbitrary finite players and selected participant coalitions

### 10.1. One common coalition size

Theorem. Let I be ANY finite player set of size n>=2. Fix arbitrary
finite singleton rows and define Gamma_ij=r_i({j})-s_i off the zero
diagonal as above. Suppose A=Gamma^(-1) is entrywise strictly positive.
For EACH i choose a coalition S_i containing i of one common size d+1,
where1<=d<=n-1, and choose a_i>0. For every R>=0 there is M0 such that
for every M>M0 and EVERY original table satisfying

    r_i(S_i)=M*a_i+c_i, |c_i|<=R,
    |r_i(S)|<=R on every OTHER nonsingleton coordinate,

there is a full-support stationary exact terminal Nash against all
complete deviations and one fixed same-profile uniform payoff. Hazards
are q_i=M^(-1/d) z_i, with z in a fixed positive compact set. The threshold
is uniform on compact parameter sets of singleton rows and positive a
inside the strict inverse-positive region, with the coalition choices fixed.

Proof. Put t=M^(-1/d), D_i=S_i\{i}. The sole unbounded term of Q_i is

    a_i product_(j in D_i) z_j
          product_(j notin S_i)(1-t z_j)
      +t^d c_i product_(j in D_i) z_j
          product_(j notin S_i)(1-t z_j).

This is polynomial through t=0, whereas B_i has no unbounded term.
Therefore the EXACT field is

    H_i/t=a_i P_i(z)-(Gamma z)_i+t E_i(t,z,ddata),
    P_i(z)=(sum_(j!=i)z_j) product_(j in D_i)z_j.    (13)

P_i is homogeneous of degree d+1 and strictly positive whenever all
coordinates are positive. Here ddata denotes bounded reward parameters,
not the integer coalition-size parameter d.

Let b=min A_ij>0, B=max A_ij and kappa=b/(2nB). The simplex
K={sum x_i=1, x_i>=kappa} is nonempty compact convex because
kappa<=1/(2n). Every normalized positive A-image has coordinates at
least b/(nB)=2kappa. On K the continuous function
g(x)=sum_i[A diag(a)P(x)]_i has0<g_min<=g_max. Choose radii satisfying

    0<ell<u,  ell^d*g_max<1/2,  u^d*g_min>2.

On the positive compact shell ell<=rho<=u the vector diag(a)P(rho*x)
has all coordinates uniformly bounded below by a positive number.
The polynomial E is uniformly bounded over this shell, small t and
the entire finite bounded reward cube. Hence for small enough t the
exact F_t=A[diag(a)P+t E] still has positive preimage vector, normalized
image in K, inner mass<ell and outer mass>u. The identical Brouwer map
(11) gives an interior exact fixed point. Shrink t so t*u<1.

All n hazards are positive, and n>=2, so every deleted-opponent system
contracts. The complete deadline/Never and uniform-payoff proof of
Section6 applies without change. Uniformity on compact parameter sets
follows from common inverse-entry and positive-coefficient bounds.
This proves the theorem, not only a limiting eigenvector statement.

### 10.2. Different coalition sizes with their natural scales

There is also a complete mixed-size version. For each i choose ANY
coalition S_i containing i with size at least2, put d_i=|S_i|-1>=1,
and let L be a common large hazard-scale parameter. Assume

    r_i(S_i)=a_i L^(d_i)+c_i, |c_i|<=R,
    |r_i(S)|<=R on every other nonsingleton coordinate.

For every sufficiently large finite L the same conclusion holds, with
q_i=z_i/L. This includes the equal-size theorem by L=M^(1/d).

Indeed t=1/L cancels the unique t^(-d_i) pole in each Q_i separately.
Equation(13) remains exact with P_i of degree d_i+1, all at least2.
For the same compact simplex define

    g(x)=sum_(i,j) A_ij a_j P_j(x),
    0<g_min<=g(x)<=g_max.

Choose0<ell<1<u with ell*g_max<1/2 and u*g_min>2.
Because all degrees d_j+1 are at least2,

    sum_i F_0(ell*x)_i
       =sum_(i,j) A_ij a_j ell^(d_j+1) P_j(x)
       <=ell^2*g_max<ell/2,
    sum_i F_0(u*x)_i>=u^2*g_min>2u.

Every component diag(a)P is still uniformly positive on the shell.
Thus the exact finite-t correction preserves positivity and both
strict radial barriers, uniformly over the entire bounded cube. The
same map(11) produces an EXACT original-game root and the full consumer
is unchanged. This proof needs no common homogeneous degree, only
that each selected coalition contains its recipient and at least one
opponent. Singleton data and positive a may again range over compact
subsets of the strict matrix region.

These finite-player extensions are raw-table existence classes, not an
assertion that arbitrary original tables possess such reward scales or
strict inverse-positive singleton matrices. In particular they do not
settle the finite-quitting conjecture. The four-player explicit family
in Section8 remains an actual uncovered subfamily of these theorems.
