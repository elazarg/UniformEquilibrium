# Joining-attractive triple premium cores

At every live date finitely many players independently choose Continue
or Quit. The first nonempty quitting coalition S absorbs at the finite
vector r(S), paid thereafter. Live dates and perpetual continuation
pay zero. All public histories and arbitrary independent behavioral
strategies are retained, as are complete unilateral behavioral deviations.
No correlation device, extra information or bounded controller is added.

Let I be finite and let r(S) be every nonempty-coalition reward vector.
Set s_i=r_i({i}). A nonempty A⊆I is a premium trap if every i∈A
has some S⊆A containing i with r_i(S)>s_i. The union of two traps
is a trap, retaining each old witness. Let C be the union of all
traps, or the empty set if there are none. Every trap lies in C,
and nonempty C is itself a trap. This is a finite computation on
the raw table. Assume |C|=3 and, for every i∈C and every
nonempty T⊆C\{i}, assume

    d_i(T):=r_i(T∪{i})−r_i(T) ≥ 0.                  (1)

There is NO sign condition on participant premiums, for core players
or for outsiders, beyond those already entailed by the computed core.
In particular a core player may have negative participant premiums
both inside C and on coalitions involving outsiders. The raw condition
compares joining with being passive, not with one's own singleton.

**Theorem.** In Fin4, if s≥0 and (1) holds, the original game has a
fixed uniform-equilibrium payoff against complete behavioral deviations.
There is one vector u such that, for every ε>0, a profile and one
horizon threshold work at every larger horizon: expected average payoff
is within ε of u and every unilateral expected average payoff is at
most u_i+ε. The target is chosen before accuracy.
No root, continuation value, strategy or degree is supplied as input.
Strict (1), after taking the pure-C equilibrium exit when it exists,
gives selected return at every below-singleton source. With that direct
exit included it excludes a smooth full exact-root potential.
Weak (1) gives UE by a simultaneous reward perturbation, not by an
unproved weak local-index assertion. The statements about roots below
use independent product quitting at one date; the eventual strategic
conclusion has the original independent behavioral information model.

## Strict joining: the support and sure-hazard alternatives

First suppose every difference in (1) is strictly positive. At a
source v and product hazard q∈[0,1]^I, let
μ_q(S)=∏_{i∈S}q_i ∏_{i∉S}(1−q_i). Write c=μ_q(∅), a=1−c and

    w=c v+∑_{S≠∅}μ_q(S)r(S).

The literal forced Quit and Continue endpoints are

    Q_i=∑_{T⊆I\{i}}μ_{−i}(T)r_i(T∪{i}),
    C_i=μ_{−i}(∅)v_i+∑_{∅≠T⊆I\{i}}μ_{−i}(T)r_i(T),

where μ_{−i} is the independent opponents' coalition law. In particular
w_i=q_i Q_i+(1−q_i)C_i. These are actual full-game endpoints.
Exact Nash means w_i≥Q_i,C_i; if q_i>0 then w_i=Q_i. A root is
bad when w_i>s_i for EVERY player. Any nonempty nontrap active
support has a member whose participant rewards on that support are
all at most its singleton, hence has w_i=Q_i≤s_i. Thus a bad root
has trap support A⊆C. No singleton is a trap, so |A|=2 or 3.

For k∉C and T⊆C one has r_k(T∪{k})≤s_k. Otherwise the
core witnesses and this one new witness would make C∪{k} a trap.
Consequently an outside-core player at a bad core-only root has

    Q_k≤s_k<w_k=C_k,                               (2)

so its zero hazard has a STRICT full-game gap. This uses only an
upper bound; there is no protected outsider floor.

If a bad root has one sure core player j, every other i∈C faces
a nonempty opponent coalition T⊆C\{i} with probability one.
Its endpoint difference is an average of the strictly positive
d_i(T), so q_i=1. All of C is then sure. A pure-C exact root at
any source is exact independently of the source: each player has
another sure quitter. It is therefore an actual pure terminal Nash
profile. It also yields w=r(C) at source r(C), with absorption one,
contradicting any positive full-root potential drift.

We may take this direct UE exit first. Otherwise EVERY hazard on a
bad root's active support is strictly between zero and one. This
exhausts partly-sure roots; none is silently included in an interior
Jacobian computation.

## Full local indices for pairs and triples

On a proper-hazard support A put z_j=q_j/(1−q_j). For active i,
divide its endpoint gap g_i=Q_i−C_i by opponent survival. The
exact expression is

    g_i/∏_{j∈A\{i}}(1−q_j)
       =s_i−v_i+∑_{∅≠T⊆A\{i}} d_i(T)∏_{j∈T}z_j. (3)

At an interior root the right side is zero. For a pair A={i,j},
the active gap derivatives are α_i=v_i−s_i+d_i({j})>0 and
α_j>0. Indeed the interior equation gives

    q_j=(v_i−s_i)/(v_i−s_i+d_i({j})),

and strict joining forces v_i>s_i. The active determinant for
q−clip(q+g(q)) is −α_iα_j<0.

For A=C={i,j,k}, let a_ij=∂g_i/∂q_j at the root. Differentiating
(3), including the zero factor multiplying the derivative of the
survival term, gives the exact formula

    a_ij=(1−q_k)/(1−q_j) [d_i({j})+z_k d_i({j,k})]>0. (4)

The gap has no own-coordinate dependence. Hence the three-by-three
active determinant is

    det(−Dg|C)=−(a_ij a_jk a_ki+a_ik a_ji a_kj)<0.  (5)

This is a genuine triple-root sign, not a principal pair calculation.
At a bad triple root all other players are outside C, so (2)
makes their clipped-map rows locally zero. The full matrix
Id−DF, with active coordinates first, has the active block −Dg,
an unrestricted upper-right block, and bottom blocks 0,Id. Thus
(5) is its FULL determinant. Arbitrary simultaneous rewards with
outsiders are included in the upper-right derivatives.

At a pair root, the unused member of C may instead be tied. This
requires a separate genericity step; (2) is not falsely applied to
that player. Write d_i=d_i({j}), d_j=d_j({i}), α_i=v_i−s_i+d_i,
α_j=v_j−s_j+d_j. The unique possible interior pair rates are

    q_i=(v_j−s_j)/α_j,  q_j=(v_i−s_i)/α_i.

For any inactive k, put Δ_k(T)=r_k(T∪{k})−r_k(T). Multiplying
its actual gap by α_iα_j gives

    N_{A,k}(v)=d_i d_j(s_k−v_k)
      +d_i(v_j−s_j)Δ_k({i})+d_j(v_i−s_i)Δ_k({j})
      +(v_i−s_i)(v_j−s_j)Δ_k({i,j}).             (6)

Its v_k coefficient is −d_i d_j≠0. There are finitely many pairs
in C and inactive players. The complement of the union of all their
zero-polynomial loci, and of the harmless α-zero hyperplanes, is
dense and open. To see density without a strategic genericity premise,
take the product of these nonzero real polynomials. A nonzero
polynomial cannot vanish on a nonempty open box, by induction on its
variables. Only annotations, not raw rewards, are perturbed here.

At a generic source every inactive gap of a bad pair root is nonzero,
and Nash makes it strictly negative. Its full local determinant is
therefore also the negative pair determinant, with the same bottom
identity block as above.

## Counting every root and restoring arbitrary sources

Use F_v(q)=clip(q+g(q)) on ALL of ℝ^I. Its image is the unit cube,
and its fixed points are precisely all exact Nash roots. Fix a generic
source v with some v_h<s_h. All Continue is not Nash; every root
absorbs. If no root returned to a singleton sublevel, every root would
be bad, so the preceding calculations apply to EVERY fixed point.
Each is differentiable locally with nonsingular full Id−DF and local
index −1. The fixed-point set is compact. It is finite: an infinite
sequence of distinct roots would accumulate at another root, whereas
its nonsingular derivative makes it locally isolated.

Here the local index equals the sign of the displayed determinant:
invertibility gives ‖Du‖≥m‖u‖, while differentiability makes the
nonlinear remainder at most m‖u‖/2 on a sufficiently small sphere.
The straight homotopy to Du is nonzero there. On the larger cube
(−1,2)^I, homotoping F_v to the constant center never gives a
boundary fixed point, and the total degree of Id−F_v is +1.
Finite disjoint local neighborhoods, excision and degree additivity
would instead give minus the positive number of roots. This contradiction
produces an absorbing exact root with some w_k≤s_k.

For an arbitrary source in a box [−B,B]^I, with B>M:=max|r| and
some coordinate below its singleton, take generic sources in the box's
interior converging to it and preserving that strict deficit. Select
the returning roots just proved. A subsequence converges in the hazard
cube. Endpoint Nash inequalities and the union {some w_k≤s_k} are
closed, so the limiting root has the same return property. It cannot
be all Continue at the original strict-deficit source. The reward bound
and convexity keep its successor in the SAME box. This proves return
at every original below-floor annotation, not only generic annotations.

## The same-domain minimum and the actual Fin4 consumer

For completeness, suppose a differentiable H on the box satisfied

    H(w)+a≤H(v) for every exact root at every boxed source v. (7)

Minimize H on the compact domain

    D={v∈[−B,B]^I : some v_i≤s_i}.

A minimum x with any strict singleton deficit contradicts selected
return and (7). Thus x≥s and at least one coordinate binds.
At every binding coordinate j the exact collision-adjusted solo probe
gives, with g=∇H(x),

    g·(x−r({j}))≥1.                               (8)

Explicitly, set b_j=0; for another binding i set
b_i=max(0,r_i(ij)−r_i(j)); set all nonbinding b_i=0. Use source
x+t b/(1−t) and solo-j hazard t. Every inactive Continue-minus-Quit
gap is

    (1−t)(x_i−s_i)+t[b_i+r_i(j)−r_i(ij)]≥0

for all sufficiently small positive t, and the owner is indifferent.
No upper-box face is moved since it is nonbinding. The successor is
x+t(b+r({j})−x). Divide (7) by t and pass to zero; the b terms
cancel and give (8).

If j were the unique binding coordinate, all other interior derivatives
would vanish and upper-face derivatives would be nonpositive. The
j displacement in (8) is zero, while every upper-face displacement
B−r_i(j) is positive. This contradicts (8). Therefore at least two
coordinates bind. Increasing any one binding coordinate leaves another
binding, so the minimum on D gives g_j≥0 for every binding j.

Fix one such j and put v=x−εe_j. Selected return gives w∈D with
absorption a>0. The two signed estimates are

    Q_j≥s_j−2Ma,   ‖w−v‖∞≤(M+B)a.

The first follows because the chance of nonempty opponents is at
most a and every reward differs from s_j by at most 2M; it uses
no participant-premium sign. Since w_j≥Q_j and v_j=s_j−ε,
these estimates give ε≤(3M+B)a. Minimum and drift now imply

    H(x−εe_j)−H(x)≥a≥ε/(3M+B).

Differentiability would give −g_j≥1/(3M+B)>0, contradicting g_j≥0.
Thus no H as in (7) exists. This part is analytic and works for any
finite I with the stated core size and reward conditions.

For Fin4 and s≥0, all players are normal. If some singleton is positive,
failure of a fixed-target UE supplies the actual rational polynomial
potential on the reward box M+2. Restrict that SAME function to exact
roots and to, for instance, B=M+1; the preceding argument contradicts
it. If every singleton is zero, all Never is directly an exact uniform
equilibrium. This completes the strict raw-data-to-UE implication, not
merely a verifier for a supplied root selection.

For weak (1), lower r_i(T) by δ>0 for every i∈C and nonempty
T⊆C\{i}. These are distinct passive coordinates. No participant
coordinate r_i(S) with i∈S changes, nor does any own singleton.
Consequently EVERY premium trap, and hence the greatest core C, is
exactly preserved. Each compared difference d_i(T) increases by
δ, simultaneously. No participant endpoint in one compared difference
is accidentally changed by another adjustment. The perturbed reward
table is within δ in sup norm, has the same nonnegative singletons,
and satisfies the strict theorem. Arbitrarily close-table UE closure
therefore yields one fixed uniform payoff for the original table.
No assertion about weak-case individual local determinants is needed.

## A rational signed triple-core fixture

Here is a full table with s=(1,0,0,0), M=4:

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (0,2,−1,0) |
| 01 | (0,0,2,−1) |
| 02 | (0,−1,0,2) |
| 03 | (0,2,−1,0) |
| 12 | (−1,0,3,0) |
| 13 | (−1,3,0,0) |
| 23 | (−1,0,0,3) |
| 012 | (0,0,0,3) |
| 013 | (0,0,2,0) |
| 023 | (0,2,0,0) |
| 123 | (−1,4,4,4) |
| 0123 | (0,−2,−2,−2) |

The only trap is C=123. Every row involving pivot 0 has its
participant reward at most s_0=1, so no trap can include it. Each
core pair has one zero and one positive participant premium, so no
pair is a trap. At 123 every participant premium is four. For each
core player the two singleton-joining differences are 1,1 and its
two-opponent joining difference is 4. Thus strict (1) holds.
All four players have negative premiums at the grand row; the
globally protected set is empty.

No pure exit is an equilibrium. For singletons 0,1,2,3, respectively,
players 1,2,1,1 profitably join, each by one. At 01 and 02 pivot 0
withdraws for gain two; at 03 player 2 joins for gain one. At pairs
12,13,23 the omitted core player joins for gain four. At triples
012,013,023, respectively, players 2,1,3 withdraw for gain two.
At 123 pivot 0 joins for gain one. At the grand row player 1
withdraws from −2 to 2. All Never fails by pivot 0's singleton.

The singleton-difference matrix is

    Γ=[[0,1,1,−1],[-1,0,-1,2],
       [-1,2,0,-1],[-1,-1,2,0]].

It is the R=0 cyclic matrix: the child123 inverse is
[[2,4,1],[1,2,4],[4,1,2]]/7, and its actual passive inverse row is
(−1/7,5/7,3/7). At offset (1,−1,−1,−1) the unique LCP root
is (0,1,1,1), active determinant 7 and inactive residual 2. In the
homogeneous problem a positive pivot forces the three child coordinates
equal to it, giving a positive pivot residual; zero pivot forces the
child vector zero. Thus Γ is R₀ of degree one. The other three
principal triple inverses have negative entries −2,−2/3,−2/3,
and the full inverse has row0,column2 entry −5/7. These named
singleton screens do not consume this table.

A response-invariant quotient requires equal singleton block-row sums
for receivers in the same block. The following thirteen partitions fail
that necessary condition; the displayed sums are exact:

| Partition | Receivers | Column block | Sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | 1,−1 |
| 02 / 1 / 3 | 0,2 | 02 | 1,−1 |
| 03 / 1 / 2 | 0,3 | 1 | 1,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 0 / 13 / 2 | 1,3 | 13 | 2,−1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 012 / 3 | 0,1 | 012 | 2,−2 |
| 013 / 2 | 0,1 | 013 | 0,1 |
| 023 / 1 | 0,2 | 023 | 0,−2 |
| 01 / 23 | 0,1 | 01 | 1,−1 |
| 02 / 13 | 0,2 | 02 | 1,−1 |
| 03 / 12 | 0,3 | 12 | 2,1 |
| 0123 | 0,1 | 0123 | 1,0 |

The remaining nondiscrete partition is 0|123. At q=(t,t,t,t), its literal zero-discount response
coordinates satisfy

    F_1=F_2=−t²(3t⁴−7t³+16t−8),
    F_3=F_1−t³,

so that partition also fails for 0<t<1. The asymmetric passive
entry r_3(012)=3 is deliberately retained; replacing it by two
would remove this particular exclusion. No response quotient is
inferred merely from the symmetric singleton child matrix.

Protected-leaver criteria fail because the protected set is empty.
The all-member positive-weight aggregate-leave inequality fails on
every singleton of C since each joining difference there is positive.
The boxed-charge and mixed boxed hypotheses fail already at their
singleton layers: P_C({j})=3 and L_C({j})=2, not negative.
The greatest core is not of size at most two. Product-low and
positive-weight nonpositive participant-sum tests fail at sure123,
where every active participant has premium four. Every pivot-0 pair
premium is −1, excluding prescribed pivot joint-phase tests requiring
a nonnegative or positive pivot premium.
These are bounded raw-source comparisons, not an exhaustive exclusion
of all stationary or chronological producers. In particular no claim
about all fourteen universal child-debt criteria is made for this table.

## Overlapping traps, signed premiums and weak boundaries

For an explicit overlapping-pair stress test, change only
r_1(12), r_3(13), r_2(23) from zero to one in the displayed table.
Its traps are now 12,13,23,123, so all three pairs overlap. The two
singleton-joining gaps for each core player become 1 and 2, while
the two-opponent gap remains 4. The same sure-exit exclusions and
empty protected set remain valid. The same-domain proof must therefore
handle bad pair roots and bad triple roots together, not assume that
the sole trap is C. The inactive-pair polynomial step is necessary.

Conversely, changing those same three zero entries to −1/2 gives a
strictly admitted table with negative core-player participant premiums
INSIDE C. Changing them to −1 gives a weakly admitted boundary table
with three zero joining gaps. In both cases the sole trap remains C,
and all nonzero joining gaps stay positive. Lowering the corresponding
passive singleton coordinates by δ is exactly the closure perturbation
above: it makes the zero gaps strict without altering any participant
premium or creating another trap. These are exact scope and boundary tests.

## An actual bad triple root inside the box

The original displayed table admits a bad triple root; the proof does
not exclude that support by a hidden payoff inequality. At source

    v=(9/10,26/57,26/57,10/9)

use q=(0,1/4,1/4,1/20). Its core odds are 1/3,1/3,1/19.
Formula (3) gives zero active gaps, since each singleton insertion
difference is one and each two-opponent difference is four. Its actual
successor and the outside Quit gap are

    w=(3559/3200,13/80,61/80,13/16),
    Q_0−C_0=−1849/3200.

Thus w>s in every coordinate while v_0<s_0, and this is a FULL
exact root with a strictly inactive outsider. All data lie in the
box [−5,5]^4. The six active derivatives are

    a_12=a_21=23/15,
    a_13=a_23=35/19,
    a_31=a_32=7/3.

The full determinant is −2254/171, strictly negative. The theorem's
index argument must produce another root returning to a singleton
sublevel; it cannot claim that every root returns. This test separates
actual triple-root index counting from a triple-support prohibition.

## Tracked inputs and Lean handoff

The following are existing mathematical inputs under their imports;
this manuscript is ordinary mathematics, not a claim that the new
raw theorem is already Lean-checked.

- `IsFiniteCoalitionPremiumTrap.union`,
  `IsFiniteCoalitionPremiumTrap.subset_core`,
  `isFiniteCoalitionPremiumTrap_core` and `not_positive_on_core_insert`
  in `MathUE/FiniteCoalitionPremiumCore.lean` implement the finite raw
  trap union and the outsider witness implication.
- `exists_successor_le_singleton_of_exactRoot_nontrap_support` in
  `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`
  uses signed participant rewards, exact Nash and positive absorption,
  not a nonnegative-premium hypothesis. The strict-leaver theorem in
  that same file is a different comparison from (4)–(5).
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies Nash
  roots at arbitrary continuation annotations.
- `ambientDegree_homotopy` and
  `ambientDegree_affineRootField_eq_sign_det` in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`, together
  with `ambientDegree_excision` and `ambientDegree_additive` in
  `MathUE/Topology/AmbientDegreeProperties.lean`, supply the degree
  primitives used in the explicit local comparison and finite sum.
  `ambientDegree_of_selfMap_eq_one` in
  `MathUE/Topology/AmbientDegreeSelfMapNormalization.lean` gives the
  corresponding global self-map normalization. The full triple
  derivative and pair tie-polynomial adapters are proved above.
- `abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
  in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`
  is the signed successor displacement estimate.
  `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
  is the exact collision-adjusted face inequality, including upper faces.
- `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
  obtains normality from the assumed own-singleton signs.
  `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
  produces the actual rational polynomial obstruction when Fin4 has
  no uniform payoff, under normality and a positive singleton.
  `isQuittingFullExactRootPotential_of_robustPotential` and
  `IsQuittingFullExactRootPotential.mono_box` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
  retain that identical function on the exact-root box.
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
  consumes the explicit strict perturbations, preserving the fixed-target
  uniform-payoff quantifiers. It does not assert openness of UE.

For the fixture's bounded source comparisons, the regular root-sum
criterion is `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`. The original-table degree
exit is `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
The named inverse screen is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The partition necessary condition is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
the response polynomial is the literal zero-discount displacement from
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.

A direct formalization starts with the finite raw predicate: compute C,
assert |C|=3, and compare the nine within-core insertion differences.
The new producer lemmas are the sure-hazard cascade, positive off-diagonal
triple derivative, negative full local determinant, simultaneous pair-tie
avoidance and selected-return theorem after the pure-C exit. The explicit
same-D minimum then excludes the already defined full-root potential;
the existing polynomial and reward-closure consumers yield strict and
weak Fin4 UE. No strategy witness, favorable annotation, supplied index,
or new equilibrium compiler is part of the raw input.
