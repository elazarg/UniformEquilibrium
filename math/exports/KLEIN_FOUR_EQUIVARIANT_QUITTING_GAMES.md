# Uniform equilibrium for Klein-four-equivariant quitting games

## Exact statement

Let I=(Z/2Z)², with additive notation. For each nonempty subset S of I,
let r(S) be an arbitrary vector in Rᴵ. Assume full-table translation
equivariance:

    r_(i+k)(S+k) = r_i(S)       for all i,k in I and all nonempty S.    (E)

Consider the quitting game with this reward table. At each live date the
four players independently choose Quit or Continue. The first nonempty
quitting coalition S absorbs at reward r(S); play that never absorbs has
payoff zero. Before absorption the stage reward is zero. Strategies and
unilateral deviations may be arbitrary behavioral strategies, with private
randomization and observation of the public history. No public correlating
device is available or required.

**Theorem.** Every table satisfying (E) has a uniform-equilibrium payoff.
Explicitly, there is one vector v in Rᴵ such that for every ε>0 there are
one independent behavioral profile σ and one horizon threshold H₀ with
the following properties for every H≥H₀:

1. The expected H-stage average payoff of σ is within ε of v in every
   coordinate.
2. No player can improve its expected H-stage average payoff by more than
   ε through any unilateral behavioral deviation.

The target v is selected before ε. A deviator need not be stationary,
periodic, finitely supported, or almost-surely quitting. The construction
uses only stationary profiles: either one exact stationary terminal Nash
profile, the all-Never profile, or a family of stationary approximate
terminal Nash profiles with a single fixed limiting target. The theorem
does not assert that every table in the class has an exact stationary
terminal equilibrium.

All reward coordinates may have arbitrary signs. In particular, no
monotonicity, premium bound, or positivity assumption is imposed on joint
quitting rewards.

## Conjecture-facing change

This is complete existence coverage of an independently specified raw
four-player reward class. It adds an actual-data stationary producer for
the positive-singleton-surplus, mixed-singleton part of that class. Its
input is the literal full reward table and (E), not a supplied hazard row,
response solution, complementary vector, or continuation-value certificate.

After normalizing positive own singleton rewards to one, the class has
fourteen unrestricted real coordinates. Its singleton matrices include the
paired standard-Q, no-homogeneous, non-projective-Q-bar pattern described
in the source correspondence below. Nonsingleton coordinates are consumed
by the exact stationary field, not suppressed by a rare-exit approximation
in the new branch.

The unrestricted finite-player conjecture, and arbitrary nonsymmetric
four-player reward tables, remain open obligations outside this statement.

## Strategic inputs

No strategic witness is assumed. The proof produces all of the following
from the table:

* A case choice based on the common own singleton and three outsider
  singleton rewards.
* In the new branch, a pairing, a sufficiently small cutoff, and a
  stationary hazard row selected by a projected-field fixed point.
* In the other branches, a scalar root, the all-Never row, or an explicit
  common-hazard or rare-owner family.
* Actual continuation payoffs and complete unilateral-response bounds.
* One payoff target independent of requested accuracy, followed by one
  profile and one common horizon threshold for that accuracy.

Brouwer's finite-dimensional fixed-point theorem and the scalar intermediate
value theorem are used as existence results. Their selected points depend
only on the fixed table. No selection from a changing game or a recursive
child is needed.

## Definitions and normalization

Until absorption, every public action history is a sequence of all-Continue
rows. Consequently a behavioral strategy induces a complete private
stopping law on {0,1,2,…} together with Never. Conversely every such law
can be implemented behaviorally. Independent private randomization gives
independent laws; replacing one entire law describes every unilateral
behavioral deviation. In particular, a deviation is not allowed to inspect
another player's future private stopping choice.

A stationary hazard c_i in [0,1] means that player i independently quits
with probability c_i at each live date. Hazard zero means literal Never;
hazard one means Quit at the first live date. The terminal payoff is r(S)
at the first nonempty coalition and zero on joint Never.

Let s=r_i({i}). Equation (E) makes s independent of i. If s≤0, all-Never
is exact Nash for every finite horizon and for the terminal evaluation:
the only payoffs a unilateral deviation can realize are zero and its own
nonpositive singleton, or a finite-average fraction of that singleton.
Thus v=0 proves the theorem in this case, including s=0.

For the rest of the proof assume s>0 and divide every reward by s. This is
a common positive scaling, not a translation; it preserves Never=0 and
every incentive comparison. Own singleton rewards are now one. At the end
multiply the produced target by s and adjust accuracy by the same factor.

For each of the three nonzero t in I, define the following coordinates:

    r_i({j}) = a_(i-j)                         when i≠j,
    r_i({j,j+t}) = p_t                         when i is in the pair,
    r_i({j,j+t}) = f_t                         when i is outside the pair,
    r_i(I\{m}) = h_(i-m)                       when i≠m,
    r_m(I\{m}) = h₀,
    r_i(I) = g.

Together with own singleton one, these formulas parameterize exactly all
tables satisfying (E). For pairs, translation by t swaps the two members
and the two outsiders; translating the pair to its complementary coset
then gives the same p_t and f_t. Triple and full-coalition formulas follow
directly by translating the missing player. The fourteen coordinates
a_t,p_t,f_t,h_t,h₀,g are otherwise arbitrary real numbers.

Write

    D = sum_(t≠0) a_t - 3.

The four exhaustive normalized cases are:

1. D<0.
2. D=0.
3. D>0 and a_t≥1 for every nonzero t.
4. D>0 and a_t<1 for at least one nonzero t.

## Source correspondence

The following are existing source declarations, distinct from the ordinary
mathematical producer proved here.

* `quittingFaceNumerator`, `continuous_quittingFaceNumerator`,
  `quittingFaceNumerator_eq_gainValue`, and
  `quittingFaceNumerator_eq_one_sub_continueMass_mul_conditionalFaceGap`
  in `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean` provide
  the exact division-free field used below. Extend the nonempty-coalition
  reward table by zero at the empty set to match that file's total-function
  signature. Its `sigmaValue`, `excludedValue`, and `continueMassExcl`
  are respectively Q_i, A_i, and α_i below.
* `heterogeneousFaceNumerator_update_self` and
  `heterogeneousFaceNumerator_congr_off_self` in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`
  express independence of the individual field from that player's own
  hazard. The same file's `exists_heterogeneousStationaryFaceNash` supplies
  constrained rectangular Nash data. It does not supply the triangular
  origin exclusion and diagonal decoding proved here.
* `quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto` and
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  consume actual terminal Nash families whose errors tend to zero and
  whose payoff vectors tend to one fixed target. The former retains an
  actual family member as the witness for all sufficiently long horizons;
  the latter concludes `IsUniformEquilibriumPayoff none target`. The
  proof below supplies these hypotheses and also gives direct finite-average
  estimates, including the rare owner's exceptional deviation case.
* `quittingGame_exists_uniformEquilibriumPayoff_of_cardinalSymmetric` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_permutationSymmetric`
  in `UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`
  concern the stronger full cardinal/permutation symmetry. Unequal a_t
  are allowed here and need not satisfy those hypotheses.
* `exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos` in
  `UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`
  already covers the D≤0 existence branches, even without nonsingleton
  symmetry. Those branches are included for a complete self-contained
  signed statement, not as additional implementation coverage.
* The normalized off-diagonal singleton margins (3,−1,−1), equivalently
  (a_t)=(4,0,0), give the XOR presentation of `pairedSingletonMatrix` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingleton.lean`.
  The declarations `pairedSingletonMatrix_standardQ` and
  `pairedSingletonMatrix_noHomogeneous` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`,
  together with `pairedSingletonMatrix_not_projectiveQBar` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`,
  show that this admitted singleton pattern is not automatically consumed
  by the non-standard-Q, homogeneous, or projective-Q-bar alternatives.
  It is standard Q, not non-Q.

The missing content is the raw full-table equivariant producer in case 4,
combined with the complete signed classification. The comparison does not
claim that every individual example supplied below avoids every existing
producer, or make a claim of external publication priority.

## Proof: exact stationary field and unrestricted responses

Fix a hazard row c. For player i let J be the independently sampled subset
of opponents who quit at one date, and define

    α_i = product_(j≠i)(1-c_j),
    Q_i = E[r_i(J union {i})],
    A_i = E[1_(J nonempty) r_i(J)],
    F_i(c) = (1-α_i) Q_i - A_i.                              (1)

These are finite polynomials in the opponents' hazards. In particular F_i
is continuous on the whole cube and does not depend on c_i. It remains
defined even when opponents never absorb.

Suppose every player has a positive-hazard opponent and the following
individual complementary inequalities hold:

    c_i=0       implies F_i≤0,
    0<c_i<1     implies F_i=0,
    c_i=1       implies F_i≥0.                               (2)

Set b_i=1-(1-c_i)α_i>0. The actual stationary terminal payoff is

    U_i = [c_i Q_i+(1-c_i)A_i]/b_i.                         (3)

This follows either by summing the geometric absorption series or by
solving its scalar recurrence. The pure Continue endpoint at continuation
value U_i is C_i=A_i+α_i U_i. Direct substitution gives

    Q_i-C_i = F_i/b_i,
    U_i = c_i Q_i+(1-c_i)C_i.                              (4)

Thus (2) makes both pure-action endpoints at most U_i. At an interior
hazard both equal U_i; at hazard zero or one the chosen endpoint equals
U_i and dominates the other endpoint.

Now permit any behavioral deviation by i. At each surviving public history
the unchanged opponents have exactly their same product row, independently
of the deviator's private choice. Iteration of the endpoint inequalities
therefore bounds the deviator's payoff through N dates plus continuation
U_i at date N by U_i. The probability of survival through those dates is
at most α_i^N. Since α_i<1 and rewards and U_i are bounded, the remainder
tends to zero. This proves exact terminal Nash against every complete
behavioral deviation, not only stationary deviations.

For completeness, let M=max_(i,S)|r_i(S)|. Under any deviation by i, the
first opponent quit has geometric mean waiting time bounded in terms of
1/(1-α_i). The actual absorption time is no later. The absolute difference
between terminal payoff and H-stage average payoff is bounded by a constant
times M times the number of pre-absorption dates divided by H. Taking
expectations gives a bound K_i/H, uniform over all deviations by i. The
possible convention of crediting the reward on the quitting date changes
this bound by at most M/H. The same estimate applies to prescribed play.
Because there are only four players, one common threshold makes all these
errors small. Consequently the single row c is a uniform witness at its
fixed actual payoff U. This proves the semantic implication needed for
every exact stationary row below.

## Proof: the triangle producer in case 4

Choose t≠0 with a_t<1, and let u,v be the other two nonzero elements.
Partition I into B₀={0,t} and B₁={u,v}. Give each B₀ player hazard x and
each B₁ player hazard y. Translation by t interchanges the members of
each pair and preserves this row, so the two individual face numerators
within each pair coincide. Denote the resulting pair values by F₀(x,y)
and F₁(x,y). Translation by u exchanges the pairs, giving the exact identity

    F₁(x,y)=F₀(y,x)                 on the entire square.     (5)

These are individual player numerators, not payoffs of two aggregate
decision makers. Although F_i does not depend on its own hazard, F₀ can
depend on x because the other member of B₀ also has hazard x.

Put A=1-a_t>0 and B=a_u+a_v-2. Then B-A=D>0. For a B₀ player, opponent
absorption is x+2y+O((x+y)²), the forced-Quit value is 1+O(x+y), and the
unconditional passive contribution is a_t x+(a_u+a_v)y+O((x+y)²).
Therefore

    F₀(x,y)=A x-B y+O((x+y)²),
    F₁(x,y)=A y-B x+O((x+y)²).                             (6)

The second formula also follows from (5). Since these are polynomials,
their remainder bounds are uniform near the origin. On 0≤y≤x one has
A y-B x≤-(B-A)x=-D x. The positive linear term A x on y=0 similarly
dominates its quadratic remainder. Hence choose 0<δ<1 sufficiently small
that for 0≤y≤x≤δ and x>0,

    F₁(x,y)<0,                 F₀(x,0)>0.                 (7)

One can choose δ directly from finite coefficient bounds: on this triangle
bound each remainder in (6) by Cx² with C>0, then take δ positive smaller
than 1, D/(2C), and A/(2C). In particular (5) and (7) imply
F₀(x,x)=F₁(x,x)<0 for 0<x≤δ.

Let

    T={(x,y):0≤y≤x≤1},
    φ(x)=max(δ-x,0),
    F̃(x,y)=(F₀(x,y)+φ(x),F₁(x,y)).

The compact convex triangle T has continuous Euclidean metric projection
P_T. Brouwer applied to the continuous self-map

    z ↦ P_T(z+F̃(z))

gives a fixed point z in T. The metric-projection characterization gives
the sign convention

    F̃(z)·(w-z)≤0                   for every w in T.        (8)

Indeed, at a closest point z, compare the squared distances to
z+λ(w-z), divide by λ>0, and let λ tend to zero; the displayed inequality
follows. Conversely the same inequality makes every such squared distance
at least the squared distance to z. This fixes the outward-normal sign
without appealing to a game-theoretic interpretation of the projection.

First exclude every point with x≤δ:

* At (0,0), the field is (φ(0),0) with positive first coordinate. A small
  positive horizontal direction is feasible and contradicts (8).
* At 0<y<x≤δ, both vertical directions are feasible because δ<1. Thus
  (8) would force F₁=0, contradicting (7).
* At y=0 and 0<x≤δ, both horizontal directions are feasible. Hence (8)
  would require F₀+φ=0, whereas F₀>0 and φ≥0.
* At x=y in (0,δ], if φ>0 then (5) gives
  F̃₀-F̃₁=φ>0. A small displacement in direction (1,−1) is feasible and
  contradicts (8). If φ=0, both field coordinates are the same strictly
  negative number; direction (−1,−1) gives the contradiction instead.

This includes x=δ, where φ vanishes. The cutoff line is not an additional
boundary of T. We therefore have x>δ, so F̃(z)=F(z) is the original exact
reward-table field at the selected point.

It remains to decode every genuine face of T:

* If 0<y<x<1, both coordinate directions have both signs, so F₀=F₁=0.
* If y=0 and 0<x<1, horizontal directions give F₀=0 and an inward
  positive vertical direction gives F₁≤0.
* If x=1 and 0<y<1, vertical directions give F₁=0 and an inward
  negative horizontal direction gives F₀≥0.
* At (1,0), the negative horizontal and positive vertical directions give
  F₀≥0 and F₁≤0.
* If x=y in (0,1), both diagonal tangent directions give F₀+F₁=0.
  Equation (5) gives F₀=F₁, hence both vanish.
* At (1,1), equation (5) still gives equality of the two coordinates.
  The inward direction (−1,−1) gives F₀+F₁≥0, hence both are nonnegative.

These are exactly the individual complementary inequalities (2) for the
four hazards (x,x,y,y) on B₀,B₁. There are two positive-hazard players in
B₀ because x>δ>0. Deleting any one player's own strategy therefore leaves
at least one positive-hazard opponent. Equations (3)–(4) and the complete
response argument prove exact stationary terminal Nash and its fixed
uniform-equilibrium payoff. This completes the new branch.

## Proof: the other exhaustive cases

### Negative singleton surplus

For common hazard q put z=1-q. Direct enumeration of opponent coalitions
gives the common forced-Quit value

    Q(q)=z³+qz² sum_t p_t+q²z sum_t h_t+q³g,

and the common unconditional passive contribution

    A(q)=qz² sum_t a_t+q²z sum_t f_t+q³h₀.

The common field is F_i=qL(q), where the polynomial

    L(q)=(3-3q+q²)Q(q)
         -[z² sum_t a_t+qz sum_t f_t+q²h₀]                 (9)

satisfies L(0)=-D and L(1)=g-h₀.

Suppose D<0. If g≥h₀, all four players quitting surely is exact Nash:
an individual Continue realizes the triple missing that player and pays
h₀, while Quit pays g. All opponents quit at once, so later deviation
behavior is irrelevant. If g<h₀, equation (9) has an interior root by
the intermediate value theorem. The corresponding common hazard q in
(0,1) gives F_i=0 for every i, with positive opponent absorption. The
exact stationary argument supplies the fixed uniform payoff. Equality
g=h₀ belongs to the sure-exit case and causes no missing endpoint.

### Zero singleton surplus

Suppose D=0 and let every player use common hazard q>0, with q tending
to zero. For any player let α=(1-q)³ and define C(q)=A(q)/(1-α).
Against these stationary opponents, quitting at the pure date n gives
terminal payoff

    (1-αⁿ) C(q)+αⁿ Q(q),

and Never gives C(q). The formula follows by summing opponent absorption
before n and then evaluating the forced-Quit endpoint if n is reached.
Every complete stopping law is a mixture of these cases. Therefore the
exact full-response cap is max(Q(q),C(q)). Both endpoints tend to one:

    Q(q) → 1,
    C(q) → (sum_t a_t)/3 = 1.

The prescribed terminal payoff also tends to one, since it is a mixture
of the same endpoints. Thus full terminal regret tends to zero and the
fixed target is v=(1,1,1,1). For each ε first choose q small enough to
make terminal regret and target error small. With that same q fixed,
every deviator faces positive geometric opponent absorption, so the
uniform finite-average estimate proved above gives a common threshold.
This is the required quantifier order; the target is not reselected with q.

### Positive surplus with no subunit outsider singleton

Suppose D>0 and every a_t≥1. Choose one owner o. Let it use stationary
hazard q>0 and let the other three players use Never. For every q the
prescribed terminal payoff is exactly r({o}), since the owner eventually
quits alone with probability one. This is the fixed target.

The owner can obtain only its own singleton one or Never payoff zero,
so has no profitable terminal deviation. For an outsider i put
a=r_i({o})≥1 and p=r_i({o,i}). Conditional on reaching any chosen finite
quitting date, its Quit reward is

    (1-q)·1+q p=1+q(p-1),

while following Never from that date gives a. Earlier owner absorption
pays a under either strategy. Thus the gain from any pure finite stopping
date is at most q max(p-1,0), multiplied by the probability of reaching
that date. A mixture of dates and Never obeys the same bound. This covers
every complete behavioral deviation. Full terminal regret tends to zero
as q tends to zero, at the same target r({o}).

For each outsider, the unchanged owner supplies a geometric absorption
bound uniform over all deviations. The owner has no positive-hazard
opponent, so that particular bound must not be used for its deviations.
Instead every finite-average deviation payoff of the owner is at most
one, while its prescribed finite average tends to one. Prescribed payoff
in all coordinates converges to r({o}). First choosing q by accuracy and
then a sufficiently large horizon threshold therefore proves the uniform
claim in this branch as well.

The four cases and the earlier s≤0 branch are exhaustive. Restoring the
positive scale s completes the proof of the theorem.

## Boundary tests

### Own-singleton zero and negative rewards

Take any fully equivariant table with common own singleton s≤0; all other
coordinates may be arbitrarily large, positive, or negative. Against
all-Never only a unilateral singleton can occur, so every finite-average
deviation payoff is ≤0. This checks that no positivity assumption or
normalization across s=0 has been hidden in the statement.

### An exact scalar interior root

Take own singleton one, a_t=p_t=f_t=h_t=0 for every t, h₀=0, and g=-1.
These data specify the entire table by the formulas above. Here D=-3.
At q=1/2 one has Q(q)=(1-q)³-q³=0 and A(q)=0. Thus every field coordinate
vanishes, the stationary terminal payoff is zero, and unchanged opponents
absorb geometrically. This is a literal interior-root example with negative
grand-coalition reward.

### Positive surplus in the paired singleton pattern

Label the nonzero group elements 1,2,3 with XOR addition. Take

    own singleton = 1,
    (a₁,a₂,a₃)=(4,0,0),
    (p₁,p₂,p₃)=(2,1,1),
    (f₁,f₂,f₃)=(1,0,0),
    (h₁,h₂,h₃)=(0,1,1),     h₀=0,     g=-1.

The parameterization specifies every nonempty-coalition payoff. Here D=1,
and the normalized off-diagonal singleton matrix is

    [[0, 3,-1,-1],
     [3, 0,-1,-1],
     [-1,-1,0, 3],
     [-1,-1,3, 0]].

The exact row (c₀,c₁,c₂,c₃)=(1,1/2,1,1/2) has payoff
(1/4,0,1/4,0). For a sure player its Quit endpoint is
(p₂+h₁+h₃+g)/4=1/4 and its Continue endpoint is
(a₂+f₁+f₃+h₀)/4=1/4. For a nonsure player the endpoints are respectively
(h₂+g)/2=0 and (f₂+h₀)/2=0. Every deleted opponent row still contains a
sure quitter, so these are unrestricted equilibrium comparisons.

This example also fails the product-low-premium hypothesis. At the product
root where players 0 and 1 each quit with probability 1/2 and the other
two Never, both active players have forced-Quit payoff
(1+p₁)/2=3/2>1. Positive absorption is 3/4, and there is no active player
with forced-Quit payoff at most its own singleton. This violates exactly
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
Thus the whole equivariant theorem cannot be inferred merely by asserting
that every table satisfies the hypothesis of
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
The example is not claimed to avoid every other existing producer.

### Full-table symmetry is essential to this proof

Singleton symmetry alone does not establish equation (5). For a concrete
test, `boundaryReward` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`
assigns coalition {0,2} the vector (1,1,1,0). The XOR translation by 2
fixes this coalition and swaps outsiders 1 and 3, whose payoffs are one
and zero. Hence this row violates (E). A singleton-matrix match with that
table cannot be used as a counterexample to the full-table theorem or
as permission to drop its nonsingleton hypothesis.

### Projection seams and approximate branches

The cutoff boundary x=δ is included in the exclusion argument even though
φ=0 there. The diagonal is a genuine chamber boundary: its tangent
equation only gives F₀+F₁=0, and the exact equality of the two individual
fields is used here to deduce both vanish. At (1,1) equality
is again used to decode the inward diagonal inequality. These are
the boundary cases where a generic two-variable constrained Nash argument
would not alone imply individual complementarity.

At D=0 the proof explicitly uses a sequence of positive hazards with target
ones; at a_t≥1 the rare-owner target is its singleton vector. Neither
limit is interpreted as saying that the limiting all-Never row is itself
an equilibrium when own singletons are positive.

## Adapter and consumer

The actual-data adapter takes any four-player table satisfying (E), computes
s, and applies the exhaustive case split. In case 4 it chooses a subunit
a_t, forms the exact individual fields from all coalition rewards, obtains
δ from their finite polynomial coefficients, and selects a projected fixed
point. The point lies outside the altered region and supplies an actual
independent stationary row satisfying every individual incentive condition.
In the scalar and approximation cases the profiles and targets are given
explicitly above. No additional strategic input remains unproduced.

The ordinary mathematical consumer has been proved directly: exact rows
give full terminal Nash and fixed uniform payoff; approximation families
give full terminal regret tending to zero and a fixed limiting target.
For formalization, the supplied-family consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` named
above reaches the exact existing semantic endpoint. A constant family can
be used in the exact cases. The proof also preserves actual stationary
family members as sufficiently-long-horizon witnesses through
`quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto`.

## Lean handoff

The narrow missing mathematical pieces are as follows.

1. Define full reward-table translation equivariance on the finite group
   `(Z/2Z)²`, or an explicitly equivalent four-element type. This must
   quantify over every nonempty coalition, not only singleton columns.
   Prove the fourteen-coordinate parameterization or use equivariance
   directly for the two pairwise field identities.
2. Prove a two-dimensional continuous-field lemma on
   `{(x,y):0≤y≤x≤1}` with coordinate-swap symmetry and the local strict
   signs (7). Its output is a point with x>0 satisfying all rectangle
   complementarity signs. Include the projection convention, the entire
   cutoff region, every diagonal point, and both outer corners. No
   stationary equilibrium should be assumed in this lemma's hypotheses.
3. Instantiate that lemma with `quittingFaceNumerator`. Derive its linear
   expansion (6) from the raw singleton coordinates and bound the remaining
   finite polynomial terms. All nonsingleton coordinates remain in the
   unmodified field used at the selected point.
4. Supply actual stationary profiles and their terminal values, proving the
   endpoint identities and full behavioral comparison with opponent
   absorption. The same calculations verify the scalar branches and the
   explicit approximation families. Existing source consumers may replace
   the direct finite-average estimates once their literal hypotheses are
   matched.
5. Conclude `IsUniformEquilibriumPayoff none target`, transporting the result
   to `Fin 4` by a player bijection if desired. Treat s≤0 separately and
   use only positive scaling in the normalized branches.

Suggested final theorem shape: every finite real nonempty-coalition reward
table on the Klein four group with the literal equivariance property admits
a uniform-equilibrium payoff. A useful stronger intermediate conclusion in
case 4 is existence of an actual stationary row with two positive hazards,
all individual complementary inequalities, and exact full terminal Nash.
No statement here is itself a claim of an implemented Lean theorem.

## Scope and nonclaims

This theorem covers every signed full-table Klein-four-equivariant reward
table, with independent play and unrestricted unilateral behavioral
deviations. The positive-surplus mixed-singleton branch produces an exact
stationary equilibrium; the complete theorem deliberately allows approximate
stationary families in its other branches.

It does not prove stationary completeness for arbitrary quitting games,
equilibrium for all tables with a symmetric singleton matrix, an asymmetric
neighborhood result, arbitrary four-player coverage, or the full finite-player
conjecture. It supplies no public correlation and does not weaken deviations
to the profiles' stationary strategy class. The argument is an application
of Brouwer and scalar continuity, not a new general fixed-point theorem.
