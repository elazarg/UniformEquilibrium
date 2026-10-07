# Negative-premium three-phase producer: independent scope review

Reviewer: CODEX_MORSE.

Review surface: the final section “A negative-premium three-phase producer
for a no-good cyclic child” in
`../notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md`,
whole-note SHA256
`5540f0d1b6843507b1859cc123566a380f24d74d96b543720c4c423eb88bdd01`.
No other review was read. The primary assignment was adversarial coverage
checking; the root and full-strategy arguments needed to identify the claim
were also checked directly. This is ordinary mathematics, not a Lean seal
or a final standalone-artifact check.

Current verdict: final-artifact PASS at the repaired standalone hash
`d914edc619e9d28d64131dc734cd31f9f6d8c87f00a323693911d68794d82421`,
as recorded below. The earlier notebook surface has the erroneous (N15)
entry identified in the correction section. The initial scope verdict
missed it; that old version is not being treated as the accepted artifact.
In particular the exact center is not admitted by the full concrete-base
selection mechanisms or ANY of the fourteen universal child quiet-lift
systems compared below. These are exclusions of whole selection sets and
whole certificate families, not tests of a few selected candidate laws.
A supplied-root verifier is not counted as an overlapping raw producer.

## Exact scope

For 0<ε≤1 the canonical rewards fix the four singletons

    (1,0,0,0), (2,1,4,0), (2,0,1,4), (0,4,0,1)

and the scheduled joint row r(03)=(1−ε,3,−1,1−ε). The twelve
specified upper bounds (N2) constrain passive joining endpoints; all other
coordinates remain unrestricted. The original signed-row extension takes
arbitrary own levels s_i and positive scales k_i, requiring
1+(r_i(S)−s_i)/k_i to satisfy those canonical conditions.

The conclusion is one produced periodic profile that is exact terminal
Nash against all behavioral deviations, and one fixed original-game
uniform target. It is not exact finite-horizon Nash. The profile uses the
joint row03 followed by solo1 and solo2 when ε<15/26; the boundary and
larger-ε arm use the child-only solo3,1,2 cycle. This is a raw completion
family, not an asserted full sixty-coordinate open neighborhood.

## Producer and unrestricted-consumer checks

I independently checked the following potentially fragile steps.

1. On y∈[2/5,2/3], the cap p̄=(3−4y)/(4−3y) lies in[0,1/2].
   For p≤p̄, 3y−p≥7/10, so all denominators and w are valid.
   The child equation has the concave quadratic numerator (N6).
   Its sign at p=0 and strictly positive sign at p̄ give exactly one
   crossing before the cap. At y=2/3 the selected crossing is0, with
   derivative (55−8ε)/3>0. Thus the displayed smaller-root formula is a
   genuine continuous selection, including its zero endpoint.
2. The pivot numerator at y=2/5 is strictly negative because the selected
   p>1/5, whereas at y=2/3 the pivot equation equals
   (30−52ε)/27. The IVT therefore produces rates in the proper interior
   for EVERY 0<ε<15/26. No isolated numerical solution or unproduced
   strategic input is being used.
3. The actual negative joint-phase values are retained. The two passive
   margins that cannot be replaced by singleton floors are
   (3−ε)y−(1−ε)p and the exact expressions H/d, 3H/d with
   H=(3−ε)y−p>0. The triple rewards013 and023 enter the joint-phase
   Quit bounds explicitly. All four prescribed Continue recursions at
   the joint row agree with the produced values.
4. The child-only branch has actual pivot values
   (8/13,24/13,20/13). Its first-row Quit bound is1−2ε/3, so the
   threshold ε=15/26 and its equality case are exact. No persistence of
   a positive pivot hazard at the boundary is asserted.
5. Every player still has at least two proper opponent hazards each
   period, even in the child-only arm. The four deleted-player period
   survivals are strictly below1. Iteration therefore controls Never,
   every arbitrarily late pure stopping time, and every behavioral
   replacement. Positive row scaling and arbitrary reward shifts are
   legitimate for this particular constructed profile because opponents
   force absorption under EVERY unilateral replacement; no general
   affine invariance of zero-Never quitting games is assumed.
6. With the initial zero live date, delivery is bounded by C/N and
   finite-horizon unilateral regret by2C/N. The rates and target are
   selected before accuracy and horizon. These are the actual semantics
   consumed by the named periodic compiler, not a terminal-only claim.

## The complete concrete-base carriers really are excluded

At the full rational center ε=100/729, the actual punishment value is
P=1−ε for all four players. Quit immediately guarantees P because every
participant reward is at least P. The adverse opponent quitting surely
allows only passive reward0 or joining reward P; this is the matching
upper bound on the full behavioral response cap.

I checked the unique auxiliary root at continuation P directly. For fixed
pivot hazard h, the child gap is

    g₁=ε(1−h)(1−y)(1−z)+(1−ε)h+y−(3−ε)z,

with its two cyclic rotations. A quiet child forces its successor positive,
then bounds the other child below1, while that child's own gap forces it
sure. This is contradictory. A sure child makes another positive child's
gap at most−1. Thus all three children are proper. Their equations form
a three-cycle of the same strictly increasing map, so their hazards are
equal to the unique r(h) solving

    ε(1−h)(1−r)²+(1−ε)h−(2−ε)r=0.

This root increases strictly in h. The pivot gap then is
ε(1−r(h))³−r(h), strictly decreasing. It vanishes at h=r=1/10 and
excludes both endpoint pivot hazards. Hence this is the ONLY full cube
Nash root, and it has no sure coordinate.

The literal production definitions inspected were
`quittingPersistentLargeBaseComponent`, `quittingPersistentLargeBaseExcess`,
`quittingPersistentLargeBaseExcess_nonpos_iff`,
`quittingSingletonBaseOwnerFloorExcess`,
`quittingSingletonBaseExcess_nonpos_iff`, and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

For every disjoint base/free choice with nonempty base, a nonpositive
concrete excess at an induced free-game Nash point would extend to a FULL
cube root at P with the base sure. For base size≥2, every base owner
retains a sure opponent, so the continuation price is irrelevant. For a
singleton base, its actual Continue endpoint is priced at exactly its
punishment P. Free players already optimize, and the concrete screen also
checks every player outside base∪free. Thus partial free sets cannot evade
the argument. This covers all65 base/free choices, including empty free
sets, not only the fifteen full-complement carriers. Compactness then
gives the corresponding uniformly positive gaps over each Nash set.

Consequently neither `exists_uniformPayoff_or_singletonBase_pos_gap` nor
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` conceals a producer
accepting this center. This is the substantive distinction from the older
coarse-regret/anchor family, whose complete class was source-covered.

## All fourteen quiet-child systems, including every withdrawal kind

The listed thirteen sure-exit child profiles and the remaining child123
cycle are exact full-behavior terminal equilibria of their deleted games.
For a sure singleton, every other child has nonpositive joining gain;
the owner compares own1 with Never0. For sure03, both owners have positive
joining gain1−ε; when child1 is also present its joining gain is−2.
The child123 cycle has all active centered values0 and its passive Quit
bounds are0 or2ε/3 against Continue values0 or2. Its opponent survival
contracts. These checks include delayed and Never replies, not only
one-stage deviations.

Every displayed child profile has zero debt in every child coordinate
and zero joint Never probability. The selected omitted player's full-game
gain is positive: the table gives either1−ε,1,2−ε, or, for child123,

    1−2ε/3−8/13=(15−26ε)/39>0.

The quantifier is: for EACH child carrier there EXISTS an omitted player
with this obstruction. It need not be every omitted player.

The exact common source consumer is
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
For any of patient, deadline, evaluated-security, terminal-security or
cancellation certificates, it bounds outsider debt at EVERY supplied child
profile by a nonnegative weighted sum of child debts plus Never-excess
times child joint Never probability. Both terms are zero at the displayed
profile. Hence all five kinds are impossible for the indicated omitted
player, for each of the fourteen carriers, regardless of the weights.
This proves failure of the actual universal systems. Advancing-only
certificates are included; no equality between their weights and the
broader withdrawal weights was assumed.

## Conditional ranges, influence and response quotients

For each child the maximum participant reward is1+ε<4, whereas a passive
singleton reward is4. In `IsQuittingConditionalFaceGapRange` the universal
Continue-upper bound must therefore be≥4, while both proposed lower Quit
bounds, and every admissible mixture of them, are≤1+ε. The required strict
lower-face inequality is impossible for EVERY blocker permutation and box.
This excludes the raw producer
`exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`,
not arbitrary supplied polynomial face data.

The membership influence0→1 equals−ε at empty background and1−ε at
background{2}. Hence `SignConsistentQuittingInfluence` fails, as does
`IsAffineQuittingMembershipGain`. Their exact definitions were inspected
in `UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.
The contradiction is preserved by relabeling and positive playerwise
affine reward transport.

A further complete quotient comparison is useful. Response invariance
forces equal singleton block-row sums, by
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
Of the fifteen partitions only three pass this necessary test:

    discrete:       Γ;
    {0}|{1,2,3}:    [[0,1], [−1,2]];
    indiscrete:     [1].

This remains exhaustive after positive playerwise scaling. Any two-player
block other than03 has opposite-sign entries in its own block column,
so positive proportionality is impossible. Block03 with singleton1 has
opposite-sign entries in column1. Each three-player block other than123
has incompatible zero/positive/negative self-block sums. In block123 the
self-block sums2 force equal scales, as do the full-block row sums1.

The full matrix is R₀ of degree1. The two-dimensional quotient has inverse
[[2,−1],[1,0]], and at offset−1 its sole complementary root is(1,1),
of determinant1. The one-dimensional quotient is[1] and has degree1.
Positive row scaling preserves these conclusions. Thus neither quotient
degree≠1 nor negative determinant with nonnegative inverse applies.
The relevant actual producers are
`exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
One must NOT say that all response-invariant partitions fail: the coarse
partitions do survive, but their accepted degree exits do not.

The full inverse has mixed signs, so the inverse-positive raw stationary
half-polynomial guards also cannot accept the center. I checked the
literal nonnegative full-inverse premise in
`exists_uniformPayoff_of_weakHalfPolynomialGuards`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`.
This is an exclusion of that actual matrix-plus-face producer, not an
arbitrary stationary-root verifier.

## Remaining bounded raw comparisons and conclusion

The singleton principal determinants, inverse and regular offset−1 root
census are exact. The favorite graph is not bijective; row0 has two
positive comparisons. The only mutually nonnegative joining pair is03,
so no partition has four nonnegative within-pair joins. No pair has two
negative joins. These strict sign facts exclude every relabeling of the
accepted crossed matching, below-singleton matching, opposite-sign
matching and complementary-odds two-pair sources. Every triple has a
negative pair join, excluding the buffered triple–singleton criterion.

The greatest premium core is all four players; each player has a negative
participant premium, so no protected-player criterion applies. At a
product root supported on123 with all three hazards equal to any t>0,
every active forced-Quit premium is εt>0. Thus the actual product-low
predicate fails too, not merely a stronger sufficient raw condition.
The trap123 has positive singleton premium sum ε, excluding the boxed
and mixed-trap charge hypotheses. Its weighted-floor test at background0
is strictly negative for every positive child weight vector.

The original cyclic-child singleton resonance/passive-inverse exits fail,
and all pivot-child participant increments are−ε, excluding every
scheduled partner of the prior nonnegative-partner-premium source.
This explains the genuine new negative-premium regime of the producer.
It does not assert that every completion is outside all older criteria,
or that no other periodic or stationary equilibrium exists.

There is therefore a complete accepted-by-this-theorem center outside
the compared implemented and accepted raw producers, including the
strong complete-base and child-carrier selection mechanisms. The stated
whole completion family is not subsumed by them. No unproduced strategy,
chosen good root, fixed response witness, or assumed positive minimum
enters its existence theorem. A final self-contained assembly still needs
its separate exact-byte check; no export is made by this review.

## Required phase-entry correction

After the scope review, the coordinator relayed an objection to (N15).
I checked it directly without reading another review. The correct child-only
vectors are

    V_A=(8/13,3,1,1),
    V_B=(24/13,1,3,1),
    V_C=(20/13,1,1,3).

The old displayed V_B,3=3 is false: at solo1, player3 receives0 on
absorption, so its actual Continue value is (1/3)V_C,3=1. Its passive
Quit bound is also1, because r₃(13)≤1 and its own singleton is1. The
comparison remains valid but can bind. At solo3, active player3 is then
indifferent between Quit1 and continuing to V_B,3=1, as required.
The original displayed value3 would not satisfy this active Bellman
equality. None of the rates, pivot threshold, deleted-child witness or
raw coverage conclusions changes. This correction is required for a
valid self-contained final packet, and is not waved away as a harmless
annotation that was never used.

## Final repaired standalone-artifact check

Artifact:
`../exports/NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`.
Read all795 lines. Exact SHA256:

    d914edc619e9d28d64131dc734cd31f9f6d8c87f00a323693911d68794d82421

Verdict: PASS. This is a bounded assembly/correction check against the
substantive review above, not another speculative whole-tree audit.
No counterpart review was read. There is no unresolved mathematical
objection in the final bytes and no new Lean-verification claim.

The required (N15) correction is made: V_B,3=1. The final packet explicitly
checks its passive B endpoint and all three active child endpoints, so
the erroneous annotation is not silently retained in a dependent line.
All nine passive high-branch inequalities hold, including Q₃≤1=V_B,3
and the pivot's equality at ε=15/26. The same correction supplies the
exact child123 zero-debt witness used in the universal quiet-lift exclusion.
Its outside payoff8/13 and gain(15−26ε)/39 are unchanged.

The full raw premise and its twenty fixed, twelve capped and twenty-eight
unrestricted reward coordinates are unchanged. The produced low-branch
rates, scalar crossing, complete joint-coalition tests and opponent-only
contraction remain the same. No selected hazard, auxiliary root, response
law, punishment plan or assumed positive minimum has become an input.
The original signed-game conclusion and one fixed target are retained.

The added signed stresses check directly. At s=(−3,−5,−1,−4),
k=(1,2,3,4), the displayed low-branch target has all four coordinates
negative; the second is<−1 since3y−p<2. At ε=1 with capped coordinates
at their bounds and unrestricted entries37, the proposed child-only law
never visits those unrestricted entries under any single-player deviation.
At s=(−5,2,−7,0), k=(2,1/3,5,7/2), its target is indeed
(−75/13,8/3,−7,0). Geometric opponent absorption, rather than an assumed
Never-payoff transformation, handles both tests.

The incorporated quotient comparison is self-contained and accurate.
The useful refinement is that row sums1 force equal positive scales within
each prospective block, making the three-partition exhaustion immediate.
The two coarse candidates are not denied response invariance; their
R₀/degree1 matrices and positive determinants fail the relevant producer
exits. The paired-region comparison correctly uses
`RawRegion.eq_partner_of_singleton_lt`; each child has two distinct
below-own singleton recipients. The signed-four-cycle comparison correctly
uses the positive predecessor field of `SignedFourCycleSingletonData`;
column0 has no positive off-diagonal entry. I inspected those exact fields
in `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` and
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`.

The full concrete-base proof still excludes every partial free choice,
not only a selected law or full complementary set. All fourteen universal
child-debt-plus-Never contradictions are retained with their exact scopes.
The raw conditional-range/influence exclusions and other bounded source
comparisons have not been promoted to an unspecified all-stationary or
all-neighborhood nonexistence claim.

All unformalized construction and coverage calculations used by the packet
are inline. No conference note, feedback file, process history or untracked
reproduction input is a mathematical dependency. The handoff identifies
the raw scalar producer as new work and the existing endpoint/periodic
consumers as downstream declarations. It does not confuse the latter's
presence with a kernel check of the new theorem. The main significance
remains the new raw completion family with a complete screen-surviving
center, not its scalar root inventory or a stronger finite-horizon claim.
