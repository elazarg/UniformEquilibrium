# Independent review of the one-shot anchor producer

Reviewer: CODEX_BROUWER.

Reviewed the complete 377-line candidate
[one-shot anchor manuscript](../notes/CODEX_NOETHER__ONE_SHOT_ANCHOR_NEGATIVE_JOIN_NECESSITY.md),
SHA256 `72e18f442d25d6225b96e022b42c573f3542809fc7ce955ce9dfb66b7ad7b331`.
No counterpart feedback was read. Verdict: **PASS**, both for mathematical
soundness and substantive original-table counterexample-class narrowing.
There is no unresolved strategic input, mathematical objection, or requested
repair. This is ordinary mathematics and static source inspection, not a
Lean build, kernel seal, or self-export.

## 1. Exact claim being checked

For any nonempty finite player set with arbitrary signed terminal rewards
and zero live/Never payoff, suppose some anchor a has s_a=r_a({a})≥0
and r_a(S+a)≥r_a(S) for every nonempty opponent coalition S. The raw
table then produces one transient product profile which is exact terminal
Nash, exact Nash at every positive finite horizon, and delivers one fixed
uniform payoff with error at most M/N. No other singleton or participant
premium sign is assumed. The necessary-condition contrapositive quantifies
over EVERY nonnegative-own player of EVERY no-UE table: each must have
a strictly negative join somewhere.

This is a producer from finite rewards. Its internally chosen normal-form
equilibrium is not an additional input. It is not a stationary theorem,
a finite-calendar tester, a correlated equilibrium, or a conclusion only
against one-shot deviations.

## 2. Independent full-response derivation

Remove a and form the finite binary game whose payoff at coalition T of
free quitters is the original r(T+a). Let μ be any of its mixed Nash
points. The actual source
`quittingPersistentBaseNashSet_nonempty` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean` supplies
such a product point without sign or regularity assumptions. Its dependency
`mixedNashPolytopeSet_nonempty` in
`UniformEquilibrium/Finite/MixedNashSet.lean` only requires nonempty finite
individual action sets. An empty free-player type is harmless: its product
and all Nash inequalities are trivial. I also checked
`expectedUtility_persistentBase_eq_rootExpectedPayoff` and
`quittingPersistentBaseRoot_free_purePayoff_le` in the former file; the
binary rewards are the actual simultaneous coalition rewards.

Prescribe anchor Quit at date0; the free players independently sample μ
at date0 and use Never thereafter. Their behavior after a surviving date0
is part of the original profile, not a reaction they select after seeing
the anchor deviate. Off-path anchor behavior can be Continue. No one has
access to the simultaneous random choices of another player.

Let p_T be the induced complementary coalition probabilities. A nonanchor
deviation faces the sure date0 anchor, so every complete replacement reduces
to its binary first action. Its later behavior cannot affect the absorbed
payoff. The finite Nash inequalities therefore control its complete terminal
payoff, not just its one-stage gain.

For the anchor, first-date Quit pays

    V_a=p_∅s_a+∑_{T≠∅}p_T r_a(T+a).

After first-date Continue, a nonempty T has already absorbed at r_a(T).
On the literal empty event all opponents are now Never. The exact complete
continuation cap there is max(s_a,0)=s_a, attained by quitting at date1.
Thus the complete Continue-first cap is

    C_a=p_∅s_a+∑_{T≠∅}p_T r_a(T)≤V_a.

Every full behavioral replacement makes an independent binary first choice;
all later choices on its only possible continuing history are included in
this cap. Its full cap is max(V_a,C_a)=V_a. The argument remains valid
when these unconditional values are negative, when p_∅ is positive or one,
and when the deviator chooses Never or an unbounded random stopping date.
No opponent-deleted contraction or almost-sure absorption has been assumed
on the anchor-deviation branch. This distinction is load-bearing.

## 3. Finite horizons, fixed target, and boundary stress tests

For N≥1, the prescription pays exactly h_N V, h_N=(N−1)/N. A
nonanchor replacement remains bounded by h_N V_j. On an anchor deviation's
empty event, a later quit at date t≥1 pays
(N−t−1)_+ s_a/N≤h_Ns_a; Never pays zero and satisfies the same bound.
The nonempty events pay h_Nr_a(T), even when those rewards are negative.
Consequently the entire anchor deviation is bounded by h_N V_a. At N=1
all these averages are zero. The profile is exact Nash at every positive
horizon, and |h_NV_i−V_i|≤M/N gives a single fixed target before accuracy.
Nothing requires the deviator or its stopping time to be fixed across N.

The exact terminal result could also be consumed by
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The direct horizon proof is stronger: that general theorem alone need not
preserve this same profile at every horizon, whereas the new proof does.

I tested the empty-event and weak-own boundary independently on a two-player
table with anchor a:

    r({a})=(0,−2),       r({b})=(−5,−1),       r({a,b})=(−5,−2).

The anchor has s_a=0 and zero nonempty join gain. The induced free player
is indifferent, so take μ_b(Quit)=1/2. Then V=(−5/2,−2), and the
anchor's Continue-first cap equals −5/2, despite a positive empty event
and negative unconditional value. All finite-horizon bounds hold with
equality in the relevant comparison. This checks that no implicit
nonnegative target, strict join, or geometric tail was used.

Conversely the one-player table s_a=−1 makes the nonempty join condition
vacuous but the proposed immediate-Quit profile loses to Never0. Thus the
own-sign hypothesis cannot be silently removed from this producer. This is
a boundary of the construction, not a counterexample to UE existence.

## 4. Exact fixture and stationary-repeat falsification

I recomputed all seven anchor0 join differences: each is1. In its induced
game, player3 has strictly negative join difference−1 on every relevant
background and therefore uses Continue surely. Players1 and2 then have
differences −5+6q₂ and 1−2q₁, respectively. No boundary pair is Nash;
the unique point is (q₁,q₂,q₃)=(1/2,5/6,0).

The four probabilities (1/12,1/12,5/12,5/12) give exactly

    V=(43,2/3,1/2,125/3),
    C₀=505/12,                 V₀−C₀=11/12.

Repeating the same complementary hazards instead gives the anchor a
Never payoff504/11, exceeding43 by31/11. This is an actual complete
stationary deviation calculation, not a one-step annotation. The transient
off-path specification is therefore genuinely different. No stationary
compiler can be substituted by identifying first rows.

The sixteen pure coalition possibilities also recompute as stated. Sets
without0 admit its strict join; sets containing0 and3 admit3's withdrawal;
the four remaining possibilities have the binary matching-pennies toggle.
All Never loses to solo0. These are literal failures of `IsQuittingSureExitSet`
and `not_isQuittingSureExitSet_iff_strict_toggle` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

## 5. Separation from the actual anchor and persistent-base producers

I read `QuittingPersistentBaseComplementLeaveSafe` and
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.
Its raw inequality has the required completion quantifier, but its producer
requires base cardinality at least two. The new singleton-base transient
argument is not supplied by that theorem. All eleven eligible bases fail
on the author's explicit completion/member witnesses. The six pair gains
are −5,−1,−1,−1,−1,−1; the triple witnesses and the grand99<100
comparison also check. There is no alternate qualifying base hidden in the
fixture. The robust-predecessor subclass is consequently excluded.

The more general `QuittingSingleAnchorInducedDominance` in
`UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`
requires anchor Quit value≥0 and domination of EVERY excluded coalition
reward. I inspected its consumers
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint`,
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchor`, and the raw
membership producer
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership`.
The distinction is not merely that the membership special case fails.
The fixture excludes the complete induced-dominance screen for every anchor:

- Anchor0 has its unique value43<r₀(12)=100.
- For anchors1,2,3, free player0 strictly joins on every background and
  must Quit surely at every induced Nash point. The respective anchor values
  are bounded above by100,100,99 over all such points, but excluded coalition
  values1000,1000,100 exceed those bounds.

Thus the old stationary source cannot be recovered by selecting another
induced equilibrium. The exact background reversal for the positive edge
0→2 has join gain1 at0 and−1 at01. It falsifies
`QuittingNoStrictBackgroundReversal` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinStrictBackgroundReversal.lean`.

## 6. Other actual raw coverage tests

The thirteen direct quiet J witnesses check exactly. For the exceptional
child012 and outsider3, the three necessary rows are

    100≤λ₃₀,             −1≤−λ₃₂,
    −99≤−100λ₃₀+λ₃₂.

With nonnegative weights these are inconsistent. The literal source
`CappedClockParentFutureJoinCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`
requires these same F/J inequalities. This is a raw certificate exclusion,
not a conclusion about every separately chosen safe child profile.

The singleton matrix has determinant45 and the stated positive inverse.
I recomputed each triple inverse: the favorite-pair diagonal entries are
−1/6 and the unmatched entry is−3/2. The full matrix is R₀ and has
degree+1, using `r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`. The negative
determinant assumption in
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` and
`exists_uniformEquilibriumPayoff_of_strictlyPositive_singletonInverse`
in `UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
is not satisfied. The child source
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
also cannot apply to these negative child diagonals.

The strongest crossed-matching arbitrary-passive criterion and the
opposite-sign averaged-cap criterion fail on both harmful schedules at
player0: the individual cap sees r₀(01)=5>1, and the pair sum is6>2.
For the signed-column cone, a strictly positive Γ⁻¹ forces every σ_i=+1.
Those same caps fail on harmful words; on the favorite word player1 has
Π₁=−2,c₁=−5. An all-below two-pair producer is excluded on every word:
harmful mates give player0 c₀=1 and W₀>1, while the favorite word
gives Π₀=4 and U₀>1. These comparisons include relabelings and do not
guess a local persistence radius.

The only premium trap is I; no player has globally nonnegative participant
premiums. At background23 the forced-Quit floor coefficients are all
strictly negative, (−100,−101,−101,−101). At full trap/subset12 the
outside joining charge is101>0. The protected, proper-core, weighted-floor,
boxed/mixed-charge and product-low hypotheses therefore fail. Row sums1
exclude nonzero nonnegative terminal upper weights. The all-sure response
values (1,100,99,−1) and equal-scale consequence of
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
exclude all fourteen nondiscrete response partitions after positive affine
transport. Literal transitive Klein symmetry also fails: the singleton
pattern forces equal row scales under such a transitive transport, whereas
the grand rewards (1001,100,100,99) cannot then be invariant.

The weak-unit guard failures are on actual polynomial faces. The source
`quittingSingletonMatrix_nonpos_of_axis_displacement_nonneg` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
forces the passive choice to be the favorite. For the four remaining ordered
pairs, the stated pure-face gaps1,−1100,−1,−1 fail the corresponding
upper or lower guard in `QuittingOneSidedWeakUnitGuards` from
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
Every half-guard pair also includes a failed nonanchor lower face.

The `IsQuittingConditionalFaceGapRange` upper mixture from
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`
fails at player0 for every blocker: ContinueLower≤−100, while the two
Quit upper bounds are at least1 and1001. The actual influence2→1
changes from−101 at empty background to+6 at0; the sign-consistent and
affine membership predicates fail. Matching singleton signs exclude directed
three-child and four-cycle signs; the unique-negative paired and tournament
patterns fail too. Every off-diagonal singleton gap is nonzero. For the
explicit overlapping period-three visible cylinder, favorite pair participant
premiums at the center are zero, whereas the fixture pair01 premiums are4
and−2, after normalization by the unit harmful singleton gap. Positive affine
row transport preserves these ratios, so the explicit tiny cylinder is not
an overlap. The inspected literal center/visible-coordinate definitions are
`overlappingPeriodThreeRewardRow` and `IsInvisibleRewardCoordinate` in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`
and `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.

## 7. Significance and limits

The necessary condition really strengthens the known incoming raw-table
restrictions: every nonnegative-own player of a no-UE table must have a
negative join. The complementary arbitrary-completion family is consumed
by a complete original-game producer for every finite player cardinality.
The complete fixture is not absorbed by the applicable actual raw criteria
checked above, including the strongest accepted matching and signed-column
packets. Thus this is substantive counterexample-class narrowing, not merely
a new supplied-object interface or a better constant.

No absence of arbitrary stationary or other equilibria is needed or claimed.
Unspecified existential neighborhoods remain unspecified; no blanket
nonmembership or membership assertion is inferred. The proof has no remaining
strategic selection, continuation, off-path, correlation, or horizon input.
The initial live-zero convention and the indispensable off-path Never laws
are both explicit. I recommend mathematical acceptance and a later bounded
standalone artifact check, not another repeat audit of the same theorem.

## Final standalone: exact-byte assembly PASS

Read all 447 lines of the
[final standalone](../exports/ONE_SHOT_ANCHOR_UNIFORM_EQUILIBRIUM.md),
SHA256 `64cbf15fe912af117ee42d6d32a29806a8c72316cf88d28a7a8f85d06bdb6f02`.
Verdict: **final-artifact PASS**, with no requested repair or unresolved
objection. This is a bounded complete-artifact/delta check against the
independent substantive review above, not another base audit. No counterpart
review was read.

The arbitrary finite-player raw criterion and negative-join necessary
condition are preserved exactly. The producer still internally chooses the
finite complementary Nash point, specifies literal off-path Never for its
free players, retains the true empty-event cap, and proves exact terminal
and every positive-horizon Nash with one fixed target. Signed rewards,
zero singleton equality and unbounded behavioral deviations remain covered.
The two-player equality/negative-target regression and one-player negative-
own falsifier agree with my independent calculations above.

The expanded singleton-base explanation is literal: the existing
`QuittingPersistentBaseComplementLeaveSafe` predicate at base={a} is (A),
including its empty completion. Its old strategic consumer has a genuine
cardinality≥2 hypothesis; the new transient consumer fills that missing
case without pretending to invent a different finite Nash theorem.

The additional no-sure-stationary proof is sound and exhaustive. If some
j≠0 is sure, player0's first-date gain from joining is exactly1 on every
opponent outcome. Thus q₀ must also be1. With q₀=1 the other players
must use the unique induced point(1/2,5/6,0), and that profile is refuted
by the exact anchor Never value504/11>43. The same reasoning starts
directly if0 is the designated sure player. No assertion about all-proper
stationary equilibria has been added.

I inspected the added actual one-date consumers
`quittingOneDateThenNeverProfile_exactHorizonNash` and
`quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness` in
`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`.
Their required exact terminal premise is produced in the packet. They do
not produce the anchor inequalities or its finite-game root, so they are
not overlapping raw existence theorems.

The new local-source comparison is intrinsic and correct. In
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`,
`AdaptiveChildCenter.exists_nearby_oneDate_sameProfile_horizon_equilibrium`
requires and produces three probabilities strictly between1/4 and3/4.
The literal definitions `nearbyProfile`, `nearbyRoot_anchor`, and
`nearbyRoot_active_true` in
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyOneDate.lean`
and `UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyInteriorRoot.lean`
identify one sure anchor and those three proper first-date coordinates.
For anchor0 the fixture forces free3=0; for any other anchor it forces
free0=1. Thus it cannot possess the needed all-proper complementary Nash
point under any relabeling. These are strict finite-game signs, preserved
by positive affine utility transport. The comparison neither guesses a
radius nor rules out arbitrary existential neighborhoods by fiat.

The explicit outsider-axis face formula added in Section9 evaluates
negatively for all four listed favorite premiums, including4. All other
coverage arithmetic and the fourteen-child F/J contradiction are preserved.
All twenty-two cited Lean paths are tracked. There is no dependency on
math-folder content, untracked helpers, reviewer narrative or process
history inside the packet. Its significance remains the actual necessary
condition on every counterexample plus an uncovered arbitrary-completion
raw class; it is not merely an interesting verifier. No new Lean seal or
full-conjecture claim is made by this acceptance.
