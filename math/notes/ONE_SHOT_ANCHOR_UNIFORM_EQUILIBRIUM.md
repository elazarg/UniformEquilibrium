# Every quitting counterexample needs a negative join at each nonnegative-own player

Status: proved ordinary mathematics. The exact same-profile terminal and
positive-horizon Nash construction is valid. Its entire UE existence class,
including the complete rational example, is already covered by the tracked
singleton-base punishment-tail consumer. The source inclusion below makes
this distinction explicit; this note asserts no additional counterexample
exclusion.

## 1. Exact necessary condition and whole raw family

Let I be any nonempty finite player set. At each live date the players
independently choose Continue or Quit, using private randomization and public
past actions. A nonempty quitting coalition S absorbs at an arbitrary finite
signed vector r(S). Live dates pay zero, including the absorption-selection
date; subsequent dates pay r(S). Infinite all-Continue pays zero. Strategies
and unilateral replacements are arbitrary complete behavioral strategies.
Every payoff and equilibrium assertion is in expectation.

Write s_i=r_i({i}). No own-singleton normalization or sign restriction is
imposed globally. There is no public correlation, payoff translation,
discounting, or bound on a deviator's stopping time.

**Necessary condition.** If this original game has no uniform-equilibrium
payoff, then for every player a with s_a≥0 there is a nonempty coalition
S⊆I\{a} such that

    r_a(S∪{a})<r_a(S).                                  (N)

The same necessary condition holds for a strictly positive lower bound on
unrestricted terminal exploitability, since the complementary raw class
below has an exact terminal Nash profile. This is a condition on every
possible counterexample, not on a supplied strategy or restricted tester.

The producer proving (N) is stronger than uniform existence. Suppose one
anchor a satisfies the finitely many raw inequalities

    s_a≥0,
    r_a(S∪{a})≥r_a(S)       for every ∅≠S⊆I\{a}.        (A)

Then an internally selected one-shot profile is exact terminal Nash and
exact Nash at every positive finite horizon. One fixed terminal vector is
delivered within M/N at horizon N≥1, where M=max_{i,S≠∅}|r_i(S)|.
All other reward coordinates and all other own-singleton signs are arbitrary.
Thus (A) describes a whole arbitrary-completion family for every finite
cardinality. There is no supplied root, equilibrium point, value, or
controller certificate in the theorem's inputs. Equalities in (A), including
s_a=0, are included directly without a closure argument.

## 2. Internally selecting the finite binary Nash point

Let J=I\{a}. Form the finite normal-form game in which each j∈J chooses
one binary action, Quit0 or Continue0. If its action coalition is T⊆J,
the utility vector for the free players is the actual original reward
r(T∪{a}). This is defined even at T=∅, because the anchor is present.

The finite mixed-Nash theorem produces one product distribution μ on
these binary actions. Fix any such point once. It may have zero, proper,
or sure coordinates; none is assumed. If J is empty the product and its
Nash property are trivial. The exact finite dependency inspected is
`quittingPersistentBaseNashSet_nonempty` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`, with
base={a} and free=J. It reduces to `mixedNashPolytopeSet_nonempty` in
`UniformEquilibrium/Finite/MixedNashSet.lean`. These are finite-game
existence statements, not an original-game stopping-cap conclusion.

Prescribe the following full behavioral profile:

    anchor: Quit surely at date0;
    each free player: use its independent μ coordinate at date0;
    after date0: every surviving free player always Continues.

The free player's sampled Continue0 action therefore means literal Never,
not repeated mixing at later dates. Its behavior after date0 is specified
also on histories created by an anchor deviation. The anchor can be assigned
Continue at later live histories, which have zero probability under the
prescribed profile and do not affect any nonanchor unilateral replacement.

This uses private independent randomization only. It is crucial that this
transient profile is not identified with the stationary profile having the
same first row. Section5 gives an exact falsifier of that identification.

## 3. Complete-response terminal proof

Let p_T be the complementary date0 coalition law. The prescribed payoff is

    V_i=∑_{T⊆J}p_T r_i(T∪{a}).                          (1)

For a nonanchor j, the anchor still Quits surely at date0 under every
unilateral replacement of j. Therefore date0 absorbs regardless of j's
action. Its entire behavioral replacement reduces to its mixed binary
choice at that date. The finite Nash inequalities for μ prove payoff≤V_j.
Choosing Never, a late deterministic date, or an unbounded stopping law
does not change the Continue0 payoff, because the game has already absorbed.

For the anchor, immediate Quit gives

    V_a=p_∅s_a+∑_{T≠∅}p_T r_a(T∪{a}).                  (2)

If it Continues at date0, each nonempty T has already absorbed at r_a(T).
On T=∅ all free players Continue forever. There is only the anchor left
with any possibility of quitting, and its full later terminal cap is
max(s_a,0)=s_a. It is attained by Quit at date1; literal Never pays zero.
Every arbitrarily late, randomized, or history-dependent replacement is
bounded by this same cap. Hence the exact cap after first-date Continue is

    C_a=p_∅s_a+∑_{T≠∅}p_T r_a(T)≤V_a.                 (3)

The inequality follows term by term from (A). At date0 the anchor does not
observe its opponents' simultaneous actions. Any behavioral replacement
randomizes independently between first-date Quit and Continue, and its
subsequent live behavior is already included in (3). Its payoff is bounded
by max(V_a,C_a)=V_a. This proves exact terminal Nash against every full
behavioral replacement.

There is no opponent-deleted contraction assumption: under an anchor
deviation, the empty event can genuinely remain Never. Its zero payoff has
been included in max(s_a,0), not discarded by almost-sure absorption or
an affine reward change. Negative rewards on the nonempty events also
remain exactly as given. This is why the own-sign hypothesis s_a≥0
must be used explicitly.

## 4. Exact positive-horizon Nash and fixed target

For N≥1 the horizon contains dates0,…,N−1. A date0 absorbing coalition
has average payoff h_N r(S), with h_N=(N−1)/N, because date0 still pays
the live reward. The prescribed payoff is exactly h_N V.

For every nonanchor replacement the same first-date absorption argument
applies. Its payoff is h_N times its binary-game payoff, so the finite
Nash inequalities remain valid even when that payoff is negative.

For an anchor replacement whose first action is Continue, each nonempty
T gives the fixed contribution h_N r_a(T). On the empty event, a quit
at date t≥1 gives [(N−t−1)_+/N]s_a, where u_+=max(u,0), and Never
gives zero. Since s_a≥0, every such finite-horizon continuation payoff
is at most h_N s_a. Thus its entire payoff is bounded by

    h_N[p_∅s_a+∑_{T≠∅}p_T r_a(T)]≤h_N V_a.

First-date Quit gives exactly h_N V_a; every mixture of the two first
actions is bounded likewise. The profile is therefore exact Nash at every
positive finite horizon, not just asymptotically. No assertion at N=0 is
needed. The terminal and every positive-horizon profile are the same.

Because |V_i|≤M, prescribed delivery satisfies

    |h_N V_i−V_i|≤M/N.

Fix μ, the profile, and V once, before accuracy. For any ε>0 choose an
integer threshold≥max(1,M/ε); every larger horizon has zero regret and
delivery error≤ε for these same objects. This establishes an original-game
uniform-equilibrium payoff, and contraposition proves (N).

The tracked consumer `quittingOneDateThenNeverProfile_exactHorizonNash`
in `UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`
likewise turns exact terminal Nash of any one-date/Never profile into
exact Nash at every finite horizon. Its companion
`quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness`
preserves the profile and terminal target before accuracy. These are
downstream consumers, not producers of the raw anchor class (A).
The direct proof above establishes their needed terminal premise and
the stronger explicit delivery bound without another strategy input.

### Weak-own boundary, negative target, and genuine Never mass

For two players a,b take the complete table

    r({a})=(0,−2),     r({b})=(−5,−1),     r({a,b})=(−5,−2).

Anchor a has s_a=0 and zero nonempty joining gain. Its induced free
player is indifferent, so choose μ_b(Quit0)=1/2 internally from the
nonempty finite Nash set. The target is V=(−5/2,−2). The anchor's
Continue-first cap is also−5/2: on the event b Continues, of probability
1/2, every opponent is literal Never and the cap is zero; on the other
event the reward is−5. Thus neither a positive target, a strictly positive
own level, strict joining inequalities nor zero empty mass is required.
The finite-horizon argument applies with equality in this cap comparison.

The own-sign hypothesis cannot be dropped from this producer. In the
one-player table s_a=−1, every nonempty opponent comparison is vacuous,
but its prescribed immediate Quit gives−1 and loses to Never0. This
is a falsifier of that proposed extension, not a counterexample to
uniform existence.

## 5. Complete rational table and the false stationary repetition

Take I={0,1,2,3}, anchor0, all s_i=1. This entire sixty-coordinate table
has favorable singleton gap3 and both harmful gaps−1 in every row, with
favorite matching(01)(23).

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,−1,1,0) |
| 02 | (1,0,1,0) |
| 03 | (1,4,0,−1) |
| 12 | (100,−100,−100,1000) |
| 13 | (100,−100,1000,−100) |
| 23 | (−100,1000,−100,−100) |
| 012 | (101,1,0,100) |
| 013 | (101,−1,1,−1) |
| 023 | (−99,0,1,−1) |
| 123 | (1000,−100,−100,1100) |
| 0123 | (1001,100,100,99) |

All seven nonempty anchor joining gains are exactly1, and s_0=1. In the
anchored complementary game, player3 has joining gain−1 on every
background containing0 and therefore always Continues. With3 absent,
player1's joining gain is−5 if2 Continues and+1 if2 Quits; player2's
is+1 if1 Continues and−1 if1 Quits. This matching-pennies pair has
the unique mixed Nash point

    (q_1,q_2,q_3)=(1/2,5/6,0).

The complementary probabilities for∅,1,2,12 are1/12,1/12,5/12,5/12.
The produced complete profile has first row(1,1/2,5/6,0) and all later
free-player hazards zero. Its exact terminal vector is

    V=(43,2/3,1/2,125/3).

The anchor's first-date Continue terminal cap is505/12<43. If instead
these free hazards are repeated forever, its Never payoff becomes the
conditional nonempty singleton/pair lottery

    (4/12+100·5/12)/(11/12)=504/11>43.

Thus the stationary repetition is not terminal Nash. The minimal failed
implication is “an anchored binary Nash row automatically gives a stationary
quitting equilibrium.” The proof here avoids precisely that false step by
retaining the actual transient laws.

## 6. Pure, leave-safe and single-anchor stationary source exclusions

No pure exit exists. Any nonempty coalition excluding0 is strictly joined
by0. Any coalition containing0 and3 is profitably left by3. With0 but
not3, players1,2 have the matching-pennies instability, so one toggles.
All Never loses to0's own Quit1. This directly tests the pure sure-set
criterion of `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The implemented arbitrary-completion persistent-base family requires a
base of size≥2 whose members never lose by remaining, uniformly over all
complementary action coalitions. The six pair bases01,02,03,12,13,23
have respective (coalition,member) counterexamples
(01,1),(012,2),(03,3),(012,2),(013,3),(023,3), with joining gains
−5,−1,−1,−1,−1,−1. Each displayed coalition contains its base. The
four triple bases012,013,023,123 fail at their own coalitions for members
2,3,3,1 with gains−1,−1,−1,−1100. The full base fails by3's99<100.
These exhaust every eligible base. The precise raw definition and consumer
are `QuittingPersistentBaseComplementLeaveSafe` and
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.
For the singleton base={a}, that raw predicate is exactly (A): its empty
completion uses the literal empty reward zero, requiring s_a≥0, and its
other completions are the nonempty joining comparisons. That particular
strategic consumer assumes base cardinality≥2 and constructs stationary
repetition. The transient construction here extends its exact same-profile
conclusion to singleton bases. A different implemented singleton-base
punishment-tail consumer already covers the UE existence claim, as shown
below.
Its robust-predecessor subclass also fails. Moreover the positive singleton
join0→2, with gain1, reverses to−1 on background1, violating
`QuittingNoStrictBackgroundReversal` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinStrictBackgroundReversal.lean`.

The implemented single-anchor stationary family requires an induced
complementary Nash point whose anchor Quit value dominates zero and every
excluded terminal reward. Anchor0's unique point gives43<r_0(12)=100.
For any other designated anchor, free0 has strict joining gain1 and must
Quit surely at every complementary Nash point. Anchor1's immediate value
is then≤100<r_1(23)=1000; anchor2's is≤100<r_2(13)=1000;
anchor3's is≤99<r_3(012)=100. These are bounds over EVERY induced
Nash point, not failure at one selected point. The exact predicate is
`QuittingSingleAnchorInducedDominance` and the raw literal-membership
producer is `exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership`
in `UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`.
The new theorem replaces that stronger stationary screen by (A) and a
different, fully specified transient profile.

In fact this table has no stationary terminal Nash profile with any sure
quitter. If j≠0 is sure, every opponent outcome faced by player0 is
nonempty, so its first-date Quit-minus-Continue difference is exactly1.
A stationary Nash profile must therefore also have q_0=1. With q_0=1,
each nonanchor's entire replacement reduces to its binary first action,
forcing the unique complementary Nash point(1/2,5/6,0). The same point
is forced if0 was the initial sure quitter. This sole candidate fails
player0's stationary Never comparison504/11>43. This exhausts all sure
stationary boundaries, not all-proper stationary profiles.

An existing transient neighborhood producer has a different intrinsic
output requirement.
`AdaptiveChildCenter.exists_nearby_oneDate_sameProfile_horizon_equilibrium`
in `UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`
produces one sure anchor and three free probabilities in(1/4,3/4).
Its `nearbyProfile` in
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyOneDate.lean`
is a one-date/Never profile; `nearbyRoot_anchor` and
`nearbyRoot_active_true` in
`UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyInteriorRoot.lean`
identify its sure and proper coordinates. For anchor0 the present table
forces free3=0. For any other anchor it forces free0=1 by strict joining
gain1 on every background. Hence no anchor label has an all-proper
complementary Nash point. These strict signs survive positive playerwise
affine reward transports. This excludes the actual output architecture
without guessing an existential neighborhood radius.

## 7. All fourteen actual nonnegative quiet F/J children fail

The relevant raw family chooses a nonempty proper child S and weights
λ_ki≥0 so that, for every nonempty T⊆S and outsider k,

    s_k−r_k(T)≤∑_{i∈S}λ_ki[s_i−r_i(T)],
    r_k(T∪{k})−r_k(T)
      ≤∑_{i∈S}λ_ki[r_i(T∪{i})−r_i(T)].                 (F/J)

If S excludes0, take T=S: outsider0 gains1 and every child joining gain
is zero. If S contains0 and omits2, use T=0 for S=0 or01, and T=03
for S=03 or013: outsider2 gains1 and all child joining gains are
nonpositive. If S contains02 but omits1, use T=S: outsider1 gains1
at02 or100 at023, while child gains are zero. These cases exhaust all
children except012.

For child012 and outsider3, its J row at T=12 forces λ_30≥100.
Its J row at T=01 forces λ_32≤1, since the outside gain is−1 and
the only nonzero child gain is player2's−1. Its F row at T=012 gives

    −99≤−100λ_30+λ_32,

which would force λ_30≤1. Contradiction. No child and no nonnegative
weight family satisfies the actual raw F/J inequalities. This is not
merely absence of a supplied quiet-child strategy certificate. Some
separately selected child equilibrium may nevertheless lift safely;
that stronger nonexistence claim is not made.

## 8. Other matching and matrix families

Let Γ_ii=0 and Γ_ij=r_i({j})−s_i. Here Γ is

    [[0,3,−1,−1],[3,0,−1,−1],
     [−1,−1,0,3],[−1,−1,3,0]].

It has determinant45 and strictly positive inverse with diagonal2/15,
favorite entries7/15 and other entries1/5. All principal pairs and
triples are nonsingular and each singleton column has a negative entry,
so it is R₀; its nonnegative-inverse degree is+1. Harmful principal
pairs are not Q and each triple inverse has negative diagonals. Thus the
negative-determinant, degree-not-one and child-nonnegative-inverse exits
do not apply. Exact sources inspected are
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`,
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`, and
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

The arbitrary-passive crossed matching criterion requires outsider joins
bounded by own levels. Both harmful scheduled matchings fail at
r_0(01)=5>1. The stronger opposite-sign family allowing average pair
caps still requires their sum≤2s_0, or a smaller bound for a below-own
type. Both harmful words give player0 sum6>2. A general positive-inverse
harmful-mate producer has the same cap failure. The signed-column cone
requires Γ⁻¹diag(σ)>0, so every σ is positive here. On harmful words
player0 has positive c_0 and zero buffer, again requiring the failed
individual cap. On favorite word01/23, player1 has Π_1=−2,c_1=−5,
contradicting the positive-column signs. These are finite raw failures.

Every all-below-singleton proper two-pair output is intrinsically excluded:
on either harmful word player0 has Π_0=0 and mate comparison−1, forcing
W_0=1+X_mate>1; on favorite word its Π_0=4 forces U_0=1+4q_1>1.
These cover all three partitions and all their relabelings without a
guessed radius for any local persistence theorem.

## 9. Further finite-source tests and limits

The only premium trap is I. In every proper coalition some member has
no positive participant premium at any subcoalition containing it; at I
all four grand premiums are positive. The greatest core is therefore full.
No player is protected: use023 for0,01 for1,12 for2,03 for3.
At background23 the four forced-Quit premiums are
(−100,−101,−101,−101), excluding every nonzero nonnegative global
forced-Quit floor weight. At full trap I and subset12 the aggregate
outside joining charge is101>0, excluding intermediate nonpositive-L
criteria. Sure I violates product-low and supportwise premium balance.

The singleton row sums are1, so Γᵀλ≤0 with λ≥0 forces λ=0. All-sure
displacements are(1,100,99,−1), distinct. The block-row-sum necessity
forces equal positive row scales within a response block, which then
cannot have equal all-sure displacements. This also excludes every
nondiscrete response quotient after positive affine row transport. The
exact sources are
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`
and `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

All ordered crossed weak-unit guards fail. If the selected passive partner
is not the favorite f(i), put only the favorite's hazard at1/2. The lower
displacement face then has owner value

    (1/2)[−3+(r_i({i,f(i)})−s_i)/2]<0.

The four favorite participant premiums are4,−2,−101,−101, so every
nonfavorite choice fails this necessary nonnegative face. This is also
captured by `quittingSingletonMatrix_nonpos_of_axis_displacement_nonneg`
in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`.
For the remaining four choices, owner0 fails passive1's upper face at02 (gain1); owner1
fails its lower face at23 (gain−1100); owners2 and3 fail their lower
faces at01 (gain−1 each). Every two-owner half guard includes a
nonanchor owner and fails its corresponding lower witness. The exact
structures are `QuittingHalfWeakPolynomialGuards` and
`QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
and `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.

For every conditional range blocker, player0 has ContinueLower≤−100,
QuitWithoutUpper≥1 and QuitWithUpper≥1001. Their convex upper mixture
is≥1, contradicting its upper inequality. This uses
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
Influence2→1 is−101 at∅ and+6 at{0}, falsifying
`SignConsistentQuittingInfluence` and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

The favorable graph is a matching, not a four-cycle or cyclic three-child;
two harmful singleton comparisons in each row exclude the unique-negative
paired and tournament patterns. No off-diagonal Γ entry is zero, excluding
the literal owner-risky family. The explicit visible period-three cylinder
has participant pair gap ratios near zero with radius1/50000000; pair01
has ratios4 and−2 and therefore fails, including positive affine transports.
The literal center and visibility sources are
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`
and `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.

No absence of arbitrary proper-three or full-support stationary profiles
is asserted. No unspecified local neighborhood is blanket-excluded or
claimed to contain this table. An arbitrary supplied-root verifier is not
a producer for the raw completion family. These separations exclude the
displayed stationary, withdrawal and matrix criteria, not every implemented
UE producer. In particular, the singleton-base punishment-tail source
already admits this table and the entire family (A).

### Whole-class inclusion in the implemented singleton-base source

Choose the internally available induced product Nash point on I∖{a}.
Let p_T be its coalition law, V_a its anchored prescribed payoff, and
P_a the punishment value. The source's owner floor excess is exactly

    floorExcess = ∑[T≠∅]p_T r_a(T) + p_∅P_a − V_a
                = −∑[T≠∅]p_T[r_a(T∪{a})−r_a(T)]
                  + p_∅(P_a−s_a).

The tracked theorem `quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives
P_a≤max(s_a,0)=s_a. Condition (A) therefore gives floorExcess≤0.
With free=I∖{a}, there are no omitted outsider conditions. Thus the
positive-gap arm of `exists_uniformPayoff_or_singletonBase_pos_gap`
cannot hold. Its certificate is consumed by
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.
The floor definition, induced-Nash certificate constructor, and alternative
are in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

Consequently both UE for (A) and the necessary condition (N) follow from
existing production sources. The additional result proved here is an exact
terminal and every-positive-horizon equilibrium using one fixed transient
profile, rather than error-dependent punishment continuations.

## 10. Formalization shape and semantic boundary

The finite Nash dependency is already available as named in Section2.
An implementation should construct the date0/Never product laws and their
full behavioral realization, then prove the exact two first-action cap
formulas, preserving the true empty event. A stationary or opponent-
contraction compiler is not applicable to the anchor-deleted profile.
The final theorem can quantify over arbitrary finite I, reward, and anchor
satisfying (A), and produce one exact terminal Nash profile with zero
regret at every positive horizon and one fixed UE target. Contraposition
then gives (N) directly for every no-UE or positive-gap table.

This is ordinary mathematics with named existing Lean dependencies, not
new Lean verification. No unrestricted stationary-completeness theorem,
full-conjecture conclusion, or new trust seal is claimed.
