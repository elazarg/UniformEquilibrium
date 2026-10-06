# Independent review of the one-shot anchor producer

Reviewer: CODEX_MORSE.

Verdict: **PASS**, with no unresolved mathematical objection, for the
377-line candidate
`../notes/CODEX_NOETHER__ONE_SHOT_ANCHOR_NEGATIVE_JOIN_NECESSITY.md`,
SHA256 `72e18f442d25d6225b96e022b42c573f3542809fc7ce955ce9dfb66b7ad7b331`.
This verdict covers the complete raw producer, unrestricted terminal and
finite-horizon claims, the necessary condition for every counterexample,
and meaningful additional raw-table coverage. It is ordinary mathematics,
not a Lean build or kernel-verification claim. No counterpart review was
read. A later standalone requires a bounded final-artifact check.

## The statement actually proved

For any finite nonempty player set, suppose one player a has s_a≥0 and
every nonempty coalition S excluding a satisfies

    r_a(S∪{a})≥r_a(S).

Then the theorem produces a one-date-then-Never profile with a sure
date-zero anchor. It is exact terminal Nash against all behavioral
replacements, exact Nash at every positive finite horizon, and delivers
one fixed terminal vector with error at most M/N. Other own levels,
all other players' rewards, and the signs of the produced payoff are
unrestricted. No equilibrium point or stopping certificate is an input.

Consequently, every no-uniform-payoff table has a strictly negative
nonempty joining comparison at every player whose own singleton is
nonnegative. The quantifier over every such player follows by applying
the producer separately to any proposed exception. The same implication
holds for a positive unrestricted terminal-exploitability floor, since
the constructed profile has exactly zero debt.

## The finite producer and full behavioral proof

The complementary binary game pays r(T∪{a}) at action coalition T.
It is a finite complete game, including at T=∅. Its mixed Nash point
is supplied internally by the finite Nash theorem; arbitrary signed
utilities and zero/sure mixed coordinates cause no difficulty. The
empty complement also works. I checked the utility and Nash-set
definitions, not only the name of their nonemptiness theorem, in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`.
`quittingPersistentBaseNashSet_nonempty` has exactly the needed scope.

Under any nonanchor replacement the prescribed anchor still quits
surely at date zero. Thus the whole replacement reduces to that player's
first binary action and is bounded by the induced Nash inequality.
No later off-path specification can alter its payoff.

For the anchor, following first-date Continue, nonempty T has already
absorbed and the empty event leaves every opponent permanently quiet.
Its exact subsequent terminal cap on the latter event is max(s_a,0)=s_a.
Thus the complete first-Continue cap is

    p_∅s_a+Σ_{T≠∅}p_T r_a(T),

whereas first Quit pays p_∅s_a+Σ_{T≠∅}p_T r_a(T∪{a}). The raw
inequalities compare these term by term. Randomizing the initial action
cannot reveal simultaneous opponent choices. Every later strategy,
including Never and unbounded random stopping, is already bounded by
the empty-event cap. This is a genuine unrestricted proof.

The distinction from stationary repetition is indispensable. No contraction
of the anchor-deleted profile is assumed; that profile can have positive
Never probability. Zero on that event is retained, rather than silently
translated with the absorbing rewards. This is exactly where s_a≥0
is needed.

## Literal horizons and adversarial boundary tests

The initial live-zero convention gives prescribed N-date payoff
(N−1)V/N for N≥1. Nonanchor deviations multiply their binary payoffs
by the same nonnegative factor. For an anchor who first Continues,
the nonempty contributions have that same factor, and its empty-event
reward from quitting at t≥1 is at most (N−1)s_a/N. This remains
correct when the nonempty contributions and V_a are negative. Thus
regret is exactly zero, while delivery error is at most M/N. The target,
mixed point and profile are fixed before the accuracy parameter.

I tested weak equalities and a negative target on the following complete
three-player table, with anchor 0:

    r(0)=(0,0,1),      r(1)=(−4,−7,0),     r(2)=(3,0,−5),
    r(01)=(−4,1,0),    r(02)=(3,1,0),      r(12)=(−2,0,0),
    r(012)=(−2,0,1).

All nonempty anchor joining gains are zero and s₀=0. The complementary
matching-pennies game has q₁=q₂=1/2. Its target is
(−3/4,1/2,1/2), and the anchor's full Continue cap is also −3/4.
The empty event has probability 1/4 and cannot be suppressed. The
terminal and finite-horizon inequalities hold exactly, showing that
neither positive V_a nor nonnegative nonanchor own levels are hidden
assumptions.

Changing only r₀(0) to −1 keeps every nonempty anchor joining comparison
unchanged but makes the prescribed anchor payoff −1. Never gives −3/4,
an improvement of 1/4. Thus dropping s_a≥0 would invalidate this
producer. This is a test of the hypothesis, not a game-level counterexample
to uniform existence.

The exact existing consumer
`quittingOneDateThenNeverProfile_exactHorizonNash`, and its companion
`quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness`, in
`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean` can consume
the newly proved terminal-Nash profile. They do not already supply the
new anchor selection. The manuscript's direct horizon proof is also
complete on its own.

## Exact full table and raw-source checks

I recomputed the seven anchor joining gains, all equal to one, and the
complementary differences: player 3 always has gain −1, and players
1,2 have respectively endpoint pairs (−5,1) and (1,−1). The unique
complementary Nash probabilities are therefore (1/2,5/6,0). Direct
averaging gives

    V=(43,2/3,1/2,125/3),
    anchor first-Continue cap=505/12,
    stationary-repetition Never payoff=504/11>43.

The last calculation uses the actual geometric conditional nonempty
law and proves that the proposed one-shot profile cannot simply be
replaced by its repeated stationary row.

Every pure coalition has the claimed strict deviation. The eleven
eligible persistent bases have the listed negative leaving comparisons.
In particular the exact predicate
`QuittingPersistentBaseComplementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`
does include the anchor inequalities for a singleton base, interpreting
the empty reward as zero. But its strategic consumer
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`
explicitly requires base cardinality at least two and constructs a
stationary profile. It does not cover this missing singleton-base case.

The stronger stationary-anchor predicate
`QuittingSingleAnchorInducedDominance` in
`UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`
requires domination of every excluded terminal reward, not only the
weighted contemporaneous comparison used here. The candidate fails it
for every anchor and every induced Nash point, by the manuscript's
exact bounds. Thus the existing literal-membership corollary does not
consume the new arbitrary-completion family.

All fourteen nonnegative F/J tests check. For the exceptional child 012,
the J tests at 12 and 01 give λ₃₀≥100 and λ₃₂≤1, while F at 012
gives −99≤−100λ₃₀+λ₃₂, hence λ₃₀≤1. The other thirteen tests
have a positive omitted joining gain and nonpositive child coordinates.
This is a direct contradiction of the raw certificate, not an assertion
that every selected child equilibrium has an unsafe lift.

I checked the remaining finite screens against the stated table: full
R₀/degree +1, principal inverse signs, every matching cap failure, the
all-three-schedule below-floor output exclusion, sole premium trap I,
absence of any protected player, strictly negative forced-floor vector
at 23, positive intermediate leave charge 101, and product-low failure
at sure I. The all-sure displacement vector is exactly (1,100,99,−1),
giving the response-partition exclusion after the row-sum test. Conditional
range and signed-influence witnesses are literal reward differences.

For the one-sided lower guards, a useful explicit check fills the small-
hazard step: when the chosen passive player is not the favorite f(i),
use only favorite hazard 1/2. The owner's stationary displacement is

    (1/2)[−3+(r_i({i,f(i)})−s_i)/2]<0,

because these four favorite-pair premiums are 4,−2,−101,−101. This
excludes all eight nonfavorite choices. The four remaining favorite
choices fail the listed pure upper or lower faces. Thus the guard
exclusion does not confuse pointwise nonnegative anchor joining with
nonnegative stationary displacement at small opponent hazards.

## Additional exact structural separation

The same table actually has no stationary equilibrium with any sure
quitter. If some j≠0 is sure, every opponent outcome faced by player 0
is nonempty, and its first-date Quit-minus-Continue difference is exactly
one. Therefore player 0 must also be sure. Once q₀=1, every stationary
equilibrium must use the unique complementary Nash point
(q₁,q₂,q₃)=(1/2,5/6,0). This sole candidate fails player 0's Never
comparison 504/11>43. The argument exhausts all sure boundaries,
without making any claim about all-proper stationary profiles.

There is a second useful comparison with an existing transient producer.
`AdaptiveChildCenter.exists_nearby_oneDate_sameProfile_horizon_equilibrium`
in `UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`
outputs one sure anchor and all three free probabilities in (1/4,3/4).
For anchor 0 the present table forces free player 3 to probability zero.
For any other anchor it forces free player 0 to probability one. Hence
no anchoring label has an all-proper complementary Nash point. The same
strict signs survive positive affine row transports. This excludes the
actual output of that existing neighborhood producer; no unknown radius
is being guessed.

Both extra separation facts were sent to the author as mathematical
checks, not used to change the frozen theorem. Together with the direct
source comparisons, they confirm genuinely new arbitrary-completion
coverage and a global necessary condition on every possible counterexample.
No full-conjecture claim, generic proper-stationary exclusion, or new Lean
seal is warranted.
