# Vanishing-debt atom access and executable chronological shadowing

Author: `CODEX_CEDAR`
Status: `BLOCKED_AT_EXACT_ADAPTER`

Current status: the exact target is much stronger than putting each static atom
behind an increasingly long exact Nash-root word.  A single certificate must
choose one infinite executable root sequence and candidate tails indexed by
absolute time.  Its forcing bounds are uniform over every player and every
starting time, both joint and player-deleted survival must vanish from every
starting time, and every candidate debt coordinate at time zero must be at most
the requested accuracy.  The actual atom access gives a fixed mover, observer,
and charge, but an unrelated alternative at each sufficiently large frontier
rank.  The exact-prefix adapter gives a separate word of length `rank + 1` for
each rank; it explicitly supplies no prefix coherence and its two-active branch
has joint survival tending to one, not zero.  This is an interface audit, not
yet a no-go theorem.  Section 4 recovers one piece which the packaged atom
alternative erased: before the prescribed/rectangle split, the actual positive
off-diagonal construction always supplies a common pure-time response whose
debt at the full mover-reset endpoint tends to zero.  This remains true when
the exported atom takes its prescribed arm.  On a finite active transfer cycle
the recovery can be simultaneous with one uniform positive gain margin, but
the resulting endpoints are frozen profiles over a common source, not
successive executable tails.  The exact period-two test in section 7 shows
that the active-transfer ``cycle'' does not repair this: it is cyclic in the
labels of tangent recipients, but its actual reset-cube path only inserts
coordinates.  After the two active coordinates have been inserted the face
has saturated, and recurrence would require an uncontrolled reverse reset or
a jump to a new rank-dependent source.  Thus even the smallest transfer cycle
is not a debt-excursion return.  Section 8 recovers a different, genuinely
scale-free conclusion: compactifying the common-response endpoints and
minimizing on the observer-reset face transfers the observer's entire positive
base debt to the other coordinates.  This works before the atom disjunction,
including its prescribed arm.  The selected reset-face point, however, has
all-Continue as its unique exact cap--Nash root, so the transfer ends at the
precise nonabsorbing obstruction rather than at a forward return.

Handoff condition: at the branch-independent reset-face minimizer from
section 8, can a sequence of non-cap--Nash roots have divergent joint and
player-deleted absorption while its prescribed defects have uniformly small
interval sums and its adverse direct-debt forcing is summable?  Uniqueness of
the all-Continue exact cap--Nash root rules out a zero-defect absorbing root,
but does not give the quantitative residual-to-absorption modulus needed to
rule out sparse approximate roots.  The actual source currently supplies no
such modulus.  Until one is supplied, this notebook's atom-access route is
stopped at an exact interface deficit; the active work has pivoted to the
distinct source-matched fresh radial packet obligation.

This route is a pivot from the exact paid-row adapter deficit in
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](CODEX_CEDAR__PAID_ROW_REENTRY.md): neither
route should borrow the other's missing chronology or return datum silently.

## 1. Exact producer obligation

Fix a finite player type `I`, rewards on every nonempty quitting coalition, a
`QuittingTerminalExploitabilityWitness`, an extracted
`QuittingPositiveMinimumDebtTangentFamily`, and
`access : QuittingVanishingDebtAtomAccess frontier`.  Thus there are fixed

- `mover` in the positive-debt support;
- `observer != mover`;
- `charge > 0`; and
- for all sufficiently large ranks, a
  `HasQuittingStoppingLawVanishingDebtAtomAlternative` at the literal source
  profile and selected mover replacement, with decoder error tending to zero.

For every real `eta > 0`, construct a
`QuittingChronologicalDebtShadowingCertificate reward eta`.  Its data are one
infinite sequence of executable product roots and, at every absolute time,
candidate prescribed payoff, nonnegative candidate debt, and generated
secant.  The nontrivial quantifiers are exactly:

1. for every player, start, and finite length, prescribed forcing discrepancy
   is at most `eta`;
2. for every player and start and every slack `> 0`, eventually in the suffix
   length, the survival-weighted adverse direct-debt forcing is at most
   `eta + slack`;
3. for every start, joint survival tends to zero;
4. for every player and start, player-deleted survival tends to zero; and
5. for every player, candidate debt at absolute time zero is at most `eta`.

The order matters.  A rank-dependent finite word does not meet `for every
start` on one infinite schedule, and a limit taken separately after choosing a
player or start does not provide the simultaneous certificate.

## 2. Named declarations and files inspected

- `VanishingDebtAtomChronologicalConsumer`,
  `QuittingVanishingDebtAtomAccess`,
  `QuittingPositiveMinimumDebtTangentFamily.nonempty_vanishingDebtAtomAccess`,
  and `exists_vanishingDebtAtomAccess_of_supportEntry`
  (`UniformExistenceBoundary.lean`).
- `HasQuittingStoppingLawVanishingDebtAtomAlternative` and
  `hasDebtSlopeAtomAlternative_of_hasVanishingDebtAtomAlternative`
  (`VanishingDebtAtomAlternative.lean`).
- `QuittingChronologicalDebtData`,
  `QuittingChronologicalDebtShadowingCertificate`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
  (`ChronologicalDebtShadowing.lean`).
- `QuittingChronologicalDebtData.exactOfRoots` and its exact zero-defect
  bookkeeping declarations (`ExactChronologicalData.lean`).
- `QuittingStoppingLawAtomExactPrefixStackAccess`,
  `nonempty_atomExactPrefixStackAccess_of_fixedAlternative`,
  `opponentSurvival_tendsto_one`,
  `jointSurvival_tendsto_one_of_twoActive`, and
  `singletonActive_or_jointSurvival_tendsto_one`
  (`ExactPrefixStackAccess.lean`).
- `continuePrefix_atomAlternative_eventually`
  (`ContinuePrefixAccess.lean`).
- `absorptionSum_tendsto_zero_of_twoActive`
  (`ExactPrefixStackCharge.lean`).
- `IsQuittingLiteralExactRootStack`,
  `exists_quittingLiteralExactRootStack`, and
  `quittingTerminalDeviationDebt_literalRootStack_eq_blockAct`
  (`LiteralExactPrefixStack.lean`).
- `QuittingStoppingLawCommonResponseWitness`,
  `exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise`, and
  `QuittingStoppingLawCommonResponseWitness.sourcePositiveGain_tendsto_zero`
  (`VanishingDebtAtomAlternative.lean`).
- `QuittingStoppingLawActiveTransferCycle.exists_eventually_uniformSlope`
  (`ActiveTransferCycle.lean`).
- `QuittingStoppingLawActiveTransferCycle.exists_eventually_uniformCubeEdge`,
  `QuittingStoppingLawActiveTransferCycle.exists_eventually_reachedCubeEdge_or_curvature`,
  `QuittingStoppingLawActiveTransferCycle.prefixWord`,
  `QuittingStoppingLawResetCubeData.profile_insert_eq_reset_of_not_mem`, and
  `QuittingPositiveMinimumDebtTangentFamily.sourceMatchedResetCubeData`
  (`ActiveTransferCycle.lean`, `TerminalSemanticStoppingLawResetCube.lean`, and
  `SourceMatchedResetCube.lean`).
- `projectiveTerminalEscapeDebt_tendsto_one` and
  `projectiveTerminalEscapeSource_tendsto_zero`
  (`TwoEndedDynamicDebtCompactification.lean`), found by the narrow follow-up
  search for an existing moving-boundary no-go.
- `capNashStack_absorptionBudget_of_nearMinimum`,
  `one_sub_capNashStackContinueProduct_le_absorptionSum`, and
  `exists_deep_nearMinimum_capNashChronology`
  (`TerminalCapNashChronology.lean`).
- `exists_positive_causalStage_of_positive_pureTimeRectangleAtom`,
  `quittingStoppingLawRectangleStageAtom_eq_causalFactor`, and
  `positive_actualTerminalMass_of_positive_stoppingLawRectangleStageAtom`
  (`TerminalSemanticPureTimeRectangleDisintegration.lean`).
- `sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero` and
  `exists_resetFace_minimizer_with_unique_allContinue_capNash`
  (`TerminalSemanticResetExcursionReturn.lean`).
- `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`
  (`TerminalSemanticOwnStrategyTransport.lean`) and
  `exists_totalNashDefect_moat_of_unique_allContinue`
  (`TerminalSemanticPlateauNashMoat.lean`).
- `QuittingStoppingLawVanishingDebtRectangleSequence.nonempty_resetFaceDispatch`
  and `QuittingStoppingLawRectangleResetFaceDispatch.opponent_transfer`
  (`EndpointReturn.lean`).

The bounded phrase search before proposing a lemma covered only these atom,
exact-prefix, and chronological subtrees.  No declaration there supplies a
coherent infinite limit of the rank-indexed words.

## 3. First interface separation

The static vanishing-debt alternative is a disjunction.

- In its prescribed-atom arm it stores a positive terminal-law atom but no
  small endpoint debt at all.
- In its rectangle arm it stores one observer pure time, one terminal-law atom,
  and a bound only on the observer's semantic debt after the mover and observer
  updates.

Consequently the word “vanishing-debt” does not mean that the whole debt vector
vanishes.  It means that one coordinate vanishes in only one disjunct.  The
producer must either eliminate the prescribed arm, rotate the controlled
coordinate through all players, or use the atom to derive a vector-valued
forcing improvement.  None of those conclusions is a field of
`QuittingVanishingDebtAtomAccess`.

The exact-prefix stack adapter solves a different problem: the literal atom
suffix can sit after exact state-matched Nash roots of arbitrary prescribed
finite depth.  The words `roots rank` are chosen independently by finite Nash
existence.  Their only compatibility is their common terminal source at the
same rank; `roots (rank + 1)` is not required to extend `roots rank`, and their
terminal profiles also change with rank.  Compactness could produce convergence
of each fixed root coordinate along nested subsequences, but by itself it would
not retain the atom, which moves to time `rank + 1` and may escape to infinity.

There is also a direct sign mismatch with the survival clauses of the consumer.
With two active debtors, the exact access stacks have joint survival through
their entire increasingly long word tending to one, while a chronological
certificate needs joint survival from every fixed start to tend to zero.
Indeed `absorptionSum_tendsto_zero_of_twoActive` shows that the total literal
one-row absorption charge of those words tends to zero.  Hence the access words
cannot simply be nested or diagonalized into the desired absorbing chronology;
separate killing blocks must be inserted.  Those blocks create precisely the
new prescribed and direct-debt seam forcing that the certificate controls.

The repository already contains the exact scalar regression for a tempting
projective repair.  `projectiveTerminalEscapeDebt` is zero at each moving
finite terminal boundary, yet at every fixed earlier time it converges to the
positive harmonic value one while its only source atom escapes to infinity.
Thus a diagonal compact limit of zero-boundary finite words cannot by itself
preserve small initial debt.  One needs either survival contraction or a
two-ended bridge retaining the moving terminal packet.

## 4. Recovering the common-response carrier erased by the atom disjunction

The actual atom decoder is stronger than
`HasQuittingStoppingLawVanishingDebtAtomAlternative`.  Let an active mover `m`
and observer `o` satisfy

`tau = frontier.tangent m o > 0`.

Set `c = tau / 2`.  By `frontier.tangent_tendsto` and
`normalizedDebtDirection_le_fullReplacementDebtChange`, for all sufficiently
large ranks,

`c <= debt(fullReplacement(m,n),o) - debt(source(n),o)`.

For any chosen positive error sequence `e_n -> 0`, the checked theorem
`exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise` therefore
gives, eventually, a pure time `q_n` such that, with

`E_n = update(source_n,m,replacement(m,n))`

and

`Z_n = update(E_n,o,pureTime(q_n))`,

the following exact inequalities hold:

1. `debt(Z_n,o) <= e_n`;
2. `debt(source_n,o) + c - e_n <= payoff_o(Z_n)-payoff_o(E_n)`;
3. `c - e_n <= [payoff_o(Z_n)-payoff_o(E_n)]
   - [payoff_o(update(source_n,o,pureTime(q_n)))-payoff_o(source_n)]`;
4. the positive part of the last source-response gain is at most
   `debt(source_n,o)`.

This conclusion precedes the proof's `by_cases hprescribed`.  The later theorem
`hasVanishingDebtAtomAlternative_of_endpointDebtRise` keeps the small endpoint
debt only in its rectangle arm, but its proof constructs the same common
response witness before selecting either atom arm.  Therefore a strengthened
actual-source adapter can retain vanishing endpoint debt in *both* arms without
new mathematics.  The public `QuittingVanishingDebtAtomAccess` structure does
not retain it, but the chronological consumer receives the whole frontier and
may reconstruct the stronger carrier rather than use its supplied `access`.

There is a simultaneous finite-cycle form.  Suppose there is no support entry
and let `v_0,...,v_(p-1)` be an active transfer cycle.  Since `p` is finite and
each `tau_t = tangent(v_t,v_(t+1))` is positive, choose

`c = (min_(t<p) tau_t) / 2 > 0`.

After one common rank threshold, the preceding construction gives for every
`t<p` a common response at the full reset by `v_t`, with observer `v_(t+1)`,
endpoint debt at most the same `e_n`, and gain margin at least `c-e_n`.  This
follows either by a finite intersection of the individual eventual
inequalities or directly from
`QuittingStoppingLawActiveTransferCycle.exists_eventually_uniformSlope`.
It is a genuine vector-coverage improvement over one fixed observer: every
vertex of the chosen cycle is made low-debt at one corresponding endpoint.

It is not yet chronological.  All `p` endpoint profiles are constructed from
the same `source_n`, and the response endpoint for `v_t -> v_(t+1)` is not the
source profile for the edge `v_(t+1) -> v_(t+2)`.  Nor need the cycle cover
every active player.  Consequently no single executable root schedule, seam
forcing bound, or survival contraction follows from this finite-cycle packet.
The precise new question is whether the common source makes those `p` frozen
profiles close enough, in the generated-secant metric rather than merely in
terminal semantic debt, to splice them with a summable seam budget.

## 5. Exact stack perturbation bound and a non-small actual seam

The block seam can be quantified without choosing generated secants.  Let
`roots=[r_0,...,r_(L-1)]` be a literal exact-root stack built over a terminal
profile with terminal prescribed payoff `a`.  Roll the terminal candidate pair
`(a,a)` backward through `quittingTerminalSemanticPrefix` along the word.  By
exact endpoint Nash at every suffix, every resulting candidate debt is zero,
and the prescribed coordinates are the literal payoffs of the corresponding
stack suffixes.

Now replace the terminal candidate pair by

`(b,b+d)`, with `d_i>=0`,

and roll it backward through the *same* roots.  Write

`Q = product_t stationaryContinueMass(r_t)`

and

`S_i = product_t opponentContinueMass(r_t,i)`.

Then the modified head debt `D_i` satisfies the exact perturbation bound

`0 <= D_i <= S_i |b_i+d_i-a_i| + Q |b_i-a_i|`.          (5.1)

Proof: the prescribed prefix is affine in its successor prescribed value,
with slope the joint Continue mass.  Hence its head difference is exactly
`Q(b_i-a_i)`.  The best-response prefix is a maximum of a tail-independent
Quit value and an affine Continue branch whose tail slope is the deleted-player
Continue mass.  Since `x -> max(k,x)` is one-Lipschitz, iterating gives cap
difference at most `S_i|b_i+d_i-a_i|`.  The reference head debt is zero, so
subtracting cap and prescribed coordinates and applying the triangle
inequality proves the upper bound; nonnegativity is part of the terminal
semantic prefix construction.

In particular, if both terminal coordinates are within `rho` of the intended
terminal pair, then `D_i<=2rho`.  Conversely, terminal semantic-debt closeness
without prescribed-payoff closeness is insufficient.  A block with small `Q`
and every small `S_i` can attenuate a large seam, but the two-active atom-access
stacks have `Q->1` and active-player `S_i->1`, so they provide no attenuation.

The actual common-response carrier has a quantitatively non-small seam.  In
the notation of section 4,

`payoff_o(Z_n)-payoff_o(E_n) >= debt(source_n,o)+c-e_n >= c-e_n`.

For all sufficiently large `n` with `e_n<=c/2`,

`|payoff_o(Z_n)-payoff_o(E_n)| >= c/2`.                 (5.2)

Thus the useful low-debt response endpoint `Z_n` is necessarily a
nonperturbative prescribed-payoff jump away from the full-reset endpoint
`E_n`.  Prepending the existing two-active access stacks cannot hide this
jump: their joint survival tends to one, so the prescribed part of (5.1)
retains it.  This is the same structural tension seen from both sides: the
actual atom remains visible precisely because the prefix does not contract,
whereas a chronological certificate needs contraction to discard terminal
errors.

There are now only two viable gluing modes.

1. Insert a separate block with both joint and all player-deleted survival
   uniformly below one before every non-small carrier jump.  Its root choices
   must still keep the rolled-back candidate debts and seam forcing summable.
2. Pair positive and negative prescribed seams so that
   `prescribed_discrepancy` cancels on *every interval*, while separately
   controlling the one-sided survival-weighted direct-debt forcing.  Ordinary
   zero-sum cancellation is insufficient because the certificate quantifies
   over every start and length.

Equation (5.1) makes the next missing datum exact: one needs a contracting
state-matched bridge, not merely another atom or another long exact prefix.

## 6. A contracting bridge must pay a scale-free debt cost

The most natural separate bridge is an exact cap--Nash stack, because its debt
recursion is state matched.  The checked absorption budget rules it out near
the positive minimum at arbitrarily small cost.

Let `delta>0` be the global infimum of total terminal debt.  Let an exact
cap--Nash stack have terminal total debt at most `delta+epsilon`, joint Continue
product `Q`, and unweighted absorption sum `A`.  The named checked theorems give

`delta A <= epsilon`

and

`1-Q <= A`.

Therefore

`delta(1-Q) <= epsilon`.                              (6.1)

If one demands a uniform contraction `Q<=rho<1`, then necessarily

`epsilon >= delta(1-rho)>0`.                          (6.2)

Hence exact cap--Nash blocks based arbitrarily close to the positive-minimum
stratum cannot supply the fixed contraction needed to attenuate (5.2).  Their
joint survival tends to one, consistently with
`exists_deep_nearMinimum_capNashChronology`.  The literal exact-prefix access
has the same conclusion in the two-active branch by a different debt-block
argument.

This does not make a contracting bridge impossible.  It says precisely that
such a bridge must either leave the near-minimum stratum by a scale-free total
debt amount or cease to be exact cap--Nash.  In the first case the producer
must later return and account for that debt excursion; in the second it must
charge the resulting direct-debt defect to the one-sided weighted forcing
budget.  Neither accounting datum is present in static atom access.

## 7. Exact period-two transfer test: an insertion path, not a return

The smallest active-transfer cycle has two distinct active players, call them
`A` and `B`, with positive tangent edges `A -> B` and `B -> A`.  Fix one large
rank, write `lambda=frontier.scale rank`, and let `c>0` be the common normalized
charge from `exists_eventually_uniformCubeEdge`.  On the source-matched reset
cube, for a face `F` write

`D_i(F) = debt_i(data.profile F)`.

The actual-data adapter gives the two frozen source inequalities

`D_B({A}) - D_B(empty) >= lambda*c`,                    (7.1)

`D_A({B}) - D_A(empty) >= lambda*c`.                    (7.2)

These are simultaneous, exact statements about four static behavioral
profiles.  The reached-edge/curvature theorem transports the second edge past
the first insertion and says exactly that either

`D_A({A,B}) - D_A({A}) >= lambda*c/2`,                  (7.3)

or the square

`[D_A({A,B})-D_A({A})] - [D_A({B})-D_A(empty)]`

has absolute value greater than `lambda*c/4`.  Thus in the small-curvature
case the insertion path

`empty -> {A} -> {A,B}`

really does carry first a positive transfer to `B` and then a positive
transfer to `A`.  This is the strongest literal two-step conclusion available
from the named cube declarations.

It is not a recurrence.  By
`CubicalResetIntegrability.finalSet_eq_union_toFinset`, executing the prefix
word only unions its coordinates into the current face.  After `A` and `B`
have appeared, further occurrences are idempotent.  In particular the cycle
word `A,B,A,B,...` reaches `{A,B}` after two steps and then stays there.  The
theorem is deliberately quantified only over `time < cycle.period`; it does
not produce new reached edges after saturation.

There is of course an algebraically closed square,

```
empty -> {A} -> {A,B} -> {B} -> empty,
```

and every scalar observable telescopes to zero around it.  But the last two
arrows remove resets.  They are the negatives of forward cube edges at other
faces, not further applications of the positive-transfer theorem.  No named
actual-data declaration identifies either reverse arrow with a selected best
response, a frontier replacement at a new source, or a Bellman successor.
Consequently the closed square cannot be used as an exact debt-excursion
return.

This also separates two meanings of state matching which had been easy to
conflate:

1. **Static reset matching holds.**  By
   `profile_insert_eq_reset_of_not_mem`, the profile at `{A,B}` is obtained by
   resetting `B` from the already reached static face `{A}`.  The target law
   and scale remain frozen from the common source.
2. **Chronological Bellman matching is absent.**  A cube face is an entire
   behavioral profile.  Executing its time-zero root leaves its own shifted
   tail, not the next cube face.  If one instead executes the root from one
   face and declares a different face to be its continuation, the resulting
   profile is no longer the profile on which (7.1)--(7.3) were proved.  No
   equality of the form `face(F) = rootThenContinuation(root,face(F'))` is
   supplied.

Nor does the cube identify the two required clocks.  Joint survival of a
candidate root sequence uses the product of all-player Continue masses;
player `i`'s deviation recursion uses the product with `i` deleted.  Static
terminal debts at the four faces determine neither product for a spliced
sequence.  A face can be evaluated as a behavioral tail, but then its actual
successor is its own shift and the insertion path disappears.

The quantitative scale makes the obstruction more severe.  Each guaranteed
transfer in (7.1)--(7.3) is only `O(lambda)`, with `lambda -> 0`.  Obtaining a
scale-free excursion from one rank would require on the order of `1/lambda`
positive packets.  The finite cube supplies at most one fresh insertion per
player and then saturates.  Moving to another rank restarts at a different
source profile, with no controlled seam from the full face at the previous
rank.  Moreover tangent convergence gives no lower bound on a cumulative sum
of selected scales; a subsequence of the positive scales can always be chosen
summable.  Therefore normalized positive charge alone cannot fund the
scale-free excursion which (6.2) shows a fixed cap--Nash contraction would
cost.

The exact period-two audit therefore rules out a tempting mechanism, not the
frontier conjecture: active-transfer cyclicity plus source-matched cube
geometry does not imply a chronological return.  A usable producer needs one
additional actual datum, such as a forward face-to-source return with a
Bellman-root identity, a scale-clock inequality forcing enough cumulative
charge before survival dies, or a direct one-sided forcing estimate for the
uncontrolled source seam.

## 8. Branch-independent scale-free reset excursion, and its exact trap

The common-response recovery of section 4 yields more than the vanishing
`O(lambda)` cube edges.  Fix one active transfer edge `m -> o`, so

`d = debt_o(frontier.base) > 0`.

Choose positive errors `e_n -> 0` and, after discarding a finite prefix, let
`Z_n` be the full `m`-replacement followed by the common pure-time response of
`o`.  The checked witness gives

`debt_o(Z_n) <= e_n`.                                  (8.1)

All semantic pairs of the `Z_n` lie in the compact terminal semantic carrier.
Pass to a convergent subsequence with limit `Z`.  Continuity of semantic debt
and (8.1) give

`debt_o(Z)=0`.                                         (8.2)

Now apply
`exists_resetFace_minimizer_with_unique_allContinue_capNash` with source
`frontier.base`, target `Z`, and reset owner `o`.  It returns an attainable
semantic pair `R` satisfying

`debt_o(R)=0`,

`DebtSum(base) <= DebtSum(R) <= DebtSum(Z)`,

and the exact transfer identity

`sum_(j != o) [debt_j(R)-debt_j(base)]`

`= [DebtSum(R)-DebtSum(base)] + debt_o(base)`.           (8.3)

In particular,

`d <= sum_(j != o) [debt_j(R)-debt_j(base)]`.           (8.4)

This is a scale-free actual-source debt excursion.  Unlike the cube transfer,
its lower bound is the fixed positive base debt `d`, not `lambda*c`.  Since
there is at least one other player, (8.4) also selects some `j != o` with

`debt_j(R) > debt_j(base)`.                             (8.5)

The recipient `j` need not belong to the original active support, and neither
the compact endpoint `Z` nor the minimized point `R` is asserted to retain the
terminal atom or response law.  But (8.3) is a rigorous nonlocal transfer from
the actual common-response endpoint geometry, including ranks where the later
atom decoder chooses its prescribed arm.  The existing rectangle-only
`nonempty_resetFaceDispatch` is a checked overlapping instance; the argument
above observes that the common response available before the disjunction
extends the semantic reset-face conclusion to both arms.

The same minimizer theorem identifies the obstruction to using `R` as a
return.  It proves

- the all-Continue root is exact cap--Nash against `R.2`;
- prefixing `R` by that root fixes `R`; and
- every exact cap--Nash root against `R.2` is all-Continue.

Thus the scale-free excursion ends at a nonabsorbing cap face.  Any forward
root that contracts joint survival must be non-cap--Nash and must be charged
through `prescribedDefect` or `directDebtDefect`.  Exact cap--Nash existence
cannot provide the clock.

### 8.1 What causal stage disintegration does and does not add

In the rectangle arm,
`exists_positive_causalStage_of_positive_pureTimeRectangleAtom` localizes a
positive signed terminal rectangle at a finite time `t`.  Its exact
factorization is

`opponent first-stop factor * mover law difference * reward`.  (8.6)

Positivity also implies that the same nonempty terminal coalition has positive
stage mass in at least one of the two literal endpoint profiles.  Therefore,
at that endpoint's root at time `t`, joint Continue mass is strictly below
one.  For a deleted player `i`, the opponent Continue mass is strictly below
one only when the selected coalition contains a quitter other than `i`.
Consequently a coalition of size at least two contracts every deleted-player
clock, while a singleton `{i}` does not contract player `i`'s deleted clock.
The theorem imposes no coalition-size or rotating-singleton condition.

There are three further losses which prevent (8.6) from being the required
chronological packet.

1. It returns only strict positivity of one stage atom, with no lower bound in
   terms of the original charge.  A finite pure response may split the atom
   among arbitrarily many earlier dates; a `Never` response uses an infinite
   summable series.  The selected stage masses may therefore tend to zero too
   rapidly to make any survival product vanish.
2. The actual positive stage mass may belong to the target endpoint or the
   source endpoint.  The theorem does not select one orientation as the next
   candidate tail.
3. Conditional on all players Continuing through the selected date, the
   successor is the shifted tail of that endpoint profile.  It is not the next
   frontier source or the reset-face minimizer `R`.  Absorption at the positive
   row ends play; survival does not close a face-to-source seam.

The branch-independent endpoint-gain atom from
`QuittingStoppingLawCommonResponseWitness.exists_endpointGainAtom` is even
less directly covered: it compares the observer's own pure response with its
old strategy, whereas the rectangle disintegration assumes a distinct mover
whose source and target laws change while the payoff observer is fixed.

### 8.2 The remaining one-sided forcing datum

At `R`, let a proposed absorbing root be `q` and keep `R` as the candidate
successor pair.  Write `P(q)=prefix(q,R)`.  The one-step candidate defects are
exactly

`f_i(q)=R.1_i-P(q).1_i`,

`g_i(q)=debt_i(R)-debt_i(P(q))`.                        (8.7)

Let `rho_i(q)` be `q`'s coordinate Nash defect in the one-stage game with
continuation vector `R.2`, and let `C(q)` be its joint Continue mass.  The
checked arbitrary-root cap decomposition gives the exact identity

`debt_i(P(q)) = rho_i(q) + C(q)*debt_i(R)`,

so

`g_i(q) = (1-C(q))*debt_i(R) - rho_i(q)`.                (8.8)

This is the exact one-sided forcing account.  Positive tail debt provides an
absorption credit; cap defect spends it.  At the reset coordinate it reduces
to

`g_o(q) = -rho_o(q)`,                                  (8.9)

because `debt_o(R)=0`.  Thus every cap defect of the reset player is purely
adverse forcing, with no debt stock available to pay it.

Exact cap--Nash roots have every `rho_i=0`, but the reset-face minimizer says
the only such root is all-Continue, with `C=1`.  Roots can nevertheless
approach all-Continue with both absorption and defect tending to zero at an
unknown relative rate.  The fixed-cap moat theorem gives a positive total
defect only after imposing a fixed positive incidence floor.  It supplies no
linear modulus as that floor tends to zero, no allocation of total defect to
the reset coordinate, and no prescribed-drift cancellation.  Consequently
uniqueness alone neither constructs nor excludes a diffuse sequence with
divergent absorption and summable weighted `rho_o`.

### 8.3 Exact two-player rare-root test

The smallest all-clock test makes the missing first-order data explicit.  Let
the players be the reset owner `o` and one recipient `j`.  Write

`u=R.1`, `v=R.2`, `d=v-u`, with `d_o=0`.

At one stage let both players Quit independently with probability `p`.  Then
both player-deleted Continue masses equal `1-p`, so choosing `p_t -> 0` with
`sum_t p_t=infinity` kills joint survival and both deleted-player survivals.
The prescribed defect is exactly

`f_i(p) = p*(2*u_i-r({o})_i-r({j})_i)`

`         + p^2*(-u_i+r({o})_i+r({j})_i-r({o,j})_i)`.  (8.10)

The certificate bounds *unweighted* sums of `f_i` on every interval.  Hence a
same-sign nonzero linear coefficient in (8.10) is fatal when `sum p_t`
diverges.  The quadratic remainder, by contrast, can be made uniformly
summable by taking for example `p_t` proportional to `1/(t+T)` with `T` large.
Thus this literal two-player schedule needs the first-order singleton balance

`2*u_i = r({o})_i+r({j})_i` for every `i`,               (8.11)

or a separate signed circulation cancelling those linear drifts on every
interval.

The reset owner's cap defect is equally explicit.  Against the opponent's
quit rate `p`, its pure endpoints are

`Q_o(p)=(1-p)*s_o+p*r({o,j})_o`,

`K_o(p)=(1-p)*u_o+p*r({j})_o`,

because `v_o=u_o`.  The mixed root uses Quit probability `p`, so

`rho_o(p)=max(Q_o(p),K_o(p))`

`           - [p*Q_o(p)+(1-p)*K_o(p)]`.                (8.12)

If `s_o<u_o`, then for all small `p` the Continue endpoint is better and

`rho_o(p)=p*(u_o-s_o)+O(p^2)`.                         (8.13)

By (8.9), this is adverse direct forcing.  If it is estimated using the
deleted-player survival envelope, its weighted sum has a scale-free positive
cost when `sum p_t=infinity`; delaying or uniformly shrinking a divergent
rare clock does not make that coarse hazard account arbitrarily small.  The
certificate actually weights by the *generated secant*, which is only bounded
above by deleted-player Continue mass.  It may be smaller, so (8.13) is an
adapter obstruction to the available estimate, not a no-go theorem for every
generated-secant selection.  If instead `s_o=u_o`, the first-order endpoint
tie leaves two orientations:

- when `r({o,j})_o<=r({j})_o`, Continue remains weakly better and
  `rho_o(p)=O(p^2)`;
- when `r({o,j})_o>r({j})_o`, Quit becomes better and
  `rho_o(p)=p*(r({o,j})_o-r({j})_o)+O(p^2)`.

Only the first orientation has a summable reset-owner forcing cost under the
standard divergent rare clock.

The actual reset-face minimizer supplies merely

`s_o <= v_o=u_o`.

It supplies neither equality, the collision orientation, nor the vector
balance (8.11).  With two players one cannot avoid giving both players
divergent own hazard, because each is the other's only source of deleted-player
absorption.  With at least three players one may keep the reset owner passive
and use two other quitters to contract all deleted clocks, but the source data
does not guarantee two suitable positive-debt recipients or their analogous
first-order payoff balances.

Equations (8.8)--(8.13) are the concrete non-cap--Nash bridge deficit.  The
scale-free reset excursion is real, but chronological compilation additionally
needs a balanced rare-root direction tangent to the prescribed-payoff level
set and second-order cap defect on every zero-debt coordinate.  Neither datum
is a consequence of vanishing-debt atom access.  Also, `R` itself cannot be
used as the certificate's time-zero candidate when `eta` is small: its total
debt is at least the fixed positive minimum.  Candidate chronological debts
need not be semantic-carrier debts, but a further artificial-candidate bridge
would have to move the scale-free transfer into later tails while keeping all
initial candidate coordinates below `eta`.

This is now the exact adapter deficit.  The source does supply a scale-free
debt transfer, but its canonical endpoint is a unique all-Continue cap trap.
To turn it into chronological shadowing one needs either a quantitative
non-cap--Nash root selection proving the two certificate budgets directly, or
a coercive residual-to-absorption bound such as (8.8) which would refute that
route and force a different consumer.

## Proved or checked here

- The exact quantifier comparison above is a declaration-level audit.
- The atom alternative controls at most one debt coordinate and only in its
  rectangle arm; this is immediate from its checked definition.
- The present exact-prefix access words are not a coherent projective family;
  no such field appears in the structure or constructor.
- In the two-active branch their joint survival tends to one and their total
  literal absorption charge tends to zero, by the named checked declarations.
- The common-response recovery in section 4 is a direct ordinary-mathematics
  corollary of the named checked endpoint-rise and tangent-convergence
  declarations.  The simultaneous finite-cycle version uses only finiteness
  and the checked uniform-slope theorem.  No chronology is claimed.
- The finite-stack terminal-pair perturbation bound (5.1) and the actual
  response seam lower bound (5.2) are proved in ordinary mathematics in
  section 5.  They are not checked Lean declarations.
- The bridge lower bound (6.2) is an immediate consequence of the named
  checked cap--Nash absorption-budget and union-bound declarations.
- The period-two cube formulas (7.1)--(7.3), monotone face saturation, and the
  distinction between static reset matching and chronological Bellman
  matching are exact consequences of the named checked declarations.  The
  conclusion that these fields do not by themselves produce a return is an
  interface nonimplication, not a theorem that no return can be constructed
  from richer actual source geometry.
- The scale-free transfer (8.3)--(8.5) is an ordinary-mathematics application
  of compactness, common-response endpoint debt convergence, and the named
  checked reset-face minimizer theorem.  It is not a new Lean declaration.
  The all-Continue cap trap at `R` is part of that checked theorem.
- The causal-stage probability audit uses the named exact factorization and
  actual-stage-mass theorem.  No divergent survival clock is claimed.
- The direct-forcing identity (8.8) is the named checked arbitrary-root cap
  decomposition rearranged.  The symmetric-root formulas (8.10)--(8.13) are
  exact ordinary mathematics; their asymptotic conclusions concern that
  literal root family only.

No new Lean result is claimed here.

## Open claims and objections

- It remains possible that a careful block concatenation uses each static atom
  as a sparse repair while separate exact roots provide the required killing.
- `exactOfRoots` makes all forcing defects zero, but then its initial candidate
  debt is the actual exploitability of the constructed schedule; static atom
  access does not yet make that whole vector small.
- A compact diagonal limit of finite stacks needs a proof that exact root Nash
  conditions survive and a separate mechanism preventing all useful atom data
  from escaping to infinity.  Even if both hold, survival still has the wrong
  direction in the two-active access words.
- The support-entry adapter gives an observer with zero debt at the limiting
  base.  It is stronger than universal access but still controls only one
  recipient; whether finite support iteration can serialize all coordinates is
  open.
- The recovered cycle endpoints control one coordinate each, but state
  matching between successive endpoints is wholly open.  Debt closeness alone
  is not yet a bound on the prescribed and generated-secant seam terms.
- The common-response endpoint cannot be reached by a vanishing prescribed
  perturbation: its observer payoff jump is eventually at least `c/2`.  A new
  bridge must contract or cancel this jump.
- Any exact cap--Nash bridge with fixed joint contraction must leave the
  positive minimum by at least the scale-free amount in (6.2).  How to return
  from and chronologically account for that excursion is open.
- The active-transfer cycle is not itself a recurrence: its `prefixWord`
  saturates the reset face after finitely many insertions.  Reverse reset edges
  and seams between ranks are uncontrolled.
- A branch-independent reset-face minimizer receives a scale-free transfer of
  the erased observer debt, but its unique exact cap--Nash root is
  all-Continue.  The source supplies neither a forward return from that point
  nor a quantitative non-cap--Nash forcing modulus.
- In the smallest two-player diffuse root, the actual source lacks both the
  first-order prescribed balance (8.11) and the reset-coordinate tight/collision
  conditions which turn its adverse cap defect from linear into quadratic.

## Requested check

Test whether the actual reset-face transfer can guarantee two non-reset
recipients and a nonnegative rare-root direction satisfying the vector
first-order prescribed balance and zero first-order cap defect on all
zero-debt coordinates.  Absent that datum, this route is exhausted at the
exact interface level and should hand off to a distinct frontier obligation.
