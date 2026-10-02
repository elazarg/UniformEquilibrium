# Prioritized positive-absorption attachments reduce to the singleton-defect residual

Authors: `CODEX_RAMSEY`, `CODEX_EULER`

Independent reviews:
[infinite-spine contraction review](../feedback/CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION__BY_CODEX_EULER.md),
[reached-row floor-lift review](../feedback/CODEX_EULER__AGKRS_REACHED_ROW_FLOOR_LIFT_CONSUMER__BY_CODEX_RAMSEY.md)

Whole-packet gate:
[ACCEPT after the incorporated strategy-semantics wording repair](../feedback/AGKRS_PRIORITIZED_ATTACHMENT_TO_SINGLETON_DEFECT__BY_CODEX_MINER.md)

## Exact statement

Let `I` be a finite nonempty player type with decidable equality, let

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I,
delta : ℝ,
0 < delta,
R : QuittingPrioritizedRefinedSourceResidualAt reward delta,
```

and work in the positive-absorption branch of the inclusive disjunction
`R.residual`, witnessed by

```text
attachment :
  QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
    reward (1/2).
```

Then

```text
Nonempty
  (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta).
                                                               (A)
```

Consequently, on the same reward table and at the same `delta`, there is a
`QuittingPrioritizedRefinedSourceResidualAt reward delta` whose corrected
residual is specifically its third, positive-singleton-defect disjunct.  Its
four priority-negation fields are exactly those of `R`.

Equivalently, within the prioritized residual, the local two-level arm rank

```text
positive-absorption attachment : 1
positive-singleton defect      : 0
```

strictly decreases from `1` to `0`.

## Conjecture-facing change

The maintained prioritized source obligation in
[`AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md`](../questions/AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md)
contains a positive-absorption attachment arm.  Before this result, its
checked finite/infinite extension had two live outputs: a finite uniformly
reached sure-exit row, and an infinite exact support--Bellman spine.  The
finite output had no punishment-floor consumer, while only the infinite
output was known to contract.

The new reached-row theorem supplies the missing unrestricted S.2 consumer
for the finite output.  Hence the entire attachment arm, not merely its
infinite subarm, reduces at the same table and scale to (A).  This removes one
named prioritized source arm as an independent obligation.

The rank-zero positive-singleton defect is still open.  In particular this
packet does not prove S.1, S.2, or S.3 for every prioritized source and does
not close AGKRS Theorem 3.4.

## Definitions and assumptions

Write

```text
P_i = quittingPunishmentValue reward i.
```

For a uniformly reached limiting row

```text
row : QuittingLowSurvivalPositiveRhoReachedRowLimit base,
```

put

```text
q       = quittingRootOfSimplex row.root,
T_i     = row.nextValue i,
T^P_i   = max(T_i,P_i).
```

The essential intermediate theorem is

```text
IsQuittingRootNash reward T^P 0 q.                 (B)
```

The predicate (B) quantifies one-stage marginal replacements
`dev : PMF Bool`.  Its derivation uses the source's unrestricted behavioral
Nash inequality: after conditioning on arrival, a deviator combines its
chosen current marginal with an unrestricted suffix reply.  The sure-row
compiler's resulting terminal equilibrium again controls unrestricted
behavioral deviations.  A behavioral strategy is observed through the unique
live history before absorption, and its live hazards may depend on time.  No
stationary best response or attained punishment minimizer is assumed.

The `row.reached` field provides a *uniform* positive lower bound on the joint
probability of reaching the current row along the selected literal sources.
This is stronger than merely saying that each individual reach probability is
positive and is essential to the limiting argument.

## Source correspondence

The following checked declarations supply the actual source data and existing
consumers.

- `QuittingPrioritizedRefinedSourceResidualAt` in
  `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedRefinedSourceBoundary.lean`
  packages the corrected residual and the four same-scale priority
  negations.
- `QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual`,
  `QuittingCorrectedPointwiseRefinedSourceResidualAt`,
  `QuittingSupportBellmanPositiveSingletonDefectResidual`, and
  `QuittingSupportBellmanPositiveSurvivalBoundary.stationary_or_defect` are
  in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveRhoLandingClassificationBoundary.lean`.
- `QuittingLowSurvivalPositiveRhoReachedRowLimit`,
  `QuittingLowSurvivalPositiveRhoInfiniteExactSpine`, and
  `finiteSureExitAttachment_or_exists_infiniteExactSpine` are in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/PositiveRhoLandingCompactLimit.lean`.
- `IsQuittingConditionalReservation`, `quittingLiftedContinuation`, and
  `isεQuittingRootNash_quittingLiftedContinuation` are in
  `UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`.
- `quittingPunishmentValue`, `quittingPunishmentValue_le`, and the
  unrestricted `quittingBestReplyValue` are in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
- `exists_oneStagePunishedProfile_of_rational_support_sureQuitter` is in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactQuantitativeAlternatives.lean`.
- `quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary`
  is in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/CompactSpineSurvivalBoundary.lean`.

The checked declarations provide the finite/infinite attachment dispatch,
the continuation-lift inequality, the sure-row compiler, and the semantic
split of an infinite exact spine.  They do not contain theorem (B), its
finite-arm consumer, or their composition with the reviewed infinite-spine
argument into the attachment-wide reduction (A).

`PositiveJointSummablePortPhantomReduction.lean` reaches the same raw
positive-singleton-defect type from a different, summable-port source.  It
does not subsume this theorem: it supplies neither the attachment's reached
rows nor its prioritized provenance.  Conversely, this packet does not
identify the two separately produced defect witnesses or consume their
common codomain.

No external paper theorem is invoked.  The result is a source-native
composition of maintained project interfaces plus the new reached-row limit
argument below.

## Proof

### 1. Punishment values are conditional reservations

Fix a literal root word `roots`, a player `i`, a suffix starting at `s`, and
`zeta>0`.  Let `profile_s` be the behavioral profile generated by that suffix.
By `quittingPunishmentValue_le`,

```text
P_i <= quittingBestReplyValue reward profile_s i.
```

The right side is the supremum over all unrestricted behavioral replies to
the fixed opponents in `profile_s`.  Its payoff range is bounded and the
reply class is nonempty.  Supremum approximation therefore gives a reply of
value at least `P_i-zeta`.  Along the unique live history, that reply is its
time-dependent live-hazard sequence.  The checked live-root and terminal-
payoff identities turn the reply payoff into precisely the tail-hazard value
required by

```text
IsQuittingConditionalReservation reward roots P.
                                                               (1)
```

This does not require the punishment infimum or the reply supremum to be
attained.

### 2. A uniformly reached row is exact against its punishment-floor lift

For the `n`th source selected by the row's nested subsequence, set

```text
index_n = base.index (row.subsequence n),
source_n = landing.family.source index_n,
t_n = source_n.crossingStage + row.offset,
s_n = quittingJointSurvivalWeight source_n.roots 0 t_n.
```

The field `row.reached` supplies one `r>0` such that `r<s_n` for every `n`.
Apply `isεQuittingRootNash_quittingLiftedContinuation` to the unrestricted
source Nash inequality at stage `t_n` and to (1).  It gives

```text
IsQuittingRootNash reward L_n (source_n.accuracy/s_n)
  (source_n.roots t_n),                              (2)
```

where

```text
L_n(i) = max(
  quittingRootSequenceTailVector reward source_n.roots (t_n+1) i,
  P_i).
```

The conditioning denominator is only the joint probability of reaching the
current row.  A unilateral deviator, after arrival, chooses its current
action and then an unrestricted suffix reply.  In particular, (2) has no
additional factor for the prescribed probability that this same player
Continues at the current row.

The selected source indices tend to infinity, so `source_n.accuracy -> 0`.
Because `s_n>=r`, the error in (2) tends to zero.  Along the same subsequence,

```text
source_n.roots t_n -> q,
quittingRootSequenceTailVector reward source_n.roots (t_n+1) -> T.
```

Coordinatewise maximum with the fixed vector `P` is continuous, hence
`L_n -> T^P`.  The finite product-root payoff expressions are continuous in
the root and continuation.  Passing the endpoint inequalities in (2) to the
limit gives exact root Nash against `T^P`, proving (B).

### 3. The finite attachment alternative is impossible under priority

Apply

```text
attachment.consecutive.finiteSureExitAttachment_or_exists_infiniteExactSpine.
                                                               (3)
```

Suppose (3) returns a finite sure-exit attachment.  Its terminal is still a
uniformly reached limiting row, and its decoded root has at least one sure
quitter.  By (B), that root is exact Nash against the punishment-floor lift
of its displayed next value.  This lifted continuation is punishment rational
at error zero by definition.

Exact root Nash implies exact support-local Nash.  Choose one sure quitter
and apply
`exists_oneStagePunishedProfile_of_rational_support_sureQuitter` with support
error zero and compiler tolerance `delta`.  Because `delta>0`, the compiler
returns

```text
QuittingInstantPunishmentεEquilibriumAt reward delta.
```

Its terminal Nash assertion is against every behavioral deviation, not just
stationary or pure-time deviations.  This contradicts `R.not_instant`.
Therefore the finite branch of (3) cannot occur.

### 4. The infinite attachment alternative contracts

The remaining branch of (3) supplies

```text
spine : QuittingLowSurvivalPositiveRhoInfiniteExactSpine
  attachment.consecutive.reachedRow.
```

For each `n`, distinguish the simplex state

```text
s_n = (spine.row n).root
```

from its decoded behavioral product root

```text
q_n = quittingRootOfSimplex s_n.
```

Writing `V_n=(spine.row n).currentValue`, the checked edge has chronological
Bellman orientation

```text
V_n = quittingRootSuccessorPayoff reward V_(n+1) q_n,
```

and `q_n` is exact endpoint Nash against `V_(n+1)`.  The carrier fields bound
every `V_n` by `quittingRewardBound reward`.  Thus the checked bounded
support--Bellman split gives either

1. `QuittingWellSupportedAbsorbingSequenceAt reward delta`, contradicting
   `R.not_wellSupported`; or
2. a `QuittingSupportBellmanPositiveSurvivalBoundary reward delta`.

Applying `QuittingSupportBellmanPositiveSurvivalBoundary.stationary_or_defect`
to the second output gives either stationary equilibrium existence,
contradicting `R.not_stationary` at the positive scale `delta`, or exactly
(A).  Therefore (A) holds.

Finally insert (A) into the third disjunct of
`QuittingCorrectedPointwiseRefinedSourceResidualAt` and copy
`R.not_stationary`, `R.not_instant`, `R.not_wellSupported`, and
`R.not_generated`.  This constructs the claimed prioritized residual on the
same table and at the same scale.

## Probability and behavioral-deviation audit

- Source profiles and their suffixes are literal infinite behavioral
  profiles.  The proof conditions their Nash inequalities on positive joint
  survival to a deterministic row.
- The punishment-floor reservation uses the supremum over the full
  unrestricted behavioral reply class.  Time-dependent hazards and Never are
  included; no finite-time or stationary extremality reduction is used.
- Root randomization is independent product randomization only at a fixed
  current row, exactly as encoded by `quittingRootOfSimplex`.  Later hazards
  remain arbitrary behavioral strategies.
- The infinite spine is a projective sequence of nested subsequential limits,
  not one realized chronology.  Only the checked support--Bellman semantic
  split is applied to it.
- The sure-row compiler, rather than an informal endpoint argument, supplies
  the unrestricted terminal S.2 witness in the finite branch.

## Boundary tests

1. **Zero reach.**  If survival to the current row is zero, conditioning the
   source Nash inequality gives no information.  The floor-lift theorem is
   not claimed.
2. **Nonuniform positive reach.**  If every reach probability is positive but
   tends to zero as fast as the source accuracy, the quotient
   `accuracy/reach` need not vanish.  The uniform field `row.reachFloor>0`
   cannot be dropped.
3. **Raw-tail clipping is false.**  Let player `0` quit surely, player `1`
   quit with probability `1/2`, and set

   ```text
   r_0({0})=r_0({0,1})=0,
   r_0({1})=2,
   T_0=-2,
   P_0=0.
   ```

   Player `0` is tied between Quit and Continue against `T`, while replacing
   `T_0` by `P_0` raises Continue to `1`.  Thus raw-tail exact Nash and a
   rational current value do not imply floor-lifted Nash.  The theorem avoids
   this regression through the uniformly reached unrestricted source-Nash
   inequality.
4. **Several sure quitters.**  The proof needs only one sure quitter.  The
   compiler remains applicable when the terminal root has more than one.
5. **One player.**  Nonemptiness is sufficient.  The same finite/infinite
   dispatch and sure-root compiler apply; no two-player incidence argument is
   hidden in the proof.

## Adapter and consumer

The actual-data adapter is literal: unwrap the second disjunct of
`R.residual` to obtain `attachment`, then invoke the checked exhaustive
finite/infinite dispatch on `attachment.consecutive`.  No separately selected
profile, tail, or root is identified with this source.

The finite output is consumed by theorem (B) followed by the checked sure-row
compiler, yielding the S.2 branch forbidden by `R.not_instant`.  The infinite
output is consumed by the checked support--Bellman split and priority fields,
yielding (A).  Hence every output of the attachment dispatch is accounted for.

The downstream output is the already named
`QuittingSupportBellmanPositiveSingletonDefectResidual reward delta`.  This is
a strict maintained arm reduction but not a terminal AGKRS branch.

## Lean handoff

The narrow implementation can use the following theorem shapes.

```text
theorem isQuittingConditionalReservation_punishmentValue
  (roots : Nat -> I -> PMF Bool) :
  IsQuittingConditionalReservation reward roots
    (fun i => quittingPunishmentValue reward i)

theorem QuittingLowSurvivalPositiveRhoReachedRowLimit
    .isQuittingRootNash_punishmentFloorLift
  (row : QuittingLowSurvivalPositiveRhoReachedRowLimit base) :
  IsQuittingRootNash reward
    (fun i => max (row.nextValue i) (quittingPunishmentValue reward i))
    0 (quittingRootOfSimplex row.root)

theorem QuittingPrioritizedRefinedSourceResidualAt
    .positiveAbsorptionAttachment_to_positiveSingletonDefect
  (R : QuittingPrioritizedRefinedSourceResidualAt reward delta)
  (hdelta : 0 < delta)
  (attachment :
    QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
      reward (1/2)) :
  Nonempty
    (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta)
```

For the limit theorem, name the literal suffix profile and use the live-root
identities when proving conditional reservation.  Convert root Nash to
endpoint Nash before applying the existing closed-graph limit theorem.  Keep
the simplex root `s_n` distinct from the decoded PMF root `q_n` in the spine
proof.

Finite tests should cover zero and nonuniform reach, the scalar clipping
regression above, multiple sure quitters, and the singleton player type.

## Scope and nonclaims

- This packet reduces only the prioritized positive-absorption attachment
  arm.  It makes no claim about the all-Continue positive-rho source arm.
- It does not consume the rank-zero
  `QuittingSupportBellmanPositiveSingletonDefectResidual` or the common
  positive-singleton/all-Continue phantom reached by other reductions.
- It does not prove full prioritized-source closure, AGKRS S.1/S.2/S.3 in all
  cases, AGKRS Theorem 3.4, or the finite-quitting uniform-equilibrium
  conjecture.
- It does not turn the nested infinite spine into an executable chronology,
  recurrence, or return, and it does not identify separately selected source
  laws.
- It does not prove that arbitrary coordinatewise punishment-floor clipping
  preserves root Nash.  The conclusion depends essentially on uniformly
  reached unrestricted source-Nash provenance.

## Checked Lean realization

The packet is realized in
`UniformEquilibrium/Quitting/Classification/Existence/`
`PrioritizedAttachmentSingletonDefect.lean`.  Its checked declarations are:

- `isQuittingConditionalReservation_punishmentValue`, which realizes the
  min-max punishment vector as a conditional reservation against every
  literal, possibly nonstationary, root word;
- `QuittingLowSurvivalPositiveRhoReachedRowLimit.`
  `isQuittingRootNash_punishmentFloorLift`, which gives exact one-stage root
  Nash at every uniformly reached limit row after lifting its successor to
  the punishment floor;
- `isQuittingRootSupportApproxNash_zero_of_endpointNash`, the zero-error
  endpoint-to-support complementarity lemma;
- `QuittingLowSurvivalPositiveRhoInfiniteExactSpine.`
  `nonempty_positiveSingletonDefect_of_priorities`, which contracts the
  infinite attachment output under failure of the stationary and
  well-supported priority branches;
- `QuittingPrioritizedRefinedSourceResidualAt.`
  `positiveAbsorptionAttachment_to_positiveSingletonDefect`, which consumes
  both finite and infinite outputs of the supplied attachment at the original
  reward table and tolerance;
- `QuittingPrioritizedRefinedSourceResidualAt.`
  `prioritizedPositiveSingletonDefect_of_attachment`, which reconstructs the
  same-scale prioritized witness with the third residual disjunct selected;
  and
- `QuittingPrioritizedRefinedSourceResidualAt.`
  `sourcePhantom_or_positiveSingletonDefect`, the exact prioritized normal
  form: the source-faithful all-Continue arm or the positive-singleton defect.

Evidence seals:

- `M`: the complete packet passed independent mathematical review after the
  one incorporated strategy-semantics wording repair;
- `L`: all seven declarations above are proved in Lean under the module's
  stated imports;
- `A`: the reduction starts from the literal prioritized residual and its
  positive-absorption attachment on the same reward table and tolerance, and
  copies all four priority negations exactly; and
- `C`: the checked finite sure-exit and infinite support--Bellman consumers
  remove the attachment as an independent source arm.  This is consumer
  coverage for that arm only, not a consumer for either surviving normal-form
  arm.

The result leaves the source-faithful all-Continue residual and the
positive-singleton defect open.  It supplies no S.1, S.2, or S.3 conclusion
for either survivor, no well-founded descent beyond the one local arm step,
no unconditional AGKRS classification, and no new unconditional advance on
the finite-quitting uniform-equilibrium conjecture.
