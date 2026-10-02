# Review of prioritized attachment-spine contraction

Reviewer: `CODEX_EULER`

Note reviewed:
[`notes/CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION.md`](../notes/CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION.md)

Verdict: **PASS as ordinary mathematics after one literal notation repair;
retain internally, not export-ready.**  I checked the uniform-reach
conditional-rationality argument, the exact Bellman orientation, the
support-spine semantic split, reuse of all four priority negations, the finite
sure-exit compiler, and the strengthened unique-sure-owner localization.  I
found no mathematical counterexample.  The theorem genuinely contracts the
infinite extension of the prioritized attachment arm to the already existing
positive-singleton-defect arm at the same scale.  It does not consume that
rank-zero arm or the finite sure-exit alternative, so it is a strict internal
normal-form reduction rather than a terminating consumer accepted by the
current AGKRS question.

## Claim checked

Starting with the positive-absorption sharp-attachment witness inside a
`QuittingPrioritizedRefinedSourceResidualAt reward delta`, iterate the checked
uniformly reached-row extension.  If this produces an infinite nested exact
spine, apply the checked bounded support--Bellman semantic split and priority
negations to obtain a prioritized positive-singleton-defect residual at the
same `delta`.  If iteration terminates, obtain an exact reached sure-exit row
whose current value is punishment rational but whose displayed next value is
not.  Under failure of S.2, the terminal root has a unique sure quitter and
the deficient tail coordinate is exactly that quitter's coordinate.

## 1. Uniformly reached current values are punishment rational

For a reached row with offset `m`, let

`t_n = source.crossingStage + m`

on its nested subsequence.  The row's `reached` field supplies one fixed
`r>0` with joint survival to `t_n` strictly above `r`.  Shifting the source's
unrestricted root-sequence Nash inequality to `t_n` therefore costs at most

`e_n = source.accuracy / survival_n <= source.accuracy/r`.

The indices are a composition of the base's cofinal index and the row's
strictly increasing subsequence, so source accuracy tends to zero and hence
`e_n -> 0`.  Punishment value is bounded above by every continuation best
reply.  The shifted unrestricted Nash inequality therefore gives, for each
player,

`punishment_i - e_n <= TailVector(source.roots,t_n)_i`.

The right side converges to `row.currentValue i`; passage to the limit yields
exact `QuittingSimonRationalPayoffAt reward 0 row.currentValue`.  The argument
uses the actual survival lower bound at the same offset and does not confuse a
Bellman annotation with a stationary payoff.

This is a legitimate extension of
`QuittingLowSurvivalFirstCrossingSourceAt.actualTail_rational` from the first
crossing row to every uniformly reached nested row.

## 2. Infinite-spine contraction

For the spine, set

- `s_n = (spine.row n).root`, the simplex-coded root; and
- `q_n = quittingRootOfSimplex s_n`, the corresponding behavioral root.

The checked theorem `QuittingLowSurvivalPositiveRhoInfiniteExactSpine.edge`
has orientation

`IsQuittingNashBellmanEdge reward ((V_n,s_n),(V_(n+1),s_(n+1)))`.

Unfolding it gives exactly

`V_n = quittingRootSuccessorPayoff reward V_(n+1) q_n`

and exact endpoint Nash for `q_n` against `V_(n+1)`.  Exact endpoint Nash
implies zero-error support-local Nash, which can be weakened to `delta`.
Each `V_n` is bounded by the checked `currentValue_mem` field.

Thus
`quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary`
applies.  Its absorbing branch contradicts `R.not_wellSupported`.  On the
positive-survival branch,
`QuittingSupportBellmanPositiveSurvivalBoundary.stationary_or_defect` either
gives stationary existence (hence a stationary witness at this positive
`delta`, contradicting `R.not_stationary`) or exactly a
`QuittingSupportBellmanPositiveSingletonDefectResidual reward delta`.

The latter inserts into the third disjunct of
`QuittingCorrectedPointwiseRefinedSourceResidualAt`.  The four fields
`R.not_stationary`, `R.not_instant`, `R.not_wellSupported`, and
`R.not_generated` are global propositions at the same table and scale, so
they can indeed be reused verbatim.  This proves the advertised same-scale
arm change.

### Mandatory literal repair

The current Proposition 2 prose defines `q_n` as
`quittingRootOfSimplex (spine.row n).root` and then displays
`IsQuittingNashBellmanEdge reward ((V_n,q_n),...)`.  This is not literally
typed: a `QuittingNashBellmanPoint` stores a `QuittingRootSimplex`, whereas
`q_n` is the decoded root `iota -> PMF Bool`.  Use the two symbols `s_n` and
`q_n` above, put `s_n` in the edge display, and put `q_n` in the Bellman and
endpoint formulas.  No mathematical change is needed.

## 3. Finite sure-exit endpoint

In the finite arm, the terminal object is still a uniformly reached row, so
the preceding rationality lemma applies to `terminal.currentValue`.  Its
`exactEdge` supplies both the displayed Bellman equality and exact endpoint
Nash against `terminal.nextValue`.

Suppose the next value were punishment rational at error zero.  Convert exact
endpoint Nash to exact support-local Nash, choose a sure quitter from
`terminal.sureExit`, and apply
`exists_oneStagePunishedProfile_of_rational_support_sureQuitter` with
`eta=0` and compiler tolerance `delta`.  Its outputs are precisely:

- a punishment-row cap at most `punishmentValue + delta`; and
- an unrestricted one-stage punished terminal `delta`-Nash profile.

This is `QuittingInstantPunishmentεEquilibriumAt reward delta`, contradicting
`R.not_instant`.  Hence the next value is not rational at zero, equivalently
some coordinate is strictly below its punishment value.  This argument uses
the correct tail (`nextValue`), not the rational current value.

For proof-writing clarity, the note should explicitly mention the conversion
from exact endpoint Nash to exact support-local Nash before invoking the
compiler.  This is expository, not a mathematical repair.

## 4. Unique-sure-owner localization

The strengthened Proposition 4 is correct.  For player `i`, only tail
coordinate `i` enters player `i`'s Quit-minus-Continue endpoint difference,
and it enters with coefficient equal to the probability that all opponents
Continue.  Other payoff coordinates never enter player `i`'s scalar endpoint
comparison.

If some opponent of `i` quits surely, that coefficient is zero.  Therefore:

- with two distinct sure quitters, every coordinate has a sure opponent, so
  the entire tail can be coordinatewise raised to its punishment-floor clip
  without changing any exact support inequality;
- the clipped tail is rational and the sure-row compiler would give S.2,
  contradicting priority; hence there is exactly one sure quitter `k`;
- every other player's Continue probability is then strictly positive, and
  finiteness makes their product positive; and
- every coordinate other than `k` is still tail-irrelevant because `k` is a
  sure opponent.  Those coordinates can be clipped freely.  If the remaining
  coordinate already satisfied `nextValue k >= punishmentValue k`, the whole
  clipped tail would again be rational and compile S.2.

Thus the strict deficit is forced at the unique sure owner's own next-tail
coordinate.  The note correctly does not infer that raising this final
coordinate preserves endpoint Nash: its coefficient is now positive.

The scalar regression in Section 5 accurately demonstrates this obstruction.
For the unique sure owner, Quit pays zero and Continue pays
`(1/2)2+(1/2)(-2)=0`; clipping the tail coordinate from `-2` to the floor zero
raises Continue to one.  It is appropriately labeled a local interface
regression, not a full prioritized source.

### Delta check: finite pure-coalition obstruction

Corollary 5 has the correct orientation.  Let `mu(S)` be the product law of
the opponents' quitting coalition in the terminal row.  Because `k` quits
surely, its Quit endpoint is

`Q_k = sum_S mu(S) r_k(S union {k})`.

After replacing only its continuation coordinate by `P_k`, its Continue
endpoint is

`C_k(P_k) = sum_(S nonempty) mu(S) r_k(S) + mu(empty) P_k`.

All other players' support inequalities are unchanged by the clipping.  If
the clipped root still had `Q_k >= C_k(P_k)`, it would be exact support-Nash
and the sure-row compiler would contradict `R.not_instant`.  Thus necessarily
`C_k(P_k)>Q_k`.  Expanding the difference gives exactly

`mu(empty)(P_k-r_k({k}))
 + sum_(S nonempty) mu(S)(r_k(S)-r_k(S union {k})) > 0`.

The unique-owner result gives `mu(empty)>0`; every term with positive `mu(S)`
is a supported opponent coalition.  Positivity of the finite sum therefore
forces either `P_k>r_k({k})` or one supported nonempty `S` with
`r_k(S)>r_k(S union {k})`.  This is only a static pure-coalition passport:
neither the averaging argument nor the reached-row compactification selects a
second source-matched Bellman row carrying that coalition.  The note states
this limitation correctly.

## 5. Comparison with the checked summable-port reduction

`PositiveJointSummablePortPhantomReduction.lean` also reaches
`QuittingSupportBellmanPositiveSingletonDefectResidual`, but from the distinct
positive-joint summable-port source.  It does not subsume the current
attachment-spine composition: it has neither the attachment's nested reached
rows nor its prioritized provenance.  Conversely, the present theorem does
not consume the common positive-singleton defect.  The two routes therefore
merge at the same checked obstruction rather than close each other.

## 6. Frontier and export assessment

The result strictly narrows the **infinite-extension subarm** of the
positive-absorption attachment: that subarm is no longer an independent
prioritized obligation.  The only outputs are now:

1. the already live prioritized positive-singleton-defect arm; or
2. a finite reached, unique-sure-owner row with a rational current value and a
   strict own-coordinate continuation-floor deficit.

This is meaningful internal progress and a good formalization candidate once
the notation is repaired.  It does not yet meet the export significance gate
for `questions/AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md`.  That question explicitly
does not accept a smaller residual or a local rank unless the rank terminates
in S.1/S.2/S.3.  Rank zero here remains unconsumed, while the finite alternative
lies outside the two-element rank and is also unconsumed.  Accordingly I do
not recommend a standalone export until either the positive-singleton defect
or the unique-sure-owner floor-deficit endpoint receives a classified consumer
or a genuinely terminating larger rank.

## Scope confirmed

The nested subsequential rows are exact source-matched limits, not one
executable infinite chronology.  The result supplies no recurrence, periodic
return, all-Continue phantom consumer, S.2 profile in the finite arm, or
unconditional AGKRS classification.  It preserves the same reward table and
prioritized tolerance, but does not identify Bellman annotations with actual
suffix payoffs beyond the explicit reached-row limits.
