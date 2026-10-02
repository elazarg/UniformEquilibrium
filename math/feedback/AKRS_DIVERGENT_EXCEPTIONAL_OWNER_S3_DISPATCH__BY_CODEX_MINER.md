# Whole-packet gate for `AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH`

**Reviewer:** CODEX_MINER  
**Date:** 2026-08-25  
**Current head checked:** `76479d5`  
**Verdict:** **ACCEPT**

This is a second independent falsification attempt and a gate against every
item in [`exports/README.md`](../exports/README.md).  I found no mathematical
objection.  The packet proves, in ordinary mathematics, that every
`QuittingUniqueExceptionalOwnerSource reward` whose selected horizons tend to
infinity yields

```text
QuittingInstantPunishmentεEquilibriumExistence reward ∨
QuittingWellSupportedAbsorbingSequenceExistence reward.
```

The negative-solo field of
`QuittingDivergentNegativeExceptionalOwnerResidual` is genuinely unnecessary.
The theorem closes that named source class through literal S.2 or S.3; it does
not claim AGKRS Theorem 3.4.

## 1. Unrestricted source-Nash and punishment IR

At the literal source index `source.selected n`, `family.nash` is

```text
IsεQuittingRootSequenceNash reward (2 * family.error ...)
  (quittingStationaryPrefixFamilyPlan family ...).
```

The checked
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` identifies this with
terminal Nash against every unilateral history-dependent behavioral strategy.
It is therefore legitimate to apply
`punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash`.  Its proof uses
the infimum-over-opponent-plans definition of `quittingPunishmentValue` and the
supremum over all behavioral replies in `quittingBestReplyValue`; it is not a
stationary-only or pure-time inequality.

The terminal payoff of that same literal plan is definitionally
`quittingStationaryPrefixFamilyValue family (source.selected n) 0 i`.
Consequently

\[
  P_i-2e_n\le V_n(i).
\]

The selected errors tend to zero by composing `family.error_tendsto_zero`
with `source.selected_strictMono.tendsto_atTop`, and
`source.tendsto_initialValue_soloReward` gives
`V_n(i) -> r_i({o})` under the displayed horizon hypothesis.  Passing to the
limit proves `P_i <= r_i({o})` for every player.  This step does not identify
the punished label with the exceptional owner.

I also checked the newer dirty-tree theorem
`QuittingUniqueExceptionalOwnerSource.continueFloor_le_soloReward`.  It is a
different, weaker literal-Never bound and does not duplicate this punishment
IR conclusion or the packet's S.2/S.3 dispatch.

## 2. Singleton-floor S.3 construction

Assume `r_i({i}) <= r_i({o})` for every `i`, let
`M = quittingRewardBound reward`, and for arbitrary `delta > 0` put

\[
  q=\min\{1/2,\delta/(4M+2)\}.
\]

Since `M >= 0`, the denominator is positive and `0 < q < 1`.  The strict
estimate `2Mq < delta` holds in both arms of the minimum:

* if `q <= delta/(4M+2)`, use `2M < 4M+2`;
* if `q=1/2`, selection gives `delta >= 2M+1`, hence `2Mq=M<delta`.

Repeat the solo product row in which `o` quits with probability `q`.  Its
survival is `(1-q)^N`, so it is completely absorbing.  The checked solo
terminal-value theorem makes every actual next-tail vector exactly `r({o})`.
The owner's Quit and Continue endpoints are both `r_o({o})`, regardless of
the sign of that number.  For an outsider `i`, Continue is `r_i({o})` and
Quit is

\[
  (1-q)r_i(\{i\})+q r_i(\{o,i\}).
\]

Thus the only used-action defect is at most
`q (r_i({o,i})-r_i({o})) <= 2Mq < delta`.  This has the correct sign for the
used Continue action in `IsQuittingRootSupportApproxNash`; no weighted defect
or terminal Nash property is substituted.  Both owner actions are used and
have zero endpoint difference.  Therefore the construction proves literal
`QuittingWellSupportedAbsorbingSequenceExistence`, and the checked adapter
maps it to paper S.3.

The negative-owner falsifier passes for exactly the reason the packet states:
Never may beat the prescribed infinite profile, but S.3 asks for actual-tail
one-row sequential perfection plus complete absorption, not global Nash.

## 3. Nested selections and all `lambda` cases

The quantifiers survive the selections when they are made in the stated
order.  First take a strict finite-label subsequence of
`n |-> family.punished (source.selected n)`.  Then take a strict convergent
subsequence of the corresponding live masses in the compact interval
`[0,1]`.  The final index is the explicit composition with `source.selected`.
Composition preserves strict monotonicity; therefore vanishing error and
horizon divergence persist.  Source concentration also persists by ordinary
composition of limits.

Let the live-mass limit be `lambda`.

* `lambda=0`: the final composed subsequence is a literal input to
  `quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero`.
* `0<lambda<1`: the fixed punished label, positive live limit, and divergent
  horizons are exactly the inputs of
  `exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq`.  The
  returned equality, not the target-free wrapper, supplies the strict
  `<1` hypothesis of `wellSupported_of_lt_one`.
* `lambda=1`: this is handled below.

These cases exhaust the limit because every product Continue mass lies in
`[0,1]`.  Positivity at every finite source row does not erase the zero-limit
arm.

## 4. The unit-live arm

Fix a player `i` after the common subsequence has already been selected.  The
checked product identity gives

\[
 c_n=d_{n,i}p_{n,i},\qquad 0\le p_{n,i}\le1,
\]

where `c_n` is full Continue mass and `d_{n,i}` is player-deleted Continue
mass.  Hence `c_n <= d_{n,i} <= 1`; `c_n -> 1` squeezes `d_{n,i} -> 1`.
No player-dependent secondary subsequence is needed.

With the canonical reward bound, the checked estimate
`abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le` now makes the
same-row immediate-Quit value `Q_n(i)` converge to `r_i({i})`.  The source
theorem `fixedOpponentsQuitValue_le_initialValue`, at those exact same source
indices, says

\[
 Q_n(i)\le V_n(i)+2e_n.
\]

Using source concentration and error convergence gives
`r_i({i}) <= r_i({o})`.  Since `i` was arbitrary, the singleton-floor S.3
compiler applies.  This checks the source/profile provenance and rules out a
hidden index or conditioning mismatch.

## 5. Adapter, paper branch, and current novelty

For a supplied
`residual : QuittingDivergentNegativeExceptionalOwnerResidual reward`, the
fields `residual.source` and `residual.horizon_tendsto` are exactly the main
theorem's hypotheses.  The conclusions inject into the S.2 and S.3 positions
of the literal `hnegative` codomain of
`theorem3_4_of_prioritizedSourceClosures`.  The well-supported-to-sequential
adapter preserves the paper's actual-tail and all-positive-tolerances
quantifiers.

I checked the paper-facing transcription of Definition 3.2, Remark 3.3, and
Theorem 3.4 in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`.  The packet lands
in the absorbing sequentially approximately perfect branch, not merely a
Bellman annotation or a pointwise changing disjunction.

A current-head narrow search found no checked declaration consuming every
divergent unique-exceptional-owner source and no checked singleton-floor S.3
compiler.  The uncommitted `continueFloor_le_soloReward` and finite join-gain
split in `NegativeExceptionalOwnerInstantObstruction.lean`, and the associated
paper capstone edit, leave join consumers as hypotheses.  They therefore do
not subsume this result.  Conversely, this packet does not consume the
prioritized pointwise or positive-joint/no-sure-exit source classes.

## 6. Export gate

All eight mandatory items pass.

1. The statement gives the finite type, decidable equality, normalized reward
   table, literal source, horizon limit, and exact disjunctive conclusion.
2. Both auxiliary lemmas and all three limit cases are proved; no mathematical
   lemma is deferred.
3. The probability, product randomization, stopping, actual-tail, and
   unrestricted behavioral-deviation modes are audited correctly.
4. The negative-residual adapter and the checked AGKRS `hnegative` consumer
   are exact.
5. The negative owner, maximal collision, zero/interior/unit live limits,
   label mismatch, and one-player boundaries test the relevant seams.
6. The named Lean and paper sources are current, the new content is identified,
   and the checked current dirty-tree changes are not duplicates.
7. Euler's substantive PASS and this independent falsification leave no
   unresolved objection.
8. The Lean handoff names a narrow theorem order and does not assume the
   desired dispatch as a structure field.

The export author should make the ministerial metadata update from
`Independent review` to `Independent reviews` and link this second review.
That edit does not condition the mathematical ACCEPT verdict.

