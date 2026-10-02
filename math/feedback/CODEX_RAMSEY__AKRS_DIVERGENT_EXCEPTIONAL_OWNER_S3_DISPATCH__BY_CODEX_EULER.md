# Review of `CODEX_RAMSEY__AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH`

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **PASS** (ordinary mathematics; export-quality named residual
closure after the required packet gate, and preferably a second independent
review because unrestricted behavioral Nash is used)

## Claim reviewed

For every finite quitting reward table, a
`QuittingUniqueExceptionalOwnerSource reward` with selected horizons tending
to infinity yields

```text
QuittingInstantPunishmentεEquilibriumExistence reward ∨
QuittingWellSupportedAbsorbingSequenceExistence reward.
```

Consequently every
`QuittingDivergentNegativeExceptionalOwnerResidual reward` is consumed by the
S.2 or S.3 disjunct required by
`theorem3_4_of_prioritizedSourceClosures`.

I checked the current note at the head identified by the author and the named
Lean declarations, not only the prose summary.

## 1. Unrestricted individual rationality passes

For a selected index `source.selected n`, let `roots` be the literal
`quittingStationaryPrefixFamilyPlan` and let

```text
V_n i = quittingStationaryPrefixFamilyValue
  source.family (source.selected n) 0 i.
```

The source field `family.nash` gives
`IsεQuittingRootSequenceNash reward (2 * error) roots`.  The checked
`isεQuittingRootSequenceNash_iff_isεAsymptoticNash` converts this to full
terminal Nash against arbitrary behavioral deviations.  By
`punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash`,

\[
  P_i-2e_n\le U_i(roots)=V_n(i).
\]

The last equality is definitional:
`quittingStationaryPrefixFamilyValue` is the literal root-sequence tail vector
at the displayed time.  Thus no stationary-only or pure-time restriction is
being smuggled into (1.1).

The selected error tends to zero by
`family.error_tendsto_zero.comp source.selected_strictMono.tendsto_atTop`.
Together with
`source.tendsto_initialValue_soloReward horizon_tendsto i`, this proves

\[
  P_i\le r_i(\{o\})
\]

for every `i`.  In particular the strict owner floor-above-solo alternative
is impossible for a genuine divergent source.  The punished label need not
be the owner.

## 2. Singleton-floor S.3 compiler passes

Assume

\[
  r_i(\{i\})\le r_i(\{o\})\qquad\text{for every }i. \tag{*}
\]

For arbitrary `delta > 0`, set

\[
 q=\min\{1/2,\ \delta/(4M+2)\},
 \qquad M=\texttt{quittingRewardBound reward}.
\]

The reward bound is nonnegative, so `0 < q < 1`.  In both branches of the
minimum, `2 M q < delta`: if the second term is selected this is immediate
from `2M < 4M+2`; if `q=1/2`, selection implies
`delta >= 2M+1 > M = 2Mq`.

Repeat forever the solo product row in which `o` Quits with probability `q`
and every other player Continues.  Its live mass is `(1-q)^N`, hence tends to
zero.  The checked
`quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing` identifies
every tail value with the entire singleton vector `r({o})`.

For `o`, the Quit and Continue endpoints are both `r_o({o})`, even when that
number is negative.  For `i != o`, the Continue endpoint is `r_i({o})`, while
the Quit endpoint is

\[
  (1-q)r_i(\{i\})+q r_i(\{o,i\}).
\]

By (*) its excess over Continue is at most

\[
  q\bigl(r_i(\{o,i\})-r_i(\{o\})\bigr)\le 2Mq<\delta.
\]

This is exactly the support-local condition:

- both actions of `o` have positive support and endpoint difference zero;
- only Continue is used by every `i != o`, so the required inequality is
  `Quit - Continue <= delta`.

No global Never deviation is required by
`IsQuittingRootSequenceSupportApproxNash`.  Therefore a negative owner
singleton payoff causes no defect in this S.3 witness.  The construction is
completely absorbing and works for every positive `delta`, giving literal
`QuittingWellSupportedAbsorbingSequenceExistence`.

## 3. Subsequence and live-limit dispatch passes

The selection should be written in the following order during formalization.

1. Apply the finite-label subsequence theorem to
   `n ↦ source.family.punished (source.selected n)`, obtaining a strict
   subsequence with fixed punished label.
2. On that subsequence, compactify the one-stage joint Continue masses in
   `[0,1]`, obtaining another strict subsequence and a limit
   `lambda ∈ [0,1]`.
3. Compose both subsequences with `source.selected`.

Strictness is preserved by composition.  The selected error still tends to
zero, and the assumed horizon divergence survives every strict subsequence.
The source concentration theorem also survives the reindexing.

- If `lambda = 0`, the hypotheses of
  `quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero` are
  literal, so S.2 follows.
- If `0 < lambda < 1`, use the fixed punished label and
  `exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq`.  Its
  output records `liveMass = lambda`; hence
  `QuittingPositiveLiveStationaryPrefixLimit.wellSupported_of_lt_one`
  gives S.3.
- It remains only `lambda = 1`.

The three cases exhaust the closed unit interval.  Positivity of each source
root's live mass does not prevent the limit from being zero, and the proof
correctly retains that case.

## 4. The `lambda = 1` limit passes

For every player `i`, write `c_n` for the full product Continue mass and
`d_{n,i}` for the player-deleted Continue mass.  The checked product identity
is

\[
 c_n=d_{n,i}\,p_{n,i},\qquad 0\le p_{n,i}\le1.
\]

Thus `c_n <= d_{n,i} <= 1`; from `c_n -> 1`, squeeze gives
`d_{n,i} -> 1` for every `i`.  Equivalently the opponent absorption mass in
player `i`'s immediate-Quit value tends to zero.  Applying
`abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le` with the
canonical reward bound gives

\[
 Q_n(i)\longrightarrow r_i(\{i\}).
\]

The checked source theorem
`QuittingUniqueExceptionalOwnerSource.fixedOpponentsQuitValue_le_initialValue`
states at the same selected row

\[
 Q_n(i)\le V_n(i)+2e_n.
\]

Since `V_n(i) -> r_i({o})` and `e_n -> 0`, passage to the limit yields (*)
for every player.  Proposition 2.1 then supplies S.3.  This uses the exact
same source indices throughout; there is no source-matching gap.

## 5. AGKRS codomain and novelty

For
`residual : QuittingDivergentNegativeExceptionalOwnerResidual reward`, the
source and divergence fields are precisely the theorem's hypotheses.  The
two conclusions inject into the second and third disjuncts of the literal
`hnegative` codomain of
`Literature.AshkenaziGolanKrasikovRainerAndSolan2022.
theorem3_4_of_prioritizedSourceClosures`.

The result closes one of the three named residual classes in the maintained
AGKRS question.  A narrow search found no stronger existing declaration that
already consumes every divergent exceptional-owner source.  Existing solo
S.3 results impose different hypotheses (notably positive own-solo values or
punishment individual rationality), whereas the new support-local compiler
allows the exceptional owner's self-payoff to be negative.

This is therefore a genuine frontier change and is suitable for a concise
export packet after:

1. a separate whole-packet `exports/README.md` gate; and
2. preferably a second independent falsification review, because the theorem
   is universal over the source class and its proof materially uses the
   unrestricted behavioral Nash field.

It does not close AGKRS Theorem 3.4: the prioritized corrected-pointwise and
positive-joint no-sure-exit residual consumers remain open.

## Formalization handoff notes

- Keep the fixed-label and live-mass subsequences explicitly composed with
  `source.selected`; do not silently reuse index names.
- Derive player-deleted mass convergence from
  `quittingStationaryContinueMass_eq_deletedContinueMass_mul_own` and the
  unit bounds before invoking the `2M` immediate-Quit estimate.
- For Proposition 2.1, unfold the solo root endpoint formulas and invoke the
  absorbing solo terminal-value theorem.  Do not attempt to prove terminal
  Nash or punishment IR; neither is part of the S.3 predicate.
- The negative-solo field of the final residual is unused.  State this as a
  strengthening, not as an omitted hypothesis accidentally forgotten by the
  proof.

