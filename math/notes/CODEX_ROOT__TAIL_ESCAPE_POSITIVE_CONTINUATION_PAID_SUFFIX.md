# Positive-continuation tail escape carries a post-mark paid row

Author: `CODEX_ROOT`

## Status

**Ordinary-mathematical proof draft; not Lean-checked.**  This is a strict
localization of the paid-row data in the positive-continuation subfamily of
the Fin4 quantitative tail-escape leaf.  It is not yet a consumer: the
existing paid-cap trichotomy does not use the fact that the paid witnesses
first disagree strictly after the retained collision row.

The complementary root geometry is treated in
[`ATLAS_FALSIFIER__TAIL_ESCAPE_TWO_ANCHOR_REPAIR.md`](ATLAS_FALSIFIER__TAIL_ESCAPE_TWO_ANCHOR_REPAIR.md):
two asymptotically sure quitters permit a source-faithful low-tail repair.

## Question

Let `profile` be one literal selected profile in a
`TailEscapeSubsequence`, let `stage` be its retained marked date, and let
`tail` be the literal behavioral spine strictly after that date.  Assume:

1. the marked nonsingleton coalition has unconditional mass at least
   `lambda > 0`;
2. the marked product root has joint Continue probability at least
   `rho > 0`; and
3. the shifted tail has total terminal debt at least `Dtail > 0`.

Can the high tail debt be attached to the same literal chronology without
moving the marked atom or selecting an unrelated paid source?

## Theorem

For `n = card iota`, there are a player `i` and two pure quitting times
`sourceTime`, `receivingTime`, both strictly after `stage`, such that

\[
 U_i(\text{profile}[i\leftarrow Q_{\rm receivingTime}])
 -U_i(\text{profile}[i\leftarrow Q_{\rm sourceTime}])
 \ge \frac{\lambda\rho D_{\rm tail}}{2n}.
\tag{1}
\]

Consequently the literal `profile` carries a
`QuittingPaidFirstDisagreementRow` of gain

\[
 g=\frac{\lambda\rho D_{\rm tail}}{2n},
\tag{2}
\]

whose first-disagreement date is strictly later than the marked collision
date.  On Fin4 the gain is `lambda * rho * Dtail / 8`.

The constant `1/2` merely avoids best-response attainment.  Any fixed factor
strictly below one is available.

## Proof

Write `Z` for the terminal semantic pair of the literal tail.  Some player
`i` satisfies

\[
 d_i(Z)\ge D_{\rm tail}/n.
\tag{3}
\]

Against the fixed opponents in the tail, the unrestricted behavioral cap is
the supremum of the pure-time values.  The prescribed behavioral strategy is
a stopping-law average of those same pure-time values.  Therefore there are
relative pure times `a,b in Nat union {Never}` such that

\[
 V_i^Z(b)-V_i^Z(a)\ge d_i(Z)/2.
\tag{4}
\]

For example, choose `b` within `d_i(Z)/4` of the cap and choose a stopping
time `a` in the prescribed stopping-law support whose value is at most the
prescribed average plus `d_i(Z)/4`.  This uses no cap attainment and includes
`Never` and arbitrarily late finite times.

Rebase `a,b` to absolute dates after `stage`.  The exact common-prefix
transport identity gives

\[
 V_i^{\rm profile}(\widehat b)-V_i^{\rm profile}(\widehat a)
 =H_i\bigl(V_i^Z(b)-V_i^Z(a)\bigr),
\tag{5}
\]

where `H_i` is the probability that all opponents of `i` Continue through
the marked date.  This identity concerns the two pure-time deviations; the
prescribed action of `i` before the mark is irrelevant.

Let `L` be the joint live mass reaching the marked row and `c` its joint
Continue probability.  The marked atom has mass at most `L`, so

\[
 L\ge\lambda.
\tag{6}
\]

Deleting player `i` from a survival product can only increase it.  Hence

\[
 H_i\ge Lc\ge\lambda\rho.
\tag{7}
\]

Combining (3)--(7) proves (1).  Applying
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` produces the
paid row.  Since both absolute witnesses are rebased into the tail, their
first disagreement is strictly after `stage`.

## Tail-escape specialization

In `TailEscapeSubsequence`, with minimum-law atom mass `mu`, one may take

\[
 \lambda=\mu^2/8,
 \qquad
 D_{\rm tail}\ge D_*+\mu^2D_*/16.
\tag{8}
\]

If the selected marked roots have joint Continue mass bounded below by
`rho`, the same literal selected profiles therefore carry post-mark paid rows
with the fixed gain

\[
 \frac{\rho\mu^2}{64}
 \left(D_*+\frac{\mu^2D_*}{16}\right)>0.
\tag{9}
\]

No semantic representative is substituted and the marked atom remains in
the prescribed receiving profile.

## What is new, and what is not

A terminal exploitability witness already supplies a full-gap paid row at
every actual profile through
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`.  The new
content here is the **ordering and co-realization**:

```text
retained marked collision row
        < first disagreement of the paid witnesses
        < same literal post-mark tail.
```

This is precisely the provenance absent from an independently selected paid
row.  It may be useful to a chronology consumer that can spend a paid mark
only after reaching a retained causal atom.

It does not by itself yield a prescribed-payoff exact edge, an admissible
return, terminal approximants, or support descent.  The current paid-cap port
forgets this ordering, so feeding (2) into that port merely re-enters its
quantitative-descent/inert-stall boundary.

## Resulting root-geometry split

After compactifying the four marked marginal roots:

* at least two sure-Quit limit coordinates are handled by the two-anchor
  self-tail repair;
* no sure-Quit limit coordinate gives a positive joint Continue floor and
  therefore the post-mark paid row above; and
* exactly one sure-Quit limit coordinate is the remaining unique-owner
  geometry.

Thus the unresolved quantitative tail-escape leaf is reduced to consuming a
source-ordered paid collision/tail pair or the unique-owner boundary.

## Declarations inspected

* `QuittingNonsingletonMinimumLawTransfer.TailEscapeSubsequence`,
  `selectedStageMass`, and `selectedTailExcess` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
* `quittingRelativePureTimeTerminalValue_sub_prefixTransport` and
  `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`.

## Next question

Can the exact order “fixed collision first, fixed paid disagreement later” be
converted into a prescribed-payoff admissible edge/return, or can the paid
tail deviation be pulled backward through the collision row to force a
source-matched support drop?
