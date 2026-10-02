# Verification of the renewal and paid-cap status claims

## Verdict

Claude's three mathematical status claims are substantially correct.

1. Commit `f0f1b34` does answer alternative 1 of
   `FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md`, understood as the structural
   source/regeneration/rank alternative.  The export packet under-claims this
   point by treating a horizontal backward compiler as mandatory even after
   the checked construction has supplied an exhaustive recursive dispatch and
   proved that source-independent downstream conclusions compose without such
   a compiler.
2. Commit `00d67a4` advances, but does not answer, the two paid-cap closure
   questions.  It reconstructs actual paid/reset descendants in both descent
   arms and sharpens double inertness to double unique-all-Continue caps, but
   supplies neither a well-founded descent nor a consumer of the unique-cap
   arm.
3. Commit `d91c3be` proves the stated negative boundary: near-minimum paid-cap
   sources have vanishing total absorption, so their fixed paid premium cannot
   be converted into a fixed cap-charge floor by this construction alone.

## 1. Renewable canonical support handoff

The exact declarations establish all the structural fields named in the first
numbered alternative.

### Complete endpoint and recursive sources

`CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_endpointSourceRegeneration`
jointly compactifies the handoff's literal endpoint profiles, retains their
marked mass, and builds a complete `FinFourMinimumAtomProducer` at the exact
endpoint semantic cluster with the same hard residual.

`FinFourRenewableMinimumSourceNode.nonempty_fullReplacementSourceRegeneration`
does the same at every minimum-fibre recursive full-replacement endpoint.  Its
causal chronology is built from a subsequence of the parent's literal
full-replacement profiles; it does not substitute an unrelated behavioral
source.

### Renewable rank and exhaustive next dispatch

`FinFourRenewableMinimumSourceNode.terminalExit_or_nonempty_supportDescent`
is exhaustive.  Its only recursive arm is the flat, no-entry, minimum-fibre
full-replacement arm, and that arm constructs a child satisfying strict
positive-debt-support inclusion.

`canonicalPairRenewableTransition_rank_lt` proves strict decrease of one
natural-valued phase-tagged rank on every declared edge.  The origin phase has
no incoming transition and therefore cannot be recreated by regeneration.
Within the tangent phase, every recursive edge strictly lowers support
cardinality.  `nonempty_renewalTrace` proves termination of the recursive lane.

This is exactly the kind of phase-tagged rank explicitly allowed by the
maintained question; it is not a new parent-relative rank at every step.

### Why the absent horizontal compiler does not defeat alternative 1

The maintained question's numbered alternative 1 asks for a complete child
source, a strict renewable finite rank, and enough provenance to iterate the
construction.  All three are supplied.

The surrounding prose additionally asks either for horizontal-seam control or
for proof that the recursive composition does not need it.  The latter is now
provided by `FinFourRenewableTrace.consume` and
`CanonicalPairMinimumEndpointSupportRankHandoff.consume_renewalTerminalExit`:
if each terminal descendant yields one proposition depending only on the
reward table—such as existence of a uniform-equilibrium payoff—then the result
is consumed at the descendant and requires no transport of deviations back
through earlier horizontal seams.

The construction does not prove the three terminal-exit consumers.  That is a
separate closure obligation, not a failure of renewable source/rank
regeneration.  It also correctly makes no claim that a source-indexed or
profile-indexed conclusion can be transported backward.

Accordingly, the export packet's sentence saying that alternative 1 is not
literally completed is too conservative relative to the maintained numbered
alternative and the checked source-independent composition theorem.  The
question should be marked answered in its structural sense, with its three
terminal exits redirected to their own maintained questions.

## 2. Paid-cap descent and inertness

Commit `00d67a4` contains the following genuine advances.

* `QuantitativeDebtDescent.nonempty_finitePaidResetRegeneration` turns a
  quantitative cap-port descent into one finite actual descendant retaining a
  paid row, zero reset debt, positive incidence, and a fresh fixed-law reset
  dispatch.
* The Fin4 double-port adapters establish this regeneration on both the source
  and repaired sides.
* `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` replaces
  selector-dependent inertness by a canonical alternative: a positive-
  absorption maximal exact root gives immediate actual descent/regeneration,
  while zero maximal absorption makes all Continue the unique exact root at
  that cap.
* Applying this to both actual profiles leaves source regeneration, repaired
  regeneration, or two unique-all-Continue caps.

These theorems do not orient repeated real-valued descent by a finite rank and
do not consume the final double-unique-cap arm.  Hence both
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` and
`FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md` remain open, but their entrance should
be updated to include the new actual regeneration and strengthened inert
normal form.

The repaired-owner zero-debt proof currently has a proof-script defect in the
top stacked file, but not a mathematical gap:
`quittingTerminalSemanticPair_stationary_envelope_eq_cap` bridges the full
behavioral envelope to the stationary unilateral cap, after which
`repaired_owner_cap_eq_payoff` proves zero debt.  The preceding stacked layer
already uses this exact bridge for the same profile.

## 3. Vanishing cap charge near the minimum

Commit `d91c3be` proves
`QuittingPaidCapLiftedSource.totalAbsorption_tendsto_zero_of_initialDebt_tendsto_minimum`
and its no-positive-floor corollary.  The proof is the exact debt budget

```text
D_* * totalAbsorption <= initialDebt - D_*,
```

followed by `initialDebt -> D_*`.  The paid-row gain does not enter this upper
bound and may remain uniformly positive.

Thus a family of paid sources approaching the global minimum cannot obtain a
fixed cumulative-charge floor from its cap lifts merely by retaining a fixed
normalized premium.  This is a genuine no-go for that proposed route.  It does
not exclude profile-dependent regeneration, a different chronology carrying
charge, or a finite-rank descent.

## Files and declarations inspected

* `CanonicalPairEndpointSourceRegeneration.lean`
* `CanonicalPairFullReplacementSourceRegeneration.lean`
* `CanonicalPairRenewableSourceRank.lean`
* `CanonicalPairMinimumEndpointRenewal.lean`
* `FinFourPaidResetDescentRegeneration.lean`
* `FinFourPaidResetDoubleDescentRegeneration.lean`
* `PaidCapMaximalOneStepRegeneration.lean`
* `FinFourPaidCapMaximalDoubleRegeneration.lean`
* `PaidRowCapPortDispatch.lean`
* `PaidCapPortExactTrichotomy.lean`
* `FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md`
* `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`
* `FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`
