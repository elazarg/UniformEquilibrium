# Source and freshness audit of `SHADOW.md`

Reviewer: `SHADOW_GATE_SOURCE_AUDIT`

## Verdict

**FAIL for `SHADOW.md` as presently written; PASS for the four narrowed
mathematical statements after the qualifications below are incorporated.**

The all-half construction, the actual-profile implementation inequality, and
the two finite telescopes are mathematically correct.  None is currently a
Lean declaration.  The universal-interface diagnosis is, however, partly a
strengthening of an already recorded conference diagnosis, and the final
claims in `SHADOW.md` overstate what the telescopes prove.  The source audit
therefore does not approve exporting `SHADOW.md` verbatim.

The exportable mathematical core is:

1. unconditional universal inhabitance of the *bare*
   `QuittingBudgetStablePacketSystem` interface when the finite player type
   contains two distinct players;
2. the finite-player all-behavior implementation inequality

   ```text
   D_* <= card(I) * eta + sum_i (alpha_i + beta_i);
   ```

3. the finite total-debt packet telescope; and
4. its one-coordinate analogue.

These statements do not construct either tier of chronological shadowing and
do not prove that the tangent entrance cannot produce a stronger packet.

## Exact source correspondence

### Bare packet interface

The exact fields are in
`UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`:

* `QuittingBudgetStablePacketData` stores a finite positive-length root word,
  semantic candidates satisfying exact prefix recursion, a successor port,
  prescribed and total endpoint seams, two fixed marginal-hazard lower
  bounds, radius loss, and uniform payoff/debt bounds.
* `QuittingBudgetStablePacketSystem` stores the port type, annotation,
  radii, error functions, two distinct labels, bounds, packet availability,
  and operational sublinearity.

The structure stores no behavior profile, terminal outcome law, marked atom,
or equation relating a port annotation to an externally supplied tangent
source.  Its own docstring explicitly says that actual-source provenance may
be carried externally but is not identified with the annotation.

The all-half stationary construction matches these fields.  The required
complete semantic fixed point follows from:

* `quittingRootThenContinuationProfile_stationary` in
  `UniformEquilibrium/Quitting/Stationary/Root.lean`; and
* `quittingTerminalSemanticPair_rootThenContinuation` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

Together they give, for the stationary semantic pair `z`, the exact equality
`z = quittingTerminalSemanticPrefix reward q z`, including the cap coordinate.
The bound used in the construction is supported by
`abs_quittingTerminalPayoff_le_quittingRewardBound` and
`abs_quittingContinuationBestResponseValue_le`.  Thus prescribed payoff and
cap are both bounded by the finite reward bound, and actual semantic debt lies
between zero and twice that bound.

For every legal scale `0 < h < 1`, `kappa = 1/2` gives
`kappa * h <= 1/2`, the one-row marginal Quit hazard of either fixed label.
The zero combined cost satisfies `IsOperationallySublinearCost` directly.
No probability or strategy-class gap occurs in this construction.

The statements in `SHADOW.md` about probability `2^(-card(I))` of a chosen
coalition, positive successor reach, and deleted-player survival are true for
the all-half stationary profile.  They are **not fields of the inspected
packet-system structure** and must not be described as fields being verified.

### Behavioral cap scope

`quittingContinuationBestResponseValue` is defined in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean` as the supremum over the
entire type `(quittingGame reward).BehaviorStrategy who`.  Consequently the
cap in `quittingTerminalSemanticPair` is the unrestricted unilateral
behavioral cap.  It includes Never, arbitrarily late stopping, calendar- and
history-dependent behavior, and the randomization already available in a
behavior strategy.  The implementation inequality therefore has the claimed
all-behavior scope; it is not merely a stationary or pure-deadline estimate.

### Operational schedule

`IsOperationallySublinearCost` and
`exists_budgetedDivergentCostSchedule` are in
`MathUE/SublinearCostSchedule.lean`.  The latter supplies a positive scale
sequence tending to zero, with nonsummable scale and summable declared cost.
For the packet application, nonnegativity of `omega` and `chi` implies
summability of `omega` along this selected schedule.  This is a scheduled
aggregate conclusion.  It is not a pointwise assertion that
`omega(h) / h -> 0` along every route to zero.

### Existing seed/seam barriers

The exact checked nearby results are:

* `exists_directSemanticSeam_ge_average_sub` and its tangent-family
  specialization in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`;
* `QuittingBoundedSeamChain.abs_actualDebt_sub_candidateDebt_le_tsum`,
  `actualDebtGap_le_candidate_add_seams`, and
  `actualDebtGap_le_two_mul_card_eta` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`;
  and
* `abs_semanticDebtSum_sub_le_of_within` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPrefixMetric.lean`.

The direct-seam results compare two semantic pairs.  The chronological results
compare an artificial candidate chain with the actual profile generated by
the same literal roots and vanishing survival.  Neither states the proposed
one-sided arbitrary-implementation inequality with independent payoff errors
`alpha_i` and cap errors `beta_i`.  That inequality is a genuine, though
elementary, generalization: it follows immediately from

```text
B_i(sigma) - U_i(sigma)
  <= (b_i + beta_i) - (u_i - alpha_i).
```

The all-behavior scope comes entirely from the exact definition of `B_i` just
audited above.

### Packet drift telescopes

No declaration matching either internal-drift telescope was found in the
inspected `Quitting/Debt/Dynamic` or `Diagnostics/Quitting` subtrees.  The
existing sup-tube theorem `abs_semanticDebtSum_sub_le_of_within` is related but
does not telescope marked packet drift.  The sharper endpoint estimate used
here is the elementary `L1` identity

```text
|D(e) - D(x)|
  <= sum_i (|u_i(e)-u_i(x)| + |b_i(e)-b_i(x)|).
```

Combining this with `total_endpoint`, the marked drift inequality, and the
compatibility equation identifying one packet's successor annotation with the
next packet's entrance gives the displayed finite telescope.  If each
coordinate candidate debt lies in `[0,M]`, its boundary term is at least
`-card(I) * M`; for one coordinate it is at least `-M`.  The constants in
`SHADOW.md` are therefore correct for Fin 4.

The telescope requires extra data not present in
`QuittingBudgetStablePacketSystem`: a marked internal candidate, a fixed
positive drift coefficient, and summable drift errors.  Those hypotheses must
remain explicit in any export and proposed Lean declaration.

## Freshness audit

### Theorem A: partially anticipated, unformalized strengthening

No declaration of

```text
Nonempty (QuittingBudgetStablePacketSystem reward)
```

was found.  The unconditional all-half theorem is therefore new at the Lean
surface.

The underlying interface warning is not wholly new.  Proposition 6AO in
`notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md` already constructs a
conditional one-port periodic self-loop and observes that the packet type does
not tie its declared scale to literal mesh or its annotation to actual-source
provenance.  The new construction removes all of that proposition's producer
hypotheses and proves universal inhabitance from an arbitrary reward table.
It is best described as an unconditional strengthening and definitive
specification test, not as the first discovery that the interface is weak.

### Theorem B: new exact formulation, closely adjacent to checked barriers

No exact declaration or conference statement with independent one-sided
payoff and unrestricted-cap implementation errors was found.  It is not a
duplicate of the direct seam theorem or the same-root chronological seam
theorem.  Its proof is elementary, and its significance is quantitative
scope rather than a new producer.

### Theorems C and D: fresh in the inspected corpus

No matching total or coordinate marked-packet telescope was found in Lean,
`exports/`, or the narrowly searched conference notes.  They appear to be the
genuinely new mathematical content of the packet.  They strictly rule out a
repeated positive-drift packet architecture whose only repayment is a
summable endpoint seam.

No paper claim is used, so there is no literature-translation dependency to
audit.

## Required scope repairs before export

1. Replace the assertion that the full two-tier producer “does not follow” by
   the exact result: the present Lean interface does not express source
   attachment, and any source-faithful realization satisfying the displayed
   marked-drift hypotheses must contain divergent cumulative internal debt
   drain.  No logical countermodel to a richer producer is supplied.

2. Call the telescope output an **internal semantic debt drain**, not an
   admissible payoff return.  The proof does not supply prescribed-payoff
   charge, punishment-floor admissibility, a return to one fixed semantic
   pair or law, or a downstream uniform-equilibrium consumer.

3. State exact packet compatibility and marked-candidate hypotheses in
   ordinary mathematics.  Merely referring to a “source-faithful packet” is
   not self-contained enough for an export theorem.

4. State the direct-reprojection obstruction along the selected divergent
   schedule.  Operational sublinearity does not give the claimed pointwise
   comparison at every sufficiently small scale.

5. Keep terminal-atom and positive-reach facts outside the list of fields
   verified for `QuittingBudgetStablePacketSystem`.

With these repairs, the narrowed A--D packet has correct source
correspondence, correct unrestricted-deviation scope, and identifiable fresh
content.  Without them, `SHADOW.md` fails the export source/freshness gate.
