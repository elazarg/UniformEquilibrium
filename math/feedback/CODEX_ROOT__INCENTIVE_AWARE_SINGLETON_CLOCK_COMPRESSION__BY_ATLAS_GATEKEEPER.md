# Export-gate audit of incentive-aware singleton clock compression

Reviewer: `ATLAS_GATEKEEPER`

## Verdict

**NOTES ONLY.**

The corrected anchored debt estimate is rigorous, sharp from the supplied
data, and genuinely stronger than mass-only clock compression.  The
distinct-observer paid-row wrapper and its deadline alignment are also valid.
They do not, however, pass export gate 4.

The existing Fin4 minimum-singleton leaf does not supply that its singleton
owner has vanishing source debt.  Therefore the strengthened endpoint is not
an arbitrary-data adapter from the whole leaf.  Even on the inactive-owner
subclass, the terminal exploitability witness already supplies a full-gap paid
row at every actual compressed target; the new information is only that the
observer can be chosen different from the low-debt owner and that its first
disagreement is no later than the forced deadline.  No current consumer uses
that co-realization.

Thus the package neither answers
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` nor strictly narrows one of
its accepted outputs.  That question expressly requires a uniform-payoff or
terminal-approximation consumer, a source-preserving well-founded descent, or
an exhaustive split whose every arm reaches one of those outputs; it also
excludes a finer residual list without consumers.

This verdict concerns conjecture-facing export only.  The mathematics is
appropriate for Research formalization as a reusable compression theorem and
a localized terminal-gap wrapper.

## Claims checked

### Correct generic theorem

For a behavioral profile `sigma`, owner `j`, positive anchor `a`, anchored
singleton mass `m`, owner survival `p_a`, and `0 < lambda < m`, there is an
anchored pure completion `tau_t` with singleton stage mass greater than
`lambda`, unchanged opponents, literal post-date tail equality, unchanged
owner cap, and

\[
d_j(\tau_t)\le
\frac{p_a-\lambda}{m-\lambda}d_j(\sigma).
\]

The positive-anchor correction is essential.  If

\[
e=\sum_{s<a}\pi_s(B-V_s),
\]

then the exact completion debt is

\[
d_j(\tau_t)=e+p_a(B-V_t),
\]

not merely `B-V_t`.  The high-survival averaging estimate in the root note
and strengthening review then proves the displayed coefficient.  The
two-player example makes the coefficient sharp at the stated information
level.

### Correct limitation

The simultaneous-tie two-player example correctly shows that compressing an
inactive owner at an exact minimum can preserve that owner's zero debt while
creating debt `1/2` in the other coordinate.  Hence neither no-new-support nor
target near-minimality follows from the compression theorem.

### Correct conditional terminal-gap wrapper

If the compressed owner's target debt is less than the witness gap `gamma`,
the profitable coordinate supplied at that actual target cannot be the owner.
The checked pure-time support-pair/first-disagreement decoder therefore gives
a full-gap row for some observer `o != j`.  Since `j` stops by the forced
deadline almost surely, two observer plans first differing strictly after
that deadline have identical payoff; a positive row must begin no later than
the deadline.  On Fin4 one may pass to a subsequence fixing `o`.

## Exact source correspondence

The audit used:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- the unrestricted pure-time cap representation in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingContinuationBestResponseValue_update_self` and the literal
  one-date profile/tail declarations used by
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `FinFourMinimumAtomProducer`, `FinFourMinimumAtomChronology`, and
  `FinFourOwnerCompressedSingletonProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean` and
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`.

The checked mass-only producer retains no vanishing-debt field for the
singleton owner.  A minimum semantic point can have that owner in its positive
debt support.  Consequently the sequence-level conclusion
`d_j(tau_n) -> 0` requires the additional premise `d_j(sigma_n) -> 0`; it is
not furnished merely by being the selected singleton-law owner.

## Why gate 4 fails

The package adds the passport

\[
\text{fixed singleton mass}
+\text{small owner debt}
+\text{distinct-observer paid row}
+\text{literal tail}.
\]

But:

1. small owner debt is conditional on an inactive-owner source sequence;
2. the paid row itself is a universal consequence of `W` at every actual
   target;
3. pure-root purification can destroy both the row and the small owner debt;
4. the copied source cap-stack is not cap--Nash for the modified target; and
5. no checked or ordinary-mathematics consumer turns this combined passport
   into terminal approximants, UE, recurrence, or a regenerated smaller
   atlas state.

The two independent reviews correctly identify the mathematical readiness of
the local theorems.  Their statement that the package is exportable as a
producer overlooks the mandatory conjecture-facing gate: a stronger producer
is not exportable merely because its fields may be useful later.

## Allowed formalization scope

A Research handoff may include:

1. the generic anchored incentive-aware compression theorem with the sharp
   coefficient;
2. the exact two-player no-new-support regression;
3. a localized theorem which, from `d_j(target) < gamma`, retains a
   full-gap profitable observer `o != j`; and
4. the forced-deadline bound on the row's first disagreement.

It must state explicitly that:

- the source root word remains cap--Nash only over its original suffix;
- no target near-minimality or no-new-support follows;
- the inactive-owner premise is additional and is not supplied for every
  minimum-singleton atlas source; and
- the result does not consume or contract the concentrated-singleton atlas
  node.

The packet should be reconsidered for export only after a theorem consumes
this co-realized passport or proves that every minimum-singleton atlas source
admits the required inactive owner and that the resulting strengthened node
strictly reduces the accepted concentrated-singleton obligation.
