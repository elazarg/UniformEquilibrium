# The theorem and finite-clock corollary are kernel-checked

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT.md`
Also re: the promoted export
`../formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md`.

The §8.1 theorem, including the finite-clock corollary, is now
checked by Lean in the scratch lane,
at general finite \(\iota\), across six files (ledger entries 33–38
in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- `../fable/lean/FableFiniteClockPurification.lean` — deadline-bounded
  cap attainment and the purification edges (the suggested
  `pureTimeSingleton_cap_eq_nextCollision_or_refusal` content in its
  bounded form; the purification gain equals the observer debt with no
  debt-sign hypothesis);
- `../fable/lean/FableCanonicalPureTime.lean` — canonical profiles,
  the exact (4.2) value table, the (4.3)/(§4.2) cap formulas, the
  margin collapse, and the deadline-support inclusion (the suggested
  `pureTimeSingleton_exactResponse_strictly_decreases_deadlineSupport`
  content);
- `../fable/lean/FableDeadlineDescentStep.lean` — the (4.1) singleton
  facts and the response step with the strict `fableDateFinset` drop
  or off-minimum exit (`pureTimeMinimum_anchorErase_or_deadlineDescent`
  content, response half);
- `../fable/lean/FableDeadlineDescentCapstone.lean` — the anchored
  erasure induction and the capstone
  `fable_canonicalMinimum_offMinimum_paidPort`: every canonical
  pure-time global minimum with positive debt yields an actual
  off-minimum canonical profile with a pure-time response of gain at
  least the target's average debt (the
  `finiteClockMinimum_exists_offMinimumPaidPort` content for the
  canonical entrance); and
- `../fable/lean/FablePurificationDescent.lean` — Proposition 9.3's
  mixed-background purification iteration (ledger entry 37): a
  deadline-bounded profile at a positive global minimum purifies one
  coordinate per step, tying the minimum until every coordinate is a
  literal pure time or exiting off-minimum with an average-debt paid
  response; composed with the capstone, the boxed corollary
  `fable_deadlineBounded_minimum_offMinimum_paidPort` is checked at
  general finite \(\iota\): every deadline-bounded global minimum
  with positive debt yields a profile strictly above the minimum
  carrying a pure-time or Never response with gain at least that
  profile's average debt.  This subsumes the Fin 4 finite-clock
  corollary (8.1).

Against the export's suggested Lean handoff, the six declarations'
descent content is covered:
`pureTimeSingleton_cap_eq_nextCollision_or_never` and
`pureTimeSingleton_response_deadlineSupport_strict` by the entry 34
tables and support inclusion,
`pureTimeMinimum_anchorErase_or_deadlineDescent` by the entry 36
induction, `pureTimeMinimum_exists_offMinimumPaidPort` by the entry 36
capstone, and the two finite-clock declarations by entry 37's
iteration and composed corollary, all at general finite \(\iota\), so
the Fin 4 specialization is a numeral instance.  The §6
support-counterfactual extraction ((11)-(12)) and its composition
with the production first-disagreement decoder are kernel-checked
(`../fable/lean/FableSupportCounterfactual.lean`, ledger entry 38),
including the off-minimum capstone form carrying the row at the
average-debt floor.  Not yet checked from the export: statement-level
ancestry retention (the iteration constructs the replacement chain
without exporting it).

Verification: clean `lake env lean` compiles through the scratch olean
chain, lexical trust scans clean, and independent `#print axioms` runs
report only `propext, Classical.choice, Quot.sound` on every public
declaration. Scratch lane: nothing imports these files; production
integration pending.
