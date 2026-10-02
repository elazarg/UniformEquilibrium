# Handoff items 2–3 are already kernel-checked; item 4 in progress

Reviewer/contributor: CLAUDE_FABLE
Re: `../formalized/FIN4_DEBT_RATIO_CHAMBER_CONTRACTION.md`

Lifecycle note: the complete result is now checked in production Lean. This
file records the earlier scratch-lane handoff state and is not a current
formalization-status report.

Against the export's five-item Lean handoff, the scratch lane already
carries (ledger entries 51 and 53 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- item 2, Theorem A: `fableDebtMinima_add_lt_debtSum` and
  `fableDebtMinima_sqrt_separation`
  (`../fable/lean/FableDebtMinimaSeparation.lean`), stated with the
  certificate in per-profile hypothesis form
  (`FableCertifiedExploitabilityFloor`); the alignment to the
  production `quittingTerminalExploitabilityInf` is a thin bridge
  (`fableThinSlice_exists_debt_ge_of_exploitability` covers the
  per-pair half);
- item 3, Theorem B: `fableDebtPort_debtSum_le_of_exact` and
  `..._of_exact_ratio`, with the attainment hypothesis explicit and
  a general residual-debt form carrying the response debt as a free
  real (so approximate responses specialize); and
- item 1, partially: the mover chord identity and nonmover chord
  bounds are consumed from the production
  `TerminalSemanticStoppingLawDebtConvexity` module; the
  \(2M\theta\)/\(4M\theta\) packaging at a general (non-pure-time)
  target exists in pieces (entry 43's uniform bounds are pure-time
  targeted; the convexity module plus the 2M debt bound covered the
  §9 proof without a standalone lemma).

The export's source-correspondence remark that the scratch
thin-slice theorem "does not subsume these statements" is right for
entry 51 but predates entry 53, which contains (A) per profile and
(B) exactly.

Items 4 (Theorem C, the liminf carrier/actual-source packaging) and
5 (the Fin4 two-stage adapter) are not yet compiled; a formalization
is in progress in this lane.

Verification status of the cited entries: clean compiles, lexical
scans, and independent `#print axioms` runs on all declarations,
only permitted axioms. Scratch lane; production integration pending.
