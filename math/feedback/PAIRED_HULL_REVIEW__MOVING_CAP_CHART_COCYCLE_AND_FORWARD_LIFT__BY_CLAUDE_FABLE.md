# Sections 2–5 and 7 are kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/PAIRED_HULL_REVIEW__MOVING_CAP_CHART_COCYCLE_AND_FORWARD_LIFT.md`

The cocycle and the conditional lift are now checked by Lean in the
scratch lane at general finite \(\iota\), with production imports
only (`../fable/lean/FableMovingCapChart.lean`; ledger entry 52 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- (2.1)–(2.2) and (2.4) as thin alignments of the named production
  identities;
- the chain structure (actual sources, exact cap-Nash roots, literal
  one-player replacements of the prefixed profiles), the chart, and
  the exact cocycle (3.3) with its unfolded (3.4) prefix-sum form;
- the §4 support transport
  (`isQuittingRootSupportApproxNash_of_tail_close` at the exact
  root), the compact chart carrier;
- Theorem 5.1 (`QuittingMovingCapChain.toForwardPacket` and
  `nonempty_forwardPacket`): uniform chart error \(\le\varepsilon\)
  plus cumulative exact-root absorption \(\ge A\) instantiate the
  production `QuittingFiniteForwardPacket`; the §7 two-row form; and
- Corollary 5.2
  (`quittingGame_exists_uniformEquilibriumPayoff_of_movingCapChains`),
  composed with the production finite-forward-packet compiler.

The uniform every-prefix smallness hypothesis (6.1) is carried, not
discharged, matching the note's status line. Not compiled: §§8–10
(the regression is the fork-seam note's table; the obstruction
discussion is prose).

Verification: clean `lake env lean` compile, lexical trust scan
clean, and an independent `#print axioms` run reporting only
`propext, Classical.choice, Quot.sound` on all 33 named
declarations; the delegated build additionally swept all 65 local
constants (auto-generated names included) with `Lean.collectAxioms`,
with the same result. Scratch lane: nothing imports the file;
production integration pending.
