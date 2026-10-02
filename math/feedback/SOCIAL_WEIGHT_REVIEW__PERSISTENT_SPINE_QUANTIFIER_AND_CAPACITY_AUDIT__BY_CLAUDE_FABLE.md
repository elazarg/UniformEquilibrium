# Sections 2–3 are kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/SOCIAL_WEIGHT_REVIEW__PERSISTENT_SPINE_QUANTIFIER_AND_CAPACITY_AUDIT.md`

The quantifier bootstrap and the composed negation are now checked
by Lean in the scratch lane
(`../fable/lean/FableSpineCanonicityBootstrap.lean`; ledger entry 54
in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- §2's bootstrap, at general finite \(\iota\):
  `fableSpine_canonical_of_bounded_of_not_summable` — an exact
  Bellman/exact-Nash spine bounded by an arbitrary finite constant,
  with one nonsummable marginal, satisfies the canonical reward-cube
  bound (via the marginal-to-absorption comparison, joint-survival
  vanishing from every suffix start, and the production bounded
  transversality identifying the values with the root-schedule
  terminal values), hence is an
  `IsCanonicalExactQuittingNashBellmanSpine`; and
- §3's composition (5), at the production theorem's Fin 4
  generality:
  `finFour_all_marginalQuitHazards_summable_of_no_uniformPayoff_of_bounded_spine`
  and its persistence-facing restatement — without a
  uniform-equilibrium payoff, every bounded exact Nash–Bellman spine
  has every marginal summable.

This closes the note's "harmless arbitrary-bound wording gap" at the
Lean level. Not compiled: §§5–6 (the reversal/ballistic routing and
the surviving-question discussion are prose over already-recorded
material).

Verification: clean `lake env lean` compile on production imports,
lexical trust scan clean, and an independent `#print axioms` run
reporting only permitted axioms on all theorems. Scratch lane;
production integration pending.
