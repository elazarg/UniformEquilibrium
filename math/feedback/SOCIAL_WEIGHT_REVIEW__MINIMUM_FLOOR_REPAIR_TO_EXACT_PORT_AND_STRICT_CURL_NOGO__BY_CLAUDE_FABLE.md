# The per-profile softening core is kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/SOCIAL_WEIGHT_REVIEW__MINIMUM_FLOOR_REPAIR_TO_EXACT_PORT_AND_STRICT_CURL_NOGO.md`

The per-profile core of the §3 unique-debtor repair is now checked by
Lean in the scratch lane at general finite \(\iota\), with production
imports only (`../fable/lean/FableFloorRepairSoftening.lean`; ledger
entry 43 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- the softened profile is the production
  `quittingStoppingLawMixtureBehaviorStrategy` (the complete
  stopping-law mixture, per the review's revision 1);
- the mover's payoff moves exactly affinely ((3.5)'s identity) and
  the mover's cap is exactly unchanged ((3.9), through the
  production own-update cap invariance);
- the uniform-over-deviations nonmover estimate the review's
  revision 2 requested is compiled: every behavioral deviation of a
  nonmover sees a payoff change of at most \(2M\theta\)
  ((3.7)), and the csSup transfer gives the cap bound ((3.8));
- every terminal outcome mass, Never included, is the exact convex
  mixture ((the law clause));
- a paid pure-time pair is retained verbatim, with the source
  witness in the support of the mover's original stopping law and
  cap optimality of the target preserved ((3.10)); and
- the punishment floor is packaged per profile, sequence-free
  (\(\theta=2f/a\) arrives as a hypothesis).

The sequence-level entrance is now also kernel-checked
(`../fable/lean/FableFloorRepairEntrance.lean`, ledger entry 46):
the §2 minimum inequalities (including the two-debtor strict moat
and the quantitative punishment margin), the note's clamped weights
with the (3.4) repair inequality, eventual all-player floors at the
softened profiles, retention of the incoming semantic packet in the
limit, and the eventually retained paid pair at gap at least half
the minimum debt sum.  The exact-port invocation is now compiled
too (`../fable/lean/FableFloorRepairExactPort.lean`, ledger entry
48): the floor-safe packaging at gain \(D_*/4\), the production
alternative restated verbatim, and the lifted case split — a
uniform-equilibrium payoff outright, or every late softened
entrance profile the literal paid suffix of a summable all-Continue
semantic port with positive paid-suffix reach.  The note is
compiled end to end at its stated boundary.

Verification: clean `lake env lean` compile, lexical trust scan
clean, and an independent `#print axioms` run reporting only
`propext, Classical.choice, Quot.sound` on all 17 declarations.
Scratch lane: nothing imports the file; production integration
pending.
