# The composition is kernel-checked in the scratch lane, at general ι

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/PAIRED_HULL_REVIEW__ZERO_SINGLETON_MINIMUM_TO_FINITE_CLOCK_PAID_PORT.md`

The §7 handoff is complete in the scratch lane. The §3 declaration
search found nothing because it looked at `UniformEquilibrium/` and
`Research/`; the three requested pieces were already kernel-checked
in `math/fable/lean/` (ledger entries 25, 27, 37–38 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

1. the closed-law product-root theorem
   (`fable_zeroNever_zeroSingleton_law_productBase`,
   `FableProductBaseLaw.lean`);
2. the strict positive-minimum root-then-Never semantic realization
   (`fable_zeroNever_zeroSingleton_semantic_productBase_realization`,
   `FableProductBaseRealization.lean`); and
3. the finite-clock minimum-to-paid-port descent at deadline-bounded
   generality (`fable_deadlineBounded_minimum_offMinimum_paidPort`
   and the first-disagreement row form, `FablePurificationDescent.lean`
   and `FableSupportCounterfactual.lean`) — the one-date-then-Never
   realization is deadline bounded at 0, so it enters directly.

The composite seam itself is now also kernel-checked
(`../fable/lean/FableZeroZeroLawSeam.lean`, ledger entry 44):
`fable_minimumJointLaw_zeroNever_zeroSingleton_exists_offMinimumPaidPort`
and the row form
`fable_minimumJointLaw_zeroNever_zeroSingleton_offMinimumPaidRow`, at
general finite \(\iota\) with `1 < Fintype.card ι` — stronger than the
note's Fin 4 statement. The hypotheses are the joint-carrier
membership, the two law conditions, and the global-minimum quadruple;
the conclusion exposes the exact realization (root, two sure
quitters, pair = z, law = μ) and the off-minimum paid port with gain
strictly above \(D_*/|\iota|\), plus the literal paid
first-disagreement row in the row form. This also serves §3 of
`PAIRED_HULL_REVIEW__RESET_RIGID_LAW_SUPPORT_CONTRACTION.md` (its
Output A in the zero/zero arm).

Per the note's §5, nothing claims the product root is a one-stage
cap-Nash root; per §6, the conclusion is the already open actual
off-minimum paid port, not a consumer of it.

Verification: clean compile through the scratch olean chain, lexical
trust scan clean, and an independent `#print axioms` run reporting
only `propext, Classical.choice, Quot.sound` on all 6 declarations.
Scratch lane: nothing imports these files; production integration
pending.
