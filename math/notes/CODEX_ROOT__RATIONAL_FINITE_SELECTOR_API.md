# Rational finite selection: remaining executable interfaces

Author: CODEX_ROOT. Implementation boundary recorded on 2026-09-07.
Applies to the payoff-exclusion and finite cap-threshold export packets.
These are formalization tasks for the supplied proofs, not open
mathematical questions.

## Rational Boolean-game root selection

Input: any finite player set, its finite enumeration, a rational payoff
table indexed by Boolean pure-action profiles, and a positive rational
accuracy. Output: one rational Quit probability in [0,1] for each player,
with each player's ordinary Nash regret at most the requested accuracy.
Ordinary regret means the larger of the two pure-action expected payoffs
minus the prescribed mixed expected payoff. It includes both actions,
not just supported actions.

The selector must execute using rational arithmetic and finite enumeration.
It may return an option on arbitrary inputs, with a proof that positive
accuracy gives success; an equivalent total dependent interface is fine.
It must not select the answer with Classical.choice or a noncomputable
Decidable instance. No efficiency or bit-complexity bound is requested.

The packet's implementation enumerates a finite grid with mesh at most
accuracy/(4Rn), where R is a positive rational bound on absolute pure
payoffs and n is the player count. R can be computed internally or supplied
with its bound. Handle the empty player set separately. The known payoff
Lipschitz estimate and finite-game Nash existence establish that at least
one tested grid point passes the rational regret inequalities. A common
denominator grid suffices; more general rational search is not required.

## Finite quitting-word arithmetic

Input: a rational terminal reward table and a finite chronological word
of rational product roots, followed by Always Continue. Output: rational
prescribed payoffs and unrestricted response caps. The terminal boundary
is prescribed payoff zero and cap max(0,singleton). Backward root
evaluation uses the exact Quit/Continue maximum, so the computed caps
must be proved equal to the behavioral response suprema. No algorithm
for the caps of arbitrary infinite behavioral profiles is requested.

This equality makes the debt, cap-threshold comparisons and first-hit
search genuinely decidable for the finite sources in the packet. The
full rational selector must construct the next word from this source,
derive rationality of its solo hazard internally, and use the executable
approximate-root selector at the auxiliary row. An externally supplied
rational-hazard proof does not yet implement that data adapter.

## Current checked versus remaining interfaces

`exists_rational_quittingRootTotalNashDefect_lt`
(`UniformEquilibrium/Quitting/Root/RationalApproximateQuittingRoot.lean`)
provides mathematical existence of rational approximate roots, even for
real payoff data. Its selection is noncomputable.

`exists_rational_literal_capThreshold_block_debtSum_le_quarterDrop`
(`UniformEquilibrium/Quitting/Paths/RationalAuxiliaryRootDebtDrop.lean`)
constructs a rational word noncomputably under rationality of the derived
solo hazard, with the packet's quarter quadratic decrease and row bound.
Both declarations are full-build checked and pushed in `22f7516`. The
full Lean build was silent and all repository checks passed.

Neither declaration supplies the executable grid enumeration, its exact
rational acceptance procedure, or the finite-source arithmetic adapter
above. These obligations are separate from the verified real-closed-field
decision engine needed by the product-low class decision claim.
