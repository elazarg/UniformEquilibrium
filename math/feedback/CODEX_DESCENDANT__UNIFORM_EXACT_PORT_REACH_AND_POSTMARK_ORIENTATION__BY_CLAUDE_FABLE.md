# Sections 2–3 are kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/CODEX_DESCENDANT__UNIFORM_EXACT_PORT_REACH_AND_POSTMARK_ORIENTATION.md`

The quantitative core (§§2–3), in the scope confirmed by the
SOCIAL_WEIGHT_REVIEW review, is now checked by Lean in the scratch
lane at general finite \(\iota\), with production imports only
(`../fable/lean/FableUniformWordSurvival.lean`; ledger entry 42 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- the charge-to-log conversion \(-\log c\le(1-c)/r\) on \([r,1]\);
- the one-root Continue-product floor
  \(r=(\gamma/4M)^{|\iota|}\), through the production margin
  `terminalGap_div_four_mul_le_exactFloorRoot_continueProbability`,
  with reward-bound positivity derived from the terminal gap;
- the table-uniform floor
  `fableUniformSurvivalFloor_le_prefixContinueProduct`: every
  compatible `QuittingPunishmentFloorFinitePrefix` certificate, of
  every depth, keeps joint Continue product at least
  \(\lambda=e^{-C/r}\) with
  \(C=\) `quittingPunishmentFloorPrefixChargeBound`; and
- the joint-survival-weight alignment.

The review's quantifier discipline is enforced in the statements:
the floor quantifies only over prefix certificates, never arbitrary
root words. The §4 composition with the actual-reach paid row is now
also kernel-checked
(`../fable/lean/FableShiftedRowComposition.lean`, ledger entry 47):
the outward word-prefix constructor, the (4.3)–(4.4) factorizations
with the uniform floor \(\lambda\), the one-equation compatibility
interface with derived later-stage agreement, the (4.5) debt
sandwich, and the composed packet (shifted row of gain
\(\lambda\Delta/4\), joint entry floor
\(\lambda\Delta^2/(32M^2)\)). The §4.1 fork lift is compiled too
(`../fable/lean/FableForkLift.lean`, ledger entry 49): the exact
payoff cancellation, the update-form lifted-strategy identity, and
the composed lifted fork behind any compatible certificate at the
fork's constants scaled by the uniform floor.  Not compiled:
anything in §§5–6 (whose Never-mass sentence the review rejects).
The note's review-confirmed scope (§§2–4 with 4.1) is compiled end
to end.

Verification: clean `lake env lean` compile, lexical trust scan
clean, and an independent `#print axioms` run reporting only
`propext, Classical.choice, Quot.sound` on all 13 declarations.
Scratch lane: nothing imports the file; production integration
pending.
