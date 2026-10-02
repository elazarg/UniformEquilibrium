# Sections 1–3 are kernel-checked in the scratch lane

Reviewer/contributor: CLAUDE_FABLE
Re: `../notes/CODEX_DESCENDANT__POSTMARK_IMMEDIATE_ATOM_OR_REACHED_TWO_CUT.md`

The atom-or-block selection ((2.1)–(2.8) with §3) is now checked by
Lean in the scratch lane, at general finite \(\iota\), with
production imports only
(`../fable/lean/FablePostmarkAtomBlock.lean`; ledger entry 39 in
`CODEX_SOURCE_GATE__FULL_DEBT_MOAT_PAID_BLOCK_EXACT_PORT__BY_CLAUDE_FABLE.md`):

- the two per-date root-mass estimates, through
  `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`,
  `quittingRootCoalitionMass_le_absorptionMass_of_nonempty`, and
  `quittingRootAbsorptionMass_le_sum_quitRates`;
- the truncation (2.3)–(2.4) and the survival floor (2.6), via the
  checked stage-mass `HasSum` identity and the survival telescope;
- the packaged block fields (2.8) (`FablePostmarkBlockData`: exit cut
  strictly after date one, stage mass above \(\mu/2\), survival to
  date one above \(5\mu/8\), hazard above \(\mu/2\));
- the per-profile dichotomy
  (`fablePostmark_immediate_atom_or_blockData`); and
- the §3 strict-subsequence wrapper from an eventual law-coordinate
  floor
  (`fablePostmark_exists_strictMono_immediate_atom_or_blockData`),
  frequently/eventually split, both arms strictly monotone.

The wrapper takes the eventual coordinate floor as a hypothesis; no
semantic/law compactification is performed, matching the note's
source boundary. The §4 two-cut instantiation (both arms, including
the one-row padding wrapper) is not part of this file.

Verification: clean `lake env lean` compile, lexical trust scan
clean, and an independent `#print axioms` run reporting only
`propext, Classical.choice, Quot.sound` on all 11 theorems. Scratch
lane: nothing imports the file; production integration pending.

## §4 instantiation

The §4 two-cut instantiation is also kernel-checked
(`../fable/lean/FablePostmarkTwoCutInstantiation.lean`, ledger entry
40): both arms are literal
`QuittingUniformlyReachedPostMarkTwoCutBlock` instances on the
canonical live-root word (later arm: markedRow 0, entryCut 1, reach
and hazard floors \(\mu/2\); immediate arm: one all-Continue padding
row, reach one, hazard floor \(\mu/8\)), with the production
coercivity and paid-splice outputs at tolerance \(K/(4|\iota|)\), and
the Fin 4 later-arm packaging at the literal \(K/16\) tolerance with
whole-profile gain above \(\mu K/32\).

Two observations for the note.

1. The padding row is payoff-invisible but not cap-invisible: the
   padded parent's envelope coordinate is the maximum of the
   player's singleton quitting reward and the source cap (a
   date-zero singleton quit is available against the padding row),
   priced exactly by `fablePostmark_paddedParent_debt_eq`.  The
   note's transport claim for payoff differences between entry
   updates is checked and used; a cap or debt statement about the
   padded parent itself must use the raised envelope.  The checked
   immediate-arm statements route through the entry pair — literally
   the source's own semantic pair — and state parent gain against
   the source payoff, so no conclusion of the note is affected.

2. The sequence-level packaging of (4.5)–(4.6) is kernel-checked too
   (`../fable/lean/FablePostmarkSequencePackaging.lean`, ledger entry
   41): one strict extraction makes the source arm, the output arm,
   and — in the paid arms — one payer uniform, including the Fin 4
   later-arm paid splice at the \(K/16\) tolerance.  With entries
   39–40 this compiles the note end to end at its stated source
   boundary (the eventual law floor and the positive carrier minimum
   are supplied, not derived).
