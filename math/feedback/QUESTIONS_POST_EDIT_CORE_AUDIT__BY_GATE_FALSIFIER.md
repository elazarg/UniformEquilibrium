# Post-edit audit of the core Fin4 questions

Author: `CODEX_GATE_FALSIFIER`

## Verdict

**REVISE.  No P1 mathematical error remains.  Three P2 specification or
roadmap errors remain.**

The two top-level terminal components are now stated accurately, the uniform
escape maximal-root dispatch is not overclaimed as a consumer, the canonical
support descent is correctly marked conditional, the five equality-decoder
outputs are present, and the paid/reset charge-collapse no-go is correctly
scoped to sources whose initial debts tend to \(D_*\).

## P2-1: the roadmap puts the independent paid/reset fork “inside” the two
terminal components

`questions/README.md` says that every item in its long focused list is
“inside” uniform escape or minimum return.  This is not the proved provenance
of

- `FIN4_PAID_RESET_REGENERATION_RANK.md`;
- `FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`; and
- their parent `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.

Those objects come from the independent hard-residual paid/reset double-port
construction.  They are parallel direct consumers of a hypothetical hard
residual, not checked descendants of either terminal component of the
source-preserving completion atlas.  Counting them as extra atlas components
would also be wrong, but calling them “inside” the two components asserts a
source attachment which has not been proved.

Required repair: split that list into:

1. focused questions genuinely downstream of uniform escape or minimum
   return; and
2. a parallel hard-residual paid/reset fork, with its regeneration and paired
   unique-cap children.

The parent fork remains a useful question; only its placement is wrong.

## P2-2: the minimum-return notation and supplied reductions are not fully
self-contained

`FIN4_MINIMUM_RETURN_CAPSTONE.md` says “write \(U_i(\sigma),B_i(\sigma)\)” but
does not define either quantity.  The uniform-escape question now gives the
correct self-contained definitions; the minimum-return question should repeat
them.

More importantly, the displayed eight hypotheses do not literally contain
all the source fields used by every theorem in “Supplied conditional
reductions.”  The actual normalized decoder and canonical support/ray
dispatch are indexed by the complete minimum-atom/hard-residual source, not by
an arbitrary profile family satisfying only the bullets shown in the file.

Required repair: do one of the following.

- Add the complete quantitative hard-residual/minimum-source provenance to
  the mathematical data; or
- state the two conditional dispatches themselves as additional supplied
  hypotheses on the displayed chronology.

The latter is shorter and keeps the question in ordinary mathematics.  It
must be clear that the dispatches are part of the input, not claimed to follow
from the reduced bullet list alone.

## P2-3: the direct hard residual is named but not mathematically specified

`FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md` refers to “full-support singleton
separation,” “recursive normality,” and “punishment normality” without
defining their inequalities or quantifiers.  A reference to the generated
frontier documents does not make an ordinary-mathematics question
self-contained.  The phrase “resulting quantitative hard residual” also
suggests the full checked residual while listing only a partial informal
summary of its fields.

Required repair: either

1. remove the hard-residual summary entirely and pose the direct question
   simply as impossibility of a fixed positive all-behavior exploitability
   gap for a four-player table; or
2. state the exact quantitative residual hypotheses in ordinary mathematical
   notation.

The first option is preferable for this deliberately open-ended shortcut.
The positive-gap premise already makes the desired theorem exact, and the
hard-residual reductions can be cited as available consequences rather than
left as undefined assumptions.

## Files passing as edited

Subject to the roadmap placement in P2-1,
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` passes.  Its selector-independent fork,
nonexclusive regeneration arms, source-renewal requirement, scoped
near-minimum no-go, and exact punishment-floor near-return target match the
checked sources.

`FIN4_UNIFORM_ESCAPE_CAPSTONE.md` passes.  It is self-contained, makes the
actual chronology and fixed quantitative floors explicit, and accurately
treats the maximal-root result as a supplied unconsumed dispatch.

