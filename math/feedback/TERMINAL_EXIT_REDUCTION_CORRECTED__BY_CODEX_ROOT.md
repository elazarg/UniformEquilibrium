# Review of `TERMINAL_EXIT_REDUCTION_CORRECTED`

## Verdict

The central reduction is mathematically sound and materially sharper than the
discarded exact-block argument.  In particular, the minimum-fibre flat-entry
arm really yields an interior stopping-law chord on which every debt coordinate
is affine, and hence a strict positive-debt-support expansion.  The note is
correct not to claim a terminal consumer.

This is suitable as an internal research reduction after the corrections
below.  It is not yet a completed answer to the terminal-exit question.

## Checked core

For a full-replacement cluster `c`, the retained coordinate inequalities and
the exact killed-mover identity imply

```text
D(c) - D_* >= sum_i t_mi.
```

Thus positive total slope forces every such cluster off the minimum fibre and,
in Fin4, forces a positive off-diagonal entry at least

```text
(sum_i t_mi + d_m(b)) / 3.
```

The `7/16` atom charge is the exact checked constant in
`PositiveTotalSlopeFullReplacement.lean` and
`PositiveTotalSlopeAtomAccess.lean`.

In the flat support-entry arm, if `D(c)=D_*`, the nonnegative coordinate
slacks sum to zero and therefore vanish coordinatewise.  Along any fixed
interior one-player stopping-law mixture, debt convexity gives the upper
chord bound.  Global minimality supplies the matching total lower bound, so
the coordinatewise convexity gaps again sum to zero and vanish.  Consequently
the old active coordinates remain positive, the inactive entrant becomes
positive, and

```text
support+(b) proper-subset support+(x_theta).
```

This argument uses the literal source/full-replacement pairs and does not
transport an arbitrary response across their horizontal seam.

The paid-row trichotomy is also stated at the right level: charged near-return
is consumed, quantitative debt descent is not well founded by itself, and the
inert arm remains unconsumed.  The later two-source maximal regeneration
theorem justifies the sharper double-unique-cap boundary when its Fin4 adapter
hypotheses are present.

## Required corrections

1. Section 5 calls formulations A and B “genuinely equivalent.”  No map in
   either direction is proved.  They are two alternative sufficient producer
   routes.  Replace “equivalent” by “sufficient” unless an equivalence theorem
   is supplied.

2. “Complete exact-minimum support-expansion source” is stronger than the
   argument written in Section 2.2.  The displayed proof gives a minimum
   semantic point realized by the literal mixture sequence.  If “source” means
   a complete `FinFourMinimumAtomProducer` with joint-law atom and causal
   chronology, add the joint compactification, positive finite-atom selection,
   source-faithful causalization, and tangent re-extraction.  Otherwise call it
   a source-faithful minimum semantic point/realizing sequence.

3. The display beginning `D(c)>D_*` in Section 3 is missing its closing display
   delimiter.

4. The sentence about exact-prefix absorption tending to zero is correct only
   in the explicitly stated two-active-debtor branch.  It should cite
   `QuittingStoppingLawAtomExactPrefixStackAccess.absorptionSum_tendsto_zero_of_twoActive`
   so it cannot be read as covering the singleton-active branch.

## Remaining boundary

The note exposes, rather than closes, the issue: support expansion and the
checked support drop can alternate without yielding a well-founded rank, while
the atom-access output lacks nested successor-compatible chronology.  Neither
finite recurrence of a support label nor repeated availability of a marked
suffix is an admissible payoff return.  A completion still needs a chronology
producer of type A, a seam-compatible recurrence compiler of type B, or an
independent consumer of the double-unique-cap inert state.
