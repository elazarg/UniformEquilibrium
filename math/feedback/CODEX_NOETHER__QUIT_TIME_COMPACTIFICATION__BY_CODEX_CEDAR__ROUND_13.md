# Round 13 Feedback on Quit-Time Compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: only Section 49, the source-scope question following Propositions
43--45. This is a bounded consumer audit, not another review of the Simon
orbit construction.

Status: `HARMED_PLAYER_UNUSED; POSITIVE_SOLO_STILL_ESSENTIAL; NO_UNIFORM_SHORTCUT_VACUOUS`.

## Consumer fields actually used

The proof ledger of Proposition 43 does not use normality or
`EveryNormalSoloQuitterHarmsNormal`. Its only clause-(1) datum is one player
with strictly positive own singleton payoff. That datum enters
`exists_tailSurvival_lt_of_equilibrium_positiveSolo`
(`Literature/Simon2007.lean`), whose assumptions literally require
`0<SoloPayoff G n` and do not require `IsNormalPlayer` or a harmed-player
relation. The subsequent survival-jump, logarithmic-charge, purification, and
large-path calls use the quantitative `rho`, no-sure scale, and equilibrium
profile, not the harmed-player clause.

Thus the harmed-player half of corrected Lemma 2.1 is not consumed by this
necessity chain. This is a valid source-scope reduction.

## Why the proposed positive-solo shortcut is vacuous

The zero-solo implication is exact:
`exists_uniformEquilibriumPayoff_of_zeroSolo`
(`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`) proves that
if every own singleton reward is nonpositive, the zero vector is a uniform-
equilibrium payoff. Hence failure of uniform-payoff existence implies a
positive singleton reward.

But Section 49's proposed shortcut adds failure of uniform-payoff existence
to the premise

```text
terminal approximate Nash profiles exist at every positive error.
```

Those two statements are inconsistent by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`),
with the behavior adapter named in the note. The resulting implication to
`CyclicOrbitCondition` is therefore formally true but vacuous. It cannot
replace the positive-solo source in the nonvacuous theorem

```text
terminal approximate Nash at every error ==> CyclicOrbitCondition.
```

In particular, one cannot reason inside the antecedent of that implication
by additionally assuming no uniform payoff: the antecedent already supplies
one through the checked equivalence.

## Verdict

Section 49's current corrected label `Failed Proposition 46` is accurate.
For conjecture-facing necessity, the historical sign clause can be narrowed
from

```text
positive normal solo + harmed-normal relation
```

to

```text
one positive solo payoff,
```

but that last positive-solo input remains essential unless a different
nonvacuous survival-crossing argument is supplied. The zero-solo production
disjunct does not supply it under the theorem's meaningful quantifiers.
