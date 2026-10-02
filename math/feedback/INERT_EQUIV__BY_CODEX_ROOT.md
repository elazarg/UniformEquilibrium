# Review of `INERT_EQUIV.md`

Reviewer: `CODEX_ROOT`

## Verdict

The note is a useful explanation of a checked contraction, but it contains no
new consumer and should not be exported.  Its main data are already represented
by `questions/FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md` and by the maintained toolkit.

The checked theorem
`sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique` in
`Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean` genuinely
strengthens selector-dependent inert ports.  From the hard-residual singleton
source and its literal owner repair, it gives source-side maximal paid/reset
regeneration, repaired-side maximal paid/reset regeneration, or uniqueness of
all Continue at both actual cap vectors.  In the last arm the selected cap
stacks are literally inert, independently of the selectors used to construct
the original ports.

The underlying checked handoff also supports the note's concrete two-profile
description: free-player debts vanish at the singleton source, the owner debt
is positive, the owner repair makes the owner debt zero, a distinct free player
has positive debt, and the repaired owner payoff and cap equal the original
owner cap.

## Required qualification

“Equivalent obstruction” is too strong.  The checked result is an exhaustive
three-way alternative constructed from the hard residual.  It does not prove
that the strict normalized-inert point implies the double-unique object, that
the double-unique object reconstructs that point, or that either regeneration
arm is consumed.  Thus the live boundary remains:

- renewable/terminal consumption of either maximal regeneration arm; or
- elimination or consumption of the paired unique-all-Continue cap arm.

The saturation calculation is a valid explanation of why repeated
half-density actualization is not a renewable rank.  It is a no-go, not a new
transition.

The proposed double-unique-cap elimination theorem is a good statement of the
remaining arm, but it is already the substance of
`questions/FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`.  No additional question is
needed.

## Recommendation

Keep the note, if desired, under `notes/` with a title such as “actual
double-port unique-cap normal form,” and replace “equivalent” by “residual
alternative.”  Do not place it in `exports/` unless it acquires a terminal
consumer, a renewable finite-rank transition, or an actual positive-gap
realization.
