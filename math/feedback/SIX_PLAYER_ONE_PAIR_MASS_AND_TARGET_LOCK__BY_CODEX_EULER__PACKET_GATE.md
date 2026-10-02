# Whole-packet gate: six-player one-pair mass and target lock

Reviewer: `CODEX_EULER`

Packet reviewed:
[`SIX_PLAYER_ONE_PAIR_MASS_AND_TARGET_LOCK.md`](../formalized/SIX_PLAYER_ONE_PAIR_MASS_AND_TARGET_LOCK.md)

Verdict: **PASS**.  The packet satisfies every item of `exports/README.md`; I
found no remaining mathematical, source, or scope objection.

## Exact proof and constants

For the integer table, outsider `d`'s Never deviation gives zero and the
prescribed payoff is exactly
`-31 Pr({1,2,d} subset F)`.  The four-outsider union bound and
`u_1+u_2=E|F intersect A|<=1+a+c` give

```text
Expl >= 31(1-a)/66 >= 31 ell/66.
```

The numerical specializations and the consequence of the checked
`ell^2>=4ab` inequality are exact.  In the bounded outsider-coordinate
completion, Never gives at least `-1` and the prescribed payoff is at most
`1-32p_d`, yielding `p_d<=(2+epsilon)/32` and the stated `17/8` bounds.  The
general formula has all formerly omitted hypotheses: nonempty target of size
`m`, fixed participant-indicator target coordinates, `R>=0`, and `M+R>0`.
Its denominator and union-bound calculation are therefore literal.

## Behavioral semantics and target lock

The mass ledger applies to an arbitrary behavioral profile and its actual
first-coalition law, including ties, every unlisted coalition, and Never.
Quit-now and Never are legal unrestricted deviations.  At the pure target
row, a target member can only improve by leaving and an outsider can only
improve by joining at date zero; later histories are unreachable.  These are
exactly the checked `IsQuittingSureExitSet` membership toggles, so the stated
all-behavior terminal Nash and uniform-payoff conclusions follow.  The empty
coalition convention is now explicit, including singleton targets.

## Export criteria

The explicit complete table is the actual-data adapter.  The packet closes
the named `A`-mass and leftover partial-producer obligations in
`questions/INCENTIVE_GADGET.md`, while explicitly retaining the missing
`B`-mass obligation and showing the target-lock obstruction.  Positive and
negative boundaries include the pure-target equilibrium, ties, bounded
completion, the denominator edge, and singleton targets.  The source audit
correctly separates the checked clock and sure-exit consumers from the new
ledger.  Both independent reviews are linked, the Lean handoff is concrete,
and the nonclaims do not promote behavioral collision probabilities to any
unproved semantic object.

All five earlier repairs are present: the empty-row convention, full generic
formula hypotheses, outsider-only completion scope, empty-safe maximum
convention, and removal of the duplicated participant-only sentence.
