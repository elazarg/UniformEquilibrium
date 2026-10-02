# Independent falsification of Section 20

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md`](../notes/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md), Section 20.

## Claim checked

For a positive global-minimum carrier pair `X_*` and any debtor `e`, choose
two other players `b,c` as a sure base and solve the induced game on the
complement `{e,f}`.  The resulting complete-law target resets `e` and has
unit `(e,b)` opponent incidence.  Applying the checked fixed-law reset
dispatcher then yields either:

1. a positive-absorption, positive-survival exact cap root whose literal
   semantic prefix strictly contracts debt, together with the separate exact
   floor Bellman edge `R.2 -> Succ(R.2,q)`; or
2. an all-Continue cap self-loop at the returned reset point, retaining the
   complete law, transferred debt, positive incidence, and a supported strict
   toggle.

## Verdict

**PASS, with no repair.**  The pair-base target supplies every hypothesis of
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch`; the
semantic contraction and the payoff-only Bellman edge are correctly kept
distinct.  The current orientation `R.2 -> W` is the checked charged-relation
orientation.

## Pair-base target and unrestricted semantics

Literal `Fin 4` permits the choice of pairwise distinct `e,b,c,f`.  The
persistent-base Nash set for `base={b,c}`, `free={e,f}` is nonempty.  In its
ambient stationary profile both `b` and `c` Quit surely at date zero.
Consequently any unilateral behavioral deviation by either free player is
resolved at date zero: only that player's initial Quit/Continue mixture can
matter.  The induced two-player Nash inequalities are therefore the full
unrestricted best-response inequalities, not merely stationary-regret
bounds.  It follows that the actual target semantic pair `T` satisfies

```text
d_e(T)=d_f(T)=0,
```

and `(T,lambda)` lies in the complete terminal-semantic law carrier.

Every terminal realization under this profile contains both `b` and `c`,
and absorption occurs with probability one.  Since `b!=e`, expanding the
definition of displayed opponent incidence gives

```text
Incidence_(e,b)(lambda)
 = sum_{terminal containing b} lambda(terminal)
 = 1.
```

Thus the target provides the required positive incidence.  It also explains
why the later positive-mass terminal selected from the unchanged law is
nonsingleton: every positive `lambda` atom contains the sure pair `{b,c}`.

## Fixed-law dispatcher

The source `X_*` is a global debt minimizer with positive total debt, `e` is
a positive-debt coordinate, the pair-base target has `d_e(T)=0`, and the
complete law has positive `(e,b)` incidence.  These are exactly the hypotheses
of

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch.
```

Its returned structure gives, literally:

- `(R,lambda)` in the law carrier and `d_e(R)=0`;
- `D_*<=D(R)<=D(T)`;
- the displayed off-coordinate transfer inequality;
- a positive-law atom carrying `b` with a strict witness toggle; and
- the stated dynamic disjunction.

No extra normality, paid-row alignment, or attained-profile hypothesis is
silently used.  The target `T` is attained by the constructed stationary
profile; the reset minimizer `R` is the literal joint carrier point supplied
by the checked compact reset-face theorem and need not itself be represented
by one preselected behavioral profile.

## Dynamic arm and edge orientation

In the absorbing arm the checked dispatcher supplies an exact root `q`
against the **cap** tail `R.2`, positive absorption, positive joint Continue
mass, and

```text
R' = Prefix(q,R),       D(R')<D(R),       d_e(R')=0.
```

It also gives the prefixed complete law and positive retained incidence.
These are the semantic-prefix conclusions.

Separately, exact root Nash at `R.2` defines

```text
W = Succ(R.2,q).
```

Carrier caps are bounded by the reward box and dominate the behavioral
punishment floor.  The exact floor-successor inequality puts `W` above the
same floor, and the successor formula keeps it in the box.  Hence the literal
charged relation edge is

```text
R.2 -> W.
```

This is tail-to-prefixed-current orientation; behavioral execution reads the
row in reverse chronology, from current `W` to continuation `R.2`.

Crucially, the note does not identify `W` with `R'.2`.  The latter is the cap
of the semantic prefix and includes the cap-defect/envelope update, whereas
`W` is the prescribed successor computed at the old cap tail.  The checked
dispatcher couples them through the same root and tail but does not assert
equality.  This distinction is essential and is stated correctly.

In the other arm, the all-Continue root is exact at `R.2` and its semantic
prefix fixes `R`; all law, incidence, transfer, and toggle fields remain
attached to that same returned point exactly as claimed.

## Novelty and maintained-boundary assessment

Most of the dynamic mathematics is already contained in the checked
`exists_fixedLawResetDispatch`.  Section 20's genuine adapter is the
source-native pair-base construction: for **any** selected positive minimum
debtor it manufactures a complete-law zero-debt target with unit incidence,
so the checked dispatcher applies without label alignment to an earlier paid
atom.  This does narrow the maintained reset-conversion boundary to the
explicit all-Continue fixed-law wall (or the already supplied contraction
arm).

It does not yet close the paid-near-return problem.  In arm 1 the exact floor
edge `R.2 -> W` is not a Bellman edge between the semantic states `R` and
`R'`, and strict contraction from `D(R)>D_*` need not be a decrease below the
global minimum or a well-founded iteration.  In arm 2 the debt transfer may
create new positive coordinates, and the retained toggle/incidence has no
chronological compiler.  I therefore recommend keeping Section 20 internal
until one of these two interfaces is consumed; it is a valid and substantive
reduction, but not by itself an export-quality paid producer.
