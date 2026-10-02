# Independent falsification of Section 21

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md`](../notes/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md), Section 21.

## Claim checked

Corollary 21.1 composes the source-native wall dispatch of Cedar Proposition
9 with the pair-base stationary handoff of Theorem 19.1.  It claims that the
zero-drop blocker gate has only two remaining output types:

1. a finite literal exact semantic prefix ending in a positive-charge strict
   total-debt contraction; or
2. a same-table attained stationary source with two unrestrictedly solved
   coordinates, debt on at most the complementary two labels, a fixed
   positive-mass nonsingleton terminal atom with a strict witness toggle, and
   a source-matched paid row for a debtor of size at least `Gamma`.

## Verdict

**REVISE, then PASS after two bounded statement repairs.**  The mathematical
composition is correct and exhaustive.  Before export, the corollary must:

1. explicitly quantify `M>=0` and assume
   `|reward(A)_h|<=M`, since both handoff constructors and the atom constant
   `Gamma/[3*(Gamma+2M)]` use that bound; and
2. replace “actual zero-drop carrier gate,” “actual carrier pair `W`,” and
   “actual ... semantic carrier pair” in the descent arm by **literal carrier
   gate/pair/prefix**.  Proposition 5 produces a compact carrier point, not
   necessarily the semantic pair of one attained behavioral profile.  The
   stationary source in arm 2 is genuinely attained and may continue to be
   called actual.

These repairs change no mathematical output or constant.

## Composition and constants

Apply the independently reviewed Cedar Proposition 9, after its literal
carrier/edge/index repairs.  Its debt arm is exactly a finite sequence of
semantic prefixes followed by an exact root `z` at the continuation payoff
`W.1`, with

```text
A(z)>=omega>0,
D(Prefix(z,W))<=D(W)-omega*D(W).
```

This is genuine chronological semantic contraction: the checked Bellman
relation edge is `W.1 -> Prefix(z,W).1`, while behavioral execution reads the
same prefix in reverse.

The stationary-handoff output of Proposition 9 is already the checked
`FinFourLeaveJoinStationaryTwoDebtorHandoff` on the same reward table,
witness, gap, and bound `M`.

In the remaining output, Proposition 9 gives distinct `k,i,j` with

```text
r_{ki}(j)+Gamma<=r_{kij}(j).
```

Literal `Fin 4` supplies the unique fourth label `o`.  Theorem 19.1 applies
with sure base `{k,i}` and free set `{j,o}`.  Its denominator is positive:
the reward bound and the displayed join imply `Gamma<=2M`, so

```text
alpha=Gamma/(Gamma+2M)>0.
```

The free-player absorption is at least `alpha`, and its three triple/grand
atoms sum to that amount; hence one has mass at least

```text
alpha/3=Gamma/[3*(Gamma+2M)].
```

No constant or gap is reselected.

## Unrestricted semantics and summarized handoff fields

For the pair-base handoff, two sure base quitters make every deviation by the
two free players terminate at date zero.  Their induced Nash conditions are
therefore their full behavioral best-response conditions.  They have zero
debt and lie above punishment; all positive debt is on the sure base.  The
terminal witness localizes a debtor in that base with debt at least `Gamma`
and the pure-time decoder gives the source-matched paid row.

For the singleton-base handoff, the checked structure stores:

- distinct solved leaver/joiner coordinates, each with zero debt and above
  punishment;
- positive debt support contained in `{spectator,fourth}`;
- a debtor in that pair with debt at least `Gamma` and a literal paid row;
- a pair or triple atom of mass at least
  `Gamma/[2*(Gamma+2M)]`.

The heavy atom is nonsingleton.  Applying the same terminal witness's
`terminalCoalition_has_strictToggle` to that selected atom supplies the strict
reward toggle summarized in `(21.2)`.  Thus the shorthand fields are all
justified; the proof should mention this last one-line witness application
when expanded for export.

## Chronology and exact scope

The provenance split in Section 21.2 is correct.  The descent arm is reached
through literal exact carrier prefixes.  The triple-join arm is consumed by
**same-table reselection** of an induced stationary Nash point; no Bellman path
from the terminating wall to that stationary source is claimed.  The terminal
law atom is not identified with Bellman absorption.

The corollary does not iterate the debt decrease through a support change,
produce a floor connector from the stationary source, or yield a payoff
near-return or uniform equilibrium.  After the two repairs, however, it is a
clean export-qualified Fin4 partial reduction: it removes both the static
triple-join chamber and the all-Continue/changed-solo selection chamber from
the zero-drop blocker branch, leaving only literal strict semantic descent or
the common actual stationary two-debtor paid-source interface.
