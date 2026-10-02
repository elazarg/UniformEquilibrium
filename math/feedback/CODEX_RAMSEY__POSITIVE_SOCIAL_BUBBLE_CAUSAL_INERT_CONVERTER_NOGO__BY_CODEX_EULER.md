# Independent review: positive-social bubble causal-inert converter no-go

Reviewer: CODEX_EULER

Date: 2026-08-26

Note reviewed:
[CODEX_RAMSEY__POSITIVE_SOCIAL_BUBBLE_CAUSAL_INERT_CONVERTER_NOGO.md](../notes/CODEX_RAMSEY__POSITIVE_SOCIAL_BUBBLE_CAUSAL_INERT_CONVERTER_NOGO.md)

## Verdict

**REVISE for one literal cap-enumeration sentence; mathematical theorem PASS
after that bounded repair.**

The complete Fin4 table, unrestricted caps, weak-law bubble, unit paid row,
unique all-Continue cap root, floor safety, arbitrary-depth inert prefixing,
and zero-minimum scope all check.  The required edit is in Section 3:

> For players 0,1, every finite Quit time gives -1 ...

is false literally, since a planned finite time \(t>n\) is preempted by the
other base player's exit at \(n\) and pays \(0\).  Replace the sentence by:

> For players 0,1, quitting at a date \(t\le n\) gives \(-1\), while every
> date \(t>n\), as well as Never, is preempted by the other base player's
> exit at \(n\) and gives \(0\).

This is already the case distinction used by the displayed cap \(B_i=0\);
it changes no formula or conclusion.

## 1. Reward and semantic enumeration

For \(i\in\{0,1,3\}\), quitting in the terminal coalition always gives that
player \(-1\), while being absent gives \(0\).  At \(\sigma_n\), players
\(0,1\) quit together at \(n\), so the terminal coalition is exactly
\(A=\{0,1\}\) and

\[
U(\sigma_n)=(-1,-1,4,0).
\]

The unrestricted cap calculations are exact:

- for \(i=0,1\), dates \(t\le n\) pay \(-1\), while \(t>n\) and Never pay
  \(0\);
- for player \(3\), dates \(t\le n\) pay \(-1\), while later dates and Never
  pay \(0\);
- for player \(2\), dates \(t<n\) pay \(-1\), date \(n\) pays \(5\), and
  dates \(t>n\) or Never pay \(4\).

Thus \(B=(0,0,5,0)\) and \(d=(1,1,1,0)\).  The declaration
sSup_range_quittingTerminalPayoff_update_eq_pureTime in
UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean upgrades
this exhaustive pure-time list, including Never, to arbitrary behavioral
deviations.  No stationary-only inference occurs.

## 2. Bubble and paid-row provenance

The two moving clocks are \(\delta_n\), hence converge to Never in the
one-point compactification of \(\mathbb N\).  The other two clocks are already
Never.  Nevertheless the terminal coalition law is \(\delta_A\) for every
\(n\), whereas the limiting all-Never profile has no finite terminal
coalition.  Therefore the escaped bubble satisfies \(e(A)=1\).

The aggregate reward is

\[
\sum_i r_i(A)=-1-1+4+0=2.
\]

At the same literal source, player \(2\)'s Never witness pays \(4\) and its
date-\(n\) witness pays \(5\).  No player exits before \(n\), so all survival
factors to the disagreement date equal one, and the receiving event is
literally \(A\cup\{2\}\) with probability one.  The paid-row gain and full
reach are both exactly one.

## 3. Unique root and inert prefixes

At cap tail \(V=(0,0,5,0)\), Quit gives \(-1\) to each of players \(0,1,3\)
regardless of the other current actions.  Continue gives \(0\), either from
absence in the current coalition or from the tail.  Hence Continue strictly
dominates Quit for these three players.

Once they Continue, player \(2\) compares singleton Quit \(-1\) with
continuation \(5\), so it also strictly Continues.  This proves that the
all-Continue product root is unique, including against mixed product roots.

The floor claim is also sound.  For every player, opponents can select a
pure row whose unilateral cap is at most \(0\); hence the punishment value,
which is the infimum over opponent plans of unrestricted best replies, is at
most \(0\).  Every coordinate of \(V\) is nonnegative.

Since the only exact cap root is all Continue, every iterated cap prefix has
zero absorption and leaves \(U,B,d\), and positive-debt support unchanged.
The terminal atom and the paid disagreement row are merely shifted one date
outward at each prefix.  This supplies arbitrary finite prefix depth but no
positive charge or descent.

## 4. Boundary and significance

At the limiting all-Never profile every cap and prescribed payoff coordinate
is \(0\), so its debt is zero and it is already an unrestricted equilibrium.
The disappearing cap sum is \(5\), while the escaped social reward is \(2\);
therefore

\[
0-3=2-5.
\]

The example consequently refutes the stated **local converter class**:
positive retained atom mass, positive aggregate bubble reward, a same-source
full-reach paid row, and arbitrary-depth exact inert cap prefixes do not by
themselves force charge or debt-support descent.

It does not satisfy \(D_*>0\), a terminal exploitability witness, or the full
Fin4 hard residual.  It neither supplies a counterexample nor obstructs a
converter that genuinely uses positive-minimum provenance.  This precise
scope is stated correctly.  The result is useful as an internal architecture
no-go, but it does not meet the conjecture-facing export significance gate.

