# Fin4 pair-base data do not produce the same-profile spare cancellation

**Author:** `CODEX_RAMSEY`  
**Status (2026-08-25):** proved ordinary mathematics; independent review
requested.  This is a producer-side screen for
[`CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION.md`](CHATGPT_EXTERNAL__SAME_PROFILE_SPARE_PLAYER_CANCELLATION.md),
not a review or restatement of that supplied verifier.

## 1. Question and checked inputs

The supplied five-player verifier starts with two sure base quitters

\[
B=\{b_0,b_1\},
\]

two free players `F={f_0,f_1}`, and a fifth spare `s`.  Its open producer asks
for

\[
\Phi_{p_f}(\Delta_f^1)=0\quad(f\in F)                 \tag{1.1}
\]

at the endpoint where `s` Quits surely, and for

\[
q_*\kappa\le D_0.                                    \tag{1.2}
\]

Here `D_0` is the two-base debt at the endpoint where `s` Continues,
`q_*` is the larger base-cancellation threshold, and
`kappa=C_s-Q_s`.

I inspected the following checked declarations.

* `FinFourPairBaseStationaryDebtLocalization` and
  `nonempty_finFourPairBaseStationaryDebtLocalization` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryDebtLocalization.lean`;
* `FinFourPairBaseStationaryTwoDebtorHandoff` and
  `nonempty_finFourPairBaseStationaryTwoDebtorHandoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryTwoDebtorHandoff.lean`;
* `FinFourLeaveJoinStationaryTwoDebtorHandoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`;
* `quittingPersistentBaseRoot_free_purePayoff_le` and
  `isNash_of_mem_quittingPersistentBaseNashSet` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
* `isBinaryDifferenceNash_of_mem_quittingPersistentBaseNashSet_pair` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargePersistentBaseDeletionAdapter.lean`.

The relevant actual pair-base source has two base players Quit surely and an
exact induced Nash point for its two free players.  The checked handoff says
that the two free coordinates realize their unrestricted behavioral caps and
meet their punishment floors.  Positive debt is nonempty and supported on
the base, but it is only asserted to have cardinality at most two.  Thus the
supplied verifier's stronger assumption that **both** base players have
positive debt is itself an additional subbranch assumption.

## 2. What is produced: exactly the original endpoint

For a free player with prescribed Quit probability `p`, write
`Delta=Q-C`.  Immediate absorption gives

\[
\max\{Q,C\}-\bigl(pQ+(1-p)C\bigr)
=(1-p)(\Delta)_+ +p(-\Delta)_+
=\Phi_p(\Delta).                                      \tag{2.1}
\]

Consequently the checked `free_solved` (equivalently `joiner_solved` and
`fourth_solved`) fields imply

\[
\Phi_{p_f}(\Delta_f^0)=0                              \tag{2.2}
\]

for both free players at the original Fin4 source.  This is also the direct
semantic content of `point_mem` through
`quittingPersistentBaseRoot_free_purePayoff_le`.

The zero condition has the exact boundary interpretation

\[
\Phi_p(t)=0\iff
\begin{cases}
t\le0,&p=0,\\
t=0,&0<p<1,\\
t\ge0,&p=1.
\end{cases}                                           \tag{2.3}
\]

No checked field cited above mentions a fifth label or a terminal coalition
containing it.  Hence none supplies (1.1).

## 3. Exact extension-freedom lemma

Let an arbitrary Fin4 reward table and an arbitrary product row with both
members of `B` surely Quitting be fixed.  Add a fifth label `s`, preserving
every old-player payoff on every terminal coalition not containing `s`.

For every old player `i`, choose arbitrary real numbers
`Qbar_i,Cbar_i`.  On a terminal coalition `T` containing `s`, define only
player `i`'s coordinate by

\[
r'_i(T)=
\begin{cases}
\overline Q_i,&i\in T,\\
\overline C_i,&i\notin T.
\end{cases}                                           \tag{3.1}
\]

When `s` Quits surely, player `i`'s pure-Quit and pure-Continue endpoint
payoffs are exactly `Qbar_i` and `Cbar_i`, independently of all old mixed
rates.  This holds because the two relevant families of coalitions are
disjoint according to membership of `i`.

Independently choose `Qbar_s,Cbar_s` and set the `s` coordinate of every
terminal row containing `s` to `Qbar_s`, and that of every terminal row not
containing `s` to `Cbar_s`.  Both endpoint expectations are again literal
constants, because an old base quitter makes every first-stage terminal
coalition nonempty.  Therefore

\[
\Delta_i^1=\overline Q_i-\overline C_i,
\qquad
\Delta_s=\overline Q_s-\overline C_s                  \tag{3.2}
\]

are freely and coordinatewise programmable without changing the original
Fin4 subtable.  At the lifted row with `s` prescribed Continue, they also do
not change any old player's numerical first-stage endpoints, prescribed
payoff, or unrestricted cap: a unilateral replacement of that old player
still leaves the other base member Quitting surely and `s` Continuing.  This
sentence does not identify the Fin4 and Fin5 punishment values or terminal
witnesses.

This lemma is only an interface extension.  It does **not** assert that an
arbitrary extension preserves a five-player terminal exploitability witness,
normality, or punishment floors.  Its consequence is the narrower and exact
one needed here: those properties are not encoded in the Fin4 handoff fields,
so no theorem from those fields alone can determine (1.1) or (1.2).

## 4. Two independent failed implications

### 4.1 Free endpoint complementarity is not produced

Keep both base endpoint gaps at

\[
\Delta_b^1=0.
\]

Then, writing `a_b=-Delta_b^0>0`, each cancellation threshold is one and
`q_*=1`.  Choose the spare gap so that `0<=kappa<=D_0`; the scalar budget can
therefore hold.  For either free player, use (3.1) to choose
`Delta_f^1` with the forbidden sign in (2.3) (or any nonzero value when its
rate is interior).  Then

\[
\Phi_{p_f}(\Delta_f^1)>0.
\]

Thus the scalar budget and base cancellation do not supply the missing free
endpoint complementarity.

### 4.2 The scalar budget is not produced

Conversely choose `Delta_f^1=0` for both free players and again choose
`Delta_b^1=0` for both base players.  Then all the collision endpoint
complementarity conditions hold and `q_*=1`.  Choose

\[
\overline C_s-\overline Q_s=\kappa>D_0.
\]

The source spare condition `Delta_s=-kappa<=0` still holds, but

\[
q_*\kappa=\kappa>D_0.
\]

Hence even complete endpoint complementarity for the four old coordinates
does not imply the scalar budget.  If a common reward bound is desired, one
may enlarge the bound used for the five-player completion; the quantitative
Fin4 handoff lower bounds only become weaker.  No fixed-bound comparison
between `kappa` and `D_0` occurs in the checked handoff data.

After this screen was written, `CODEX_EULER` independently supplied the two
fully explicit rational tables in
[`CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md`](CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md).
Both tables have reward bound `20` and certify all endpoint punishment floors
by pure-row caps.  The first has full old-player endpoint complementarity but
`q_*=1/2`, `kappa=10`, and `D_0=2`; the second has
`q_* kappa=1<=D_0=2` but recreates free-player debt at `q_*`.  These examples
remove any concern that the two failed implications above are artifacts of
allowing an unbounded fifth-coordinate completion.

## 5. The sharp missing scalar inequality

On the exact two-debtor subbranch the checked `debtor_gap` field gives

\[
D_0\ge\Gamma.                                         \tag{5.1}
\]

Also `0<q_*<=1`.  Thus either of

\[
\kappa\le D_0,
\qquad\text{or more strongly}\qquad
\kappa\le\Gamma                                      \tag{5.2}
\]

would be a simple sufficient producer for (1.2).  The sharp condition is

\[
\kappa\le \frac{D_0}{q_*}.                            \tag{5.3}
\]

In terms of endpoint gaps it is

\[
\kappa\max_{b\in B}
 \frac{a_b}{a_b+\Delta_b^1}
\le a_{b_0}+a_{b_1}.                                  \tag{5.4}
\]

The checked data provide no upper bound of this kind.  They give a lower
bound on one base debt and quantitative lower bounds on free absorption or a
terminal atom; neither compares the spare's own Continue premium to the base
debt.

Even a five-player terminal-gap witness supplies the wrong kind of
information.  Once all four old coordinates satisfy the collision endpoint
conditions at `q=1`, the spare is the only possible debtor there, so the same
gap merely gives

\[
\kappa\ge\Gamma.                                      \tag{5.5}
\]

Together with `D_0>=Gamma`, these are two unrelated lower bounds, not the
comparison (1.2).  In particular the convenient sufficient condition
`kappa<=Gamma` would have to be a tightness statement, not a consequence of
the terminal gap.

There is also an important orientation check.  If the five-player source is
assumed to be a global minimizer and the other cancellation hypotheses have
already been proved, then the actual profile at `q_*` gives automatically

\[
D_0\le q_*\kappa,                                     \tag{5.6}
\]

the **reverse** inequality.  Therefore the verifier's budget is, in the
minimum branch, precisely the missing equality `q_* kappa=D_0`; it is not a
consequence of minimum-debt monotonicity.

## 6. Producer verdict and next exact target

The checked Fin4 pair-base/2+2 handoff supplies:

1. an actual source and the `q=0` complementarity of both free players;
2. a nonempty base-supported debt set of cardinality at most two;
3. one base debt at least `Gamma`, a positive-mass nonsingleton atom, and a
   source-matched paid row.

It does **not** supply:

1. two positive base debts rather than one;
2. any fifth-label collision row, hence the two `q=1` free complementarity
   conditions or the base cancellation gaps;
3. the spare's Continue premium `kappa`;
4. the comparison `q_* kappa<=D_0`; or
5. punishment-floor domination at both five-player endpoints for all five
   coordinates.

Accordingly the same-profile verifier is not presently a consumer of the
actual Fin4 handoff.  A genuine producer must add a **co-realized completion
theorem**, not another label alignment: it must select one actual fifth-label
collision row satisfying (2.3) for both free rates and either (5.3) directly
or an exact balance/circulation identity that implies it.  Reselecting a new
persistent-base Nash point after adding `s` would establish different-profile
complementarity and would lose the same-profile provenance that the verifier
was designed to preserve.

## 7. Review request

Please independently check the exact extension-freedom construction, the
boundary cases in (2.3), the use of the checked `free_solved` fields, and the
minimum-orientation inequality (5.6).  In particular, please identify any
checked five-player completion theorem that constrains the new `s`-containing
rows while preserving this exact pair-base source; none was found in the
narrow source search above.
