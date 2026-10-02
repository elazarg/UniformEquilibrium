# A minimum-return endpoint is already an active marked passport

Author: `SERIAL_ENDPOINT_AUDITOR`

## Status

This is an ordinary-mathematics closure of the exactification-return arm of
the empty-corner reactivation question.  It uses only actual profiles,
unrestricted behavioral caps, the positive global minimum, and the retained
pure marked atom.  No cap-curvature localization is needed.

If fresh exactification of the killed-mover endpoint returns to the minimum
fibre, the returned profiles themselves have debt tending to \(D_*\), retain
a fixed marked stage mass, and carry a fixed currently executable behavioral
gain at that same marked row.  Thus they are exactly the first allowed output
of the active-passport capstone.  Passing them immediately to the broad
concentrated-packet residual is valid but loses sight of this stronger direct
conclusion.

This is a **producer/contraction output, not a terminal consumer**.  It sends
the minimum-return arm back to the maintained active-passport / concentrated
collision route; it does not by itself produce terminal approximants, an
exact return, a support drop, or a uniform-equilibrium payoff.  The result
does not address the genuinely off-minimum normalized-passport inert
minimizer, where no minimum-return sequence is available.

## 1. Input from exactification return

Let \(D_*>0\) be the global minimum terminal-semantic debt.  Suppose
\(V_n\) are actual behavioral profiles obtained by exactifying the literal
killed-mover endpoints, with

\[
 D(V_n)\longrightarrow D_*.
\tag{1}
\]

Let \(t_n\) be their retained marked dates.  In the source-specific
forced-pair construction, suppose the marked root is the same pure pair
\(T=\{j,o\}\) and

\[
 \Pr_{V_n}(\text{terminal }T\text{ at }t_n)\ge\rho>0.
\tag{2}
\]

Write \(p\) for the killed mover.  Exact endpoint routing gives

\[
 \delta_{n,p}=0,
\tag{3}
\]

where \(\delta_{n,p}\) is the root-coordinate Nash defect at the marked row
against the **prescribed payoff** of the literal post-mark tail.  This
qualification matters: the checked field is not stated against the tail cap.
At a pure pair it is nevertheless exactly the semantic-debt coordinate,
because another sure quitter screens every unilateral continuation.

These are exactly the mathematical fields of the returned endpoint sequence
\(V_n\) in the strict killed-mover exactification construction.  The generic
checked actualizer exposes all but the pure-root equality:

* `QuittingMarkedPairMinimumReturnActualizer.profiles` and `.mark` are the
  actual rows and shifted marks;
* `.resolution_le_stageMass` is (2);
* `.markedOwnerDefect_eq_zero` is (3), against the tail pair's `.1`
  prescribed-payoff coordinate; and
* `.wholeDebt_tendsto_minimum` is (1).

The exact source-side purity theorem is
`FinFourWeakCoreForcedPairPacket.pairProfile_eq_purePair`; arbitrary literal
prefixing preserves the marked root by
`QuittingMarkedPairDecoratedFamily.descendant_markedRoot_eq`.  The current
generic `QuittingMarkedPairDecoratedFamily` structure does not store this
pure-root field, so a Lean composition must either retain the source-specific
forced-pair wrapper or add the marked-root equality as an explicit hypothesis.
It cannot be inferred merely from positive stage mass of `family.terminal`.
Likewise, one must not silently reinterpret
`.markedOwnerDefect_eq_zero` as a cap-coordinate assertion.  The conversion
is valid here only through pure-nonsingleton screening.

## 2. Positive minimum forces another marked payer

Take the actual all-Continue spine of \(V_n\) starting at \(t_n\), and call
its terminal-semantic pair \(y_n\).  Its first root is the pure pair \(T\).
For every player, forcing that player to Continue leaves another sure
quitter.  Hence the continuation is screened coordinatewise.  The checked
pure-nonsingleton identity reduces the total semantic debt to prescribed-tail
root defects:

\[
 \boxed{
 D(y_n)=\sum_{i\in\operatorname{Fin}4}\delta_{n,i}.
 }
\tag{4}
\]

The point \(y_n\) is realized by an actual profile.  Global minimality gives

\[
 D_*\le D(y_n).
\tag{5}
\]

Using (3)--(5),

\[
 D_*\le\sum_{i\ne p}\delta_{n,i}.
\]

There are only three terms, so some \(i_n\ne p\) satisfies

\[
 \delta_{n,i_n}\ge D_*/3.
\tag{6}
\]

Pass to a subsequence and fix \(i_n=i\).  No response strategy is asserted to
stabilize.

This argument works for every **nonsingleton** pure root.  It does not extend
as written to a singleton: the singleton owner can Continue into the tail,
so a zero prescribed-tail endpoint defect need not be a zero cap defect.

## 3. Turn the marked defect into an actual whole-profile gain

Let \(L_n\) be the probability that \(V_n\) reaches date \(t_n\).  Since the
marked root is pure, its conditional mass on \(T\) is one.  Hence (2) gives

\[
 L_n\ge\rho.
\tag{7}
\]

At a pure pair every player's two relevant endpoint values are literal:
even after one player Continues, the other pair member Quits surely.  Choose
the better Boolean endpoint for \(i\), leave its behavior before \(t_n\)
unchanged, and perform the literal one-date update.  Its whole-profile gain is
the reached mass times the root defect.  Equations (6)--(7) give the sharper
bound

\[
 \boxed{
 U_i(V_n[i\leftarrow\tau_{n,i}])-U_i(V_n)
 \ge \rho D_*/3.
 }
\tag{8}
\]

No cap-attainment assumption occurs: pure-nonsingleton screening makes the
better response a literal one-date Boolean endpoint.

Combining (1), (2), and (8), the returned endpoint sequence satisfies

\[
 \boxed{
 \begin{array}{c}
 D(V_n)\to D_*,\\
 \Pr_{V_n}(T\text{ at }t_n)\ge\rho,\\
 \text{one fixed player has a currently executable gain}
   \ge\rho D_*/3.
 \end{array}}
\tag{9}
\]

All profiles, exactification words, marked dates, terminal labels, and
post-date tails are the original source-matched objects.  Thus (9) is the
near-minimum active-passport output, not a newly selected generic paid row.

For the checked forced-pair source one can avoid the nonattained-cap
approximation entirely.  `FinFourWeakCoreForcedPairPacket.nonempty_forcedPairPacket`
uses `quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect`,
selects a distinct payer, and stores the exact bound in
`FinFourWeakCoreForcedPairPacket.payerDefect_floor`.  The literal endpoint
adapter then supplies
`QuittingStageAtomConcentratedPacketAdapter.sourceToTargetGain_eq_liveMass_mul_defect`
and its monotone lower-bound form `sourceToTargetGain_lowerBound`.

There is also a genuinely separate table-level singleton fallback:
`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
is used by
`FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` to pick
a strict outsider join for any supplied singleton owner.  It is available for
the exact hard-residual source and does not depend on the previous marked
owner.  At a literal pure singleton row, the selected outsider's Quit and
Continue outcomes are immediately \(\{j,o\}\) and \(\{j\}\), so the theorem
does give a literal positive marked gain with the hard-residual terminal-gap
floor.  It does **not** repair the singleton owner's prescribed-defect/cap-
defect mismatch, and invoking it without first proving that the marked root
is literally that pure singleton would be invalid.

Thus a more abstract exactification result whose routed terminal might be
singleton or nonsingleton still has an active-passport conclusion, but by two
different proofs:

* nonsingleton: pure screening plus (3)--(6), with conditional gain at least
  \(D_*/3\);
* singleton: the hard-residual outsider-join theorem, with conditional gain
  at least the terminal gap \(\gamma\).

With stage-mass floor \(\rho\), a common safe whole-profile gain floor is
\(\rho\min\{D_*/3,\gamma\}\).  The present forced-pair return uses only the
first arm.

## 4. Consequence for the exactification split

Fresh exactification of the killed-mover endpoint has two genuinely
different outcomes.

1. **Minimum return.**  The returned sequence \(V_n\) satisfies (9).  This
   arm has already reached the allowed active-passport producer output.  The
   existing recurrent concentrated-packet construction and three-role
   collision machinery are the downstream contraction; (9) is not itself a
   terminal solution.
2. **Strict normalized-passport inertness.**  The selected compact slice
   remains strictly above \(D_*\), and exact prefixing freezes at unique all
   Continue.  No \(V_n\) satisfying (1) is produced.  The proof above says
   nothing about this arm.

The whole-word fixed-observer cap-curvature square belongs to the first case,
after an exactification-return word has already been selected.  It is useful
extra structure, but it is not needed to obtain (9) and should not be treated
as an obstruction left over from that case.

## Lean handoff

The composition needs only:

* the returned endpoint fields `D(V_n) -> D_*`, marked mass, pure routed
  terminal, and killed mover defect zero;
* the checked pure-nonsingleton screening identity;
* finite averaging over `Fin 4 \ {p}`; and
* the literal reached-row best-endpoint gain identity.

A suitable source-specific declaration is:

```text
minimumReturnKilledEndpoint_exists_fixedMarkedBehavioralGain
```

with conclusion (9) and the complete returned-endpoint source wrapper as an
index.  It should not be stated for an arbitrary
`QuittingMarkedPairMinimumReturnActualizer` unless literal nonsingleton purity
of its marked root is added.  Zero joint-Continue alone is insufficient for
coordinatewise screening: every player needs a different sure quitter.
