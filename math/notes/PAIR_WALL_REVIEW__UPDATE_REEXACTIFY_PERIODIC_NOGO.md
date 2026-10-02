# Horizontal update followed by maximal re-exactification can cycle exactly

Author: `PAIR_WALL_REVIEW`

## Status

Exact ordinary-mathematics sensitivity theorem plus a Lean-checked finite
regression assembled into the requested update--re-exactify operation.

The result is a broad no-go for any renewal theorem using only the local
post-stall passport: positive marked mass, a paid best-endpoint edge, exact
maximal prefixing, debt support or normalized debt, current cap, and remaining
exact-prefix charge.  Those data can execute a nontrivial periodic loop.

The regression has global semantic minimum zero.  It therefore does not
refute a theorem that uses positive global minimum provenance essentially.
Its conclusion is the narrower and useful one: no strict rank or charged
return can be extracted from the update--re-exactify interface alone.

## 1. Exact finite-prefix sensitivity

Fix a finite word of product roots

\[
 W=(q_0,\ldots,q_{K-1})
\]

and two actual behavioral tails \(\sigma,\tau\).  Let \(W*\sigma\) and
\(W*\tau\) be the literal profiles obtained by placing the same word above
the two tails.  Put

\[
 J(W)=\prod_{h<K}c(q_h),
 \qquad
 R_i(W)=\prod_{h<K}c_{-i}(q_h),                 \tag{1}
\]

where \(c(q_h)\) is joint all-Continue probability and \(c_{-i}(q_h)\)
is opponents-only all-Continue probability for player \(i\).

For prescribed payoff there is an affine identity

\[
 U_i(W*\tau)-U_i(W*\sigma)
   =J(W)\bigl(U_i(\tau)-U_i(\sigma)\bigr).       \tag{2}
\]

For the unrestricted behavioral cap, define the one-root Bellman map

\[
 \Phi_{i,q}(b)=\max\{Q_{i,q},A_{i,q}+c_{-i}(q)b\}. \tag{3}
\]

Here \(Q_{i,q}\) is the payoff from quitting at that root, and \(A_{i,q}\)
is the absorbing contribution when \(i\) Continues and some opponent Quits.
The full behavioral cap satisfies

\[
 B_i(W*\sigma)
 =\Phi_{i,q_0}\circ\cdots\circ\Phi_{i,q_{K-1}}
      (B_i(\sigma)).                             \tag{4}
\]

This is exact against arbitrary behavioral deviations.  Before absorption a
quitting game has one live public history, so the deviator's dynamic program
at each row is exactly Quit now versus Continue to the next cap.  In
particular, the composite map in (4) is monotone and
\(R_i(W)\)-Lipschitz.  Therefore

\[
 \begin{aligned}
 d_i(W*\tau)-d_i(W*\sigma)
   ={}&\Phi_{i,W}(B_i(\tau))-
       \Phi_{i,W}(B_i(\sigma))\\
     &-J(W)\bigl(U_i(\tau)-U_i(\sigma)\bigr),    \tag{5}
 \end{aligned}
\]

and

\[
 |d_i(W*\tau)-d_i(W*\sigma)|
 \le R_i(W)|B_i(\tau)-B_i(\sigma)|
      +J(W)|U_i(\tau)-U_i(\sigma)|.              \tag{6}
\]

If rewards are bounded in absolute value by \(M\), then

\[
 |d_i(W*\tau)-d_i(W*\sigma)|\le4M R_i(W),        \tag{7}
\]

because \(J(W)\le R_i(W)\).

Equation (6) is the exact cross-coordinate cap-leakage scale.  The marked
payoff edge is transported by **joint** reach \(J(W)\), while another
player's cap can react at the larger **opponents-only** reach \(R_i(W)\).
There is no general estimate \(R_i(W)=O(J(W))\): their ratio is the inverse
of player \(i\)'s prescribed Continue reach through the word and can be
arbitrarily large.

### Own-coordinate exception

Suppose \(\tau\) is obtained from \(\sigma\) by changing only player \(p\)'s
complete strategy.  Then

\[
 B_p(\tau)=B_p(\sigma),                           \tag{8}
\]

because the opponents are unchanged.  Hence (5) becomes

\[
 d_p(W*\tau)-d_p(W*\sigma)
 =-J(W)\bigl(U_p(\tau)-U_p(\sigma)\bigr).         \tag{9}
\]

This is the exact mover-debt subtraction used by the marked endpoint update.
No analogous cancellation holds for the other coordinates.

If \(W\) is an exact cap--Nash prefix word for \(\sigma\), its source debts
scale by \(J(W)\).  After replacing \(\sigma\) by \(\tau\), however, the
same roots need no longer be cap--Nash.  Recomputing maximal exact prefixes
from \(W*\tau\) scales the *new* debt vector along a new ray; it does not
undo the leakage in (5).

## 2. An exact update--re-exactify cycle

The checked table
`FourPlayerCyclicPlateauCandidate.reward` in
`Research/Quitting/FourPlayerCyclicPlateauCandidate.lean` supplies a complete
regression.

Write the players as movers \(0,1\), permanent host \(2\), and passive
observer \(3\).  Its four pure marked coalitions are

\[
 \{2\}\to\{0,2\}\to\{0,1,2\}\to\{1,2\}
 \to\{2\}.                                       \tag{10}
\]

To make the arrows literal **one-date** updates with one common tail, let
\(\widehat P_k\) use the pure root displayed at phase \(k\) at date zero and
then, after the counterfactual all-Continue outcome, use the stationary
phase-zero profile as its common tail.  At phase zero this is exactly the
stationary phase-zero profile.  At the other three phases the marked root is
nonsingleton, so its semantic pair is independent of the attached tail and
equals the checked stationary pair \(Z_k\).

Every arrow in (10) is now one literal date-zero best-endpoint update of
\(\widehat P_k\), leaving the common phase-zero tail unchanged.  After four
arrows the complete behavioral profile, not only its semantic pair, returns
to \(\widehat P_0\).  The checked table theorems

```text
phaseMover_payoff_gain
nextPhase_mover_debt_eq_zero
```

give, at every step:

\[
 U_{p_k}(Z_{k+1})-U_{p_k}(Z_k)=1,
 \qquad
 d_{p_k}(Z_k)=1,
 \qquad
 d_{p_k}(Z_{k+1})=0.                              \tag{11}
\]

Every marked coalition has mass one.  In particular, the two pair phases
\(\{0,2\}\) and \(\{1,2\}\) satisfy the requested positive fixed-pair mass
and paid endpoint hypotheses.

The cap is the same at all four phases:

\[
 B(Z_k)=(1,1,0,0).                                \tag{12}
\]

Moreover, all-Continue is the unique exact cap--Nash root at this cap.  This
is checked by

```text
phase_cap
exactCapNash_forces_allContinue
phaseZero_allContinue_exactCapNash.
```

Therefore the canonical maximal-absorption exact root is all-Continue at
every phase.  Re-running maximal exact prefixing after any horizontal update
only inserts literal all-Continue delays.  It has:

\[
 \text{absorption}=0,
 \qquad
 \text{charge}=0,
 \qquad
 \operatorname{Sem}(\text{delayed phase }k)=Z_k. \tag{13}
\]

Thus the operation

\[
 \text{paid horizontal endpoint update}
 \quad\longrightarrow\quad
 \text{maximal exact re-prefixing}                \tag{14}
\]

is exactly the four-cycle (10), modulo an irrelevant all-Continue delay.
After four operations the marked coalition, complete semantic pair, cap,
debt vector, terminal coalition law, marked mass, and remaining exact-prefix
charge all return to their initial values.

## 3. Exact cross-coordinate replenishment

This regression is stronger than a large-cap-leakage example: its cap leakage
is identically zero.  The common cap (12) gives

\[
 B_i(Z_{k+1})-B_i(Z_k)=0
 \quad\text{for every }i,k.                       \tag{15}
\]

The mover's unit prescribed-payoff gain removes its unit debt.  At the same
time the *next* mover's prescribed payoff falls by one, creating exactly one
unit of new debt there.  The host keeps one unit throughout.  Hence

\[
 d(Z_k)=e_2+e_{p_k},
 \qquad
 D(Z_k)=2.                                        \tag{16}
\]

The debt support always has cardinality two, but alternates between
\(\{2,0\}\) and \(\{2,1\}\).  The normalized debt vector alternates between

\[
 \tfrac12(e_2+e_0),\qquad
 \tfrac12(e_2+e_1).                               \tag{17}
\]

Thus cross-coordinate failure need not appear as an increase of an
unrestricted cap.  Pure prescribed-payoff externality alone can replenish
the exact mover-debt drain and close the renewal loop.

## 4. No local well-founded rank or charged return

On the exact operation (14), none of the proposed local ranks decreases:

* coalition label returns after four updates;
* positive-debt-support cardinality is constantly two;
* the full support and normalized debt vector are periodic;
* total debt is constantly two;
* the cap is constant;
* marked mass and paid gain are constantly one; and
* all current and future maximal-prefix charge is zero.

Any function of this complete finite tuple returns to its initial value after
four steps, so it cannot strictly decrease at every update--re-exactify
operation.  If one retains the accumulating all-Continue delays as part of
the state, the operation instead gives an infinite executable sequence; a
natural-valued rank still cannot decrease strictly at every step.  The exact
roots also provide no positive charge to feed a
near-return compiler.  The horizontal edges are profitable behavioral
updates, but they are not punishment-floor exact Bellman edges; counting
their gains as chronological charge would be the forbidden horizontal-to-
vertical conversion.

This is a formal no-go for a universal theorem of the form

\[
 \boxed{
 \text{local paid collision passport}
 +\text{ maximal re-exactification}
 \Longrightarrow
 \text{strict local rank descent or charged return}.}
                                                               \tag{18}
\]

The no-go remains true even when every cap coordinate is perfectly stable.

## 5. Positive-minimum boundary

The regression has an exact all-Continue terminal equilibrium and global
semantic minimum zero, as checked by

```text
zeroProfile_isExactTerminalNash
zeroPair_debtSum_eq_zero.
```

Therefore it does not refute a theorem whose proof uses \(D_*>0\) to exclude
or consume the periodic replenishment.  Producing the same regression with a
positive global minimum would itself produce a counterexample to the Fin4
conjecture.

The correct remaining positive-minimum question is consequently sharper:

> Prove that positive-minimum source provenance forbids a periodic
> replenishment of the form (15)--(17), or convert the replenished coordinate
> into an actual source-matched charged edge/support drop.  Maximal exact
> prefixing and the local pair passport supply neither fact.

In particular, the next successful theorem must use data not present in the
post-stall tuple: a punishment-floor chronology, no-new-support control,
source-law incidence tied to the replenished coordinate, or another genuine
positive-minimum variational inequality.

## 6. Lean handoff

The generic sensitivity theorem can be packaged as finite-word prescribed
and cap transport:

```text
quittingTerminalPayoff_commonRootWord_sub_eq_jointReach_mul
abs_quittingBehavioralCap_commonRootWord_sub_le_opponentReach_mul
quittingTerminalDebt_commonRootWord_update_self_eq_sub_gain
```

The regression needs no new reward calculation.  It first adds the common-
tail one-date profiles \(\widehat P_k\), proves that their semantic pairs are
the existing `pair k`, and then composes existing checked facts into:

```text
FourPlayerCyclicPlateauCandidate.maximalCapPrefixRoot_eq_allContinue
FourPlayerCyclicPlateauCandidate.update_reexactify_semantic_eq_nextPhase
FourPlayerCyclicPlateauCandidate.update_reexactify_period_four
FourPlayerCyclicPlateauCandidate.update_reexactify_futureCharge_eq_zero
```

The first theorem follows from
`quittingMaximalCapPrefixRoot_exactNash` and
`exactCapNash_forces_allContinue`; semantic fixation follows from
`quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap`.

## Declarations inspected

* `quittingMaximalCapPrefixRoot_exactNash`,
  `quittingMaximalCapPrefixProfile_debt_succ`, and
  `summable_maximalCapPrefix_absorption` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`;
* `quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap`
  in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
* the complete finite table and checked identities in
  `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`; and
* the live maximal-prefix ray question in
  `notes/FORCED_PAIR_REVIEW__MAXIMAL_PREFIX_RAY_DICHOTOMY.md`.
