# Review of the minimum-cap-tube forced-pair barrier

Reviewer: `ATLAS_GATEKEEPER`

Source:
[`SERIAL_ENDPOINT_AUDITOR__MINIMUM_CAP_TUBE_FORCED_PAIR_BARRIER.md`](../notes/SERIAL_ENDPOINT_AUDITOR__MINIMUM_CAP_TUBE_FORCED_PAIR_BARRIER.md)

Verdict: **MATHEMATICALLY SOUND AFTER A SMALL SOURCE REPAIR, BUT NOTES ONLY.**
The cap-projection linear estimate and the reached finite-word telescope are
valid.  In fact the cap-projection statement is generic for every nonempty
finite player set with positive global terminal-semantic debt minimum; it does
not need the Fin4 hard residual or punishment normality.  It is, however, a
direct specialization of already checked generic declarations plus an
elementary finite telescoping sum.  The maintained frontier already records
that the compact minimum-fiber tube and linear-defect bound exclude purely
local fixed-charge constructions.  The forced pair is already treated as a
counterfactual sibling rather than a proposed exact row.  The note therefore
does not strictly narrow a named live atlas obligation and does not meet export
gate item 4.

## 1. Cap-projection specialization: PASS, with corrected sources

Let $m>0$ be the global minimum of total terminal-semantic debt, let
$\mathcal M$ be its compact fiber, and put

\[
 K_B=\{z.2:z\in\mathcal M\}.
\]

Compactness and nonemptiness of $K_B$ follow from
`quittingTerminalSemanticMinimumFiber_isCompact` and
`quittingTerminalSemanticMinimumFiber_nonempty` in
`TerminalSemanticFinFourMinimumFiberIsolation.lean`, by continuous image
under `Prod.snd`.  Those declarations are generic despite the filename.

The note cites the prescribed-coordinate singleton-separation and freezing
theorems as if the cap case were the same specialization.  The cap case is
valid, but the sharper exact sources are instead:

* `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`, which gives, for every minimum
  pair $z$ and every player $i$,

  \[
  m\le z.2_i-r_i(\{i\});
  \]

* `minimumTerminalSemantic_auxiliaryNash_eq_allContinue` in the same file,
  applied with the zero subsidy $h=0$, which says that every exact Nash root
  against $z.2$ is all Continue.

Thus the abstract hypotheses of
`exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` in
`Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean` hold on
$K_B$ with the uniform gap $\delta=m$.  It yields an open $N_B\supseteq K_B$
and $c>0$ such that

\[
 c\,A(q)\le \operatorname{Def}(b,q)
 \qquad(b\in N_B)
\]

for every product root $q$.  This proves the note's (1).  Since a coalition
root mass is at most total root absorption, (2)--(3) follow immediately.
For `Fin 4`, `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash`
gives the factor $4$ in (4).

This proof uses cap vectors, not prescribed payoffs.  It should not cite
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` as
the actual cap-projection theorem: that checked declaration takes

```text
K = Prod.fst '' minimumFiber
```

and therefore prices roots against the prescribed projection.  The new cap
wrapper is a short, legitimate corollary of the three generic declarations
above.

## 2. Near-minimum passage: PASS with an explicit topology statement

If $z_n$ are carrier pairs with $D(z_n)\to m$, carrier compactness implies
that every cluster point lies in $\mathcal M$.  Equivalently,

\[
 \operatorname{dist}(z_n,\mathcal M)\to0,
 \qquad
 \operatorname{dist}(z_n.2,K_B)\to0.
\]

Hence $z_n.2\in N_B$ eventually.  One may prove this either by contradiction
and a compact subsequence or after a convergent subselection, as the note
says.  The conclusion is about the actual suffix cap $z_n.2$; it is not an
attainment claim for the minimum pair.

## 3. Finite-word telescope: PASS under the stated rowwise tube hypothesis

For a finite word let

\[
 C_t=\prod_{s<t}(1-A(q_s)).
\]

If the continuation cap displayed at every row lies in $N_B$, multiply the
one-row estimate by $C_t\ge0$ and sum:

\[
 c\sum_{t<T}C_tA(q_t)
 \le
 \sum_{t<T}C_t\operatorname{Def}(b_{t+1},q_t).
\]

The identity

\[
 \sum_{t<T}C_tA(q_t)=1-C_T
\]

is the elementary survival telescope.  If the unconditional marked mass is
$C_t\beta_C(q_t)\ge\lambda$, then $C_tA(q_t)\ge\lambda$, proving (7).
There is no hidden independence across dates: only each displayed one-stage
root is a product distribution.

The hypothesis that **every displayed continuation cap** belongs to $N_B$ is
essential for approximate words.  Proximity of the final semantic tail to
the minimum fiber does not alone keep a long approximate cap word in the
tube.  For an exact cap stack, backward induction makes this issue disappear:
the final cap is in the tube, so the last exact root is all Continue and leaves
the cap unchanged; repeat backwards.  For approximate stacks, one needs the
rowwise tube hypothesis or a separate successor/cap-motion estimate.  The
note's status paragraph states the rowwise hypothesis, but the question and
Section 4 should not abbreviate it merely as “the same near-minimum tail.”

The note correctly uses **unconditional** marked mass in the word result.  A
fixed conditional root mass at a row whose reach $C_t$ tends to zero does not
give a fixed charge.

## 4. Forced-pair specialization

For a literal pure pair, its conditional pair mass is one.  The source packet's
stronger selected-payer estimate is a separate source-specific fact; it is
not needed for the cap-tube theorem.  The tube theorem says more uniformly
that any root retaining a fixed amount of pair mass has fixed total defect.

This is a valid impossibility statement about a proposed *local
exactification*.  It does not consume the forced-pair source, because the
maintained construction never requires the pure pair itself to be a cap--Nash
row.  The pair is a counterfactual marked sibling carrying mass and paid gain.
Nor does the theorem turn its fixed defect into a punishment-floor edge,
near-return, terminal approximant, or support descent.

## 5. Freshness and export gate

The mathematical content is almost entirely present in checked form:

1. compact strict-basin linear pricing is
   `exists_open_linearAbsorptionDefect_of_compact_strictAllContinue`;
2. the cap singleton margin and cap-root uniqueness are
   `minimumTerminalSemantic_singletonMargin` and
   `minimumTerminalSemantic_auxiliaryNash_eq_allContinue`;
3. finite-family absorption summation is already represented by
   `sum_quittingRootAbsorptionMass_le_card_div_mul_sum_error`; and
4. the stronger successor-linked prescribed-projection gate is checked as
   `FinFourCarrierSourceChargeDebtErrorGate.debt_or_error` and
   `.debt_of_exactPath` in
   `TerminalSemanticFinFourCarrierSourceChargeDebtErrorGate.lean`.

The only absent convenience declaration is the cap-projection wrapper and its
reach-weighted word corollary.  The current `questions/README.md` already says
that the compact minimum-fiber tube and linear-defect bound rule out a purely
local fixed-charge construction.  Therefore this is not a strict new answer
to a named question, a new actual-data producer, or a new semantic consumer.
The proper disposition is **NOTES ONLY**, not export.

## 6. Required repairs to the note

1. Replace the prescribed-projection source description by the exact generic
   cap-margin and zero-subsidy auxiliary-Nash declarations listed above.
2. State the strongest scope: arbitrary nonempty finite player type with
   positive global terminal-semantic debt minimum.  Only the conversion from
   coordinatewise error to total error uses the cardinal, with `4` in Fin4.
3. In every finite-word application, retain the explicit hypothesis that all
   displayed continuation caps lie in $N_B$, except when exact backward
   induction derives it from the final cap.
4. Remove the duplicated sentence at the beginning of `Lean handoff`.
5. Add boundary tests if this is ever promoted: $m=0$ (the zero table) destroys
   every positive linear modulus; leaving $N_B$ can admit absorbing exact
   roots; and fixed conditional mass with vanishing row reach does not imply a
   fixed word charge.

No mathematical objection remains to the corrected no-go itself.
