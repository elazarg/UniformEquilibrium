# Review of the postmark paid-port bridge and near-return regression

Reviewer: `CODEX_DESCENDANT`

Date: 2026-08-31

Verdict: **REVISE, then PASS.**  The bridge and the Fin4 regression are
mathematically sound.  The paid-splice debt calculation, actual-reach
selection, and cap-port packaging all use actual behavioral profiles and
unrestricted caps.  The exact local regression has the stated payoffs, caps,
debts, suffixes, and hazard behavior.  One sentence in the off-minimum arm
reverses the meaning of the cap-prefix absorption budget, and two displayed
formulae are missing closing delimiters.  Neither issue damages the main
reduction.

## 1. Claim audited

The note makes three claims:

1. the paid arm of the postmark two-cut producer supplies enough whole-parent
   debt for the scratch actual-reach selector, and its resulting literal paid
   row instantiates the production paid-cap trichotomy;
2. the uniformly off-minimum exit suffix can likewise be packaged into that
   trichotomy, but has no generic return or renewable consumer; and
3. a four-player table realizes uniform paid reach, arbitrarily deep
   all-Continue exact prefixes, and a later unit-hazard crossing whose exit
   debt is strictly larger, while still having global minimum zero.

All three survive, with the absorption-budget wording repaired as in
Section 4 below.

## 2. Paid-splice debt and actual-reach constants

The checked Fin4 splice is a literal one-player update of the canonical
parent.  Its theorem gives both the parent payoff gain and the equality

\[
 d_p(P_n)-d_p(Y_n)=G_n.
\]

Since \(Y_n\) is actual, \(d_p(Y_n)\ge0\).  Therefore

\[
 d_p(P_n)=G_n+d_p(Y_n)\ge G_n>G_0.
\]

This is the correct direction; no target-side small-debt field is needed for
this inequality.

For the later-block constants, the symbol \(K\) should be identified with
the current producer's

\[
 K_1=(1-e^{-\mu/2})D_*,
 \qquad G_0=\mu K_1/32.
\]

Taking

\[
 \Delta=G_0/2
\]

meets the scratch selector's hypothesis \(\Delta\le d_p(P_n)\).  The selected
row has declared gain

\[
 \Delta/4=G_0/8
\]

and its joint reach \(R_n\) satisfies

\[
 \Delta^2\le32M^2R_n.
\]

Thus, when written as an explicit floor,

\[
 R_n\ge \frac{G_0^2}{128M^2}.
\]

Positive \(G_0\) excludes the degenerate reward-bound case \(M=0\).  The
constants and strictness are correct.

The source profile passed to the selector is \(P_n\), not the paid target
\(Y_n\).  The resulting row can be different from the date-one splice and
can occur outside the two-cut interval.  The note records this loss
correctly.

## 3. Exact cap-port packaging

`paidFirstDisagreement_capPortTrichotomy` requires only:

* one globally minimizing semantic pair;
* positivity of its total debt;
* one actual profile;
* one positive declared gain; and
* one `QuittingPaidFirstDisagreementRow` carrying that gain.

The selector supplies exactly these fields with profile \(P_n\), observer
\(p\), and gain \(G_0/8\).  The theorem therefore returns a
`QuittingPaidCapLiftedSource` and a summable port in the exact disjunction

\[
 \text{ChargedNearReturn}\ \lor\
 \text{QuantitativeDebtDescent}\ \lor\
 \text{InertStall}.
\]

The classification asserted in the note is accurate:

* `ChargedNearReturn` already contains a uniform-equilibrium payoff;
* `QuantitativeDebtDescent` has positive cap displacement but is not by
  itself a renewable natural-valued rank; and
* `InertStall` has total absorption and cap displacement exactly zero,
  every selected cap root all Continue, constant finite-prefix semantics,
  and lossless horizontal transport of the paid row.

Thus the composition is an exact source-faithful packaging theorem, not a
new consumer.

The missing display closes after equations (2.5) and (2.6) should be added.

## 4. Off-minimum arm: valid packaging, invalid budget sentence

From

\[
 D(u_n)\ge D_*+\delta
\]

some player has debt at least \((D_*+\delta)/4\).  After a finite-label
subsequence one player is fixed.  Applying the actual-reach selector with

\[
 \Delta_{\rm off}=(D_*+\delta)/4
\]

gives a uniform row gain

\[
 (D_*+\delta)/16
\]

and, if desired, the explicit joint-reach floor

\[
 \frac{(D_*+\delta)^2}{512M^2}.
\]

Hence the generic off-minimum family really does enter the same paid-cap
trichotomy with uniform quantitative data.  This strengthens the note's
bare “positive coordinate” wording.

The sentence

> The extra debt excess pays a nonzero cap-prefix absorption budget

must be changed.  The checked estimate is an **upper** bound

\[
 \operatorname{totalAbsorption}
 \le \frac{D(u_n)-D_*}{D_*}.
\]

Positive debt excess permits a positive upper budget; it does not force any
positive absorption.  The selected exact roots may all Continue, and the
inert arm remains possible.  The subsequent no-consumer conclusion is
correct and should simply omit this false suggestion.

## 5. Exact audit of the four-player regression

For

\[
r_0=0,\qquad r_1=1,\qquad
r_2(S)=\mathbf1_{\{2\in S\}},\qquad r_3=0,
\]

and the profile where player \(0\) uses `QuitAt N` and the others use
`Never`, the terminal coalition is \(\{0\}\).  Hence

\[
 U=(0,1,0,0).
\]

The cap computation is exact:

* player \(0\) can only obtain zero;
* player \(1\) obtains one at every terminal coalition;
* player \(2\) obtains one by quitting at any date at most \(N\);
* player \(3\) can only obtain zero.

Therefore

\[
 B=(0,1,1,0),\qquad d=(0,0,1,0),\qquad D=1.
\]

Player \(2\)'s replacement `Never -> QuitAt 0` has gain one and first
disagreement reach one.  At the cap \(B\), every singleton Quit endpoint is
exactly its corresponding cap coordinate:

\[
 (r_i(\{i\}))_{i<4}=(0,1,1,0)=B.
\]

Thus all Continue is an exact cap root, and arbitrarily many chosen
all-Continue exact prefixes retain the pair and reach the shifted row with
probability one.  This is an existence statement about a compatible exact
prefix word; it does not assert that the noncomputably selected canonical
maximal/cap-lift root must be all Continue.  The note does not need that
stronger assertion.

For every \(0\le k\le N\), the live suffix has player \(0\) using
`QuitAt (N-k)` and therefore the same pair and debt one.  The canonical pure
time quits only at its specified date, so after the all-Continue history
through date \(N\), the suffix at \(N+1\) is all Never.  There

\[
 U=0,\qquad B=(0,1,1,0),\qquad D=2.
\]

The sole prescribed positive hazard is player \(0\)'s unit hazard at date
\(N\).  A block has positive total hazard exactly when it contains that
date; its exit cut is then greater than \(N\), so its exit suffix is
all Never with debt two.  Conversely, a block whose exit suffix has debt one
must end no later than \(N\) and excludes the unit-hazard date.  All suffix
and hazard claims are correct.

Finally, the profile in which player \(2\) Quits immediately has pair

\[
 U=B=(0,1,1,0),
\]

so it has zero debt.  The regression is not a positive-minimum
counterexample.

## 6. Novelty and exact remaining waist

The bridge itself is a short but useful composition of checked interfaces.
It proves that the weak postmark paid output is not stranded outside the
paid-cap atlas; it enters the exact existing terminal SCC with an explicit
actual-reach floor.  It does not shrink that SCC.

The regression is the more informative new content.  It falsifies any
consumer based only on:

* uniform paid-row reach and gain;
* a later positive-hazard block;
* arbitrarily deep compatible all-Continue exact ancestry; and
* literal suffix provenance.

The remaining waist is therefore genuinely global: positive-minimum
provenance must either turn an off-minimum literal suffix into an executable
return/renewable child, or prevent the inert zero-absorption port while
retaining the postmark law/atom passport.  No local reach, gain, hazard, or
exact-prefix field in the note does so.

After the display and absorption-budget repairs, I found no mathematical
blocker.
