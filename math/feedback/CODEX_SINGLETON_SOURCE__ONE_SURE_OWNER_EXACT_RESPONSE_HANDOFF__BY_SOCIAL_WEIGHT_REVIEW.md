# Review of the one-sure-owner exact response handoff

Reviewer: SOCIAL_WEIGHT_REVIEW  
Date: 2026-08-31  
Verdict: **PASS**

## Claim reviewed

The note starts from an attained positive global-minimum semantic pair and
law realized by an all-Continue padding row, one product root with exactly
one sure quitter (k), and a Never continuation.  It claims that the sure
owner has an exact unrestricted behavioral response which gains exactly its
debt and kills that debt.  The response target is then either strictly
off-minimum or, without changing its law or replacing it by another
realizer, enters the checked reset-rigid chamber.

I checked the complete behavioral response class, the exact payoff/debt
identities, the equality target's finite incidence, and the literal
law-tight saturation re-anchor.  I also tried the boundary cases in which
all opponents Continue, the owner singleton reward is zero or negative, and
the other players' caps rise by the full amount of the killed debt.  None
falsifies the statement.

## 1. The unrestricted cap formula is exact

Let (s_i=r_i(\{i\})).  Against the fixed padded one-root profile, any
behavioral replacement by player (i) has only the following payoff-relevant
choices.

1. Quit at the padding row, for payoff (s_i).
2. Reach the product row and Quit, for payoff (Q_i).
3. Reach the product row and Continue.  On opponent absorption this gives
   the displayed coalition reward.  On opponent survival all opponents play
   Never, so an arbitrary future stopping law is a mixture of finite stopping
   for payoff (s_i) and Never for payoff zero.  Its optimum is
   (max\{0,s_i\}), giving (C_i).

Private randomization and calendar-dependent late stopping only convexify
these values.  Hence

\[
B_i=\max\{s_i,Q_i,C_i\}
\]

is the complete behavioral cap, not a stationary cap.  The checked theorem
`minimumTerminalSemantic_singletonMargin` makes (s_i) strictly nonbinding,
so removing the padding preserves the same cap.  For the unique sure owner,
the prescribed payoff is (Q_k); full debt therefore forces

\[
B_k=C_k>Q_k.
\]

This explicitly covers Never, arbitrarily late stopping, and the case where
the deviator is the sole sure quitter.  The note correctly distinguishes this
last case from the easier two-sure-quitter screening identity.

## 2. The response gain and debt kill are exact

The proposed response attains (C_k).  Since it changes only player (k)'s
strategy, the opponent profile faced by (k) is identical and therefore its
unrestricted best-response cap is literally unchanged.  Consequently

\[
U_k(\widehat\sigma)-U_k(\sigma)=C_k-Q_k=d_k(z),
\qquad
d_k(\widehat z)=0.
\]

The total-debt identity in (3.4) is then just exact coordinate bookkeeping.
No claim that the other three caps are unchanged is made.  In particular,
the note correctly permits all killed debt to reappear in the other
coordinates.

## 3. The equality target has positive opponent incidence

Let (a_{-k}) be the probability that a nonempty opponent coalition quits
at the product row after (k) is changed to Continue.  If (a_{-k}=0):

* when (s_k\ge0), the chosen response has pure singleton law and
  (U_k=B_k=s_k), contradicting the singleton margin at the assumed positive
  global minimum;
* when (s_k<0), it has pure Never law, contradicting
  `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`.

Thus (a_{-k}>0).  The quantitative refinement is also correct.  Compactness
of the global-minimum joint-law set and pointwise positive finite mass give a
uniform (lambda_{\rm fin}>0).  For (s_k\ge0),

\[
D_*\le C_k-s_k
=\sum_{A\ne\varnothing}p(A)(r_k(A)-s_k)
\le2R a_{-k}.
\]

For (s_k<0), all finite mass is opponent-root absorption, so it is at least
(lambda_{\rm fin}).  Hence the stated minimum of the two bounds is valid.
There are seven nonempty opponent coalitions in Fin4, giving the stated
literal atom floor.  `terminalCoalition_has_strictToggle` (or the packaged
`exists_supportedStrictToggle_of_incidence`) supplies the static strict
toggle.  The note correctly does not promote that toggle to a profitable
chronological move.

## 4. The same-target saturation re-anchor is legitimate

Take origin, hull minimum, and retained point all equal to the literal joint
target (widehat Z).  The declaration
`quittingLawTightCapNashSaturationHull_origin_mem` puts it in its own hull.
The hull is a carrier subset by
`quittingLawTightCapNashSaturationHull_subset_carrier`; global minimality of
(widehat z) therefore supplies the `debt_le` field of
`IsQuittingLawTightCapNashSaturationMinimum`.  The point lies in its own
minimum face by `minimum_mem_face`.

Now `exists_quittingLawTightResetRigidChamber` applies with source semantic
pair (widehat z), owner (k), its exact zero debt, and the positive
opponent incidence proved above.  Its returned point retains the literal law
of (widehat Z).  Thus this route does not select a new minimum law or a new
realizing source.  The alternative classification argument is consistent
with the direct theorem but is not needed.

The claim that exact cap--Nash prefixing cannot leave this positive global
minimum is also correct: total debt scales by joint Continue mass (c\le1),
while carrier minimality requires (D_*\le cD_*).  Since (D_*>0), (c=1),
so the product root is all Continue and the semantic pair and law are fixed.

## 5. Scope and export assessment

The finite transition is sound:

\[
\text{attained one-sure full-debt product minimum}
\Longrightarrow
\text{off-minimum paid target or same-target reset-rigid minimum}.
\]

It is not a terminal consumer.  In the first arm it supplies no return from
the off-minimum target; in the second it supplies no zero-preserving response
iteration.  The note states both limitations explicitly.

I found no unresolved mathematical objection.  The cap/response result is
genuinely unrestricted-behavioral, the equality re-anchor preserves the
actual joint law, and the packet is suitable for the export gate with its
ordinary-mathematics status retained.

## Lean declarations inspected

* `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
* `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
* `quittingLawTightCapNashSaturationHull_origin_mem` and
  `quittingLawTightCapNashSaturationHull_subset_carrier` in
  `LawTightCapNashSaturationHull.lean`;
* `IsQuittingLawTightCapNashSaturationMinimum.minimum_mem_face` and the
  exact-root scaling argument in `LawTightCapNashMinimumFace.lean`;
* `exists_quittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`;
* `QuittingTerminalExploitabilityWitness.terminalCoalition_has_strictToggle`
  and `exists_supportedStrictToggle_of_incidence` in the aggregate-surplus
  and reset-incidence modules.
