# Adversarial review of vanishing-Jensen clock compression

Reviewer: `JENSEN_REVIEW`

## Verdict

The vanishing-loss argument is mathematically sound after one essential
statement repair and one clarification of the reached-gain proof.

The essential repair is that (D_*) must be declared to be the global
minimum of total terminal-semantic debt on the attainable carrier (equivalently,
a lower bound for every actual component profile).  The hypothesis currently
displayed in the Question, (D(\sigma_n)\to D_*>0), does not imply

\[
D(\sigma_n^t)\ge D_*.
\]

That inequality is used in (9)--(10) and again for the marked suffix.  With
the global-minimum premise inserted, the deterministic-clock disintegration,
the Jensen identity, the weighted selection, and the constant
(\mu D_*/16) all check.

Section 4 does not establish its claimed identification with a reviewed
whole-word cap square: no four corners (U,V,X,E), transport factor (c), or
zero prescribed-payoff square are constructed from the countable clock
mixture.  The analogy should be removed or marked conjectural.  There is,
however, a direct and stronger rigorous replacement: persistent positive
Jensen loss produces a fixed-gain paid first-disagreement row on a **finite**
deterministic owner-clock component from the same source.  This remains true
when the Jensen contribution is initially concentrated on the `Never`
component.  The exact argument and constants are given below.

The repaired result is ordinary mathematics, not checked in Lean here.  It is
not export-ready: neither arm of the resulting dichotomy reaches a named
semantic consumer, and the positive-Jensen arm supplies no near-minimum,
mass-floor, return, regeneration, or descent property for its paid component.

## Claim checked, with the missing premise made explicit

Fix a finite quitting game on `Fin 4`.  For an actual behavioral profile
(\rho), write

\[
U_i(\rho)=\text{prescribed terminal payoff},\qquad
B_i(\rho)=\sup_{\delta_i}U_i(\rho_{-i},\delta_i),
\]

where the supremum is over all history-dependent behavioral deviations, and

\[
D(\rho)=\sum_i(B_i(\rho)-U_i(\rho)).
\]

The needed global premise is

\[
D_*:=\min_{z\text{ in the terminal-semantic carrier}}D(z)>0.
\tag{R1}
\]

In particular (D(\rho)\ge D_*) for every actual profile and every literal
suffix profile.  Suppose actual profiles (\sigma_n) satisfy

\[
D(\sigma_n)\to D_*,\qquad
\Pr_{\sigma_n}(Q=\{j\})\ge\mu>0
\]

for one fixed owner (j).  Disintegrate the live-path stopping law of (j)
over (x\in\mathbb N\cup\{\infty\}), with weights (\alpha_{n,x}), and let
(\sigma_n^x) replace only (j) by that deterministic finite clock or by
`Never`.  Define

\[
J_n=\sum_x\alpha_{n,x}D(\sigma_n^x)-D(\sigma_n).
\]

Under (R1), if (J_n\to0), the note correctly constructs finite clocks
(t_n) such that

\[
D(\sigma_n^{t_n})\to D_*,\qquad
\Pr_{\sigma_n^{t_n}}(Q=\{j\}\text{ at }t_n)\ge\mu/2,
\]

and, after a subsequence if a fixed player label is required, one complete
unilateral behavioral replacement with gain at least (\mu D_*/16) whose
first change is at the marked row.

## 1. Deterministic-clock disintegration and unrestricted deviations

This step is valid, but (1) must be read as equality of terminal-semantic
expectations, not as a literal vector-space equality of behavioral profiles.

Before absorption, the only public history is the all-Continue history.  The
live-path behavioral hazard of (j) therefore has a genuine stopping law on
`Option Nat`: a finite first-Quit date or `Never`.  For any fixed payoff
observer (i), and also after replacing an outsider (i\ne j) by any fixed
behavioral deviation, bounded terminal payoff is affine in this complete
stopping law.  Thus

\[
U_i(\sigma_n)=\sum_x\alpha_{n,x}U_i(\sigma_n^x)
\tag{R2}
\]

and, for (i\ne j) and every deviation (\delta_i),

\[
U_i((\sigma_n)_{-i},\delta_i)
=\sum_x\alpha_{n,x}
 U_i((\sigma_n^x)_{-i},\delta_i).
\tag{R3}
\]

This genuinely covers unrestricted behavioral deviations.  A deviation may
replace the player's entire strategy and may use arbitrarily late stopping or
`Never`; the disintegration is of (j)'s fixed opponent strategy, not of the
deviator's strategy class.  Restoring (j)'s behavior strictly after its pure
finite Quit date is harmless both prescribedly and under an outsider's
deviation, because that branch is unreachable.  Under a deviation by (j),
the entire (j)-strategy is replaced, so the stored post-date behavior is
again irrelevant.

For (j), all clock components have exactly the same opponents, hence

\[
B_j(\sigma_n^x)=B_j(\sigma_n).
\tag{R4}
\]

For (i\ne j), (R3) followed by `sup of an average <= average of sups`
gives

\[
B_i(\sigma_n)\le\sum_x\alpha_{n,x}B_i(\sigma_n^x).
\tag{R5}
\]

No stationary or bounded-controller restriction occurs here.

## 2. `Never` and the Jensen identity

The `Never` atom is handled correctly and is necessary.  The weights satisfy

\[
\sum_{t\in\mathbb N}\alpha_{n,t}+\alpha_{n,\infty}=1.
\]

Putting (s_{n,\infty}=0) is exactly right: `Never` cannot generate a
singleton-(j) terminal.  Hence

\[
\Pr_{\sigma_n}(Q=\{j\})
=\sum_{t\in\mathbb N}\alpha_{n,t}s_{n,t};
\tag{R6}
\]

there is no missing infinite-time terminal term.  The finite reward table
uniformly bounds all prescribed payoffs and caps, so the countable sums are
absolutely controlled.

Expanding (D=\sum_i(B_i-U_i)), using (R2), (R4), and (R5), gives exactly

\[
J_n=
\sum_{i\ne j}
\left(\sum_x\alpha_{n,x}B_i(\sigma_n^x)-B_i(\sigma_n)\right)\ge0.
\tag{R7}
\]

Thus equations (5)--(6) have the correct sign and contain precisely the three
outsider cap gaps.  There is no hidden prescribed-payoff remainder.

## 3. Weighted selection and constants

Let (A_n=\{x:s_{n,x}\ge\mu/2\}).  Since (0\le s_{n,x}\le1), (R6) gives

\[
\mu\le \alpha_n(A_n)+(1-\alpha_n(A_n))\mu/2,
\]

so

\[
\alpha_n(A_n)\ge\frac{\mu}{2-\mu}\ge\frac\mu2.
\tag{R8}
\]

Because (s_{n,\infty}=0<\mu/2), every member of (A_n) is finite.  Under
(R1), each excess (D(\sigma_n^x)-D_*) is nonnegative, and

\[
\sum_x\alpha_{n,x}(D(\sigma_n^x)-D_*)
=D(\sigma_n)-D_*+J_n.
\tag{R9}
\]

A weighted average over (A_n) therefore selects a positive-weight finite
(t_n\in A_n) with

\[
D(\sigma_n^{t_n})-D_*
\le \frac{2}{\mu}
  \bigl(D(\sigma_n)-D_*+J_n\bigr).
\tag{R10}
\]

The factor (2/\mu) is valid.  The sharper value available from (R8) is
((2-\mu)/\mu); nothing downstream needs that improvement.

Without (R1), (R9) still holds algebraically but the selection argument is
false: negative component excess can cancel positive excess.  This is why the
missing global-minimum premise is substantive rather than editorial.

## 4. Marked-suffix debt and reached gain

At the marked suffix of (\sigma_n^{t_n}), player (j) Quits surely at the
root, so the joint all-Continue probability is zero.  The arbitrary-root
cap--debt recursion gives

\[
D(\text{marked suffix})
=\operatorname{RootDef}(B(\text{post-tail}),q_n).
\tag{R11}
\]

The suffix is itself an actual behavioral profile.  Under (R1), its debt is
at least (D_*).  The four nonnegative coordinate root defects therefore
have one coordinate (p_n) at least (D_*/4).  A strict subsequence fixes
the player label if the output interface needs one fixed (p).

The proof must split according to whether (p=j):

- If (p\ne j), the sure quitter (j) screens the post-root tail from
  player (p)'s endpoint comparison.  The cap-coordinate root defect equals
  the prescribed-tail coordinate defect, and the canonical same-stage best
  endpoint is an exact legal behavioral deviation.
- If (p=j), the usual one-stage best-endpoint identity against the
  prescribed tail is not the needed theorem.  Player (j) must Continue at
  the marked row and then use an unrestricted behavioral response within
  (D_*/8) of the cap of the retained opponent tail.  Pure-time extremality
  allows this response even when the cap is achieved only by arbitrarily late
  finite times or by `Never`.

In both cases the conditional suffix gain is at least (D_*/8).  The live
probability of the row is at least its singleton stage mass and hence at least
(\mu/2).  Copying the original strategy up to the marked history and then
using the selected response gives the whole-profile gain

\[
(\mu/2)(D_*/8)=\mu D_*/16.
\tag{R12}
\]

Thus the advertised constant is correct.  In the outsider case the sharper
bound (\mu D_*/8) is available.  The note should cite the owner/outsider
split explicitly rather than suggesting that the prescribed-tail
same-stage endpoint identity covers both cases.

## 5. Rigorous exhaustive Jensen-loss dichotomy

Here is a direct replacement for Section 4.  It avoids any unconstructed
four-corner square.

For an outsider (i\ne j), define its Jensen contribution

\[
G_{n,i}:=
\sum_x\alpha_{n,x}B_i(\sigma_n^x)-B_i(\sigma_n)\ge0.
\tag{R13}
\]

Then (J_n=\sum_{i\ne j}G_{n,i}).  After passing to a subsequence, exactly
the following useful alternative is available.

1. If (\liminf J_n=0), pass to a subsequence with (J_n\to0).  Equations
   (R8)--(R12) give the near-minimum concentrated singleton and its marked
   reached gain.
2. If (\liminf J_n>0), choose (\kappa>0) with (J_n\ge\kappa) eventually.
   Since there are three outsiders, pass to a further subsequence and fix
   (i\ne j) such that
   
   \[
   G_{n,i}\ge\gamma:=\kappa/3.
   \tag{R14}
   \]
   
   For every such (n), there is a **finite** clock (t_n) in the positive
   support of (\alpha_n) and two pure-time deviations of (i) whose payoff
   difference on (\sigma_n^{t_n}), in one orientation, is greater than
   (\gamma/4).  Consequently
   
   \[
   \operatorname{Nonempty}
   \bigl(\operatorname{QuittingPaidFirstDisagreementRow}
     (r,\sigma_n^{t_n},i,\kappa/12)\bigr).
   \tag{R15}
   \]

### Proof of the positive-loss arm, including `Never`

Fix (n) and suppress it.  For a pure-time response (a) of outsider (i),
write

\[
v_x(a):=U_i((\sigma^x)_{-i},a).
\]

Choose a pure time (a) with source payoff

\[
\sum_x\alpha_xv_x(a)>B_i(\sigma)-\varepsilon,
\qquad \varepsilon:=\gamma/16.
\tag{R16}
\]

This uses the checked pure-time extremality of unrestricted behavioral best
responses.  Set

\[
R_x:=B_i(\sigma^x)-v_x(a)\ge0.
\]

By (R13), (R16), and source disintegration,

\[
\sum_x\alpha_xR_x\ge G_i\ge\gamma.
\tag{R17}
\]

Split (R17) into finite clocks and `Never`.

If

\[
\sum_{t<\infty}\alpha_tR_t\ge\gamma/2,
\]

some positive-weight finite (t) satisfies (R_t\ge\gamma/2).  Choose a
pure-time response (b) within (\varepsilon) of (B_i(\sigma^t)).  Then

\[
v_t(b)-v_t(a)>\gamma/2-\varepsilon>\gamma/4.
\tag{R18}
\]

This already gives the paid row on the finite component (\sigma^t).

Otherwise the `Never` contribution satisfies

\[
\alpha_\infty R_\infty\ge\gamma/2.
\tag{R19}
\]

Choose a pure-time response (b) within (\varepsilon) of
(B_i(\sigma^\infty)), and put
(\Delta_x=v_x(b)-v_x(a)).  Source near-optimality of (a) gives

\[
\sum_x\alpha_x\Delta_x<\varepsilon,
\]

while (\Delta_\infty>R_\infty-\varepsilon).  Therefore

\[
\begin{aligned}
\sum_{t<\infty}\alpha_t\bigl(v_t(a)-v_t(b)\bigr)
&=\alpha_\infty\Delta_\infty-
  \sum_x\alpha_x\Delta_x\\
&>\alpha_\infty R_\infty-2\varepsilon\\
&\ge 3\gamma/8.
\end{aligned}
\tag{R20}
\]

Hence some positive-weight finite (t) satisfies

\[
v_t(a)-v_t(b)>3\gamma/8>\gamma/4.
\tag{R21}
\]

This is the reverse orientation of the same paid comparison.  Thus `Never`
cannot trap the persistent Jensen output at infinity: aggregate optimality at
the source forces a compensating finite-clock witness switch.

Applying
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` to (R18) or
(R21) proves (R15).  No normalized-curvature or reset-square decoder is
needed.

## 6. What the strengthened dichotomy does and does not supply

The positive-loss arm is source-matched in the following exact sense:

- the owner (j), outsider (i), source profile (\sigma_n), stopping-law
  weight, finite clock (t_n), component profile (\sigma_n^{t_n}), and both
  pure-time response witnesses are retained;
- (t_n) lies in the positive support of the original owner stopping law;
- the paid row uses unrestricted-cap pure-time extremality, so arbitrarily
  late times and `Never` remain available as response witnesses.

It does **not** imply any of the following:

- (s_{n,t_n}\ge\mu/2) or any other singleton stage-mass floor;
- a positive lower bound on the component weight (\alpha_{n,t_n});
- (D(\sigma_n^{t_n})\to D_*), or even a bounded excess above (D_*) sharper
  than the ambient reward bound;
- a first-disagreement date equal to, before, or after the owner clock (t_n);
- payoff near-return, source regeneration, support/rank descent, or a terminal
  approximate Nash profile.

Persistent Jensen loss can live on clocks disjoint from the high-singleton-
survival set (A_n).  Therefore it cannot simply be joined to the vanishing
arm's mass and near-minimum conclusions.  This is the remaining consumer gap.

## Source audit

The following checked declarations and maintained boundary records were
inspected.

- `quittingBehaviorStoppingLaw` and
  `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` and
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` give the
  complete finite-time/`Never` stopping law and its payoff expectation.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` keeps
  the unrestricted behavioral cap while allowing pure finite times and
  `Never` as approximate witnesses.
- `quittingTerminalPayoff_stoppingLawMixture_eq` and
  `quittingContinuationBestResponseValue_stoppingLawMixture_le` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
  are the checked binary affine-payoff and convex-cap analogues of (R2)--(R5).
  A formalization of the present result should add the countable
  any-observer expectation form rather than iterate binary mixtures.
- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`
  is the arbitrary-root recursion used in (R11).
- `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`
  verifies the exact reached-row gain for the outsider case.
- `minimumDebt_sub_observerDebt_div_reachFloor_le_sum_other_reachedDefect` and
  `exists_fixed_other_reachedRowGain_subsequence` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`
  confirm the existing sure-quitter localization interface and also show why
  its public theorem is phrased for a non-observer; the owner case here needs
  the separate cap-tail response described above.
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
  consumes the positive pure-time edge in the persistent-loss arm.
- `FIN4_ATLAS_CONCENTRATED_SINGLETON.md` and
  `FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md` were checked for the named live
  obligations.  The former still requires a semantic consumer or
  source-preserving descent; the latter has already been contracted by the
  checked clock-compression route.

## Requested revisions

1. Add (R1) explicitly to the theorem statement and define (D,U_i,B_i).
2. Replace the literal profile notation in (1) by semantic expectation
   equalities, while retaining the exact component profiles as data.
3. State that a strict subsequence is taken when the reached-gain player is
   fixed.
4. Split the reached-gain proof into (p=j) and (p\ne j), since only the
   latter is the direct prescribed-tail best-endpoint identity.
5. Replace Section 4 by the finite-clock paid-row dichotomy (R13)--(R21), or
   else downgrade the whole-word-square paragraph to an unproved analogy.
6. Keep the result internal.  The new paid row is exact and potentially
   useful, but there is still no named adapter/consumer that converts every
   branch into return, descent, terminal approximation, or uniform payoff.

## Export assessment

The note does not pass the export gate in its current form.  After the above
repairs, it would be a rigorous conditional contraction, but it still would
not answer an accepted arm of `FIN4_ATLAS_CONCENTRATED_SINGLETON.md`: the
vanishing-Jensen hypothesis is not produced for arbitrary source data, and
the complementary paid row has no near-return or recursive consumer.  No
export or frontier seal is recommended.
