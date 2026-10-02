# Adversarial audit of joint exposure--incentive selection

Reviewer: `SINGLETON_INCENTIVE_AUDITOR`

## Claim checked

The note selects one owner completion which simultaneously has large
singleton exposure and controlled owner debt.  It also gives the complementary
high-exposure/low-exposure payoff polarity, applies the selection along a
minimum-source chronology, and claims sharpness through an exact two-player
example.

## Verdict

The mathematical statements are correct, including the positive-anchor
correction and the all-behavior cap interpretation.  The inactive-owner
endpoint really does co-realize fixed singleton mass, vanishing owner debt,
and a full-gap paid row for a fixed nonowner whose first disagreement is no
later than the selected deadline.

This does **not** pass the export gate.  The Fin4 singleton leaf does not imply
that its singleton owner is inactive at the minimum, and neither arm of the
unconditional polarity dispatch has a consumer controlling the other
coordinates' unrestricted caps.  The result therefore strengthens a
source-attached endpoint passport but does not strictly contract
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` under its stated acceptable
answers.

## Abstract inequality

Let `H={t:s_t>lambda}` and `w=pi(H)`.  From

\[
0\le s\le p,\qquad E[s]=\mu,
\]

one obtains

\[
w\ge {\mu-\lambda\over p-\lambda}>0.
\]

Since `E[Y]=0` and `Y<=d`,

\[
E[Y1_H]=-E[Y1_{H^c}]\ge-d(1-w).
\]

Countable support causes no attainment problem here: if every supported
member of `H` were strictly below the displayed conditional-average bound,
the positive weighted sum of the strict deficits would be positive.  Hence
some supported `t in H` satisfies

\[
Y_t\ge-d{1-w\over w}
\ge-d{p-\mu\over\mu-\lambda}.
\]

Adding `d` gives the stated debt factor

\[
d-Y_t\le {p-\lambda\over\mu-\lambda}d.
\]

No lower bound on `Y` is being smuggled in; integrability is enough to justify
the restricted expectations.

## Positive-anchor stopping-law mixture

Condition on the owner's own clock surviving to the anchor.  For every
conditional finite deadline, and for Never, form a whole completion which
copies the source before the anchor and every opponent, then uses that
conditional deadline.  Mixing these completions by the conditional stopping
law reconstructs the owner's complete stopping law.  It need not reconstruct
the behavioral strategy on zero-reach histories, but terminal payoff and the
terminal law depend only on the reconstructed stopping law, which is exactly
what the proof uses.

Thus the whole-completion gain

\[
Y_t=U_j(\tau_t)-U_j(\sigma)
\]

has conditional mean zero.  This would be false for the raw tail pure-time
gain at a positive anchor.  The exposed singleton stage mass `beta_t` is
bounded by the owner's anchor-survival probability `p_a`, and its conditional
mean is the source singleton mass after the anchor.  Since only the owner's
strategy changes,
`quittingContinuationBestResponseValue_update_self` makes its full behavioral
cap invariant, so the target owner debt is exactly `d-Y_t`.

This validates the coefficient

\[
d_j(\tau_t)\le {p_a-\lambda\over m-\lambda}d_j(\sigma).
\]

The argument includes Never and arbitrary infinite-support stopping laws; it
is not a stationary or bounded-deadline reduction.

## Exposure--payoff polarity

If every supported high-exposure completion has gain at most `-kappa`, zero
mean forces positive conditional average on the low-exposure set.  The same
bound on `w` gives a supported low completion with gain at least

\[
\kappa{\mu-\lambda\over p-\mu}
\]

when `p>mu`.  If `p=mu`, the exposure equals `p` almost surely and a
high-exposure completion has nonnegative gain, so this adverse arm cannot
occur.  Conditioning the stopping law on the high and low sets gives the
literal same-opponents whole-law chord claimed in the note.  Other players'
caps are only convex along this chord, so it yields no signed total-debt
curvature.

The cofinal dichotomy is also valid.  Approximate maximizers suffice when the
high-exposure gain supremum is not attained.  If its limsup is nonnegative,
they give owner debt at most source debt plus `o(1)`.  If the limsup is
negative, one fixed `kappa>0` gives a low-exposure completion with a fixed
owner payoff gain.  Own-cap invariance gives exact owner-debt subtraction,
and global minimality gives

\[
\sum_{i\ne j}(d_i(\rho_n)-d_i(\sigma_n))\ge g-o(1).
\]

This last inequality is a leakage account, not a descent: it says the other
coordinates must absorb essentially the drained debt.

## Inactive-owner paid-row localization

If the selected owner's debt at the minimum is zero, coordinatewise exact
cap-stack scaling and convergence to the minimum make the reference owner
debt vanish.  The bounded selection factor then makes the compressed target
owner debt vanish too.

Under a terminal gap `gamma`, that owner cannot be the profitable coordinate
once its debt is below `gamma`.  The support-pair decoder therefore selects a
full-gap paid row for a nonowner.  If its two pure-time witnesses first
disagreed strictly after the compressed owner's forced deadline, they would
agree through a date at which the owner Quits surely whenever play remains
live.  They would induce identical outcomes pathwise, contradicting positive
gain.  Hence the paid row starts no later than the selected deadline.  Finite
player pigeonhole fixes the nonowner along a subsequence.

## Sharp regression

In the two-player example, the owner's deadline-zero payoff/exposure pair is
`(0,1)` and its deadline-one pair is `(d/w,lambda)`.  The prescribed singleton
mass is

\[
w+(1-w)\lambda=\mu,
\]

the cap is `d/w`, the prescribed payoff is `(1-w)d/w`, and the debt is exactly
`d`.  Date zero is the only deadline with exposure strictly above `lambda` and
has gain

\[
-{1-\mu\over\mu-\lambda}d.
\]

Thus the constant and the adverse exposure orientation are sharp in an
actual finite quitting game.  The all-Never equilibrium correctly limits its
scope: this is a regression against a stronger inference, not a positive-gap
example.

## Source audit

The audit used the following checked declarations and their exact scopes:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingContinuationBestResponseValue_update_self` and
  `quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `QuittingPaidFirstDisagreementRow.gain_le_liveMass` and
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- the chronology and exact mass transport in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`.

The existing Research clock-compression theorem is probability-law only and
does not contain this incentive-aware weighted selection.  Thus the local
mathematics is new relative to the named checked interface.

## Precise missing consumer

An export would require one of the following additional theorems:

1. consume the inactive-owner passport

   ```text
   fixed singleton mass
   + vanishing owner debt
   + temporally localized full-gap nonowner paid row
   + literal source tail
   ```

   into terminal approximants, a charged admissible return, or a regenerated
   minimum-fiber support drop; or

2. consume the unconditional polarity arm by controlling the cross-coordinate
   cap leakage, turning the exposure-reversing owner transfer into a renewable
   response/curvature square or a well-founded source-preserving descent.

Without such a theorem, export would be another producer with an unconsumed
residual, which the concentrated-singleton question explicitly excludes.

## Recommendation

Retain and, if useful, formalize the generic sharp selection theorem and its
two-player regression in `Research`.  Do not export the packet yet.  Revisit
the gate only after the localized paid-row passport or the complementary
transfer has a complete semantic consumer.
