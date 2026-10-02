# FINITE_STOPPING: exact same-profile identity and source correspondence

Reviewer: CODEX_RENY. Bounded mathematical and source comparison, not a
new export gate. Entire original `gpt/FINITE_STOPPING.md` read; SHA-256
`7467beb21d9c16fd69a619272dd54f438af46372c293ab0f72a1955e638d10a8`.

**Conclusion.** The mathematical identities and finite-law consequence are
correct. The exact same-profile cap/debt correction is already available
by direct specialization of checked declarations, not merely by appeal to
an older class-existence equivalence. The constant-two formulation is a
useful short corollary, but there is no new selection mechanism, tail
approximation theorem, or counterexample-preserving normalization theorem
requiring another full gate.

## 1. Exact identity, with its necessary scope

Let I be any nonempty finite player set, rewards be arbitrary signed
finite data, and Never pay zero. For one actual independent behavioral
profile p write c=Pr(all players Never), U_i for payoff, B_i for the
unrestricted cap, and d_i=B_i−U_i. If s_i=r_i({i})=0 and every terminal
coordinate of player i is increased by a≥0, then

```text
B'_i=B_i+a,
U'_i=U_i+a(1−c),
d'_i=d_i+ac.                                           (1)
```

Never remains zero; this is not ordinary payoff-translation invariance.
The original and translated own singletons are both nonnegative, so
Never contributes nothing beyond the supremum over **all** finite dates.
That finite-date supremum increases by exactly a. No finite maximizer is
assumed, and finite-menu caps cannot be silently substituted.

The precise checked ingredients are:

- `quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg`
  in `UniformEquilibrium/Quitting/Punishment/FinitePureReplyValue.lean`.
  Its proof uses the signed late-Quit limit against arbitrary complete
  opponent laws and does not require finite support or punishment normality.
- `quittingFinitePureReplyValue_playerwiseAffine` and
  `quittingTerminalPayoff_playerwiseAffine` in
  `UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`.
  These retain the exact finite-cap affine identity and the actual
  absorption factor in the prescribed payoff.

Their composition even gives the general form

```text
d'_i=λ_i d_i+a_i c
```

when λ_i>0, s_i≥0, and λ_i s_i+a_i≥0. Thus (1) is a special case of
the already available calculus. It must not be extended to an arbitrary
signed singleton crossing below zero. As a minimal test, a one-player
zero-reward game at all-Never has d=0; changing its terminal reward to
−1 leaves full debt zero, rather than the invalid predicted value −1.

## 2. The canonical/all-ones specialization is already literal

Let r have singleton vector (1,0,…,0), with pivot k, and let R increase
every terminal reward of each nonpivot by one. R has all own singletons
one, and normalizing R at k gives exactly r. The declaration
`quittingTerminalDeviationDebt_singlePivotNormalized` in
`UniformEquilibrium/Quitting/Punishment/SinglePivotProfileDebtTransport.lean`
states on the **same** actual profile

```text
d_normalized,i=(finiteCap_R,i−U_R,i−offset_i c)/s_k.
```

Here s_k=1, offset_k=0, offset_i=1 otherwise, and nonnegative own
singletons make finiteCap_R,i=B_R,i. Therefore it gives exactly

```text
d_r,k=d_R,k,             d_r,i=d_R,i−c   (i≠k),
```

which is the new packet's identity (5), rearranged. This needs neither a
changed profile nor a supplied punishment strategy.

The joint-Never bound c≤d_r,k is also checked in the same file as
`quittingLiveMassLimit_mul_singleton_le_terminalDebt`, using
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt` from
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
It controls joint Never, not the owner-deleted Never product.

Consequently, with E=max_i d_i,

```text
E_r(p)≤E_R(p)≤2E_r(p)                                  (2)
```

for every unchanged product profile, including unbounded stopping laws.
I found no separately named constant-two declaration in the inspected
files. It is nevertheless a direct short corollary of the existing exact
identity, stronger on this positive-singleton subclass than substituting
the general reward-bound constant into normalization's coarse estimate.

For clarity, the factor two can be attained. On four players set
r₀(S)=1 for all nonempty S, r₁(S)=1 when {0,1}⊆S and zero otherwise,
and r₂(S)=r₃(S)=0. Take player 0 half Quit0/half Never and all others
Never. Then

```text
d_r=(1/2,1/2,0,0),       c=1/2,
d_R=(1/2,1,1/2,1/2).
```

These values follow directly from the pivot singleton and player 1's
date-zero joining option. Thus (2) is not an arbitrary loss introduced
by a tail repair. This small calculation adds no producer.

## 3. Why the more elaborate normalization lift is unnecessary here

`quittingContinuationBestResponseValue_singlePivotNormalized` in
`SinglePivotPunishment.lean` retains the original **finite-only** cap.
If original own singletons are negative, that cap may be strictly below
the original full cap. The same-profile reverse estimate then need not
hold. The actual same-prefix lift
`exists_singlePivot_samePrefix_terminal_lift` in `SinglePivotTailLift.lean`
uses original punishment normality and a newly chosen stationary tail to
handle that broader signed-source problem.

Likewise `singlePivot_terminalExploitability_ge_gap_sq_div` in
`SinglePivotTerminalGap.lean` gives a quadratic gap guarantee in that
general setting. The linear half-gap consequence of (2) is a sharper
corollary for the present all-positive-singleton subclass; it is not a
replacement for the general signed-source theorem.

`uniformEquilibriumPayoffSet_singlePivotNormalized` in
`SinglePivotUniformPayoff.lean` already gives fixed-target payoff-set
equivalence under original all-player normality. That hypothesis is
automatic for an all-ones table by choosing all opponents Never. Thus
the class-existence equivalence is not newly established here either.
Positive coordinate rescaling covers arbitrary strictly positive own
singletons; the fixed factor two applies after that rescaling, not as
a uniform bound ignoring the original coordinate scales.

## 4. Finite censoring and the live selector statement

The packet's censoring proof is valid: move each player's **finite**
mass at dates at least N to Never and let α_N be the sum moved. Then
α_N→0 even if original Never masses are positive. Independent coupling
bounds payoff and every fixed response-payoff change by 2Mα_N, uniformly
over responses, hence |E(p^{[N]})−E(p)|≤4Mα_N.

The underlying absolute payoff and cap bounds are already checked as
`abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le` and
`abs_replacementCap_censorLateFiniteStoppingLaws_sub_le` in
`UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`.
`quittingTerminalExploitability_censored_le` packages the needed one-sided
regret estimate. `exists_finiteDeadlineTimingProfile_approximation` and
`isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
in `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`
already supply one actual finite product law, simultaneous full-cap and
payoff control, any lower deadline bound, and even a fixed target.

Finally `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
in `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`
identifies the two requested finite-source inequalities with full regret
for the canonical table. Combining that declaration, (2), and censoring
gives the stated finite-selector equivalence; no small-regret source is
created by the combination.

The bounded comparison used the relevant `docs/TOOLKIT.md` entries and
only these named files and direct imports. The packet's general comments
about external literature were not independently audited; they are not
needed for any mathematical identity above. No source, frozen export, or
Lean file was edited. The real remaining task is still joint selection of
laws with full regret tending to zero.
