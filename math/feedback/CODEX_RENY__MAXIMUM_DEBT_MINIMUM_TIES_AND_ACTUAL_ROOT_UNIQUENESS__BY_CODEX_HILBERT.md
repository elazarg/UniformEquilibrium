# Independent check of maximum-debt ties and actual-payoff root uniqueness

Reviewer: CODEX_HILBERT. Ordinary mathematical review, not a Lean check.

Reviewed the entire
`notes/CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md`,
SHA-256

    6790f3932c73783777ab13ec6f8b2e97dd3b1288692ad1194d587cb57f99b410

**Verdict: PASS.** There is no unresolved mathematical objection to its two
compact-minimum assertions or its geometric-minimum correspondence. The
claims retain arbitrary signed rewards, all finite nonempty player sets,
Never=0, unrestricted deviations, and potentially nonattained carrier
minima. They do not imply zero minimum debt.

## 1. Maximal debts must tie

The near-response is an actual complete law, with residual error ε_n→0;
it need not attain the cap. Mixing it into the uniquely maximal debtor's
law with one fixed small θ gives exact own-debt contraction and at most
4Mθ additional debt on every other coordinate. Choose θ below the fixed
strict gap to those other coordinates. On a realizing sequence of actual
profiles, all limiting upper bounds are then strictly below the minimum.
Finiteness permits taking the maximum of these strict bounds. The repaired
profiles need not have convergent laws or semantic pairs.

The same argument rules out a positive minimum with one player: omit all
other-coordinate inequalities. No hidden two-player assumption is needed.

This assertion and its nonattainment handling were previously proved in
Section 11 of the owned mathematical note
`CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md`. The present
proof is a valid independent derivation, not a new claimed repository
declaration or a use of the separate finite-clock two-full-gap cosource.

## 2. Every absorbing actual-U root is excluded

For a fixed root q, the complete semantic prefix map is continuous and
preserves the closure of actual semantic pairs. This fact does not require
q to be Nash against approximating payoff vectors U_n. Nash against the
limiting U suffices to obtain, at the prefixed pair,

    0≤d'_i≤c_i(q)d_i,        c_i(q)=∏_(j≠i)(1−q_j).

If q has at least two positive Quit coordinates, every c_i<1. With m>0
and finitely many players, the new maximum is strictly below m. If q has
only one positive coordinate k, all j≠k have d'_j<m. Minimality forces
d'_k=m, creating another global minimum with a unique maximal debtor.
Section 1 excludes it. Exact finite-game Nash existence then supplies the
remaining all-Continue root and proves its uniqueness.

This is stronger than merely U≥s or existence of an all-Continue root.
It closes the critical-shift boundary h=B−U where some h_i=m, which the
strict auxiliary-shift uniqueness theorem does not directly cover.

## 3. Geometric minima converge to the actual global value

Every relaxed geometric optimizer lies in the actual semantic carrier:
positive first-atom implementations preserve U exactly and converge in all
cap coordinates by their finite endpoint formulas. This is not convergence
of their stopping laws to a realizing boundary law.

Conversely, start with any actual profile p and move each nonpivot's finite
mass after N to Never. The sum ε_N of these changed masses tends to zero
even when original Never masses are positive. Independent coupling bounds
the changes in every prescribed payoff and in every fixed unilateral
response payoff by 2Mε_N. For a deviator whose own law was truncated, its
cap simply ignores that own-law change; the same total bound remains valid.
Taking response suprema gives full regret at most E(p)+4Mε_N.

Geometric compression of the remaining pivot preserves U and cannot
increase any cap. Hence m≤m_N≤E(p)+4Mε_N, with the upper bound understood
for the constructed competitor. Taking N→∞ and then the infimum over p
gives m_N↓m. Every full semantic cluster of optimizers is consequently a
global MAX minimizer. Bounded caps also permit extending a prescribed-payoff
cluster to a full semantic cluster along a subsequence.

Applying Sections 1–2 afresh at that genuine global minimum proves exact
root uniqueness at the cluster payoff. This correctly avoids the invalid
inference from vanishing source-root absorption through a possibly
non-lower-hemicontinuous equilibrium correspondence.

## 4. Source and scope check

The following exact declarations were inspected in place:

- `quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` and
  `quittingTerminalSemanticDebt_stoppingLawMixture_le_boundChord` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
- `quittingTerminalDeviationDebt_rootThenContinuation_le` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
- `continuous_quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `minimumTerminalSemantic_exploitabilitySingletonMargin`,
  `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`, and
  `minimumTerminalSemantic_exploitabilityIs_allContinuePlateau` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The inspected MAX declarations establish the margin and all-Continue
existence, with uniqueness for strictly subcritical shifts. The supplied
proof gives actual-U uniqueness at the boundary, using the two-tie fact.
The nearby minimum-SUM results do not justify replacing their objective by
MAX, and this review makes no exhaustive novelty claim.

The result does not establish strict U_i>s_i, an open unique-root tube,
positive absorption near the minimum, or an actual regret-lowering move
inside the all-Continue region. Those remain separate producer questions.
