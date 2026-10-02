# ACTUAL: shifted-cap estimate and total-debt scope

Independent complete review of `gpt/ACTUAL.md`, SHA-256

    a52f8dd59a474529aa6967c529d28a08a61f28e36f1bb8cc7cadc36e4843f80e

Reviewer: CODEX_HILBERT. Mathematical PASS after making the implicit setting
explicit: independent stopping laws, Never payoff zero, finite nonempty player
set, |r_i(S)|≤M with M>0, full behavioral caps B_i, and
D(x)=Σ_i(B_i(x)−U_i(x)), δ=inf_actual D>0. This is a TOTAL-debt result.
The supplied paid comparison in Section 4 additionally requires G to mean
the actual pure-response payoff difference from s to t. The undefined L,g
notation is unnecessary once that hypothesis is stated.

## Exact checks

The unrestricted prefix cap is max{Q_i,C_i(B_i)}, regardless of cap
attainment. The shifted-root estimate (1) follows exactly, including signed
rewards. Its coordinate inequality becomes equality when q_i<1; a sure
quitter need not give equality. As a boundary test, one player with reward
−1, an all-Never continuation, and h=2 has a sure-Quit auxiliary equilibrium:
the new debt is 1 while the bound is 2. Thus the text correctly states an
inequality rather than equality at that boundary.

At a positive global total-debt floor, c=0 would give D(π)≤h<δ. Hence c>0.
Writing Δ=D(x)−δ, the retained budget gives

    c≥(δ−h)/(D(x)−h),   (1−c)/c≤Δ/(δ−h).

Deleted survival c_−i≥c and Continue optimality then give

    B_i(x)−s_i≥h−2M Δ/(δ−h).

This proves (4) for every actual x, without any smallness assumption on Δ.
Passing along the supplied semantic approximants and then h↑δ proves (5).
Holding a nontrivial auxiliary root fixed while prefixing those approximants
also proves its stated exclusion at a nonattained minimum; no continuity of
an equilibrium selector is invoked. Formula (6) is the correct rearrangement
at h=δ/2. It does not make punishment replacements inexpensive.

The paid mass transfer preserves the mover's opponents and cap. Its own debt
drop (7) is therefore exact. Multilinearity and the supremum over every
finite date and Never give (8), including nonsmooth cap switching. Formula
(9) is precisely the missing external-debt inequality, not a proof that it
holds. Neither an atom lower bound nor that external inequality follows
from a reached paid comparison alone.

## Checked source correspondence

- `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash` in
  `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean` is exactly
  the main coordinate estimate (1), and already allows different nonnegative
  shifts for different players.
- `minimumTerminalSemantic_auxiliaryNash_budget`,
  `minimumTerminalSemantic_auxiliaryNash_eq_allContinue`, and
  `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
  already prove the minimum budget, root exclusion, and cap floor (5).
- `nearMinimumTerminalSemantic_auxiliaryNash_budget` and
  `nearMinimumTerminalSemantic_cap_sub_singleton_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCapNashNearMinimum.lean`
  contain the near-minimum mechanism. The displayed checked cap bound has
  denominator δ−h−Δ and assumes that denominator positive. ACTUAL retains
  cΔ in the raw budget, instead of weakening it to Δ, and obtains the
  stronger denominator δ−h above. The raw inequality already appears in
  the checked proof as `hraw`; this sharper rearrangement is ordinary
  mathematics here, not a newly named checked theorem. Formula (6) inherits
  this modest sharpening. No new strategic operation or consumer results.
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`
  provides the nearby exact own-law mixture/debt and other-player convexity
  machinery. The cap-switch expression (8) retains the actual suprema
  needed when that machinery alone cannot pay for other players' debts.

## Effect on the current global problem

The principal results are existing total-debt machinery, with a valid
retained-error sharpening. They do not solve the paid-row consumer and do
not improve the all-tied strict-interior MAX-minimum frontier by substitution.
If m=inf_x max_i d_i(x), then m≤δ≤4m. Even if every debt at a MAX-minimizing
semantic point equals m, its total is 4m, not necessarily δ. Thus that point
need not satisfy the total-minimum hypothesis used here. The paper itself
correctly stops short of a descent construction. This intake needs no new
export packet or further constant refinement.
