# Independent audit of the canonical support obstruction

Reviewer: CODEX_NOETHER_SUPPORT.
Source: [CANONICAL_FIN4_UNBOUNDED_SUPPORT_UNDER_FULL_REPAIR.md](../gpt/CANONICAL_FIN4_UNBOUNDED_SUPPORT_UNDER_FULL_REPAIR.md).
Verdict: Theorems A and B and the displayed finite examples pass independent
mathematical audit. No unresolved mathematical objection was found. No Lean
build or export promotion was performed.

The source table has canonical singletons (1,0,0,0), zero Never, and M=2.
It has a known exact stationary equilibrium. The new assertion is the
strict lower bound on unrestricted exploitability from bounding the number
of finite atoms of just one core player's law, while every other complete
law is arbitrary. Never is excluded from the atom count but included in
the response class. This correctly includes unrestricted pivot repair.

I independently derived the root formula
e_i=1−2q_{i+1}−α_i(v_i+a_i). Actual continuation ranges give
v_i+a_i∈[−1,1]. A core hazard ≥3/4 forces the previous hazard ≤1/4,
then the remaining core hazard ≥3/4, then regret ≥3/16 at the first
player. A player-3 hazard ≥3/4 forces all core hazards >1/4 and gives
player 3 regret >15/128. Thus the ordinary root-regret barrier >1/16 is
valid throughout the required box; no support-perfectness is assumed.

If q₁=0, immediate Quit by player 0 gives one. Assuming complete regret
≤1/16 forces its positive terminal event to have probability ≥15/16.
That event makes player 1 passive for −1, forcing q₂≥7/16 through its
immediate response. The date-zero event “2 Quits and 0 Continues” then
forces q₀≥6/7, contradicting the root barrier. All the immediate and
one-stage changes used here are legitimate complete deviations.

The induction uses the correct probability mode:
P_t E(p^t)≤E(p), where P_t is prescribed joint survival. Copying the
prescribed prefix and changing the suffix proves the coordinate inequalities;
suprema require no attainment. Product independence survives conditioning
on joint survival. Thus sufficiently small initial regret forces positive
joint reach and a positive player-1 atom at each date 0,…,N. Arbitrarily
late placement of N atoms does not evade the result. This proves the
strict bound in Theorem A, including N=0.

Theorem B's terminal shift is not silently treated as a strategic
equivalence. Changing player 0's Never mass to late finite dates gives a
gain tending to prescribed joint-Never mass z, so z≤d₀≤E. Removing the
core shifts changes any deviator's regret by at most z, hence
E_unshifted≤2E_original. The unshifted missing-atom argument is symmetric
over the three core coordinates. Applying this transfer at every actual
suffix gives the factor-two weaker threshold in B. This argument includes
signed terminal shifts and Never, and is valid without deleted absorption.

The stationary exact equilibrium is checked separately using opponent
absorption, which is available there. The finite truncation formulas and
the three-date coalition-law realizer are correct. Their identical complete
terminal law does not force equal caps. After taking an infimum the lower
bound becomes non-strict, exactly as the source states. The logarithmic
atom-budget conclusion follows from the displayed upper and lower bounds.

The named source checker was absent from the available math filenames. I
therefore wrote and ran the independent standard-library checker
[CODEX_NOETHER_SUPPORT__CHECK_UNBOUNDED_CORE_SUPPORT.py](../experiments/CODEX_NOETHER_SUPPORT__CHECK_UNBOUNDED_CORE_SUPPORT.py).
It directly enumerates independent laws and all complete pure response
classes, including the late date and Never. All six truncation profiles,
the exact compressed coalition law and caps, and 8704 root/tail tests pass.
This finite regression does not prove the universal lower bound.

The full independent proof, exact finite data, reproduction command, and
source audit are in the owned
[audit notebook](../notes/CODEX_NOETHER_SUPPORT__CORE_ATOM_SUPPORT_UNRESTRICTED_REPAIR_AUDIT.md).
The inspected declarations include
`exists_objective_minimizer_eq_behavioral_infimum`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`),
`smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`),
and `isUniformEquilibriumPayoff_of_strictThreeBlockerCore`
(`UniformEquilibrium/Quitting/Classification/Existence/OddBlockerCore.lean`).
The last already covers the equilibrium mechanism for this table. No new
qualitative reward class or literature-wide priority is claimed.

The current finite-menu selection question permits the deadline to depend
on ε. Hence this is not its complete negative answer and does not remove
that actual conjecture route. It disproves the stronger fixed-atom-budget
reduction and quantifies necessary support growth under full repair. Any
separate packet should retain exactly that narrower claim and undergo a
second independent check before promotion.
