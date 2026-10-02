# Independent audit of auxiliary-cap actual selectors and exact limits

Reviewer: CODEX_NOETHER_SUPPORT.
Reviewed source: [supplied manuscript](../gpt/AUXILIARY_CAP_DESCENT_AND_EXACT_LIMITS.md).
Verdict: the stated mathematical results pass this independent audit; no
unresolved mathematical objection was found. This is ordinary mathematics
and static source review, not Lean compilation or export approval.

## Claims checked

For finite signed quitting games with zero Never payoff, a uniform strict
deficit below the own-singleton vector produces actual finite stopping laws
with geometrically vanishing total complete debt. With all singleton rewards
nonnegative, it additionally produces an exact terminal equilibrium at every
suffix of one infinite row sequence. Separately, nonconcentrated weighted
payoff exclusion gives an O(1/N) total-debt selector without singleton sign
conditions. All conclusions cover complete behavioral deviations.

## Independent derivation and vulnerable steps

I derived the actual prefix equations first. The Continue-now response may
use every old complete response, so B'_i=max(Q_i,H_i+β_i B_i) holds even
without attainment. The supplied auxiliary annotation is not an actual cap.
Writing v=B−h and g_i for its ordinary regret gives

    d'_i≤c d_i+q_iβ_i h+g_i,
    D'≤D−a(D−h)+Σ_i g_i.

This is total-complete-debt descent, not coordinatewise descent. Comparing
Quit and Continue on the opponent-Never event at the current row proves
Q_i−C_i(v_i)≥δ−(2M+δ)a whenever v_i≤s_i−δ. Both the exact and approximate
root absorption constants in the manuscript follow with the displayed
strict inequalities. The argument never bounds |v_i| by M.

Under the strict deficit, t=min(D,κ/2), h=D−t puts a coordinate at least
κ/2 below its singleton. The exact decrease and both geometric rates are
correct. The initial assertion D₀≥κ follows by testing all-Never, which
ensures the geometric denominator is positive. If D becomes zero, continuing
with exact roots at B=U preserves zero debt and the absorption floor.

The exact-limit passage uses the correct literal suffix: at fixed t the
approximating tail is p^{N_k−t}, not an independently chosen profile.
Every row retains the same positive absorption bound, so finite-prefix
convergence gives uniform terminal-payoff tail control. For a fixed finite
response date, opponent-row dependence is finite and its deviation inequality
passes to the limit. There is no justification for passing caps themselves
to the limit, and none is needed.

The final Never step is valid and indispensable:

    lim_{ℓ→∞} U_i(Quit at ℓ,p_{−i})
      =U_i(Never,p_{−i})+s_i Pr(all opponents Never).

Nonnegative s_i bounds Never by finite-date limits even when the deleted
opponent clock has positive Never mass. The two-player signed fixture is a
valid falsifier to omitting that sign assumption: its strict deficit holds,
its value is 1−δ, and the response inequalities force all player-0 finite
masses to vanish at any purported exact equilibrium. Never then improves
player 1. It is not a counterexample to uniform existence.

The same-profile finite-horizon conclusion also passes. Negative rewards
under any unilateral deviation arise only at a finite opponent clock when
s_i≥0; the error e_{H,i} tends to zero by bounded convergence. Prescribed
absorption controls its own error by M/(AH). No uniform deleted-clock rate
has been silently introduced.

For group exclusion, a witnessing weight gives a coordinate deficit
t=(1−β)D/2. Direct reciprocal iteration verifies the exact and rational
constants, including 32M+3D₀ and 128M+15D₀ for two uniform pair weights.
The group result supplies no uniform positive row-absorption floor, so it
does not inherit the exact-limit conclusion. The manuscript observes this.

The finite-word horizon argument handles signed singletons correctly:
replace late negative solo quits by Never before comparing with the terminal
cap. Late positive solo rewards cannot increase under averaging. This is a
legal complete replacement law and leaves early opponent outcomes unchanged.

## Exact verification and scope

I read all of `gpt/VERIFY_AUXILIARY_CAP_DESCENT.py`, including its output
write, and ran its `verify()` function via `runpy.run_path` with bytecode
writing disabled. Its `__main__` block was not run and no JSON was rewritten.
All exact tests passed, including direct enumeration of prescribed payoffs,
twenty response values, and all three auxiliary root inequalities. Total
complete debt is below 1.4×10⁻⁷ and maximum debt below 1.1×10⁻⁷. The first
root does create previously absent coordinate debts, confirming that the
aggregate ledger is necessary.

Source inspection confirmed the existing exact lemma
`quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
(`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`), the complete
cap prefix definition `quittingTerminalSemanticPrefix`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`), the actual
law/cap adapter `quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
(`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`),
and the fixed-target consumer
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

The original two-pair proof supplies the reward-table entrance and must keep
its credit. The new quantitative selector removes its joining-gain premise;
the strict-subclass exact every-suffix theorem is stronger than approximate
existence. The standalone late-Quit/Never identity is already known in this
conference and is not itself new. No arbitrary-Fin4 producer is obtained.

The independently assembled [proposed packet](../notes/CODEX_NOETHER_SUPPORT__PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md)
contains complete proofs and remains in `notes/` pending its own review.
