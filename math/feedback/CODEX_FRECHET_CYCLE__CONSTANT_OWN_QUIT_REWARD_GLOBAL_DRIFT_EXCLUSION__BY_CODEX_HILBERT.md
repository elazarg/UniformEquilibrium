# Constant own-quitting rewards: source coverage and bounded proof check

Reviewer: CODEX_HILBERT.

Reviewed complete source:
[CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION.md](../notes/CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION.md),
SHA-256 `15ecd111e19db25c6ad19f591efc446522d88a49f92227dfe477d073c883fd53`.

Verdict: PASS for the bounded mathematical and source-coverage check. No
correction is required. The canonical family is not new UE coverage. The
independent C¹ drift-exclusion proof is valid and is not merely a unit-solo
theorem quoted under the wrong normalization.

## Exact ordinary-mathematical coverage

The existing theorem covers the following larger boundary class by elementary
transport. Let I be finite and nonempty, Never pay zero, and put s_i=r_i({i}).
Assume

    s_i≥0,    r_i(S)≤s_i whenever i∈S.

Rewards of nonmembers may be arbitrary signed reals. For t>0 define

    r^t_i(S)=r_i(S)+t,       d_i=s_i+t>0,
    hat r_i(S)=r^t_i(S)/d_i,

on nonempty coalitions only; keep Never at zero. The normalized table has
own singletons one and quitter rewards at most one. For an original target
error γ>0, choose η=γ/2, t=γ/4, and request normalized terminal error
η/max_i d_i from the checked unit-solo/capped-joint-exit theorem.

Positive coordinate scaling transports every unilateral behavioral payoff
difference exactly, so the same stopping laws have regret at most η in r^t.
For EVERY complete profile σ, including every unilateral replacement,

    U_i(r^t,σ)−U_i(r,σ)=t Pr_σ(absorption)∈[0,t].

The safe two-sided comparison therefore gives every original full regret
at most η+2t=γ. This is uniform over all behavioral deviations, all finite
dates, Never, and all profile absorption probabilities. No finite cap
attainment or small Never mass is assumed. Normalization may create large
nonmember rewards as t decreases; the checked class theorem puts no fixed
bound or sign condition on those entries.

These profiles may vary freely with γ. The checked terminal-all-errors
selection theorem then supplies ONE fixed uniform-equilibrium payoff, not
merely a succession of terminal payoff vectors. Using the stronger cyclic
source also retains its periodic roots and terminal approximate equilibrium
at every suffix for each fixed γ; no uniform period bound follows.

This covers the canonical constant-own-reward class, and more generally the
displayed nonnegative-singleton weak-solo class, for every finite player
set. It does not use the Fin4 polynomial alternative. It does not cover
arbitrary signed singleton levels by the same small-t argument, since
s_i+t need not be positive.

The terminal shift is NOT a strategic affine equivalence with Never fixed
zero. At the all-Never profile it changes payoff by zero; at a sure finite
quit it changes payoff by t. The proof charges this difference. Only the
subsequent positive scaling is an exact payoff-difference transport.

## Named declarations and what remains unassembled

The definitions read in `UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`
are `QuittingUnitSoloExit`, `QuittingCappedJointExit`, and
`QuittingWeakSoloExitPreference`. The last is scale-free, but the existence
wrapper still explicitly assumes the first. Its header correctly warns that
the module itself does not provide positive-rescaling transport.

The source is genuinely proved, not merely a Literature proposition:

- `exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`
  supplies all-behavior terminal approximate Nash at every suffix;
- `quittingCappedJointExitUniformεExistence_holds` and
  `exists_uniformEquilibriumPayoff_of_soloExitPreference` there give the
  unconditional profile-level and fixed-target consequences;
- `exists_uniformEquilibriumPayoff_of_weakSoloExitPreference` in
  `Classification/TerminalExploitabilitySoloExitPreference.lean` retains its
  literal unit-solo hypothesis.

The semantic transport is already partly integrated elsewhere:
`quittingTerminalPayoff_playerwiseAffine` in
`Quitting/Terminal/TerminalAffineReward.lean` states exactly

    U'_i=scale_i U_i+shift_i(1−liveMassLimit).

It applies to the same complete profile and hence every unilateral
replacement. Setting shift zero supplies the scaling identity; setting
scale one and shift t supplies the perturbation identity above.
By contrast the root theorem `quittingRootPayoff_playerwiseAffine` in
`Root/PlayerwiseAffineReward.lean` transforms the continuation value too;
it must not alone justify a terminal-only shift with Never zero.

Finally `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
and its `...iff_terminalNash_all_errors` version in
`Terminal/TargetTail/TerminalUniformPayoffSelection.lean` give the fixed-target
consumer. I also checked `IsεAsymptoticNash` and `IsUniformEquilibriumPayoff`:
the former quantifies over complete behavioral replacements, and the latter
fixes the payoff before the accuracy request and covers all sufficiently
long finite horizons.

The narrow lookup did not find the final nonnegative-solo weak-preference
existence wrapper. This is a useful production-library assembly opportunity,
not new mathematical class coverage and not a claim that transport primitives
are wholly absent. No exhaustive source absence claim or implementation is
made.

## Independent sanity check of the new root argument

Under constant own-quitting rewards, Q_i(q)=s_i for all opponents. Every
exact root successor w therefore has w_i≥s_i, and every active quitter i
has w_i=s_i. Thus every positive-absorption exact root maps into the same
compact lower boundary L of the box ∏[s_i,B]. This uses constant own rewards,
not merely the canonical singleton vector.

At a minimum x of H on L, a unique binding coordinate gives a small solo
exact root whose successor stays in L, immediately contradicting positive
drift. If several coordinates bind, increasing any one of them remains in
L, so its partial derivative is nonnegative. Lower all binding coordinates
by ε. Every exact root at that nearby point has positive absorption and
successor in L. The displacement of each lowered coordinate is at least ε,
while |F−v|∞≤(M+B)a, yielding a≥ε/(M+B). Drift would then require

    [H(x−ε1_J)−H(x)]/ε ≥ 1/(M+B),

whereas differentiability gives limit −Σ_(i∈J)∂_iH(x)≤0. The contradiction
is valid on upper box faces, with one player, and with arbitrary signed
singleton levels. B>M guarantees both the inward perturbation and a
positive denominator. No continuous root selector is required.

The fixed-box separator composition in Sections 4–5 uses inner radius M+1
and outer radius M+2 correctly. Exact edges belong to every positive-error
relation. The canonical punishment identity P=s follows from immediate
Quit and all-Never opponents; no joint realization of punishment coordinates
is assumed. These checks support the stated independent root proof, while
the older-class closure above removes any new canonical UE-class credit.

No author file, frozen export, or Lean source was modified.
