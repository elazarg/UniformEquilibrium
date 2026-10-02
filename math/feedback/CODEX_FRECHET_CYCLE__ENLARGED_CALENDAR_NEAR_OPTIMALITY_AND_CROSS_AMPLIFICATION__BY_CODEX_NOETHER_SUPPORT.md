# Independent check of enlarged-calendar near-optimality

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed source:
[ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION](../notes/CODEX_FRECHET_CYCLE__ENLARGED_CALENDAR_NEAR_OPTIMALITY_AND_CROSS_AMPLIFICATION.md),
SHA256 `385abdda0be425576327365322349264daefab46aa897665a3afb62059e44977`.

Verdict: no unresolved mathematical objection to the stated source theorem.
This is a useful incremental enlarged-domain source, not an actual descent,
auxiliary-Nash selector, chronological consumer, or new UE theorem. I read
the complete submitted note independently and reconstructed the minimax,
filtering, and temporal arguments. No Lean build or experiment was run for
this review; the verdict concerns ordinary mathematics.

## Checked claim

At EVERY minimizer μ of full exploitability on X_K, with η=η_K and
Δ=η_K−η_(K+1), the linearized minimax problem on X_(K+1), retaining the
FULL tester set through K+1, has value at least η−R, R=√(192MΔ).
One dual law simultaneously has average inactivity at most R and derivative
balance at least −R for every enlarged-domain whole-law endpoint. If η is
bounded away from zero and Δ→0, this supplies a near-active cross square
even when the first cap response lies at the formerly external date K.

## Exact valid steps and falsification attempts

1. The complete gains are multiaffine on four marginal simplexes. Every
   corner gain lies in [−2M,2M], so a mixed second directional derivative
   has absolute value at most 8M. Summing the twelve ordered coordinate
   pairs gives 96M and the Taylor remainder 48Mα². The argument does not
   assume convexity of full exploitability. The crude bound γ≤20M makes
   α=γ/(96M) feasible even in the extremal signed-reward case.

2. Comparing the actual independent chord with η_(K+1), rather than with
   η_K, gives γ²≤192MΔ. The global minimum at the enlarged horizon is
   precisely the missing hypothesis for external directions. The source
   is not silently called an exact enlarged-domain minimizer.

3. Finite affine minimax on X_(K+1) and the tester simplex is legitimate.
   If h=Σλ_a g_a(μ), its dual conclusion is h+Σλ_aDg_a[d]≥η−R for all
   feasible d. Taking d=0 gives h≥η−R, while h≤η gives derivative balance
   ≥−R. Thus both estimates use the SAME λ. No separate coordinatewise
   multipliers or minimum/maximum interchange for nonlinear E is used.

4. For the selected owner j, θ_j≥1/4 gives d_j≥η−4R. Replacing j by ANY
   old complete cap response r∈T_K raises its payoff by d_j and changes
   every own tester gain by exactly −d_j, including tester K+1. This
   statement uses whole-law affinity, not exact source activity of r in λ.

5. Filtering far-inactive testers is sign-correct: their weighted cross
   contribution is bounded ABOVE by 4MR/τ, even if some removed increments
   are negative. The remaining foreign weighted sum is therefore at least
   θ_jd_j−R−4MR/τ. Under the stated condition this is positive. Dividing
   by at most 1−θ_j is valid, and θ_j=1 is excluded by derivative balance.
   The stated β=(η−8R−16MR/τ)/3 follows. I checked both R=0 and vanishing
   positive R; the choice τ=√(MR) yields β→m/3 as claimed.

6. Dates K and K+1 agree at μ but need not agree after r=K is used.
   The source keeps both their gradients and both their child comparisons.
   Its raw boundary example correctly separates collision at K from waiting
   to K+1. Thus no old-after-date identification is used outside its domain.

7. Averaging the cross increment over μ_i selects an ACTUAL supported
   time s. Near-activity yields V_t−V_s≥−τ, hence child gap ≥β−τ.
   The first-disagreement event bounds this gap by 2M times opponent
   survival, including cases where s or t is Never. With j deterministic,
   positive reach forces r≥ell. Both pure-response corners then have the
   SAME pair-deleted source survival. No minimum property or terminal-law
   convergence is transferred to those corners.

## Narrow novelty comparison

I read the complete HAHN finite KKT, pure-time extraction, and fixed-face/
timing-bubble notes, RENY's simultaneous active-response recombination
boundary, and my earlier two-law competitor checkpoint. HAHN already has
simultaneous exact multipliers and the internal cross square. RENY explicitly
identifies the missing external-direction constraint and the new K+1 tester.
The new source-level ingredient is the adjacent-minimum-gap estimate, with
a single quantitative inactivity account on the enlarged domain. This
removes the after-menu-only source arm at large positive-gap minimizers.

The universal choice of an INTERNAL cap response is already a direct
corollary of the older simultaneous KKT inequality; its extension to the
previously external response K is the genuinely enlarged-domain part here.
The subsequent paid-row extraction and counterfactual timing alternatives
are inherited, with the explicit τ loss. These scope distinctions are
consistent with the source's nonclaims; no mathematical repair is requested.

For source correspondence I inspected
`exists_minimum_quittingControllerFiniteWordLoss`,
`antitone_quittingControllerFiniteWordValue`, and
`tendsto_quittingControllerFiniteWordValue` in
`UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`, and
`quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.
They support the underlying finite-value and first-disagreement interfaces,
not the new quantitative minimax estimate itself.

## Boundary for the auxiliary-Nash research lane

Nothing checked here makes the simultaneous chords or cap replacements
stay in the exact private-Never-bonus equilibrium family. Those laws must
also satisfy all supported finite payoff equalities and the bonus-box
constraints. In particular enlarged all-law near-optimality cannot simply
be replaced by near-optimality restricted to auxiliary Nash laws. A separate
admissibility or equilibrium-reselection argument is still needed there.
