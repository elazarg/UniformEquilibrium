# Independent review of cardinal-free stationary repair and index escape

Reviewer: CODEX_LERAY_CARDINAL.

Verdict: the main claims of
[`CARDINAL_FREE_LCP_INDEX_ESCAPE.md`](../gpt/CARDINAL_FREE_LCP_INDEX_ESCAPE.md)
pass as ordinary mathematics. No unresolved mathematical objection was found.
This is one independent review, not export approval or Lean validation.
The detailed reconstruction, inspected declarations, and source comparison
are in the
[owned review note](../notes/CODEX_LERAY_CARDINAL__STATIONARY_REPAIR_AND_INDEX_ESCAPE.md).

## Claims checked

For every finite quitting game with independent private randomization,
signed coalition rewards bounded by M, and zero live/Never payoff:

- A stationary discounted equilibrium with absorption a > 0 has a repair
  among itself and its sole-owner restrictions with full terminal regret
  at most min(2M, M[λ/a+2√(λ/a)]), hence at most 3M√(λ/a).
- If the full singleton matrix is R0 with integer min-map degree different
  from +1, every sufficiently small discount has an original stationary
  equilibrium at a fixed positive distance from all Continue. Repair and
  payoff subsequence selection give one fixed uniform payoff implemented
  by stationary profiles at every positive accuracy.
- Under that same R0/degree hypothesis, nonnegative own-singleton rewards
  give an exact stationary terminal Nash equilibrium with positive
  absorption. Arbitrary signed nonsingleton rewards are retained throughout.

## Valid critical steps and boundaries

The cap max(Qᵢ,Hᵢ/bᵢ) for bᵢ > 0 includes every private stopping law and
Never. For bᵢ = 0 the cap is max(sᵢ,0). This agrees with the existing
`quittingBestReplyValue_stationary` and
`quittingTerminalPayoff_update_stationary_le_cap` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

The nonpositive-owner branch is sound and essential. The discounted
Continue inequality gives Hᵢ/bᵢ ≤ Vᵢ when Vᵢ ≤ 0, because its multiplier
minus one is λ(a−bᵢ)/(bᵢL) ≥ 0. If the deleted clock is exactly zero,
discounted optimality and positive own hazard force sᵢ ≥ 0; the branch
therefore has sᵢ = 0. For a positive owner, the repair separately controls
prescribed singleton concentration and every outsider's changed Quit
endpoint. It does not confuse those two probability laws.

The local degree argument has the required ambient domain. Near all
Continue the upper clip disappears, but the lower clip remains, giving
G₀(q) = min(q,−D(0,q)). The R0 sphere margin dominates the quadratic
remainder uniformly and makes the homotopy boundary safe. The ambient
linearization is consistent with
`hasFDerivAt_quittingDiscountedDisplacement_zero` in
`UniformEquilibrium/Quitting/Stationary/DiscountedAmbientDerivative.lean`.
The outer domain has degree 1−κ for every small discount, including zero.
No strict complementarity, isolated outer roots, selected support, or
localization of the entire equilibrium set is assumed. Binding coordinates
and upper faces are covered. Degree 2 does not count exactly two roots.

The fixed-target argument has the correct quantifier order. Each chosen
stationary profile has its own sufficiently large horizon threshold, which
controls every replacement. No uniform lower bound on all deleted clocks
across the approximation family is needed. Independent finite censoring
and the signed late-deviation/Never comparison also pass.

The weaker exact-stationarity condition in Section 4 is valid: for each
negative own-singleton player k, infeasibility over 0 < h ≤ 1 of

    rⱼ({k}) ≥ (1−h)sⱼ + h rⱼ({j,k})        for every j ≠ k

excludes precisely the offending sole-owner zero-discount roots. It suffices
for the degree-produced nonzero root to be exact terminal Nash.

The packet's signed two-player example actually satisfies R0 and κ = 0,
yet has no exact stationary terminal equilibrium; the owned note gives
the short case proof. Thus an unqualified exact signed strengthening would
be false, even under the main matrix hypothesis. The weak-inverse corollary
proves stationary approximate implementation. It does not claim that the
weak boundary is R0 or that a hazard limit is exact Nash.

The n ≥ 3 second-order inverse-positivity argument and the bordering
Schur-complement formulas pass. The proper-child cycle non-subsumption
claim is valid for that specific inheritance mechanism. Finite censoring
does not itself make probabilities rational; rational finite laws follow
separately by continuity of the finite deadline/Never cap. No rational
exact root, denominator bound, or effective discount selector follows.

## New contribution and verification scope

The `(2)` references resolve to the existing exports
`INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md` and
`INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`.
Those already contain the integer-degree mechanism, strict-inverse example,
multibranch example, and weak-inverse approximation. The new contributions
are the universal quantitative stationary repair and its composition with
the original-table, zero-discount local degree argument for arbitrary
finite player count. Stationary approximate implementation and the exact
nonnegative-singleton result strengthen the predecessor conclusions.
No literature-wide priority judgment is made.

Gowda's
[author-hosted original](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf),
Section 2, printed pages 869–871, matches the packet's integer min-map
degree convention and degree properties. Existing Lean declarations were
inspected statically; no new theorem or composition was compiled.

The companion program was read before execution. All five check functions
passed with the reported exact counts and all three repair branches; its
JSON-writing main was not invoked. An independent exact two-player boundary
grid also passed for 6,096 discounted equilibria, including zero deleted
clocks and sure-quitting coordinates. These experiments check algebra and
boundary examples, not universal topology or strategy-class completeness.

The general quitting conjecture and the R0 degree-one case remain open to
this argument. The quantitative O(λ) restriction is necessary under a
positive stationary gap as well as under a full behavioral gap; it cannot
by itself prove arbitrary-game stationary or nonstationary existence.
