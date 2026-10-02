# Global maximum-debt repair across the critical auxiliary box

Identity: CODEX_FRECHET_CYCLE.

## Status and question

Ordinary mathematics, not independently reviewed or Lean-checked. This is an
actual full-objective competitor and a critical-box source restriction,
not a Fin4 consumer. The calculation's scope is the entire
closed critical auxiliary box, including continuation reductions paid for by
inactive players' regret slack. The existing actual-payoff root repair is
the special case h=B−U. No KKT multiplier, auxiliary-Nash output minimizer,
or minimum of total debt is substituted for the global source below.
The subsequent overlap check found that HILBERT's existing ordinary-math,
unreviewed all-player-tie draft makes the displayed limiting cap collar
equivalent to the earlier
lowered-U margin. Thus no new residual class of positive global minima is
excluded; the finite inequality and full-box accounting are retained only
as an internal checkpoint.

Fix four players, arbitrary signed terminal rewards with |r_i(S)|≤M and M>0,
and zero reward at all Never. Strategies are independent laws on
Nat∪{Never}; every behavioral unilateral replacement is allowed. Write U for
the prescribed payoff, B for the complete response cap, d=B−U, and
E=max_i d_i. For K≥1 let

    A_K={0,...,K−1,Never},       η_K=min_{μ∈∏_i Δ(A_K)} E(μ).

The complete tester menu is {0,...,K,Never}, not A_K. These minima are
attained, decrease, and converge to the infimum over all actual profiles.
Can a root chosen at B−h, with h allowed to reach or slightly exceed E in
some coordinates, still yield a complete-objective improvement of the
original mixed source after one whole-law repair?

The answer is the inequality (4). It supplies the cap-margin consequence
(7), but does not force an absorbing root after that consequence holds.

## 1. Exact root ledger and the actual competing laws

Take ANY actual finite source μ∈∏_i Δ(A_K), with e=E(μ)>0. Fix ε≥0 and
a vector h satisfying 0≤h_i≤e+ε. For a product root q∈[0,1]^4 put

    W=B−h,  c_i=∏_{j≠i}(1−q_j),  c=∏_j(1−q_j),
    p_i=q_i c_i,                 a=1−c.

Let Q_i be the root Quit payoff and C_i(W)=H_i+c_i W_i the root Continue
payoff. Here H_i sums the payoffs of nonempty opponent root coalitions.
Set n_i=q_i Q_i+(1−q_i)C_i(W) and

    z_i=max{Q_i,C_i(W)}−n_i,       z=max_i z_i≥0.

Prefix q at date zero and shift μ's finite dates by one, leaving Never as
Never. This is an actual independent profile P on A_(K+1). Its complete
payoff and cap are exactly

    U'_i=n_i+c(h_i−d_i),
    B'_i=max{Q_i,C_i(W)+c_i h_i}.

The second formula includes every continuation response, with each player
choosing its own best continuation. Since h_i≥0, it implies

    d'_i≤c d_i+p_i h_i+z_i≤c_i e+p_i ε+z.              (1)

This is the existing auxiliary-defect ledger, used here at the critical
maximum-debt face. It retains the Quit branch even when that branch changes.
In particular q=0 prefixes a new preemption opportunity: it is not silently
identified with μ unless that opportunity was already bounded by B. The
admissible competing family also contains μ itself, embedded on the original
dates in A_(K+2); no root-prefix equality is needed for that inclusion.

If a=0, (4) below follows from the unchanged source and z≥0. Otherwise
choose k of maximal q_k. Then q_k≥a/4. Since p_i≤a and every i≠k has
c_i≤1−q_k, (1) gives

    d'_k≤e+aε+z,
    d'_i≤(1−a/4)e+aε+z                 (i≠k).           (2)

Choose a complete pure best response τ_k to P_-k, and privately replace k's
whole law by (1−θ)P_k+θδ_(τ_k), where θ=ae/(32M). The response is attained:
the opponents are supported through K, so {0,...,K+1,Never} is complete.
Thus the repaired profile P'' belongs to A_(K+2). No other player conditions
on k's private selector or on a detected deviation.

The unchanged opponents give the EXACT own-coordinate relation

    d''_k=(1−θ)d'_k.

For i≠k, both prescribed payoff and EACH complete response payoff change by
at most 2Mθ, uniformly over all dates and Never. Taking the supremum gives

    d''_i≤d'_i+4Mθ.                                    (3)

This also controls the newly exposed response K+2. It cannot be dropped
merely because τ_k was selected from the previous complete menu.

Since e≤2M, θ≤1/16, and e²/(32M)≤e/16≤e/8, equations (2)–(3) prove

    E(P'')≤e−a e²/(32M)+aε+z.                          (4)

Indeed the owner is at most e−a e²/(32M)+aε+z; every other coordinate is
at most e−ae/8+aε+z, which is no larger. Constants are inherited from the
earlier actual-payoff repair, not optimized.

## 2. The precise finite-global source consequence

Now and only now suppose μ is a GLOBAL minimizer defining η_K=e. Since
the actual repaired profile lies in A_(K+2), (4) gives, for every h and q
above,

    η_(K+2)≤η_K−a(q)η_K²/(32M)+a(q)ε+z(q;B−h).        (5)

This is an all-four-law global comparison; KKT stationarity alone does not
give it. If q is exact Nash at B−h and

    0≤h_i≤η_K+η_K²/(64M),

then

    a(q)≤64M(η_K−η_(K+2))/η_K².                        (6)

It holds for EVERY such root at EVERY selected global minimizer. In
particular it is not an assertion about one favorable root selection.

There is also an unconditional numerical cap collar at the finite source.
Choose h_i=e+e²/(64M) for all i, and take any exact Nash root at W=B−h.
Finite mixed Nash existence applies; W need not be a realized payoff.
Put δ=(e+e²/(64M)−min_i(B_i−s_i))_+, where s_i=r_i({i}). If δ>0, choose
i with s_i−W_i=δ. Since e≤2M, W_i≥−49M/16, so δ+2M<7M. The exact
endpoint comparison gives

    Q_i−C_i(W)≥δ−7M(1−c_i).

If 1−c_i<δ/(7M), Nash forces q_i=1; otherwise a≥1−c_i. In either case
a≥δ/(7M). Combining with (5) proves

    η_(K+2)≤η_K−δ η_K²/(448M²).                        (7)

No canonical sign assumption is used in this argument.

## 3. Every positive global minimum and every root on its enlarged box

Let C be the closure of the actual semantic pairs (U,B), and let

    m=min_{(U,B)∈C} max_i(B_i−U_i)=inf_actual_μ E(μ)>0.

Fix ANY minimizing pair (U,B), not necessarily attained by a literal law.
For every h with 0≤h_i≤m+m²/(64M), every exact root against B−h is all
Continue. Here is the nonattainment argument, without root-correspondence
lower hemicontinuity.

Choose finite actual profiles μ_n whose semantic pairs converge to (U,B).
Such finite approximation preserves payoffs and complete caps: censoring
each player's remote finite mass to Never has vanishing total variation,
and the payoff/cap coupling estimates are uniform over deviations. Then
e_n=E(μ_n)≥m and e_n→m. Fix an arbitrary exact root q at B−h. Use that
SAME q at W_n=B(μ_n)−h. Its finite root defect z_n tends to zero by
continuity in the continuation vector. Since h_i≤e_n+m²/(64M), (4) gives

    limsup_n E(P''_n)≤m−a(q)m²/(64M).

If a(q)>0 this contradicts the actual-profile infimum m. The repaired laws
need not converge. Thus all such roots are all Continue. Applying ordinary
finite Nash existence at h=(m+m²/(64M))·1 yields

    B_i−s_i≥m+m²/(64M),
    U_i−s_i≥m−d_i+m²/(64M)              for every i.    (8)

The same bounds follow for semantic clusters of any sequence of finite
global minimizers from (7). A payoff-only realization or a cap-preserving
calendar compression is not used.

## 4. What has and has not advanced

The strict-box maximum-debt moat already excludes absorbing exact roots at
B−h when all h_i<m. RENY's minimum-tie argument already handles the actual
payoff U, corresponding to h=d and possibly several critical coordinates.
The earlier lowered-U repair proves U_i−s_i≥m²/(64M). The accounting scope
here is the ENTIRE enlarged closed box: at a finite source a nonmaximal
debtor may use h_i=e even though h_i>d_i. However, HILBERT's ordinary-math
draft already proves
ALL d_i=m at every positive unrestricted maximum minimum, by a slack-aware
solo prefix with the complete new Quit branch retained. I independently
reconstructed that argument and then read the draft; this is additional
mathematical evidence, not a Lean check or a completed independent gate.
Consequently (8)
does not strengthen the existing limiting singleton floor there. The
finite bounds (5)–(7) do not justify claiming a new residual class reduction.

HILBERT's simultaneous small-root computation also already gives the
necessary harmonic condition mΣ_i 1/(B_i−s_i)≤1. Reconstructing its balanced
hazards from (1) would be another rediscovery, not the missing macroscopic
KKT competitor. The enlarged-box root restriction does not resolve that
all-tied, strictly above-singleton region.

This comparison does not use or identify NOETHER's minimum among exact
Never-bonus auxiliary Nash sources. Here a fixed limiting root may be used
as an approximate root at the actual sources because every resulting
profile is admissible for the unrestricted objective. An auxiliary-source
domain may not be closed under that operation.

The source implication is now explicit, but an absorbing root is NOT
forced once (8) holds. All Continue satisfies its endpoint inequalities
throughout the indicated box. None of the inspected KKT cross-amplification
constraints supplies a root whose defect z in (5) is smaller than its
absorption-relative repair gain. The distinct question left open is:

> Can the genuine mixed global KKT source produce one root q and one
> h∈[0,η_K+η_K²/(64M)]⁴ for which
> z(q;B−h)<a(q)η_K²/(64M)−(η_K−η_(K+2))?

No arbitrary-profile regression is offered as a counterexample to that
positive-limit/global-source implication. This note is an internal source
restriction, not an export proposal or a proof that η_K tends to zero.

## Sources inspected

- `exists_minimum_quittingControllerFiniteWordLoss`,
  `antitone_quittingControllerFiniteWordValue`, and
  `tendsto_quittingControllerFiniteWordValue` in
  `UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`.
- `quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect` and
  `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash` in
  `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`.
- `nearMinimumTerminalSemantic_exploitabilityAuxiliaryNash_absorptionMass_le_sharp`,
  `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`, and
  `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
- [RENY's maximum-minimum ties and actual-root uniqueness](CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md).
- [Earlier actual-payoff finite repair](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_PAYOFF_FLOOR_ESCAPE.md),
  [approximate-root transport](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_APPROXIMATE_ROOT_CLUSTER_ADDENDUM.md),
  and [lowered-U margin](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_LOWERED_ROOT_MARGIN_TEST.md).
- [Same-source two-law KKT comparison](CODEX_NOETHER_SUPPORT__GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT.md).
- [HILBERT's all-player ties](CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md)
  and [simultaneous small-root harmonic test](CODEX_HILBERT__SIMULTANEOUS_SMALL_ROOT_TEST.md),
  read completely for the final overlap check.

These source inspections do not constitute a Lean check of (4)–(8).

## Bounded checks and one domain diagnostic

Fifty exact rational tests used arbitrary signed integer reward tables in
[−2,2], three-atom source laws on {0,1,Never}, independent quarter-grid
roots, and h_i∈[0,e+e²/(64M)]. Direct terminal enumeration checked (1) and
the actual repaired profile's complete menu {0,1,2,3,4,Never}. All passed.
They test the ledger and the new response branch, not global optimality.

The following small internal calculation explains why the source domain
cannot be replaced by auxiliary Nash selection. Use canonical H from the
[earlier calendar calculation](CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_MINIMUM_CALENDAR_EXTENSION.md),
not its modified-pivot or modified-pair variants. On its one-date laws,
q=(23/50,14/25,19/50,7/50) has full debts

    (81/625,181937/1562500,385149/3125000,373051/3125000).

Thus η_1≤81/625<2/15. On the ENTIRE face q_3=0, put (x,y,z)=(q_0,q_1,q_2).
The complete objective is the maximum of zero and the following six
multiaffine polynomials:

    (1−x)(1−2z),
    (1−y)(1−z)−x(1−2z),
    y[x(1+z)−z],        z[y(1+x)−x],
    (1−y)[z−x(1+z)],    (1−z)[x−y(1+x)].

A cheap exact dyadic certificate gives a strict lower bound 2/15 on this
face. The deterministic verification rule is: start with [0,1]³; compute
the minimum of each displayed polynomial at the eight vertices of a box;
discard the box if one minimum exceeds 2/15, otherwise subdivide it into
eight equal boxes. Multiaffinity makes every discard rigorous. Exact integer
arithmetic exhausted the tree in 241 visited boxes of depth at most six.
No numerical optimizer or unverified global-minimum annotation is used.

Consequently every attained all-law minimizer at K=1 has q_3>0. It also
has some active player with positive hazard, since otherwise pivot Quit0
earns one while its prescribed payoff is zero. Player 3 then STRICTLY
prefers Never to Quit0 on H. Such a minimizer is not Nash under any
nonnegative private Never bonus. This is only a finite-horizon domain
separation: H has unrestricted infimum zero. It does not falsify the
positive-limit KKT target or supply an auxiliary-horizon lower bound.
