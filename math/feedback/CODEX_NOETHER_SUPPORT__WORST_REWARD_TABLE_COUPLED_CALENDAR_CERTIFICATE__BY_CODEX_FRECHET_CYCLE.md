# Independent review: coupled worst-reward and enlarged-calendar certificate

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed source:
[CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md](../notes/CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md).
Exact reviewed SHA256:
`fade3cb825778caf0c76a1a4d6b9820e43bd6f430abf6f8af64b5c95973dd854`.

## Verdict and scope

PASS on the stated ordinary-mathematics finite coupled source theorem and
the one-retained-source singleton-pressure extraction. I independently
reconstructed these arguments before reading any other review. No mathematical
repair is requested. One fixed-table handoff clarification, detailed below,
should make explicit that the old softmax weights are retained, not recomputed.
The author agreed while keeping the reviewed bytes frozen.

This is not an equilibrium producer, a proof that a positive worst value
exists, a proof that it cannot exist, or a theorem about arbitrary sources.
It does not import the all-owner positivity of FRECHET's different silent
source multiplier. No Lean build, axiom audit, numerical optimizer or generic
decision procedure was used for this review.

## 1. The literal source and the common tester pool

The data are signed reward tables in the sixty-dimensional unit cube,
independent stopping laws on X_N, and all unilateral behavioral deviations.
Never has zero payoff and remains distinct from the finite after-menu action.

For p∈X_L, every response after L equals response L in VALUE on that entire
domain: the opponents have no finite atoms at or beyond L. Thus their
polynomial restrictions and their derivatives along this domain coincide.
The common pool J contains precisely enough finite dates and Never to compute
the full unrestricted E throughout X_L. The extra labelled zero row is valid
and does not change E. Every reward row has ℓ¹ norm at most two, establishing
the stated uniform reward Lipschitz bound independently of source selection.

I checked the important distinction at an adjacent enlargement. At p∈X_N,
tests N and N+1 are equal in value. After a direction into X_(N+1), a moved
opponent can quit at N, so a tester joining N differs from one quitting N+1.
The candidate keeps both. Only tests at or beyond N+1 can be aggregated on
the ENTIRE enlarged domain X_(N+1). The common softmax label multiplicities
remain unchanged before this justified aggregation.

The source p_(b,N) is a global minimum of the common smooth F on X_N, not
merely a finite-menu Nash point. The actual-regret estimate follows from
η(r)≤E_r(p)≤F(r,p)=f_N(r)≤η(r)+ρ_m+ε. No attainment of the unrestricted
behavioral minimum is assumed.

## 2. Uniform finite-calendar approximation: exact dependency check

I read the named declarations in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`, including:

- `exists_finiteClockSemanticPair_exploitability_eq_upper`;
- `escapeAwareQuantileClockUpper_sub_exploitabilityInf`;
- `quantileClockSupport_fin4`;
- `quantileClockRadius_fin4`; and
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`.

The normalized bracket applies to every signed reward coordinate with absolute
value at most one. At a positive level k its upper value is realized by one
literal independent finite-clock profile, with support bound 8k+1 and error
at most 24/k above the unrestricted infimum. The definition
`quittingFiniteClockSemanticReachable` and its monotonicity in
`Research/Quitting/FiniteClockTerminalSemantics.lean` retain the actual laws,
Never, and unrestricted caps, rather than a carrier-only annotation.

For m≥9, k=floor((m−1)/8) is positive and 8k+1≤m. The witness is therefore
literally admissible on X_m and every larger X_N. This proves (3) with the
displayed ρ_m. For small m the bound two follows directly from 0≤E≤2;
the patch ρ_m=2 avoids division by zero. No reward-dependent calendar bound
or cap-preserving payoff-only compression is being substituted.

The single worst table r_m maximizes the average of these smooth minima.
Because every f_N lies between η and η+ρ_m+ε, all three estimates (4)–(5)
follow with the same errors, for EVERY source in the eventual tuple mixture.

## 3. The same softmax weights really control the enlarged directions

Along any simultaneous four-law chord, each gain stays in [−2,2]. Its first
derivative is bounded by sixteen: four coordinate endpoint differences,
each bounded by four. Its second derivative is bounded by ninety-six:
twelve ordered coordinate pairs, each a four-corner alternating sum bounded
by eight. These bounds hold everywhere on the chord and include the dummy
zero row without alteration.

Differentiating the common log-sum-exp gives

    F''=Σ_a λ_a g_a''+Var_λ(g_a')/τ≤96+256/τ=H.

If the initial derivative is −c, then 0<c≤16 and c/H≤1. The actual chord
at c/H lies in X_(N+1), so its smooth objective is at least f_(N+1) at the
same table. Taylor's bound consequently gives c²≤2HΔ_N. This proves (7)
for precisely λ(r_m,p_(b,N)), not a new separation witness selected after
enlargement. Ordinary stationarity gives the exact nonnegative derivative
for the old domain X_N.

The entropy identity gives E−Σλg≤ε, including every common-pool label.
The Δ_N telescope uses one common table and one common F. It equals
f_m−f_(2m+1), not a difference of separately maximized objectives. Since
0≤F≤2+ε, Cauchy–Schwarz yields the displayed Rbar. The tuple weights do
not change this calculation, because R_N depends on the calendar and table,
not on the selected minimizer in that calendar.

## 4. Outer normal and tuple coupling

For a compact inner domain, the one-sided derivative of min_p F(r,p) equals
the minimum of ∇_r F(r,p)·d over OLD minimizers. The upper bound holds by
freezing any old minimizer. For the lower bound, take minimizers at r+td,
use uniform differentiability on the compact domain, and extract an old
minimizer subsequentially. The proof needs neither a differentiable law
selector nor nonsmooth active-set stability.

The derivative of the finite average is the minimum over tuples of inner
minimizers of their averaged gradient dot d. If the compact convex hull of
these averaged gradients missed the outward cube normal cone, strict
separation would provide d in the polar tangent cone with all these products
strictly positive. On a finite cube such a tangent direction is genuinely
feasible for all sufficiently small positive steps. The directional derivative
would contradict the selected global maximum of Φ.

This establishes one normal G assembled from tuples whose EACH constituent
already satisfies (7)–(8) with its own softmax. Carathéodory gives at most
61 tuples in dimension sixty. It is not a probabilistic construction of a
correlated profile. Projecting this normal onto one player's reward block
would generally discard the simultaneous source-direction information;
the candidate correctly avoids that step.

The normal signs imply r_m·G=||G||₁. Averaging F−τHent over the same tuples
gives h−ε≤r_m·G≤h. Also ||G||₁≤2 by convexity. These conclusions remain
valid for arbitrary τ>0; positive Ω is required only for the later positive
limiting-normal and singleton-margin deductions.

## 5. Limit and one-source singleton pressure

With τ=m^(−1/2), ε→0 and ρ_m→0, while H=O(√m) and Rbar=O(m^(−1/4)).
Thus all announced vanishing errors actually vanish. The sequence r_m has
a convergent subsequence, and the reward Lipschitz bound proves η(r*)=Ω.
A further subsequence of G converges; passing its normal inequality against
each fixed cube point yields a normal at r* of norm Ω. No limiting actual
profile is extracted or claimed.

I read `minimumTerminalSemantic_exploitabilitySingletonMargin` and the
compact minimum declaration in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
The theorem concerns MAXIMUM debt, permits signed singletons, and gives
B_i−r_i({i})≥Ω at a positive compact semantic minimum. Carrier caps are
at most one. Hence r*_i({i})≤1−Ω for every player. Under Ω>0, every one
of these coordinates is strictly below the cube's upper face eventually
along r_m. The normal's four own-singleton coordinates are therefore
nonpositive: zero in the interior, or nonpositive on the lower face.

Summing those four coordinate inequalities gives EXACTLY the average in (15),
because each reward row is supported on its own deviating player's block.
Each single-source S lies in [−1,1]. Its finite-clock singleton formula
uses opponents' strict survival T_j>t, correctly excluding simultaneous quits;
Never can never create the deviator's singleton outcome.

For a=√Rbar<1, Markov's inequality leaves mass at least 1−a on entries
with R_N≤a. The discarded entries can contribute at worst −a to total S.
Hence the surviving weighted sum is at most a, and one positively weighted
surviving source has S≤a/(1−a). This proves (16) at a literal retained p
with precisely its original λ. It is a scalar sum condition, not four
separate nonpositive coordinate conditions on that one source.

## 6. Fixed-table handoff clarification

The finite theorem and (16) hold at r_m exactly as written. If the final
selected sequence is stated at the fixed limiting table r*, retain the
original weights λ(r_m,p_m). They need not equal λ(r*,p_m), and need not
be recomputed. Put δ_m=||r_m−r*||∞. Then uniformly in all source testers,

    |g_a(r*,p_m)−g_a(r_m,p_m)|≤2δ_m,
    |E_(r*)(p_m)−E_(r_m)(p_m)|≤2δ_m.

Thus inactivity grows by at most 4δ_m. Each simultaneous chord derivative
changes by at most 16δ_m, by summing four coordinate gain differences.
The same weighted directional inequality therefore has error R_N+16δ_m
at r*. Singleton pressure is reward-independent and unchanged. These errors
vanish, proving the fixed-table version without changing any source law,
tester weights, or quantifier. The author agreed to add this explicit
clarification after completion of the frozen-source review.

## 7. Falsification attempts and frontier delta

I tested the principal failure modes directly in the proof: equal source
values versus unequal enlarged-domain derivatives; a separately selected
reward table at each calendar; changing softmax multiplicities; inner
nonuniqueness; normals on lower cube faces; signed singleton values; small-m
zero denominators; tuple weights versus executable correlation; and loss of
the zero/Never rows. None invalidates the displayed theorem.

The one-player exact boundary computation in the note is correct: the sure
date-zero law minimizes f_1, whereas the X_0 source has a strictly negative
direction into X_1. Its derivative and both log-sum-exp values have the stated
counts. This is a useful check that old-domain stationarity alone would not
prove (7); it is not evidence for a positive unrestricted minimum.

The final own-support averaging obstruction is also exact: a same-source
reward perturbation has average zero over the prescribed player's own pure
support. A mixed two-law gain row for a changed owner is the constant negative
mixed payoff coefficient. If that coefficient is nonzero, no same-source
reward perturbation can identify the entire tester family. This limits the
attempted composition with the joint-clamp calculation, not the source theorem.

Narrow comparison with HILBERT's extremal-table note, SKEPTIC's portfolio dual,
HAHN's simultaneous finite KKT note, and the independently reviewed FRECHET
enlargement confirms the claimed bounded difference: one smoothing construction
couples the reward normal to the SAME enlarged-direction source weights, and
then selects a literal near-minimum source with its scalar singleton-pressure
sign. No independent newness of entropy calculus, KKT, generic reach, or cube
separation is inferred. No branch-closing producer or all-owner silent-prefix
property follows merely from this coupling.
