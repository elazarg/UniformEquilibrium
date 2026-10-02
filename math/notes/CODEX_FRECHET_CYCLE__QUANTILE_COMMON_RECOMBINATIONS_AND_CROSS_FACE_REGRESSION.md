# Quantile common clocks and the cross-face survival mismatch

Recorder: `CODEX_FRECHET_CYCLE`.

Status: preservation of mathematical claims independently reviewed PASS by
CODEX_RENY in `feedback/QUANTILE__BY_CODEX_RENY.md`, SHA
`5b66d4d0f8c99facca56b61b4b55e9f6d2a018b1ab04dd390692be4e061c7275`.
This is neither a new review nor new research. The inputs, read completely
for this preservation, are:

- `gpt/QUANTILE.md`, SHA
  `f28bfa0de099c88555d7ebf7c2864ceb74b51c324bec315e259b12b662e9ad48`;
- `gpt/QUANTILE_CLOCK_COMPRESSION.md`, SHA
  `afa8417acf568a98a10632b210447e59a64ac814ab8ba7c36f240a15035b7e00`.

The main positive-gap semidecision is already covered by checked repository
sources. The useful material preserved here is the uniform common-clock
theorem for independently crossed finite source families and the exact
failure of child-error-only cross-face splicing. No export or new strategy
class completeness claim is made.

## 1. CDF continuity and a gap-preserving finite clock

There are n≥2 players, signed terminal rewards bounded by M>0, and zero
all-Never payoff. Laws on ℕ∪{Never} are independent. Write U_i for
prescribed terminal payoff, B_i for the supremum over ALL behavioral
replacement laws, d_i=B_i−U_i, and E=max_i d_i.

For a law μ let F_μ(t)=Pr_μ(T≤t), with F_μ(−1)=0, and define

    d_CDF(μ,ν)=sup_(finite t)|F_μ(t)−F_ν(t)|.

If only coordinate j changes by CDF distance δ, every payoff coordinate
changes by at most 4Mδ, uniformly over all other independent laws.
Indeed, fix the other pure times. If their first finite time is t with
coalition S, the observed payoff as j's time varies is A before t, B at t,
and C after t, including Never. Its expectation is

    C+(A−B)F_μ(t−1)+(B−C)F_μ(t).

Each difference coefficient has absolute value at most 2M. If all others
choose Never, the expectation is r_i({j}) lim_t F_μ(t), whose change is
at most Mδ. Integrating the bounded functions over the other laws proves
the claim. In particular, for coordinate discrepancies δ_j,

    |U_i(p)−U_i(q)|≤4M Σ_j δ_j,
    |B_i(p)−B_i(q)|≤4M Σ_(j≠i) δ_j.             (CDF)

For the cap inequality the same bound holds BEFORE taking the supremum,
uniformly over the deviator's entire replacement law. No best-response
attainment, moment bound or tightness is needed. The constant 4M cannot
simply be halved by ignoring ties: A=C=M, B=−M, with the other player
at date 1, gives payoff change 2M when half mass at 0 and half at 2 is
replaced by sure date 1, at CDF distance 1/2.

For K≥1 use midpoint quantiles u_k=(2k−1)/(2K). Let Q_μ(u) be the
first finite date with F_μ(t)≥u, or Never if none exists, and put

    μ^[K]=(1/K)Σ_(k=1)^K δ_(Q_μ(u_k)).

At every finite t its CDF is #{k:u_k≤F_μ(t)}/K, so its CDF error is
at most 1/(2K). It has at most K atoms including Never, all masses being
multiples of 1/K. A quantile equal to a finite-mass limit that is never
attained at a finite date is correctly assigned Never. Arbitrary Never
mass is rounded, not preserved exactly; identically Never is preserved.

For a finite union of support dates D={t₁<⋯<t_L}, shorten the clock by

    φ(t₁)=min(t₁,1),
    φ(t_(a+1))−φ(t_a)=min(t_(a+1)−t_a,2),
    φ(Never)=Never.                                    (CLOCK)

This preserves order, ties, the existence of a preemption date before the
first support, and the existence of an empty date between supports. For
every pure response, its class is: a support date, an available preceding
or interior gap, strictly after the last support, or Never. Corresponding
classes exist on both clocks and give identical outcomes against every
supported pure opponent tuple. Consequently prescribed payoffs AND full
caps are exactly preserved in both directions. The argument works for
any subset of the union D as well. If D is empty, all laws are Never
and no clock change is needed. The largest image date is at most 2L−1.

With at most nK finite dates this proves the elementary single-profile net
on {0,…,2nK−1,Never}, with errors

    |ΔU_i|≤2nM/K,   |ΔB_i|≤2(n−1)M/K,
    |ΔE|≤(4n−2)M/K.                                    (NET)

The late finite response is distinct from Never. With prescribed support
strictly below H, complete response tests include {0,…,H,Never}.
Deleting H merely because it lies outside prescribed support is invalid.

## 2. One clock for EVERY independent recombination

Fix ANY finite family of m≥1 ambient source profiles p¹,…,pᵐ. For
each source and each player perform the K-midpoint approximation. Form
the union of all these finite supports, and apply ONE map (CLOCK).
Let the resulting source laws be p̂_iᵃ. There are at most mnK dates,
so all finite support lies strictly below 2mnK.

For arbitrary real weights θ_ia≥0 with Σ_a θ_ia=1, form product laws

    x_i(θ)=Σ_a θ_ia p_iᵃ,
    x̂_i(θ)=Σ_a θ_ia p̂_iᵃ.

Then simultaneously for EVERY choice of these weights,

    |U_i(x(θ))−U_i(x̂(θ))|≤2nM/K,
    |B_i(x(θ))−B_i(x̂(θ))|≤2(n−1)M/K,
    |E(x(θ))−E(x̂(θ))|≤(4n−2)M/K.               (FAMILY)

Proof: before shortening, convex mixtures preserve the common CDF error
1/(2K) at each coordinate. Apply (CDF). Pushforward through the one fixed
map φ commutes with mixtures, and every recombination is supported in the
same finite union. The two-sided response-class argument therefore applies
uniformly to every mixture, giving exact payoff/cap preservation in the
shortening step. This proves all three inequalities.

Each coordinate chooses its source law privately and independently of the
other players. This is NOT a shared random source label or a correlated
mixture of complete profiles. Distinct players may use different sources.
The compressed individual source laws have denominator K; arbitrary real
mixture weights need not produce denominator-K or even rational laws.

For quiet lifts from child games, identically Never coordinates remain
quiet. A child with k players has exploitability error at most
(4k−2)M/K. The common map preserves the interpretation of immediate
Quit0, including when the first prescribed support is positive. Applying
(CDF) to the immediate outsider payoff and prescribed payoff shows that
an ambient immediate outsider gain changes by at most (4n−2)M/K.

The finite family is fixed BEFORE this common clock is selected. There is
no one bounded clock for an infinite source sequence, no preservation of
an externally supplied prefix or numerical reach at an arbitrary nonzero
cut, and no finite-horizon payoff-process equivalence. Most importantly,
(FAMILY) does not produce weights yielding small parent debt.

## 3. Exact cross-face prefix law

Let P be any fixed finite product prefix of length T, and append a full
behavioral tail x. Put

    c=∏_(t<T)∏_j(1−q_j^t),
    λ_i=∏_(t<T)∏_(j≠i)(1−q_j^t).

Let a_i be the prescribed absorbing reward contribution inside the prefix,
h_i the contribution there if i always Continues, and k_i the best pure
response Quitting strictly inside the prefix. For T>0,

    U_i(P*x)=a_i+cU_i(x),
    B_i(P*x)=max{k_i,h_i+λ_i B_i(x)}.                  (PREFIX)

This is the full cap: a pure response Quits before T or reaches T and
uses a complete tail replacement, and mixtures cannot exceed their
supremum. No tail best reply need attain that supremum. At T=0 omit the
nonexistent inside-prefix maximum; then U and B are just the tail values.

For two tails x,y, let Δu_i=U_i(y)−U_i(x) and Δb_i=B_i(y)−B_i(x).
The exact debt change is the difference of the two maxima in (PREFIX)
minus cΔu_i. Therefore

    d_i(P*y)−d_i(P*x)≤λ_i(Δb_i)₊−cΔu_i.              (SPLICE)

Even if B_i=U_i in BOTH tails, this can equal (λ_i−c)Δu_i>0 when
the continuation branch is active and Δu_i>0. The deviator who avoids
its own prescribed Quit risk reaches the changed tail with probability
λ_i rather than c. Child-equilibrium errors alone do not price this
payoff-level difference.

## 4. Exact proper-face regression

Take three players, Never zero, and this complete terminal table:

| S | r₁ | r₂ | r₃ |
| --- | --- | --- | --- |
| {1} | 1 | 0 | 0 |
| {2} | 0 | 1 | 0 |
| {3} | 2 | 0 | 1 |
| {1,2} | 1 | 1 | 0 |
| {1,3} | 2 | 0 | 1 |
| {2,3} | 0 | 1 | 1 |
| {1,2,3} | 1 | 1 | 1 |

On every nonempty proper child J let everyone Quit0, except on {1,3}
let player 3 Quit0 and player 1 Never. Every child profile is exact Nash
against unrestricted deviations: each participating player obtains its
maximum available reward in that child. In the order

    J={1},{2},{3},{1,2},{1,3},{2,3},

choose outsider 2,1,2,3,2,1 respectively. In each quiet lift that outsider
gains exactly one by Quit0. Thus γ=1, M=2, ρ=1/4 meet the displayed
SOURCE conditions; constant exact sequences have any positive error
upper bounds tending to zero and date-zero reach one.

Let x be the quiet {1,2} source and y the quiet {1,3} source. Their
ambient semantic vectors are

    U(x)=(1,1,0), B(x)=(1,1,1),
    U(y)=(2,0,1), B(y)=(2,1,1).

Prefix both by one date where player 1 Quits with probability 1/2 and
the others Continue. Then c=1/2, λ₁=1, a₁=1/2, h₁=0, k₁=1.
Consequently

    U₁(P*x)=B₁(P*x)=1,
    U₁(P*y)=3/2, B₁(P*y)=2.

Player 1 has zero debt in each child source, but the face switch creates
debt 1/2. Never attains its new full cap, because player 3 Quits at the
next date and pays it two. The added debt exactly equals
(λ₁−c)(U₁(y)−U₁(x)). Continuation reach is 1/2≥ρ.

This parent game has an exact equilibrium: everyone Quit0. A player who
instead Continues receives zero from the other two quitting, rather than
one. Thus the GLOBAL positive-gap premise is absent. The example refutes
error-only cross-face splice accounting, not a cardinal-minimal positive-
gap implication or existence of a different successful parent strategy.

## 5. Existing coverage and preservation boundary

The TOOLKIT quantile route identifies the already checked
`hasEscapeAwareQuantileClockCompressionAtBound` and
`hasEscapeAwareQuantileClockCompression_of_normalized` in
`Research/Quitting/EscapeAwareQuantileClockTransport.lean`. That escape-
aware construction preserves arbitrary Never mass exactly, unlike the
midpoint rounding here. `exists_finFourFixedTableCounterexampleStep_of_infimum_pos`
in `Research/Quitting/FinFourFixedTableCounterexampleSearch.lean` already
provides positive-gap fixed-table semidecision. Their declarations and
the maintained TOOLKIT scope were inspected for this preservation; no
fresh build or additional review was performed.

For context, (NET) itself gives the elementary finite grid bracket

    max(0,a_K−(4n−2)M/K)≤inf_p E(p)≤a_K,

where a_K is the grid minimum over denominator-K laws on
{0,…,2nK−1,Never}. The grid has binomial((2n+1)K,K)^n profiles, and
the full cap tests include the extra finite date 2nK. Its exhaustive
positive certificate is complete, but does not give a positive instance
or a terminating zero-gap test. The reviewed packet's main Fin4
semidecision, reward-robustness and rationalization consequences already
have the exact existing homes listed in RENY's review and are not being
republished as new results here.

The reviewed common-family theorem and the exact regression are now
preserved in notes/, independently of raw GPT inputs or archive retention.
No files were moved, no new cross-face selection was attempted, and no
coefficient, clock, or equilibrium search was begun.
