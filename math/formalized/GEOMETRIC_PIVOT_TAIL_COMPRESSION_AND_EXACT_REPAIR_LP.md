# Geometric pivot compression, exact repair LP, and three-law selection

Authors: external GPT submission; CODEX_RENY assembled the complete statement,
signed-singleton extension, and source-equivalence details.
Source: [preserved original](../notes/CODEX_ROOT__GEOMETRIC_TAIL_COMPRESSION_INTAKE.md),
original SHA-256
`a710fb8d255a60af4a564bc921c0bb0668716233e7120b2f1d6c9dffcd138b19`.
Independent original reviews:
[CODEX_RENY](../feedback/GEOMETRIC_COMPRESSION__BY_CODEX_RENY.md),
[CODEX_HILBERT](../feedback/GEOMETRIC_COMPRESSION__BY_CODEX_HILBERT.md).
Both original reviews passed. CODEX_HILBERT's linked review also confirms the
whole assembled statement and proof; CODEX_ROOT completed the final
whole-packet gate with no unresolved objection.

## Exact statement

Let I be a finite nonempty player set, let k ∈ I be a distinguished pivot,
and let r(S) ∈ ℝ^I be an arbitrary real reward vector for every nonempty
coalition S ⊆ I. At each date in ℕ, players independently choose Continue or
Quit. The first nonempty quitting coalition receives r(S); infinite
all-Continue receives zero. Strategies and unilateral deviations are
unrestricted behavioral strategies. Equivalently they are independent laws
of stopping times in ℕ ∪ {Never}. All payoffs below are terminal expectations.

For a product law p, let U_i(p) be prescribed payoff, B_i(p) the supremum
payoff over all unilateral behavioral deviations of i, and

    E(p) = max[i ∈ I] (B_i(p)−U_i(p)).

Fix N ≥ 1 and all nonpivot laws p_j on F_N = {0,…,N−1,Never}.

**Theorem 1 — exact simultaneous compression.** For every pivot law μ on
ℕ ∪ {Never}, there is a law μ̃ with the same head atoms before N, the same
Never mass, and a geometric late finite component, such that the terminal
coalition distribution, including all-Never, is unchanged and

    U_i(μ̃,p_{−k}) = U_i(μ,p_{−k}),
    B_i(μ̃,p_{−k}) ≤ B_i(μ,p_{−k})       for every i ∈ I.

The pivot cap is equal. More explicitly, if λ = Pr(N ≤ T_k < ∞) > 0,
t_* is its first positive late atom, α = Pr(T_k = t_*), and h = α/λ, take

    μ̃(N+ℓ) = α(1−h)^ℓ,       ℓ ≥ 0.

If λ = 0, leave μ unchanged. For arbitrary signed singleton rewards the
nonpivot cap formula has three late endpoints. If every nonpivot own
singleton is zero, only two are needed.

**Theorem 2 — exact finite inner optimization.** The finite linear program
defined below has a minimum z_*(p_{−k}) satisfying

    z_*(p_{−k}) = inf[all behavioral pivot laws μ] E(μ,p_{−k}).

This identity holds for every signed reward table and finite I. The LP
minimum need not be attained by an actual pivot law. Every LP optimizer is
either literally implementable or approached by geometric laws with all
prescribed payoffs unchanged.

**Theorem 3 — actual finite-menu consumer.** Let |r_i(S)| ≤ M. From any
feasible LP point of value z, and any η > 0, one obtains an actual geometric
implementation with E ≤ z+η. Retaining its first K late atoms and moving the
remaining finite mass β to Never gives an actual finite product law p with

    E(p) ≤ z+η+4Mβ.

Let g = r_k({k}). If g > 0, then for every H ≥ 1 and N₀ ≥ 1, that truncated
law can be displayed at a deadline L ≥ N₀ with

    R_p(L−H) ≤ z/g+β,

where R_p(t) is the literal probability that nobody has quit before t.
Consequently, if these fixed-opponent LP values are arbitrarily small as
the finite opponent laws and N vary, then for every e > 0, H ≥ 1, ρ > 0,
and N₀ ≥ 1 there are L ≥ max(H,N₀) and laws on F_L with E(p) < e and
R_p(L−H) < ρ. The nonpivot singleton rewards may have either sign.

**Theorem 4 — canonical Fin4 source equivalence.** Suppose I = {0,1,2,3},
k = 0, r_0({0}) = 1, and r_j({j}) = 0 for j ≠ 0. All other reward entries
remain arbitrary. The following conditions on this fixed reward table are
equivalent:

1. For every ε > 0, some N ≥ 1 and four laws p on F_N satisfy
   E_N(p) ≤ ε and W_0(p)+D_0(p)−U_0(p) ≤ ε, where E_N is the finite-menu
   Nash error, W_0 is the pivot's Never payoff, and
   D_0 = ∏[j≠0] p_j(Never).
2. For every δ > 0, some N ≥ 1 and three laws p_1,p_2,p_3 on F_N satisfy
   z_*(p_1,p_2,p_3) < δ.
3. For every e > 0, H ≥ 1, ρ > 0, and N₀ ≥ 1, some L ≥ max(H,N₀) and
   four laws p on F_L satisfy E(p) < e and R_p(L−H) < ρ.

The equivalence eliminates the pivot from the remaining outer selection
problem. It does not establish any of these conditions for every table.

## Conjecture-facing change

The prior obligation is the canonical single-pivot finite-menu selection
question: select four finite laws with small finite-menu regret and a small
pivot late-deviation scalar, on the same law. The new reduction replaces one
whole unrestricted stopping law by an exact finite-dimensional convex inner
problem. The remaining variables are three finite opponent laws and their
common deadline. Small inner values yield actual finite laws with full
behavioral regret control and arbitrarily early absorption relative to the
displayed deadline.

The remaining outer search is not asserted convex, and no theorem here
forces its values to approach zero. The exact numerical example below shows
why unrestricted optimization of the pivot alone need not fix supplied
opponents. It also illustrates a successful table-specific repair, not a
general convergence procedure.

## Definitions and assumptions

Write ∞ for Never, ordered after every finite date. A stopping law μ has
nonnegative atoms with total mass one. It is realized behaviorally by the
hazard μ(t)/Pr(T ≥ t) whenever that denominator is positive; behavior at an
unreached history may be chosen arbitrarily. Conversely the survival products
of a behavioral hazard sequence give its law. Since the only live public
history at date t is t previous all-Continue outcomes, this representation
covers every unilateral behavioral deviation. Players' marginal randomness
is independent. No common random seed is introduced.

For each deterministic date t or Never, write V_i(t;p_{−i}) for the payoff
when i uses that pure time against the fixed opponents. Independence and
conditioning on i's sampled time give

    U_i(p) = ∑[t ∈ ℕ∪{∞}] p_i(t)V_i(t;p_{−i}),
    B_i(p) = sup[t ∈ ℕ∪{∞}] V_i(t;p_{−i}).

All sums are absolutely convergent because rewards are bounded. The second
identity follows because mixtures cannot exceed the pure-time supremum and
each pure time is itself an admissible deviation. In particular E ≥ 0.

For a finite product law on F_N, define

    B_i^N(p) = max[t ∈ F_N] V_i(t;p_{−i}),
    E_N(p) = max[i ∈ I] (B_i^N(p)−U_i(p)).

Its product survival at the start of t is

    R_p(t) = ∏[i ∈ I] (p_i(∞)+∑[s≥t, s finite] p_i(s)).

Law preservation in Theorem 1 concerns the terminal coalition and the
all-Never outcome. It does not preserve the absorption date or every
finite-horizon payoff. Also, “geometric” describes the late finite component:
if its Never mass ν > 0, the actual hazard at N+ℓ is

    α(1−h)^ℓ / [ν+λ(1−h)^ℓ],

not the constant h. If the denominator is zero the history is unreached.
For h = 1, the tail has just one positive atom; interpret the first geometric
term as α and all later terms as zero.

## Source correspondence

The source comparison is bounded to the finite-menu and terminal-compression
interfaces, not a worldwide priority claim. The following declarations were
inspected in place:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  supply the existing unrestricted pure-time semantics. The mixture proof
  needed here is included above.
- `quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le` and
  `quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`
  in `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`
  give the single late candidate for an all-finite displayed profile.
- `IsSinglePivotSingletonTable` and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`
  give the exact canonical finite-law identity used in Theorem 4. They do
  not select the law or optimize an arbitrary infinite pivot law.
- `Math.Probability.abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV` in
  `MathUE/ProbabilityMassFunction/GeneralTotalVariation.lean` is the general
  discrete bounded-observable estimate underlying the censoring proof.
- `exists_elementaryCompressedProfile_terminalSemantics_close` in
  `UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`
  approximates a whole profile's terminal payoff and cap data using elementary
  tails. It does not keep the given opponent marginals fixed, preserve every
  payoff exactly, and simultaneously decrease all caps.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the existing semantic endpoint for terminal approximants at every error.
  It selects one fixed uniform-equilibrium payoff target; the present packet
  does not assume that endpoint's source has already been produced.

The new mathematics is the exact one-marginal geometric domination, its
finite LP including the nonliteral boundary, and the resulting three-law
source reduction. Narrow searches for geometric compression, first late atom,
simultaneous pivot repair, and a fixed-opponent LP found no matching earlier
declaration in the inspected quitting subtrees. No external paper theorem is
invoked. This packet makes no claim that its new statements are checked in Lean.

## Proof

### 1. Terminal outcome preservation and the signed late formula

Fix the nonpivot laws on F_N and an arbitrary pivot law μ. Put

    μ_t = μ(t) for t < N,    λ = Pr(N ≤ T_k < ∞),    ν = μ(∞).

When λ > 0, well-ordering supplies a first positive late atom t_* and its
mass α > 0. Then h = α/λ ∈ (0,1], and
∑[ℓ≥0] α(1−h)^ℓ = λ. The new law is therefore a probability law.

Fix any realization of the nonpivot times. If one is finite, its earliest
time is before N. Both pivot laws have identical probabilities of every
earlier pivot time, of joining at that time, and of continuing beyond it.
The terminal coalition probabilities are identical. If every opponent is
at Never, only the pivot's total finite versus Never mass matters; both are
unchanged. Integrating proves preservation of every terminal outcome and U_i.
The cap B_k is unchanged because its opponents are unchanged.

For j ≠ k define

    c_j = r_j({j}),   a_j = r_j({k}),   b_j = r_j({k,j}),
    d_j = ∏[ℓ∉{k,j}] p_ℓ(∞).

Let A_j be the unconditional expected contribution from a first opponent
absorption before N while j Continues. This includes possible pivot quitting
before N, and never requires division by a survival probability. For t ≥ N
let F_t = Pr(N ≤ T_k < t) and f_t = Pr(T_k = t).

If no opponent stopped before N, all nonpivot opponents other than j are
at Never. The possible late rewards from j quitting at t are: a_j if the
pivot quits before t, b_j if they tie, and c_j if the pivot is later or Never.
Consequently its exact payoff is

    A_j+d_j[c_j(λ+ν)+(a_j−c_j)F_t+(b_j−c_j)f_t].             (1)

Its Never payoff is A_j+d_j a_jλ. Against the geometric replacement, with
r = (1−h)^ℓ, one has F_{N+ℓ} = λ(1−r) and f_{N+ℓ} = αr. Hence (1) equals

    r C_j + (1−r) Z_j,

where the three relevant endpoints are

    C_j = A_j+d_j[c_j(λ+ν)+(b_j−c_j)α],
    Z_j = A_j+d_j(a_jλ+c_jν),
    W_j = A_j+d_j a_jλ.                                    (2)

C_j is the old payoff at t_*. Since F_t → λ and f_t → 0, Z_j is the limit
of old finite-date payoffs as t → ∞. Thus both are bounded by the old cap,
even if Z_j is not attained. W_j is the unchanged old Never payoff. All
head pure deviations are unchanged. Pure-time extremality proves the full
cap inequality for j and hence Theorem 1. If λ = 0, no change was made.

If c_j = 0, then Z_j = W_j; all new late finite values lie between C_j and
the actual Never payoff. This is the canonical two-endpoint simplification.
There is no sign restriction on a_j or b_j and no requirement that d_j > 0.

### 2. Definition of the finite LP

All coefficients in this subsection are computed from the fixed finite
opponent laws and the reward table. Set

    g = r_k({k}),     D = ∏[j≠k] p_j(∞),
    Q_t = V_k(t;p_{−k}) for t < N,
    W = V_k(∞;p_{−k}),     L_k = W+gD,
    B_k = max({Q_t : t < N} ∪ {W,L_k}).                     (3)

Every finite pivot time ≥ N has payoff L_k, because all finite opponent
atoms are before N. Formula (3) is therefore its exact full cap. In the
canonical case g = 1, W may be omitted from the maximum.

Introduce variables μ_0,…,μ_{N−1}, λ, ν, α, z and impose

    μ_t ≥ 0, λ ≥ 0, ν ≥ 0,
    ∑[t<N] μ_t + λ + ν = 1,
    0 ≤ α ≤ λ,       z ≥ 0.                                (4)

Define U_k = ∑[t<N] μ_t Q_t + λL_k + νW. For a nonpivot j let
π_{j,t} be its pure payoff at t < N against the opponents with this pivot
head and total remaining mass λ+ν. Let A_j have the early-contribution
meaning of subsection 1. These are well-defined affine functions of the
variables. Concretely, compute both using the finite provisional pivot law
with head μ_t, mass λ at N, and mass ν at Never; neither quantity sees the
location of the finite pivot mass at or after N. All computations are finite
sums over opponent atoms and quitting coalitions.

With s_j = p_j(∞), define

    U_j = ∑[t<N] p_j(t)π_{j,t} + s_j W_j,

where W_j, C_j, Z_j are the affine expressions (2). Prescribed payoffs do
not depend on α. Impose the following additional inequalities:

    B_k−U_k ≤ z,
    π_{j,t}−U_j ≤ z       for every j ≠ k and t < N,
    W_j−U_j ≤ z,   C_j−U_j ≤ z,   Z_j−U_j ≤ z  for every j ≠ k.       (5)

Minimize z subject to (4)–(5). This is the signed finite LP. In the
canonical case each c_j = 0, so Z_j = W_j and the repeated inequality can
be deleted. Also C_j = A_j+d_j b_jα there. The mass domain in (4) is compact;
the objective is equivalently the maximum of zero and all the finitely many
affine gains in (5). Thus a minimum exists. Denote it by z_*(p_{−k}).

For an actual geometric law with α > 0, the exact nonpivot cap is

    B_j = max({π_{j,t} : t < N} ∪ {W_j,C_j,Z_j}).             (6)

Indeed, W_j is attained at Never, C_j at N, and Z_j is the limit of the
finite geometric responses; the converse bound follows from their convex
combination. If λ = α = 0, all late finite responses equal
A_j+d_j c_jν = C_j = Z_j, and (6) still holds. Thus in both literal cases
the constraints give exactly the full behavioral regret bound.

### 3. Exact infimum and approximation of the relaxed boundary

Given any actual pivot law, Theorem 1 produces a geometric law with unchanged
payoffs and no greater E. If it has no late finite mass, it is already a
literal point with λ = α = 0. Otherwise it determines α > 0. Formula (6)
then supplies a feasible LP point of value at most its old E. Therefore

    z_* ≤ inf[μ] E(μ,p_{−k}).

Conversely, take an optimizer. If α > 0 or λ = 0, implement it literally.
The only other case is α = 0 < λ. Choose a ∈ (0,λ] as small as needed and
replace α by a while leaving all other probability variables unchanged.
Only C_j changes, by d_j(b_j−c_j)a, of absolute value at most 2Ma.
All U_i, W_j, Z_j, head candidates, and B_k remain unchanged. The resulting
actual geometric law therefore has E ≤ z_*+2Ma. In the canonical case the
sharper bound Ma holds because c_j = 0. For arbitrary η > 0, choose a so
that this increase is ≤ η; if M = 0 there is no increase for any a.

Taking η ↓ 0 proves the reverse infimum inequality and Theorem 2. The same
argument applies to any feasible point of value z. No compactness or
attainment of the original infinite-dimensional strategy optimization was
assumed. For a one-player game all nonpivot constraints disappear, with D = 1.

If reward entries and the fixed finite opponent probabilities are rational,
the displayed coefficients are rational and this is a finite rational LP.
This assertion does not select the opponent probabilities or bound the
deadline of a global search.

### 4. Censoring and the exact survival budget

Implement a feasible point up to η as just proved. If its late finite mass
is positive, retain atoms N,…,N+K−1 and move the remaining mass

    β = λ(1−h)^K

to Never. For λ = 0 take K = 0 and β = 0. This changes only one independent
marginal, by total variation β. It can be coupled with the old marginal so
that they disagree with probability β, while all other times are identical.
Any prescribed reward changes by at most 2M on that event, giving a 2Mβ
payoff bound. For any fixed nonpivot behavioral deviation the same coupling
and bound apply, uniformly over that deviator's complete stopping law. Taking
suprema yields a 2Mβ cap bound. The pivot cap is unchanged. Subtracting the
prescribed payoffs gives

    E(p) ≤ z+η+4Mβ.                                       (7)

This is full behavioral regret of the actual censored law, so every finite
menu containing that law satisfies the same error bound.

Suppose now g > 0. From (3), B_k ≥ Q_t, B_k ≥ L_k, and B_k−W ≥ gD. Thus

    B_k−U_k
      = ∑[t<N] μ_t(B_k−Q_t)+λ(B_k−L_k)+ν(B_k−W)
      ≥ νgD.

Feasibility yields νD ≤ z/g. The α perturbation leaves ν unchanged. All
finite atoms of the censored law lie before N+K. For any

    L ≥ max(N+K+H,N₀),

its joint survival at L−H consists exactly of all Never atoms. Hence

    R_p(L−H) = D(ν+β) ≤ z/g+β.                            (8)

This remains valid if D = 0, if the original joint survival was zero, or
if some player has no finite atom. No conditional error is divided by reach.

If z_* is arbitrarily small across finite opponent laws, given e,H,ρ,N₀
choose a source with z_* < min(e/3,gρ/3), implement with η < e/3, and
choose K so β < min(e/(12M),ρ/3). Here g > 0 implies M > 0. If λ = 0,
β is already zero; otherwise h > 0 makes such K finite. Equations (7)–(8)
give E < e and R_p(L−H) < ρ. This proves Theorem 3, including every stated
deadline and window quantifier.

### 5. Exact canonical source equivalence

For four laws on F_N in the canonical table, a nonpivot's pure payoff at
any finite date ≥ N equals its Never payoff because its own singleton is
zero. The pivot's corresponding payoff is W_0+D_0. By pure-time extremality,

    E(p) = max(E_N(p), W_0(p)+D_0(p)−U_0(p)).               (9)

This also proves the existing finite-menu identity directly in the present
notation. For 1 ⇒ 2 in Theorem 4, use condition 1 at ε = δ/2, keep its three
opponent laws fixed, and apply Theorem 2 to its actual finite pivot law:
z_* ≤ E(p) ≤ δ/2 < δ. For 2 ⇒ 3, use Theorem 3 with g = 1. For 3 ⇒ 1,
take e = ε, H = 1, ρ = 1, and N₀ = 1; the resulting actual finite law has
E < ε, so both terms in (9) are at most ε. No menus or profiles must be
nested, and no exact finite Nash condition is imposed.

## Boundary tests

### 1. A genuine unattained optimum

Take canonical Fin4 with all three opponents fixed at Never. Define the full
reward table by

    r_0(S) = 1 if 0 ∈ S, and 0 otherwise;
    r_1(S) = 1 if {0,1} ⊆ S, and 0 otherwise;
    r_2(S) = r_3(S) = 0.

The LP point with zero head, λ = 1, ν = α = 0, z = 0 is feasible at every
N ≥ 1. An actual pivot law with Never mass ν > 0 has pivot debt ν. If
ν = 0, some finite atom μ(t) is positive, and player 1 gains μ(t) by
quitting at t. Thus no actual law attains E = 0. Geometric laws with λ = 1,
ν = 0, and α ↓ 0 have E = α. The LP optimum is zero and its behavioral
infimum is genuinely unattained.

### 2. Signed and degenerate endpoint tests

For the signed formula, let c_j = 1, a_j = 0, b_j = −1, d_j = 1, A_j = 0,
λ = ν = 1/2, and α = λ. These data are realized with two players, the
nonpivot at Never, the pivot with one late atom 1/2, and its remaining mass
at Never. The first late payoff C_j and Never payoff W_j are both zero,
but a subsequent finite date pays Z_j = 1/2. Thus the third endpoint cannot
be dropped in arbitrary signed-singleton games.

Negative a_j or b_j causes no difficulty in the convex-combination proof.
If d_j = 0, every late term vanishes. If λ = 0, the law has no geometric
component and the literal formulas above apply. If h = 1, one retained atom
removes all finite tail mass. If ν > 0, the actual hazard is the mixture
hazard displayed in the definitions, not a constant.

The positivity assumption g > 0 belongs only to the absorption deduction.
Compression and the LP allow all signed g, but one cannot infer small
survival from the same small-value point without it: in the all-zero game,
the all-Never law has z = E = 0 and survival one. This is not a failure of
the compression theorem and is not a claim that that game lacks absorbing
equilibria.

### 3. A positive optimal-repair value for fixed opponents

Here is the full canonical reward table used for the exact numerical test.
For T = S∩{0,1,2}, the first three coordinates are:

| T | (r_0,r_1,r_2) |
| --- | --- |
| ∅ | (0,0,0) |
| {0} | (1,7,7) |
| {1} | (7,0,7) |
| {2} | (7,7,0) |
| {0,1} | (6,8,7) |
| {0,2} | (9,7,5) |
| {1,2} | (7,5,8) |
| {0,1,2} | (7,6,6) |

Player 3 receives −1 if 3 ∈ S and T ≠ ∅; receives 1 if 3 ∉ S and
S∩{1,2} ≠ ∅; and receives 0 otherwise. This specifies every nonempty
coalition. Infinite all-Continue pays zero.

Fix N ≥ 1 and τ = N−1. Player 1 has mass 4/7 at τ and 3/7 at Never;
player 2 has mass 1/7 at τ and 6/7 at Never; player 3 chooses Never.
For an arbitrary pivot law aggregate its masses as

    u = Pr(T_0 < τ),       v = Pr(T_0 = τ),
    w = Pr(τ < T_0 < ∞),   n = Pr(T_0 = ∞).

They sum to one. The pivot's pure payoffs before τ, at τ, finitely after τ,
and at Never are respectively 1, 217/49, 235/49, and 217/49. Its cap is
235/49, so its exact debt is

    d_0 = (186u+18v+18n)/49.

Player 1's Never payoff is 7−6n and its prescribed payoff is
7u+(363v+167w+41n)/49. Its gain from Never is therefore

    G_1 = (−20v+176w+8n)/49.

Because E bounds both d_0 and G_1, even when G_1 is negative,

    E ≥ (98d_0+9G_1)/107
      = (1584+16644u+252n)/5243 ≥ 1584/5243.                (10)

This lower bound covers every behavioral pivot law. When N = 1, u is
necessarily zero and the same bound applies.

It is attained here: put v = 88/107 at τ and the remaining λ = 19/107
into a geometric finite tail starting at τ+1 with h = 1/2 and ν = 0.
Thus α = 19/214. Direct finite conditioning gives:

| nonpivot | pure payoff at τ | A_j | first late payoff | Never payoff |
| --- | --- | --- | --- | --- |
| 1 | 4847/749 | 635/107 | 4901/749 | 7 |
| 2 | 4040/749 | 692/107 | 9973/1498 | 7 |
| 3 | −4901/5243 | 31/49 | 3146/5243 | 31/49 |

Any available pre-τ deviation gives a nonpivot its singleton zero. Formula
(6) controls every remaining finite date and every behavioral deviation.
The resulting complete payoff, cap, and debt calculation is:

| player | U_i | B_i | B_i−U_i |
| --- | --- | --- | --- |
| 0 | 23561/5243 | 235/49 | 1584/5243 |
| 1 | 35117/5243 | 7 | 1584/5243 |
| 2 | 35498/5243 | 7 | 1203/5243 |
| 3 | 31/49 | 31/49 | 0 |

Together with (10), this proves z_* = 1584/5243 for these fixed opponents,
independently of N. It does not give a positive gap over all four laws.

### 4. Two actual further replacements solve this example

Keep this optimized pivot law. First replace player 1 by Never. The preceding
cap calculation proves this is a full best response of value 7. Against the
now-fixed laws, player 2's Never payoff is 7, its date-τ payoff is 440/107,
and its first late payoff is 1327/214. Its other late payoffs lie between
that endpoint and 7; earlier singleton deviations pay zero. Thus replacing
player 2 by Never is a full best response as well.

After both replacements, player 1's date-τ payoff is 704/107 and its first
late payoff is 692/107, both below its Never payoff 7. Player 2's same
endpoint bounds remain below 7. Player 3 obtains zero and has no profitable
Quit: joining the pivot pays −1, and quitting alone pays zero. The pivot
quits almost surely and gets its singleton payoff and full cap 1. Hence the
final profile is exact terminal Nash with payoff (1,7,7,0).

The two replacements did not reactivate an earlier player's profitable
deviation in this particular table. This is a complete numerical boundary
test, not a proof of convergence of such updates for arbitrary reward data.
No claim about uniqueness of this table's exact finite-menu Nash profiles
is needed for any assertion in this packet.

## Adapter and consumer

The actual-data input is a finite reward table, a distinguished pivot, and
finite opponent probability vectors. Enumerating their finite quitting
outcomes gives every coefficient of (3)–(5); the LP then optimizes over the
entire unrestricted pivot response law with no supplied equilibrium or
cycle certificate. Theorem 3 converts a feasible LP point into a literal
finite product law and verifies its actual unrestricted and finite-menu
regret, along with the stated early-absorption bound when g > 0.

For canonical Fin4, Theorem 4 exactly narrows the single-pivot finite-menu
selection obligation to the three-law small-LP-value problem. If that
remaining source is produced for a table, equations (7)–(9) give terminal
approximate Nash profiles at every positive error. The existing theorem
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
then yields one fixed uniform-equilibrium payoff target. This last statement
is a conditional use of an existing semantic consumer, not a new selection
proof and not a conclusion that payoff targets may vary with the accuracy.

## Lean handoff

Suggested mathematical interfaces, not existing declaration claims:

1. Define finite-opponent stopping data and the pivot head/late/Never split
   on `Option Nat`. Prove the late finite pure-response formula (1) from
   independent stopping-law semantics for arbitrary finite I and signed
   rewards, with no positive deleted-survival hypothesis.
2. Define the geometric finite component plus Never. Prove its mass sum,
   head agreement, terminal-outcome-law equality, and the three-endpoint
   formula (2). Combine this with pure-time extremality to prove cap
   nonincrease for every behavioral deviator.
3. Define the finite affine feasible polytope (4)–(5), including α = 0 < λ.
   Prove its value equals the unrestricted pivot infimum by the two actual
   maps in subsection 3. Do not encode “equals the infimum” or an attaining
   strategy as a field of the input. Separate the literal α > 0 and λ = 0
   cases from approximation of the remaining boundary.
4. Specialize to `IsSinglePivotSingletonTable` for the canonical two-endpoint
   LP. Use `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
   for the outer-source equivalence after the actual censoring construction.
5. Implement the one-coordinate finite-tail censor and its general-PMF TV
   estimate, with a bound uniform over unilateral deviations. Retain the
   actual law, chosen displayed deadline, Never masses, and equations
   (7)–(8), not only an abstract approximate-Nash witness.
6. State the three-law small-value condition as the remaining source
   proposition, and prove its equivalence to the existing canonical
   finite-menu source shape. Do not assume a field that supplies vanishing
   LP values or assert that an outer optimizer exists.
7. Use the exact nonattainment table, the signed third-endpoint test, and
   the rational 1584/5243 fixture as small independent checks. Rational
   coefficients describe the fixed-input LP, not a bounded global algorithm.

No speculative repository refactor or alteration of the existing semantic
interfaces is required by these suggestions.

## Scope and nonclaims

The compression and exact inner LP apply to every finite player set, every
signed reward table, and every fixed finite family of nonpivot laws. The
early-absorption estimate requires a positive pivot own singleton. The
two-endpoint simplification requires zero nonpivot own singletons. All caps
are unrestricted behavioral terminal caps, not only root or bounded-memory
deviation tests.

The theorem does not preserve finite-horizon payoffs exactly, absorption
dates, a constant actual hazard when ν > 0, or payoff/cap equality under
arbitrary later changes of the opponents. LP attainment does not imply
attainment of the unrestricted pivot infimum. The outer three-law search is
not shown convex, to have a minimum, or to admit a vanishing-value sequence.
There is no general monotone repair algorithm, no requirement of exact
finite-menu Nash, and no universal Fin4 or finite-player UE conclusion.

The new statements are ordinary reviewed mathematics, not Lean-checked
results. The next open mathematical step is precisely to select the three
finite opponent laws with arbitrarily small LP value from arbitrary
canonical Fin4 reward data.
