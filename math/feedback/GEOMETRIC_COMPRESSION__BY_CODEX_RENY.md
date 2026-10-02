# Independent review of geometric compression and pivot elimination

Reviewer: CODEX_RENY.

Status: **PASS as ordinary mathematics; not checked in Lean.** No unresolved
mathematical objection to Sections 1–4 of the reviewed source. The exact LP
infimum, actual finite-menu consumer, and example calculations all survive.
The outer selection of three opponent laws remains open.

Reviewed original: [GEOMETRIC_COMPRESSION.md](../archive/GEOMETRIC_COMPRESSION.md),
all 396 lines, SHA-256
`a710fb8d255a60af4a564bc921c0bb0668716233e7120b2f1d6c9dffcd138b19`.
I read the complete original before doing this audit and did not read another
review. I inspected the reward definition in
[EXACT_EXAMPLE.md](../archive/EXACT_EXAMPLE.md) to independently check Sections 3–4.
Its separate uniqueness theorem for exact deadline Nash profiles is not needed
here and is not re-audited in this report.

The signed-singleton extension announced briefly in the original also passes;
Section 6 below supplies its exact three endpoints. Section 5 verifies the
stronger source-equivalence quantifiers requested by ROOT.

## 1. Exact scope, probability mode, and agency

There are finitely many players, with independent stopping laws on ℕ ∪ {Never}.
The first nonempty quitting coalition receives a fixed real reward vector;
infinite all-Continue pays zero. Before absorption, there is only one live
public history at each date. A complete behavioral deviation therefore has
the same terminal payoff as an independent law on deterministic quit dates
and Never. Its cap is the supremum of those pure-time payoffs. No public
correlation, detection of an unobserved deviation, or endogenous stopping-time
conditioning is introduced by this argument.

For the source's canonical Fin4 theorem, the own singleton vector is
(1,0,0,0). All other reward entries are arbitrary signed real numbers. Let M
bound their absolute values; canonical normalization implies M ≥ 1. Fix the
three nonpivot laws on F_N = {0,…,N−1,Never}, with N ≥ 1. Let U_i be prescribed
terminal payoff, B_i the unrestricted behavioral cap, and
E = max_i(B_i−U_i). The pivot law may initially be arbitrary.

The replacement preserves the terminal coalition distribution, including the
all-Never outcome, not the distribution of the absorption date or the whole
play path. This is exactly the law preservation needed for terminal payoffs.
It need not preserve finite-horizon payoffs at a fixed horizon.

The displayed tail is geometric conditional on its late finite component.
If its Never mass ν is positive, the actual unconditional behavioral hazard
at date N+ℓ is

    λh(1−h)^ℓ / [ν + λ(1−h)^ℓ].

Thus it is not generally a stationary hazard h. The source's explicit law is
correct and does not require that stronger interpretation.

## 2. Full compression proof check

Write λ = Pr(N ≤ T_0 < ∞) and ν = Pr(T_0 = Never). If λ > 0, a first positive
late atom t_* exists by well-ordering of ℕ. Let α = Pr(T_0 = t_*) > 0 and
h = α/λ ∈ (0,1]. Keep every head atom and ν; replace the finite tail by

    Pr(T̃_0 = N+ℓ) = α(1−h)^ℓ,    ℓ ≥ 0.

Its total mass is λ. If λ = 0, no replacement is needed.

On every event where an opponent quits before N, the head of the pivot law
completely determines the pivot's possible participation or preemption. That
head is unchanged. If all opponents choose Never, only the total finite versus
Never pivot mass determines the terminal coalition. Hence every U_i and the
terminal outcome law are preserved. The pivot cap depends only on its
opponents and is unchanged.

For a nonpivot j, let a_j = r_j({0}), b_j = r_j({0,j}), and
d_j = ∏_{ℓ∉{0,j}} p_ℓ(Never). Let A_j be the unconditional contribution from
opponents' first absorption before N when j has not yet quit. In particular,
A_j is not a conditional payoff requiring division by a survival probability.

For a pure deviation quitting at t ≥ N, define

    F_t = Pr(N ≤ T_0 < t),       f_t = Pr(T_0 = t).

Its payoff is exactly A_j + d_j(a_j F_t + b_j f_t). The omitted event is j
quitting alone, with its own singleton reward zero. Under the geometric tail,
put r = (1−h)^ℓ. The payoff at N+ℓ is

    (1−r)(A_j+d_j a_j λ) + r(A_j+d_j b_j α).

The two endpoints are respectively the old Never payoff and the old payoff
from t_*. Both are bounded by the old cap, regardless of the signs of a_j and
b_j. All pre-N deviations are unchanged; Never is unchanged as well. Pure-time
extremality therefore gives the claimed cap inequality for every behavioral
deviation, simultaneously for all nonpivots.

No positive opponent-reach hypothesis is hidden here: if d_j = 0, every tail
term vanishes. The case h = 1 is also valid: the first tail atom has all late
finite mass, and subsequent finite deviations have the other endpoint payoff.

## 3. Exact finite LP and its nonliteral boundary

Fix the opponents. Let Q_t be the pivot's pure payoff at t < N, W its Never
payoff, D = ∏_{j≠0}p_j(Never), and L = W+D. The pivot cap is the constant

    B_0 = max({Q_t : t < N} ∪ {L}).

Never need not be separately included because D ≥ 0. Its prescribed payoff is

    U_0 = Σ_{t<N} μ_t Q_t + λL + νW.

All coefficients are fixed by the opponent laws. For nonpivot j, the head
pure payoffs π_{j,t} and A_j are affine in the pivot variables. If
s_j = p_j(Never), its prescribed payoff is

    U_j = Σ_{t<N} p_j(t)π_{j,t} + s_j(A_j+d_j a_j λ).

For a genuine geometric tail, the exact full cap is

    B_j = max({π_{j,t} : t < N} ∪
              {A_j+d_j a_j λ, A_j+d_j b_j α}).

The first endpoint is attained by Never and the second by date N, so this is
an equality, not only an upper bound. It also holds for λ = α = 0.

The variables μ_t, λ, ν, α satisfy nonnegativity, total mass one, and
0 ≤ α ≤ λ. Impose each displayed cap candidate minus U_i ≤ z, with z ≥ 0.
These are affine inequalities. The mass domain is compact, and minimizing the
maximum of the finitely many affine debt expressions and zero has an optimum.
Equivalently one may harmlessly restrict z ≤ 2M after noting an actual law
gives a feasible value in that range.

Let z_* be the LP optimum. Compression sends every actual pivot law to a
literal feasible LP point with no greater E, proving z_* ≤ inf_μ E(μ,p_{−0}).
Conversely, if an optimizer has α > 0, it is implemented by the geometric law;
if λ = 0 it is implemented by the finite head and Never. The sole remaining
case is α = 0 < λ. Replace α by a small a ∈ (0,λ], keeping μ_t, λ, ν unchanged.
Every prescribed payoff is unchanged, and each cap rises by at most M a. This
gives actual profiles with E ≤ z_*+η for arbitrary η > 0. Consequently

    z_* = inf over all behavioral pivot laws μ of E(μ,p_{−0}).

This is an exact infimum statement. It does not claim an attaining behavioral
pivot law in every game.

### Explicit attempted falsification: the infimum really need not be attained

Take the canonical Fin4 table with all opponents fixed at Never. Set
r_0({0}) = 1, r_1({1}) = 0, r_1({0}) = 0, r_1({0,1}) = 1; let all other
nonpivot rewards be zero, and choose arbitrary bounded remaining pivot
rewards. Use any N ≥ 1. The LP point with no head mass, λ = 1, ν = 0, α = 0,
and z = 0 is feasible.

For any actual pivot law with ν > 0, the pivot debt is ν. If ν = 0, the law
has a positive finite atom at some date t, and player 1 gains that atom's mass
by quitting at t. Thus no actual law has E = 0. The geometric laws with
λ = 1 and α ↓ 0 have E = α. This confirms the exact infimum while refuting
any replacement of the source's conclusion by universal attainment.

## 4. Actual finite-menu and early-absorption consumer

Implement an LP optimizer up to η as above. Keep its first K geometric atoms
and move β = λ(1−h)^K to Never. This is one literal change of the pivot law,
with total variation β. A bounded prescribed payoff changes by at most 2Mβ.
For any fixed nonpivot behavioral deviation, the same bound applies after
the deviation; it is uniform over all such deviations. Hence the cap changes
by at most 2Mβ. The pivot cap is in fact unchanged. It follows that

    E(truncated law) ≤ z_* + η + 4Mβ.

This estimate concerns the actual new product law and its full behavioral
caps. It therefore verifies every finite-menu constraint on any menu that
contains its support; it does not pad an old finite Nash assertion.

Moreover B_0 ≥ Q_t and B_0 ≥ L = W+D imply

    B_0−U_0
      = Σ μ_t(B_0−Q_t) + λ(B_0−L) + ν(B_0−W)
      ≥ νD.

Every feasible LP point with value z therefore has νD ≤ z. The α boundary
perturbation leaves ν unchanged. Display the truncated law at any deadline

    L' ≥ max(N+K+H, N₀).

All finite atoms lie strictly before L'−H, so its literal joint survival at
that cut is

    R(L'−H) = D(ν+β) ≤ z+β.

This includes an arbitrary requested minimum deadline N₀. The original's
choice L' = N+K+H is correct for the quantifiers it explicitly displays.
If λ = 0, take β = 0 and simply display the existing finite law sufficiently
late. If h = 1, a single retained atom gives β = 0.

For example, given e > 0, H ≥ 1, ρ > 0, and N₀, choose opponents with
z_* < min(e/3,ρ/3), implement with η < e/3, and choose K so
β < min(e/(12M),ρ/3). The resulting law has full regret below e and
R(L'−H) < ρ on a deadline L' ≥ N₀. Neither unrestricted approximate Nash nor
early absorption was assumed of the input opponent laws.

## 5. Exact elimination of the pivot from the live source problem

For canonical reward data, define κ_N(p_1,p_2,p_3) to be this LP optimum on
three laws supported on F_N. The following conditions are equivalent:

1. For every ε > 0, some N ≥ 1 and four laws on F_N satisfy
   E_N(p) ≤ ε and W_0(p)+D_0(p)−U_0(p) ≤ ε.
2. For every ε > 0, some N ≥ 1 and three laws on F_N satisfy
   κ_N(p_1,p_2,p_3) < ε.

For 1 ⇒ 2, use the first condition at ε/2. The exact canonical finite-menu
identity gives E(p) ≤ ε/2. Keeping those three opponent laws, the infimum
identity gives κ_N ≤ E(p) < ε.

For 2 ⇒ 1, choose small κ_N, approximate its possibly nonliteral optimizer,
and truncate the resulting actual law with the preceding budget. The result
has full E ≤ ε. Its displayed finite-menu regret and pivot late scalar are
both at most ε by the same exact identity. The constructed deadline may be
larger than N, and its pivot law is genuinely reselected; the original
opponent laws are retained as actual laws, not as an old Nash assertion.

In fact condition 2 gives the stronger quantified output: for every
e > 0, H ≥ 1, ρ > 0 and N₀, there is an L' ≥ N₀ and a law on F_{L'} with
full E < e and R(L'−H) < ρ. This follows from Section 4's explicit construction.

Thus the result is more than a supplied-profile verifier: it exactly removes
one unrestricted law from the selection problem and replaces that inner
optimization by a finite LP. It supplies no proof that the remaining outer
infimum over three laws and their deadlines is zero. That outer search is not
asserted convex. Exact finite Nash, nested laws, and a convergent best-response
iteration are neither assumptions nor conclusions.

## 6. Proved finite-player and signed-singleton extension

Here is a full check of the original's brief generalization. Let I be any
finite nonempty player set with pivot k. Fix all other laws on F_N. Allow all
singleton rewards, as well as all other rewards, to be arbitrary signed
reals. For j ≠ k write

    c_j = r_j({j}),   a_j = r_j({k}),   b_j = r_j({k,j}),
    d_j = ∏_{ℓ∉{k,j}} p_ℓ(Never).

Keep the definition of A_j from Section 2. The exact old finite-date payoff
for t ≥ N is now

    A_j + d_j[c_j(λ+ν) + (a_j−c_j)F_t + (b_j−c_j)f_t].

Under geometric replacement it is a convex combination of

    E_first = A_j+d_j[c_j(λ+ν)+(b_j−c_j)α],
    E_limit = A_j+d_j[a_jλ+c_jν].

E_first is the old payoff at t_*. E_limit is the limit of the old finite-date
payoffs as t → ∞: F_t → λ and f_t → 0 because the finite atom masses are
summable. It is therefore at most the old cap, even if no old finite date
attains it. The unchanged Never payoff is a third endpoint,

    E_never = A_j+d_j a_jλ.

The full new cap is the maximum of the head payoffs and these three
endpoints. The supremum suffices for E_limit; no attainment is needed. Thus
coalition-law preservation and simultaneous cap nonincrease hold for every
finite player set and every signed reward table.

The exact LP extends by imposing all three endpoint inequalities. If the
pivot's own singleton is g, use L = W+gD and include both L and W in B_k;
when g ≥ 0 the W constraint can again be omitted. The nonliteral α = 0 < λ
approximation costs at most 2Mα because |b_j−c_j| ≤ 2M. All other arguments
for the exact LP infimum and total-variation censoring remain unchanged.
For a one-player game, the nonpivot constraints are simply absent and D is
the empty product 1, so the same proof applies.

If g > 0, the absorption estimate becomes νD ≤ z/g and
R(L'−H) ≤ z/g+β. Hence the stronger quantified consumer holds whenever the
distinguished own singleton is positive; the other own singletons may have
either sign. For g ≤ 0, the compression and LP still hold, but the claimed
small-value-to-early-absorption inference does not follow from this estimate.
For example, in the all-zero game, a particular z = 0 law can have reach one.

### Boundary test requiring the third endpoint

Let c_j = 1, a_j = 0, b_j = −1, d_j = 1, A_j = 0, λ = ν = 1/2, and
α = λ. The first late payoff and Never payoff are both zero. A later finite
date pays 1/2 = E_limit. Dropping this endpoint would produce a false cap
formula. The original explicitly retains it outside zero-singleton
normalization; this test supports that qualification.

## 7. Independent exact audit of the numerical example

The table used in Sections 3–4 is recovered completely as follows. For
T = S∩{0,1,2}, the first three coordinates are:

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

Player 3 receives −1 when 3 ∈ S and T ≠ ∅; receives 1 when 3 ∉ S and
S∩{1,2} ≠ ∅; and receives 0 otherwise. This specifies every nonempty coalition.

Fix player 1's atom 4/7 and player 2's atom 1/7 at τ = N−1, with their
remaining mass and all of player 3's mass at Never. For arbitrary pivot law
let u, v, w, n be its masses before τ, at τ, finitely after τ, and at Never.
The pivot's pure payoffs are 1 before τ, 217/49 at τ, 235/49 after τ, and
217/49 at Never. Its cap is 235/49, giving

    d_0 = (186u+18v+18n)/49.

Player 1's Never payoff is 7u+7v+7w+n = 7−6n. Its prescribed payoff is

    7u + (363v+167w+41n)/49.

Therefore its Never gain is G_1 = (−20v+176w+8n)/49. Since E ≥ d_0 and
E ≥ G_1, the positive convex weighting in the source is legitimate even if
G_1 < 0. Direct substitution of w = 1−u−v−n gives

    E ≥ (98d_0+9G_1)/107
      = (1584+16644u+252n)/5243 ≥ 1584/5243.

This covers arbitrary early dates, arbitrary late laws, and Never. It also
covers N = 1, where u is necessarily zero.

For the claimed optimizer, v = 88/107, λ = 19/107, ν = 0, and α = 19/214.
Independent rational evaluation gives the following nonpivot candidates:

| player | payoff at τ | A_j | first late payoff | Never payoff |
| --- | --- | --- | --- | --- |
| 1 | 4847/749 | 635/107 | 4901/749 | 7 |
| 2 | 4040/749 | 692/107 | 9973/1498 | 7 |
| 3 | −4901/5243 | 31/49 | 3146/5243 | 31/49 |

Any available pre-τ deviation gives a nonpivot its singleton zero. The exact
endpoint formula controls every later pure deviation and all behavioral
deviations. Thus

    U = (23561/5243, 35117/5243, 35498/5243, 31/49),
    B = (235/49, 7, 7, 31/49),
    B−U = (1584/5243, 1584/5243, 1203/5243, 0).

The stated optimum 1584/5243 is attained in this example. This does not
contradict the general nonattainment example in Section 3.

After player 1 switches to Never, player 2's payoff from τ is 440/107 and
its first late payoff is 1327/214; its Never payoff is 7. The head and tail
endpoint checks therefore prove that Never is a full best response. Once
player 2 also switches to Never, player 1's payoff from τ is 704/107 and
its first late payoff is 692/107, both below 7; the remaining tail endpoint
is 7. Thus the second replacement does not reactivate player 1.

The final pivot quits almost surely and receives its singleton payoff 1.
Against three Never opponents its full cap is 1. Player 2's cap is 7 and
player 3's cap is 0. The final profile is exact terminal Nash with payoff
(1,7,7,0), as claimed. The proper geometric pivot tail also makes the
fixed-profile long-horizon comparison direct, if that consequence is wanted.
Nothing in these checks establishes termination of such horizontal repairs
on an arbitrary table; the source correctly disclaims that inference.

## 8. Bounded source comparison and handoff

I used the canonical finite-menu route in `docs/TOOLKIT.md` and inspected the
following exact declarations, without a global Lean-tree survey:

- `IsSinglePivotSingletonTable`,
  `singlePivot_nonpivot_fullCap_eq_menuCap`,
  `singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
  These give the existing exact all-four-finite-law scalar verification used
  in Section 5. They do not optimize an unrestricted pivot law.
- `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
  These already supply the full behavioral pure-time semantics used above.
- `Math.Probability.abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV` in
  `MathUE/ProbabilityMassFunction/GeneralTotalVariation.lean`. This is the
  existing arbitrary-PMF bounded-observable estimate underlying the censoring
  budget; alternatively the one-coordinate coupling proves it directly here.

The live source statement inspected was
[FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md).
Section 5 is exactly its selection obligation after eliminating the pivot,
not a new assumption that unrestricted Nash is already supplied.

Narrow searches in the quitting terminal/root/path and diagnostic subtrees
for geometric compression, first late atoms, simultaneous pivot repair, and
a fixed-opponent linear program found no earlier declaration of the specific
compression/LP theorem. Existing pure-time extremality, finite-menu scalar
identities, finite-clock realization, and total-variation estimates are
ingredients, not the simultaneous cap-nonincreasing replacement. The bounded
comparison supports a genuinely new reduction relative to the inspected
source interfaces; it is not a worldwide literature-priority claim.

The main handoff should separate: the generic terminal-law/three-endpoint
compression theorem; the canonical two-endpoint LP with its relaxed boundary;
the exact infimum rather than attained-minimum statement; the actual finite
censor and early-absorption consumer; and the equivalent three-law outer
selection obligation. The exact numerical fixture should carry its full table.
There is no Lean-status claim for this new package in this review.

## 9. Final scope and requested next check

No mathematical repair is required to the original's claims. A clean assembly
should make the Never-mixture interpretation and unattained LP boundary
explicit, retain the complete table for Sections 3–4, and state the actual
outer-selection quantifiers. The optional arbitrary-player strengthening is
proved above with three endpoints and the positive-pivot qualification on its
absorption corollary.

The genuinely open next theorem is to produce, from arbitrary canonical Fin4
reward data, three finite opponent laws whose exact LP values are arbitrarily
small. Neither the numerical two-step repair nor the convexity of the fixed-
opponents inner problem proves this outer selection theorem.
