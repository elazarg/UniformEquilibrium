# A solved canonical table with deleted Never equal to one in every bonus equilibrium

Author: CODEX_NOETHER_SUPPORT.

Status: complete ordinary-mathematical counterexample to the proposed
vanishing-deleted-Never representation implication. Not Lean-checked,
independently reviewed, or exported. Every horizon and every permitted small
bonus vector are covered. The auxiliary selector's OUTPUTS in this example
are already exact original equilibria; the result refutes necessity of its
deleted-Never certificate, not the selector's regret conclusion itself.

## 1. Exact representation question

There are four players I={0,1,2,3}. Every nonempty coalition S pays the
finite vector r(S); all-Never and preabsorption pay zero. Own singleton
rewards are (1,0,0,0). Players independently select stopping laws, with no
public correlation. For N≥1, the finite menu is F_N={0,...,N−1,Never}.

Given δ≥0 and ξ∈[0,δ]^4, the auxiliary normal-form game pays player i
its original terminal payoff plus ξ_i if its PRIVATELY PLANNED action is
Never. The bonus is paid even when an opponent absorbs earlier. No finite
action payoff is perturbed. Let E_N(ξ) be the set of exact product mixed
Nash laws of this finite auxiliary game. Define

    V(N,δ)=min { ∏_{j=1}^3 p_j(Never) :
                 ξ∈[0,δ]^4, p∈E_N(ξ) }.                   (1)

The minimum exists: the finite bonus box and product simplex are compact,
the auxiliary Nash inequalities are closed, and finite Nash existence makes
the feasible set nonempty.

For original payoffs let U_0 be the prescribed pivot value, W_0 its Never
response value, and D_0=∏_{j>0}p_j(Never). The sole additional finite-law
late-pivot gain is

    L_0=W_0+D_0−U_0.

Nonnegative Never bonuses imply W_0≤U_0 at auxiliary Nash. Menu regret
is at most δ. Thus δ→0 and V(N,δ)→0 suffice for original complete
exploitability tending to zero. The question is whether canonical UE
existence conversely guarantees some N_k→∞ and δ_k→0 with V(N_k,δ_k)→0.

The answer is NO. In the table below,

    V(N,δ)=1        for EVERY N≥1 and EVERY 0≤δ<1,          (2)

although there is an immediate exact uniform Nash profile.

## 2. Complete rational table and its original equilibrium

For the pivot set

    r_0(S)=1   if S={0},
            2   if 0∈S and |S|≥2,
            0   if 0∉S.

For each nonpivot j>0 set

    r_j(S)=−1  if j∈S and |S|≥2,
             0  if S={j},
             1  if j∉S and 0∈S,
             0  otherwise.                               (3)

These rules specify all sixty coordinates. Every reward lies in [−1,2],
and the own singleton vector is canonical. Nonpivots dislike participating
in a joint quit and receive one passively when the pivot participates.
The pivot receives a strictly positive collision premium.

Let the pivot quit at date zero and every nonpivot choose Never. The
prescribed payoff is (1,1,1,1). Against these opponents every finite pivot
response pays one and Never pays zero. A nonpivot response at date zero
pays −1, whereas every later response and Never pay one, since the pivot
has already absorbed. Thus the profile is exact terminal Nash against
every complete behavioral replacement.

It is also exact Nash for every finite-horizon average payoff: a later
pivot response merely delays reward one and cannot improve on immediate
reward one; nonpivot deviations either leave immediate absorption unchanged
or join it and receive −1. In particular (1,1,1,1) is a uniform-equilibrium
payoff, without a compact-limit existence argument.

## 3. Characterization of EVERY auxiliary Nash law

Fix ANY N≥1, 0≤δ<1, ξ∈[0,δ]^4 and p∈E_N(ξ). All probabilities below
are computed from its actual independent planned clocks. We prove

    p_0(Never)=0,       p_j(Never)=1 for j=1,2,3.           (4)

### 3.1 Never dominance eliminates every joint-quitting event

For a nonpivot j and fixed pure opponents' clocks, changing its own
planned action to Never never lowers its original payoff. If others have
already absorbed, the payoff is unchanged. If j would be the sole first
quitter, its payoff zero is replaced by either zero or one. If j would
belong to a joint first-quitting coalition, its payoff −1 is replaced by
either zero or one. The all-Never outcome is included in these possibilities.

Consequently, writing U_j and W_j for original prescribed and Never values,

    W_j−U_j ≥ Pr(j belongs to a first-quitting coalition of size ≥2).

The auxiliary gain from the pure Never replacement is

    (W_j−U_j)+ξ_j(1−p_j(Never)).

Both terms are nonnegative and Nash makes their sum nonpositive. Therefore
the probability on the right is zero. Every coalition of size at least
two contains a nonpivot, so ALL joint-quitting coalitions have probability
zero at p. This argument also covers zero bonuses; it does not rely on
strict dominance supplied by a positive subsidy.

### 3.2 The pivot quits properly and wins alone almost surely

With joint quitting excluded, the original pivot payoff is precisely
Pr(the terminal coalition is {0}). In particular

    U_0 ≤ 1−p_0(Never).

Quitting at date zero guarantees original payoff at least one, regardless
of the opponents' clocks, and earns no auxiliary bonus. Nash therefore gives

    1 ≤ U_0+ξ_0 p_0(Never)
      ≤ 1−(1−ξ_0)p_0(Never) ≤ 1.

Since ξ_0<1, p_0(Never)=0 and U_0=1. Hence the pivot is the unique
first quitter almost surely. Equivalently

    Pr(T_0<T_j for every j>0)=1.                          (5)

### 3.3 A last pivot atom excludes even unreached finite nonpivot plans

The pivot law is proper and supported on a nonempty FINITE menu. Let m
be the largest date in its support, so p_0(m)>0. Independence and (5)
imply that every finite support date of every nonpivot is strictly greater
than m. Indeed any atom at t≤m would give positive probability to
T_0=m and T_j=t, contradicting (5).

Suppose some nonpivot nevertheless has a finite support date. Let t be
the earliest such date among ALL three nonpivots. It is a legal menu date,
t>m, and no nonpivot can quit earlier than t. Let α>0 be the probability
that at least one nonpivot quits at t. If the pivot replaces its entire
law by pure t, it receives two on that event and one otherwise. Its original
and auxiliary payoff from this finite action are therefore

    2α+(1−α)=1+α>1.

Its prescribed auxiliary payoff is U_0=1, a contradiction. Thus no
nonpivot has any finite support, proving (4).

This last step is necessary. Dominance alone would allow nonpivots with
zero bonus to schedule irrelevant late finite actions after the pivot's
prescribed absorption. The collision premium makes each such first planned
late atom a profitable pivot response, eliminating those off-path plans.

### 3.4 Converse and exact minimum

Conversely, every proper pivot probability law on the N displayed dates,
together with three certain Never laws, belongs to E_N(ξ). The pivot's
finite actions all pay one, strictly above its Never bonus ξ_0<1. Each
nonpivot's Never payoff plus bonus is 1+ξ_j, while every finite response
has original payoff at most one and earns no bonus. Thus all prescribed
actions are best responses.

We have proved the entire auxiliary equilibrium set:

    E_N(ξ)=Δ({0,...,N−1}) × {Never} × {Never} × {Never}
               for ξ∈[0,δ]^4 and δ<1.                    (6)

Every feasible point of (1) has D_0=1, proving (2). Increasing horizons,
reselecting bonus vectors, changing every law, or choosing a different
global minimizer cannot alter this conclusion.

## 4. What fails and what survives

For EVERY law in (6), the original prescribed payoff and complete response
cap both equal (1,1,1,1). Also

    W_0=0,       D_0=1,       U_0=1,       L_0=0.           (7)

Thus the surrogate estimate L_0≤D_0 discards essential cancellation.
Canonical UE existence does not imply arbitrarily small deleted Never mass
inside the permitted auxiliary Nash family. This remains false when all
auxiliary selector outputs are exact original equilibria.

The result therefore does NOT refute a possible universal theorem that
globally chosen auxiliary Nash laws themselves have small original late
gain. It does not refute minimizing L_0 instead of D_0, or the separate
compensated geometric-pivot correspondence. Those are different questions.
It also does not exclude small D_0 among original APPROXIMATE equilibria:
exact auxiliary Nash and the permitted Never-only bonuses are material
restrictions in (6).

The precise failed implication is

    canonical UE existence
      ⇒ some N_k→∞, δ_k→0 with V(N_k,δ_k)→0.

Its reverse implication remains the valid sufficient construction in
[the bonus-box note](CODEX_NOETHER_SUPPORT__GLOBAL_NEVER_BONUS_SELECTION_AND_DISCOUNT_STALL.md).
No all-error approximation theorem with arbitrary finite-action subsidies
is substituted for the permitted Never-only program.

The exact omitted slack can also be recorded. This identity was pointed
out independently by CODEX_FRECHET_CYCLE after the counterexample derivation.
For an arbitrary auxiliary Nash law put z_i=p_i(Never) and

    k_i=U_i+ξ_i z_i−W_i−ξ_i≥0.

This is the auxiliary payoff slack of its Never response, and elementary
rearrangement gives the exact canonical identity

    L_0=D_0−ξ_0(1−z_0)−k_0.                              (8)

If z_0>0, support optimality forces k_0=0; on that face small actual late
gain and small bonuses do force small D_0. If z_0=0, the unused Never
response can have positive slack. In the present fixture k_0=1−ξ_0,
so the two subtractions in (8) cancel D_0=1 exactly. Both the bonus term
and the unused-action slack must be retained; claiming k_0=1 at nonzero
pivot bonus would be incorrect.

## 5. Narrow source and prior-work comparison

The current finite-menu identity and complete deviation interpretation were
read in `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
and `singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar`, in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The target is the current
[canonical finite-menu question](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md).

The prior-work lookup read
[RENY's positive-bonus completeness test](CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md),
[HILBERT's expressiveness test](CODEX_HILBERT__COMPENSATED_SELECTOR_EXPRESSIVENESS_TEST.md),
and [FRECHET's compensated boundary tests](CODEX_FRECHET_CYCLE__COMPENSATED_NEVER_SELECTOR_BOUNDARY_TESTS.md).
Those concern a globally optimized geometric pivot with compensation and
exact outer equations. Their remaining approximation-to-exactification
question is not answered negatively by this different deleted-Never test.
HILBERT's
[fixed-label bonus obstruction](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md)
uses Never dominance for one subsidized passive player. Here the distinct
content is a single canonical table with the ENTIRE equilibrium set (6)
for every bonus vector in the box and every horizon, using the collision
premium to eliminate all late off-path finite atoms.

Small rational checks enumerate all auxiliary equilibria on half-grid
mixed-law simplices for N=1,2,3 and several bonus vectors in the permitted
box. They are recorded in
[the owned checker](../experiments/CODEX_NOETHER_SUPPORT__CHECK_BONUS_BOX_DELETED_NEVER_FLOOR.py).
These checks test the table and boundary formulas; the all-real/all-horizon
proof is Section 3, not a finite-grid inference.

## 6. Actual output completeness: the exact remaining distinction

Let G_N,δ be the compact feasible set of bonus vectors and auxiliary Nash
laws used in (1), and let T_N,δ⊆G_N,δ be its set of D_0 minimizers. Define

    A(N,δ)=min_(ξ,p)∈G_N,δ E(p),
    B(N,δ)=min_(ξ,p)∈T_N,δ E(p),
    C(N,δ)=max_(ξ,p)∈T_N,δ E(p).

Complete exploitability on a fixed finite menu is continuous, since its
pure-response cap is a maximum of finitely many continuous response values,
including Never and one late date. These extrema therefore exist. They obey

    0≤A(N,δ)≤B(N,δ)≤C(N,δ)≤max(δ,V(N,δ)).                (9)

Vanishing A asks whether SOME permitted auxiliary Nash outputs suffice.
Vanishing B asks whether SOME minimizers of the deleted-Never objective
suffice. Vanishing C would make EVERY such optimizer safe. These are
different representation and tie-selection assertions.

In the present table A=B=C=0 for every N and δ<1, despite V=1. Thus
every optimizer succeeds; the many ties between proper pivot laws do not
require a second objective on this regression.

For an alternative global objective put

    ℓ(N,δ)=min_(ξ,p)∈G_N,δ L_0(p).

Every minimizer has E(p)≤max(δ,ℓ(N,δ)), while any law attaining A has
L_0≤A. Hence

    max(0,ℓ(N,δ)) ≤ A(N,δ) ≤ max(δ,ℓ(N,δ)).               (10)

Minimizing actual late gain is consequently equivalent, up to the known
vanishing menu error δ, to the SOME-output criterion A. This algebra is
not a producer: proving A→0 still requires a good exact auxiliary Nash
branch from the raw table or from an already supplied approximation source.

The narrow subsequent lookup read the coupled-selector parts of
[RENY's pivot-LP/outer-bonus note](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md),
the statement and scope of
[its zero-extra-bonus obstruction](CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION.md),
HILBERT's adaptive portfolio, and its
[bounded timing-incentive test](CODEX_HILBERT__BOUNDED_TIMING_INCENTIVE_TEST.md).
Those results do not settle A here: bad branches need not minimize an
objective; zero-bonus impossibility does not exclude arbitrarily small
positive bonuses; the compensated geometric pivot changes the feasible
correspondence; and arbitrary finite-action subsidies are not allowed.

Current next question: does canonical UE existence imply some sequence
N_k→∞, δ_k→0 with A(N_k,δ_k)→0? No all-horizon counterexample or universal
approximation-to-bonus-Nash theorem is proved in this note. The failed V
criterion must not be substituted for this still-open actual-output test.
