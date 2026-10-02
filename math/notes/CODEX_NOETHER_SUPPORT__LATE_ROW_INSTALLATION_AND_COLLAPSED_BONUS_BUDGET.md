# Late-row installation benefit and the collapsed-source bonus budget

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary-mathematics installation ledger, not an exported producer.
It isolates the raw reward signs behind the H availability calculation.
The required SAME-BOX source comparison is an explicit hypothesis, not a
consequence of constrained equilibrium. No source-forced upper bound on
the source cost, renewable descent, or general selector is established.

## 1. Literal source and availability branch

Let p be an exact private-Never-bonus equilibrium on
F_N={0,...,N−1,Never}, with ξ∈[0,δ]^4, for a bounded canonical Fin4 table.
Write z_i=p_i(Never), D_0=∏_(j>0)z_j, and suppose original full E(p)>δ.
The pivot is then the unique maximum debtor, and its old late response
strictly exceeds every old menu response by at least E(p)−δ.

Let q(α), α≥0, be a differentiable family of ACTUAL independent laws on
F_(N+1), with q(0)=p and new-date masses

    q_i(α)(N)=αh_i+o(α),        h_i≥0.

Write q_i(α)(Never)=z_i(α). Define the collapsed law p̄(α) on F_N by
moving ONLY each new-date mass back to that player's Never atom. Its old
finite atoms are exactly those of q(α). No source or tester date is erased
when evaluating E(q(α)); its full testers include N AND N+1.

The installation identities below hold for any such differentiable laws.
The additional bonus-source statement uses the assumption that q(α) is
constrained Nash with only an availability bound on its new-date mass,
using bonuses ξ(α)∈[0,δ]^4. Assume also that each player retains positive
Never mass, so its old-submenu support comparisons include Never.

## 2. Exact collapsed-source correspondence and its budget condition

For any player i and old finite response t<N, moving an opponent's date-N
mass to Never changes no outcome: i itself quits earlier. Thus ALL old
finite response values, not only supported ones, agree under q and p̄.

Let W_i(q) and W_i(p̄) be original Never responses. Their exact difference
is the last-row absorbing contribution

    H_i=Σ_(∅≠S⊆I\{i})
          [∏_(j∈S)q_j(N) ∏_(j∉S,j≠i)q_j(Never)] r_i(S).  (1)

Set

    χ_i=ξ_i+H_i.                                      (2)

At a constrained Nash law with positive Never mass, every positive old
finite atom ties W_i(q)+ξ_i, and every old finite response is at most
that value. Under p̄, Never plus χ_i has EXACTLY that same value. The
collapsed law is therefore exact Nash on its OLD menu with bonuses χ,
PROVIDED

    0≤χ_i(α)≤δ for every i and all sufficiently small α. (3)

This proof also covers a player using only Never in the old submenu:
its finite responses are merely bounded above. It does not cover a player
with no retained Never action without checking that player's support
separately. Condition (3) is not automatic because the table is signed
and the original bonuses may lie on either face of their box.

For differentiable bonuses, the first derivative in (2) is

    χ'_i(0)=ξ'_i(0)+Σ_(j≠i) h_j[∏_(k≠i,j)z_k]r_i({j}). (4)

Actual interval feasibility (3), not just weak derivative signs, is the
source-budget hypothesis used below. If p is a GLOBAL A(N,δ) minimizer
and (3) holds, then E(p̄(α))≥E(p). Thus its derivative, when defined,
is nonnegative. This gives a LOWER bound on the collapsed-source cost,
not the upper bound needed for an installation improvement.

## 3. Exact first-order full-error installation ledger

Put D_(0j)=∏_(k≠0,j)z_k for j>0. Define two raw source coefficients

    P_late=h_0D_0
       +Σ_(j>0)h_jD_(0j)[1−(1−z_0)r_0({j})],

    P_tie=h_0D_0
       +Σ_(j>0)h_jD_(0j)[1+z_0r_0({j})−r_0({0,j})].  (5)

Let C=(d/dα)E(p̄(α)) at zero. Then

    (d/dα)_+ E(q(α)) at zero = C−min(P_late,P_tie).    (6)

Here is the full-response derivation. At zero the pivot's two exposed
tests N and N+1 are tied at E(p), strictly above every other tester.
This finite strict separation persists nearby. At the collapsed profile
the pivot's old late test likewise remains uniquely above its old menu.
The first-order contribution of two or more newly quitting players is
zero, so it suffices to enumerate each singleton new-date event.

Its prescribed payoff increment, relative to collapse, has derivative

    h_0D_0 + Σ_(j>0)h_j z_0D_(0j)r_0({j}).

For the pivot's response N+1 the payoff increment has derivative
Σ_(j>0)h_jD_(0j)[r_0({j})−1]. Subtracting the prescribed increment
gives −P_late. For its response N the payoff increment instead has
derivative Σ_(j>0)h_jD_(0j)[r_0({0,j})−1], giving −P_tie. Taking the
maximum of these two retained derivative values proves (6). The same
formula follows by expanding the finite product probabilities; it does
not assume that waiting until N+1 remains better than joining at N.

The exact source-level sign needed for this particular branch is therefore

    C < min(P_late,P_tie).                            (7)

Even when collapse is admissible in the SAME bonus box, global minimality
only gives C≥0. It does not prove (7). Both coefficients in (5) can have
either sign for general canonical raw rewards.

There is one particularly simple target: set h_0=1 and h_j=0 for j>0.
Then P_late=P_tie=D_0>0, regardless of the off-diagonal rewards. The
missing inequality becomes C<D_0. If the collapsed old auxiliary-Nash
path extends to BOTH signs of α within the SAME bonus box through an
actual global minimum, its differentiable cost must satisfy C=0. That
would settle the sign for this path. Current source/support hypotheses
do not supply a two-sided feasible path: in particular a zero bonus or
a support face can obstruct its reverse direction. No generic regularity
or selected-component continuation is inferred here.

## 4. What happens in the checked H local calculation

For the local branch in
[the availability test](CODEX_NOETHER_SUPPORT__AVAILABILITY_HOMOTOPY_FULL_OBJECTIVE_TEST.md),
the source is z=(2/3,3/4,1/2,1), h=(1,1,1,0), ξ=0. Equations (1)–(4)
give, for the three active players,

    (χ'_0,χ'_1,χ'_2)=(9/4,1/3,7/12).

Player 3 remains strictly pure Never and may retain bonus zero after
collapse. The active collapsed bonuses are positive for small α. They
therefore LEAVE the SAME zero bonus box. In particular, A(1,0)-minimality
cannot be applied to this collapsed law. For any fixed positive budget
they eventually fit, but the original source has not here been proved
globally minimizing in that different budget.

Direct calculation of the collapsed old-source error gives C=33/64.
Indeed its Never masses are 1−a_i(α), so the derivative of its pivot
deleted product is 81/64; its required pivot bonus derivative 9/4 is
multiplied by its finite mass 1/3, subtracting 3/4. H's raw rewards give

    P_late=7/8,          P_tie=9/8.

Thus (6) yields 33/64−7/8=−23/64, agreeing with the direct full-cap
calculation. The successful sign is a SPECIAL reward-dependent benefit
exceeding the source cost, not a consequence of the minimum label alone.

The invariance of old finite responses under later-tail changes is already
used in RENY's [finite-head coupling](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md).
The complete response split is the one in
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).
These source facts do not supply the budget condition or inequality (7).

Next question: can a genuine positive limiting A minimum force an available
branch with (3) and an upper source-cost bound strong enough for (7), while
also controlling repeated use or eventual full error? The present ledger
identifies that comparison but proves neither of those additional facts.
