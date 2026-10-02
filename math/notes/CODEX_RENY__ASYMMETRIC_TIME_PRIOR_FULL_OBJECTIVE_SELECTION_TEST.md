# One asymmetric time-prior rule: geometric success and an undecided cyclic selector

Author: CODEX_RENY.

This bounded test concerns one explicit rule, not all entropy or logit
selectors. On the geometric table below, the existing invariant-set proof
supplies a successful branch for the rule. On the cyclic table, only the
known weak-tie representability obstruction is obtained. The full-objective
selector on that table remains undecided, so this note neither declares the
rule successful in general nor refutes it. No new game-class coverage or
export is claimed. The mathematics is not newly checked in Lean.

## 1. The table-driven rule and its exact target

There are four players, independent private stopping laws on
ℕ∪{Never}, terminal rewards r(S) for nonempty quitting coalitions, and
zero payoff when all players Never. The table has own-singleton vector
(1,0,0,0), identifying pivot 0. The labels order the other three players;
the rule does not choose an order from a supplied successful strategy.

On F_N={0,…,N−1,Never}, for N≥1, use the positive reference weights

    π₀(t)=2^(−t−1),        π₀(Never)=2^(−N),
    π_j(t)=exp(−4^(t+j)),  π_j(Never)=1,    j=1,2,3,
    τ_N=4^(−N).                                            (1)

The pivot weights already sum to one. Normalize each nonpivot's weights
by their finite positive sum if probability priors are desired; this
changes no equation below. Every finite action and Never has strictly
positive weight. The distinct nonpivot priors break their player symmetry.

Let f_i(t;p₋ᵢ) be the literal pure-time payoff. Define the weighted-logit
map on the product of finite menu simplexes by

    L_i(p)(t)=π_i(t)exp(f_i(t;p₋ᵢ)/τ_N)
                 /Σ_(u∈F_N)π_i(u)exp(f_i(u;p₋ᵢ)/τ_N).       (2)

All prescribed laws and deviations remain independently randomized.
Each fixed point has positive mass on every menu action, including Never.
The map is continuous, so Brouwer gives a fixed point. Its fixed-point
set C_N is a nonempty closed subset of the compact product simplex.

The selector chooses ANY minimizer over C_N of the FULL objective

    F(p)=max_i [sup_(t∈ℕ∪{Never})f_i(t;p₋ᵢ)−U_i(p)]
        =max(E_N(p),L₀(p)),
    L₀(p)=f₀(Never;p₋₀)+∏_(j≠0)p_j(Never)−U₀(p).           (3)

For a finite source, all full responses are represented by the finite
test set {0,…,N,Never}, so F is continuous and the minimum exists.
The rule minimizes neither menu regret alone nor distance to a reference
profile, and is not restricted to a symmetry-invariant fixed-point set.

The exact target tested is

    inf_(N≥1) min_(p∈C_N) F(p)=0.                           (4)

Compactness gives an existence selector, not an executable global
optimization algorithm. Even for rational rewards, (2) has exponential
constraints; no polynomial-feasibility or exact global fixed-point
selection algorithm follows here. Nor does a successful local root solve
certify a global minimum over C_N.

## 2. The geometric table: actual success of this selector

Let the active coordinates 0,1,2 have coalition rows

    {0}: (1,7,7),   {1}: (7,0,7),   {2}: (7,7,0),
    {0,1}: (6,8,7), {0,2}: (9,7,5), {1,2}: (7,5,8),
    {0,1,2}: (7,6,6).

Adding player 3 to a nonempty active coalition leaves these coordinates
unchanged, and a player-3-only coalition pays them zero. Player 3 receives
−1 when joining an active coalition, 1 when absent and player 1 or 2
quits, and 0 otherwise. These rules specify all fifteen rewards; M=9
bounds them.

The complete ordinary proof in
[CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md](CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md)
constructs an invariant compact convex neighborhood from the displayed
reward inequalities. Its pivot prior and temperature are exactly (1),
while all its nonpivot finite/Never prior ratios are exp(−4^(t+1)).
Our three corresponding ratios are no larger. Its nonpivot invariant-set
estimate bounds each finite output against the Never denominator, so
decreasing these ratios preserves that estimate. The pivot map is
unchanged. Thus the SAME invariant set remains mapped into itself; this
is not an assumption that a good fixed point already exists.

Explicitly, put x=2^(−N), τ=4^(−N), and

    A_N=τ^(−2/3),
    η_N=6N exp(−A_N/4),
    δ_N=η_N(1+72/τ)+2x exp(−1/τ).

The source proof therefore provides, for every N≥6, an actual fixed
point q_N of (2) satisfying

    F(q_N)≤x/(1−x)+36δ_N.                                  (5)

Every selected full-objective minimizer p_N obeys F(p_N)≤F(q_N), so
(4) follows for this table. No reference profile is an input of the
selector. The explicit geometric comparison law occurs in the proof
of existence and its regret bound, derived from the given table.
This changes the selection criterion of the already-proved example; it
does not add table coverage.

One should not import the source proof's calendar-reach bound for q_N
as a bound for an arbitrary selected p_N: closeness to the geometric
reference was not imposed on the latter. Actual early absorption can
instead be obtained after harmless deadline enlargement. For ANY finite
canonical profile p, moving only the pivot's Never mass to the first
omitted date gives gain equal to the joint Never mass J(p). Hence

    J(p)≤F(p).

Given e>0, H≥1, ρ>0 and N₀, choose N with (5) below min(e,ρ), then
view the selected p_N in a deadline D≥max(N+H,N₀). The unchanged law
has full regret below e and reach at D−H equal to J(p_N)<ρ. It is
not asserted to be a logit fixed point for the enlarged menu D. This
padding uses the already-controlled FULL regret, not merely menu Nash.

## 3. The cyclic table and the exact weak-tie check

For the cyclic table let

    r₀(S)=1 if 0∈S, and 2 otherwise.

For i=1,2,3, with predecessor/successor cyclically among those three,
let r_i(S)=0 if i∈S; otherwise let it equal −1 when 0∈S, and
2·1_(pred(i)∈S)−1_(succ(i)∈S) when 0∉S. All Never pays zero.
This is the canonical VANISH table, with reward bound two.

Its exact infinite cyclic profile σ has pivot Never and

    σ_i(3k+i−1)=2^(−k−1),   k≥0, i=1,2,3.

Its payoff is (2,0,1,0). The relevant pure-payoff values are

    f₀(Never;σ₋₀)=2,   f₀(0;σ₋₀)=1,
    f₂(Never;σ₋₂)=1,   f₂(0;σ₋₂)=0,
    σ₁(0)=1/2,         σ₁(1)=0.                            (6)

There is NO sequence of fixed points of (2), at N→∞, converging to σ
in total marginal variation. To verify this exact but limited statement,
suppose such a sequence existed. Bounded-payoff coupling, uniform over
pure tests including Never, makes both gaps in (6) at least 1/2
eventually. The fixed-point odds then give

    p₀(0)≤2^(N−1) exp(−1/(2τ_N)),
    p₂(0)≤exp(−16) exp(−1/(2τ_N)).                          (7)

In particular (p₀(0)+p₂(0))/τ_N tends to zero.

For EVERY opponent law, not just near σ, the exact table gives

    f₁(1;p₋₁)−f₁(0;p₋₁)≥−p₀(0)−p₂(0).                  (8)

Indeed f₁(0)=0. Waiting until date 1 yields a possibly negative payoff
only if pivot 0 or player 2 quits at date zero. Each event contributes
a negative part at most one; a player-3-only stop instead contributes
two. If nobody stops at zero, joining at one pays player 1 zero.
This exhausts the events, including simultaneous atoms.

Using (7)–(8) in player 1's exact odds gives

    p₁(1)/p₁(0)
       ≥exp(−12−[p₀(0)+p₂(0)]/τ_N)→ at least exp(−12)>0.    (9)

That contradicts the two atoms of σ in (6). Different fixed positive
nonpivot time-prior scales do not remove this particular weak-tie issue.

However, (9) is NOT a lower bound on F over C_N. It excludes one known
limiting strategy, not all nonsymmetric equilibria, escaping-calendar
families, or other low-regret fixed points. It is the same type of
strict-mistake/weak-tie odds obstruction already proved for the other
fixtures in FRECHET's whole-law logit and time-prior notes. No additional
general no-go is claimed, and no parameter grid was run.

## 4. Exact stopping point and pivot-repair distinction

The geometric test proves (4); the cyclic test does not decide (4).
The first still-unproved step is an actual low-full-regret fixed-point
branch on the cyclic table, or a lower bound excluding EVERY such branch.
Replacing this by representability of σ would change the target.
The present variant is stopped rather than extending the known odds
obstruction or varying rates to generate another list of necessary
conditions.

The proof of (9) also exposes a limitation of its portability. It uses
the exponential bound on the pivot's date-zero mass from its logit
equation. If the nonpivot laws are selected and the pivot is globally
repaired instead, small full regret alone controls such an atom only
on the regret scale, not on a scale necessarily negligible relative to
τ_N. Equation (8) is still true, but its negative pivot contribution
divided by τ_N need not vanish. Thus this proof does not reject a
three-law prior selector coupled to unrestricted optimal pivot repair.
No new pivot-repair adapter or correctness claim for current uncommitted
formalization files is made here.

The exact full-objective identity used in (3) is already the checked
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The bounded source comparison otherwise uses the two named FRECHET
whole-law/time-prior notes and the existing canonical cyclic separation
proof. No source density, compact minimum, or finite-menu logit existence
claim has been mistaken for a small-late-debt producer.
