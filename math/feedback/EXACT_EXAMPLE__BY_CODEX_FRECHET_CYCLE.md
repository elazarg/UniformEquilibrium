# Independent review of the canonical exact-menu example

Reviewer: `CODEX_FRECHET_CYCLE`.

Status: PASS as ordinary mathematics. No unresolved mathematical objection
was found to the finite-menu uniqueness, fixed unrestricted defect,
geometric approximate producer, or noncommuting limits. The omitted
one-date boundary cases are supplied below. No Lean check or export was
performed.

Submission: [`gpt/EXACT_EXAMPLE.md`](../archive/EXACT_EXAMPLE.md), full-file
SHA-256
`f4f258367064525d0e890be3a0b66588eb8881eb553a50bda674cbdd378a8079`.
The entire submission was read before assessing it. No other review or
coordinator verdict was read. The previously read HILBERT canonical notebook
was used only for the requested comparison, not as proof of this table.

## 1. Exact statement and table

The game has four independently randomized stopping clocks in
`ℕ ∪ {Never}`; first simultaneous minimum determines the absorbing coalition,
and all Never pays zero. The fifteen nonempty-coalition rewards are fully
determined by the seven active-coalition rows and the dummy rule. The latter
does not change the active coordinates when it joins an active coalition.
The own-singleton vector is `(1,0,0,0)` as claimed. Against three Never
opponents each player's full cap equals its own singleton, so the claimed
punishment-normal upper bounds hold directly in the actual table.

The claims being checked are: a unique product Nash law on every finite menu
`F_N = {0,…,N−1,Never}` for `N ≥ 1`; the same strictly positive pivot defect
at each such exact law; an explicit product law on each actual menu with
vanishing full terminal exploitability; and the displayed failure to
interchange menu-size and zero-error limits. Behavioral deviations have no
time or memory restriction. The conclusion concerns this table and a
selection obstruction, not a positive gap against every behavioral profile.

## 2. Root calculation and all boundary cases

I independently expanded Quit minus Continue from every active coalition
row. With the dummy continuing, the three polynomials are exactly

```text
Δ₀ = 1 + q₂ − 2q₁ − v₀(1−q₂)(1−q₁),
Δ₁ = q₀ − 2q₂ − v₁(1−q₀)(1−q₂),
Δ₂ = q₁ − 2q₀ − v₂(1−q₁)(1−q₀).
```

The dummy cannot quit surely at a reached date. If an active player quits
with positive probability, its immediate Quit payoff is strictly negative,
whereas its complete Never payoff is nonnegative. If no active player quits
at that date, the pivot can join the sure dummy and gain one. If an active
player quits surely, the dummy's current Continue strictly beats current
Quit, so the dummy must continue at that date. The three sure-active
exclusions in Fact A then use the correct polynomials and are independent
of the unknown suffix because the relevant opponent quits surely.

For completeness, the abbreviated zero-coordinate argument at the last date
is as follows. No active coordinate can equal one by Fact A. If `q₀ = 0`
and `q₁ > 0`, then `Δ₂ = q₁ > 0`, forcing the forbidden `q₂ = 1`.
Hence `q₁ = 0`, but then `Δ₀ = 1 + q₂ > 0`, contradicting `q₀ = 0`.
Thus `q₀ > 0`. If `q₁ = 0`, then `Δ₂ = −2q₀ < 0` forces `q₂ = 0`,
after which `Δ₁ = q₀ > 0` contradicts `q₁ = 0`. Finally, if `q₂ = 0`,
the same `Δ₁ = q₀ > 0` forces the forbidden `q₁ = 1`.
All three active coordinates are therefore interior at the last date.

Their three linear indifference equations have the unique solution
`(2/7,4/7,1/7)`. Direct rational calculation gives both action payoffs
`31/7`, `19/7`, and `34/7` for the active players. The dummy receives
`1−(3/7)(6/7) = 31/49`. All four entries of `V` are correct.

Against continuation `V`, the dummy strictly continues for every active
root: if active absorption can occur its Quit payoff is negative; otherwise
its positive continuation makes Continue strictly preferable. Every singleton
active support and every two-player active support is excluded by the
displayed negative gap of one supported player. For full active support,
the multiaffine inequality is correct: its eight cube-vertex values are
`6,3,3,2,3,2,2,3`, all at least two. Since every `Vᵢ > 2`, it implies
`ΣΔᵢ < 0`, incompatible with nonnegative gaps for all supported players.
At the all-Continue root every active gap is `gᵢ−Vᵢ < 0`, so that root
actually is Nash and is the unique root Nash against `V`.

These checks verify all the coalition entries used in the proof. The argument
does not presume a restricted strategy class for finite-menu equilibrium.

## 3. Why the backward induction covers every exact selector

Fact A implies strictly positive current Continue probability for every
player in every finite-menu Nash law. Conditioning the product law on
current all-Continue conditions each coordinate on its own Continue event,
so the conditional tail remains a product law. A player can retain its
current choice and replace only its conditional tail. The resulting gain is
the conditional-tail gain multiplied by the strictly positive joint current
Continue probability. Thus the conditional tail must be Nash on the shorter
menu, without a subgame-perfect assumption.

This is exactly the semantic step expressed by
`timingLawTail_isNash_of_isNash_of_positiveContinue` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`,
whose hypotheses and proof were inspected. Applying the argument at every
successive reached date validates induction: the last root has the unique
mixed action above, and every preceding root is all-Continue against its
unchanged value `V`. The entire four-coordinate product stopping law is
therefore unique. There is no unobserved suffix freedom from a zero-reach
event that could produce additional product laws.

At this law `U₀ = W₀ = 31/7`. Every finite stopping date outside the menu
adds exactly the opponents' joint Never probability `18/49` to `W₀`.
For nonpivots their zero singleton levels make after-menu Quit equal to
Never. All other finite deviations belong to the menu. Consequently the
full debt vector is exactly `(18/49,0,0,0)`, and arbitrary behavioral
mixtures cannot improve these caps.

The reach formula `R(N−H)=1` is correct with `R(t)` meaning no Quit
strictly before date `t`, for `1 ≤ H ≤ N`. This convention also makes
the later geometric reach formula correct.

## 4. Approximate producer and its limiting equilibrium

For the geometric truncated pivot clock, `x=2^(−N)`, all other players
Never, the prescribed vector is exactly `(1−x,7−7x,7−7x,0)`.
Against the independent pivot clock, pure-date payoffs are:

- Pivot: one at every finite date and zero at Never, giving debt `x`.
- Player one: `7−3·2^(−t)` for `t<N`, increasing to `7−6x` at `N−1`;
  Never and all `t≥N` pay `7−7x`, so its full debt is `x`.
- Player two: `7−(9/2)·2^(−t)` for `t<N`, increasing to `7−9x`, strictly
  below its Never/after-menu value `7−7x`; debt zero.
- Dummy: a collision with the pivot pays minus one and every other outcome
  available to it pays zero; its cap and prescribed payoff are zero.

Thus both the actual-menu and unrestricted exploitability equal `2^(−N)`.
Every full behavioral replacement is a mixture over the pure dates and
Never just checked. There is no finite-support restriction in this argument.
The reach at `N−H` is `2^(−(N−H))`, so the stated menu-size choice meets
all the approximation and early-absorption quantifiers. If the intended
version of the error requirement is strict `< e`, choose `2^(−N) < e`
rather than `≤ e`; arbitrarily large such deadlines are available.

I also directly checked the limiting profile, which makes the statement
that the laws converge to an equilibrium precise. Let the pivot use the
uncensored geometric law and let all others Never. Its value is
`(1,7,7,0)`. The same pure-date calculations with no final boundary give
player-one values strictly below seven and supremum seven, player-two values
below seven, pivot cap one, and dummy cap zero. This is an exact terminal
Nash profile. The truncated laws converge to it in marginal total variation
at rate `2^(−N)`.

It also has the claimed uniform-payoff interpretation. Along each active
player's unilateral deviation all terminal rewards are nonnegative, so
every finite-average payoff is at most that deviation's terminal payoff.
For the dummy every available stage payoff is nonpositive. The prescribed
geometric profile has finite expected absorption delay, so its finite-average
payoff converges to `(1,7,7,0)` with an `O(1/n)` error. These observations
give the uniform unilateral horizon caps directly for this fixed profile.

As independent arithmetic checks, explicit finite-product evaluation at
`N=1,2,4,8` reproduced both prescribed payoff vectors and both complete
debt vectors, including the extra pure date `N`. The proof for all `N`
is the symbolic argument above, not the finite test.

## 5. Noncommuting limits

On a fixed menu the four marginal simplexes form a compact space. The
finite-menu exploitability is continuous. Full exploitability is also
continuous here: it is the maximum of finitely many pure-deviation payoff
differences, since every omitted date has the same payoff as date `N`.
Thus each nonempty constraint set `E_N ≤ e` is compact and the displayed
minimum exists.

For any sequence `e_k ↓ 0`, minimizers have convergent subsequences, and
each limit satisfies `E_N = 0`. Uniqueness then identifies it with the
exact finite Nash law. Continuity gives
`lim[e↓0] Φ_N(e) = Φ_N(0) = 18/49`. Conversely for every fixed `e>0`,
arbitrarily large geometric truncations are feasible and have full regret
tending to zero. Exploitability is nonnegative, so `inf_N Φ_N(e)=0`.
Both sides of (14) follow with the stated constants and quantifier order.

The Never-coordinate separation in (15) is also correct for every `N≥1`.
Hence this is a barrier to exact finite-menu re-equilibration at any chosen
deadline, not merely to one unfortunate selection among multiple equilibria.
It does not exclude direct work in approximate equilibrium sets.

## 6. Bounded comparison and conjecture-facing significance

The finite-menu route and semantic cap definitions were selected through
`docs/TOOLKIT.md` and inspected in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean` and
the conditional-tail source cited above.

The already present production comparison is
`existsUnique_finiteDeadlineTimingNash`,
`finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`, and
`quarter_lt_finiteDeadlineTimingNash_exploitability` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`.
Their table and exact singleton declarations in
`FinFourHardDeadlineTimingNashBarrier.lean` have own singleton vector
`(1/2,−1,−1,−1)`. Thus a selection-independent positive-defect exact-menu
barrier was already proved in Lean for a different, noncanonical table.
The present exact constant, table, and simple geometric approximation are
not those checked declarations.

The conference note
[`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`](../notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md)
already gives the canonical singleton vector, unique defective exact-menu
laws, and successful approximate laws on another table. It additionally
handles its all-Never boundary-credit homotopy. The present submission is
therefore an independently useful second explicit realization and a precise
noncommuting-limit formulation, not the first canonical example within the
conference record. I do not infer an unreviewed notebook's theorem status
from its presence, and the proof of this submission did not depend on it.

This table is outside the nonhomogeneous matrix residual in a particularly
transparent way. Its singleton comparison matrix is

```text
Γ = [0 6 6 −1;
     7 0 7  0;
     7 7 0  0;
     0 1 1  0].
```

The pure weight `e₀` is a homogeneous simplex witness because
`Γe₀=(0,7,7,0)≥0` and its coordinate-zero residual vanishes. Its recursive
normal core is all four players: rows zero, one, and two can retain player
three as witness, and row three can retain player zero. Thus it satisfies
the homogeneous input in `HomogeneousMatrixBranch` in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`, whose existing
consumer is `exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch` in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProducer.lean`.
I inspected these definitions and the consumer. The example's UE existence
is therefore in an already covered matrix class. The valuable conclusion is
the exact-selection obstruction and explicit approximate bypass; it does
not remove a new nonhomogeneous hard-source case.

## Disposition

No false mathematical claim was found. The complete uniqueness proof,
unrestricted debts, explicit approximate selector, and limit separation
pass this audit. The only presentational repairs suggested are writing out
the short last-date boundary argument and specifying the pre-date convention
for `R`. Use a strict geometric bound if a strictly smaller error is desired.

No other review was consulted, no Lean build was run, and no source,
author note, or export was edited. The concrete next research question is
whether a specified approximate selector, such as a branch of logit fixed
points, can select low full regret on a canonical exact-menu stress table;
this submission establishes that exact re-equilibration cannot do so here.
