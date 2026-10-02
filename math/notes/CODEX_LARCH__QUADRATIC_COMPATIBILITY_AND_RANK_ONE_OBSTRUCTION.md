# Quadratic compatibility, hidden convexity, and the rank-one obstruction

Author: CODEX_LARCH. Internal outside-field theory sketch, 2026-09-07.

## Status and motivation

The outside import is homogeneous quadratic optimization: a small case of
hidden convexity turns response-by-response curvature into one actual common
perturbation. The result below is conditional ordinary mathematics, not Lean
and not a UE producer. A three-form counterexample delineates where a tempting
semidefinite relaxation becomes strategically invalid. The main claims passed
[independent mathematical review](../feedback/CODEX_LARCH__QUADRATIC_COMPATIBILITY_AND_RANK_ONE_OBSTRUCTION__BY_CODEX_LARCH_DUAL.md),
including the exact counterexample and the homogeneous scope of the external
quadratic-range theorem.

This specializes the independently reviewed
[common acceleration sketch](CODEX_LARCH_JOINT__MULTILATERAL_REPAIR_THEORY.md).
Its point is to simplify that sketch's nonlinear search over directions in
one recognizable case, not to duplicate its acceleration LP.

## 1. Exact finite question

Fix one actual independent finite-calendar profile p, including Never. Keep
every pure unilateral response test, including the first date after the
calendar and Never. Write g_a for its polynomial response gains and
E=max_a g_a. Suppose E(p)=m>0 and let I be all tied maximal tests.

Restrict profile perturbations to a specified product face F containing p in
its relative interior. Let T be its tangent space. Define

    L_a(v)=Dg_a(p)[v],       Q_a(v)=½D²g_a(p)[v,v],
    V={v∈T : L_a(v)=0 for every a∈I},
    Λ={λ∈Δ(I) : Σ_a λ_a L_a vanishes on T}.

Assume Λ is nonempty. A first-order minimum supplies such balancing weights,
but it need not supply any nonzero V. The zero-dimensional case is allowed
and gives no improvement.

For v∈V the acceleration test says that some w∈T makes
p+εv+ε²w decrease every maximal gain at order ε² exactly when

    Q_λ(v):=Σ_a λ_a Q_a(v)<0 for every λ∈Λ.          (1)

The same v must work for the whole polytope. Face restriction matters: with
outside-face openings the acceleration set is a cone, not T, and this
particular reduction must be reconsidered.

## 2. A two-extreme-dual alternative

**Candidate lemma.** If Λ has at most two extreme points, exactly one of the
following holds:

1. There is v∈V satisfying (1), and hence a common acceleration w producing
   one literal product-law improvement.
2. There is one λ∈Λ such that Q_λ is positive semidefinite on all of V.

For one extreme point this is the definition of positive semidefiniteness.
For two, write their forms as Q_1,Q_2. Dines's homogeneous joint-range theorem
says that {(Q_1(v),Q_2(v)):v∈V} is a convex cone. If it avoids the open
negative orthant, separation gives nonnegative weights α,1−α, not both zero
before normalization, for which αQ_1+(1−α)Q_2≥0 everywhere. Conversely that
combination precludes simultaneous strict negativity. Closedness of the
joint-range cone is unnecessary because the other cone is open.

The classical input, including its homogeneous finite-dimensional scope, is
stated in Nguyen, Chu, and Sheu,
[On the convexity for the range set of two quadratic functions](https://www.aimsciences.org/article/doi/10.3934/jimo.2020169),
introduction and Table 1. No inhomogeneous extension or constrained-domain
version is invoked here. The source's original theorem concerns extensions;
its statement of Dines's theorem supplies the established background.

This is not a two-player theorem or even a two-debtor theorem. One player can
have many tied response deadlines, and the relevant count is extreme points
of the balancing-weight polytope after all response constraints are retained.
Counting only convenient multipliers would invalidate the conclusion.

### A further product-structure consequence

Suppose, additionally, V decomposes as independent player blocks ⊕_i V_i.
Multiaffinity makes each Q_λ zero on every single-player block. If Q_λ is
positive semidefinite on V, it is therefore identically zero on V: a PSD
bilinear form cannot have a nonzero mixed pairing against a vector with zero
quadratic value. Thus, in this special case, alternative 2 is exact weighted
cancellation of every mixed interaction, not merely nonnegative curvature.

This could turn failure of repair into a rigid table identity. The extra
block-product hypothesis is substantial: imposing all L_a(v)=0 usually
couples different players' direction blocks and can create effective
same-variable quadratic terms on V. Do not infer it from multiaffinity alone.

## 3. Why three forms permit a false mixed certificate

For u=(x,y), take three unit vectors e_j at unoriented angles 0,60,120 degrees
and define

    Q_j(u)=(e_j·u)² − (2/3)||u||².                  (2)

Every unoriented direction lies within 30 degrees of one e_j. Therefore

    max_j Q_j(u) ≥ (3/4−2/3)||u||² = ||u||²/12.

There is no nonzero direction making all three forms negative.

But the covariance X=(1/2)I is positive semidefinite, has trace one, and
satisfies tr((e_j e_jᵀ−(2/3)I)X)=−1/6 for every j. Equivalently, an isotropic
random direction makes every quadratic negative in expectation. Also every
convex combination of the three matrices has trace −1/3, so none is PSD.
Thus both the naive extension of the two-form alternative and rank-relaxed
semidefinite feasibility fail on this exact two-dimensional example.

This is a coefficient-level falsifier, not a claimed quitting-table
realization. Its purpose is to prevent importing a relaxation theorem with
the wrong quantifiers. A covariance is a mixture of perturbation directions;
it is not one direction. Averaging their game profiles can also correlate
players, and averaging their marginal laws changes the mixed terms. Neither
operation supplies (1).

The analogy with mixed versus pure states in quantum mathematics is exact
at the matrix level: the admissible rank-one object u uᵀ is smaller than the
PSD trace-one set. No quantum theorem or physical implementation is claimed.

## 4. A universality check before proposing a game-specific shortcut

Any n-player binary-action normal-form game embeds on a face of an
(n+1)-player quitting game. Add a player who quits surely at zero, give that
anchor constant terminal payoff one, and identify each original player's
binary action with Quit0 or Never. For every coalition containing the anchor,
assign exactly the original game's payoff at that binary action profile.
Set rewards at other coalitions arbitrarily for original players and keep
the anchor's reward one.

Against the fixed anchor every later response is equivalent to Never, so
all original players' full behavioral caps are exactly their binary-game
best-response caps. The anchor has no profitable deviation. The face's
entire payoff and exploitability functions reproduce the binary game.

This simple embedding is a methodological stress test, not a novelty claim.
A proposed local theorem based solely on quitting multilinearity must survive
arbitrary binary-game incentives on this face. Useful additional structure
must come from a special response pattern, actual global-minimum provenance,
or an operation leaving the face. The quadratic alternative above deliberately
exposes its additional dual-complexity hypothesis.

## 5. Bounded next test and rejection criterion

For one existing actual response-preserving family, compute T, V, and all
extreme balancing multipliers. If Λ has at most two extremes, test the PSD
alternative exactly. A nonzero common direction now has a finite linear
acceleration consumer; an obstruction is one explicit quadratic form valid
on the whole flat subspace. If V also splits by player, inspect the forced
mixed-coefficient cancellations for a source-retaining erasure or reset.

If there are many extremes, the useful next question is structural:
simultaneous diagonalization or another verified joint-range convexity
condition might retain exactness. Solving only the PSD relaxation is
insufficient. If no actual frontier source reduces this dual complexity,
demote the idea to a diagnostic and do not build a general library around it.

Source audit: the complete-response and multiaffinity setup is inherited from
the reviewed joint note and its named Lean files. Narrow searches for Dines,
S-lemma, S-procedure, and semidefinite curvature found no matching theory in
the sampled optimization, notes, formalized, or exports lanes. This is a
bounded overlap check, not an exhaustive novelty claim. No Lean was changed
or compiled. The linked review found no unresolved mathematical objection;
the source hypothesis reducing dual complexity remains unproved.
