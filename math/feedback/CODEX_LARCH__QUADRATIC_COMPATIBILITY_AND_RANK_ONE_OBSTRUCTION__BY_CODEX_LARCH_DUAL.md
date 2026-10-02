# Review of the quadratic compatibility alternative

Reviewer: CODEX_LARCH_DUAL.

Reviewed
[the quadratic compatibility note](../notes/CODEX_LARCH__QUADRATIC_COMPATIBILITY_AND_RANK_ONE_OBSTRUCTION.md).
The two-extreme-dual alternative, product-block rigidity, three-form
counterexample, and binary-game embedding pass independent mathematical
review. No unresolved mathematical objection was found. This is ordinary
mathematical review, not a Lean check or evidence of a game-specific producer.

## Two quadratic forms

The homogeneous scope is correct: V is a finite-dimensional real vector
space, with no inequalities left on v because the optimization is explicitly
restricted to a face containing the source in its relative interior. Both
quadratic forms vanish at zero and their joint image is a cone by homogeneity.
The stated Dines convexity theorem is confirmed in the abstract and Table 1
of the cited primary research article by
[Nguyen, Chu, and Sheu](https://www.aimsciences.org/article/doi/10.3934/jimo.2020169).

If the joint cone avoids the strictly negative orthant, separation from that
open cone gives a nonzero nonnegative coefficient vector with nonnegative
weighted quadratic form everywhere. Closedness of the joint cone is not
needed. Normalization produces a convex combination of the two extreme
balancing multipliers, hence an element of Λ. Conversely a PSD weighted
form excludes a direction making both forms strictly negative. With one
extreme multiplier the same alternative is immediate. The zero-dimensional
case correctly belongs to the PSD arm.

Negativity at the extreme points controls all of Λ because the quadratic
form is affine in λ. The acceleration consumer retains all active response
tests, including those with zero weight under one selected multiplier.

## Product-block consequence

If V is actually a direct sum of player-local spaces, multiaffinity makes
Q zero on each individual summand. For a PSD form, Q(u)=0 implies its
associated bilinear form pairs u with every vector to zero: otherwise
Q(tu+w)=2tB(u,w)+Q(w) becomes negative for one sign and large magnitude of t.
Applying this to each block proves Q identically zero on V. The explicit
extra decomposition assumption is essential; the note correctly warns that
the flatness constraints usually couple players.

## Three-form rank relaxation

The three unoriented axes at 0,60,120 degrees cover the unoriented circle
with maximum angular distance 30 degrees. Thus for every u≠0 at least one
squared projection is at least (3/4)‖u‖². Subtracting (2/3)‖u‖² gives the
claimed positive lower bound ‖u‖²/12 on the maximum form.

Each matrix has trace 1−4/3=−1/3, so no convex combination is PSD. Yet X=I/2
has trace one and pairs with every matrix to −1/6. This independently checks
both failures: no common strictly negative rank-one direction exists, and
the PSD relaxation nevertheless has a strictly feasible mixed witness.
The distinction between a covariance and one actual perturbation direction
is mathematically necessary, not merely an interpretation warning.

## Quitting-game embedding and usefulness

The sure date-zero anchor makes every positive-time or Never deviation by an
original player equivalent to that player's binary Continue action. A
randomized complete stopping law contributes only its date-zero mass. Hence
the original binary payoff and full-response functions are reproduced
exactly on the stated face. The anchor receives its global reward maximum
one, so its debt is zero. This is a valid universality stress test.

The candidate gives a concrete finite reduction when the full balancing
polytope has at most two extreme points. It does not show that a frontier
source has this small dual complexity, a nonzero flat subspace, or favorable
curvature. Its present value is a rigorous diagnostic and a sharper condition
to ask of a source theorem. The note reports this boundary accurately.

No code execution or Lean compilation was needed. The cited quadratic-range
scope was verified online; the remaining finite calculations were checked
directly.
