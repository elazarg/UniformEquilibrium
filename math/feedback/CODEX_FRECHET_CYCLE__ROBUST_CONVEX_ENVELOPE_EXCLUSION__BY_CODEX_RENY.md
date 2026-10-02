# Bounded corollary review: robust convex-envelope exclusion

Reviewer: CODEX_RENY.

Original reviewed in full:
[robust convex-envelope exclusion](../notes/CODEX_FRECHET_CYCLE__ROBUST_CONVEX_ENVELOPE_EXCLUSION.md),
SHA-256

    eba5827fd2fa9de6fd1498c615a4e70d76c132bed7c5cb5d77e393ba5b3ba8ce

Verdict: **PASS.** No correction is required. This is a bounded companion
check using the separately reviewed C¹-convex theorem, not another full
gate or an extension to arbitrary nonconvex potentials. Author bytes and
exports were left unchanged; no Lean build was run.

## 1. Exact corollary checked

For any nonempty finite player set, arbitrary rewards |r_i(S)|≤M,
M≥0, padded full box K=[−B,B]^I with B>M, and δ>0, there is no bounded
convex f:K→ℝ satisfying

    f(v)−f(w)≥a(q)

for EVERY product root q and v,w∈K with ordinary root regrets at most
δa(q) and Bellman error ||w−F(q,v)||∞≤δa(q). No differentiability,
punishment normality, realizability, or selected-start restriction is
assumed. The exact-edge nonsmooth case δ=0 is explicitly not claimed.

The lower convex envelope of every continuous H on K is bounded and
convex. Thus, for every positive tolerance and every positive drift
coefficient, that envelope has a positive-charge violating triple.
This conclusion does not assume existence of an original polynomial
certificate on any table.

## 2. Positive translation: ordinary regret and both endpoints

For an exact Nash root at v, let c=∏(1−q_i), a=1−c and
α_i=∏_(j≠i)(1−q_j). A coordinatewise nonnegative translation h gives

    F(q,v+h)=F(q,v)+ch,
    Q_i−F_i(q,v+h)=(Q_i−F_i(q,v))−ch_i,
    C_i(q,v+h)−F_i(q,v+h)
      =(C_i(q,v)−F_i(q,v))+q_iα_i h_i.

The two parenthesized gains are nonpositive by EXACT root Nash. Since
q_iα_i is the probability of the singleton event {i}, it is at most
the entire absorption probability a. Thus each new gain is at most
a||h||∞. This is ordinary mixed-root regret, not an unsupported
endpoint-support estimate or a full behavioral cap estimate.

If w=F(q,v), then

    (w+h)−F(q,v+h)=ah.

Therefore both the new root regret and Bellman residual are bounded by
a||h||∞, at the same literal root. No division by a occurs. At a=0,
the root is all-Continue, w=v, and both translated errors remain zero.

One-sidedness is essential. For one player with singleton reward zero,
v=0 and any 0<t<1, the root q=t is exact Nash. A negative translation
h=−η makes the Quit gain η(1−t), while absorption is t. This is not
bounded by ηt as t↓0. The author uses only positive h and avoids this
counterexample.

The chosen inner radius and smoothing window satisfy

    B'=(B+M)/2>M,   d=B−B'>0,
    η=min(δ/2,d/4)>0,
    O=(-B'−d/4,B'+d/4)^I.

For every x∈O and every sampled h∈(0,η)^I, all coordinates of x+h
lie strictly between −B and B. In particular both v+h AND w+h are
in K when v,w∈K'. Root successors of points in K' stay in K' because
the reward vectors are in its interior and F is a convex combination.
The proof does not check only the source endpoint or silently assume
the translated successor equals F(q,v+h).

## 3. Convolution for merely bounded convex functions

A finite convex function restricted to the relative interior of each
box face is continuous there. The box has finitely many faces, each
relative interior being Borel. Consequently f is Borel on K, including
possible boundary discontinuities. Boundedness then makes its zero
extension a compactly supported integrable Borel function.

The convolution

    V(x)=∫ρ(h) f̃(x+h)dh

is smooth on all of ℝ^I: after changing variables, derivatives fall on
the smooth compactly supported kernel. No derivative or continuity of f
at the original boundary is required.

Convexity of V is claimed only on O, where EVERY sampled point belongs
to the original convex domain. For fixed h, convexity applies to x+h,
y+h and their segment; integrating with nonnegative weights proves
convexity on O. Zero extension need not be convex, and the proof never
uses such a statement.

For each exact edge of K', all shifted triples are admissible in the
old robust relation. Integrating their inequalities gives

    V(v)−V(F(q,v))≥a(q).

Thus V is C¹ on a neighborhood of K', convex on K', and satisfies the
forbidden exact drift there. The existing C¹ theorem applies because
B'>M. This is an honest restriction to a smaller STILL reward-padded
box, not smoothing on a boundary without room.

## 4. Envelope and quantifier check

The finite-mixture formula for the lower convex envelope gives

    min_K H≤co H(v)≤H(v)≤max_K H.

Concatenating approximate minimizing decompositions proves convexity,
so the preceding bounded-convex theorem applies without requiring a
smooth envelope. Applying it to (co H)/γ gives a violating triple for
every γ>0 and every δ'>0. Such a violation must have a>0: at a=0,
the admissible relation forces w=v and hence zero difference.

The author's final contact-decomposition explanation is correctly
conditional on SAME-root and common-residual compatibility. For an
attaining contact decomposition, these assumptions imply
Σθ_k y^k=F(q,v)+z=w and yield the claimed averaged inequality. For
continuous H on compact K, finite attaining contact decompositions are
available from compactness of the convex hull of its graph; one can
also phrase the calculation with approximate decompositions and an
arbitrarily small error. The proof does not infer this compatibility
from convexity of a fixed-root admissible fiber.

## 5. Source and stopping boundary

The positive common-translation identities and bounded Borel smoothing
are already in Sections 4.1 and 4.3 of
[the polynomial packet](../exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md).
They agree with `quittingRootCoordinateNashDefect` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean` and the root endpoint
definitions in `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
The separate C¹ theorem and its source/domain audit are covered by
[the independent C¹ review](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY__BY_CODEX_RENY.md).

The corollary's addition is convexity-preserving smoothing on a smaller
padded box, closing the nonsmooth escape for a robust convex-envelope
operation. It does not claim new convolution theory or reproduce a
producer from arbitrary reward data.

The tested convexification operation is now excluded at every positive
tolerance and positive uniform drift rate. Arbitrary nonconvex polynomial
certificates and the actual positive selection problem remain untouched.
No further convex-subclass or constant refinement is needed for this
conclusion.
