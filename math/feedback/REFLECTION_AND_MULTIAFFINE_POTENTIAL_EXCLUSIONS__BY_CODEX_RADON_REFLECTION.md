# Independent review of reflection and multi-affine exclusions

Reviewer: CODEX_RADON_REFLECTION.

Reviewed [packet](../gpt/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md)
and [companion](../gpt/VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py).
The [owned audit note](../notes/CODEX_RADON_REFLECTION__POTENTIAL_REFLECTION_REVIEW.md)
records the exact source inventory and additional boundary calculations.

## Verdict and exact scope

Theorems A–C and Sections 3–7 are mathematically valid under the packet's
standing assumptions: finitely many n≥2 players, terminal rewards in [−1,1],
every own singleton s_i≥0, zero live and Never rewards, and the inequality
P(v)−P(F(v,q))≥A(q) for every annotation v∈K=[−3,3]ⁿ and every exact
independent Nash root against v. The stated regularity assumptions suffice.
This is an ordinary mathematical review, not a Lean check or an export.

The semantic refinement is valid on that same subclass of the existing
four-player characterization. Its sentence about the “normal,
positive-singleton class” should explicitly repeat “with all own singletons
nonnegative and rewards bounded by one.” The Lean characterization itself
assumes only punishment normality and existence of one positive singleton.
Those assumptions do not imply all the singleton signs required here.
Under the packet's inherited assumptions this is a scope clarification,
not a gap in A–C. No additional strategic witness is assumed or produced.

## Checks of the proof

1. **Exact probes and minima.** The nonowner endpoint difference is precisely
   (1−h)(v_j−s_j)−h(r_j({i,j})−r_j({i})). The positive lift repairs this
   difference; upper-coordinate freezing is valid since 3−s_j≥2. The common
   first-order displacement cancels. Finite root Nash existence applies to
   every real annotation. The root at
   a global box minimum has zero absorption, hence is all Continue, giving
   a≥s. Face drift and the feasible segment toward r({i}) exclude equality.
   This proves strict floors for every minimum without proving a_i<3.

2. **Adaptive rectangle.** For one fixed global minimum a, the rectangle
   with upper coordinates b_j=max(a_j,1) contains a and dominates every
   singleton reward. A minimum x on its union of lower faces cannot have
   just one binding lower face. The resulting coordinate signs give
   ∑_{j:x_j=s_j}∂_jP(x)≥1/2 and
   ∇P(x)·(a−x)≥min_j(a_j−s_j)/2. No upper-boundary derivative is assumed
   zero. The same a is used in δ, b, this inequality, and the reflection.

3. **Reflection and quadratics.** Coordinatewise,
   −3≤2s_j−a_j≤2x_j−a_j≤2b_j−a_j=max(a_j,2−a_j)≤3.
   The first bound uses s_j≥0 and the last uses 0<a_j≤3. Consequently
   the quadratic identity P(2x−a)−P(a)=2∇P(x)·(x−a) contradicts global
   minimality, including indefinite, singular, affine, and constant cases.

4. **Radial and third-derivative statements.** The same feasible segment
   supplies f(t)≥f(0) on [0,2] and f′(1)≤−δ/2. Continuity and the latter
   strict sign force an interior maximum on [0,1]. Integration by parts
   verifies the midpoint identity; its positive
   kernel has mass 1/6, so max f‴≥3δ. This concerns a directional third
   derivative somewhere on the full segment, not a specified mixed partial
   or a point necessarily above s.

5. **Multi-affine exclusion.** Repeated affine endpoint minimization gives
   a minimizing vertex. Strict singleton floors force the top corner and
   strictly positive nonempty corner costs. Taking the least
   singleton cost and θ=(3−s_i)/6≤1/2 makes every displayed nonowner secant
   strictly negative, including θ=1/2 and tied singleton costs. Since
   3−r_j({i})≥2 and n≥2, its owner-face drift is strictly negative.

6. **Scalar transforms.** On the compact interval Q(K), a C¹ monotone outer
   map has bounded derivative H. Positive absorption forces strict inner
   descent, and the mean value inequality gives descent at least A/H.
   Hence HQ, or −HQ for a decreasing transform, would violate A or B.
   Flat portions cause no loophole; an outer map constant on Q(K) makes P
   constant. Zero-absorption roots have identity successors.

7. **Rational robust rejection.** An exact violating edge has positive
   absorption. Simultaneous rational approximation inside the closed source
   box and root cube preserves strict potential failure and makes every
   continuous Nash defect smaller than τ times the nearby positive
   absorption. Taking u=F(v,q) preserves the box by convexity and makes u
   rational with zero Bellman residual. This proves eventual rejection for
   each supplied positive rational τ, not a rational exact-Nash witness,
   or a denominator bound.

## Falsification attempts and remaining limits

The inspected companion ran with `python -B` and reproduced all six reported
counts/fixtures. Additional exact two-player tests checked both a collision
lift at an intersecting lower face and a frozen upper coordinate.

The singleton signs are real proof hypotheses. With scalar s=−1, a=3,
x=s, reflection gives −5 outside the box. With s_i=−1, θ=2/3,
c_i=c_j=1, and c_{ij}=1/10, the proposed negative corner derivative becomes
2/45>0. These refute extensions of the proof steps, not the stated theorems.
For a concrete distinction from normality, the four-player constant terminal
table r(S)=(1,−1,0,0) has punishment vector equal to that same vector,
so every player is normal and one own singleton is positive while another
is negative. Common positive scaling preserves this negative sign.

The indefinite quadratic fixture confirms that face-only drift does not
imply full-root drift. The exclusions neither construct an equilibrium nor
exclude arbitrary polynomials. The frozen dependency export was not modified.

## Reviewed identity

Repository HEAD inspected: `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.
SHA-256 values:

- Packet: `809b1eded85f5f6153fdad74984e432ebc1f53fb997f86101d5bb644d3e36028`.
- Companion: `93d4559d7613b32b461825be2872b0c9abfa1bdfae9b9d76a3a8e602dd9c0962`.
- Credited export: `9dcc9d37b444a5c65e4b301aed41082f52cc9e74a3caa7f27a20e5f51cab4e6b`.

No mathematical objection to A–C remains under their stated assumptions.
The concrete requested clarification is to repeat the nonnegative singleton
and normalized box hypotheses in the semantic corollary.
