# Independent review of the universal-drift finite crossing word

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed source:
[finite-word candidate](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_DRIFT_FINITE_WORD_FORCES_MACROSCOPIC_FLOOR_CROSSING.md),
SHA256 `42d8287474c7789bb9309bcf1c55ecc2145fd01d002fa93b5cc5678368a69089`.

Verdict: PASS as ordinary mathematics; no mathematical repair requested.
This is one bounded independent correctness/utility review, not an export
gate, Lean validation, UE proof, or claim of a new raw-table class. The
proof was reconstructed from the candidate and exact source definitions,
not from a coordinator reconstruction or another review of this candidate.

## 1. Exact claim checked

For a four-player table bounded by M>0, a box radius B>M, and own
singletons s, put K=[−B,B]^4, C=∏[s_i,B], and let L be C's lower
singleton boundary. The supplied C² function H satisfies decrease by
at least a(q) on EVERY boxed source/root/target triple whose Bellman
residual and four ordinary root Nash defects are at most δa(q).

Choose the SAME minimizer x of H on L. Its boundary-gradient pressure
allows v0=x−ε1_J, for every sufficiently small positive ε, with
H(v0)<h=min_L H. The claim is that EVERY sequence of exact root Nash
choices, iterating v_next=F(q,v), enters C in finitely many steps.
The first crossing has all successor slacks >δa, absorption
a>2/[κ(M+B)^2], positive collision mass >δa²/(8M), and at most one
sure quitter. Here κ is a supplied finite lower-Hessian bound, not a
uniform constant over all possible polynomials.

The root word uses arbitrary annotations. It does not claim those
annotations are actual payoff or cap vectors, nor that the word is
terminal Nash after an arbitrary actual tail.

## 2. Exact robust-edge and potential correspondence

I inspected `IsQuittingFloorFreeRobustEdge`,
`quittingRobustChargedEdgeResidual`,
`quittingRobustChargedEdgeRegret`, and
`quittingFloorFreeRobustChargedRelation` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`.
The target changes only the residual condition; root regret is evaluated
against the SOURCE annotation. Both source and target lie in the box.
The note's simultaneous four-coordinate formulation matches these
definitions exactly.

`quittingRootCoordinateNashDefect` in
`UniformEquilibrium/Quitting/Root/NashDefect.lean` is exactly
max(Q_i,C_i)−F_i. `IsPotential` in `MathUE/ChargedPathBudget.lean`
is target potential plus absorption charge at most source potential.
There is no transpose, sign, or hidden factor-of-four mismatch.

`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies a root
at EVERY annotation, with no selection or support hypothesis.

The stated polynomial equivalence in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
was read under its imports. Its no-UE application has normality and
positive-singleton hypotheses and uses radius rewardBound+2. The root
theorem being reviewed instead takes H directly and needs neither
normality nor a sure-root exclusion. No extra semantic consumer is
silently obtained by dropping the hypotheses of the equivalence.

## 3. Independent proof audit and attempted failure modes

### Starting point and all-choice termination

The imported boundary lemma gives |J|≥2, nonnegative pinned gradient
coordinates ρ, and a strictly positive sum of those coordinates. I
rechecked its exact solo-root eligibility and one-sided upper-face
gradient treatment in the linked drift checkpoint. In particular,
one cannot simply assume an eligible solo root at a multiply pinned
face; that lemma first proves the inequality at strictly unpinned
nonowners and takes a gradient-continuity limit. Its conclusion
does justify H(x−ε1_J)<H(x) and keeps the point inside K for small ε.

For any start outside C below h, a=0 would force q=0, which is exact
Nash only at v≥s. Thus every pre-entry root has positive absorption.
The Bellman update remains in K and obeys

    ||F(q,v)−v||∞≤(M+B)a.

If a choice sequence never enters C, telescoping bounds the sum of its
absorptions. The displayed displacement estimate therefore gives an
actual Cauchy sequence of annotations, not just a convergent subsequence.
Moreover q_i≤a forces all root probabilities to zero. Closed endpoint
Nash inequalities at the limit say max(s_i,v∞_i)=v∞_i, so v∞∈C.
Since every preceding point was outside C, continuity of the minimum
singleton slack puts the limit on L. Finally H(v∞)≤H(v0)<h is a
contradiction. All choices were arbitrary. No equilibrium-component
continuation or positive lower bound on each intermediate root was used.

The conclusion is finite termination for each such choice sequence.
The note does not assert a uniform root count as ε tends to zero.

### Robust pinning at the first entry

At the crossing, w∈C. If w_i−s_i≤δa, replacing just that coordinate
by s_i leaves a target in L∩K and within the permitted residual ball.
The exact source Nash defects are unchanged. Potential decrease to this
modified target contradicts H(v)<h. This includes equality at δa and
proves a STRICT bound for EVERY coordinate of the same successor.
No root is falsely re-equilibrated against the modified target.

### Curvature sign and positive absorption

The lower Hessian bound D²H[d,d]≥−κ||d||∞² gives the upper chord
estimate used in the note. Its direction is correct: subtract the
endpoint interpolation from the one-dimensional restriction, or add
the appropriate positive quadratic to make that restriction convex.

The last chord from v outside C to w strictly inside C crosses L at
some 0<θ<1. Taking the maximum of the crossing times of initially
deficient coordinates produces a point with ALL lower bounds satisfied;
an arbitrary first coordinate crossing would not suffice. The padded
upper bounds remain satisfied along the chord.

At this point H≥h>H(v), while H(w)≤H(v)−a. Hence

    0<−θa+(κ/2)θ(1−θ)(M+B)^2 a².

Division is legitimate because θ,a>0. It forces κ>0 and the claimed
strict absorption bound. Since a≤1 it also forces κ(M+B)^2>2.
The κ=0 case is a contradiction, not a division-by-zero exception.

### Collision and sure-quitter boundaries

Select i with q_i≥a/4. This is positive, so exact mixed-root optimality
gives Q_i=F_i even if i is a sure quitter. The empty-opponent event
contributes exactly s_i; every other contribution to Q_i−s_i is at
most 2M. Strict floor slack therefore forces opponent participation
probability >δa/(2M). Independence makes the event that i quits AND
an opponent quits have probability q_i times that probability. It is
a subset of the collision event, proving the claimed lower bound.

With at least two sure quitters, every unilateral endpoint ignores the
annotation, because another sure quitter remains. The same root at its
absorbed payoff R is then an exact positive-charge self-loop. This
contradicts the universal potential. The argument does NOT apply to
one sure quitter. I checked that boundary against
`SureRootNonrepeatability.not_exactNash_terminalValue` in
`UniformEquilibrium/Quitting/Examples/SureRootNonrepeatability.lean`;
the candidate correctly does not make that invalid upgrade.

## 4. Exact checks and a nonclaim falsifier

Exact rational enumeration checked q_i∈{0,1/4,1/2,3/4,1}: all 624
positive-absorption profiles satisfy the selected-owner q_i≥a/4 and
collision-subset inequality. A separate 27-case rational check of
H(t)=−t²/2 gives equality in the semiconvex chord formula. The initial
console summary accidentally labelled those 27 cases as 81; the count
was rerun with an explicit counter and corrected before this review.
These checks supplement the proofs, not the existence of a universal H.

An exact strict crossing can exist as finite Nash data. Set each own
singleton to zero; set r_i(S)=1/2 if i∈S and |S|≥2, and r_i(S)=1
if i∉S. At annotation v=(−7/2,...,−7/2), q=(1/2,...,1/2) has both
endpoints 7/16 in every coordinate, successor strictly above s=0,
absorption 15/16, and collision probability 11/16. It lies in the
box with M=1,B=5. Direct outcome enumeration checked all four endpoint
pairs. This table has all-Never exact equilibrium, and is NOT asserted
to admit H. It only falsifies the tempting extra implication that a
strict crossing root, by itself, is inconsistent or a completed UE
argument. The candidate avoids that implication.

## 5. Practical novelty and remaining consumer

I read the full relevant construction and declaration
`exists_exactRoot_strictSingletonInterior_of_not_weakPeeling`, and
`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary`, in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`.
They assume nonnegative own-quitting premiums. Failure of weak peeling
produces an interior-successor exact root by small common-support
hazards and coordinatewise continuation selection. They do not start
at this H-boundary minimizer, put the predecessor below C and below h,
or constrain EVERY exact-root continuation from that point. Under
nonnegative premiums every exact root already has F_i≥s_i, so the
reviewed word enters C on its FIRST step in that special class; this
does not make its general signed-table word redundant.

The distinct content in the inspected corpus is therefore the
same-source, all-choice finite entry and the certificate-dependent
macroscopic crossing. The curvature and collision bounds prevent
dismissing the entire word as arbitrarily small singleton directions.
Generic finite root existence and production of some interior root
do not give this attachment.

Qualitative raw-table conclusions should still be calibrated narrowly.
An interior root already implies failure of weak support peeling:
every active owner's Quit expectation exceeds its singleton, so on
that active support each owner has a positive own-premium coalition.
The note does not establish a new UE class through that observation.
Its cited constant-own-quit and discounted all-anchor comparisons were
checked; neither contains this all-choice finite crossing statement,
but their already covered raw classes are not broadened here.

Finally v_next=F(q,v) adjoins a root BEFORE the continuation represented
by v. Thus the order of the displayed annotation iteration is the
reverse of the chronological order if the finite roots are compiled
around a tail. An actual tail would have to be attached at v0, with
its payoff AND cap discrepancy priced. The successor being inside C
does not supply that tail, permit repetition of a one-sure crossing,
or restore an actual source minimum. The note's explicit nonclaims
keep this boundary intact.

Useful next target: exclude, redirect, or legally compose this produced
crossing using additional same-table data. Another supplied-crossing
verifier would not consume the new necessary structure. No export
recommendation or broader search was part of this bounded review.
