# Independent review of the convex smooth-potential exclusion

Reviewer: CODEX_BROUWER.

Scope: Section 7 of
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`](../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md),
as read on 2026-10-05. This review does not certify the earlier cap-saturation
argument or any subsequent nonconvex extension.

Verdict: **PASS as ordinary mathematics**, with no unresolved mathematical
objection to the convex theorem or its one-polytope source corollary. No
Lean build or implementation was performed. Its arbitrary-game adapter is
still missing; this is not a proof of Simon's orbit conclusion or of the
quitting conjecture.

## Exact claim checked

Let C be a nonempty compact convex subset of R^n, n>=1, with nonempty
ambient interior. Let f,g:C->R^n be continuous and equal the identity on
boundary C. Assume only

    f(z)=g(z) implies f(z) belongs to boundary C.

The parameter z itself need not be on the boundary. Let H be C^1 on an
open set Omega containing C, f(C), and g(C). Assume

    f(z)!=g(z) implies H(g(z))<H(f(z)),

and, at every boundary x, some y in C satisfies

    gradient H(x) dot (y-x)<0.

Then these data do not exist. The images f(C),g(C) need not lie in C;
H need not be convex, quasiconvex, polynomial, or bounded outside the
compact sets used in the proof. The boundary choices y need not vary
continuously.

## Adversarial proof audit

The projection step has the correct sign. For

    W(x)=P_C(x-gradient H(x))-x,

the metric-projection variational inequality, tested against x in C,
gives gradient H(x) dot W(x)<=-||W(x)||^2. Moreover W(x)=0 implies
gradient H(x) dot (y-x)>=0 for every y in C. Thus the stated boundary
descent excludes W=0 there. The boundary is nonempty and compact because
n>=1, C is compact, and its ambient interior is nonempty. Continuity
therefore gives a uniform strict negative bound on that boundary.

The extension from the boundary to nearby points does not misuse projection
outside C. The projection inequality is invoked only at boundary points;
continuity of gradient H(y) dot W(y) supplies the strict neighborhood
estimate. Projection is globally continuous on R^n, so W is continuous
on Omega even when y lies outside C.

The cutoff construction is valid with C^1, not C^2, regularity. Choose U
around the compact boundary with compact closure inside Omega and inside
the strict negative region. A continuous cutoff equal to one near the
boundary can have compact support K contained in U. Its support has
positive clearance from the complement of U. If L bounds ||W|| on K,
choose the common step small enough that every moved segment remains in
that clearance neighborhood and the change of gradient along it is at
most beta/(4L). Here L>0 follows from the strict negative dot product on
the nonempty support. Uniform continuity on the resulting compact
neighborhood gives exactly the claimed uniform directional inequality.
The case chi=0 is harmless: the segment is stationary and the map is the
identity. Thus T is continuous on all of Omega, maps Omega into itself,
never increases H, and strictly decreases H wherever chi>0. No evaluation
of H outside Omega or differentiability of the cutoff is used.

The potentially dangerous diagonal case is handled correctly. When
f(z)!=g(z), the original strict inequality combined with H(T(g(z)))<=H(g(z))
excludes T(g(z))=f(z). When f(z)=g(z), the diagonal-IMAGE premise locates
the common image on boundary C, where chi=1 and T strictly lowers H.
This also excludes equality for an interior parameter z. The proof does
not replace the source premise with interior-parameter nonvanishing.

Consequently Z(z)=T(g(z))-f(z) is a continuous nowhere-zero field on C.
Brouwer applies to z |-> P_C(z+Z(z)). At a fixed point the projection
inequality is Z(z) dot (y-z)<=0 for all y in C. An interior fixed point
is impossible by choosing y=z+t Z(z). At a boundary fixed point the
identity boundary data give Z(z)=e W(z), and the feasible point
y=P_C(z-gradient H(z))=z+W(z) makes the left side e||W(z)||^2>0.
The contradiction is exact. No source-projection degree, differentiable
f or g, continuous boundary-direction selector, or repeatable orbit is
being smuggled in.

Two elementary removal tests confirm that important assumptions are not
vacuous. On C=[0,1], H(x)=x, f(z)=z and
g(z)=z-z(1-z)/2 satisfy the strict off-diagonal drop and exact diagonal
condition, but fail inward descent at 0. Conversely f=g=id and
H(x)=(x-1/2)^2 satisfy inward descent at both boundary points but violate
the diagonal-image condition. These are not counterexamples to the
stated theorem.

## Exact Simon source correspondence

I read `QuestionOneHypotheses`, `IsFullDimensionalCompactConvexPolytope`,
`IsStraightLineOn`, `homotopyTerminalImage`, `graphFiber`, and
`QuestionOneHypotheses.exists_escapeScale` in
`MathUE/Topology/SimonViabilityQuestion.lean`.

At pieceCount=1 the domain really equals its unique compact convex,
full-dimensional piece. Terminal evaluation of the continuous homotopy
gives continuous f,g. The boundary clause gives f=g=id there. The actual
diagonal clause is precisely an assertion about the image point, not
the domain parameter, as used in this proof.

For a boundary x, the neighborhood condition puts x in the local
neighborhood. The relevant boundary-piece intersection contains x and
has distance zero from x, so the guarded local escape clause applies.
It supplies a target y with distance(y,C)<=0, distance(x,y)>=scale>0,
and segment[x,y] in the fiber over x. Closedness of nonempty C gives
y in C. Inclusion of the local graph into J gives every segment pair
(x,x+t(y-x)) in J. Therefore a uniform graph inequality

    H(x)-H(y)>=c||x-y||, c>0,

implies, by dividing the segment inequalities by t>0 and differentiating
at zero, gradient H(x) dot (y-x)<=-c||y-x||<0. Terminal graph inclusion
gives the strict off-diagonal drop. This proves the advertised corollary
for EVERY C^1 graph potential, including polynomials of arbitrary degree.

The explicit n>=1 assumption matches `QuestionOneAffirmative`'s nonempty
coordinate type. If one instead instantiates the bare hypotheses in
dimension zero, their own terminal diagonal condition is already
impossible: the ambient one-point domain has empty boundary and its
terminal pair is necessarily diagonal. This degenerate case is not an
exception to the exclusion.

## Quitting adapter and novelty limits

I inspected `IsQuittingFloorFreeRobustEdge` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`,
`abs_quittingRobustChargedEdge_target_sub_source_le` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelationTranslation.lean`,
and `ChargedRelation.IsPotential` in the imported
`Maths/Graph/ChargedRelation.lean`. The absorption-relative displacement
bound already exists with the exact coefficient M+B+delta. Its Euclidean
corollary has the stated sqrt(n) factor. The potential convention is
H(target)+absorption<=H(source), so the claimed conversion to positive
metric drift has the correct orientation. Zero absorption forces zero
displacement, and the explicit positive-denominator qualification avoids
division by zero.

The named polynomial producer in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
is specifically a Fin4 theorem with a reward bound, all-player normality,
and a positive own singleton. Its potential is on the full robust relation
at one positive rational tolerance and radius rewardBound+2. Any eventual
game application must retain these source hypotheses and the SAME relation,
tolerance, and box. The current section does not claim to have supplied
those geometric data, so this is a scope reminder, not a mathematical
objection to the current conditional discussion.

I also checked `QuittingSimonFEdgeAt` and
`HasQuittingSimonFiniteCellLyapunovCertificate` in
`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`,
and `TruncatedW`, `TruncatedPiece`, `truncatedW_eq_iUnion`, and `lemma4_5`
in `Literature/Simon2012.lean`. The first graph uses support-local absolute
error; it is not automatically the full absorption-relative robust graph.
The finite-cell certificate is supplied data. The displayed Section 4
construction has several explicit hypotheses and a union of pieces, not
the convex domain required here. No literature declaration was promoted
to an unconditional production theorem in this review.

Narrow comparison with existing source exclusions found no existing version
of this convex coincidence lemma. In particular
`IsQuittingFullExactRootPotential.not_quasiconvex` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialQuasiconvexExclusion.lean`
excludes a shape-restricted class on actual root geometry; the present
generic theorem excludes all C^1 potentials but assumes different,
unproduced convex homotopy/escape geometry. Neither theorem subsumes the
other's complete hypothesis-conclusion package.

This is a meaningful missing generic mathematical lemma and an exact
one-polytope corollary, proved by standard projection and Brouwer methods.
It is not an unrestricted polynomial exclusion for arbitrary quitting
tables, not an affirmative solution of Simon's extended-orbit question,
and not a new equilibrium producer until the concrete adapter is built.
Those limitations are honestly stated in the reviewed section. I make
no external-literature priority claim and recommend no export promotion
as part of this review.
