# Independent review of the convex smooth-potential exclusion

Reviewer: CODEX_BROUWER.

Additional scope: the independent Section 10 assessment and its exact
implementation-overlap witness appear at the end of this file. The original
Section 7 verdict below retains its original scope.

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

## Independent review of Section 10: the two-player premium core

**PASS as ordinary mathematics** for the full-root smooth-potential
exclusion and its original four-player uniform-equilibrium consequence.
There is no unresolved mathematical objection. This assessment is separate
from the Section 7 review above. I checked the Section 10 argument before
reading KREIN's independent review; subsequently I checked his new exact
overlap witness, as specified below. No Lean build or implementation was
performed, and no arbitrary-game or arbitrary-finite-player UE theorem is
asserted here.

The exact raw class has nonnegative participant premiums, constant
participant rewards for all but two designated players i,j, and
`r_i({i,j}) < r_i({j})`. The analytic result permits signed singletons and
any finite player set containing distinct i,j. The UE consequence requires
four players and nonnegative singletons. Passive rewards and all premiums
of the two designated players on larger coalitions remain unrestricted
subject to the stated nonnegative-premium condition and finite reward
bound. The conclusion concerns unrestricted behavioral deviations and one
fixed uniform payoff target, not only root or stationary deviations.

### The full-root and minimizer arguments

Every exact root successor dominates the Quit endpoint coordinatewise and
hence is above the singleton vector. Convexity of the reward box puts it in
the SAME set C. If any constant-participant outsider has positive hazard,
supported Quit pins its successor coordinate exactly at its singleton.
This argument retains every other hazard and all triple/grand-coalition
rewards. Only when every outsider hazard is zero does the displayed
two-core endpoint formula apply. With both core hazards positive, its
strict pair-leave term and the core source floor contradict supported Quit.
With only one active core, its successor coordinate is its singleton.
Consequently every positive root from the stated core-floor region really
returns to the original lower boundary L.

The singleton-face derivative inequality is also valid at multiple-face
and upper-box intersections. At a face with strict other floors, sufficiently
small sole-owner hazards are exact Nash because the actual nonowner
endpoint differences are strictly negative at rate zero. Their pair-join
payoffs are finite and vary continuously with the rate. Lifting the other
coordinates toward B and using gradient continuity gives the weak-face
inequality. No uniform permissible rate across the lifting parameter is
needed.

At a minimum on L, one binding coordinate gives a positive sole-owner
return and an immediate contradiction. With at least two binding
coordinates, increasing one remains feasible, giving nonnegative binding
gradient coordinates. Nonbinding interior gradients vanish and upper-box
gradients are nonpositive. If just the two core coordinates bind, apply
the face inequality with owner j: its i term is nonpositive because
`r_i({j}) > r_i({i,j}) >= s_i`, its owner term vanishes, and every other
term is nonpositive. The claimed lower bound one is impossible. Hence a
constant-participant outsider must bind.

Lowering exactly the binding outsiders preserves both core floors and
stays in the original ambient box for sufficiently small positive epsilon.
All-Continue ceases to be Nash, but every finite-game Nash root still
returns to the SAME L. This uses no continuity or special selection of
roots. A lowered coordinate must move upward by at least epsilon, whereas
the absorption-relative motion bound is `(M+B)*a`. Thus

    epsilon/(M+B) <= H(v_epsilon)-H(x).

The right side divided by epsilon tends to the negative sum of the binding
outsider gradient coordinates, which is nonpositive. Since B>M>=0, the
left coefficient is strictly positive. This closes the contradiction,
including arbitrarily small absorption, arbitrary root supports, upper-box
coordinates, and signed singleton values. In particular, the proof never
perturbs both core coordinates below their floors, never changes the
minimization boundary, and never claims that a root is repeatable as an
equilibrium strategy.

### Exact source composition and its scope

I inspected the following declarations in their source files:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`;
- `quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `isQuittingFloorFreeRobustEdge_of_exactRoot` and
  `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.

Nonnegative singletons make the all-Never response ceiling equal to the
singleton, and nonnegative premiums give the opposite unrestricted
punishment inequality. Normality is therefore supplied from the raw table.
If some singleton is positive, the no-UE hypothesis supplies an actual
rational polynomial on the full robust relation in box M+2. Exact root
edges have zero error and are in that same relation; no box, function,
game, or edge charge changes on restriction. The polynomial is smooth,
contradicting the analytic theorem. If every singleton is zero, all-Never
already yields an exact uniform equilibrium. The no-sure-root conjunct is
not an additional table assumption needed to use the forward implication.

This is a genuine raw-table existence mechanism, not a verifier awaiting
a strategy, child, selected root branch, or geometric adapter. The
finite-player analytic statement alone does not extend the specifically
four-player no-UE polynomial producer.

### Independently checked overlap witness from KREIN

I checked the complete table in the section “A new exact
implementation-overlap witness” of
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_KREIN.md`](CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_KREIN.md).
It is the cyclic singleton table with R=4, constant participant payoffs
away from the two changes `r_0({0,3})=2`, `r_3({0,3})=1`. Its designated
core is {0,3}; the strict pair-leave comparison is 2<4. Both active
premiums at hazards q_0=q_3=1/2 equal 1/2. Thus product-low fails on an
actual product root, not just by comparing individual coalition rewards.

The centered singleton matrix is exactly

    M = [[ 0,-1,-1, 3],
         [-1, 0,-1, 2],
         [-1, 2, 0,-1],
         [-1,-1, 2, 0]].

Here is a direct check of the R0 and degree assertions. If the pivot
coordinate in a homogeneous LCP solution were positive, the child-row
inequalities force all three child coordinates positive. Their equalities
then give each child coordinate equal to the pivot coordinate; the pivot
residual is positive, a contradiction. If the pivot is zero and any child
is positive, the cyclic inequalities force all children positive, but their
invertible child matrix has no nonzero kernel. Thus M is R0. At offset
`(1,-1,-1,-1)`, a zero child coordinate is impossible by the next child's
strictly negative constant term. The child equations give all children
`1+x_0`; the pivot residual is `2+x_0`, so x_0=0. The unique solution is
`(0,1,1,1)`, with strict inactive residual 2 and child determinant 7.
The exact root-sum degree is therefore +1. I checked the applicable
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`. This does not trigger the
nonunit-degree or non-Q route.

The child {1,2,3} inverse is entrywise positive, but its omitted pivot
row times that inverse is `(9/7,-3/7,1/7)`. The other three principal
triple inverses each have negative entries, and the full inverse has
entry `(0,1)=-9/7`. These agree with the raw inverse/passive-row tests in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The {0,1} principal matrix has both off-diagonal entries -1; it is R0 but
not Q, excluding the stated principal-Q alternative. No homogeneous or
inverse test is being inferred merely from a numerical eigenvalue.

I also checked all 15 set partitions using the necessary condition
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
Only the discrete partition and `{0}|{1,2,3}` survive that exact integer
test. For the latter, at the block-constant hazard `(x,0,0,0)`, the actual
zero-discount displacement is `F_1=F_2=x`, `F_3=x+x*x`, using
`quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
It therefore fails for every x>0. This excludes all nondiscrete response
quotients, not just quotients obtained from a proposed symmetry.

The proper-child falsifiers are exhaustive and use zero-regret actual
child laws with zero joint-Never mass. For the triple {1,2,3}, the three
phase values `(0,1,0)`, `(0,0,1)`, `(1,0,0)` satisfy the half-hazard solo
Bellman identities and both endpoint inequalities. Opponent survival
contracts even after one child deviates. The quiet pivot's value is 4/7,
and immediate Quit pays at least 1, a positive debt. For the delicate
child {0,2,3}, I independently obtained the following endpoint values
at first-date hazards `(2/3,1,1/4)`:

| Player | Continue | Quit |
| --- | ---: | ---: |
| 0 | 1 | 1 |
| 2 | -3/4 | 0 |
| 3 | 0 | 0 |
| omitted 1 | -5/6 | 0 |

All realized coalitions under the prescribed child profile contain 2,
so neither changed pair coordinate enters its delivered payoff. The
three other categories in KREIN's review give immediate exact child
Nash laws: a favorable singleton for one/two nonpivot children, all
sure Quit for children containing 0 but not 3, and sure owner 3 for
children containing {0,3} but not 2. The omitted negative child gets a
strict joining gain. These categories and the two displayed triples
cover every proper nonempty child. The exact source bound
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`
would give zero outside debt on each witness for any of its five kinds
and any weights. Thus all those universal proper-child gates fail.
This is not an assertion that no specially selected child equilibrium
can ever be extended by some other argument.

As an additional check, this table has no pure absorbing coalition
equilibrium. With 0 absent, a single child has a negatively paid missing
child who joins, two children have a participant who gains by leaving,
and all three children give every participant a positive leaving payoff.
With 0 present but 3 absent, player 3 strictly gains by joining. Coalition
{0,3} makes player 0 gain by leaving, and every larger coalition containing
0 and 3 makes player 0 gain from 1 to 4 by leaving. All-Never is also
not Nash because s_0=1. Thus the witness does not conceal a pure exit.

These are exact rational calculations, not floating-point evidence. They
support a strict increase over the named product-low, universal
proper-child, homogeneous, degree, inverse, and response-quotient gates.
The original spectator fixture alone would not have supported that claim.
I do not infer that every existing conditional strategy architecture has
been excluded, nor make a global external-literature priority assertion.

### Final assembly-delta check

I also checked the assembled strict-leave packet supplied by the author,
hash `cef3a65a343a0978038a80103384c4dbbe8ff56db829d6e4cba3d78840ca01ca`.
The proof and scope are preserved; all fifteen displayed reward rows
equal the independently checked fixture above. The explicit partition
comparisons, periodic pivot values 4/7, 8/7, 16/7, and complete-deviation
qualifications for the one-date child witnesses are correct. No assembly
repair is needed. This is a mathematical delta check, not a Lean check.

The final packet is
[`TWO_PLAYER_PREMIUM_CORE_STRICT_LEAVE.md`](../exports/TWO_PLAYER_PREMIUM_CORE_STRICT_LEAVE.md),
SHA256 `a77ed8034289e563c0ee34493bfd4de936d2ac9a526495c9a93e3654866c2d9d`.
Only the draft preface was removed from the checked assembly. The
mathematical PASS applies to this final packet; no Lean check is asserted.
