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
[`TWO_PLAYER_PREMIUM_CORE_STRICT_LEAVE.md`](../formalized/TWO_PLAYER_PREMIUM_CORE_STRICT_LEAVE.md),
SHA256 `a77ed8034289e563c0ee34493bfd4de936d2ac9a526495c9a93e3654866c2d9d`.
Only the draft preface was removed from the checked assembly. The
mathematical PASS applies to this final packet; no Lean check is asserted.

## Independent review of Sections 11–12: all two-variable-participant games

**PASS as ordinary mathematics**, with no unresolved mathematical
objection to the mutual-strict-joining analytic theorem, weak-leave UE
closure, or their combined four-player raw-class conclusion. This is a
new scoped review; it does not change the frozen strict-leave export.
No Lean build was run. The claim remains restricted to nonnegative
singletons, nonnegative participant premiums, and at most two players
whose participant rewards can vary. The analytic strict-joining theorem
itself allows signed singletons and arbitrary finite player count.

### Literal full-root map and boundary fixed-point index

The polynomial gap g_k is independent of its OWN hazard, but includes
every actual opponent coalition. Extending the coalition formulas to
all real hazards is legitimate for constructing the continuous ambient
map; strategic interpretations are used only at fixed points, which
necessarily lie in the unit cube. For

    F_v(q)_k=clip_[0,1](q_k+g_k(q)),

the fixed-point conditions are exactly g_k<=0 at zero, g_k=0 in the
interior, and g_k>=0 at one. These are the complete product-root Nash
conditions, not only necessary stationarity conditions. No hazard
normalization or projection changes the source reward table.

The unique-fixed-point index fact is correct. On the boundary of
(-1,2)^n the homotopy field between q-F(q) and the translated identity
cannot vanish, because its proposed fixed-point value stays in [0,1]^n.
It therefore has total degree +1. At a nonsingular sole root, the stated
derivative remainder estimate isolates the root and provides a
nonvanishing straight homotopy to its invertible derivative. Excision
then identifies its local determinant sign with +1. A fixed point on
the SMALL unit-cube boundary is an interior point of this ambient
domain, so there is no half-index issue.

I inspected `ambientDegree_homotopy` and
`ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in
`MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
Their requirements are compatible with the continuous ambient clipped
map, the bounded open isolating domains, and the explicit affine
comparison. If using the last declaration directly, a rectangle strictly
larger than the closure of (-1,2)^n supplies its chart-clearance premise.
The proof's own homotopy normalization already suffices, so this is a
formalization detail, not an additional mathematical assumption.

At the sole possible mixed core root p, both core coordinates are
strictly interior. If every inactive outsider has strictly negative gap,
its clipped row is locally constant ZERO even in an ambient neighborhood
containing negative outsider coordinates. The core rows are locally
unclipped. Thus the stated block derivative of identity minus F is exact:
its upper-left determinant is -alpha_i*alpha_j<0 and the outsider block
is the identity. The starred columns retain all full-table cross-effects
and cannot change that determinant. Consequently this particular mixed
root cannot be the only root. The argument does not need every root to
be regular or a finite root set: under the contrary hypothesis the full
classification leaves just this one nonsingular candidate.

### Exhaustive core-only classification and tie removal

The pure-pair alternative is correctly resolved first. If all outsiders
weakly prefer the pair to joining for their singleton, the pair is an
exact root at its own reward vector, with positive absorption and zero
motion. This immediately contradicts a positive-drift potential. Otherwise
one fixed harmed outsider rules out the pure core pair at EVERY source.

With an annotation below either core singleton, that core gap is a convex
combination of two strictly positive numbers. It forces its own hazard
to one; the other positive joining gap then forces the other hazard to
one, contradicting the fixed harmed outsider. Every root therefore has
an active outsider in this case.

With both core annotations strictly above their singletons, any sole
active core would strictly prefer Continue. A core hazard equal to one
forces both equal to one, again impossible. The only remaining
core-supported possibilities are all-Continue and the displayed unique
interior pair. If some annotation lies below its singleton, all-Continue
is not Nash. If any outsider's gap at the pair is positive, the pair
is not Nash either and finite Nash existence already supplies an
outside-active root. If all outsider gaps are negative, the negative
index supplies another root, which by this exhaustive classification
must be outside-active. No exact-equality core-annotation case is silently
omitted: the later perturbation deliberately creates either a strictly
below core coordinate or two strictly above core coordinates.

The O(epsilon^2) tie removal preserves exactly the quantities it must.
When no core coordinate binds at the boundary minimizer, they are kept
unchanged and strictly above their singletons; the candidate pair and
its positive all-Continue probability are therefore fixed. Its outsider
gap depends affinely on that outsider's own annotation with nonzero
coefficient -c(p), independently of all other outsider annotations.
Avoiding one scalar value in each nonempty interval (0,epsilon^2)
removes all ties. Downward perturbations stay in the same box for small
epsilon, and every binding outsider stays at least epsilon below its
singleton. No continuous selection in epsilon is needed: the aggregate
extra displacement is O(epsilon^2) in fixed finite dimension and hence
is negligible in the first-order potential quotient.

### Same-boundary potential contradiction and semantic composition

The singleton-binding minimizer case closes using a small sole-owner
root with its owner coordinate pinned at the singleton. With at least
two binding coordinates, the feasible gradient signs are valid for the
union of lower faces. In the core-binding case, lowering all binding
coordinates invokes the below-core classification. In the other case,
the tie-removed source invokes the index producer. Both produce an
ACTUAL exact root with an active constant-participant outsider, not a
root in a deleted child game. Its successor lies in the SAME original
L used for minimization.

Every chosen successor dominates s, so any lowered binding coordinate
moves upward by at least epsilon. The absorption motion bound is still
(M+B)*a. Minimality and unit potential drift therefore force the first
directional quotient to be at least 1/(M+B)>0, while differentiability
makes its limit the negative sum of nonnegative binding gradients.
This contradiction is complete for all selected roots and does not
require a uniform positive absorption bound.

Section 11's weak-leave closure also checks. Only a NONPARTICIPANT
singleton reward coordinate is increased. Own singletons, participant
premiums, and outsider participant equalities do not change. I inspected
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
It permits nearby targets and profiles to vary and returns one fixed
target for the original table. The elementary compact-target proof in
the note has the correct delta payoff error and 2*delta deviation error.
No weak-leave analytic exclusion is inferred from strategic closure.

Together the branches exhaust the two designated players' pair
comparisons. The previously checked punishment identification, positive
singleton split, full Fin4 no-UE polynomial producer, and SAME-potential
exact-root restriction apply without new assumptions. The all-zero
singleton case is handled by all-Never. Thus the combined conclusion is
an original-game uniform payoff against all behavioral deviations, not
a stationary-root or selected-policy theorem.

### Exact adversarial checks and boundary of the mechanism

I independently recomputed the three-player fixture's endpoint vectors
and successors using exact rational arithmetic. At (1/3,1/3,0), the
gaps are exactly (0,0,-53/45), the successor is (4/3,1/3,53/45), and
the clipped ambient determinant is -9. At (0,0,1), the gaps are
(-2,-3,1/10) and the successor is (3,3,0). Thus the test genuinely
requires selection of a different root; replacing the claim by universal
boundary return would be false even in its stated class.

The argument's two-core restriction is substantive. My separate ongoing
size-three-core calculation produces an actual unique interior-support
root of local index +1, with successor strictly above all singleton
floors. This does not refute Section 12, whose nonconstant-participant
set has size at most two. It does rule out treating the determinant sign
as a general Nash-root parity principle. Section 12 uses the actual
two-core block and does not make that invalid extension.

The earlier independently verified strict-leave fixture already supplies
bounded separation from the named implementation gates for a subclass
of this combined theorem. This review certifies the new index producer
and its full raw-class composition; it does not claim an exhaustive
classification of every other possible conditional repository consumer.

## Independent review of Sections 14–15: a protected common trap leaver

**Verdict: PASS as ordinary mathematics, not Lean-checked.** I checked the
strongest signed-premium statement in Section 15 together with its Section
14 prerequisites and complete rational fixture. The checked notebook has
SHA256 `addb73fce7440cb03e41ac8a0afb06d78d6563e35fcc2960019542b84eec891e`.
I did not read another agent's review of these sections before checking.
The repaired principal-02 matrix claim is included in this verdict.
No export, Lean source, build, or Git mutation was performed.

### Exact claim and the substantive change in the invariant set

For a finite nonempty player set, let s_i=r_i({i}). A positive-premium
trap is a nonempty support A in which each member has a strictly positive
participant premium on some coalition contained in A. Let C be the union
of all traps. The hypotheses are a designated p such that:

- every participant payoff of p is at least s_p;
- every trap contains p; and
- r_p(T union {p})<r_p(T) for every nonempty T contained in C minus {p}.

Other players' participant premiums can have either sign. These raw
hypotheses exclude a C1 unit-absorption-drift potential on every full
exact root in any box [-B,B]^I with B strictly above a reward bound M.
For four players with nonnegative own singletons, the existing polynomial
obstruction gives an original-game uniform-equilibrium payoff. Weak
leave comparisons give that strategic conclusion by reward closure, not
by a claimed weak-comparison analytic exclusion.

The move from Section 14 to Section 15 is essential, not cosmetic.
An absorbing exact root can now return below an unprotected singleton.
The proof therefore minimizes on

    D={v in [-B,B]^I : v_p>=s_p and some v_i<=s_i},

not just on the singleton lower boundary L. The signed proof consistently
uses this original D in both minimization comparisons. It never assumes
that the perturbed root's successor belongs to L.

### Full-root return, including sure hazards and all outsider coalitions

The active support A is nonempty at an absorbing root. If A is a trap,
then p belongs to A and A is contained in C. Conditional on p's action,
every nonempty opponent coalition T has a strictly negative Quit-minus-
Continue difference. The empty-coalition difference is s_p-v_p<=0.
A singleton cannot be a trap, so some opponent has positive hazard;
the strict event has positive probability even if one or several hazards
equal one. Thus p cannot have positive quitting probability at an exact
Nash root. This contradiction rules out the trap case without deleting
any positive-hazard outsider or imposing interior-root assumptions.

If A is not a trap, negating the defining finite quantifiers gives an
active k with r_k(S)<=s_k for EVERY participant coalition S contained
in A. Hence Q_k<=s_k and the supported-action equality gives w_k<=s_k.
Separately, the protected player's raw premium bound gives Q_p>=s_p,
and exact Nash gives w_p>=Q_p whether p is active or inactive. These
two coordinates, together with the convex-combination box bound, put
w in D. The witness k may depend on the root and may equal p; neither
possibility causes a gap. In the globally nonnegative-premium special
case the same argument sharpens to w>=s with some equality, proving
Section 14's return to the SAME L.

### Minimization, singleton probes, and the signed absorption charge

D is nonempty and compact: s lies in it and B>M bounds all singletons
strictly inside the ambient box. If a minimizer x has x_k<s_k, the
all-Continue profile is not exact Nash. Finite normal-form Nash existence
then gives an absorbing root, whose successor remains in D and strictly
decreases the potential. This contradicts minimality. Thus a minimizer
lies on L and also minimizes over L.

The singleton-face inequality is valid for signed tables. I inspected
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.
Its premises are the reward/box bounds, the full-root potential, a point
above singleton floors with one equality, and differentiability. There
is no participant-premium premise. Its actual collision-adjusted probe
also covers upper-box corners. The note's C1 argument by approaching
multiple bindings from strict other-coordinate floors is independently
valid: singleton levels are strictly below B, so the required perturbations
remain in the box.

At a minimizer with only one binding j, all other non-upper derivatives
vanish, and upper-face derivatives are nonpositive. Since
B-r_i({j})>0 and the j component of x-r({j}) is zero, the directional
value is nonpositive, contradicting the singleton-face lower bound 1.
Therefore at least two coordinates bind. Increasing any one binding
coordinate while keeping another binding shows its derivative is
nonnegative. A binding k different from p can be lowered by epsilon
without changing the protected floor.

The new charge estimate is correct and independent of the sign of
k's premiums. With a the total absorption probability and a_minus_k
the opponent absorption probability,

    Q_k >= s_k-2M*a_minus_k >= s_k-2M*a,
    Q_k <= w_k <= s_k-epsilon+(M+B)*a.

The first inequality conditions on whether anyone else quits; on the
empty event the forced-Quit reward is exactly s_k. The second line
uses exact Nash and the literal one-step convex average. Thus
epsilon<=(3M+B)*a. The coefficient is strictly positive. Minimality
over D and unit drift force the potential difference quotient to be
at least 1/(3M+B), while differentiability makes its limit the negative
of a nonnegative binding derivative. No root continuity, lower bound on
all absorption rates, index assertion, or selection hypothesis is hidden
in this contradiction.

### Original-game consumer and weak closure

I re-read the exact declarations and relevant imports of:

- `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `isQuittingFullExactRootPotential_of_robustPotential` and
  `IsQuittingFullExactRootPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.

Nonnegative singletons suffice for normality even with signed premiums.
The no-UE direction of the polynomial theorem requires normality, a
reward bound, and a positive singleton; it does NOT require singleton
and punishment values to coincide. Its actual polynomial is restricted
unchanged to every exact root in the same bounded relation. This supplies
precisely the potential just excluded. If all singletons vanish,
all-Never has zero payoff and no complete unilateral stopping law can
improve it. Thus the four-player semantic split is exhaustive.

For weak leave comparisons, increasing only passive coordinates r_p(T)
by delta changes no participant reward, own singleton, positive-premium
witness, trap, or C. The perturbed tables satisfy the strict theorem and
are uniformly delta-close. The reward-closure declaration permits nearby
targets to vary and returns one fixed target for the original table.
The resulting claim therefore has the required accuracy/target order
and unrestricted behavioral deviations, rather than root-only safety.

### Independent exact fixture and coverage checks

I reconstructed all fifteen raw vectors and performed exact rational
checks, separately for the Section 14 table and its Section 15 change
r_2({0,2})=-1/10. In both cases the complete trap list is {0,3} and
{0,1,3}; the greatest trap has size three, every trap contains 0, and
the three strict leave comparisons hold. Both also have a product root
supported on {0,3} with strictly positive premiums for every active
player. Thus the fixture does not satisfy product-low or the greatest-
core-at-most-two criterion. The signed version additionally violates
global nonnegative participant premiums.

The centered singleton matrix and all displayed inverse calculations
check exactly. Its child 123 has determinant 7 and positive inverse.
If a child coordinate vanishes at offset -t*1 with t>0, the next row
is nonpositive, an immediate contradiction; at t=0 the same chain
forces all coordinates to vanish. Positive t therefore gives the unique
child solution t*1. This proves the full R0 claim and the unique degree
test root (0,1,1,1), with inactive residual 8/5 and active determinant 7.
The resulting singleton degree is +1, not a degree exclusion.

The repaired principal 02 matrix [[0,-1],[-1,0]] is indeed R0 and
not Q: nonnegative homogeneous residuals force both variables zero,
whereas offset (-1,-1) is infeasible. Principal 01 is NOT R0 because
(0,1) has residual (1/10,0). The note now distinguishes these correctly.
The only nonnegative-inverse triple is 123; its passive row is exactly
(26/35,-1/70,-9/70), and the stated negative inverse entries of the
other triples and the full matrix are correct.

An independent enumeration of all fifteen set partitions leaves only
the discrete partition and 0|123 at first order. The latter is genuinely
broken at second order: the three residuals are t+t^2/2,t,t+t^2, or
t+t^2/2,t-t^2/10,t+t^2 in the signed table. This is an actual-response
failure, not merely a singleton-matrix heuristic.

The listed pure-coalition improvers have strictly positive gains, in
the table's order:

    3/2,1,1,1,1/10,1,1/2,2,2,2,1,3/2,3/2,1,3/2.

I also checked the twelve stated pure proper-child profiles and their
omitted-player joins directly. The remaining 123 cycle has lifted value
(69/70,0,1,0); pivot 0's first-date Quit gives 1. The 023 profile has
Continue/Quit endpoint pairs (1,1),(-4/5,0),(0,0), changing only the
middle Quit endpoint to -1/25 in the signed version. Its omitted player
1 has endpoints (-11/15,0). Child 02's sure participant-2 payoff changes
to -1/10 but still exceeds withdrawal payoff -1. Sure opponents remove
later choices in those profiles; for the one possible surviving deviator
in 023, the later solo payoff is zero. Thus these child comparisons
control complete behavior, not merely initial deviations. The cyclic
child uses the usual exact nonnegative phase-value Snell comparison.

The checked existing two-player source
`exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreExactRootBoundary.lean`
requires globally flat participants outside a pair and global nonnegative
premiums. Those assumptions do not admit the three-core fixture; the
strengthened one-protected-floor premise genuinely motivates, but does
not already prove, this raw trap criterion. The previously checked
one-joint-phase producer also does not admit the fixture through either
premium pair: the pivot's participant pair reward is strictly below the
corresponding passive singleton reward. These are bounded named-source
exclusions, not an assertion that every possible existing conditional
consumer has been classified.

No unresolved mathematical objection remains in this scope. Section 15
is the coherent stronger theorem: retain Section 14 as its nonnegative
special case rather than claiming two independent existence advances.
The old unique-root three-core falsifier violates the common-leaver
comparison and is not being disposed of by a new local-index claim.

## Final artifact check: common leaver with signed premiums

**Artifact PASS.** My Sections 14–15 mathematical PASS applies to the
complete 455-line standalone packet whose canonical destination is
[`COMMON_LEAVER_WITH_SIGNED_PREMIUMS.md`](../exports/COMMON_LEAVER_WITH_SIGNED_PREMIUMS.md),
SHA256 `2aac4a3fe2f1f3662b1f1dcea7abf2162273131e5e1c2a68f782ba8cfe1ff029`.
I read the complete final artifact and recomputed its hash. This is a
narrow assembly/delta check, not a third independent theorem review or
a Lean check. No packet or export was edited.

The opening statement retains the strongest signed hypotheses: only
the protected player's participant premiums are nonnegative, all own
singletons are nonnegative only for the four-player semantic theorem,
and the leave comparison is weak only in the final strategic conclusion.
The finite-player analytic theorem is separately strict and allows
signed singleton rewards. The active-support/trap split, return to D,
minimum localization to L, singleton-face differentiation at box corners,
different-binding perturbation, and epsilon<=(3M+B)*a charge are all
preserved without a missing step. The phrase “stronger floor estimate”
correctly warns that the unavailable inequality w_k>=s_k is not used.

The reward-closure proof is now self-contained: a common compact payoff
box yields a convergent sequence of targets; fixing one nearby table and
one nearby target before choosing its uniform profile supplies the
correct fixed-target quantifiers in the limit game. Its per-horizon
reward perturbation bound is uniform over all behavioral deviations.
The concise Lean-handoff paragraph states the actual existing source
chain without claiming a new checked declaration or importing any
conference dependency.

I checked the new three-player D-not-L example independently. Its only
trap is 02, player0 satisfies the protected floor and strict comparison
2<3, and at q=(1,1,0) the endpoint gaps are exactly (1,1,-1).
The successor (1,-1,1) lies in D but not L. Thus this new example
correctly demonstrates why the changed invariant domain is necessary.
The assembled fifteen-row signed fixture is exactly the one covered by
the full review above. Its repaired principal02 R0/non-Q argument,
fourteen response-partition exclusions, and complete quiet-child
behavioral checks have not changed their scope.

Named root-existence, singleton-face, support-peeling, inverse, response,
and quiet-debt declarations resolve at the stated files. In particular,
`hasWeakQuittingPremiumSupportPeeling_iff` genuinely has <=, not an
equality, in its raw support witness. The artifact contains no notebook,
feedback, or other math-directory dependency and no embedded review
history. No unresolved assembly objection remains for these bytes.

## Independent review: signed support-specific leavers with protected floors

**Mathematical PASS.** I independently checked Section 17, “Signed
support-specific leavers with a protected set of floors,” through EOF of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, frozen whole-note SHA256
`44cc703d932682ee292bda2b5d3c5b516b7ff14de3453d242e0af5c2b85ab811`.
I did not consult KREIN's review. This checks the full finite-player strict
analytic theorem, the four-player nonnegative-singleton UE consequence,
the separate weak-comparison closure, and the signed proper-core fixture.
It is ordinary mathematics and source inspection, not a Lean check.

### Raw hypotheses and the actual return domain

Let P be nonempty, require nonnegative participant premiums only on P,
and require each positive-premium trap A to have a designated strict
leaver in A intersect P. All other participant premiums may be signed.
The theorem retains the simultaneous product law and every outsider.

At any exact root, the protected forced-Quit endpoints satisfy Q_p>=s_p.
Nash therefore puts the successor in R_P even when the source is not in
R_P. The box part follows independently from the literal convex average.
For sources in R_P, the designated leaver eliminates each trap-supported
root: its empty-opponent term is nonpositive and its positive nonempty
mass has strictly negative terms. A trap cannot be a singleton, so that
nonempty opponent mass really is positive. If the support is not a trap,
negating the finite trap quantifiers gives an active k whose EVERY
participant reward within the support is <=s_k. Support optimality then
gives w_k=Q_k<=s_k, including when k has negative premiums.

Thus the fixed-domain return is to D_P, not to L or the full singleton
orthant. No active-support-dependent domain and no ignored outside
coordinate enters this argument.

### Minimum localization and the two exhaustive cases

D_P is nonempty and compact: s itself belongs to it, and it is a closed
subset of the reward box. At a minimum x, any coordinate strictly below
its singleton would make all Continue non-Nash. Exact finite root
existence and fixed-domain return would then give a strictly lower point
of D_P. Hence x belongs to L and minimizes H there too.

I re-read `IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
and its `exists_small_rates_quittingSingletonProbe` producer in
`UniformEquilibrium/Quitting/Root/CollisionAdjustedSingletonProbe.lean`.
The face inequality truly permits signed premiums: the collision-adjusted
source repairs the inactive players, including at upper-box faces.
With one binding coordinate, the minimum derivatives make its left side
nonpositive. Thus at least two coordinates bind. Increasing one binding
coordinate while retaining another gives a nonnegative binding partial;
nonbinding interior partials vanish and upper-face partials are nonpositive.

If some binding k is unprotected, lowering only k stays in D_P. Its root
returns to D_P. The signed Quit lower bound

    Q_k >= s_k - 2M*a

uses only that opponent absorption is at most total absorption; it does
not reinstate a nonnegative premium assumption. Combining it with Nash
and |w_k-v_k|<=(M+B)*a gives epsilon<=(3M+B)*a. Minimum and unit drift
therefore force a strictly positive lower directional quotient, whereas
its derivative is -g_k<=0. This is a complete contradiction with no
continuity or compactness assumption on a selected root.

If every binding coordinate is protected, lowering k may leave R_P.
The proof correctly does NOT apply return to that perturbed source.
Every exact root at the unperturbed minimum has zero absorption. For
any sequence of chosen perturbed roots, compactness of the finite hazard
cube and the closed polynomial Nash graph force absorption to tend to
zero; otherwise a positive-absorption subsequential root would exist at
x. No continuous selector is needed.

The successors still belong to R_P. Since all binding coordinates are
protected, the derivative signs imply g dot (w-x)>=0 throughout R_P,
even when unprotected nonbinding coordinates fall below their singleton.
The protected k floor gives epsilon<=(M+B)*a and displacement from x
at most 2(M+B)*a in maximum norm. Differentiability therefore bounds
BOTH Taylor remainders by o(a), not merely o(epsilon). The nonnegative
first-order successor term and nonpositive source term then contradict
unit absorption drift. The cases J minus P nonempty and J subset P are
exhaustive at the same minimum. No extra raw premise has been inserted.

### Exact adversarial tests of the missing stronger assertions

A two-player trap-free signed example shows that R_P cannot be replaced
by the full singleton orthant. Take P={0}, s=(0,0), and

    r(0)=(0,-1), r(1)=(0,0), r(01)=(0,-1).

At source (0,1), the exact root q=(1,0) has successor (0,-1).
The protected floor holds, but the unprotected one fails. This is allowed
by the theorem and correctly handled by D_P.

A separate signed four-player test shows that perturbed sources outside
R_P cannot be assumed to return to D_P. Pair partners 01 and 23; all
singletons are zero. For participants give reward 1 if their partner is
present and 0 otherwise; for passive players give 2 to players 0,2 and
0 to players 1,3. Change only r_1(013) to -1/10 and take P={0,2}.
The only traps are 01,23,0123, with protected strict leavers 0,2,0.
At v=(-1,1,2,2), q=(1/2,1/2,0,0), the forced (Quit,Continue)
endpoint pairs are

    (1/2,1/2), (1/2,1/2), (0,2), (0,1/2).

Thus this exact root has successor (1/2,1/2,2,1/2), strictly above
every singleton and outside D_P. The example checks the necessity of the
second arm's weaker R_P conclusion. Its zero singletons make it only a
logical stress test, not a source-coverage witness.

### Original-game consumer and weak closure

The inspected declarations supply exactly the stated chain:
`isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` has no
premium-sign assumption; the forward direction of
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
produces the polynomial under normality, a positive singleton, and absence
of UE; `isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
retains all exact roots of the same table. The box M+2 is strictly larger
than its reward bound, as required. If all nonnegative singletons vanish,
all Never is an exact uniform equilibrium instead.

Increasing every passive coordinate by delta leaves protected premiums,
own singletons, and all traps unchanged, and makes each designated weak
comparison strict. The exact
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
allows the approximating targets to vary and still gives one fixed target
for the limit table. Thus the weak STRATEGIC theorem follows. No weak
analytic exclusion is silently claimed.

### Signed proper-three-core fixture and bounded coverage

I reconstructed the full fifteen-row signed table. The protected players
0 and 2 retain all participant floors, while r_1(013)=-1/10 is genuinely
below s_1=0. Exact finite checks leave ONLY traps 01,12,012 and protected
strict-leaver sets {0},{2},{0}. The greatest core is the proper triple
012; the sole common trap member 1 still strictly joins 0. Thus this
is outside both the common-leaver class and the globally nonnegative-
premium support-specific class. The global-safe-quiet composition still
fails at r_0(3)=0<s_0=r_0(03)=1.

The singleton matrix, degree, inverse and first-order quotient tests are
unchanged from the independently checked original fixture. The response
values at (t,0,0,0) are also unchanged since the altered triple013 is not
sampled there. I checked all thirteen exact child profiles again: every
child deviation comparison remains nonpositive, and every stated omitted
gain is unchanged. At child013, the changed player-1 join is strictly
worse, not better. The pure improvement at coalition013 increases to
21/10 as stated. The diffuse child123 law, its full-regret bound tending
to zero, zero Never mass, and fixed outside gain 1/7 do not use the changed
entry at all. Hence the universal fixed weighted-debt exclusions survive
with exactly their original quantifiers. The prescribed-vector failures
of the older cyclic families are likewise unaffected.

These are bounded actual-input exclusions, not a claim that every possible
selected-child or stationary construction fails. The strongest signed
protected-set theorem, its weak strategic closure, and the stated coverage
witness all survive this independent falsification. No mathematical repair
is requested.

## Final artifact check: support-specific leavers with signed premiums

**Artifact PASS.** The preceding Section-17 mathematical PASS applies to
the entire 598-line standalone
[`SUPPORT_SPECIFIC_LEAVERS_WITH_SIGNED_PREMIUMS.md`](../exports/SUPPORT_SPECIFIC_LEAVERS_WITH_SIGNED_PREMIUMS.md),
SHA256 `fcb44202792e11237be46008dbea76718d1a2b704662fe12cab71e605a803208`.
I read every section, recomputed the hash, and checked the mathematical
assembly deltas. This is not another full theorem audit or a Lean check.

The strongest signed assumptions, strict finite-player analytic theorem,
weak Fin4 strategic conclusion, both minimum perturbations, and all
absorption-relative estimates are preserved. The canonical P_max test
is equivalent to existence of an admissible nonempty P by monotonicity
of the designated-player choice. It does not alter the raw class.

The new self-contained singleton-face proof correctly corrects only
binding nonowner coordinates. Those coordinates lie strictly below B;
nonbinding coordinates need no correction because their positive
singleton gap dominates every collision term at sufficiently small
rate. This includes upper-box faces, where the source must not increase.
The source and successor formulas yield the identical unit derivative
inequality with no premium-sign hypothesis.

The new three-player boundary regression checks for every 0<epsilon<1.
Its sole trap is01, protected player0 strictly leaves, and at the stated
source/root the endpoint pairs are exactly

    ((1+2epsilon)/(1+epsilon),(1+2epsilon)/(1+epsilon)),
    (1/2,1/2), (0,(1+2epsilon)/(2+2epsilon)).

The successor is strictly above every singleton, whereas the limit
root at the boundary annotation still absorbs. The text explicitly does
not call that annotation a potential minimum. It therefore demonstrates
the intended failure of unconditional near-boundary root collapse without
contradicting the actual-minimum compactness argument.

The signed fifteen-row fixture is unchanged. The new displayed
thirteen-partition table has the stated unequal row sums, including
full-block sums1 and0. The matrix's R0/degree-one proof and non-Q
claim for principal03 remain correctly separated. The complete child
comparisons retain their full-behavior meaning and their exact
for-each-child/there-exists-omitted-player debt quantifiers. The covered
full-core branch is honestly attributed to the tracked small-Never
and globally safe quiet-player composition.

The reward-closure argument preserves one target before accuracy and
uniformity over all behavioral deviations. Named declarations resolve
at the indicated source files. The handoff retains the signed support
endpoint and actual-support leaver choice, while identifying the second
minimum arm as new work. There are no notebook, feedback, or other
math-directory dependencies, no review-history section, and no claim
to a checked implementation. No repair is requested for these bytes.

## Independent review: signed pair core with same-sign gaps

Verdict: PASS as ordinary mathematics, not a Lean check. Scope is
section18, "Signed pair cores: a negative index without any protected
floor", frozen in the whole notebook at SHA256
`11d20a89b8670553264029ed3b6f7db4b30b351a0118f328823537e52af90c17`.
The later section19 append is outside this review and was not read.
No other review of this theorem was consulted.

The audited statement allows arbitrary signed participant premiums,
requires the union of all premium traps to be one pair C={i,j}, and
requires the two leave/join gaps to have the same weak sign. For Fin4
with nonnegative own singletons it gives a uniform-equilibrium payoff.
The analytic theorem uses strictly same-sign, nonzero gaps; the weak
boundary is obtained by reward closure, not by asserting the same
index argument at a degenerate mixed root. Opposite strict signs and
arbitrary larger cores are not covered.

### Exact supports and selected return

Every active support other than C is a nontrap: some active player has
all its within-support participant rewards at most its singleton. Its
exact Quit endpoint, hence successor, is at most that singleton. For
an outsider k and T contained in C, the same upper bound holds for
r_k(T+k), since a strict violation would make C+k a trap. These are
upper bounds; no unsupported flatness or lower bound is used.

At a core-only root, with d_i=r_i(ij)-r_i(j), the exact gaps are

    g_i=s_i-v_i+(v_i-s_i+d_i)*q_j,
    g_j=s_j-v_j+(v_j-s_j+d_j)*q_i.

If one core player is sure and the other is interior, the latter's
gap is the nonzero d. Thus a bad successor strictly above every
singleton can only come from the pure pair or the unique possible
interior pair candidate. The candidate has

    q_i=(v_j-s_j)/(v_j-s_j+d_j),
    q_j=(v_i-s_i)/(v_i-s_i+d_i).

An interior ratio forces its numerator and its d to have the same
strict sign. Zero denominator does not hide another candidate, since
the corresponding gap cannot vanish when d is nonzero. A pure-pair
root, if present at any source, is independent of that source: every
player has a sure quitting opponent. It therefore supplies an
absorbing self-loop at its reward vector and directly excludes a
strict-drift potential.

In the remaining case, suppose all exact roots at a source with some
v_h<s_h were bad. All would equal the displayed mixed candidate p.
For each outsider, Q_k<=s_k<w_k=C_k, so its Continue inequality is
strict. This crucial strictness follows from badness, not from an
assumed generic perturbation.

Extend the literal clipped map

    F(q)_k=min(1,max(0,q_k+g_k(q)))

to the ambient Euclidean space using the polynomial endpoint gaps.
Its fixed points are exactly the full Nash roots in the unit cube.
Near p the outsider rows of F are constant zero and the core rows
are unclipped. The Jacobian of q-F, with core coordinates first, is

    [ 0       -alpha_i    * ]
    [ -alpha_j  0         * ]
    [ 0         0         Id],

where alpha_i=v_i-s_i+d_i and alpha_j=v_j-s_j+d_j.
The determinant is -alpha_i*alpha_j<0. All outsider derivatives in
the upper-right block are retained. Although p lies on a face of the
unit cube, it is interior to the ambient region (-1,2)^I: its local
degree is -1, not a half-index. Globally F has degree +1 there, by
the homotopy to a constant map taking values in the unit cube. No
boundary point of the ambient region can be fixed during that
homotopy. Excision of a unique fixed point contradicts local degree
-1. This proves existence of a low-successor root, not a claim about
every root.

### Minimum argument and semantic endpoint

The compact domain is the whole boxed lower region: some coordinate
is at most its singleton. If a minimum has any strict deficit, the
selected-return lemma produces an absorbing successor in that same
domain and contradicts drift. Thus a minimum belongs to the lower
boundary above all singleton floors. The signed singleton-face
inequality rules out a unique binding coordinate. With at least two
binding coordinates each binding derivative is nonnegative.

Lowering a binding coordinate by epsilon permits selected return
again. The signed estimate Q_k>=s_k-2M*a, Nash, and bounded successor
displacement give epsilon<=(3M+B)*a. Minimality and drift force a
strictly positive lower bound for the directional difference
quotient, whereas its limit is the negative of a nonnegative binding
derivative. This is a contradiction. There is no concealed convergence
or continuity requirement on the selected roots.

Nonnegative own singletons supply normality independently of signs
of larger participant premiums. The named polynomial-obstruction
consumer then gives the original Fin4 fixed-target uniform-payoff
conclusion; all-zero singletons have the direct all-Never exit.
When one or both d's vanish, changing only the appropriate passive
partner-singleton rewards makes both gaps strictly positive or both
strictly negative. The premium core and own singletons are unchanged.
Reward closure gives one limiting target and retains unrestricted
behavioral deviations. No weak-gap analytic exclusion is claimed.

### Exact falsification tests and bounded source comparison

I independently checked all fifteen rows of the displayed fixture.
Its only trap is03, its two gaps are2, and every player has a negative
grand-coalition participant premium. None of the fifteen pure
coalitions is an equilibrium. At

    v=(3,-1,4,2), q=(1/2,0,0,1/2),

the exact endpoints are

    Q=(3/2,0,0,1/2),
    C=w=(3/2,1/2,1/4,1/2).

Thus this same table really has a bad root from a below-floor source.
The outsider gaps are -1/2 and -1/4, and the local determinant is
-16. This falsifies replacing selected return by universal return.
The singleton-matrix tests and response residuals t,t,t+t^2 retain
their stated bounded force. The sure03 law directly fails product-low;
both positive pair gaps exclude the aggregate-leave weights; and no
player has globally nonnegative participant premiums. The review does
not claim an exhaustive exclusion of every stationary or quiet-child
method.

For an independent minimal opposite-sign stress test, take two
players with r(0)=(0,0), r(1)=(2,0), r(01)=(1,1), and source
v=(-1,1). The gaps are 1-2q_1 and -1+2q_0. Every boundary support
fails, leaving the unique exact root q=(1/2,1/2), with successor
(1/2,1/2) above both zero singletons. Its local determinant is +4
and its index is +1. The selected-return extension to opposite gaps
is therefore false. This is not a counterexample to UE; both own
singletons are zero.

Static source checks included `ambientDegree_homotopy` and
`ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in
`MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
For the last declaration one can place the closed region (-1,2)^I
inside a larger ambient chart; the explicit constant homotopy already
supplies the required boundary condition.

The old `quittingPremiumCore_outsider_reward_eq_singleton` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`
and `exactRootSuccessor_active_eq_singleton_of_support_ne_pair_core`
in `UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`
require nonnegative participant premiums. So does
`exists_uniformEquilibriumPayoff_of_pairPremiumCore_weakLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/QuittingPremiumCoreUniformPayoff.lean`.
They do not automatically consume this signed fixture. The signed
face, displacement, potential restriction, polynomial-obstruction,
and reward-closure consumers have the hypotheses checked in the
earlier reviews above; none silently restores a premium sign.
No mathematical repair is requested.

## Independent check: the full four-core boxed charge and fixture

Scope: section20, "A full four-player core with no protected linear
floor", at whole-note SHA256
`80445d49c25bf21ae816af9273db7ae8dc54adb5ac6f769c97f7f120df931879`.
Verdict: PASS as ordinary mathematics, with a neighborhood-scope
clarification below. This was checked after my independent derivation
of the cardinality version in my own notebook; no other review of
section20 was read. This is intended for consolidation, not a second
special-case export.

The two coefficient sums P(T) and L(T) must remain distinct. Their
cardinality bounds give d*U<tau*E_3 and the exact source charge
sum(s-v)>=g*U+l*E_3. The equal-coordinate maximum E_3<=U^3/16
is correct, including boundary vectors. Its strict charge bound and
the available box produce return for every absorbing exact root.
The partial-sure case has a positive-probability coalition I-i with
strictly negative leave coefficient; the all-sure case is separately
excluded by withdrawal. No low-floor premise at the source is used
for this return theorem. The signed same-D minimum proof and the
same-polynomial restriction from M+2 to a smaller B>M are valid.

I reconstructed the entire fifteen-row table and independently
enumerated its traps: I is the only one and M=3. The four singleton
P coefficients are all -9/2; the L coefficients are exactly
-3/2,-13/2,-13/2,-9/2. The six pair coefficients are P=-4,L=-8,
and the four triple coefficients are P=1/10,L=-19/10. The source
threshold is exactly 348*sqrt(45)>13. The global nonnegative-floor
weight exclusion follows from the four sure-singleton product laws,
whose summed premium expression is -(9/2)*sum(lambda).

All fifteen pure coalitions have the stated improving moves. For
every proper nonempty child I checked the displayed sure-singleton
owner and omitted player. The child profile is exact against complete
behavioral deviations, has zero joint Never, and gives the omitted
player a gain1/2. Thus the strong for-every-child/there-exists-outside
quantifier really holds; this is not just a list of local incentives.

The singleton matrix is literally the previously checked G3. I also
reenumerated all fifteen partitions from the block-row sums: only the
discrete one and0|123 survive. The latter fails at q=(t,0,0,0),
where the three responses are t-2t^2,t-t^2/2,t-2t^2. The
previous R0-degree-one, inverse and non-Q screens therefore retain
their claimed force without an additional matrix assumption.

Neighborhood clarification for assembly: three displayed own
singletons are zero. Strict coefficient margins preserve the analytic
criterion in a full raw neighborhood, but the strategic Fin4 theorem
still assumes nonnegative own singletons. Its admitted set near this
fixture is full-dimensional, not an unrestricted open neighborhood
of this boundary point. Raising just the three zero singleton-own
entries slightly produces an interior point with all singletons
positive and with strict raw margins; a small full neighborhood there
is admitted. This clarification does not affect the exact fixture,
the source comparisons, or the main theorem.

## Final artifact check: signed same-sign pair cores

Verdict: PASS for the complete 568-line
[signed-pair standalone](../formalized/SIGNED_PAIR_CORE_SAME_SIGN_UNIFORM_EQUILIBRIUM.md),
SHA256 `6eef4888ef06911bf6de766cf7a798328d94b3b31e95203eebab87c6e5466f6a`.
This is a bounded assembly/delta check against my section18 proof
review, not a third full mathematical audit. I read every assembled
section and independently tested its new examples. No other final
artifact review was read. This is not a Lean check.

The statement retains arbitrary signed participant premiums, greatest
core empty or a pair, nonnegative own singletons for Fin4 UE, and
same weak sign of the pair gaps. The finite-player analytic exclusion
remains strict. The standalone degree argument includes its concrete
ambient homotopy and local affine comparison. The full root map,
strict outsiders, determinant block, same-D minimum, signed source
charge, and unchanged-function polynomial restriction are preserved.
The weak boundary perturbs only passive singleton entries and gives
one limiting target before accuracy; it does not assert a degenerate
negative-index calculation.

The newly displayed good root at the same source as the old bad root
checks exactly. At v=(3,-1,4,2), q=(0,2/3,0,1/3), the endpoints
are Q=(10/9,0,0,0), C=w=(14/9,0,17/9,0). Thus it is a full
Nash root and its active players return to their singleton levels.
The negative-index bad root remains available at that identical
source; this is an explicit distinction between selected and
universal return.

I checked all thirteen new pure child-profile rows, including the
two-player sure coalition03 in children03 and013. Their comparisons
are against both first actions and every delayed owner strategy;
the Never continuation gives no hidden profitable owner deviation.
The child123 cycle has exact values (1,0,0),(0,1,0),(0,0,1),
all forced-Quit endpoints zero, and geometric opponent survival.
Quiet player0's value is6/7 and first-date Quit pays3/2, so the
stated gain9/14 is correct. All fourteen child comparisons retain
the exact universal weighted-debt-plus-Never quantifier and are not
misrepresented as exclusion of every quiet-profile selection.

The assembled four-player opposite-sign regression also checks.
Player3 is strictly inactive at every root, and its absence makes
the modified grand row irrelevant to the other three endpoints.
The two core equations force hazards1/2,1/2, and player2 then has
Q=0<C=2. The unique successor is(3/2,1/2,2,1), with inactive
gaps-2,-1 and local determinant8. This is a selected-return
falsifier, not a uniform-equilibrium counterexample.

The singleton matrix, inverse/degree calculations and all fifteen
partition exclusions retain their verified bounded scope. Named
source declarations match the actual consumers and preserve the
distinction from the old nonnegative-premium weak-leave theorem.
The packet is self-contained, contains no conference-file dependency
or review history, and claims no new checked implementation. No
mathematical or assembly repair is requested for these exact bytes.

## Independent Section21 review: zero-premium joint phase

Verdict: PASS for **A zero-premium joint phase and an opposite-sign
residual core**, through the end of the notebook at whole-file SHA256
`3405a3a3797b5a8182c7511622f4d8b4cd2298413540df30e5c986b6bcf6080b`.
I read no counterpart review. Scope is the five literal reward rows,
arbitrary real R, sigma>=0, three player1 join caps<=1/2, and three
player2 join caps<=0, with all other reward entries free. The conclusion
is one uniform-payoff target for the actual table against unrestricted
behavioral deviations. No mathematical repair is requested. Calculations
and source inspections here are ordinary mathematics, not Lean checks.

### Original-table outer exits

The actual child matrix has determinant7, the displayed positive inverse,
and A*1=1. For a positive homogeneous pivot, the negative cycle forces
all child variables positive and equal to that pivot; the remaining
residual is p(R+1). At zero pivot the child cycle and invertibility
give only the zero root. Thus R!= -1 gives R0, and R=-1 has the
explicit nonzero homogeneous vector of all ones. The stated Fin4
no-UE implication to R0 applies at equality without a degree argument.

For R<-1, the offset q0>d with d=-(R+1)>0 has exactly the two
claimed roots. Their active determinants are7 and7(R+1), their inactive
inequalities are strict, and degree is zero. For R>=1/4 the passive
inverse row is exactly (4R-1,R+5,2R+3)/7 and is nonnegative, including
the endpoint. Both exits concern the original singleton matrix and
place no hidden condition on collision rewards. They leave precisely
the interval -1<R<1/4 for construction.

### Scalar producer and complete undiffused equations

For tau=1-4R in(0,5), X=tau*Y/(5+3Y) is positive and increasing.
The numerator of a1 is strictly positive even at sigma=0. Hence w
is proper, while z is strictly increasing from zero to infinity. The
z=1 polynomial is (tau+3)Y^2+(tau-1)Y-10. Its value at
Y=4/(tau+3) is exactly-6, so the top endpoint satisfies delta*Y*>1.
I independently expanded F: its divided origin limit is
7(tau-5)/20<0, and at z=1 it is delta*Y*-1>0. Thus IVT gives
an interior root with all four rates proper. No branch uniqueness or
continuation is presumed.

The algebraic identity X=2delta*Y-3z holds before imposing F=0.
Together with F=0 it gives X=-z+2w(1-z). I checked all twelve
literal Continue equations symbolically. Before imposing F=0 their
only nonzero residuals are -F/(1+Y) for player0 at A and -2F for
player3 at B. Every supported Quit endpoint equals the displayed
current value identically. Thus all twelve policy equations hold at
the selected root, retaining the simultaneous03 reward.

The player1 ratio a1/m is exactly the displayed fraction. Subtracting
half its denominator gives 3(5-tau)/2 plus
(9/2-tau/2+sigma*tau)Y, strictly positive across the whole interval.
Its three actual joint Quit rewards therefore give Q1<=m/2<a1.
Player2's corresponding endpoint is nonpositive. Both joint owners
are exactly indifferent. The six caps are exhaustive for the two
joint outsiders; no other collision coordinate is consumed there.

### Refinement, unlimited behavioral replacements, and target order

Refining each solo block preserves its aggregate singleton law and
both endpoint values. Interior values interpolate between the macro
endpoints, so every own singleton floor persists. Pure Continue stays
exact and the solo owner stays indifferent. Every other immediate
Quit endpoint is at most its singleton plus L times the microhazard,
hence at most its current value plus the common error epsilon_n.
This includes arbitrarily large unused collision rewards.

Adding this SAME error to every continuation value gives one global
supersolution, not a sum over the number of dates. All four displayed
opponent period-survival factors are strictly below one. From any
starting date a finite initial partial period followed by full periods
still has vanishing survival, as required by the actual path consumer.
Against any behavioral replacement, presampled independent opponent
coins bound absorption by their first Quit. This removes the bounded
Bellman remainder uniformly in the deviator. Exact policy transport
and geometric survival also identify all phase values with actual
terminal expectations, establishing their reward bound without an
extra supplied-value hypothesis.

For fixed n the expected absorption time under every replacement is
bounded by the stated K_n. Thus the uniform horizon regret allowance
epsilon_n+4M K_n/N is valid, as is target error2M K_n/N. The selected
macro target V_A is fixed before n and N. Censoring individual laws
after K periods changes total marginal mass by the displayed t_K;
opponent-only coupling against each fixed full deviation and the
separate prescribed-payoff comparison give regret epsilon_n+4M t_K.
This is uniform over complete deviations, not a finite-action test.

An independent rational stress case is R=0, sigma=101/42, Y=2/3.
It gives

    X=2/21, x=2/23, y=2/5, z=26/63, w=16/37,
    V_A=(1,16/21,0,0),
    V_B=(5/3,0,52/63,2/21),
    V_C=(53/37,0,0,32/37),   m=52/115.

All equations hold exactly. Set all three player1 caps to their positive
boundary1/2 and player2 caps to0; other unused entries can be37.
Then, for example, the last microdate of solo1 has player2 Quit excess
35*beta_n, and the last solo2 microdate has player3 excess35*gamma_n.
These genuine errors show why solo refinement is needed. This stress
completion is only an algebra/consumer check, not a new-coverage witness.

### Exact opposite-sign fixture and claimed exclusions

I independently reconstructed the entire15-row fixture. Its only trap
is12, whose gaps are3/2 and-3/2. Every player has a negative grand
premium; the protected-set, same-sign-pair, no-pair boxed-charge, and
product-low input failures are as stated. The singleton matrix retains
the previously audited bounded inverse, degree, and first-order partition
screens. I recomputed the remaining full response at q=(0,t,t,t):
the first two child coordinates are -t+t^2(1-t)(2-t)/2 and the third
is -t, so the candidate block fails. The old temporal comparisons
correctly concern actual raw inputs, not completeness of those methods.

For R=0,sigma=2, I get

    F(Y)=Y*(28Y^3+60Y^2+Y-35)
          /[(3Y+5)*(12Y^2+18Y+5)].

The cubic is increasing on the nonnegative axis, with values -844/125
and588/125 at3/5 and7/10. The displayed algebraic rates follow.
Its buffer ratio minus3/2 is Y/(2Y+3)>0.

All thirteen sure child profiles are exact against full behavioral
replacements; the omitted gains are3/2 exactly in the singleton2
rows and1 otherwise. For child123, the solo3,1,2 half-hazard cycle
has the stated child values; microhazard error is at most alpha_n/2.
The quiet player0 payoff is6/7 while its immediate Quit is exactly1,
not merely asymptotically1. Hence the fixed1/7 gain defeats every
fixed finite nonnegative weighted child-debt-plus-Never estimate.
The quantifier remains each child/some omitted player; no selected-
quiet-strategy impossibility is inferred.

The stationary quiet-player exclusion checks including sure hazards.
When q0=0 and all children are active, their endpoint inequalities
force q3<=3q2/4, q3>=3q1/2, and q1>=2q2, a contradiction.
Every two-child support has a specified active positive-passive player
whose Continue is strictly better; singletons have a profitable join.
When q3=0 and q0>0, player0's Quit is1 while any positive child
hazard makes Continue exceed1. For q1=0, positive q2 forces q2=1,
then player0 prefers Continue; otherwise the residual03 support forces
both hazards to1 and player2 joins profitably. Finally q2=0 forces
q3=1 then q0=1, after which active player1 prefers its passive2 to
Quit0. These cases exhaust every quiet coordinate. No exclusion of
fully supported stationary equilibria or UE is claimed.

Reinspected exact sources were
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
and `QuittingInfinitePathQuitErrorCertificate`,
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
`QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`,
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The quiet-debt and response definitions use the same exact source audits
recorded earlier. No source assumption is missing from this candidate.

### Final zero-premium artifact binding

Final artifact PASS applies to the complete469-line
[`ZERO_PREMIUM_JOINT_PHASE_UNIFORM_EQUILIBRIUM` packet](../exports/ZERO_PREMIUM_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md),
SHA256 `5e89dec50dd74bd1ea85b5bd7098f18805cf95951a72d6ddcef25af3f8ea450c`.
I read all its bytes and checked only assembly additions against the
independent substantive review above; no other review was read.

The standalone preserves every raw equality, six cap inequalities,
sigma=0 inclusion, both outer equality exits, fixed-target quantifier,
and unrestricted behavioral/horizon proof. The new explicit child LCP
propagation is correct: a zero first child coordinate with positive
right-hand side forces the third and then second positive, whose active
equation is impossible. Its zero-pivot argument likewise follows the
negative cycle to full support. The inverse entries and all thirteen
displayed partition row-sum mismatches check against the literal matrix.
The final grand-coalition pure-exit exclusion is correct: player0 improves
from-1 to0 by withdrawal. No broader stationary exclusion has been added.

The tracked declarations have the same source assumptions audited above.
The handoff states an actual raw-data producer, not a supplied-controller
verifier. All mathematical data and proofs are self-contained; no
conference notebook, feedback, or other math-directory dependency is
required, and no review history or new Lean-check assertion appears.
There is no mathematical or artifact repair requested for these bytes.

## Independent Section 29 review: negative scheduled premiums

**PASS for the complete raw producer and its full-coordinate neighborhood.**
The reviewed surface is Section29, “A negative scheduled-premium arm of
the matching two-phase producer”, through EOF of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, whole-note SHA256

    84cf88f403ed0004abc2c7bf107f0d9b8e5b4b5312a9ef14da9ebdbafedc31d9.

I independently read and checked this surface without reading another
review. This is ordinary mathematical review, not a Lean check. I find no
unresolved mathematical objection or missing strategic witness. A final
standalone artifact will need its own bounded byte-level assembly check.

### Claim and scope checked

There are four players with the favorable matching f=(01)(23), scheduled
pairs02 and13, private independent behavioral actions, zero live and Never
rewards, and all fifteen actual terminal reward vectors. Own levels s_i
are arbitrary signed reals, scales b_i>0, H>2. Singleton increments are
Hb_i at f(i) and−b_i at both other players. Scheduled-pair participant
and passive increments are Πb_i and Kb_i, with

    Π<−1,       K<(7Π+10−2H)/2.

For C=4(−Π−1)/3 the twelve outsider joining rewards are at most s_i−Cb_i.
All other reward entries are free. The theorem produces a proper common
hazard for the two scheduled phases, exact terminal Nash against every
behavioral deviation, and one fixed uniform payoff for the original game.
The additional neighborhood theorem imposes no exact singleton or pair
equalities on nearby reward tables.

These are actual raw-data producers. The hazard, all phase values, all
unilateral inequalities, and the deleted-opponent contractions are outputs,
not assumed strategic inputs. The theorem is not a universal periodic
architecture claim and does not solve arbitrary Fin4.

### Root selection and all action endpoints

For P(t)=Πt³+(H−1−K)t²+Kt−(Π+1), direct calculation gives

    P(1/2)=(2H−10−7Π+2K)/8<0,       P(1)=H−2>0.

Thus a root can be chosen once in (1/2,1), despite P(0)>0. With
q=1−t, U_i=s_i+qΠb_i and W_i=s_i+q(Π+1)b_i/t, both supported
active endpoints equal U_i exactly. The passive Continue value is
s_i+b_i[qt(H−1)+q²K+t²qΠ]; subtracting W_i is zero exactly at P(t)=0.
This calculation includes the simultaneous other-pair payoff K.

The passive Quit bound is s_i−(1−t²)Cb_i, including its empty-opponent
singleton term t²s_i. Set c=−Π−1>0. The passive Continue margin over
that bound is q b_i[(1+t)C−c/t]>0, because t(1+t)>3/4. Thus W_i<s_i
is legitimate here: its action cap has been lowered too. There is no false
inference that a below-singleton phase is automatically unsafe or that a
singleton floor is needed at every date.

All sixteen unilateral action endpoints and all eight policy equations
are accounted for. The twelve caps contain each possible outsider's two
pair joins and triple join. The free reward100 entries of the fixture belong
to the scheduled participants of a triple, not to its deviating outsider;
they cannot enter that outsider's payoff. Grand rewards cannot occur under
one deviation against either phase. Signed own rewards do not alter Never.

### Attempted falsification: a second proper root is not interchangeable

At H=3, Π=−11/10, K=−179/60,

    P(t)=−(3t−2)(22t²−85t+3)/60.

Besides t=2/3, there is a small positive root
t₋=(85−√6961)/44∈(0,1/20). If the twelve cap entries are all set
at their allowed equality13/15, this small root does NOT give an equilibrium:

    W_i=1−(1/10)(1−t₋)/t₋<−9/10,
    Q_i^passive=1−(2/15)(1−t₋²)>13/15.

The direct deviation gain is positive. This is an exact failed extension
from “choose a root above one half” to “choose any proper root”, not a
counterexample to the stated theorem. The author's interval choice is
load-bearing and correct. No uniqueness or favorable unproved selector is
being assumed.

### Complete behavioral and uniform-horizon consumer

Policy iteration has joint survival t⁴<1 per period and hence identifies
the proposed bounded U,W with actual terminal values. For a fixed deviator,
its three opponents survive a period with probability t³<1 independently
of the deviation. Iterating the two action inequalities leaves a bounded
remainder times t^(3n), uniformly over full behavioral replacements. It
vanishes, including for Never and arbitrary late randomized stopping.

The first-opponent stopping time has expected date-plus-one at most
1+2/(1−t³). Absorption under any unilateral deviation is no later.
Thus the quoted terminal/finite-average error and twice-that regret bound
hold uniformly over all deviations, with the initial live-zero date included.
The chosen vector and profile are fixed before the requested error; one
profile works at every sufficiently large horizon. There is no interchange
of a supremum with pointwise horizon convergence.

The exact consumers checked are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`, with the
literal endpoint definitions and endpoint-mixture identity in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
All their actual inputs are produced by the proof.

### Full sixty-coordinate neighborhood

I independently differentiated the actual four equations (127), not a
reduced symmetric equation. At X*=(1/2)1 the mate derivative is19/72,
favorite derivative−19/12, other-opponent derivative29/12, and own
derivative0. This is exactly the stated full4×4 Jacobian. Its eigenvalues
are79/72,−307/72,−41/72,269/72 and its determinant is
267486337/26873856>0.

The map T_r(X)=X−J⁻¹E(X,r) has X derivative zero at the base point.
In a sufficiently small closed positive ball and a sufficiently small
full reward neighborhood its derivative norm is at most1/2, while its
center displacement is at most half the ball radius. The mean-value bound
then makes it a self-map and contraction. The resulting fixed point is
positive and solves all four original equations. The estimate
‖X(r)−X*‖≤2‖T_r(X*)−X*‖ proves its needed convergence to X*.

Every proper probability, every actual passive Quit gap37/60, and every
opponent-deleted contraction persists. This produces a certificate for
each nearby FULL reward table, including perturbations of all singleton
and pair equalities. No local strategy witness, inverse, or implicit root
certificate is supplied as a hypothesis. The common-parameter raw theorem
and the unrestricted sixty-coordinate neighborhood are correctly distinct.

### Exact complete fixture and coverage tests

Rational recomputation of the complete fifteen-row table gives active
endpoints19/30, passive Continue19/20, passive Quit1/3, and passive
gap37/60 at every applicable row. At the full-support1/10 hazard,
the forced-Quit vector is exactly
(24739,24729,24719,24709)/10000. Every entry exceeds the singleton1,
so product-low and the supportwise nonpositive-weight condition both fail.
The only premium trap is I. All fifteen pure coalitions have the stated
profitable deviation; all Never also fails.

I checked all fourteen child cases with their stated quantifiers. For a
singleton child, or a favorable/scheduled pair, the indicated sure solo
is exact child Nash and its omitted harmful nonscheduled partner gains1/2
by joining. For a harmful nonscheduled pair its sure joint exit is child
Nash and either omitted player gains100. For a triple omitting m, pure
o(m) is child Nash and m gains1/2. Every witness has zero child regrets
and zero Never mass. These exclude universal nonnegative weighted child-debt
plus finite-Never lifts, not every conceivable specially chosen quiet profile.

The grand participant premiums are all negative, so no protected player
or nonzero global nonnegative floor weight exists. The full trap's favorable
pair insertion charge is198>0, excluding the boxed and mixed-trap charge
condition. The full greatest core excludes the pair/triple core classes.
For terminal upper-bound weights, Γ has row sums1; Γᵀλ≤0 with λ≥0
therefore forces λ=0. The conditional range test is impossible since its
ContinueUpper≥4 but its required lower Quit mixture is at most1.

The matrix Γ₃ has eigenvalues1,5,−3,−3, determinant45, and the stated
strictly positive inverse. Its nonzero principal determinants and negative
entries in every column give R₀, and the degree is+1. The negative-det
inverse and all-principal Q/homogeneous exits therefore fail. Each triple
inverse has a negative diagonal entry. The all-sure responses
−101,−102,−103,−104 exclude every nondiscrete response quotient; equal
singleton row sums also prove the claimed exclusion after positive affine
row transport.

The singleton sign graph excludes the unique-negative-partner paired
pattern, favorable four-cycles, reciprocal-opposite-sign patterns, and every
cyclic child under deletion. The overlapping period-three affine cylinder
comparison is valid: all its participant-pair coordinates are visible and
equal to the own level at its center; their invariant normalized difference
is at most2ε/(1−2ε)<1/4. Here it is1/2 or11/10 for every pair participant.
The sure-outsider crossed-face witnesses are exactly−7/2 or−1/10 for
every ordered selected pair, excluding even weak polynomial lower guards.

### Proper-three stationary exclusion and current strongest matching overlap

For support012, the designated player's Quit equation is
1−11a/10−x/2+(503/5)ax=0. It implies
a=(10−5x)/(11−1006x), 0<x<1/1001, and10/11<a<1.
For player1, direct calculation gives the stated Q₁,N₁. With
F=(a+c−ac)(N₁−Q₁), independent expansion gives

    ∂_aF=a+3+(5a−239/60)c+(5/2−6a)c².

For a≥10/11 this is concave in c with positive endpoint values a+3
and91/60. Moreover F(10/11,c)=(213c²−1855c+2280)/726 decreases
on[0,1] to29/33>0. Thus N₁>Q₁ throughout the possible support region.
The stated symmetries of the rows of size at most three give all four
deleted supports. This excludes the literal proper-three source of
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`,
not arbitrary fully supported or sure-boundary stationary equilibria.

I compared against the strongest arbitrary-K matching theorem, not only
its earlier nonpositive-K version. Favorable singleton signs force f.
For scheduled02/13, participant reward−1/10 is below the mate singleton0,
violating the weak participant comparison. For scheduled03/12, that comparison
holds but an outsider triple join pays100>1, violating a cap. These cover
every relabeling and persist under positive row affine transport. Every
pair participant premium is negative, so the separate general inverse-positive
Π_i≥0 criterion cannot apply either. Arbitrary K does not repair either
failed input. These are strict raw failures, not a claim that the new table
merely has a different displayed root.

### Source audit and significance verdict

In addition to the exact cyclic consumers, inspected declarations/files for
these comparisons include
`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`),
`quittingSingletonBlockRowSum_eq_of_responseInvariant`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`),
`PairedCycle.RawRegion.eq_partner_of_singleton_lt`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`),
`IsInvisibleRewardCoordinate`
(`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`),
`overlappingPeriodThreeRewardRow`
(`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`),
`IsQuittingConditionalFaceGapRange` and
`exists_uniformEquilibriumPayoff_of_conditionalFaceGapRange`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`),
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`),
`QuittingHalfWeakPolynomialGuards`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`),
and `QuittingOneSidedWeakUnitGuards`
(`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`).
These are read-only source inspections and exact arithmetic, not Lean builds.

My independent significance verdict is affirmative: the candidate gives an
original-table producer and a full-coordinate existence neighborhood with a
complete raw fixture outside the applicable implemented and accepted criteria,
including the arbitrary-K matching theorem. Its gain is the below-singleton
passive phase regime with actual stronger joining caps, not first use of an
implicit-function neighborhood. No unrestricted strategic input is hidden.
The same-support scalar formula alone would not establish this comparison;
the complete table and local producer do. No repair is requested, and no
stronger global negative-premium or arbitrary-game claim is inferred.

## Final below-singleton artifact: bounded assembly and delta PASS

I read all 660 lines of
[the standalone below-singleton packet](../exports/BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md),
with exact SHA256
`6b75ada2ad8e675fd32216d0f1d98fbfdfee6ef5a47d0b7ca8aed05eb2d0e3ca`.
This is a bounded final-artifact check against my independent Section 29
review above, not a new inference from another review. No counterpart
feedback was read. Verdict: **PASS on these exact bytes**, with no unresolved
mathematical or strategic objection.

The standalone preserves the strict raw parameter inequality, all twelve
pair/triple caps, signed own-singleton scope, the selected interval
t∈(1/2,1), and the full sixteen-endpoint calculation. It retains the
opponent-deleted geometric tail for every behavioral deviation including
Never, produces an actual terminal value, and proves the correct initial-zero
finite-horizon bounds for one fixed uniform target. The actual inputs to
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` are all
produced, not supplied as additional hypotheses. I rechecked these consumer
declarations directly. The full-coordinate contraction proof retains its
four original equations, nonsingular full Jacobian, positive closed ball,
uniform contraction, actual passive inequalities, and convergence to the
specified root. It does not infer an open neighborhood of every scalar
family member.

The added robust proper-three exclusion is valid uniformly over its whole
claimed coordinate ball. Forced-Quit and absorbing-opponent Never values
are both 1-Lipschitz in the reward sup norm at fixed hazards, even as the
opponent absorption probability becomes small. Approximate player-2 mixing
therefore forces a>9/10. Independently expanding the player-1 numerator gives
F(9/10,c)=(64c²−512c+621)/200≥173/200 and the displayed derivative,
whose endpoint values are a+3 and 91/60. Since 0<D≤1, the actual payoff
gap exceeds 173/200, while a reward change δ changes it by at most 2δ.
Thus δ≤1/1000 cannot repair mixing. The Klein relabelings use only rows
of size at most three and cover all four deleted supports. The artifact
correctly does not exclude full-support or sure-hazard stationary profiles.

The new signed-influence and affine-membership exclusions follow from the
two exact increments −9/2 and 1001/10 for the same ordered influence.
I checked `SignConsistentQuittingInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`:
the raw tests stated in the packet are necessary for those definitions.
Both strict violations persist locally. The inline joining-row argument
also has the right quantifiers: a child cutting an o-pair has a positive
omitted join and nonpositive child joining/withdrawal terms at one singleton
background; a child cutting neither is exactly an o-pair and has the same
contradiction at its joint background. This supports failure of universal
nonnegative debt/withdrawal lifts, not failure of every chosen child lift.

The full table, source comparisons, positive-affine partition exclusion,
and both arbitrary-passive matching alternatives are preserved. The second
cubic-root regression is complete and correctly scoped: the smaller root
has passive continuation below −9/10 and Quit above 13/15; the selected
root on the modified table has positive gap 13/540. No unspecified-root
selection is used by the theorem. The mathematical significance remains an
original-table producer and a full-coordinate region beyond the compared
accepted and implemented raw producers, rather than a new supplied witness.

All cited Lean paths are tracked. The packet contains the required proofs
and no dependency on conference notebooks, feedback, untracked helpers,
or process history. Its Lean-handoff paragraph accurately distinguishes the
new ordinary mathematics from the existing semantic consumers. No Lean
build, Lean verification of the new producer, self-export, or broader
arbitrary-game conclusion is claimed by this verdict.

## Section 45 H1–H12: independent complete-class falsification PASS

I independently read the entire H1–H12 candidate in the author's frozen
notebook, SHA256
`6a32c34b7c6d4da99abc197598d06dc386755f9e5420e6ee963d966122020220`.
No counterpart verdict was read. I tried to break the algebra at quiet,
partly-sure, all-sure and interior roots; the common box and actual
uniform-payoff consumer; and the value claim over complete selections.
Verdict: **PASS for the stated raw Fin4 class**, as ordinary mathematics
composed with the named checked semantic consumer. There is no unresolved
objection. The raw UPPER-or-CHARGE adapter itself is not yet Lean-checked.

### Universal root argument, not just the fixture

For a full exact root, positive own Quit mass implies W_i=Q_i and
Q_i≥C_i. Positive Continue mass additionally implies Q_i=C_i. These
supported identities follow from both endpoint inequalities and
W_i=q_i Q_i+(1−q_i)C_i. Quiet-player inequalities are not asserted to
follow from supported ones: the proof only uses necessary conditions of
every full Nash root, which is sufficient for its universal exclusion.

UPPER averages the inserted premium over the FULL product coalition
law. It is correct that summing over coordinate i leaves the opponent
law, even if q_i is zero or one. Extending the weights by zero outside
the support discards no positive-mass coalition, since quiet players
never belong to one. Vanishing weights on some active players cause
no problem: if ALL supported Q_i>s_i, the nonnegative weighted sum is
strictly positive because its total weight is positive. The owner
returned need not be the same for different roots. No odds, source
floors, actual tail, or cap attainment enters this branch.

For a nontrap nonempty support, the negated trap quantifiers give one
active owner whose EVERY containing subcoalition reward is at most its
own singleton. Its forced-Quit average is therefore low, including
singleton and sure-singleton supports. Empty support is correctly
excluded from the absorbing-root assertion.

For CHARGE, I rederived the full-cube identity (H6) before division.
With at least one sure hazard and at least one nonsure active owner i,
the full all-Continue mass is zero while A∖{i} has positive mass and
strictly negative leave coefficient. Every other proper leave term is
nonpositive. This contradicts the nonnegative supported left side.
At the all-sure point both sides of (H6) vanish, so the separate
withdrawal comparison is essential and valid: r_i(A∖{i})>r_i(A) for
each i. Since |A|≥3, that opponent coalition is nonempty. Thus the
interior odds passage loses no boundary root.

For each supported owner, division by its own positive opponent-Continue
mass converts Q_i−s_i into a coalition odds polynomial. Summing gives
exactly P_A(T), not an incorrectly shared denominator. Therefore all
positive supported premiums force E>(d/τ)U. The symmetric bound
E≤U^(m−1)/m^(m−2) is correct for m=3,4. Its extremal proof includes
boundary vectors: a positive maximum must have at least m−1 positive
coordinates, so unequal positive/zero coordinates have a strictly
positive e_(m−3) coefficient and can be equalized. Interior Nash makes
the left side of (H6) zero. The resulting source charge is strictly
above C_A, whereas |v_i|≤B bounds it by ∑_A s_i+|A|B. This is the
claimed contradiction; no omitted quiet inequality is used as a
surrogate for a full Nash condition.

The finitely many strict selected charge margins admit ONE B>M, B<M+2.
Zero charge supports and M=0 cause no exceptional case. Every boxed
source strictly below some own singleton has a finite exact root by
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`. Such a root is
not all Continue, since quitting alone strictly improves for that owner.
The universal absorbing-root conclusion then supplies the selected
singleton-sublevel return. It does not need a continuous root selector,
a uniform positive absorption estimate, or a realized continuation law.

### Literal semantic consumer

I directly inspected
`HasBoxedSelectedSingletonSublevelReturn` in
`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`
and
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in
`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`.
The actual inputs match H7: nonnegative own singletons, every coordinate
bounded by M, M<B, B≤quittingRewardBound+2, and selected return for every
boxed source strictly below one own singleton. The return predicate
requires successor ≤own singleton, not an unproved strict return or
an extra cap annotation. The output is the original game's fixed
`IsUniformEquilibriumPayoff none`, not merely terminal Nash verification.
The canonical sum bound in `UniformEquilibrium/Quitting/RewardBound.lean`
is at least the maximum absolute coordinate, so the box-size premise
follows exactly. The proof's abstract continuation annotations are
legitimate inputs to this consumer; no actual-tail realization is
needed to prove its raw return hypothesis.

I also inspected the exact support-local
`QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`,
the full structure in `Classification/BoxedQuittingNashCharges.lean`,
and `quittingWeightedQuitPremium_eq_fullCoalitionAverage` in
`Classification/WeightedQuittingTrapLeavers.lean`. These match the two
identities used by the adapter. A charge theorem for one supplied
support does not require charge certificates for every other support.

### Complete fixture and selection audit

An independent exact rational computation from the sixty entries found
exactly the five traps {012,013,023,123,0123}. It recomputed all sixteen
inserted full-support coefficients, every singleton and pair charge
coefficient on all four triples, the positive Gamma simplex witness,
all 24 simultaneous labelings, and strict escape from all fifteen pure
coalitions. All reported values agree. At the literal stationary hazards
ε(2,1,5,1)/9 with ε=1/10000, the FOUR terminal premium numerators are
strictly positive exact fractions. Thus the actual-payoff strict-deficit
predicate fails, not just an ambient necessary screen.

The relevant entire raw selection sets, not just chosen weights, fail
as stated. A sure triple defeats ProductLow. The positive middle-layer
full-support P_I(T)=6 defeats EVERY boxed charge coefficient choice.
The participant-only supportwise balance fails at a triple containing
any positive weighted owner. All protected sets are empty because every
grand participant reward is −200<1; so every support-specific protected
leaver selection fails. Every positive trap weight has negative GLOBAL
inserted premium at the grand coalition, defeating the weighted lower
floor even in its weak leave version. The premium core is four, ruling
out the compared core-cardinality-three/two consumers.

The deadlock rational completion's baseline is fixed by singleton
diagonals; its required entire pair {1,3} equals that baseline and the
fixture fails it. All four off-diagonal row multisets of Gamma are
distinct, so any simultaneous automorphism is identity; enumeration
agrees. Hence no allowed relabeling repairs that completion equality.
Distinct row multisets also prevent a circulant singleton matrix at
every labeling, ruling out the compared cyclic open-sign producer.
The arbitrary-completion deadlock results inspected are positive gap
bounds, not uniform-equilibrium producers for this fixture.

These comparisons are correctly LIMITED to the named relevant raw
producers; no total census of every possible supplied periodic/root
certificate is claimed. The mixed class intentionally produces the
already checked general selected-return predicate, but not through the
globally failed charge raw predicate. This is a real reward-class
adapter with a fixture beyond the compared completed selections, not
a new supplied strategic interface or full arbitrary-game theorem.

## Final mixed-support packet: byte-bound supplement and assembly PASS

I read the complete standalone
[MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md](../exports/MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md),
at SHA256
`1f342e9ee028c79f37d8b95868fa659aa628e0a65670316a7295716775fbc2f3`.
This includes the final literal live-stage-zero wording, not the earlier
opening semantics. I independently checked the substantive supplements,
without reading another review. Verdict: **PASS on these exact bytes**,
with no unresolved mathematical, agency or semantic objection. This is
ordinary mathematics plus the named existing semantic consumer, not
Lean verification of the raw adapter or fixture.

The standalone retains the complete general support argument reviewed
above. Every trap has its selected certificate, both root boundaries
are retained, and ONE box is selected before continuation annotations.
The actual source chain through
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
still supplies one original fixed target against all behavioral
deviations. All required definitions and proofs are inline or exact
tracked declaration references. There is no conference-file dependency,
missing realized-tail premise, speculative seal, or unused correlation.

### Full sixty-coordinate neighborhood

The radius 1/100 argument is valid for independently changing ALL
sixty entries, including singleton baselines. A pair remains nontrap
because at least one member retains its −200 reward strictly below its
own near-one baseline; the other participant's equality may break
without creating a pair trap. Every triple retains positive premium,
so the five-trap census persists. Full inserted coefficients change
by at most 8η, with original largest nonempty value −192. Empty H is
identically zero. Triple singleton P,L move by at most 4η and
penultimate P,L by at most 2η. The slack parameters
(200,4,197,1/2) meet every coefficient range and give C₃=33300.
The single box B=201 satisfies M<B and B<M+2 for every table in the
ball, as well as all triple charge inequalities. This is a genuine
full-coordinate open UE chamber, not a singleton equality stratum.

### True punishment and every sure-coordinate root

At r*, Never guarantees ≥−4 under all opponent laws; opponents all
quitting in I∖{i} at zero restrict i's payoff to −4 by Continue or
−200 by joining. Hence the actual punishment value is exactly −4.
It is not a nominal floor. All-v no-sure exclusion is also correct:
with at least three sure players, one sure owner's gap is
−1−195p<0; with two sure players, one pair member has four strictly
negative convex coefficients; with exactly one sure z, its two
nonfavorite opponents have uniformly negative gaps and must be quiet,
while its favorite's positive gap forces it sure and reaches the
already excluded case. These comparisons do not depend on v. Every
strict sign persists under the stated 2η coefficient error, proving
the neighborhood no-sure statement as well.

I inspected
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`,
and the singleton adapter/floor equivalence in
`PersistentBaseConcreteGap.lean`. For base size at least two, accepted
induced Nash PLUS base-leave PLUS outsider-join supplies a full exact
sure-coordinate root. For singleton base, the owner-floor condition
gives the owner's Continue comparison at true punishment; all other
players' endpoint comparisons are annotation independent since that
owner is sure. Thus the accepted data are excluded. The induced Nash
set alone is correctly NOT claimed empty. The explicit punishment-
vector root predicate in
`Classification/InstantPunishmentSureQuitterCharacterization.lean`
is also excluded by the stronger all-v statement.

### Complete degree census and universal child scope

Independent exact symbolic inversion recomputed all eleven principal
determinants and the full inverse-support table at a=(1,2,3,5).
Only support 023 is admissible, with z=(3,8,3), outside slack3 and
determinant5. One-point homogeneous support fails a negative entry in
its column, and every larger support is nonsingular. I read the exact
inputs and determinant-sign output of
`r0Degree_eq_sum_admissible_inverse_supports` in
`MathUE/LinearProgramming/FiniteSupportDegree.lean`, and the actual
`isStandardQ_of_r0Degree_ne_zero` in `R0Degree.lean`. The supplied
zero diagonal, positive anchor, negative columns, every nonsingular
large principal and strict inactive slack suffice. Degree1 and
StandardQ follow with the stated sign convention. No matrix fixture
Lean-checking or grid argument is inferred.

The quiet-child countertest is exact for every proper child: the
favorite map is a four-cycle, so a proper nonempty child cuts an edge
z→k. Sole sure z is terminal child Nash because every other child
player's join is unfavorable, withdrawal gives zero, and later
responses cannot change date-zero absorption. All child debts and
joint Never mass are zero; the cut outsider has actual join gain1.
I checked the universal bound produced by
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`Classification/QuietExtension/WithdrawalFutureJoinDebt.lean` from the
raw `WithdrawalFutureJoinRewardCertificate`. Restriction to S∪{k}
and relabeling k as none preserve this exact countertest. Thus every
universal certificate for that cut transport fails. Another selected
safe child might still exist: the packet's existential caveat is
essential, present, and not contradicted by its final scope paragraph.

The value claim remains a new raw assembly and open chamber beyond
the named complete selections, not an exhaustive producer census or
an arbitrary-game UE result. The supplements introduce no unresolved
change to that scope. No packet was edited or self-exported by this
review.

## Focused independent Section 49 DR1–DR8 proof and value check

Reviewer: CODEX_BROUWER. Verdict: PASS for the stated fresh-table
all-minimum debt-rigidity and supported-cap source restriction.
This is ordinary mathematical review, not Lean certification or
a full UE consumer. The author's packet and exports were not edited.

### Exact claim checked

Starting from the canonical positive unit-cube table with all 82
raw spectrum labels separated from its TRUE SUM minimum, arbitrarily
small POSITIVE recipient scalings produce one fresh positive table
retaining every separation and having ONE common debt vector for
EVERY global carrier minimum. At every all-unique produced minimum,
EVERY earliest-cap owner has zero own mass there, and some later-cap
owner also has zero own mass at its cap. If ALL unique cap points
are isolated, EVERY supported cap owner is pure at its cap and
has zero debt. Multiple-cap minima remain unconsumed.

### Independent attacks on scaling and complete minimum-family selection

I checked the original compact carrier and its nonnegative debt set,
the actual positive-diagonal transformation of BOTH payoff and FULL
cap, and its commutation with closure. Positive row multiplication
commutes with the supremum over all behavioral responses; no single
chosen test or stationary cap is substituted. The diagonal map is
a homeomorphism, so the scaled table's entire original carrier is
exactly the image of the old carrier. Thus its unweighted SUM
objective is exactly the old carrier's positive weighted objective
W(θ)=min_a θ·a, not the old unweighted SUM minimum or MAX debt.

W is an infimum of LINEAR functions on ONE fixed compact debt set.
It is genuinely concave and Lipschitz, unlike the retired outer
reward-table envelope. The one-dimensional concave restrictions
have unequal left/right derivatives at only countably many points;
their difference-quotient limits are measurable. Fubini and a finite
union therefore produce a coordinate-regular θ in EVERY open
positive box. At such θ, the two inequalities for t>0 and t<0
force EVERY minimizing debt vector's coordinate to equal ∂_iW.
This checks the ALL-minimizers quantifier without any unique law,
selected response, Danskin or profile-mixing premise.

The scale bounds preserve positivity using nonnegative debt at all
carrier points. The finite label family has coefficient absolute
sum at most six (the longest common join sum has three differences).
Its change≤6ρ and actual global SUM change≤8ρ leave separation
≥ζ−14ρ>0. Canonical source identities need true positive SUM
minimality and label exclusions, not continued worst-table optimality.
Thus all of them apply to freshly selected minima of the NEW table.

### Signed source and all-response stability

For an earliest supported owner, the retained positive OWN atom
allows BOTH signs of (1−u)q_h+uδ_τ with bounded nonnegative old
chart densities. Its original finite atom witnesses and complete
moving-reply convergence give actual carrier membership, not just
branch payoff convergence. Never and c⁺ are retained; c⁺ continues
to duplicate zero-mass c.

Earliest common-date selectors are isolated and have compact
complement gaps. Every later selector, including a nonisolated point
or Never, has its ENTIRE upper family transformed by one positive
affine map; a compact lower gap completes full-cap stability. Hence
the actual SUM is affine with an interior global minimum, giving
a nearby family of actual global minima. Debt rigidity then forces
the changed owner's debt (1−u)d_h to be unchanged, so d_h=0.
Unique FULL cap attainment forces its prescribed law to be pure
at that point. Prescribed clocks lie in the marked test set almost
surely by the canonical producer, so no positive-law mass is omitted
from the regret integral. A pure earliest owner screens every later
selector, making it tie c/Never; common-date uniqueness is excluded
by the preserved finite join labels. This proves the strong EVERY
earliest-owner statement even when other later caps are nonisolated.

For an arbitrary later supported reset, DR6 honestly adds isolation
of ALL other cap points; their uniform gaps replace the chronological
upper-family argument. The same rigidity implies purity. If every
later owner were supported, those caps would automatically be isolated;
all later owners would then be pure at later dates, while every
earliest owner has zero mass at the earliest point. This contradicts
the positive earliest mixture atom. The later-unsupported conclusion
does not infer support or isolation from uniqueness alone.

### Boundary tests, exact tracked overlap and strategic value

The abstract W=min_i θ_i test correctly shows the need for regular
weights; it is not claimed realizable as a positive-gap quitting
table. The two-player game with own1, passive2, joint0 has genuine
zero-debt singleton minima with different payoff/cap vectors. At
half-zero/half-Never independent play U_i=3/4, date-zero payoff1/2,
Never payoff1 and EVERY later finite payoff3/2, so full debt SUM3/2.
This exact test validates the distinction between debt rigidity and
behaviorally implementing a convex mixture of minimizing pairs.

I inspected the source statements in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`.
`minimumTerminalSemantic_weightedSingletonMargin` takes a SUPPLIED
positive weighted minimizer and strictly POSITIVE weights; the
preceding auxiliary budget permits nonnegative weights. Neither
selects coordinate-regular weights
or force one debt vector for ALL minima. The exact minimum-chord
debt affinity in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticMinimumResponseChord.lean`
likewise needs two already supplied same-minimum endpoints; it does
not provide this scale producer. This was a narrow source check,
not an entire producer census.

The strategic increment beyond the frozen 920-line artifact is real:
its all-unique arm required at least ONE zero-own-mass earliest owner
and at least two unsupported owners somewhere. DR5 excludes mixed
supported/unsupported EARLIEST groups at EVERY fresh minimum; DR6
also puts an unsupported owner LATER and, when every cap is isolated,
forces supported owners' literal purity/zero debt. These are new
pointwise restrictions, not an existential reselection to equivalent
plateau points or an automatically consumed rank. The proof still
does not consume the all-unsupported or multiple-cap arm and does
not assert UE. No substantive unresolved objection was found.

## Independent focused falsification of Section 50 / SA1–SA11

Reviewer: CODEX_BROUWER. Ordinary mathematics and static declaration
inspection, no Lean build. Reviewed the complete held section headed
“One fresh table has random outcomes and no prescribed pre-active head”,
section-to-EOF SHA256
`751097321e6ec2cbdca761ec94a55a4275be3a99800e26a760d9bf86844e4773`.
No NOETHER verdict/reasoning was read before this independent check.
Earlier participation in the MH head argument and DR review is disclosed;
the sign-adaptive typed comparison and literal one-member release were
checked independently here rather than certified by that participation.

Verdict: mathematical PASS for the exact source restriction and its
same-table compatibility. No unresolved mathematical objection found.
This is not an equilibrium producer, new Lean certification, or a
positive-debt rank theorem. Standalone assembly must inline the actual
source/DR/HR proofs rather than depend on conference notes.

### Exact claim and source quantifiers

If some signed Fin4 game has no uniform payoff, ONE fresh unit-cube
table can be selected with positive literal unweighted SUM infimum,
all-minimum debt rigidity, all82 canonical gaps and at most11 typed
mixed-debt gaps. At EVERY new produced marked minimum, prescribed
outcome is nondeterministic, no owner stops before the earliest FULL
active response, and that response is the first prescribed stage,
a positive isolated mixture atom with at least two own suppliers.
The earlier separately proved HR restriction is applicable at THAT
same table, not at an old minimizing source.

### Sign-adaptive target and all labelled contacts

The target covers every coordinate exactly once:4 own singles,
12 passive-singleton/participant-pair pairs,12 passive-pair/participant-
triple pairs,4 omitted-triple/grand pairs. For each lower join,
old positive gets endpoint2; old negative OR zero gets−1/2.
Hence member withdrawal old≥0 becomes NEW positive1/2, whereas
old negative becomes NEW negative−2. Grand withdrawals old≥0
become positive1, old negative become−1. Triple outsider joins are
the corresponding negative grand withdrawals. Thus every fixed
old typed cohort E_A,Z_A indeed agrees with the full NEW strictly
positive-debt census, including zero-born positive withdrawals
and zero-born negative joins.

For the original82 contacts: singleton C sums target≥1 whenever
their old sum is positive; pair C target≥3/2; positive triple C
and individual grand-reversal joins target1; individual lower joins
target2; F/G target1 or2; positive a target1. Mixed eligible pair,
triple and grand targets are respectively
|E|/2+2|Z|, |E|/2+|Z|, |E|, all≥1 under the stated eligibility.
Every individual actual-debt sum label has coefficient absolute
sum≤8. No incompatible endpoint sign, label omitted from the
stated classification, or hidden coordinate overwrite was found.

The positive old-contact comparison uses Ω<1 (the recorded4/5
bound suffices), not a stronger unproduced margin. Uniform reward
coupling gives the literal SUM Lipschitz modulus8. The old upper/
lower noncontact inequalities use16α and32α correctly; α≤σ/64
makes the separation strict. The value comparison is over ALL
new laws and caps, with no selected-current-minimizer Danskin step,
MAX/SUM transfer or independent profile mixing.

### Deterministic pair equality and the actual release

For a deterministic nonempty coalition A of size≥2, independence
and equality of bounded clock coordinates almost surely force every
member pure at one common finite time. Outsiders are strictly later.
A member's only possible cap values are own solo (when earlier
clocks exist), r_i(A), r_i(A∖{i}); an outsider's are own solo,
r_z(A), r_z(A∪{z}). The true cap-minus-singleton margin excludes
the own solo maximum. Hence exactly the displayed positive-part
withdrawal/join debts occur.

The literal date0 pure-A/outside-Never profile has the SAME full
semantic pair, not merely the same expected payoff. Therefore its
debt is the TRUE minimum and the one-sided original-calendar release
is authorized. For exactly one positive member debt and no outsider
debt, strict signs make every other member root strictly best and
every outsider wait strictly best. The4Mρ bounds control ALL finite
deadlines and Never, including the pair's new singleton-or-Never
branch. Another member remains sure at0, so every outsider's late/
Never payoff is exactly its prescribed passive mixture. Mover i's
full cap is independent of its own law and its debt becomes
(1−ρ)δ; all other debts remain0. The strict decrease is literal,
with no unsupported negative old-chart reset or assumed child Nash.

Singleton/Never deterministic outcomes are separately excluded by
the actual all-owner payoff margin. Every nonsingleton case either
hits an INCLUDED mixed-debt label, has debt0, or is this one-member
release. The classification is exhaustive.

### Full active heads and the first collision

The old conditional factors are legal for both parameter signs and
the cut pullbacks use retained RIGHT endpoints / whole dates, not
raw midpoint limits. Bounded-density weak-* plus moving kernel
transport supplies ALL full caps. Every upper test has the SAME
positive affine map and the lower compact set contains no old
maximizer, so even accumulating full active sets are stable. First
SUM constancy gives actual minima; only THEN all-minimum rigidity
gives individual polynomial identities. Far endpoints are selected
regrets, not asserted actual caps.

At a nonempty head cut the singleton cohort yields ORIGINAL
U_h=s_h, impossible by the all-owner quadratic payoff margin.
With≥2 head owners, each positive pre-active debt forces its
ORIGINAL head probability1. Every nonhead has selected endpoint
regret0 and hence ORIGINAL debt0, so cannot have pre-active mass.
This justifies B=P at EACH cut, strengthening the essential-endpoint
descent. At an isolated lower endpoint one whole-date event suffices;
at a nonisolated endpoint regular whole-atom cuts decrease to it.
The conclusion is a deterministic ORIGINAL coalition, consumed by
the preceding literal classification.

For a sole supplier at the first atom, the executable original
conditional suffix has positive normalizers. Its compact carrier
pair is not assumed minimal or Nash. The h cap is max(s_h,b_h);
others' caps are at least q·passive+(1−q)b_j. The exact debt
inequality δ≥(1−q)D_tail+q(B_h−s_h), together with D_tail≥δ and
the strict quadratic cap margin, is contradictory. There is no
unproduced tail or incorrect equality for the other full caps.

The narrow checked input inspected is
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`,
under its actual imports: original carrier membership, global SUM
minimality, card4, positive M, coordinate reward bound and δ>0.
It supplies BOTH strict margins used here, not a Nash row of the
original first stage. Nearby cap-Nash prefix identities in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` require
actual suffix-cap Nash roots and are not being silently substituted.

### Compatibility with BG row genericity at ONE final table

The Section50 proof is compatible with BG1–BG6 without importing
a second minimizing table. Insert the extra generic selection AFTER
the positive convex step, BEFORE DR scales. Let γ be the93-gap
minimum and κ the minimum nonzero lower-join/grand-withdrawal
magnitude. Common positive contraction makes all reward entries
interior, scaling Δ, every fixed contact and κ together. Next
perturb generically by β inside that open cube with

    8β<positive-gap margin,
    16β<contracted γ,
    2β<contracted κ.

Finite row-equality hyperplanes have dense complement. All93
labels retain their gaps and ALL typed signs retain their original
cohorts. Finally select coordinate-regular positive DR scales
arbitrarily close to1 on THIS new fixed carrier. They preserve row
inequalities and typed signs and keep all93 contact gaps. Every
later minimum is then selected AFTER fixing this one generic rigid
table. HR needs only its canonical82 gaps, rigidity, actual source
and SAME-table normality, so all its conditions also persist.

Combining this production with the independently checked BG
argument gives an earliest root-to-later active PAYOFF-kernel
bridge at EVERY produced minimum, not just some pair of test
labels. On a positive opponent-root event one reply joins S while
the later reply sees S; same-row distinct entries make the actual
payoff kernels different. This is a genuine stricter source class
than the frozen HR multiple-point conclusion. The bridging owner
may have ZERO debt; the bridge is still NOT a paid edge, a rank
drop, or an actual full-conjecture consumer.

## Focused full BA1–BA10 falsification: absorbing carrier and terminal-row penalty

Reviewer: CODEX_BROUWER. Ordinary mathematical PASS for the precise
source producer below, not a Lean check, whole-artifact export gate,
or a Fin4 UE consumer. I read all484 lines from the heading
“Forward global attempt: an absorbing carrier and a terminal-row penalty”
up to Section50, with section SHA256
b3729a8482a429a2035e66ca2d11bf3d55a92b91042a8ea25d1040a041c4ae59.
No counterpart review verdict was used. I disclose my contribution
to the earlier SA/BG/calendar source; this check does not re-certify
those inherited proofs merely because I contributed to them. It
independently checks BA's new domain, penalty, same-table production,
and the legality of EACH imported source operation on that domain.

### Exact claim and its nonclaims

Starting from ANY Fin4 counterexample, for every positive ε select
ONE bounded positive-singleton, row-generic, contact-separated table
BEFORE ALL minimizing families. On that SAME table both complete
carriers have positive SUM gaps δ_all≤δ_abs, independent all-minimum
debt vectors a and b, and relative closeness

    δ_abs−δ_all<ε δ_abs,
    max_i|a_i−b_i|<ε δ_abs.

The first carrier closes ALL independent complete laws; the second
closes ALL such laws with joint Never probability0, equivalently
the union of the four classes having some own Never mass0. Every
produced minimum in EACH class has the canonical random earliest
collision and genuine root/later kernel bridge. Every absorbing
source additionally retains some zero-Never anchor, including
literal finite-a.s. original realizing laws.

The claim does NOT put that anchor at an ORIGINAL full minimum,
give equality of the gaps/vectors, make the anchor a positive debtor
or root-sure owner, supply a tail Nash, or preserve arbitrary
non-sure-root grafts from the full carrier. Those distinctions are
indispensable and stated correctly in the draft.

### The exact full-cap penalty survives all reply modes

For s_m≥0 the OLD full cap is already its finite-deadline supremum:
finite replies tending later approach the Never payoff plus
opponent-Never-product times s_m. Adding C≥0 to EVERY finite
terminal reward in that RECIPIENT row adds C to every finite
response value; Never increases only by C times opponent absorption
probability and remains below that new finite sup. Thus

    B_m^C=B_m+C,
    U_m^C=U_m+C(1−c),
    d_m^C=d_m+Cc,

with all other debts unchanged. This is exact for arbitrarily late
finite responses and unattained suprema, not a fixed-tester envelope.
At s_m=0 the identity still holds; positivity is needed for the
later equivalence/control. On the absorbing class it is an affine
translation of the whole pair, so its debt SET really is unchanged.

The late-original-Never replacement proves d_m≥s_m c without
changing any original finite mass. This is exactly the required
same-table control. The negative-solo boundary test in BA9 correctly
refutes the row-shift identity without s_m≥0: the old cap may be
Never rather than the finite sup.

### Actual absorbing approximation and every moving minimizer

The product-zero condition is equivalent to at least ONE factor0.
For arbitrary positive s_m and debt d, select the smallest current
Never factor η≤(d/s_m)^(1/4), move it to ONE finite date, and leave
other laws fixed. This is an actual independent absorbing law.
Four payoff errors cost at most8Mη; the moved owner's cap is
unchanged and the other three full caps cost at most6Mη. Hence the
14Mη debt comparison is uniform over ALL finite/Never replies.
It proves zero-gap completeness, not positive-gap equality.

For the large-C objective, absorbing competitors give the bound d.
EVERY moving o(1)-minimizer satisfies c≤(d+o(1))/C. Applying the
coupling with the OLD reward bound makes its old pair approach the
absorbing carrier; hence its old debt is≥d−o(1). The objective upper
bound then forces both old debt→d AND Cc→0. The latter conclusion
is stronger than c→0 and was correctly derived, not assumed.
For closed-carrier minima, actual new-table approximants can be
chosen with vanishing NEW objective error, while the old pair and
c remain bounded and admit a simultaneous lift. This supplies the
same conclusion for every moving carrier minimum.

The square-root graph test correctly exposes why no FINITE C
guarantees c=0. It is honestly abstract optimization evidence,
not a realized quitting counterexample.

### Prefix floor, signed variations, strong margins and anchor seam

K_abs is compact and finite-prefix invariant. In actual realizing
sequences a fixed zero-Never owner can be retained by subsequence.
Its own late finite truncation goes to a NEW FINITE deadline, not
Never; the resulting TV error tends to0 and the entire cap menu
converges uniformly. Other owners may be truncated to Never.
The retained Never coordinate stays0 through compactification;
finite calendar endpoint mass is not identified with literal Never.
This proves an actual original-sequence anchor, not attainment by
one natural-calendar law of every abstract minimum pair.

All SA/BG variations either redistribute retained supported atoms
or condition on OLD positive head/tail submeasures. They introduce
no new Never mass into an anchor. Negative parameters multiply
existing submeasures by bounded nonnegative factors on their legal
small box, so anchor0 remains EXACTLY0 in every original witness.
The full moving-tester transport and Never/c distinction therefore
remain applicable, with the correct δ_abs floor.

The sole-supplier non-sure source has all own continuation
normalizers bounded away from0, so the original conditional suffix
retains the fixed anchor and belongs to K_abs. The deterministic
nonsingleton release leaves another sure member and hence absorbs.
Every auxiliary Nash/solo-threshold margin comparison uses only
finite prefixes and compact limits in this carrier. I checked the
ordinary proof against the actual threshold and auxiliary-budget
declarations: original full-carrier minimality is NOT silently
imported as a checked theorem for K_abs. Reconstructing the proof
gives the displayed quadratic margins with δ_abs. The singleton
column blockers are available because positive s_m and Δ_abs>0
imply no UE at THIS same table.

The expressly lost operation is real: a non-sure prefix of an
arbitrary full-carrier tail need not lie in K_abs. No imported
SA/BG step requires it. A sure absorbing prefix permits arbitrary
actual tails and preserves absorption.

### One final table and all93 contacts

Maximizing Δ_abs on the unit-cube fiber s_m≥a>0 is legitimate:
its domain is fixed, the infimum is8-Lipschitz and the table fiber
is compact. The weak prefix margin gives Ω_abs≤1−a<1 without
using AllNever as an absorbing competitor. The sign-adaptive
endpoint has own singletons1 and stays inside that fiber. Every
old contact targets at least1, while the worst-fiber comparison
keeps the new gap≤Ω_abs. Finite noncontact separations, subsequent
interior genericization and regular recipient scaling are therefore
compatible exactly as asserted.

Recipient-m translation leaves ALL within-row differences unchanged.
The listed93 family uses nonempty withdrawal coalitions and
nonempty join bases; the only empty passive-floor coordinate is
F_(m,∅)=s_m and it diverges under the translation. Thus the same
finite gaps separate BOTH objectives for sufficiently large C.

Positive regular weights can be chosen jointly for BOTH fixed
concave scalarizations, since the union of their exceptional sets
is null. The weighted full objective is exactly
Σθ_i d_i^A+θ_m Cc. Its old debts are bounded; its penalty is bounded;
θ→1 and old-reward absorbing coupling again force old debt→d
and Cc→0. Therefore EVERY new full minimizing debt vector tends
to the rigid OLD absorbing vector. The weighted absorbing vectors
also tend to that vector. One sufficiently large FINITE choice
gives the claimed relative estimates, which survive common
normalization. No normality, SUM/MAX, old-minimum or exact-contact
transfer is inferred from mere convergence.

### Exact arithmetic and value audit

I independently enumerated the BA9 half-root fixture's complete
root/later-finite/Never values. Old debts in denominator32 are
(14,19,19,28); after adding7 to row3 they are(14,19,19,42).
Row3's old menu is(28,−24,−28)/32 and new menu
(252,200,168)/32. Their total difference14/32 is exactly7/16=7c.
The negative-participant whole table has Δ_abs=1 and Δ_all=0
as claimed, so the positive-singleton hypothesis is load-bearing.

Named source declarations inspected under their imports:
quittingTerminalPayoff_playerwiseAffine,
quittingTerminalPayoff_finiteTime_playerwiseAffine and
quittingFinitePureReplyValue_playerwiseAffine in
UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean;
quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg
in UniformEquilibrium/Quitting/Punishment/FinitePureReplyValue.lean;
minimumTerminalSemantic_auxiliaryNash_budget and
minimumTerminalSemantic_singletonMargin in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean;
positive_minimum_preemptedOwner_quadraticMargins in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean;
exists_first_solo_capThreshold_hit and the solo-iterate formulas in
UniformEquilibrium/Quitting/Root/TerminalSemanticSoloCapThreshold.lean;
exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform in
UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean.
The known finite-menu/early-absorption completeness identified in
FRONTIER/TOOLKIT is not recounted as new UE coverage.

There is a genuinely different produced COMPLETE-class source:
it retains a finite-a.s. anchor while matching the all-carrier gap
and rigid debt vector relatively closely at ONE table. This is
not merely one fixed sure-root family. Its anchor belongs only
to absorbing minima, however, and finite-C closeness does not
restore the unrestricted all-tail minimum floor. The mathematical
producer passes; whether this advantage can be consumed remains
open. No unresolved objection was found in BA1–BA10.

### Separate strict export-value verdict for BA (after mathematical PASS)

Recommendation: NOTES ONLY at the present consumer frontier. This is
a sound new supporting producer, but the current argument does not
demonstrate the significant counterexample-class narrowing required
by exports/README.md. The mathematical PASS above is not an export
admission recommendation.

The exact extra output over the canonical full-carrier source is:
at a freshly selected table there is ALSO a global minimum for the
COMPLETE absorbing class, with an original zero-Never anchor,
canonical random/head-free/bridge geometry and its own rigid debt
vector, and its gap/vector are relatively close to those of the
full minimum. Zero-gap completeness of that class is already checked.
The anchor itself is automatic from membership in P_abs; the
penalty/regularity comparison is the genuinely new simultaneous
two-objective statement.

No already-established ORIGINAL residual mode is eliminated:
all original minima may still be unanchored; every original c>0
random bridge configuration may remain. The two minimum sets need
not overlap, their debt zeros need not agree, and their caps and
prescribed laws need not be close. Closeness of two scalar gaps
and debt vectors cannot substitute for any of those exact facts.
The absorbing source has a strictly weaker non-sure-root tail floor:
it prices arbitrary absorbing tails, not arbitrary full-carrier
tails. The main quantitative consumer currently requires the latter
at a TRUE original minimum.

A concrete possible leverage is identifiable but NOT supplied:
an actual absorbing-law repair below δ_abs would contradict its
own global floor, or a nonabsorbing repair with a uniformly
quantified gain exceeding δ_abs−δ_all would contradict the full
floor. BA constructs neither repair. Its finite-a.s. anchor gives
no supported cap response, positive-debt owner, root sure clock,
paid temporal edge or legal renewal. Thus it currently changes
the domain of the open consumer rather than closing a named
surviving configuration or proving a new UE class.

The relative-error quantifier does not by itself furnish a stable
approximate version of the exact full-minimum machinery. Increasing
C increases the reward bound before normalization, and common
normalization can shrink the gap and its quadratic margins. The
square-root graph already retained in BA4 has
δ_abs−f(C)=1/(4C), while the unnormalized quadratic margin has order
δ_abs²/M_C with M_C of order C. Hence arbitrarily small RELATIVE
gap error alone does not imply error below every needed exact
margin, nor restore exact cap equalities or debt zeros. This is
a scope warning, not a request to optimize constants or an actual
quitting counterexample.

To upgrade the value verdict, a load-bearing consumer should
first use the anchored absorbing source plus its admissible-law
floor to exclude one named presently surviving source arm; or
prove an exact transfer putting a useful anchored minimum back
in the ORIGINAL carrier's minimum set. Merely packaging the
parallel source or its automatic anchor would not demonstrate
that increment. The current supporting theorem and exact
penalty limit deserve retention in the notebook without a
formalization export yet.

## Independent FC1–FC6 falsification: exact full-minimum alignment and all-finite clocks

Reviewer: CODEX_BROUWER. Complete focused ordinary-mathematical PASS.
This is separate from the BA proof/value verdict above. No other FC
review verdict was read. I read the entire frozen section and its
referenced BAP initialization; the author's confirmed scope is the
heading “Forward full-source consumer: zero debt and complete finite
clocks” up to, but not including, “Forward normal form: counterexamples
arbitrarily near one constant table”. Independent extraction matches
SHA256 d5ba4cc57104b3ccce875e435200432eeb2c7af5462d924d9340dfdb38b1541d.
No author or export file was changed and no Lean build was run.

### Exact claim checked

From any hypothetical signed Fin4 counterexample, select ONE new
positive-own-singleton unit-cube table with the canonical FULL-carrier
positive SUM minimum δ, all-minimum common debt vector a, generic
rows and genuine random first-collision bridge. If some a_k=0,
the SAME table satisfies EXACT equality of its full and absorbing
minimum-pair sets, and EVERY original minimum PAIR admits an actual
realizing sequence whose FOUR Never masses are all exactly0.
The canonical source may be produced afresh from that sequence,
retaining the ORIGINAL arbitrary-tail minimum floor. This is not
pointwise preservation of every old sequence, old root, old tail or
old clock genealogy; it is not a UE theorem.

### Source and final-table checks

BAP's initialization is legal: original noUE supplies a positive
pivot and original all-player punishment normality; reverse
single-pivot transport therefore preserves noUE. The new own vector
is e_m. Positive whole finite-row shifts on the three zero-own rows
increase actual full debt by3η·P(AllNever), rather than assuming
strategic affine equivalence with Never0. Common positive scaling
then puts a still-positive-gap all-positive-own table in the cube.

FC1's compact worst-table fiber preserves all initial strict own
floors. Its full global singleton margin gives Ω≤1−a_i<1, not
merely the old unqualified whole-cube estimate. The canonical
sign-adaptive endpoint has ALL own targets1, hence its entire
convex comparison segment remains in this fiber. The complete93
contact price uses only target≥1>Ω and the actual moving-law
Lipschitz comparison. Subsequent close inward/generic/regular
scale selections preserve positive own signs; later proof does not
reuse fiber maximality. There is one final table before all minima,
not a positive sign inherited from a different normalization.

I inspected the exact statements/imports of:

- normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
  in UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean;
- all_punishmentNormal_of_normalCore_eq_univ in
  UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean;
- isUniformEquilibriumPayoff_original_of_singlePivotNormalized in
  UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean;
- exists_core_blocker_of_mem_normalCore in
  UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean;
- normalizedSoloMatrix_eq_soloReward_sub in
  UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean;
- prod_stoppingLaw_none_mul_singleton_le_terminalDebt in
  UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean;
- quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg
  and neverPayoff_add_opponentNever_mul_solo_le_finitePureReplyValue in
  UniformEquilibrium/Quitting/Punishment/FinitePureReplyValue.lean.

The normal-core witness is genuinely a RECIPIENT-ROW witness:
M(m,j)=r_m({j})−s_m≤0, with j≠m. It is not the earlier
column preemptor, and strict inequality is not needed.

### Independent reconstruction of the clock-completion seam

For an actual absorbing profile choose one old anchor m with
p_m(Never)=0. If it is the sole anchor, choose the row witness j.
Couple all unchanged clocks and replace ONLY j's old Never branch
by independent H≥T with total finite mass1 and largest atom≤η.
For all U coordinates and all response caps except m, the old
m-clock<T screens every changed outcome. Owner j's cap is
identical, because its opponent laws are identical. This bounds
those changes uniformly over ALL deadlines and Never; it does
not merely compare one selected test.

For m's cap its own old clock is deleted, so that screen is absent.
Let E be the old all-opponent-Never cylinder, of mass c_{−m}, and
let Z be the event some OLD finite opponent clock is≥T, of
probability≤ξ_T. On Z's complement outside E, the old first
opponent coalition is beforeT and is unchanged for every m
response at/afterT. On E the new outcomes are exactly solo m,
solo j or tied {m,j}. The first two recipient rewards are
s_m and r_m({j})≤s_m; the last has probability≤η for ANY
fixed test date, including moving arbitrarily late dates.
Therefore EVERY changed late finite cap candidate is bounded by

    V_m^old(Never)+c_{−m}s_m+2Mη+4Mξ_T≤B_m^old+2Mη+4Mξ_T.

The Never response has the same upper bound with no tie term.
Finite old replies beforeT are exactly retained. Since s_m≥0,
Never is dominated by the old finite supremum; fix a finite
near-maximizer first, then takeT beyond it. This gives the reverse
limiting cap inequality without assuming a finite maximizer, a
bounded response date or a payoff gap to near-maximizers.

Afterward both m and j are fixed finite-a.s. anchors. In the second
completion stage EVERY responder has at least one of them as an
unchanged opponent, including m itself (use j). Its tail probability
screens all remaining late-Never replacements uniformly over every
response. First take the first-stage parameters, then the final
dates sufficiently late; a diagonal sequence preserves the entire
(U,B) pair. Simultaneous replacement of the remaining Never atoms
is valid: a coupling changes a kernel only when the chosen anchor
has reached those dates. No response timing restriction is used.

### Exact boundary tests used to try to break the proof

High tied rewards do not defeat the atom bound. Take m=0,j=1,
s_i=1; in row0 set r_0(S)=100 if {0,1}⊆S, and1 otherwise.
In every other recipient rowℓ set r_ℓ({ℓ})=1 and all its other
finite coordinates0. Initially p_0=pure0 and all others Never,
so U=B=(1,0,0,0). Replace only p_1's Never by a geometric clock
afterT>0 with hazardη. ALL other payoff/cap coordinates remain
unchanged, and for m's finite testt

    V_0(t)=1+99P(H=t),       B_0^new=1+99η;
    V_0(Never)=1.

Thus the entire cap converges even when the row witness is only
EQUALITY r_0({1})=s_0 and the collision reward100 is very large.
Replacing that Never atom by a PURE late date instead would give
cap100, so the nonlocal DIFFUSE step is substantive, not a TV
small-mass argument. This solved table is only a cap-seam test.

The nonnegative-own assumption is indispensable for full-pair
preservation. Take row0 identically−1 on nonempty coalitions,
every other row identically0, and the same initial anchor profile.
All row inequalities hold, but old B_0=0 at Never whereas every
finite old response pays−1. Once any old opponent Never becomes
finite a.s., EVERY response of0 pays−1, including Never. Every
all-four-finite profile has B_0=−1, so the old full pair cannot
be approached. This breaks the lower-cap seam precisely when
s_0<0, outside FC3's hypotheses.

FC6's supplied positive-own countertest is also exact: passive10,
own1, participant nonsingletons0. At any four-finite profile,
all four Never responses pay10 and all possible terminal coalition
total rewards are at most31. Hence D≥9; distinct deterministic
dates have ALL caps10 and total prescribed payoff31, attaining9.
The pure-singleton/Never profile is unrestricted Nash withD0.
The entire proper-law class fails only because EVERY row witness
r_m({j})≤s_m is absent. Neither positive own signs alone nor one
absorbing anchor suffices without FC2.

### Minimum alignment and closure quantifiers

At any original minimum pair the common zero coordinate a_k=0
and s_k>0 force the realizing actual joint-Never products→0.
The smallest of four marginal Never masses is at most their
product to the power1/4, hence→0. Moving only that small mass
to a finite date changes ALL U/B coordinates by a vanishing
uniform TV bound and produces an actual absorbing sequence.
Thus EVERY full minimum belongs to K_abs. Inclusion in the
other direction and equality of gaps give EXACT equality of
minimum sets, not only δ_abs=δ_all.

FC3 applies to EVERY actual absorbing pair, not just its minimum.
Its diagonal closure argument therefore establishes the WHOLE
identity K_fin=K_abs. Combining these two facts reaches every
original minimum pair by actual all-four-finite profiles. Original
Never masses remain literally0 under the marked extraction, but
finite dates can escape to the finite compact-calendar endpoint.
Consequently this is NOT two proper limits on the original RAW
integer calendar and does not feed a raw-tightness realization
theorem. All response menus must still include literal Never and
the finite endpoint; FC explicitly retains both.

### Separate strict export-value verdict

This is a genuine incremental counterexample-source restriction,
unlike BA's merely close companion minimum. I recommend advancing
it to standalone artifact preparation, subject to the normal
independent final-artifact gate; this focused PASS does not itself
authorize an export.

The new condition is precise: on ONE selected canonical positive
table, either all common debts are positive, or EVERY original
minimum pair lies in the closure of the complete all-four-finite
class and can be reconstructed with that class's original law
agency and FULL arbitrary-K_all floor. The automatic anchor of a
restricted-domain minimum is not being counted as the increment.
The increment is EXACT original-minimum membership plus ENTIRE
pair preservation, and the all-four-finite completion controlled
by actual same-table row witnesses.

The narrower tracked finite-early-absorption results were inspected:
finiteMenuFullEarlyAbsorption_of_terminalProfiles_liveMassZero in
UniformEquilibrium/Quitting/Terminal/TerminalProfileFiniteEarlyAbsorption.lean
starts with arbitrarily LOW full exploitability and delivers a
finite-menu/early-absorption construction. It does not identify
whole carriers or positive-minimum pair sets. The nearby exact
finite-deadline cap theorem in
UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean
accounts for a late row but likewise does not supply FC3's
row-witness diffuse completion. A bounded lookup found no duplicate
whole-pair identity; no global codebase novelty claim is intended.

Concrete possible leverage is now honestly available: a construction
using all-four-zero-Never clocks can start at a TRUE unrestricted
minimum in the zero-debt arm and compare ANY actual tail, without
BA's unknown gap error. The proof does not supply that repair,
control escaping finite clocks, make a bridger paid, produce a
tail Nash or close UE. These residuals must remain explicit in a
final packet. No unresolved mathematical objection was found.

## Whole-artifact FC assembly and falsification: four finite clocks at original minima

Reviewer: CODEX_BROUWER. Artifact checked in full:
`exports/FOUR_FINITE_CLOCKS_AT_ORIGINAL_MINIMA.md`,
1787 lines, SHA256
`0452b5cdebd2cc3186634b98df67ea841c15cba1794e8749931199bfb4c3766b`.
The review was performed on the identical source draft preserved at
commit `2dbc0cf8`; the canonical target above carries the same bytes.
The hash was verified again after the complete reading. The artifact was
not edited. I contributed the earlier BG source material and authored the
earlier canonical source assembly; this verdict does not substitute for
independent certification of those contributions. I independently checked
the newly assembled positive-own initialization, whole-carrier finite-clock
completion, minimum-set alignment, and fresh-source regeneration, and
reconstructed their interface with the entire supplied source proof.

Verdict: ordinary mathematical PASS, with no unresolved mathematical or
named-source objection. This is not a Lean seal or export authorization.

### Exact claim checked

For any signed Fin4 table with nonnegative own singletons and an actual
recipient-row witness r_m({j})≤s_m for every m and some j≠m, the ENTIRE
payoff/full-cap closures satisfy K_fin=K_abs. At ONE freshly selected
positive-own counterexample table, all original minima have a common debt
vector. If any coordinate is zero, EVERY original minimum pair belongs
to K_fin and the three entire minimum-pair sets are exactly equal, at
the original full gap. New all-four-finite realizing sequences regenerate
the canonical random first-collision and different-payoff root/later bridge.
The all-positive debt alternative is retained, not eliminated.

### Table production and strategic-input audit

The initial positive pivot is forced because otherwise AllNever has zero
debt. The reverse single-pivot payoff transport uses actual original
punishment normality, obtained from the full-core counterexample theorem;
it is not affine invariance of old prescribed laws. The three zero-own
rows are then raised using F3, whose exact all-profile debt increment is
3η times joint Never mass. This produces positive own floors before the
compact worst-fiber selection. Section7's Ω<1 follows from the true
all-owner margin and the cube cap bound. Its endpoint owns are all1,
so the endpoint segment remains in that fiber. Contraction, genericity
and regular recipient scales occur afterwards, preserve positive own
signs and all93 contact gaps, and do not reuse old fiber maximality.

The final row witnesses are produced AGAIN from final-table positive
full gap and actual full normal core. I checked the exact declarations
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff in
UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean,
all_punishmentNormal_of_normalCore_eq_univ in
UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean,
exists_core_blocker_of_mem_normalCore in
UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean,
and normalizedSoloMatrix_eq_soloReward_sub in
UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean.
The last identity has recipient m in the matrix ROW and quitter j in
its column, giving r_m({j})−s_m, precisely the needed orientation.

The exact reverse declaration is
isUniformEquilibriumPayoff_original_of_singlePivotNormalized in
UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean;
its two relevant hypotheses are a positive pivot own reward and
original all-player punishment normality. The original no-UE/gap
equivalence is the named declaration in Terminal/ExploitabilityGap.lean.
The all-owner quadratic margin declaration in
Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean
requires the true unweighted global carrier minimum, four players,
positive reward bound and positive debt, and has no unproduced Nash
or tail-minimum premise. All these hypotheses match the packet.

### Independent all-response completion reconstruction

For any actual absorbing profile choose an unchanged proper anchor m.
If it is the sole anchor, replace ONLY the Never branch of the row
witness j by a late geometric finite law with maximum atom≤η.
The old anchor screens all prescribed payoffs and every cap except
its own, uniformly over the responder's complete law. The j cap is
exactly unchanged because its prescribed law is deleted.

When m itself responds, the screening anchor is deleted. I checked
the exceptional-event split in F7 separately: outside an OLD finite
opponent tail beyond T, an old finite exit screens the filler; on
the old all-opponent-Never cylinder, responses before H pay s_m,
after H pay r_m({j})≤s_m, and only coincidence can exceed s_m.
The coincidence probability is≤η for EVERY moving finite deadline.
Never has no coincidence excess. Thus the displayed uniform upper
bound holds simultaneously for all late finite tests and Never.
Its benchmark V_m^old(Never)+c_-m s_m is the old late-finite
limit and is at most the old FULL cap.

The lower bound fixes an old finite near-cap test FIRST and then
places the filler strictly later. This is justified by s_m≥0 and
the delayed finite limit, not by cap attainment or pointwise-only
convergence. The second stage has two unchanged proper anchors,
so every responder retains an opponent anchor. It screens ALL
remaining Never replacements uniformly. Parameters are chosen
in order; no uniform anchor-tail estimate while parameters vary
is required. Closing these full-pair approximations gives the
WHOLE identity K_fin=K_abs, not just equality of infima.

The packet's three completion falsifiers are exact. In particular:
passive10/own1/participant-nonsingleton0 has δ_all=δ_abs=0 but
δ_fin=9 for the ENTIRE proper class, so positivity without a row
witness is insufficient. At an equality witness with pair reward100,
the deleted-anchor cap is exactly1+99 sup H({t}); merely delaying a
pure filler is insufficient. For the all-negative table the old
anchor's Never cap0 cannot be approximated by the four-proper cap−1,
so the nonnegative-own lower-cap hypothesis is indispensable.

### Exact minimum equality and the new source seam

The actual declaration
prod_stoppingLaw_none_mul_singleton_le_terminalDebt in
UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean
holds without attainment or sign hypotheses. At the positive-own
table and a common zero coordinate it forces the realizing JOINT
Never products to zero. The smallest marginal Never mass is bounded
by the fourth root of that product. Moving that one small marginal
mass to a finite date changes the ENTIRE pair by vanishing uniform
TV bounds, while leaving the changed owner's cap exactly unchanged.
This puts EVERY full minimum pair in K_abs. Inclusion and equal
minimum values give exact set equality; F9 then gives equality with
Min(K_fin,D). No restricted-domain floor replaces the original
all-tail floor.

Finite support at each index is obtained by moving finite tail mass
to a FINITE date, not to Never. Thus all four original Never masses
remain exactly0. Extracting the Section3 chart afresh has c_n=1,
c=1 and an empty Never interval. Each marked prescribed Never mass
is literally0, and the final finite endpoint has zero mixture mass.
Moving finite dates may still escape on the raw integer calendar.
The fresh producer handles that escape by its ordered chart and
ALL moving tests; it does not assert raw tightness, retain an old
calendar, or identify the finite endpoint with literal Never.

I read the complete supplied quantile, signed-parameter, active-box,
typed-contact, rigidity, deterministic-release and bridge proofs,
not only the new final sections. Their signed likelihood bounds,
whole-date cuts, full-cap extraction and selected-polynomial versus
actual-endpoint distinction are retained in the assembly. The final
table is fixed before every source sequence. Applying that complete
producer to the new finite-clock sequence therefore preserves the
original minimum pair, the common debt vector and unrestricted caps.

### Separate strict export-value verdict

PASS for a significant incremental source reduction, subject to the
normal independent placement gate. Unlike the earlier merely close
absorbing companion, this supplies exact membership of EVERY
original minimum pair in the four-finite closure, at ONE fixed table,
in the common-zero-debt arm. The old canonical source did not impose
that condition, and the actual normal-core theorem supplies all
completion hypotheses. The whole-class boundary tests distinguish
this from an automatic anchor inside a restricted domain.

The concrete new leverage is a whole-law four-finite consumer starting
at a TRUE unrestricted minimum and retaining comparison with ANY
actual tail. The packet does not supply that consumer, an actual
minimizing profile, raw tightness, a Nash tail, or a paid bridge in
the zero-coordinate arm. Those nonclaims are stated correctly. No
SUM/MAX transfer, normalization of old minima, source input left
unproduced, or actual far-endpoint cap overclaim was found.

## Independent NP1–NP9 falsification: separated full gap and fully paid finite bridge

Reviewer: CODEX_BROUWER. Scope is the ENTIRE section beginning
“Forward global source: strict absorbing-gap separation forces a fully paid
finite bridge” and ending immediately before “Forward exact residual: all
own singletons zero, absorption required”, in
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. Frozen section SHA256:
`a2cf862fb5006c6b8acc513a5bfa5bd897e61522bd426498727ebf239600b5ed`.
The extraction hash was verified, all393 lines read, and the section was
not edited. I did not consult the other NP review. Earlier BG source
contributions are disclosed; the new signed translation, separated-gap
producer, all-minimum Never floor, contact-free source application and
whole-block periodic comparison were independently reconstructed here.

Ordinary mathematical verdict: PASS, with no unresolved objection.
Separate significant-source-increment verdict: PASS. This is not a
Lean seal, a UE theorem or authorization for export placement.

### Exact producer versus a conditional interface

The claim is ANY actual Fin4 no-UE game ⇒ ONE unit-bounded, positive-own,
row-generic table with 0<δ_all<δ_abs, all full minima sharing one strictly
positive debt vector, and a paid earliest-root/later-FINITE different-payoff
bridge at EVERY produced minimum. Near-minimizing ACTUAL profiles have a
uniform positive joint Never floor. This is a fresh-table conclusion;
old canonical minima and93 contact labels are not preserved or used.

NP3 genuinely produces its positive absorbing gap from the actual
counterexample: the tracked full-core/punishment producer and reverse
single-pivot transport give a still-no-UE table with owns e_m, whose
absorbing infimum is at least its positive full infimum. Subtracting1
from the pivot row is legitimate because both old and new own rewards
are nonnegative. At ALL absorbing profiles this translates the entire
row pair by a constant and preserves debt EXACTLY. Thus the zero-own
table has A=Δ_abs>0. A is not an assumed punishing profile, selected
tail value or unproduced original absorbing strategy.

The tracked declarations used here were checked in the preceding whole
FC audit under their actual hypotheses: the original no-UE/gap equivalence
in Terminal/ExploitabilityGap.lean; the full-core theorem in
Classification/LCP/ThreeCore/AmbientCarrierElimination.lean; the actual
all-player punishment-normality theorem in
Classification/LCP/NormalCorePunishmentNormal.lean; and
isUniformEquilibriumPayoff_original_of_singlePivotNormalized in
Punishment/SinglePivotUniformPayoff.lean. No inverse same-profile
affine claim or old normality after an unproved normalization is used.

### Exact tests of the signed translation and separation

NP2 is valid for negative C precisely when BOTH own rewards stay
nonnegative. Before and after translation the full cap is the finite
response supremum; all finite responses shift by C. The full prescribed
payoff shifts by C(1−ν), giving the exact d shift Cν. Literal Never
does not independently shift by C, but its finite-limit domination
prevents it from invalidating the full cap identity.

As a small exact test, take the participant-indicator Fin4 table
r_i(S)=1 if i∈S, otherwise0. At AllNever, translating every row by
−λ, 0≤λ≤1, gives U=0, B_i=1−λ and D=4(1−λ). At an absorbing
allQuit profile both U_i and B_i become1−λ and debt stays0. Thus
positive AllNever debt alone does NOT provide a separated gap: this
table has A=0. At the all-nonempty−1 table, a shift+1 instead changes
AllNever's full cap0 to0, not to1; crossing from negative own reward
breaks NP2 exactly outside its hypotheses. These tests check both the
joint-Never term and the indispensable cap-sign boundary.

For the actual produced A>0 table, adding t in all rows gives
D_new=D_z+4tν and keeps Δ_abs=A. AllNever bounds Δ_all≤4t<A/2.
Positivity of Δ_all is proved for EVERY law by the small-marginal
Never replacement and the exact joint-Never debt bound, not by assumed
attainment: A≤D+14M(D/t)^(1/4). Its stated positive lower bound is
correct. It follows that the new table is a genuine original no-UE
game and its full minimum is strictly below EVERY absorbing competitor.

### Final-table compatibility and every-minimum quantifiers

Both value functions are8-Lipschitz on the same fixed profile classes.
Small contraction/perturbation preserves BOTH positive full gap and
strict full/absorbing separation. Row genericity is selected before
coordinate-regular recipient scales; the regular scalarization uses one
FIXED original full debt carrier. Positive scales then give common debt
at ALL NEW unweighted full minima while continuity retains separation.
No maximization at a new table, transfer of an old debt vector, or
SUM/MAX identification is hidden in this step.

At any actual profile the absorbing replacement gives
δ+g≤D+14Mν^(1/4). Hence ALL sufficiently near-minimizers, not one
selected sequence, have the uniform positive ν floor stated in NP7.
The stronger limiting floor at a true minimum follows by taking limits.
Each marginal Never mass is at least the product, and the retained
Never interval/weak-* density argument keeps these literal masses in
EVERY marked source. The exact tracked declaration
prod_stoppingLaw_none_mul_singleton_le_terminalDebt in
Terminal/SingletonJointNeverDebt.lean gives positive debt in every row.
The late finite test has payoff R_i+h_i s_i>R_i, so literal Never is
strictly suboptimal even if the old raw finite supremum is unattained.

### Contact-free signed source argument

The earlier complete quantile and signed old-law transport apply at the
true original full minimum without93 contact exclusions. Positive own
Never mass forces EVERY finite head probability e_i<1. On a signed head
box the whole upper response family is positively affinely transformed,
not merely one response. The lower compact gap is strict. Multiaffine
constancy plus common debt then gives the individual polynomial identity.
The singleton-head case contradicts U_h>s_h; a multi-head case gives
d_i=e_i d_i with d_i>0 and e_i<1. This directly removes all heads
without the older deterministic-coalition spectrum argument.

The earliest active point is finite because Never cannot maximize;
it has positive mixture mass because a zero-mass point would pay the
own singleton. Retained positive atoms are isolated. All root rates
are strictly below1 because every own Never mass is positive. The
one-supplier contradiction uses the ACTUAL conditioned suffix in K_all
and the full global floor, not a Nash or minimum tail. Thus there are
at least two strictly mixed suppliers and the stated three positive
root coalition labels really occur.

If no owner bridged, the complete signed root box would be stable.
A root-only supplier would force its positive common debt to0; a
later-only supplier would force d_i=a_i d_i with a_i<1. Both are
contradictions. All later active tests are FINITE since Never is
strictly below the cap. Row genericity makes the positive opponent-root
event distinguish the two PAYOFF kernels. Retained root dates and moving
finite later responses witness this on the original sequence, with
response gains eventually at least half the positive common debt.
No actual far-polynomial-endpoint cap or pointwise raw attainment is
claimed. This source is paid for ALL owners, not just the observer.

### Whole-block renewal, including its born cap

I independently computed NP11. A finite original block repeated on the
unique live history delivers U_i/(1−ν). Against periodic opponents, a
pure responder that waits k whole blocks then tests at t gets
R_i Σ_(j<k)h_i^j+h_i^k V_i(t). There is an empty finite final
date in each block, and nonnegative own reward makes the old finite
supremum its ENTIRE cap. Every original finite deadline lies in one
such block, while literal Never gives R_i/(1−h_i). Taking the
supremum therefore gives EXACTLY max(B_i,R_i/(1−h_i)), even for
signed R_i. This is the maximum of the two endpoint values of the
geometric interpolation, not a selected within-block response estimate.

At least two limiting root suppliers keep EVERY denominator1−h_i
and1−ν strictly positive along sufficiently late original approximants.
The repeated actual profiles absorb almost surely and have full debt
at least δ_abs. Their complete pair limits give NP12 with the correct
sign: born cap leakage must exceed g plus the strictly positive delivery
gain νΣU/(1−ν). Thus some conditional passive Never payoff is positive
and raises an upper renewal cap above the old B_i. The proof honestly
prices why blind replay fails; it does not claim replay is an equilibrium.

### Separate significant narrowing assessment

This improves the incoming counterexample geometry rather than renaming
its multiple-cap branch. ANY original counterexample produces ONE new
table at which EVERY original minimizing sequence has positive joint
Never probability, every debt is uniformly paid, no root owner is sure,
and a genuine bridge connects two FINITE responses. Zero-debt observers,
literal-Never bridges and sure-root sources all disappear at the selected
table. The near-minimizer floor is quantitative and universal, not an
automatic property of a restricted-domain minimizer. The earlier FC
four-finite arm applies at a different selected table and is not falsely
combined with the strict separation here.

No tracked earlier source named in the supplied packet yields this
strict separation or universal positive near-minimizer Never floor.
The bounded source comparison is with the already audited canonical
source, the FC whole-carrier theorem, the exact joint-Never bound and
the cited renewal interfaces; no global novelty census is claimed.

Concrete new leverage is that a consumer may now use paid response gains,
positive continuation at EVERY owner, finite later witnesses, legal
supported Never variations and a known positive price for complete
block replay. The construction controlling that price is still open;
compatible charge, return, tail Nash and UE are not consequences. The
claimed structural increment itself is complete and genuinely produced.

## Whole-artifact NP assembly: fully paid nonsure finite bridge

Reviewer: CODEX_BROUWER. Final artifact read ENTIRELY, including all
definitions, source proofs and complete boundary tables:
`exports/FULLY_PAID_NONSURE_FINITE_BRIDGE_SOURCE.md`,1016 lines,
SHA256 `21e596e53595811ad4f83b657d97b3942d53e313d69bb2e9e243c2ee2af11953`.
The hash was verified before and after the full reading. The artifact
was not edited. No NOETHER final-artifact verdict was consulted.

Contribution disclosure: I contributed earlier BG bridge mathematics and
the earlier canonical source assembly, so this review does not replace
independent certification of those contributions. I independently
reconstructed the NEW signed whole-row producer, strict full/absorbing
separation, every-minimum positive Never/debt floor, contact-free head
and root application, and periodic full-cap comparison, and checked
their integration with every supplied source/rigidity argument here.

Ordinary mathematical and assembly verdict: PASS. No unresolved source
or mathematical objection. Separate significant export-value verdict:
PASS, subject to the coordinator's independent placement gate. No
Lean seal or UE conclusion is conferred.

### Self-contained producer and exact scope retained

The1016-line artifact includes the full stopping-law semantics, original
no-UE/gap bridge, actual normalization hypotheses, signed whole-row
translation and full-pair coupling estimate. Its zero-own table has
positive ABSORBING gap but unrestricted gap0; this distinction is
explicit. Small positive row constants then produce a strictly positive
FULL gap below the absorbing floor by the quantitative all-law bound.
No companion absorbing minimum, inverse signed affine invariance or
assumed attained clock profile is inserted.

The generic table is selected before coordinate-regular real recipient
scales. Both gap values are continuous over their fixed actual profile
classes, so this SAME final table retains strict separation while ALL
its unweighted full minima share the derived vector. Positive debts
and Never floors hold at every minimizing sequence, not just a favorable
marked selection. The fixed-carrier derivative argument is correctly
separate from differentiation of a moving reward-space infimum.

The whole old-quantile producer and ALL-moving-response convergence
proof are present, as are two-sided supported-atom/conditional-law
transport, bounded nonnegative signed densities, whole-date cuts,
compact lower gaps, upper-family affine stability and multiaffine
interior-minimum constancy. Literal Never and the last finite c test
remain distinct. These inputs no longer rely on conference files or
93 contact inequalities, and no contact exclusions are silently carried.

The contact-free no-head proof uses e_i<1 from every positive Never
mass and d_i>0 from the exact joint-Never debt bound. It does not need
the old deterministic-spectrum exclusion. The one-supplier proof
includes the actual suffix conditioning, full-cap membership and full
global debt floor rather than declaring a tail Nash or minimum. The
root box then forces a paid root/later bridge, whose later point is
FINITE because literal Never is strictly suboptimal. Every positive
root rate is mixed. Generic rows distinguish PAYOFF kernels on an
original positive-probability root event, with literal finite witnesses.
Far endpoint evaluations are selected regrets only, as stated.

### Fresh tracked periodic-source check

I opened the declarations under their actual imports in
UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean:
quittingPureTimeValue_periodizedPrefix_block_interpolation,
quittingPeriodicWindowRefusalValue_periodizedPrefix_eq_div,
and quittingBestReplyValue_periodizedPrefix_le_max.

Their assumptions and conventions match Section11. The period length
is window+1. A last supported original date N is followed by an
EMPTY phase N+1, so choosing length N+2 correctly represents every
old finite response value, including the post-support solo value.
At least two root suppliers keep every opponent survival h_i<1,
including an owner whose own law is Never, and keep the denominators
uniformly positive along late finite approximants. The tracked bound
requires ALL first-block finite phases, not merely prescribed support;
Section11 supplies exactly that bound B_i.

A maximizing first-block phase gives the lower bound B_i. Literal
Never gives R_i/(1−h_i). Together with the tracked unrestricted upper
bound they give EXACT equality max(B_i,R_i/(1−h_i)), including signed
R_i and ALL behavioral deviations. The original finite blocks' actual
periodic profiles absorb almost surely and therefore meet the strictly
higher absorbing debt floor. Passing full U/B/R/n limits gives P17
with the correct positive delivery-amplification term and the extra
gap g. No claimed new periodic formula duplicates this tracked input.

### Independently recomputed complete boundary tables

The all-nonempty−1 translation table correctly falsifies dropping the
OLD nonnegative-own hypothesis. In the zero-own cyclic pair±1/core
triple−1 table padded by dummy0, the two pair contributions cancel
per recipient. Geometric q gives U_i=−q³/[1−(1−q)⁴], finite response
−q²(1−q)^(3t), Never0 and total debt tending0. Thus adding constants
does not manufacture A>0. All sixty coordinates, including dummy
coalitions, are assigned by the displayed formula.

For passive2/own1/participant-nonsingleton0 at half-root/halfNever,
the recomputed values are U=15/16, B=15/8, R=7/4, h=1/8, ν=1/16
per row. Two-phase periodic replay has U=1,B=2 and increases total
debt by1/4, with cap birth1/2 and delivery amplification1/4. For
passive0/own1/participant-nonsingleton−1, the old empty-late cap1/8
is absent in period1: finite values are negative and full cap0.
Including the EMPTY phase restores cap1/8. These exact tests check
the delicate completeness seam, not positive-gap examples.

### Separate strict value and residual

The final full artifact preserves the serious increment assessed in
the earlier393-line review: from ANY counterexample it produces ONE
table whose EVERY full near-minimizer has uniformly positive joint
Never mass and EVERY debt paid, whose first root has no sure owner,
and whose genuine bridge is finite-to-finite. The canonical source
allowed sure roots and zero-debt/Never bridges. The new absorbing gap
separation is genuinely produced and retained at the final table;
it is not an automatic anchor from minimizing over a smaller domain.

Its periodic leakage conclusion honestly prices the remaining full
response cap rather than assuming renewal admissibility. This is a
stronger necessary counterexample source, not a complete consumer.
It makes no claimed transfer of93 exclusions, old minimum pairs,
FC absorbing membership, NF9 or SG results; the latter new notes
remain OUTSIDE this frozen proof. No UE, raw attainment, return,
charged temporal construction or ordinary existence-class coverage
overclaim was found. The file is ready for the stated independent
export/integration gate with exactly the reviewed bytes.

## Independent whole-candidate falsification: singular circuit and full60 return class

Reviewer: CODEX_BROUWER. Scope: CL1–CL10 from the heading
`Dual follow-through: a closed singular full-Nash circuit retires the rational shell`
through immediately before `Negative dual attempt:` in
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`](../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md).
The extracted bytes have SHA256
`0a7b002181838a65118b65adb6c8fe51c5cfb7de024f7707f62cafc2e6858ae2`.
I separately read the COMPLETE RM35/ZU1–ZU6 compiler in
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
whose heading-to-EOF bytes at review have SHA256
`f3cf5f3fd66896f2dfe2e6a1ea097a52929dbfa53062c26a621eca6114d881bd`.
The coordinator identifies that compiler checkpoint as1982e165.

Verdict: **PASS as ordinary mathematics**, including actual full-cap
execution and the full60-coordinate open-chamber claim. No unresolved
mathematical objection was found. I independently executed ALL exact rational
assertions in CL6, reconstructed full triple/pair endpoint identities from
the15 reward rows, and recalculated the complete inverse/support census.
This is not Lean checking. No Lean build, source edit, author-note edit,
export placement or other review verdict was used for this assessment.

### Exact claim and actual inputs

For the explicit60-entry DN table, Never0 and owns1, five closure equations
produce a real V=(1,b,1,d), two literal roots and three convergent full-Nash
ladders closing an exact continuation-to-head chain. BOTH quiet observers
are tested at every finite root. All annotations are in the reward box.
Forward predecessor order is not claimed to be chronological play order.

There are two complete consumers: continuity telescopes the closed positive
chain against every continuous charged root potential, and the tracked
no-UE→polynomial implication gives UE; independently, finite truncation and
reverse-order periodic repetition give ACTUAL approximate terminal Nash
profiles with payoff tending to ONE fixed V. A reward-only finite rational
return criterion produces all these objects, and a full60 open neighborhood
passes it. No minimizing tail, equilibrium, cap selector, closed circuit or
public random signal is assumed as a strategic input to that raw criterion.
Generic ZU alone would be only a supplied-object compiler; the table-dependent
CL closure is the substantive production step.

### Exact root and closure audit

Enumerating opponent coalitions independently gives the triple active gaps
f₁,f₂/T,f₃/T and quiet0 Continue value cU₀+R₀ exactly. Thus G₀ is the
fourth player's actual gap, not an induced-game test. Positive T justifies
its denominator clearing. All CL6 assertions, including the WHOLE-box
G₀<−33, passed exact rational arithmetic.

The Hessian majorant bounds EVERY Jacobian departure on the convex rational
box. Consequently ξ↦ξ−Lf(ξ) has Lipschitz constant≤η<1 and moves the
box into itself because β+ρη<ρ. Its exact zero is produced by contraction,
not identified with the displayed decimal approximation. Positive denominators
make the two polynomial return equations precisely B=b,D=d.

For a solo favorite excess e=v_f−s_f and passive/join values r_f,o,r_f,of,
the actual rate and head excess are

    p=e/(e+r_f,of−r_f,o),
    e′=(r_f,of−s_f)e/(e+r_f,of−r_f,o).

The strict favorite sandwich gives geometric contraction and the printed
product/endpoint formulas. Other coordinates stay between their start and
limiting endpoint. Structural own-level initial equalities are therefore
valid for ALL rows, including nearby perturbed tables; pointwise continuity
at infinitely many separate roots is not being substituted.

The pair active gaps vanish at the printed rates. Independently recomputed
quiet coefficients are

    quiet1: 1−B, −B−2/3, 1/2−B/2, 97/60−B/2;
    quiet3: 1−D, −D−2/3, 3/10−D/2, 13/15−D/2.

These give CL.15 for B,D≥1 and0≤a≤1. In particular the initial quiet
ports W₁,W₃<1 are allowed. No unavailable early solo clock is inserted.
The limiting coalition weights are nonnegative, sum to1 with C, and give
both active coordinates exactly1. General CL.24–26 reduces to these exact
base formulas and retains the correct receiver/owner orientation.

### Finite singular execution and unrestricted caps

At FULL root Nash, the maximum of the two endpoints equals the prescribed
expectation: both endpoints are bounded by it and a supported one attains it.
This includes quiet/sure owners and negative values. H_i(q,z)=max(Q_i,R_i+h_i z)
is h_i-Lipschitz on ALL ℝ. For a forward list the last root is outermost;
reversing the ENTIRE finite list is exactly its chronological Bellman word.
Endpoint seam errors add through Lipschitz constants≤1. The actual carried
port is never reset, and no word-length times seam-error occurs.

The two fixed distinct positive suppliers provide uniform joint C<1 and
EVERY deleted-opponent κ_i<1 after sufficiently large truncations. Hence
the prescribed affine map has its actual fixed point U and the scalar cap
map has a unique W_i. The delicate identification W_i=B_i is valid: censor
after m periods to0, obtaining cap T_i^m(0) by finite dynamic programming.
For EVERY complete responder clock, original/censored payoff difference is
at most Mκ_i^m, since disagreement requires ALL opponents surviving the cut.
This is uniform before taking suprema and includes Never, arbitrarily late
deadlines and behavioral mixtures. Thus the limit really is the unrestricted
cap. The printed bounds for U−V and B_i−V_i yield vanishing nonnegative
debt and one fixed payoff target.

ZU5 independently verifies why joint contraction alone is insufficient:
its signed one-supplier fixed annotation is−1 but actual Never pays0,
so that owner's debt is1 and its deleted survival is1. DN genuinely
supplies the stronger two-supplier condition; it is not removed from ZU.

### Full60 uniformity, not a pointwise perturbation argument

The actual normalized pair quiet gap is

    g_i/h=s_i−v_i+δ_i,0 a/E₂+δ_i,2 t/D₀
                      +δ_i,02 ta/(D₀E₂).

Expressing the current annotation through its fixed endpoint gives CL.26.
The finite inequalities L₀<0,L_a<0,L_t+max(L_ta,0)<0 control ALL t≥0,
0≤a≤1, hence every finite ladder row simultaneously. At the base the
endpoint lower bounds make them strictly uniform. The other conditions are
finite strict tests or structural own-level identities defined using NEW
own values. No higher-coalition coordinate is frozen when evaluating the
triple gaps, quiet0 gap and W.

The table-dependent rational map is smooth where its denominators are positive.
Invertible closure Jacobian gives a continued exact zero under EVERY
sufficiently small independent real perturbation of all60 entries. Compact
box continuity and the uniform quiet tests preserve the entire circuit.
The rational finite verifier and the real qualitative open chamber are
distinct, correctly stated scopes; no optimized reward radius is asserted.
For final assembly keep compatible positive denominator clearing/preconditioning
of the perturbed map. A differently rescaled polynomial system must not be
silently certified by CL6's old Jacobian. This is a proof-presentation caution,
not a mathematical gap: the rational smooth map and positive-cleared derivative
bounds preserve its strict contraction slack.

### Exact tracked correspondence

Inspected `quittingRootCompanionMap_eq_max_endpoints` and the full response
definition in `UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`;
`quittingCompanionComposite_eq_compList_apply` in
`UniformEquilibrium/Quitting/Cycles/CompanionTransport.lean`; and
`quittingPureTimeValue_periodizedPrefix_block_interpolation` and
`quittingBestReplyValue_periodizedPrefix_le_max` in
`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean`.
They confirm the same signed max-affine ALL-response semantics. ZU adds the
ordinary singular-seam/production argument, not new generic cap machinery.

Read `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
under its imports in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
Its forward implication needs the reward bound, normality and a positive
own singleton. `isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` supplies
normality here and in the positive-own open subchamber. The base M=5 and
outer box[−7,7]⁴ contain all ports. Exact roots are robust edges at every
positive tolerance. No normality is inherited from a different normalization,
and no SUM/MAX minimum transfer enters the proof.

### Separate strict value and complete-selection overlap

The raw criterion is a genuine open-class existence producer, not just a
better supplied-cycle theorem. Relative to the named implemented/accepted
raw criteria below it adds an actual surviving class. It is NOT a universal
NP-source consumer or a necessary condition on every counterexample.

The complete specified selection sets fail, not just one guessed witness:

- `RawRegion` in `PairedCycleSchedule.lean`: EVERY pairing has an outsider
  joining the other whole pair, earning triple4>own+1/50. `RawFamily` in
  `BelowSingletonJointPhaseSource.lean` needs two below-own singleton owners
  for each receiver, while receiver0 has only one.
- `RawSource`/`WeakRawSource` in `CrossedMatchingPhaseSource.lean` fail every
  relabeling by that receiver0 count. Its `InverseRawSource` fails every
  matching because every pair has a participant−2<own1.
- The literal cyclic-child `RawRows`/`RawTable` adapters need a pivot
  singleton harming all three others; NONE of the four columns does so.
  Positive recipient scales and nonempty-row translations do not fix it.
- ALL four choices for `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in `Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean` fail:
  only023 has nonnegative inverse, but its outsider weights are
  (−3/5,6/5,2/5); every other inverse has a negative entry. I recalculated
  the four literal inverses and products, not one selected child.
- `IsProjectiveQBarMatrix` in `Classification/LCP/MatrixClasses.lean` fails
  on13: its two negative off-diagonal entries force a homogeneous solution
  to0, while offset(−1,−1) has no ordinary solution. This is projective,
  not merely standard-Q, noncoverage.

Additional independently checked applicable classes beyond CL10's list:

- `SignedFourCycleSingletonData` in `Cycles/SignedFourCycleRewardAdapter.lean`
  requires negative successor and positive predecessor at EVERY owner.
  Receiver1's unique negative successor is3 under ANY order; this forces
  Γ_31>0 at receiver3's predecessor, contrary to Γ_31=−2. Thus both
  smaller/larger spectral branches fail EVERY relabeling before their further
  tests. This strict obstruction persists on an open subchamber.
- `IsLiteralStrictThreeBlockerCore` in
  `Classification/Existence/OddBlockerCoreRowAdapter.lean` fails because no
  owner has constant passive rows. The stronger literal interval version in
  `FiniteOddIntervalBlockerCoreRowAdapter.lean` fails EVERY embedding/blocker:
  every owner has C_i⁺≥5 from an omitted-owner pair, while blocker-absent
  H_i⁻≤own1 from its singleton. Required C_i⁺<H_i⁻ is impossible.
- `quittingPremiumCore` in `Classification/QuittingPremiumCore.lean` and
  `IsFiniteCoalitionPremiumTrap` in `MathUE/FiniteCoalitionPremiumCore.lean`
  give core=I: every owner belongs to a triple with own premium3. Hence the
  actual joining-attractive/mixed-sign triple-core and signed pair-core raw
  producers cannot select a different computed greatest core. This is NOT
  a claim excluding arbitrary induced child profiles.
- Product-low/supportwise balance fails on a pure triple. Protected participant
  leavers cannot protect any player because grand own reward−5<own1.
  On support012 all boxed-charge tuples satisfy delta≤5/2,gap≤5/2,tau≥3,
  loss≤1, so EVERY threshold≤25/3<18. The competing weighted upper average
  at its pure triple is3 for EVERY normalized nonnegative weight. Checked
  exact definitions and the three-owner threshold in
  `Classification/BoxedQuittingNashCharges.lean` and
  `Classification/BoxedQuittingNashChargeOdds.lean`.

The elementary necessary matrix screens do NOT consume the trial: principal
determinants are all nonzero, the complete16-support offset census has only023
with z=(14/5,0,34/5,13/5), quiet slack13/5 and determinant5, and
Γ(5,1,9,5)/20=(9,4,3,2)/20>0. These were recalculated exactly.

Strict value verdict: this is a significant reward-only existence class
relative to those complete raw criteria, not constant optimization or a
solved-table local trap. No specific applicable raw producer was found already
covering this chamber. The check does NOT establish a census of ALL abstract
safe-child or supplied-cycle predicates; possible acceptance of unproduced
strategic objects does not itself prove an existing raw producer supplies
them here. A final packet must retain that limitation and not claim an
unrestricted strategy-class normal form or arbitrary-game circuit production.
The full Fin4 UE conjecture remains open.
