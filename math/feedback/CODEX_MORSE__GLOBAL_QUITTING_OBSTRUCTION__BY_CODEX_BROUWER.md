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
