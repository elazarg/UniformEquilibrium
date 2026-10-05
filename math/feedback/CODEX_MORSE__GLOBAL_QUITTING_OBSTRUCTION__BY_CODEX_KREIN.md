# Independent review of the two-player premium core

Reviewer: CODEX_KREIN. Scope: Section 10, **A two-player premium core with
a strict preference to leave the pair**, in
`../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. No other review
of that section was read before this assessment. Ordinary mathematics;
no Lean build was run.

An independent addendum below reviews Sections 11–13, including mutual
strict joining and the greatest-premium-core transfer. Its scope and
verdict are separate from the original strict-leave review.

## Verdict and exact scope

**PASS for the analytic theorem and its four-player uniform-equilibrium
consequence, with no unresolved mathematical objection.** The proof treats
the full simultaneous root game and all coalition rewards. It does not
silently restrict root supports to the two core players. The semantic
consumer has the stated normality and positive-singleton hypotheses, and
the proof supplies them, treating the all-zero-singleton case separately.

The raw hypothesis is: every participant reward is at least its singleton;
all players outside a specified pair have constant participant rewards;
and one member of that pair strictly prefers the other singleton outcome
to the joint pair outcome. The analytic exclusion permits signed
singletons in every finite player set. The UE conclusion here is for four
players with nonnegative singletons. No strategy-class completeness or
general finite-player existence conclusion is inferred.

The earlier test table in the source note already has a safe-spectator
consumer, as the author states. Below I give a different complete rational
table in the new class that avoids the named product-low, proper-child F/J,
homogeneous, degree, inverse, and response-quotient screens. This supports
the intended implemented-scope increment without claiming that every
possible repository producer has been classified.

## Independent addendum: weak leave, negative-index selection, and peeling

Scope: Sections 11, 12, and 13 of the source notebook, as written at this
review. I did not read CODEX_BROUWER's review details of these sections.
I checked the full root equations, the ambient-degree hypotheses, the
boundary perturbation, the semantic consumer, and the finite trap argument
independently. Ordinary mathematical review only; no Lean build was run.

VERDICT: PASS, with no unresolved mathematical objection, for each of:

- Section 11's weak-leave four-player UE corollary and zero-pair-premium
  product-low reduction;
- Section 12's signed finite-player analytic exclusion under mutual strict
  joining, and its nonnegative-singleton four-player UE consequence;
- Section 13's transfer to a greatest premium core of cardinality at most
  two, under nonnegative participant premiums and nonnegative singletons.

The exact root producer in Section 12 is substantive: a particular bad
mixed root is allowed to exist, but cannot be the only full root because
its local index is negative. No strategy obtained by repeating an arbitrary
root, continuous root selector, bounded-controller restriction, or hidden
outside-player deletion is used.

### Weak leave and fixed-target closure

Increasing only r_i({j}) by delta, with i≠j, changes a nonparticipant
coordinate. It preserves every own singleton and participant-premium
hypothesis, and changes the reward distance by at most delta. The nearby
table satisfies strict leave even at original equality.

I read the literal declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
It permits both the nearby targets and profiles to vary and concludes
existence of one fixed target for the original table. Thus the source
really supplies the claimed strategic closure. The accompanying elementary
compact-target argument has the correct quantifiers: select one nearby
target at each requested error, then reuse one of that game's profiles
and one eventual horizon threshold. No strategy limit is required.

The zero-pair-premium reduction also exhausts the product supports. An
active globally flat outsider supplies a singleton-level Quit endpoint.
With no such outsider active, if the zero-premium core member is active,
its endpoint is its singleton mixture; if it is inactive, the other core
member is the sole possible active player and also has its singleton
endpoint. Nonnegative participant premiums are consistent with equality
here, and arbitrary larger core premiums cannot enter a core-only root.

The weak-leave corollary is correctly only an existence claim. Reward
closure has not been substituted for an unproved closure theorem for all
C¹ exact-root potentials.

### Actual full-game fixed points and the local sign

The polynomial extension of every endpoint gap to all real hazards is
well defined because the finite independent-coalition formula is a
multilinear polynomial. Composing q_k+g_k(q) with the scalar clip produces
a continuous map from all of R^I into [0,1]^I. Every fixed point lies in
that cube. At a zero, unit, or interior coordinate, its fixed-point
condition is respectively g_k≤0, g_k≥0, or g_k=0. These are exactly the
two-action Nash support conditions for the actual full root game.

On the core-only face the formulas in (55) retain the correct signs and
indices. If one core annotation is below its singleton, its gap is a
strictly positive convex combination at every other core hazard. This
forces that player to Quit surely, then forces the other core player to
Quit surely. A harmed constant-participant outsider blocks that pure
pair, independently of every continuation annotation. Thus every exact
root in this source case has an active outsider.

With both core annotations strictly above their singletons, neither a
singleton active core nor a non-pair unit core hazard is possible. Besides
all-Continue and the blocked pure pair, the only core-supported candidate
is exactly (56), whose two interior coordinates use the OTHER player's
annotation. Some source coordinate below its singleton excludes
all-Continue. Therefore a second full fixed point, if produced, must
have an active outsider; this is a complete support classification.

At the mixed candidate, strictly negative outsider gaps make the clipped
outsider rows constant zero on an actual ambient neighborhood, including
points whose outside coordinates are slightly negative. The two core rows
are unclipped on that neighborhood. Since an endpoint gap is independent
of its own player's hazard, the core diagonal of D(q−F) is zero. The core
off-diagonal entries are −alpha_i and −alpha_j; all outside rows form an
identity block. Arbitrary derivatives involving outside hazards occur
only in the upper-right block. The determinant is therefore exactly
−alpha_i*alpha_j<0, with no missing orientation factor.

The index normalization is valid also when some candidate coordinates are
zero. The source region (−1,2)^I contains the whole unit cube in its
interior; throughout the stated homotopy, any zero must lie in [0,1]^I.
Consequently the source boundary is zero-free. The terminal translated
identity has degree +1. Invertibility and differentiability justify the
local straight-line comparison with D(q−p), and uniqueness would permit
excision onto that neighborhood. The resulting local degree is negative,
contradicting the total degree +1. No assertion of smoothness at a tied
clipped outsider is made; ties are removed before this argument.

I inspected the declarations `ambientDegree_homotopy` and
`ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`,
and `ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
Their hypotheses match the supplied open bounded source, continuous full
field, boundary avoidance, and nonsingular affine comparison. The proof
does not invoke an absent game-theoretic Nash-index axiom.

### Boundary minimization and tie removal

Every exact root successor dominates every Quit endpoint, hence every
singleton, by nonnegative participant premiums. It remains in the original
box by convexity. An active globally flat outsider then supplies equality
in at least one coordinate, returning to the SAME lower boundary L.

At a boundary minimizer with just one binding coordinate, that player alone
can use a sufficiently small positive hazard. Every other player's strict
Continue preference at zero hazard persists by continuity, including the
actual pair-join rewards. The owner is indifferent and its successor
coordinate is its singleton. This alone contradicts positive potential
drift and minimality. With at least two bindings, increasing any one
binding coordinate keeps another fixed, proving the required nonnegative
gradient signs without needing L to be a smooth manifold.

When a binding core coordinate is decreased, the already-checked core
classification forces every exact root to have an active outsider.
When only outsiders bind, holding both core annotations exactly fixed
keeps the mixed candidate exactly fixed. Each outsider's Continue endpoint
contains its own annotation with the strictly positive coefficient c(p),
while its forced-Quit endpoint is constant. Thus at most one value of its
independent O(epsilon²) correction is forbidden. Finitely many coordinatewise
choices remove every outsider tie and retain at least epsilon of downward
displacement on each binding coordinate. Continuity of these choices in
epsilon is unnecessary: the total extra displacement is o(epsilon).

For any binding k, the produced successor satisfies
w_k−v_k≥epsilon, while the actual absorption formula bounds this difference
above by (M+B)*a. Potential drift and minimality then force
[H(v)−H(x)]/epsilon≥1/(M+B)>0. Differentiability gives a limit equal to
the negative sum of binding gradients, hence at most zero. All source
points stay in the same box because B>M and s≥−M leave strict lower
clearance; upper-box coordinates move only downward. This closes the
analytic contradiction without summing over successive root choices.

### Exact boundary and index tests

I independently recalculated Section 12's three-player rational fixture.
At v=(2,1,−1/10), p=(1/3,1/3,0) has gaps (0,0,−53/45), successor
(4/3,1/3,53/45), and the full ambient Jacobian

    [[0,−3,2], [−3,0,3], [0,0,1]],

whose determinant is −9. Thus the strictly interior successor of the
bad root really occurs; an argument asserting universal return would fail.
The alternative root (0,0,1) has gaps (−2,−3,1/10) and successor (3,3,0),
so it does return to the lower boundary.

The same table gives an exact clipping-tie test at v=(2,1,−11/4): all
three gaps at p are zero. Decreasing only the last annotation by eta>0
changes its outsider gap to 4eta/9>0. Thus the mixed candidate ceases
to be Nash and the finite root theorem directly supplies another root.
This tests the non-index branch of tie removal, instead of treating a
boundary-tied clip as differentiable. Signed singletons and no-outsider
player sets do not break the analytic statement: if there are no outsiders,
the pure pair already gives the fixed positive-absorption edge.

### Greatest-premium-core transfer

The union closure of traps is literal: each member retains its original
positive witness in the union. A first removed trap member cannot be flat
on the current subtable, because its whole original trap is still present.
Conversely a nonempty terminal residual is a trap. This proves that every
finite peeling order leaves exactly the union of all traps. No actual
player or payoff coordinate is removed from the game in this argument.

For greatest core C={i,j}, any nonempty support A≠C is not a trap. Indeed
any trap is contained in C, and no singleton can be a trap. Since all
participant premiums are nonnegative, some member of A is therefore flat
on EVERY participant coalition inside A. Conditional on that active
member's Quit, every possible coalition is inside A, so its Quit endpoint
equals its singleton. Its successor coordinate equals that endpoint.
This proves Fact 1 even when the returning player is a core member or is
not globally flat; it is not necessary to preselect a particular outsider.

For each outsider k, a positive participant premium at any T∪{k}, T⊆C,
together with the two pair witnesses would make C∪{k} a larger trap.
Nonnegative premiums therefore force all these entries to equal s_k.
This proves Fact 2, which is exactly the additional input required for
pure-pair blocking and for each inactive outsider's Quit endpoint during
tie removal. It does not assert flatness on coalitions containing another
outsider.

These facts transfer the proof without losing its quantifiers. For strict
leave, only support C needs the core gap argument, and the minimizer's
binding-outsider conclusion uses singleton-face drift, not global flatness.
For strict joining, the exhaustive core-only classification and negative
local determinant are unchanged. Every root with another support returns
by Fact 1; clipping makes the outside Jacobian block constant even if its
unclipped derivatives see positive premiums on larger coalitions. The
O(epsilon²) corrections and the absorption lower bound are unchanged.
Equality perturbations alter only a nonparticipant coordinate, so they
preserve all traps and the greatest core exactly.

As a finite stress test, prescribe positive participant premiums only for
both players 0,1 at {0,1}, and player 2 at {2,3}; player 3 is flat. The
only trap is {0,1}, although player 2 is not globally flat. Peeling 3 and
then 2 leaves that core. Supports containing both outsiders have flat
member 3, whereas {0,1,2} has flat member 2, checking the support-dependent
returning member. If player 3 ALSO receives a positive premium at {2,3},
then {2,3} and the full four-player set become traps. That two-sided
variant is correctly excluded by Section 13 and is not covered by the
size-two theorem merely because its premiums occur at pairs.

I checked `HasWeakQuittingPremiumSupportPeeling` and
`hasWeakQuittingPremiumSupportPeeling_iff` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`,
`HasFiniteCoalitionSupportPeeling` in
`MathUE/FiniteCoalitionSupportPeelingOrder.lean`, and
`hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative` in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`.
Their empty-core condition is exactly supportwise flatness. The nonempty
pair core is a genuine extra case, not the old peeling predicate renamed.

### Complete four-player semantic consumer and limits

I rechecked `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`,
`quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`,
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
and `isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.

The finite root producer accepts arbitrary continuation annotations and
retains every player. Nonnegative singleton rewards give punishment values
equal to singletons and hence the required normality. If any singleton is
positive, no UE supplies a rational-polynomial potential on the actual
robust relation in box M+2; exact-root restriction preserves its function,
game, and unit absorption charge. The analytic contradiction excludes it.
If all singletons are zero, all-Never is exact Nash directly. These cover
every strategic source case without assuming the sure-root arm away.

Thus Sections 11–13 establish the stated original-game fixed-target UE
conclusion for four players and do not merely supply an obstruction
interface. They do not claim arbitrary finite-player UE, signed-singleton
UE, negative-participant-premium coverage, or greatest cores of size three
or four. Those boundaries remain substantive and correctly stated.

## Final standalone assembly check

PASS for the exact artifact
`../exports/PREMIUM_CORE_AT_MOST_TWO.md`, SHA256
`6adeee61351be59759a6ae69759a44fd055b7fd4bb7db1feb28379c124d6558e`.

I read the entire assembled packet and checked its mathematical delta
against the independently reviewed Sections 10–13. The main raw class,
support-return and core-face-flatness facts, strict-leave and actual-index
proofs, all boundary cases, and unrestricted fixed-target consumer match
the reviewed arguments. Equality is handled only by UE reward closure;
no analytic-potential closure is claimed. The complete fifteen-row layered
fixture, all fourteen child cases, quotient boundary calculations, negative-
index example, and exact clipping-tie example are retained. The proof has
no mathematical dependency on conference notes or frozen exports and
identifies the exact tracked source consumers.

The final hash differs from the initially assembled artifact only by
removal of its two-line draft preface and last process sentence. No
mathematical correction is requested. This is an artifact-scope check,
not a new Lean-build claim.

## Independent addendum: a common leaver, including signed outsider premiums

Scope: Sections 14 and 15 of the source notebook, after the explicitly
resolved principal-matrix correction below. The reviewed whole-note hash
is `addb73fce7440cb03e41ac8a0afb06d78d6563e35fcc2960019542b84eec891e`.
I did not read CODEX_BROUWER's review of these sections. This is an
independent mathematical and static source audit, not a Lean build.

VERDICT: PASS for the common-leaver theorem in Section 14 and for its
strictly stronger signed-premium theorem in Section 15, with no unresolved
mathematical objection. The analytic result is finite-player and permits
signed singletons; the strategic consumer is Fin4 with nonnegative own
singletons. Only the protected player's participant premiums must be
nonnegative in Section 15. Weak leave is a UE corollary by reward closure,
not a weak-comparison C¹ potential-exclusion theorem.

### The exact raw support argument

The positive-premium trap definition makes sense unchanged when other
participant premiums are negative. Union closure still holds because
positive witnesses survive taking unions. Under signed premiums, a support
which is not a trap has an active member whose participant rewards on
ALL subcoalitions of that support are at most its singleton; equality
must not be inferred. Section 15 uses exactly this weaker inequality.

If the active support A is a trap, every-trap containment gives p∈A⊆C.
Conditional on p's action, every nonempty opponent coalition lies in
C\{p}; its actual Quit-minus-Continue difference is strictly negative
by the pointwise leave hypothesis. The empty-coalition difference is
s_p−v_p≤0. Another player must have positive hazard because singleton
traps are impossible. Thus the nonempty-opponent event has positive
probability, including at unit hazards, and the averaged gap is strictly
negative. This contradicts p being active. No positive outside hazard
has been dropped from this calculation: supports not trapped are handled
by their own low-premium active member.

For Section 14, every exact successor is at least the full singleton
vector, and that member has equality, giving return to L. For Section 15,
only the protected coordinate is known to stay above its singleton.
The low-premium active member instead supplies w_k≤s_k. Therefore the
returned point belongs to the original set

    D={v in [−B,B]^I : v_p≥s_p and some v_i≤s_i}.

That is the exact invariant set needed, not the smaller boundary L.
The return proof permits any signed participant rewards away from p,
arbitrary simultaneous coalitions, and a different returning member
at each root. It also handles C empty and the case where that member
is p itself.

### Why the minimum returns to L before perturbation

The set D is compact and nonempty, since it contains the singleton vector.
At a minimum x, any strict inequality x_k<s_k makes all-Continue fail
Nash: quitting alone improves that player. Finite Nash existence supplies
a positively absorbing exact root; the protected floor returns its
successor to D. Potential drift then gives a strictly smaller value of H
inside the SAME minimizing set. This excludes every below-singleton
coordinate at the minimum, so x≥s. Membership in D forces an equality,
hence x∈L. Because L⊆D, x minimizes H on L as well.

The singleton-face derivative inequality needs no premium signs. At only
one binding coordinate, its own contribution vanishes; all nonbinding
interior derivatives vanish, and upper-face derivatives are nonpositive
against strictly positive B−r_i({j}). This contradicts the positive
face-drift bound. Thus at least two coordinates bind. Increasing one
while retaining another proves nonnegative binding derivatives. One can
therefore lower a binding k≠p, keep p's floor exactly, and obtain a
nonpositive first-order variation of H.

I directly checked `IsQuittingFullExactRootPotential.singletonFace_drift`
in `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.
Its literal hypotheses are the reward bound, strict box margin, singleton
face, and differentiability. It has no nonnegative-premium hypothesis.
Thus the signed proof does not reuse a face theorem outside its scope.

### The signed absorption estimate is valid without a restored floor

At source v=x−epsilon*e_k, let a be full absorption and a_{−k} the
probability that an opponent quits. A forced Quit receives s_k on the
event no opponent quits and differs from s_k by at most 2M otherwise.
Hence

    Q_k≥s_k−2M*a_{−k}≥s_k−2M*a.

The second inequality uses a_{−k}≤a, independent of k's own hazard.
Exact Nash gives w_k≥Q_k, while direct averaging gives

    w_k≤v_k+(M+B)a=s_k−epsilon+(M+B)a.

Combining gives epsilon≤(3M+B)a, with a strictly positive coefficient.
It does not assume w_k≥s_k, and does not require the perturbed player
to be the returned low-premium witness. Minimality is on D, so
H(w)≥H(x) even when w lies below some singleton. Dividing the drift
bound by epsilon contradicts the nonpositive directional derivative.
This is a complete charge estimate, not a qualitative assertion that
absorption stays away from zero.

### A signed exact-root test requiring D rather than L

The following three-player table gives an explicit return below a
singleton while satisfying the nonempty-trap signed hypotheses:

    r({0})=(1,−2,0),     r({1})=(0,0,0),
    r({2})=(3,0,0),      r({0,1})=(1,−1,1),
    r({0,2})=(2,0,1),    r({1,2})=(0,0,0),
    r({0,1,2})=(1,0,0).

Take p=0. The only trap is {0,2}, and the protected comparison is
2<3. Player 0's participant rewards are all at least one. At any
annotation, the pure root with active coalition {0,1} has endpoint gaps
(1,1,−1), so it is full exact Nash. Its successor is (1,−1,1), which
lies in D but not in L. In particular the signed return must not be
strengthened to a lower-boundary return or to coordinatewise singleton
floors. Section 15's proof handles exactly this situation.

### Exact semantic consumer and reward closure

I directly inspected `isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.
It derives normality from the singleton sign alone using the general
punishment upper bound; no participant-premium assumption occurs. The
signed proof therefore does not need punishment values to EQUAL
singletons. They may be strictly lower.

The already inspected
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
requires precisely the bound, normality, and one positive singleton.
`isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
retains the same polynomial, reward table, box, and unit charge without
premium restrictions. A polynomial is C¹, so the signed analytic contradiction
consumes the actual no-UE output. The all-zero-singleton case is handled
directly by all-Never, since every unilateral exit against it pays its
own zero singleton regardless of other coalition premiums.

For weak leave, increasing r_p(T) on nonempty T⊆C\{p} changes only
passive coordinates. Every participant reward, own singleton, positive
premium trap, and the whole C remain unchanged. The protected participant
floor survives, the comparisons become strict, and reward distance is
at most the chosen delta. The literal fixed-target closure theorem in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
therefore applies. Targets may vary in the nearby games; one fixed target
is selected for the original table. No profile limit is assumed.

### Three-core fixture audit and the resolved local correction

The complete Section 14 table has positive participant witnesses only
for players 0 and 3 at {0,3}, and player 1 at {0,1}. Thus its greatest
core is {0,1,3}, every trap contains 0, and the three protected comparisons
are precisely 1<11/10, 2<5/2, and 1<5/2. It is outside product-low
and greatest-core-at-most-two coverage, while satisfying the new raw
criterion. This is coverage of actual three-core data, not a supplied
protected-return interface.

During this audit I found that the initially written principal {0,1}
matrix was incorrectly called R0. It has homogeneous vector (0,1)
with residual (1/10,0). The author corrected the source-screen witness
to principal {0,2}=[[0,−1],[−1,0]], which is R0 and non-Q, and retained
the explicit {0,1} counterexample. This objection is fully resolved;
neither the main return proof nor the signed extension was affected.

I independently recomputed the full determinant 21/5, full inverse
entry −26/21, child inverse weights (26/35,−1/70,−9/70), and the stated
negative entries −20/21, −15/13, −1/2 in the other triple inverses.
The positive-child LCP reduction has the exact unique degree-one root
(0,1,1,1) with inactive residual 8/5. The partition table retains only
0|123 at first order, and its three actual response components differ
as displayed. All fifteen named pure-coalition improving players were
checked by exact rational reward comparisons.

The proper-child sure-exit witnesses remain full child Nash, including
withdrawal to a singleton or eventual Never. The cyclic three-child
quiet pivot value is exactly 69/70 and its forced-Quit payoff one.
For child {0,2,3}, I recalculated the pairs of Continue/Quit endpoints:
(1,1), (−4/5,0), (0,0), with omitted player 1's pair (−11/15,0).
After changing r_2({0,2}) to −1/10, the participant-2 Quit endpoint is
−1/25, still above −4/5, and the other displayed pairs are unchanged.
Child {0,2}'s sure player-2 payoff −1/10 is above its withdrawal payoff
−1; delaying does not escape the other player's sure absorption. Thus
negative participant rewards have not been justified using a false
singleton-floor argument. The signed fixture preserves the positive
trap data and all protected comparisons, and its changed response
component t−t²/10 still breaks the remaining quotient.

The precise signed raw assumptions remain material. This review gives
no coverage when the protected player itself has a negative participant
premium, when no player lies in every trap, or when every possible
common member has a failed leave comparison. It also does not convert
the finite-player analytic result into a general finite-player UE theorem.

## Full-root return and the boundary derivative

For an exact root, every successor coordinate dominates its forced-Quit
endpoint, hence its singleton by nonnegative participant premiums. The
successor stays in the same box because it is a convex combination of the
source annotation and actual reward vectors.

If ANY constant-participant outsider is active, supported Quit identifies
its successor coordinate with its singleton, regardless of the other
hazards or the core's triple and grand-coalition premiums. This already
returns to the stated lower boundary L. Only after all outsider hazards
are zero may one use the two-player gap

    (1−q_j)(s_i−v_i)+q_j[r_i({i,j})−r_i({j})].

When both core hazards are positive, the gap is strictly negative under
the stated source floor v_i≥s_i, contradicting supported Quit. Positive
absorption therefore leaves exactly one active core player and again a
successor coordinate equal to its singleton. The full-root split is
exhaustive. The other core floor is retained for the later perturbation;
the algebra does not drop a positive outsider hazard.

At a singleton face with all other coordinates strictly above their
singletons, a sufficiently small sole-owner rate is an actual exact Nash
root. The nonowner gap at rate zero is strictly negative, and all endpoint
comparisons depend continuously on the rate, including actual pair
rewards. The potential inequality along the resulting successor segment
gives

    gradient H(x) · (x−r({k})) ≥ 1.

Moving the other coordinates toward B creates strict inequalities while
remaining inside the same box and preserving the owner coordinate.
Continuity of the gradient gives the weak-face conclusion. This does not
require a uniform admissible rate at a multiple-face intersection.

The exact source declaration
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
was inspected. Its hypotheses and derivative direction agree with this
argument, including the strict outer-box margin B>M.

## Binding coordinates and the selective perturbation

At a minimizer of H over compact L, a single binding coordinate is
impossible: the sole-owner root has positive absorption, remains in L by
the return property, and would lower H.

With at least two binding coordinates, increasing one retains another
binding coordinate, so its gradient coordinate is nonnegative. A
nonbinding interior coordinate has zero gradient. An upper-box coordinate
has nonpositive gradient, since decreasing it is feasible. These are
correct one-sided conditions for this union of lower faces; they do not
assume that L is convex.

If only the two core coordinates bind, apply the face derivative with
owner j. The i contribution is nonpositive because
r_i({j})>r_i({i,j})≥s_i. The owner contribution is zero; nonbinding
interior contributions vanish; and every upper-box contribution is
nonpositive because B−r_k({j})>0. This contradicts the lower bound one.
Thus at least one constant-participant outsider binds.

Lowering exactly those binding outsiders by epsilon leaves the two core
annotations untouched. This is the decisive preservation step: the new
annotation can be below some singleton floors and still lies in the source
region where the full-root return was proved. The directional potential
increment divided by epsilon tends to a nonpositive number.

Finite Nash existence at that annotation supplies an actual product root.
All-Continue is not Nash, because each lowered outsider can gain epsilon
by quitting alone. Every selected root therefore absorbs positively and
returns to the original L. Its lowered outsider coordinate moves upward
by at least epsilon. Since

    |T_q(v)_k−v_k|≤(M+B)*a(q),

its charge is at least epsilon/(M+B). Combining charge drift with
minimality on L forces a strictly positive lower bound on the same
directional quotient, contradicting its nonpositive limit. No continuous
root selection, returned strategy, or accumulated charge assumption is
needed. Upper-box coordinates and ties among binding faces are all covered.

## Actual semantic endpoint

I inspected the following declarations and their stated hypotheses:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`;
- `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.

Nonnegative singletons and premiums give punishment values exactly equal
to singletons, hence all players normal. If some singleton is positive,
the no-UE hypothesis produces a rational polynomial potential on the
full robust relation in box M+2. The last declaration restricts that SAME
potential to every boxed exact Nash root, with unchanged unit absorption
charge. Its differentiability is automatic. The analytic contradiction
therefore applies. If every singleton is zero, all-Never directly gives
the required equilibrium. The argument does not assume away the sure-root
alternative or substitute a bounded deviation class.

No strategic input remains unproduced: the finite root theorem and the
no-UE polynomial producer are established source inputs, and the new
boundary argument contradicts their exact output under the raw conditions.
This is a classical existence proof; it does not purport to compute a
particular terminal strategy from the minimizer.

## A new exact implementation-overlap witness

For every nonempty S⊆{0,1,2,3}, first define

    r_0(S)=1 if 0∈S, and 4*1_(3∈S) otherwise;
    r_j(S)=0 if j∈S,
           −1 if j∉S and 0∈S,
           2*1_(pred(j)∈S)−1_(succ(j)∈S) otherwise,

where the nonpivot cycle is 1→2→3→1. Change only two coordinates:

    r_0({0,3})=2,             r_3({0,3})=1.              (A)

This completely specifies the table. Take the premium core to be {0,3},
with designated player i=0. Its own singleton vector is (1,0,0,0).
Every participant premium is nonnegative, players 1 and 2 have constant
participant rewards, and r_0({0,3})=2<4=r_0({3}). Thus it satisfies
the theorem literally. At hazards q_0=q_3=1/2, both active premiums are
1/2>0, refuting product-low directly.

Its singleton matrix is

    [[0,−1,−1,3],
     [−1,0,−1,2],
     [−1,2,0,−1],
     [−1,−1,2,0]].                                      (B)

Every row has a distinct negative witness, so its normal core is full.
It has no nonzero homogeneous LCP solution: positive pivot coordinate
forces all child coordinates positive, then all equal to the pivot
coordinate, which leaves a positive pivot residual; zero pivot coordinate
and a positive child force every child positive, contradicting invertibility
of the child matrix. At offset (1,−1,−1,−1), the unique LCP solution is
(0,1,1,1). Its inactive pivot residual is 2 and its active determinant
is 7. Thus the inspected R0-degree root-sum criterion gives degree +1,
and nonzero degree gives standard Q. This is neither a non-Q nor a
nonunit-degree example.

The {0,1} principal has two negative off-diagonal entries: it is neither
standard Q nor homogeneous-feasible. The pivot inverse row on the cyclic
three-child matrix has middle entry −3/7. Every other triple has a row
with both off-diagonal entries negative, excluding a nonnegative inverse.
The full inverse has entry (0,1)=−9/7<0. These are direct failures of
the named projective-Q-bar and nonnegative-inverse/passive-row screens.

There is no nondiscrete response-invariant partition. The necessary block
row-sum condition excludes all six single-pair merges, all three pair-pair
partitions, all three triples containing 0, and the one-block partition:
the last has pivot row sum 1 versus child row sums zero. The sole
first-order survivor is {0}|{1,2,3}. At pivot hazard x>0 and zero common
child hazard its individual residuals are

    F_1=F_2=x,                F_3=x+x²,

using (A), so actual response invariance fails. This checks partitions
not induced by reward automorphisms as well as orbit partitions.

Every proper-child F/J family also fails. Here are all cases, each with
zero child regret and joint Never zero:

1. For one or two nonpivot children, choose a sure solo owner giving the
   other retained child payoff 2 when needed. A missing nonpivot gets
   −1 and joins for zero.
2. For all three nonpivots, repeat solo hazards 1/2 in order 1,2,3. Its
   three entry vectors are (0,1,0), (0,0,1), (1,0,0). These satisfy
   exact Bellman and action comparisons; opponent survival contracts
   every period, so full behavioral regret is zero. The quiet pivot gets
   4/7 and can quit at the first phase for one.
3. If the child contains 0 but not 3, every child quits surely at the
   first date. No changed coordinate in (A) is used. The pivot and each
   nonpivot prefer their prescribed Quit action. A missing nonpivot gets
   −1 and has a strictly better joining payoff (zero, or one for the
   special pair {0,3}).
4. If the child contains {0,3} but not 2, child 3 alone quits surely.
   The pivot gets 4 rather than the pair's 2; retained player 1 gets 2;
   owner 3 gets zero and is indifferent to Never. Missing player 2 gets
   −1 and joins for zero.
5. For child {0,2,3}, child 2 quits surely, pivot 0 uses hazard 2/3,
   and child 3 uses hazard 1/4, at the first date. Every realized coalition
   contains 2, so (A) is irrelevant. Pivot and child 3 are indifferent;
   child 2's Continue payoff is −3/4 versus Quit payoff zero. Omitted
   player 1 receives −5/6 and joins for zero.

These exhaust all fourteen proper nonempty children. The universal
five-kind bound in
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`)
would bound positive outside debt by zero on each corresponding witness.
Thus no choices of its nonnegative weights repair any proper-child
family for this table.

The degree declarations used above are
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`. The quotient necessary condition
is `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
the exact residual uses `quittingDiscountedDisplacement` at zero in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
These sources were inspected in this conference session.

The positive singleton comparison graph of (B) has one positive
off-diagonal entry in every row and no reciprocal positive pair. It also
does not satisfy the two-positive-nonpartner condition of the inspected
paired-cycle producer. No symmetry quotient is being silently assumed.

This witness supplies a concrete check that the theorem is not merely
recovering the particular safe-spectator example in the source note, nor
the named implementation gates above. The non-overlap statement remains
bounded to those precise gates. My mathematical PASS does not require an
unsupported assertion that no other proof of this same table could exist.
