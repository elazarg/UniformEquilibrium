# Independent falsification and export-gate review of `COMP`

Reviewer: Codex Poincare

## Verdict

The note contains two valid results and one valid reduction target, but it
should not be exported as one theorem.

1. **Sections 1--2 pass in ordinary mathematics.**  Same-row endpoint
   updates really do give a literal finite regeneration, and the resulting
   `Fin 4` cycle really has either a common quitter or a complementary pair.
   This is a strict producer-side contraction of the surviving
   nonsingleton-collision branch.
2. **Section 4 passes in ordinary mathematics after its data are stated
   exactly.**  The periodic two-clock estimate is a genuine useful adapter
   to the checked chronological-debt consumer.  I found no counterexample to
   its estimate; the order assumptions are sharp in the scalar recursion.
3. **Section 3 must weaken “exact executable edge.”**  Its limit is an exact
   positively absorbing one-row Nash--Bellman datum.  No punishment-floor
   path, attained limiting tail, or return is produced.
4. **Sections 5 and 7 are not proved producers.**  In particular, (35) is the
   remaining question, not a conclusion of the endpoint monodromy.  The
   horizontal cycle does not determine the first-order chronological jet or
   the two deleted-player exposure clocks.

Nothing in the raw `COMP.md` satisfies `exports/README.md` as written, because
it is not a self-contained packet and mixes the proved reductions with (35).
The strongest honest split is described in the final section of this review.

## Sources inspected

I checked the claims against the following narrow source set.

* `quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain`,
  `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`,
  `quittingStageBestEndpoint_nearMinimum_opponentTransfer`,
  `quittingStageCoalitionMass_le_stagePureEndpointRouted`, and
  `quittingLiveWeightedCollisionTransfer_tailEscape_or_routedTransfer` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* `twoDiscountDebtError_eq` in
  `MathUE/Probability/OneSidedDebtShadowing.lean`;
* `QuittingChronologicalDebtData`,
  `QuittingChronologicalDebtShadowingCertificate`, and the terminal/uniform
  consumer chain in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`;
* `QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
* `exists_reextractedFrontier_of_minimumFiberEndpoint` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`;
* the currently recorded nonsingleton adapter in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`; and
* the generated-secant and nonsingleton entries of `docs/TOOLKIT.md` and the
  chronological producer boundary in `docs/FRONTIER.md`.

A narrow phrase/declaration search found no existing same-stage closed
endpoint-gain-cycle theorem or periodic two-clock residual specialization.
The underlying collision transfer, two-discount identity, and rank
re-extraction are already checked; the finite monodromy and periodic
specialization are the new ordinary mathematics.

## 1. Same-row finite regeneration is correct

Let the row have live mass `L`, fixed literal shifted tail `z+`, and a marked
nonsingleton stage coalition of mass `m >= lambda`.  Assume

\[
 E=D(z^+)-D_*<\lambda D_*/2.
\]

A pure endpoint update changes only one player's action at that row.  The
checked routing theorem gives all three facts needed for iteration:

* the probability of reaching the row is unchanged;
* the shifted tail is unchanged; and
* the routed stage mass does not decrease.

This is literal profile equality outside the displayed root, not equality of
semantic pairs.

The important point is that repeated gain selection uses the **basic**
live-weighted theorem, not its near-minimum recipient wrapper.  The basic
theorem has no hypothesis that the current whole profile remains close to the
minimum.  At every later nonsingleton routed state,

\[
 LE\le E<\lambda D_*/2\le mD_*/2,
\]

so its tail arm is impossible and some actual endpoint update gains at least

\[
 mD_*/(2|I|)\ge\lambda D_*/8
\]

on `Fin 4`.  Thus accumulation of total debt on the other coordinates does
not invalidate the iteration.

Purifying the four coordinates is also legitimate.  Recompute a best pure
endpoint after every previous update.  Purity, once installed in a coordinate,
is not undone by changing another coordinate.  If routing ever leaves a
singleton, stop.  Otherwise the resulting root is one of the eleven pure
coalitions of ranks two, three, and four.  Every subsequent selected update
has strictly positive gain, hence flips a bit and cannot be a self-loop.
Twelve visited nonsingleton roots contain a repetition.  Since the past and
tail never changed, repeated root equality is equality of the full profiles.

The preliminary purification moves need not be profitable and should not be
listed as edges of the uniformly paid cycle.  Only the final repeated segment
has the common gain floor.

The exact mover-debt identity and the coordinatewise circulation identities
then follow by telescoping.  They do not make the horizontal edges into
Bellman successor edges.

## 2. The `Fin 4` cycle classification is correct

I independently enumerated all simple undirected cycles in the induced
four-cube on the eleven vertices of cardinality at least two.  There are 37
up to rotation and reversal.  None violates

\[
 \bigcap_kQ_k\ne\varnothing
 \quad\lor\quad
 \exists k,\ell:\ |Q_k|=|Q_\ell|=2,
 \ Q_\ell=Q_k^c.
\]

The prose argument in `COMP.md` is sound once two small points are made
explicit.

* A directed two-cycle along one cube edge must be handled separately from
  the usual simple-cycle convention.  Its two adjacent vertices plainly have
  nonempty intersection.
* For length at least four, if no complementary pairs occur, the pair
  vertices are contained in a star or in a triangle.  A triangle of pairs is
  incident to one common triple.  Closing a simple lifted cube cycle through
  all three triangle pairs without an antipodal pair forces repetition of
  that triple or of the full vertex.  Hence only the star survives, and its
  center belongs to every intervening triple and to the full coalition.

An exact negative-boundary example for the common-host conclusion is the
pure cube cycle

\[
 01,012,02,023,23,123,13,013,01.
\]

It has empty total intersection and visits the complementary pairs `01` and
`23` (also `02` and `13`).  A pair--triple directed two-cycle is the elementary
common-host boundary.

## 3. The tail limit is not yet an executable path edge

Stage mass at least `lambda` implies `L_n >= lambda`.  Hence if
`limsup L_n R_n > 0`, a fixed coordinate subsequence yields a fixed positive
literal endpoint gain.  If `L_n R_n -> 0`, then `R_n -> 0`; compactness of the
root and bounded payoff cubes gives a limit satisfying the one-row Bellman
identity and zero coordinate root defects.  The retained root coalition has
mass at least `lambda`, so the limiting root has positive absorption.

This proves an **exact positively absorbing one-row Nash--Bellman datum**.
It does not prove:

* that the limiting tail pair is attained by a behavioral profile;
* punishment-floor admissibility of the current and tail annotations;
* a source-matched exact path edge; or
* a return or terminal equilibrium.

Accordingly, (15) is valid after replacing “exact executable Bellman anchor”
by “exact positively absorbing carrier-level Nash--Bellman datum.”  Section 3
is a useful Research lemma but has no separate export-gate consumer.

## 4. Falsification audit of the periodic two-clock theorem

The theorem is valid provided “periodic executable data” is expanded to the
following exact fields.

1. The roots, candidate prescribed values, candidate nonnegative debts, and
   secants extend `K`-periodically to all natural dates.
2. `p` and `f` are exactly the `prescribedDefect` and
   `directDebtDefect` of `QuittingChronologicalDebtData`.
3. Every secant is the exact generated max-affine secant, with
   `0 <= s <= opponentContinueMass`.
4. The candidate prescribed values and debts are uniformly bounded.
5. The period contraction hypotheses hold for every player.  They may be
   imposed directly on generated secants as in (21), or more strongly on the
   player-deleted Continue clocks.

For a `K`-periodic scalar forcing `a`, put `R=sum_{k<K}a_k` and
`a_k^0=a_k-R/K`.  The zero-sum periodic sequence has every prefix bounded by
`K(A+B)h`.  Since survival weights are nonincreasing, Abel summation gives the
same bound for its infinite weighted sum.  The constant part contributes at
most

\[
 (Bh^2/K)\,K/(\rho h)=(B/\rho)h.
\]

This works from every cyclic starting phase because the period sum and the
product of the `K` scalar discounts are invariant under cyclic rotation.
Applying the estimate to `p` under both clocks and to `f` under the secant
clock gives exactly

\[
 \operatorname{DebtError}_{0,i}
 \le \bigl(2\Psi(A_p,B_p)+\Psi(A_f,B_f)\bigr)h.
\]

Bounded terminal errors vanish under period contraction, and adding the
nonnegative initial candidate debt proves (23).  The resulting bound is
against the unrestricted behavioral cap because the checked generated-secant
identity computes that cap, rather than a stationary or periodic deviation
class.  Terminal approximants for all small `h` then enter the checked fixed-
payoff selection theorem.

### Sharp falsification tests

The `O(h^2)` period-mean hypothesis cannot be weakened to `O(h)`.  In the
scalar recursion with one-turn discount `q=1-rho*h`, constant forcing `a=h`
has Green sum

\[
 \sum_{n\ge0}q^nh=1/\rho,
\]

not `O(h)`.  Likewise, without a strict period contraction, even a nonzero
`O(h^2)` mean is not summably controlled.  These abstract recursions are exact
special cases of the game-independent identity and show that the orders in
(18)--(21) are substantive, not proof artifacts.

An alternating forcing gives the positive cancellation boundary: for
`K=2`, `a_0=h` and `a_1=-h+O(h^2)` have local size `O(h)`, period mean
`O(h^2)`, and an `O(h)` weighted Green sum under a `1-rho*h` period
contraction.

## 5. A closed horizontal cycle does not produce the data of Section 4

Equations (28) only give unweighted closure of the endpoint differences.
They say nothing about a family of small roots, its Bellman derivatives, or
the generated secants.

There is a simple robustness test showing why this is a genuine gap.  A cycle
which stays among pure nonsingleton coalitions only reads rewards at those
nonsingleton vertices.  One may change singleton rewards while preserving all
payoff comparisons and literal profiles on the displayed cycle (within the
strict comparison margins).  But a small-h product-root expansion near all
Continue reads singleton rewards at first order; simultaneous collisions
enter only at quadratic order.  Thus tables with the same horizontal cycle
data can have different, even oppositely oriented, first-order Bellman jets.
The cycle data alone cannot imply (29)--(30).

The exposure hypotheses are independent as well.  A common-host cycle does
not by itself ensure order-h absorption after deleting the common host.  A
realization using only that host at first order can have host-deleted survival
`1-O(h^2)` or exactly one.  A second first-order label must be produced.
Complementary-pair geometry suggests such labels but does not produce their
ordered hazards or the generated-secant contraction.

Therefore (35) is correctly identified as the remaining producer theorem.
It has not been proved or refuted by `COMP.md`.  “Failure of realization must
be converted into support drop” is also an obligation, not a consequence of
finite-dimensional infeasibility unless a separation theorem is supplied and
attached to the checked full-replacement interface.

## 6. The rank re-extraction claim is correctly conditional

The repository does re-extract a complete tangent family at the exact new
base.  The weakest checked theorem requires:

* actual carrier membership of the endpoint;
* equality of its total debt with the old positive minimum;
* no positive debt outside the old active support; and
* vanishing debt at one old active coordinate.

Under those hypotheses,
`exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` gives a new
frontier with strict support inclusion.  The stronger full-replacement
specialization is
`exists_reextractedFrontier_of_minimumFiberEndpoint`.

Thus source regeneration is indeed automatic **after** the minimum-fiber and
no-new-support facts are proved.  Neither fact follows from the endpoint
cycle, so Section 6 must retain those premises.

## 7. Export split

### Packet A: same-stage `Fin 4` endpoint monodromy

**Gate verdict: qualifies after bounded packet repairs.**

This packet should contain Sections 1--2 only, with a precise structure for a
literal cycle and the actual-data adapter from
`quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain` and
`quittingStageCoalitionMass_le_stagePureEndpointRouted`.  It strictly narrows
the named surviving nonsingleton routed-transfer branch to:

* a literal singleton atom of unchanged mass; or
* one of two finite source-closed geometries with a uniform actual gain floor.

Before placement, add the exact pair--triple and complementary-pair boundary
cycles, distinguish purification moves from paid moves, and list the already
checked unrestricted-deviation and routing declarations.  The downstream
consumer remains open and must be stated as such.

### Packet B: periodic two-clock residual shadowing

**Gate verdict: potentially qualifies as a separate proved reduction, but is
not export-ready in the prose form.**

It weakens the live exact-edge/chronological producer target to local `O(h)`
residuals with only `O(h^2)` period mismatch, while preserving an unrestricted-
behavior terminal consumer.  This is analogous in status to the reviewed
summable-seam reduction, rather than an arbitrary-game producer.

To pass the gate, it needs a self-contained structure defining the exact
generated secants and defects, the positive alternating-residual regression
and the two sharp scalar failures above, and a source audit explaining that
`twoDiscountDebtError_eq` is checked but this periodic cancellation adapter is
new.  It should name
`quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
as consumer and explicitly say that no monodromy-to-data adapter is supplied.

### Packet C: tail anchor and capstone

**Gate verdict: do not export.**

Keep the corrected tail-anchor lemma in Research.  Keep (35) as a question or
producer obligation.  Neither currently changes the semantic endpoint.

## Appendix: relation to `FACE_ENLARGE.md`

I separately audited the new face-enlargement note because only its elementary
part is source-independent.

### Elementary claims

The zero-diagonal tightening lemma is correct.  The finite minimax strict-
blocker alternative, the full-support outside-helper inequality, and the
collision-tax inequality are also correct.  In the hard residual, the needed
full-support inequality `Mp >= 0` is already proved privately as
`weighted_normalizedSoloMatrix_nonneg` in
`ThreeCycleLassoHardPrincipalIncidence.lean`; an implementation should expose
or generalize that declaration rather than rederive packet pinning.

The small-h consequences require the harmless boundary qualifications
`C>0` when writing `eta/(2C)` and an explicit definition of the outside
linear term before (18).  If `C=0` and there is no outside mass, the conclusion
is stronger: no positive sufficiently accurate internal step exists.

These elementary results do not presently pass export gate 4.  They are
static supplied blockers with no actual-source adapter or semantic consumer.
They are good Research declarations, not separate export packets yet.

### Literature-dependent equivalence

The identity “completely `S_0` iff semimonotone `E_0`” and Pang's implication
“semimonotone plus `R_0` implies standard `Q`” do yield the claimed
projective-Q-bar equivalence when combined with the checked projective
standard-or-homogeneous split.  However, this part depends on external matrix-
class theorems not currently represented by a checked Lean declaration.  The
2019 semimonotone review supports the complete-`S_0` characterization, while
the cited DOI in the note is not by itself an exact source audit of Pang's
original theorem.  It must be checked against the original theorem and the
repository's LCP sign conventions before export.

If fully sourced, that equivalence is a valid no-go for the proposed
`FaceTangent` enlargement: the requested strict matrix-class example cannot
exist.  It should be a separate matrix-class/no-enlargement packet, not mixed
with the elementary blocker calculations.

### Interaction with the `COMP` capstone

The blocker can constrain a **particular** small-h singleton-face realization:
an internal bad-face clock either uses an order-h outside hazard or pays an
order-h collision correction.  This is relevant to the exposure side of
(35).

It does not yet solve (35).  A same-stage nonsingleton endpoint monodromy does
not choose a principal singleton face, identify its first-order Bellman
linearization with `M_P`, or attach the blocker-selected outside helper to the
literal source.  Those are precisely the missing adapters.  Until they are
proved, `FACE_ENLARGE` is a promising obstruction language for the capstone,
not its producer.
