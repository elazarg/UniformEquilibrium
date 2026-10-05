# Independent review of the pair-premium-core completion

Reviewer: CODEX_BORSUK.

Verdict: **PASS, ordinary mathematics, not checked in Lean.** I find no
unresolved mathematical objection to Sections 11–13, with Section 10 as the
strict-leave input, of
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`](../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md).
The conclusion accepted is: every four-player quitting game with
nonnegative own singleton rewards, nonnegative participant premiums, and
greatest premium core of cardinality at most two has one fixed
uniform-equilibrium payoff against all complete behavioral deviations.
The proof is an existence argument through the existing no-equilibrium
polynomial producer, not an executable strategy extraction or coverage of
all finite quitting games.

I read no other reviewer's feedback. I reconstructed the root classification,
orientation, perturbation, and peeling transfer independently, and attempted
exact falsification by preserving a bad core-only root and introducing
positive outsider premiums. The resulting complete test is in
[`CODEX_BORSUK__PREMIUM_CORE_ROOT_SELECTION.md`](../notes/CODEX_BORSUK__PREMIUM_CORE_ROOT_SELECTION.md).
No export, shared index, Lean source, or Git staging state was changed.

## Exact claim and source assumptions

For every nonempty coalition `S`, the reward vector `r(S)` is arbitrary
finite real data subject to `sₖ=rₖ({k})≥0` and `rₖ(S)≥sₖ` for `k∈S`.
A premium trap is a nonempty set `A` such that each `k∈A` has some
`S⊆A`, `k∈S`, with `rₖ(S)>sₖ`. The union of traps is the greatest premium
core. This is a condition on finitely many reward entries, with no strategic
witness in its definition.

The analytic exclusion permits signed singletons and every finite player
set having the indicated pair. Fix an absolute reward bound `M≥0`, a box
radius `B>M`, `K=[−B,B]^I`, the rectangle `D=∏ₖ[sₖ,B]`, and its lower
boundary `L={x∈D: ∃k, xₖ=sₖ}`. It excludes a `C¹` function satisfying
`H(v)−H(T_q(v))≥a(q)` for every boxed annotation and every full exact
product-root Nash equilibrium. An annotation need not be a realizable
continuation. That universal quantifier is exactly what the named
polynomial restriction supplies.

## The finite-game and degree checks

Let `gₖ(q)=Qₖ(q)−Cₖ(q,v)` be the actual multilinear endpoint difference,
extended to all real hazard vectors by its coalition formula. It is
independent of the player's own hazard. The map
`F(q)ₖ=min(1,max(0,qₖ+gₖ(q)))` is continuous on the full ambient space and
maps into the unit cube. Its fixed-point conditions are exactly Nash:
`gₖ≤0` at hazard zero, `gₖ=0` at an interior hazard, and `gₖ≥0` at hazard
one. No fictitious boundary fixed points are introduced.

For core `{i,j}`, put `dᵢ=rᵢ({i,j})−rᵢ({j})>0`, and define `dⱼ`
symmetrically. On the core-only face the actual gap is

    gᵢ = (1−qⱼ)(sᵢ−vᵢ)+qⱼ dᵢ.

If either core annotation is below its singleton, its hazard must be one,
then the other core hazard must be one. A strict passive outsider blocker
rules out this pair independently of the annotation. Thus every full root
has an outsider active in that case.

If both core annotations exceed their singletons, no sole core quitter is
possible. Any core hazard one forces the blocked pure pair. The only
remaining nonzero core-only candidate has

    pᵢ=(vⱼ−sⱼ)/(vⱼ−sⱼ+dⱼ),
    pⱼ=(vᵢ−sᵢ)/(vᵢ−sᵢ+dᵢ).

Both are strictly interior. A coordinate below its singleton rules out
all-Continue. Once outsider ties are removed, either an outsider has
positive gap at `p`, so `p` is not Nash, or every outsider has negative
gap there. In the latter case the clipped outsider rows are identically
zero on a full ambient neighborhood of `p`; the core rows are unclipped.
Consequently the derivative of `q−F(q)`, with the core ordered first, is

    [ 0    −αᵢ    * ]
    [ −αⱼ   0     * ]
    [ 0     0     I ],       αᵢ=vᵢ−sᵢ+dᵢ>0,

and its determinant is `−αᵢαⱼ<0`. Larger-coalition effects occur in the
starred entries and cannot change this determinant. Simultaneously
reordering source and target coordinates introduces no orientation change.

The total degree of `q−F(q)` on `U=(−1,2)^I` is `+1`: the homotopy to
`q−(1/2,…,1/2)` avoids zero on `∂U`, since every image lies in the unit
cube. If `p` were the only fixed point, a sufficiently small ambient
neighborhood would retain the full zero fiber. The invertible derivative
and its small remainder give a zero-free homotopy on that neighborhood's
boundary to the affine derivative field. Excision therefore makes the
total degree equal its local degree `−1`, a contradiction.

This argument remains valid when outsider coordinates of `p` are zero:
`p` is interior to the larger ambient region, and the strictly negative
outsider gaps supply genuine ambient smoothness. There is no half-index
or tacit differentiability of clipping at a tie. A different full Nash
root is therefore produced; it is not assumed as a source field.

## Perturbation and return to the identical boundary

Every exact successor is at least `s` because its Nash value dominates
the Quit endpoint, and every Quit endpoint is at least `s`. Convexity of
the successor formula retains the upper bound `B` and hence puts the
successor in `D`, even when the source lies below some singleton.

At a minimizer `x` of `H` on `L`, a single binding coordinate is
impossible. Its owner can quit at a small positive rate: its own gap is
zero and every other player's gap remains strictly negative by continuity.
The owner's successor coordinate remains its singleton, so this actual
root contradicts minimality on `L`. This works for arbitrary coalition
premiums and for upper-box coordinates.

With at least two bindings, increasing any one binding coordinate leaves
another binding unchanged. Thus the corresponding partial derivatives of
`H` are nonnegative. If a core coordinate binds, lowering all bindings
forces the first root-classification case above. Otherwise keep both core
annotations exactly unchanged. This fixes the unique mixed candidate
`p` and its positive survival probability `c(p)`. For each outsider,
the gap at `p` is affine in its own annotation with coefficient `−c(p)`
and independent of the other outsider annotations. The interval
`0<ηₖ<ε²` therefore contains a tie-avoiding choice, since only one value
is forbidden. This is a legitimate source perturbation inside the original
box; no reward or strategy constraint changes.

The extra perturbations have norm `O(ε²)` for the fixed finite player
set. No continuity of their selection is needed. Differentiability gives

    (H(v_ε)−H(x))/ε → −∑_{k binding} ∂ₖH(x) ≤ 0.

For the selected exact successor `w_ε`, the support argument below gives
`w_ε∈L`, with the original floors and original upper bound. Any lowered
binding coordinate moves upward by at least `ε`. The exact displacement
identity `w_ε−v_ε=a(q_ε)(r̄_ε−v_ε)` bounds this motion by
`(M+B)a(q_ε)`. Hence

    1/(M+B) ≤ (H(v_ε)−H(w_ε))/ε
              ≤ (H(v_ε)−H(x))/ε,

which contradicts the derivative limit. The positive denominator follows
from `B>M≥0`. All perturbed sources have lower clearance at least `B−M`
before perturbation. This verifies the entire limiting argument, not just
an infinitesimal direction with an unproved returning root.

## Premium peeling preserves all larger coalitions

Traps are union-closed because their original witnesses survive unions.
No trap loses its first deleted member in any flat-player deletion order.
Conversely a nonempty terminal residual is itself a trap. Thus every order
ends at the same raw core; these are reward calculations, not deletion of
players from the game. A singleton cannot be a trap, so a core of size at
most two is empty or a pair.

For core `C={i,j}`, every nonempty active support `A≠C` fails to be a
trap: otherwise `A⊆C`, leaving only impossible singleton traps. Therefore
some active member is flat on every participant coalition inside `A`.
Its forced-Quit distribution remains inside `A`, even if other active
players quit surely. Its Quit endpoint equals its singleton, and supported
Quit pins its actual Nash successor there. This returns the full successor
to `L` without suppressing a positive hazard or a larger coalition.

For an outsider `k`, all participant coalitions inside `C∪{k}` are flat
for `k`. A positive premium there, together with the pair witnesses for
`i` and `j`, would make a larger trap. Consequently `Qₖ(p)=sₖ` on the
core-only face, exactly as required for the pure-pair blocker and the
tie-removal formula. Positive premiums involving another outsider remain
allowed and appear in the full map. Its outsider rows are still locally
constant after strict clipping. These two facts prove the transfer.

The strict-leave transfer also checks out: the designated gap rules out
support `C` when that annotation is at least its singleton; every other
support returns by the preceding argument. The singleton-face derivative
inequality then rules out a minimizer binding only the two core players.
Lowering its outsider bindings preserves the required core floor and gives
the same absorption contradiction. The derivative inequality is valid at
multiple face intersections by moving nonowner annotations strictly upward
and passing to the limit; it does not assume small sole-owner roots exist
at the unperturbed intersection.

## Semantic consumer, equality cases, and strategic inputs

For equality in a pair-leave comparison, increase only that player's
passive reward at the other singleton by `δ>0`. No participant premium,
own singleton, trap, or core changes. Strict leave then applies, and the
literal reward-closure theorem returns a fixed target for the original
table. It allows varying nearby targets. Alternatively their boundedness
and a subsequence limit give a fixed target, with at most `δ` error in
each fixed-profile finite-average payoff and `2δ` in deviation gain.
This does not assert closure of the stronger smooth-potential exclusion.

For nonnegative singletons, the unrestricted punishment value is the
singleton: Quit guarantees the lower bound, and all-Never opponents give
the upper bound. This supplies normality. If some singleton is positive,
the literal Fin4 no-uniform-payoff theorem produces a rational polynomial
potential on the full robust relation in the box `M+2`. Its exact-root
restriction has precisely the unit absorption drift excluded above. If
all singletons are zero, all-Never is exact Nash at every horizon: a lone
deviator can receive only its zero singleton or zero Never payoff. The
empty-core case is the existing product-low producer.

There is no unproduced strategic input. Finite-game Nash existence and the
explicit degree argument supply the roots; compact minimization supplies
`x`; the forbidden values supply the tie perturbations; the no-UE theorem
supplies the polynomial under the contradiction hypothesis. The consumed
endpoint already quantifies over every complete behavioral deviation and
one fixed target before accuracy. No repeated-root stationary profile,
public lottery, favorable child equilibrium, or target-dependent horizon
switch is substituted for that endpoint.

## Sources inspected and implementation boundary

The route was chosen through `docs/TOOLKIT.md`. Literal statements and
needed definitions inspected were:

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean` and the terminal
  fixed-target selection statements in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `IsεQuittingRootNash` in `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
  the endpoint definitions, endpoint mixture, and exact Nash equivalence in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`; and
  `exists_isZeroQuittingRootNash` in `UniformEquilibrium/Quitting/Root/NashExistence.lean`.
- `ambientDegree_homotopy` and
  `ambientDegree_affineRootField_eq_sign_det` in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
  `ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`,
  and `ambientDegree_of_selfMap_eq_one` in
  `MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
  `IsQuittingFullExactRootPotential` and
  `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
  and `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.
- `quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`,
  `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`, and
  `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
- `HasFiniteCoalitionSupportPeeling` in
  `MathUE/FiniteCoalitionSupportPeelingOrder.lean`,
  `hasWeakQuittingPremiumSupportPeeling_iff` in
  `UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`,
  `hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative` in
  `UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`,
  and `exists_uniformEquilibriumPayoff_of_productLowPremium` in
  `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.

The affine degree declaration uses its named rectangular local region;
excision transfers the linear field calculation to a smaller ball if a
formalizer follows the manuscript's ball proof. No nonlinear Jacobian-index
theorem was assumed from an absent source.

A narrow overlap search also found current strict-leave source declarations
`exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreExactRootBoundary.lean`,
`not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreSmoothDrift.lean`,
and `exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/Existence/TwoPlayerPremiumCoreUniformPayoff.lean`.
Their literal premises retain strict leave and globally constant outsiders;
they do not subsume the mutual-join producer or greatest-core extension.
Some of these files were concurrent untracked work at inspection, so this
is a static statement comparison, not a certification of build or integration
status. No Lean or Lake command was run.

`Literature/README.md` and the header and relevant clipped-map material in
`Literature/Simon2012.lean` were inspected. No paper theorem is imported as
an unproved premise, and no publication novelty is asserted. The bounded
overlap audit does not claim to exclude every other implemented existence
criterion on every individual table.

The explicit four-player fixture in the owned notebook checks three
failure-prone distinctions: a bad core-only root really exists; a separate
returning root exists at the same annotation; and a root activating both
outsiders may return through the flat outsider while the other receives a
strictly positive participant premium. These tests support, rather than
replace, the complete arguments above.

Remaining request: check the eventual standalone assembly for exact reuse
of this statement and both replacement facts. No mathematical repair to
Sections 11–13 is requested by this review.
