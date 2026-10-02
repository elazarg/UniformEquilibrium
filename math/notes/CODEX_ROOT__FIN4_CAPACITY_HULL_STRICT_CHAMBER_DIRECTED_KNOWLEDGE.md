# Fin4 capacity, law-tight hull, and strict-chamber directed knowledge

## Purpose and status

This note records the exact production boundary after the unbounded-capacity
and law-tight saturation work.  Lean declarations and the living production
documentation remain the sources of truth.  The note does not add a theorem,
promote a Research declaration, or turn a carrier-level chamber into a
behavioral consumer.

The headline strict-classification status is:

- **M:** the dimension-free classification and its Fin4 specialization have
  rigorous proofs;
- **L:** the declarations are integrated in production and covered by
  `AxiomAudit.lean`;
- **A:** the Fin4 no-uniform-payoff theorem supplies one origin, positive hull
  minimum, and retained positive finite atom to the generic classifier; and
- **C:** absent.  None of the three returned chambers is consumed into a
  contradiction, terminal approximate equilibria, or a uniform-equilibrium
  payoff.

## Exact production ledger

### Unbounded exact-block hazard capacity

Commit
`e509d5c355a98afa361ff3b8688ba355b4aa278b`
(`Close unbounded hazard capacity branches`) integrates the following chain.

- `exists_summableResidualNashBellmanSpine_of_unboundedCapacity`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualNashBellmanSpine.lean`)
  extracts arbitrarily small summable Bellman and Nash residuals, with at
  least one persistent marginal label, from unbounded finite exact-block
  hazard capacity in a supplied compact carrier.
- `QuittingSummableResidualNashBellmanSpine.exists_uniformEquilibriumPayoff_of_twoPersistent`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/SummableResidualPersistentClosure.lean`)
  consumes the two-persistent-label arm.
- `exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity_of_allNormal`
  (`UniformEquilibrium/Quitting/Classification/Existence/AllNormalUnboundedExactBlockHazardCapacity.lean`)
  consumes the unique-persistent arm under literal all-player punishment
  normality.
- `finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity`
  and
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`)
  give the direct Fin4 consumer and its counterexample-side contrapositive.

This layer has **M**, **L**, and a capacity-conditional **C**.  It has no **A**
producing unbounded exact-block capacity from an AGKRS source or from one
literal source trace.  The Fin4 contrapositive is checked, but supplies only
`BddAbove` boundedness of the relevant exact-block charges, not an explicit
numerical capacity bound.

### Law-tight saturation hull

Commit
`a6d9376bc90ce1934fe1086aefb827207f7ecfc3`
(`Construct law-tight cap-Nash saturation hull`) adds
`IsQuittingLawTightCapNashInvariant`,
`quittingLawTightCapNashSaturationHull`, and
`exists_quittingLawTightCapNashSaturationHull_minimum_retaining_atom`
in
`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`.

The hull is a subset of the joint semantic/law carrier only when its supplied
origin lies in that carrier.  It is closed under exact cap-Nash prefixes and
under debt-nonincreasing replacement in the same terminal-law fibre.  A
positive global debt floor and a positive origin atom give a compact minimum
retaining a quantitative amount of that atom.  The generic module has **M**
and **L**; by itself it does not select the origin, floor, or atom and has no
behavioral consumer.

### Minimum equality level and absorption budget

Commit
`351bd82d5299158858819171d6e690ced5f69d5a`
(`Add cap-Nash minimum face and absorption budget`) adds
`IsQuittingLawTightCapNashSaturationMinimum` and
`quittingLawTightCapNashSaturationMinimumFace` in
`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`.
Here “face” means the minimum equality level set; no convexity is asserted.

The principal literal consequences are:

- `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`;
- `quittingLawTightCapNashSaturationMinimumFace_allContinue_prefix_eq`;
- `quittingLawTightCapNashSaturationHull_rootAbsorptionMass_le_debtExcess_div`;
- `sum_quittingRootAbsorptionMass_le_hullDebtDrop_div_minimum`; and
- `sum_quittingRootAbsorptionMass_le_initialHullDebtExcess_div_minimum`.

Thus finite exact-prefix absorption is charged to debt above the positive
hull minimum.  This is an exact finite-chain budget, not a source-trace
capacity theorem, an infinite chronology, or a renewable rank.

### Singleton/Never cap tightness

Commit
`331ae50a0a1d595a976ce87a215da6c0e7657de3`
(`Formalize singleton-Never cap tightness`) integrates the low collision-sign
API in
`UniformEquilibrium/Quitting/Punishment/SingletonCapBindingCollision.lean`
and the behavioral law calculation in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonNeverCapTightness.lean`.

The key declarations are
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`,
`one_sub_neverMass_mul_opponentNeverProduct_le_singletonOutcomeMass`, and
`terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward`.
The last theorem uses one common carrier-realizing sequence and quantitative
immediate-Quit and Never deviation bounds.  It does not assert that an
arbitrary semantic/law point is attained by one behavioral profile.

These declarations have **M** and **L**.  The strict classifier below is a
checked downstream use of them, but it does not turn their output into a
uniform-payoff consumer.

### Strict minimum classification and Fin4 source

Commit
`fe12b32b6df5210eabe59d0ca11cba54c77b1ea1`
(`Classify strict law-tight saturation minima`) integrates
`lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`
in
`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`
and the Fin4 source declarations
`exists_finFourLawTightSaturationMinimum_of_no_uniformPayoff` and
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.

The generic theorem is dimension-free.  The Fin4 theorem supplies the same
origin, hull minimum, globally minimal semantic source, and positive finite
atom throughout the construction.  It gives **M**, **L**, and source **A**,
but no chamber consumer **C**.

## The three current chambers

For a supplied positive law-tight minimum-face point retaining a positive
finite atom, the following exhaustive disjunction is checked.

1. **Full debt support.** Every player's terminal semantic debt is strictly
   positive.  This is a literal sign arm, not a persistent-clock or behavioral
   chronology.
2. **Reset-rigid same-law return.** `QuittingLawTightResetRigidChamber`
   records a zero-debt owner, a distinct positive-incidence opponent, the
   checked fixed-law reset dispatch, and a returned point on the same minimum
   equality level with the same terminal law.  Minimum debt excludes the
   dispatch's absorbing dynamic exit, so all Continue fixes the returned
   point.  The same-law return does not preserve stopping dates or give a
   repeatable source transition, an admissible return cycle, or a renewable
   rank.
3. **Singleton/Never binding cycle.** `QuittingSingletonNeverBindingCycleChamber`
   records a unique zero-debt owner, a positive singleton mass with the
   complementary Never mass, exact binding of the owner's cap to its
   singleton reward, uniqueness of the all-Continue exact root, and a finite
   directed binding-collision cycle of period at least two.  The cycle need
   not contain the original zero-debt owner and is not an actual temporal
   cycle or a positive admissible payoff return.

No theorem currently selects a behavioral realization of the minimum point
and consumes any one of these arms.  In particular, the classification is not
a terminal trichotomy for the Fin4 conjecture.

## The bounded-capacity frontier

The unbounded exact-block branch is closed.  Therefore a hypothetical Fin4
counterexample satisfies
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in the canonical compact reward box.  What remains is genuinely the bounded
branch:

- no explicit uniform numerical charge bound is extracted;
- exact-block capacity is not identified with capacity along one actual
  source trace;
- no theorem attaches arbitrarily useful bounded blocks to the AGKRS
  approximate-equilibrium source; and
- the law-tight finite absorption budget is not a replacement for such a
  source adapter.

The maintained source questions are
[nonzero-persistent exact-spine selection](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md)
and
[an approximate forward packet or source-derived capacity barrier](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md).
The canonical all-Continue phantom spine remains the basic regression against
source-free spine selection.

## Post-mark two-cut and renewable-source boundary

The law-tight reset arm is not the missing post-mark chronology.  The open
[post-mark two-cut and renewable child-source question](../questions/FIN4_POST_MARK_TWO_CUT_RENEWABLE_CHILD_SOURCE.md)
requires two cuts in one literal post-mark continuation, positive parent
reach, a hazard floor between those cuts, and reconstruction of a complete
same-witness child source.  None of those requirements follows from equality
of terminal laws at a carrier-level reset.

The canonical endpoint renewal branch itself has a checked Research-level
finite rank once a complete renewable node has already been supplied:
`canonicalPairRenewableTransitionRel_wellFounded`,
`FinFourRenewableTrace.descentCount_le_three`, and
`CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_renewalCertificate`
live under `Research/Quitting/FinFourProducerAtlas/`.  This Research surface
is outside the production axiom audit.  Its exact status and terminal boundary
are summarized in
[the renewable canonical support handoff note](CODEX_ROOT__RESOLVED_FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md).

The renewal result does not produce the uniformly reached post-mark two-cut,
does not identify the next packet rank with a later date of the same profile,
and does not consume its three terminal exits.  Those exits remain the
[renewal terminal-exit question](../questions/FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md).

## Plateau moat: stronger source, still a no-go

The source premise proposed in
`FIN4_STRICT_MINIMUM_PLATEAU_RESTART_MOAT.md` is already supplied in stronger
production form by
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.
The finite-path consequences
`anchoredPath_terminal_not_mem_of_positiveAbsorption`,
`le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin`, and
`exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue` are in
`UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`.

The packet's compact-set/open-set uniform moat, finite marked-crossing
corollary, and one-block hazard floor are useful proposed wrapper targets, but
they are not production declarations.  Their mathematical role is only an
obstruction to summable metric restart seams.  They do not identify the
plateau segment with the newly selected law-tight minimum, source-match a
restart chronology, consume a strict chamber, or prove a uniform payoff.  A
separately selected stronger plateau source cannot silently be substituted
for the same-point data of the law-tight classification.

## Checked AGKRS chronological work

The production chronological limit already has:

- `ChronologicalLimit.isAbsorptionPath` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalA4.lean`;
- `ChronologicalLimit.jumpPerfect` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalJumpPerfection.lean`;
  and
- `ChronologicalLimit.singletonReward_le_absorptionPathPayoff` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalSingletonLowerBound.lean`.

The positive-rate upper inequality
`absorptionPathPayoff_le_singletonReward_of_pathRightDerivative_pos` and the
resulting equality
`absorptionPathPayoff_eq_singletonReward_of_pathRightDerivative_pos` at a
nonterminal path time with positive singleton right derivative are checked in
`UniformEquilibrium/Quitting/AbsorptionPath/`
`RootSequenceAbsorbingCompletionChronologicalPositiveSingletonRate.lean`.

The checked table theorem
`QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
proves the forward S.1/S.2/S.3 trichotomy from arbitrary-behavior approximate
equilibria.  The corrected-Simon factorization survives only as an
[archived alternative architecture](../archive/AGKRS_CORRECTED_SIMON_ROUTE_SOURCE_COMPACTIFICATION.md).
The direct production theorem already proves the AGKRS forward result, so the
selector/compactification architecture is not an active Fin4 or AGKRS gap.

## Export-packet freshness

- [UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md](../formalized/UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md)
  is stale as an implementation handoff: its repaired mathematical compiler,
  persistent-label consumers, Fin4 specialization, and bounded-capacity
  contrapositive are now production declarations at commit `e509d5c3`.
  The packet remains useful as proof provenance, not as the live theorem
  inventory.
- [LAW_TIGHT_CAP_NASH_SATURATION_HULL.md](../revisit/LAW_TIGHT_CAP_NASH_SATURATION_HULL.md)
  is partially stale.  The generic hull, minimum equality level, absorption
  budgets, singleton/Never cap-tightness ingredient, strict three-form
  classifier, and Fin4 no-uniform-payoff source are now production.  Its
  numerical same-point regeneration split and any downstream consumption of
  the three chambers are not supplied by the current production capstones.

Neither packet should be edited or deleted merely because part of its handoff
has landed; this note records the divergence between packet prose and the
current declaration surface.
