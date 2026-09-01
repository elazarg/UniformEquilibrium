import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairCommonPrefixResponse
import Research.Quitting.FinFourProducerAtlas.PairedSameResidualSourceRegeneration

/-!
# Same-residual regeneration after a moving-pair support contraction

The copied target profiles eventually retain a uniform marked atom.  Dropping
that finite initial segment produces the literal paired-family input for the
existing same-residual regeneration theorem.  The one-use strict-support edge
is retained separately from the regenerated source's internal chronology.

This module is conditional on the supplied moving marked-pair family.  It does
not construct that family or assert renewal, a terminal alternative, or a
uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {moving : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual moving}
  {minimum : FinFourMovingMarkedPairMinimumApproach residual}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification :
    FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1}

/-- The cofinal tail selector which discards a finite initial segment. -/
def finFourMovingMarkedPairTailSelector (start rank : ℕ) : ℕ :=
  start + rank

/-- A finite shift is a strict cofinal selector. -/
theorem finFourMovingMarkedPairTailSelector_strictMono (start : ℕ) :
    StrictMono (finFourMovingMarkedPairTailSelector start) := by
  intro first second hlt
  exact Nat.add_lt_add_left hlt start

/-- A regenerated source at the strict-support child, together with the
separate one-use support-contraction edge which led to it. -/
structure FinFourMovingMarkedPairSameResidualSupportDescent
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) where
  tailStart : ℕ
  pairedData : FinFourPairedMinimumSourceData source
  pairedData_targetPoint_eq : pairedData.targetPoint = compactification.targetPoint
  pairedData_terminal_eq : pairedData.terminal = moving.labels.targetTerminal
  pairedData_sourceProfiles_eq :
    pairedData.sourceProfiles = common.chordPrefixedProfile
  pairedData_targetProfiles_eq :
    pairedData.targetProfiles = common.targetPrefixedProfile
  pairedData_selector_eq : pairedData.selector =
    finFourMovingMarkedPairTailSelector tailStart
  pairedData_mover_eq : pairedData.mover = moving.labels.mover
  pairedData_response_eq : pairedData.response =
    fun rank ↦ common.targetPrefixedProfile rank moving.labels.mover
  pairedData_mark_eq : pairedData.mark = common.shiftedMark
  pairedData_massFloor_eq : pairedData.massFloor = moving.reachFloor / 2
  regeneration : FinFourPairedSameResidualSourceRegeneration pairedData
  strictSupport :
    quittingPositiveDebtSupport compactification.targetPoint.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1

namespace FinFourMovingMarkedPairSameResidualSupportDescent

/-- The regenerated producer has exactly the incoming residual. -/
@[simp] theorem regenerated_residual_eq
    {common : FinFourMovingMarkedPairCommonPrefixResponse compactification}
    (descent : FinFourMovingMarkedPairSameResidualSupportDescent common) :
    descent.regeneration.next.residual = source.residual :=
  descent.regeneration.next_residual_eq

/-- The regenerated producer is based at the strict-support target point. -/
theorem regenerated_point_eq
    {common : FinFourMovingMarkedPairCommonPrefixResponse compactification}
    (descent : FinFourMovingMarkedPairSameResidualSupportDescent common) :
    descent.regeneration.next.point = compactification.targetPoint := by
  rw [descent.regeneration.next_point_eq,
    descent.pairedData_targetPoint_eq]

/-- The regenerated target support is nonempty. -/
theorem targetSupport_nonempty
    {common : FinFourMovingMarkedPairCommonPrefixResponse compactification}
    (_descent : FinFourMovingMarkedPairSameResidualSupportDescent common) :
    (quittingPositiveDebtSupport compactification.targetPoint.1).Nonempty :=
  compactification.targetSupport_nonempty_and_card_le_three.1

/-- The regenerated target support has at most three players. -/
theorem targetSupport_card_le_three
    {common : FinFourMovingMarkedPairCommonPrefixResponse compactification}
    (_descent : FinFourMovingMarkedPairSameResidualSupportDescent common) :
    (quittingPositiveDebtSupport compactification.targetPoint.1).card ≤ 3 :=
  compactification.targetSupport_nonempty_and_card_le_three.2

end FinFourMovingMarkedPairSameResidualSupportDescent

/-- The common-prefix target family regenerates a complete minimum source at
the strict-support child without changing the hard residual. -/
theorem nonempty_finFourMovingMarkedPairSameResidualSupportDescent
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Nonempty (FinFourMovingMarkedPairSameResidualSupportDescent common) := by
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    common.eventually_half_reachFloor_le_targetPrefixed_shiftedMark_mass
  let selector := finFourMovingMarkedPairTailSelector start
  have hselector : StrictMono selector :=
    finFourMovingMarkedPairTailSelector_strictMono start
  let paired : FinFourPairedMinimumSourceData source := {
    targetPoint := compactification.targetPoint
    targetPoint_mem := compactification.targetPoint_mem
    targetDebtSum_eq_source :=
      compactification.target_and_chord_debtSum_eq_source.1
    terminal := moving.labels.targetTerminal
    sourceProfiles := common.chordPrefixedProfile
    targetProfiles := common.targetPrefixedProfile
    selector := selector
    selector_strictMono := hselector
    mover := moving.labels.mover
    response := fun rank ↦ common.targetPrefixedProfile rank moving.labels.mover
    target_eq_update := fun rank ↦ common.targetPrefixed_eq_update (selector rank)
    mark := common.shiftedMark
    massFloor := moving.reachFloor / 2
    massFloor_pos := half_pos moving.reachFloor_pos
    marked_mass_floor := by
      intro rank
      exact hstart (selector rank) (by
        dsimp only [selector, finFourMovingMarkedPairTailSelector]
        omega)
    target_tendsto := by
      simpa only [Function.comp_def] using
        common.targetPrefixed_tendsto.comp hselector.tendsto_atTop
  }
  obtain ⟨regeneration⟩ :=
    nonempty_finFourPairedSameResidualSourceRegeneration paired
  exact ⟨{
    tailStart := start
    pairedData := paired
    pairedData_targetPoint_eq := rfl
    pairedData_terminal_eq := rfl
    pairedData_sourceProfiles_eq := rfl
    pairedData_targetProfiles_eq := rfl
    pairedData_selector_eq := rfl
    pairedData_mover_eq := rfl
    pairedData_response_eq := rfl
    pairedData_mark_eq := rfl
    pairedData_massFloor_eq := rfl
    regeneration := regeneration
    strictSupport := compactification.targetSupport_ssubset_chordSupport
  }⟩

end GameTheory
