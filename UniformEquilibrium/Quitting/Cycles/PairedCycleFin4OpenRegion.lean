import UniformEquilibrium.Quitting.Cycles.PairedCycleOpenRegion
import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Chart
import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Repair

/-! # A nonempty open canonical 56-coordinate paired finite-selector region -/

noncomputable section

namespace GameTheory.PairedCycle

def fin4CenterCoordinates (coordinate : Fin4FreeRewardCoordinate) : ℝ :=
  centerReward fin4Schedule coordinate.1.1 coordinate.1.2 -
    if coordinate.1.2 = 0 then 0 else 1

theorem fin4OriginalReward_center :
    fin4OriginalReward fin4CenterCoordinates = centerReward fin4Schedule := by
  funext terminal player
  by_cases h : terminal = quittingSingletonTerminal player
  · subst terminal
    change singleton (fin4OriginalReward fin4CenterCoordinates) player =
      singleton (centerReward fin4Schedule) player
    rw [fin4OriginalReward_singleton, (centerReward_own fin4Schedule player).1]
  · simp [fin4OriginalReward, fin4CanonicalReward, h, fin4CenterCoordinates]

/-- The original own singletons stay fixed at one; every other coordinate
varies freely subject only to the literal strict paired inequalities. -/
def fin4StrictCoordinates : Set (Fin4FreeRewardCoordinate → ℝ) :=
  {coordinates | StrictRawRegion (fin4OriginalReward coordinates) fin4Schedule}

theorem fin4StrictCoordinates_nonempty : fin4StrictCoordinates.Nonempty := by
  refine ⟨fin4CenterCoordinates, ?_⟩
  change StrictRawRegion (fin4OriginalReward fin4CenterCoordinates) fin4Schedule
  rw [fin4OriginalReward_center]
  exact centerReward_strictRawRegion fin4Schedule

theorem isOpen_fin4StrictCoordinates : IsOpen fin4StrictCoordinates :=
  (isOpen_strictRawRegion fin4Schedule).preimage continuous_fin4OriginalReward

/-- Openness here is in the canonical singleton affine space, not in the
ambient space where its four fixed singleton coordinates could vary. -/
def fin4CanonicalStrictRegion :
    Set {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) //
      IsSinglePivotSingletonTable reward 0} :=
  fin4CanonicalChart '' fin4StrictCoordinates

theorem fin4CanonicalStrictRegion_nonempty_open :
    fin4CanonicalStrictRegion.Nonempty ∧ IsOpen fin4CanonicalStrictRegion := by
  exact ⟨fin4StrictCoordinates_nonempty.image fin4CanonicalChart,
    fin4CanonicalChart.isOpenMap _ isOpen_fin4StrictCoordinates⟩

/-- Every point in the open canonical chart is the literal pivot transform
of a strict raw paired table with all four original own singletons equal to one. -/
theorem exists_raw_source_of_mem_fin4CanonicalStrictRegion
    {reward : {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) //
      IsSinglePivotSingletonTable reward 0}}
    (hmem : reward ∈ fin4CanonicalStrictRegion) :
    ∃ original : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4),
      (∀ player, singleton original player = 1) ∧ StrictRawRegion original fin4Schedule ∧
      fin4PivotReward original = reward.1 := by
  obtain ⟨coordinates, hcoordinates, rfl⟩ := hmem
  exact ⟨fin4OriginalReward coordinates, fin4OriginalReward_singleton coordinates,
    hcoordinates, fin4PivotReward_original coordinates⟩

/-- The open chart consists of actual small-pivot-repair sources, by the
same paired menu-family producer used for every raw-region table. -/
theorem hasSmallPivotRepairValue_of_mem_fin4CanonicalStrictRegion
    {reward : {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) //
      IsSinglePivotSingletonTable reward 0}}
    (hmem : reward ∈ fin4CanonicalStrictRegion) :
    HasQuittingSmallPivotRepairValue reward.1 0 := by
  obtain ⟨original, _, hregion, hreward⟩ :=
    exists_raw_source_of_mem_fin4CanonicalStrictRegion hmem
  rw [← hreward]
  exact hasSmallPivotRepairValue_fin4PivotReward_of_rawRegion original hregion.rawRegion

end GameTheory.PairedCycle
