import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Pivot
import Mathlib.Topology.Homeomorph.Defs

/-! # The full 56-coordinate canonical Fin4 reward chart -/

noncomputable section

namespace GameTheory.PairedCycle

/-- All reward entries except the four own-singleton coordinates. -/
abbrev Fin4FreeRewardCoordinate :=
  {point : {S : Finset (Fin 4) // S.Nonempty} × Fin 4 //
    point.1 ≠ quittingSingletonTerminal point.2}

theorem card_fin4FreeRewardCoordinate : Fintype.card Fin4FreeRewardCoordinate = 56 := by
  decide

/-- Every free coordinate is independent; only the canonical own singletons are fixed. -/
def fin4CanonicalReward (coordinates : Fin4FreeRewardCoordinate → ℝ)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) : ℝ :=
  if h : terminal = quittingSingletonTerminal player then (if player = 0 then 1 else 0)
  else coordinates ⟨(terminal, player), h⟩

theorem fin4CanonicalReward_singleton (coordinates : Fin4FreeRewardCoordinate → ℝ) :
    IsSinglePivotSingletonTable (fin4CanonicalReward coordinates) 0 := by
  intro player
  simp [fin4CanonicalReward]

theorem continuous_fin4CanonicalReward : Continuous fin4CanonicalReward := by
  apply continuous_pi
  intro terminal
  apply continuous_pi
  intro player
  unfold fin4CanonicalReward
  by_cases h : terminal = quittingSingletonTerminal player
  · simp only [dif_pos h]
    exact continuous_const
  · simp only [dif_neg h]
    exact (continuous_apply (⟨(terminal, player), h⟩ : Fin4FreeRewardCoordinate) :
      Continuous (fun coordinates : Fin4FreeRewardCoordinate → ℝ =>
        coordinates ⟨(terminal, player), h⟩))

/-- The canonical affine reward space has precisely 56 freely varying real coordinates. -/
def fin4CanonicalChart : (Fin4FreeRewardCoordinate → ℝ) ≃ₜ
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) //
      IsSinglePivotSingletonTable reward 0} where
  toFun coordinates := ⟨fin4CanonicalReward coordinates, fin4CanonicalReward_singleton coordinates⟩
  invFun reward coordinate := reward.1 coordinate.1.1 coordinate.1.2
  left_inv coordinates := by
    funext coordinate
    exact dif_neg coordinate.2
  right_inv reward := by
    apply Subtype.ext
    funext terminal player
    change fin4CanonicalReward (fun coordinate => reward.1 coordinate.1.1 coordinate.1.2)
      terminal player = reward.1 terminal player
    unfold fin4CanonicalReward
    by_cases h : terminal = quittingSingletonTerminal player
    · subst terminal
      rw [dif_pos rfl]
      exact (reward.2 player).symm
    · exact dif_neg h
  continuous_toFun := continuous_fin4CanonicalReward.subtype_mk _
  continuous_invFun := by
    apply continuous_pi
    intro coordinate
    have hcoordinate : Continuous (fun reward : {S : Finset (Fin 4) // S.Nonempty} →
        Payoff (Fin 4) => reward coordinate.1.1 coordinate.1.2) :=
      (continuous_apply coordinate.1.2).comp (continuous_apply coordinate.1.1)
    exact hcoordinate.comp continuous_subtype_val

/-- In the original chart all own singletons are one. The canonical chart is
recovered by shifting nonpivot columns down by one, with no rescaling there. -/
def fin4OriginalReward (coordinates : Fin4FreeRewardCoordinate → ℝ)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) : ℝ :=
  fin4CanonicalReward coordinates terminal player + if player = 0 then 0 else 1

theorem fin4OriginalReward_singleton (coordinates : Fin4FreeRewardCoordinate → ℝ)
    (player : Fin 4) : singleton (fin4OriginalReward coordinates) player = 1 := by
  unfold singleton fin4OriginalReward
  rw [fin4CanonicalReward_singleton]
  split_ifs <;> norm_num

theorem fin4PivotReward_original (coordinates : Fin4FreeRewardCoordinate → ℝ) :
    fin4PivotReward (fin4OriginalReward coordinates) = fin4CanonicalReward coordinates := by
  funext terminal player
  rw [fin4PivotReward_apply, fin4OriginalReward_singleton, fin4OriginalReward_singleton]
  unfold fin4OriginalReward
  split_ifs <;> simp

theorem continuous_fin4OriginalReward : Continuous fin4OriginalReward := by
  apply continuous_pi
  intro terminal
  apply continuous_pi
  intro player
  exact (((continuous_apply player).comp (continuous_apply terminal)).comp
    continuous_fin4CanonicalReward).add continuous_const

end GameTheory.PairedCycle
