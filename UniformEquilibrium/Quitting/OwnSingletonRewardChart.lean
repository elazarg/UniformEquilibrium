import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.SimpleBranches
import Mathlib.Topology.Homeomorph.Defs

/-!
# Independent own-singleton and remaining reward coordinates

This is a direct coordinate chart, not an affine recipient-row translation.
Only the displayed own singleton entries depend on the singleton vector.
Never still has its model-defined payoff zero.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

/-- Every terminal recipient coordinate other than that recipient's own singleton. -/
abbrev QuittingFreeRewardCoordinate (ι : Type) [DecidableEq ι] :=
  {point : {S : Finset ι // S.Nonempty} × ι //
    point.1 ≠ quittingSingletonTerminal point.2}

/-- Insert any own-singleton vector without changing a single free reward coordinate. -/
def quittingOwnSingletonReward (singletons : ι → ℝ)
    (coordinates : QuittingFreeRewardCoordinate ι → ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) : ℝ :=
  if h : terminal = quittingSingletonTerminal player then singletons player
  else coordinates ⟨(terminal, player), h⟩

@[simp] theorem quittingOwnSingletonReward_singleton
    (singletons : ι → ℝ) (coordinates : QuittingFreeRewardCoordinate ι → ℝ)
    (player : ι) :
    quittingOwnSingletonReward singletons coordinates
      (quittingSingletonTerminal player) player = singletons player := by
  exact dite_eq_left rfl

@[simp] theorem quittingOwnSingletonReward_free
    (singletons : ι → ℝ) (coordinates : QuittingFreeRewardCoordinate ι → ℝ)
    (coordinate : QuittingFreeRewardCoordinate ι) :
    quittingOwnSingletonReward singletons coordinates
      coordinate.1.1 coordinate.1.2 = coordinates coordinate := by
  exact dite_eq_right coordinate.2

/-- Changing the singleton vector leaves every non-own-singleton entry unchanged. -/
theorem quittingOwnSingletonReward_eq_of_ne_singleton
    (first second : ι → ℝ) (coordinates : QuittingFreeRewardCoordinate ι → ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι)
    (hterminal : terminal ≠ quittingSingletonTerminal player) :
    quittingOwnSingletonReward first coordinates terminal player =
      quittingOwnSingletonReward second coordinates terminal player := by
  simp only [quittingOwnSingletonReward, dite_eq_right hterminal]

/-- Every actual reward table is recovered from its own singletons and free entries. -/
theorem quittingOwnSingletonReward_reconstruct
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingOwnSingletonReward
        (fun player => reward (quittingSingletonTerminal player) player)
        (fun coordinate => reward coordinate.1.1 coordinate.1.2) = reward := by
  funext terminal player
  unfold quittingOwnSingletonReward
  split_ifs with hterminal
  · exact congrArg (fun source => reward source player) hterminal.symm
  · rfl

/-- Joint continuity keeps both the singleton vector and all free entries variable. -/
theorem continuous_quittingOwnSingletonReward_joint :
    Continuous (fun parameters : (ι → ℝ) × (QuittingFreeRewardCoordinate ι → ℝ) =>
      quittingOwnSingletonReward parameters.1 parameters.2) := by
  apply continuous_pi
  intro terminal
  apply continuous_pi
  intro player
  unfold quittingOwnSingletonReward
  by_cases hterminal : terminal = quittingSingletonTerminal player
  · simp only [dite_eq_left hterminal]
    exact (continuous_apply player).comp continuous_fst
  · simp only [dite_eq_right hterminal]
    exact (continuous_apply
      (⟨(terminal, player), hterminal⟩ : QuittingFreeRewardCoordinate ι)).comp continuous_snd

theorem continuous_quittingOwnSingletonReward (singletons : ι → ℝ) :
    Continuous (quittingOwnSingletonReward singletons) :=
  continuous_quittingOwnSingletonReward_joint.comp (continuous_const.prodMk continuous_id)

/-- Varying all own singletons while retaining exactly the same free reward data. -/
theorem continuous_quittingOwnSingletonReward_singletons
    (coordinates : QuittingFreeRewardCoordinate ι → ℝ) :
    Continuous (fun singletons : ι → ℝ => quittingOwnSingletonReward singletons coordinates) :=
  continuous_quittingOwnSingletonReward_joint.comp (continuous_id.prodMk continuous_const)

/-- The whole singleton fiber has exactly the independent free reward coordinates. -/
def quittingOwnSingletonChart (singletons : ι → ℝ) :
    (QuittingFreeRewardCoordinate ι → ℝ) ≃ₜ
      {reward : {S : Finset ι // S.Nonempty} → Payoff ι //
        ∀ player, reward (quittingSingletonTerminal player) player = singletons player} where
  toFun coordinates :=
    ⟨quittingOwnSingletonReward singletons coordinates,
      quittingOwnSingletonReward_singleton singletons coordinates⟩
  invFun reward coordinate := reward.1 coordinate.1.1 coordinate.1.2
  left_inv coordinates := by
    funext coordinate
    exact quittingOwnSingletonReward_free singletons coordinates coordinate
  right_inv reward := by
    apply Subtype.ext
    funext terminal player
    change quittingOwnSingletonReward singletons
      (fun coordinate => reward.1 coordinate.1.1 coordinate.1.2) terminal player = _
    unfold quittingOwnSingletonReward
    split_ifs with hterminal
    · subst terminal
      exact (reward.2 player).symm
    · rfl
  continuous_toFun := (continuous_quittingOwnSingletonReward singletons).subtype_mk _
  continuous_invFun := by
    apply continuous_pi
    intro coordinate
    have hcoordinate : Continuous
        (fun reward : {S : Finset ι // S.Nonempty} → Payoff ι =>
          reward coordinate.1.1 coordinate.1.2) :=
      (continuous_apply coordinate.1.2).comp (continuous_apply coordinate.1.1)
    exact hcoordinate.comp continuous_subtype_val

end GameTheory
