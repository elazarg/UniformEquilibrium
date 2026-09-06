import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Root.PlayerwiseUnitNormalization

/-! # Product-low quitting premiums -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every absorbing independent product root has an active coordinate whose
pure-Quit payoff is at most its own singleton reward. -/
def HasProductLowQuittingPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ root : ι → PMF Bool, 0 < quittingRootAbsorptionMass root →
    ∃ player, 0 < (root player true).toReal ∧
      quittingRootQuitPayoff reward 0 root player ≤
        reward (quittingSingletonTerminal player) player

/-- Pure-Quit payoffs transform affinely because forcing Quit guarantees
immediate absorption, so the continuation annotation is irrelevant. -/
theorem quittingRootQuitPayoff_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale shift : Payoff ι) (root : ι → PMF Bool) (player : ι) :
    quittingRootQuitPayoff
        (quittingPlayerwiseAffineReward reward scale shift) 0 root player =
      scale player * quittingRootQuitPayoff reward 0 root player +
        shift player := by
  rw [quittingRootQuitPayoff_continuation_invariant
    (quittingPlayerwiseAffineReward reward scale shift) 0
    (quittingPlayerwiseAffinePayoff scale shift 0) root player]
  change quittingRootSuccessorPayoff
      (quittingPlayerwiseAffineReward reward scale shift)
      (quittingPlayerwiseAffinePayoff scale shift 0)
      (Function.update root player (PMF.pure true)) player = _
  rw [quittingRootSuccessorPayoff_playerwiseAffine]
  rfl

/-- Product-low premiums are preserved by nonnegative playerwise affine
changes of terminal rewards. -/
theorem hasProductLowQuittingPremium_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale shift : Payoff ι) (hscale : ∀ player, 0 ≤ scale player)
    (hlow : HasProductLowQuittingPremium reward) :
    HasProductLowQuittingPremium
      (quittingPlayerwiseAffineReward reward scale shift) := by
  intro root habsorption
  obtain ⟨player, hactive, hquit⟩ := hlow root habsorption
  refine ⟨player, hactive, ?_⟩
  rw [quittingRootQuitPayoff_playerwiseAffine]
  simp only [quittingPlayerwiseAffineReward]
  have hmul := mul_le_mul_of_nonneg_left hquit (hscale player)
  linarith

/-- The shifted playerwise unit normalization preserves product-low
premiums whenever all shifted singleton scales are positive. -/
theorem hasProductLowQuittingPremium_playerwiseUnitNormalization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {shift : ℝ} (hshift : 0 < shift)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hlow : HasProductLowQuittingPremium reward) :
    HasProductLowQuittingPremium
      (quittingPlayerwiseUnitNormalization reward shift) := by
  let scale : Payoff ι := fun player =>
    (reward (quittingSingletonTerminal player) player + shift)⁻¹
  let translated : Payoff ι := fun player => shift * scale player
  have hscale : ∀ player, 0 < scale player := fun player => by
    dsimp only [scale]
    exact inv_pos.mpr (add_pos_of_nonneg_of_pos
      (hsingleton player) hshift)
  have hnormalized : quittingPlayerwiseUnitNormalization reward shift =
      quittingPlayerwiseAffineReward reward scale translated := by
    funext terminal player
    dsimp only [quittingPlayerwiseUnitNormalization,
      quittingPlayerwiseAffineReward, scale, translated]
    rw [div_eq_mul_inv]
    ring
  rw [hnormalized]
  exact hasProductLowQuittingPremium_playerwiseAffine
    reward scale translated (fun player => (hscale player).le) hlow

/-- Unit singleton rewards identify product-low premiums with the canonical
low-active-root hypothesis used by the periodic source producer. -/
theorem hasLowActiveQuittingRootQuitPayoff_iff_productLow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    HasLowActiveQuittingRootQuitPayoff reward ↔
      HasProductLowQuittingPremium reward := by
  constructor
  · intro hlow root habsorption
    obtain ⟨player, hactive, hquit⟩ := hlow root habsorption
    have hunit' := hunit player
    rw [quittingSoloReward_self] at hunit'
    refine ⟨player, hactive, ?_⟩
    rw [hunit']
    exact hquit
  · intro hlow root habsorption
    obtain ⟨player, hactive, hquit⟩ := hlow root habsorption
    have hunit' := hunit player
    rw [quittingSoloReward_self] at hunit'
    refine ⟨player, hactive, ?_⟩
    rw [← hunit']
    exact hquit

end GameTheory
