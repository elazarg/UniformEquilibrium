import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteTruncation
import UniformEquilibrium.Quitting.Cycles.PlayerwisePositiveAffinePeriodicBlock
import UniformEquilibrium.Quitting.Terminal.TerminalAffineReward

/-! # Positive-affine paired cycles, truncated afresh after transforming rewards -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

theorem affine_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (hpositive : ∀ player, 0 < q player)
    (scale shift : Payoff ι) (phase : Fin period) (player : ι) :
    value (quittingPlayerwiseAffineReward reward scale shift) schedule q hq phase player =
      scale player * value reward schedule q hq phase player + shift player := by
  have h := quittingCyclicTerminalValue_playerwiseAffine reward scale shift
    (cycle schedule q hq) (cycle_opponents_contract schedule q hq hpositive)
  exact congrFun (congrFun h phase) player

theorem affine_cycle_isZeroRootNash_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (scale shift : Payoff ι) (hscale : ∀ player, 0 < scale player) (phase : Fin period) :
    IsεQuittingRootNash (quittingPlayerwiseAffineReward reward scale shift)
      (value (quittingPlayerwiseAffineReward reward scale shift) schedule q hq
        (finRotate period phase)) 0 (cycle schedule q hq phase) := by
  have hvalue : value (quittingPlayerwiseAffineReward reward scale shift) schedule q hq
      (finRotate period phase) =
      quittingPlayerwiseAffinePayoff scale shift
        (value reward schedule q hq (finRotate period phase)) := by
    funext player
    exact affine_value reward schedule q hq
      (fun player => by linarith [(hinterior player).1]) scale shift _ player
  rw [hvalue]
  exact isZeroQuittingRootNash_playerwiseAffine reward scale shift _ _ hscale
    (cycle_isZeroRootNash_of_selected reward schedule hregion q hq hinterior hzero phase)

/-- A finite pure-date attainer transports affinely because it forces absorption;
no affine translation identity is asserted for the finite prescribed profile. -/
theorem affine_finiteProfile_firstActiveTime_attains
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (scale shift : Payoff ι) (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns)
    (player : ι) :
    quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)
        (Function.update
          (quittingCyclicFiniteProfile (quittingPlayerwiseAffineReward reward scale shift)
            (cycle schedule q hq) initial (turns * period)) player
          (quittingPureTimeBehaviorStrategy (quittingPlayerwiseAffineReward reward scale shift)
            player (some (firstActiveTime schedule initial player)))) player =
      scale player * value reward schedule q hq initial player + shift player := by
  have hprofile :
      quittingCyclicFiniteProfile (quittingPlayerwiseAffineReward reward scale shift)
        (cycle schedule q hq) initial (turns * period) =
      quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period) := by
    funext who time history
    rw [quittingCyclicFiniteProfile_apply, quittingCyclicFiniteProfile_apply]
  rw [hprofile]
  change quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)
    (Function.update (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial
      (turns * period)) player (quittingPureTimeBehaviorStrategy reward player
        (some (firstActiveTime schedule initial player)))) player = _
  rw [quittingTerminalPayoff_finiteTime_playerwiseAffine,
    finiteProfile_firstActiveTime_attains_value reward schedule hregion q hq
      hinterior hzero initial turns hturns player]

/-- Nonnegative transformed singletons ensure that the transformed Never boundary
is dominated. Consequently the fresh transformed truncation has the exact affine cap. -/
theorem affine_finiteProfile_cap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (scale shift : Payoff ι) (hscale : ∀ player, 0 < scale player)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι)
    (hsingleton : 0 ≤ scale player * singleton reward player + shift player) :
    quittingContinuationBestResponseValue (quittingPlayerwiseAffineReward reward scale shift)
        (quittingCyclicFiniteProfile (quittingPlayerwiseAffineReward reward scale shift)
          (cycle schedule q hq) initial (turns * period)) player =
      scale player * value reward schedule q hq initial player + shift player := by
  have hpositive : ∀ player, 0 < q player :=
    fun player => by linarith [(hinterior player).1]
  apply le_antisymm
  · rw [← affine_value reward schedule q hq hpositive scale shift initial player]
    apply quittingContinuationBestResponseValue_cyclicFiniteProfile_le _ _
      (affine_cycle_isZeroRootNash_of_selected reward schedule hregion q hq
        hinterior hzero scale shift hscale)
    change max 0 (scale player * singleton reward player + shift player) ≤
      value (quittingPlayerwiseAffineReward reward scale shift) schedule q hq _ player
    rw [affine_value reward schedule q hq hpositive]
    have hv := (value_bounds_of_selected reward schedule hregion q hq hinterior hzero
      (quittingCyclicOrbit initial (turns * period)) player).1
    have hmul := mul_lt_mul_of_pos_left hv (hscale player)
    apply max_le <;> linarith
  · rw [← affine_finiteProfile_firstActiveTime_attains reward schedule hregion q hq
      hinterior hzero scale shift initial turns hturns player]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue _ _ player _

/-- Fresh truncation has zero Never payoff, so the whole affine cyclic value
is multiplied by the retained absorption factor. -/
theorem affine_finiteProfile_payoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (hpositive : ∀ player, 0 < q player)
    (scale shift : Payoff ι) (initial : Fin period) (turns : ℕ) (player : ι) :
    quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)
        (quittingCyclicFiniteProfile (quittingPlayerwiseAffineReward reward scale shift)
          (cycle schedule q hq) initial (turns * period)) player =
      (1 - jointCycleSurvival q ^ turns) *
        (scale player * value reward schedule q hq initial player + shift player) := by
  rw [finiteProfile_payoff_eq, affine_value reward schedule q hq hpositive]

/-- The fresh transformed truncation has exact debt equal to cycle survival
times the transformed infinite value, including the transformed shift. -/
theorem affine_finiteProfile_debt_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (scale shift : Payoff ι) (hscale : ∀ player, 0 < scale player)
    (initial : Fin period) (turns : ℕ) (hturns : 1 ≤ turns) (player : ι)
    (hsingleton : 0 ≤ scale player * singleton reward player + shift player) :
    quittingTerminalDeviationDebt (quittingPlayerwiseAffineReward reward scale shift)
        (quittingCyclicFiniteProfile (quittingPlayerwiseAffineReward reward scale shift)
          (cycle schedule q hq) initial (turns * period)) player =
      jointCycleSurvival q ^ turns *
        (scale player * value reward schedule q hq initial player + shift player) := by
  rw [quittingTerminalDeviationDebt,
    affine_finiteProfile_cap_eq reward schedule hregion q hq hinterior hzero
      scale shift hscale initial turns hturns player hsingleton,
    affine_finiteProfile_payoff_eq reward schedule q hq
      (fun player => by linarith [(hinterior player).1])]
  ring

end GameTheory.PairedCycle
