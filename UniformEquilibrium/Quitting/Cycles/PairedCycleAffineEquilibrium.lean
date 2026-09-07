import UniformEquilibrium.Quitting.Cycles.PairedCycleAffineTruncation

/-! # The actual affine-transformed infinite paired-cycle equilibrium -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

/-- The very same cyclic roots are exact terminal Nash at every literal live suffix
in every positive playerwise affine reward table. -/
theorem affine_allSuffix_isExactNash_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (scale shift : Payoff ι) (hscale : ∀ player, 0 < scale player)
    (initial : Fin period) (start : ℕ) :
    (quittingGame (quittingPlayerwiseAffineReward reward scale shift)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)) 0
      (quittingRootSequenceProfile (quittingPlayerwiseAffineReward reward scale shift)
        (quittingCyclicRootSequence (cycle schedule q hq) initial) start) := by
  rw [rootSequenceProfile_cyclic_suffix]
  exact isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate
    (quittingPlayerwiseAffineReward reward scale shift) (cycle schedule q hq)
    (value (quittingPlayerwiseAffineReward reward scale shift) schedule q hq) _
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff _ _)
    (affine_cycle_isZeroRootNash_of_selected reward schedule hregion q hq
      hinterior hzero scale shift hscale)
    (cycle_opponents_contract schedule q hq
      (fun player => by linarith [(hinterior player).1]))

/-- The fixed transformed cyclic payoff is a uniform-equilibrium target.
No nonnegative-singleton hypothesis is needed for this infinite assertion. -/
theorem affine_isUniformPayoff_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0)
    (scale shift : Payoff ι) (hscale : ∀ player, 0 < scale player) (initial : Fin period) :
    (quittingGame (quittingPlayerwiseAffineReward reward scale shift)).IsUniformEquilibriumPayoff
      none (quittingPlayerwiseAffinePayoff scale shift (value reward schedule q hq initial)) := by
  exact isUniformEquilibriumPayoff_playerwiseAffine_of_periodicNashBellmanConditions
    reward scale shift (cycle schedule q hq) (value reward schedule q hq) initial hscale
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward (cycle schedule q hq))
    (cycle_isZeroRootNash_of_selected reward schedule hregion q hq hinterior hzero)
    (cycle_opponents_contract schedule q hq
      (fun player => by linarith [(hinterior player).1]))

end GameTheory.PairedCycle
