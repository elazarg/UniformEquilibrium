import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteTruncation
import UniformEquilibrium.Quitting.Cycles.CyclicFiniteMenu
import UniformEquilibrium.Quitting.Root.TruncatedStoppingLaw

/-! # Exact geometric calendar laws of finite paired cycles -/

noncomputable section

namespace GameTheory.PairedCycle

open _root_.Math.Probability _root_.Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

omit [Fintype ι] in
theorem prod_cycle_ownContinue (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (player : ι) :
    (∏ phase, (cycle schedule q hq phase player false).toReal) = 1 - q player := by
  rw [Finset.prod_eq_single (schedule.phase player)]
  · rw [pmfBool_false_toReal, cycle_active_rate]
  · intro phase _ hphase
    rw [cycle_outside schedule q hq hphase]
    simp
  · simp

omit [Fintype ι] in
theorem ownContinue_prefix_firstActiveTime (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (initial : Fin period) (player : ι) :
    quittingCyclicPrefixWeight (fun phase => (cycle schedule q hq phase player false).toReal)
        initial (firstActiveTime schedule initial player) = 1 := by
  apply Finset.prod_eq_one
  intro time htime
  dsimp only
  rw [cycle_outside schedule q hq
    (orbit_ne_owner_before_firstActiveTime schedule initial player time
      (Finset.mem_range.mp htime))]
  simp

/-- The infinite source law is geometric on the player's actual active calendar. -/
theorem cyclicStoppingLaw_activeDate_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (initial : Fin period) (turn : ℕ) (player : ι) :
    (quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward
          (quittingCyclicRootSequence (cycle schedule q hq) initial) 0 player)
        (some (turn * period + firstActiveTime schedule initial player))).toReal =
      q player * (1 - q player) ^ turn := by
  rw [quittingBehaviorStoppingLaw_some_toReal, quittingHazardStopMass_eq_survival_mul_stop,
    quittingHazardSurvival_eq_prod]
  simp only [quittingBehaviorLiveHazard, quittingRootSequenceProfile, Nat.zero_add,
    quittingCyclicRootSequence]
  change quittingCyclicPrefixWeight
    (fun phase => (cycle schedule q hq phase player false).toReal) initial
      (turn * period + firstActiveTime schedule initial player) * _ = _
  rw [quittingCyclicPrefixWeight_add, quittingCyclicPrefixWeight_mul_card,
    quittingCyclicOrbit_add, quittingCyclicOrbit_mul_card, ownContinue_prefix_firstActiveTime,
    orbit_firstActiveTime, cycle_active_rate, prod_cycle_ownContinue]
  ring

/-- Every retained active date has its literal geometric mass. -/
theorem finiteStoppingLaw_activeDate_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (initial : Fin period) (turns turn : ℕ) (hturn : turn < turns) (player : ι) :
    (quittingBehaviorStoppingLaw reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period) player)
        (some (turn * period + firstActiveTime schedule initial player))).toReal =
      q player * (1 - q player) ^ turn := by
  rw [quittingCyclicFiniteProfile_eq_truncatedRootProfile,
    quittingBehaviorStoppingLaw_truncatedRoots_some_eq_of_lt]
  · exact cyclicStoppingLaw_activeDate_toReal reward schedule q hq initial turn player
  · calc
      _ < turn * period + period := Nat.add_lt_add_left
        (firstActiveTime_lt_period schedule initial player) _
      _ = (turn + 1) * period := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ turns * period := Nat.mul_le_mul_right period hturn

/-- The retained Never atom is exactly the probability of missing every own active row. -/
theorem finiteStoppingLaw_none_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (initial : Fin period) (turns : ℕ) (hturns : 0 < turns) (player : ι) :
    (quittingBehaviorStoppingLaw reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period) player)
        none).toReal = (1 - q player) ^ turns := by
  rw [quittingCyclicFiniteProfile_eq_truncatedRootProfile,
    quittingBehaviorStoppingLaw_truncatedRoots_none_toReal reward _ _
      (Nat.mul_pos hturns initial.pos)]
  change quittingCyclicPrefixWeight
    (fun phase => (cycle schedule q hq phase player false).toReal) initial (turns * period) = _
  rw [quittingCyclicPrefixWeight_mul_card, prod_cycle_ownContinue]

/-- The finite laws are obtained by independent late-finite censoring of the same source cycle. -/
theorem finiteStoppingLaw_eq_censor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (initial : Fin period) (turns : ℕ) (hturns : 0 < turns) (player : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period) player) =
      censorLateFiniteStoppingLaw
        (quittingBehaviorStoppingLaw reward
          (quittingRootSequenceProfile reward
            (quittingCyclicRootSequence (cycle schedule q hq) initial) 0 player))
        (turns * period - 1) := by
  rw [quittingCyclicFiniteProfile_eq_truncatedRootProfile]
  exact quittingBehaviorStoppingLaw_truncatedRoots_eq_censor reward _ _
    (Nat.mul_pos hturns initial.pos) player

/-- Every inactive date and every date at or beyond the cut has zero finite mass. -/
theorem finiteStoppingLaw_some_eq_zero_of_inactive_or_late
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (initial : Fin period) (turns time : ℕ) (player : ι)
    (htime : quittingCyclicOrbit initial time ≠ schedule.phase player ∨
      turns * period ≤ time) :
    quittingBehaviorStoppingLaw reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period) player)
        (some time) = 0 := by
  have hroot : quittingBehaviorLiveHazard reward
      (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period) player)
      time = PMF.pure false := by
    unfold quittingBehaviorLiveHazard
    rw [quittingCyclicFiniteProfile_apply]
    split_ifs with hbefore
    · exact cycle_outside schedule q hq (htime.resolve_right (by omega))
    · rfl
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ENNReal.zero_ne_top).mp
  rw [quittingBehaviorStoppingLaw_some_toReal, quittingHazardStopMass_eq_survival_mul_stop,
    hroot]
  simp

end GameTheory.PairedCycle
