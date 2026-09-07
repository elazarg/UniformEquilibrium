import UniformEquilibrium.Quitting.Cycles.PairedCycleValues
import MathUE.Finset.ProdLtOne

/-! # Exact all-suffix paired-cycle equilibria from the raw reward region -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

theorem cycle_quit_active (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (tail : Payoff ι) (player : ι) :
    quittingRootQuitPayoff reward tail (cycle schedule q hq (schedule.phase player)) player =
      activeValue (singleton reward player) (jointReward reward schedule player)
        (q (schedule.partner player)) := by
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side
  · change quittingRootQuitPayoff reward tail
      (cycle schedule q hq (schedule.phase (schedule.first phase))) (schedule.first phase) = _
    rw [Schedule.phase_first]
    unfold cycle
    rw [rootQuit_first reward tail (schedule.first_ne_second phase)]
    simp [singleton, jointReward, Schedule.pair, Schedule.partner, Schedule.phase,
      Schedule.first, Schedule.second]
  · change quittingRootQuitPayoff reward tail
      (cycle schedule q hq (schedule.phase (schedule.second phase))) (schedule.second phase) = _
    rw [Schedule.phase_second]
    unfold cycle
    rw [rootQuit_second reward tail (schedule.first_ne_second phase)]
    simp [singleton, jointReward, Schedule.pair, Schedule.partner, Schedule.phase,
      Schedule.first, Schedule.second]

theorem cycle_continue_active (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (tail : Payoff ι) (player : ι) :
    quittingRootContinuePayoff reward tail (cycle schedule q hq (schedule.phase player)) player =
      q (schedule.partner player) * partnerReward reward schedule player +
        (1 - q (schedule.partner player)) * tail player := by
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side
  · change quittingRootContinuePayoff reward tail
      (cycle schedule q hq (schedule.phase (schedule.first phase))) (schedule.first phase) = _
    rw [Schedule.phase_first]
    unfold cycle
    rw [rootContinue_first reward tail (schedule.first_ne_second phase)]
    simp [partnerReward, Schedule.partner, Schedule.first, Schedule.second]
  · change quittingRootContinuePayoff reward tail
      (cycle schedule q hq (schedule.phase (schedule.second phase))) (schedule.second phase) = _
    rw [Schedule.phase_second]
    unfold cycle
    rw [rootContinue_second reward tail (schedule.first_ne_second phase)]
    simp [partnerReward, Schedule.partner, Schedule.first, Schedule.second]

theorem cycle_active_gap_eq_zero_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (player : ι) :
    quittingRootEndpointDifference reward
      (value reward schedule q hq (finRotate period (schedule.phase player)))
      (cycle schedule q hq (schedule.phase player)) player = 0 := by
  rw [quittingRootEndpointDifference, cycle_quit_active, cycle_continue_active,
    value_post_eq_selected reward schedule hregion q hq hinterior hzero]
  rw [continue_eq_active _ _ _ _ (by linarith [(hinterior (schedule.partner player)).2])]
  simp

theorem cycle_quiet_advantage_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (phase : Fin period) (player : ι)
    (hquiet : phase ≠ schedule.phase player) :
    17 / 150 * absorption (q (schedule.first phase)) (q (schedule.second phase)) ≤
      quittingRootContinuePayoff reward (value reward schedule q hq (finRotate period phase))
        (cycle schedule q hq phase) player -
      quittingRootQuitPayoff reward (value reward schedule q hq (finRotate period phase))
        (cycle schedule q hq phase) player := by
  have hgap := rootContinue_sub_quit_ge_of_quiet reward
    (value reward schedule q hq (finRotate period phase)) (schedule.first_ne_second phase)
    (schedule.player_ne_first_of_phase_ne hquiet)
    (schedule.player_ne_second_of_phase_ne hquiet)
    (quittingHazardCoin (q (schedule.first phase)) (hq _).1 (hq _).2)
    (quittingHazardCoin (q (schedule.second phase)) (hq _).1 (hq _).2)
    (hregion.own player).singleton_upper
    (hregion.passive player phase hquiet)
    (hregion.joining player phase hquiet {schedule.first phase} (by simp)
      (by simp [Schedule.pair]))
    (hregion.joining player phase hquiet {schedule.second phase} (by simp)
      (by simp [Schedule.pair]))
    (hregion.joining player phase hquiet (schedule.pair phase) (schedule.pair_nonempty phase)
      Finset.Subset.rfl)
    (by simpa using (hinterior (schedule.first phase)).2.le)
    (by simpa using (hinterior (schedule.second phase)).2.le)
    (value_bounds_of_selected reward schedule hregion q hq hinterior hzero
      (finRotate period phase) player).1.le
  simpa only [quittingHazardCoin_true_toReal, cycle] using hgap

theorem cycle_quiet_gap_lt_zero_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (phase : Fin period) (player : ι)
    (hquiet : phase ≠ schedule.phase player) :
    quittingRootEndpointDifference reward (value reward schedule q hq (finRotate period phase))
      (cycle schedule q hq phase) player < 0 := by
  have hgap := cycle_quiet_advantage_of_selected reward schedule hregion q hq
    hinterior hzero phase player hquiet
  have ha := absorption_pos
    (by linarith [(hinterior (schedule.first phase)).1] : 0 < q (schedule.first phase))
    (hq (schedule.first phase)).2 (hq (schedule.second phase)).1
  unfold quittingRootEndpointDifference
  linarith

theorem cycle_isZeroRootNash_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (phase : Fin period) :
    IsεQuittingRootNash reward (value reward schedule q hq (finRotate period phase)) 0
      (cycle schedule q hq phase) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro player
  by_cases hphase : phase = schedule.phase player
  · subst phase
    rw [cycle_active_gap_eq_zero_of_selected reward schedule hregion q hq hinterior hzero]
    simp
  · have hgap := (cycle_quiet_gap_lt_zero_of_selected reward schedule hregion q hq
      hinterior hzero phase player hphase).le
    have hroot := cycle_outside schedule q hq hphase
    constructor
    · simpa [hroot] using hgap
    · simp [hroot]

theorem cycle_opponents_contract (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hpositive : ∀ player, 0 < q player) (player : ι) :
    (∏ phase : Fin period,
      quittingStationaryFixedOpponentsContinueMass (cycle schedule q hq phase) player) < 1 := by
  have hfactor : quittingStationaryFixedOpponentsContinueMass
      (cycle schedule q hq (schedule.phase player)) player < 1 := by
    have hle := quittingStationaryContinueMass_le_ownContinueProbability
      (Function.update (cycle schedule q hq (schedule.phase player)) player (PMF.pure false))
      (schedule.partner player)
    rw [Function.update_of_ne (schedule.partner_ne player), pmfBool_false_toReal] at hle
    have hpartner := cycle_active_rate schedule q hq (schedule.partner player)
    rw [Schedule.phase_partner] at hpartner
    rw [hpartner] at hle
    change quittingStationaryContinueMass
      (Function.update (cycle schedule q hq (schedule.phase player)) player (PMF.pure false)) < 1
    linarith [hpositive (schedule.partner player)]
  exact Math.Finset.prod_lt_one_of_mem Finset.univ
    (fun phase => quittingStationaryFixedOpponentsContinueMass (cycle schedule q hq phase) player)
    (schedule.phase player) (Finset.mem_univ _)
    (fun phase _ _ => quittingStationaryFixedOpponentsContinueMass_nonneg _ _)
    (fun phase _ _ => quittingStationaryContinueMass_le_one
      (Function.update (cycle schedule q hq phase) player (PMF.pure false))) hfactor

omit [DecidableEq ι] in
theorem rootSequenceProfile_cyclic_suffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (initial : Fin period) (start : ℕ) :
    quittingRootSequenceProfile reward (quittingCyclicRootSequence roots initial) start =
      quittingCyclicBehaviorProfile reward roots (quittingCyclicOrbit initial start) := by
  funext player time history
  simp [quittingRootSequenceProfile, quittingCyclicBehaviorProfile,
    quittingCyclicRootSequence_add]

omit [Fintype ι] [DecidableEq ι] in
theorem unitBoundsOfInterior (q : ι → ℝ)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2)) :
    ∀ player, q player ∈ Set.Icc (0 : ℝ) 1 := by
  intro player
  exact ⟨by linarith [(hinterior player).1], by linarith [(hinterior player).2]⟩

/-- One selected hazard vector gives exact Nash at every literal live suffix and a fixed
uniform-equilibrium payoff at every chosen initial phase, in the original reward table. -/
theorem exists_exact_allSuffix_uniformPayoff_of_rawRegion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (schedule : Schedule ι period)
    (hperiod : 2 ≤ period) (hregion : RawRegion reward schedule) :
    ∃ q : ι → ℝ, ∃ hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2),
      let hq := unitBoundsOfInterior q hinterior
      (∀ player, playerGap schedule.partner (singleton reward)
        (partnerReward reward schedule) (jointReward reward schedule)
        (quietRows reward schedule) q player = 0) ∧
      (∀ phase, IsεQuittingRootNash reward
        (value reward schedule q hq (finRotate period phase)) 0 (cycle schedule q hq phase)) ∧
      (∀ player, (∏ phase : Fin period,
        quittingStationaryFixedOpponentsContinueMass (cycle schedule q hq phase) player) < 1) ∧
      (∀ phase player, singleton reward player < value reward schedule q hq phase player ∧
        value reward schedule q hq phase player ≤ 21 / 10) ∧
      (∀ initial start, (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingRootSequenceProfile reward
          (quittingCyclicRootSequence (cycle schedule q hq) initial) start)) ∧
      (∀ initial, (quittingGame reward).IsUniformEquilibriumPayoff none
        (value reward schedule q hq initial)) := by
  obtain ⟨q, hinterior, hzero⟩ := exists_hazards_of_rawRegion reward schedule hperiod hregion
  let hq := unitBoundsOfInterior q hinterior
  have hnash := cycle_isZeroRootNash_of_selected reward schedule hregion q hq hinterior hzero
  have hcontracts := cycle_opponents_contract schedule q hq
    (fun player => by linarith [(hinterior player).1])
  refine ⟨q, hinterior, hzero, hnash, hcontracts,
    value_bounds_of_selected reward schedule hregion q hq hinterior hzero, ?_, ?_⟩
  · intro initial start
    rw [rootSequenceProfile_cyclic_suffix]
    exact isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate reward
      (cycle schedule q hq) (value reward schedule q hq) _
      (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward _) hnash hcontracts
  · intro initial
    exact isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate reward
      (cycle schedule q hq) (value reward schedule q hq) initial
      (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward _) hnash hcontracts

end GameTheory.PairedCycle
