import UniformEquilibrium.Quitting.Cycles.PairedCycleSchedule

/-! # Actual cyclic values from simultaneous paired affine indifference -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

private def phaseSteps {period : ℕ} (start target : Fin period) : ℕ :=
  ((finCycle start).symm target).val

private theorem phaseSteps_lt {period : ℕ} (start target : Fin period) :
    phaseSteps start target < period :=
  ((finCycle start).symm target).isLt

private theorem orbit_phaseSteps {period : ℕ} (start target : Fin period) :
    quittingCyclicOrbit start (phaseSteps start target) = target := by
  unfold phaseSteps
  rw [orbit_eq_finCycle, Equiv.apply_symm_apply]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

def value (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (phase : Fin period) : Payoff ι :=
  quittingCyclicTerminalValue reward (cycle schedule q hq) phase

def wordRows (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (phase : Fin period) (fuel : ℕ) (player : ι) : List Row :=
  List.ofFn fun offset : Fin fuel =>
    (indexedRow reward schedule player (quittingCyclicOrbit phase offset.val)).specialize q

theorem value_step (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (phase : Fin period) (player : ι) :
    value reward schedule q hq phase player =
      ((indexedRow reward schedule player phase).specialize q).apply
        (value reward schedule q hq (finRotate period phase) player) := by
  have h := congrFun (quittingCyclicTerminalValue_eq_rootSuccessorPayoff
    reward (cycle schedule q hq) phase) player
  change value reward schedule q hq phase player =
    quittingRootSuccessorPayoff reward (value reward schedule q hq (finRotate period phase))
      (cycle schedule q hq phase) player at h
  unfold cycle at h
  rw [rootSuccessor_eq_bellman reward _ (schedule.first_ne_second phase)] at h
  simpa [indexedRow, IndexedRow.specialize, Row.apply, Schedule.pair] using h

theorem value_unroll (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (phase : Fin period)
    (fuel : ℕ) (player : ι) :
    value reward schedule q hq phase player =
      compose (wordRows reward schedule q phase fuel player)
        (value reward schedule q hq (quittingCyclicOrbit phase fuel) player) := by
  induction fuel generalizing phase with
  | zero => simp [wordRows, compose]
  | succ fuel ih =>
      have h := (value_step reward schedule q hq phase player).trans
        (congrArg (fun x => ((indexedRow reward schedule player phase).specialize q).apply x)
          (ih (finRotate period phase)))
      simpa only [wordRows, List.ofFn_succ, compose, List.foldr_cons,
        Fin.val_zero, Nat.add_zero, quittingCyclicOrbit_zero, Fin.val_succ, orbit_next] using h

theorem value_post_eq_quiet_compose (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (player : ι) :
    value reward schedule q hq (finRotate period (schedule.phase player)) player =
      compose ((quietRows reward schedule player).map fun row => row.specialize q)
        (value reward schedule q hq (schedule.phase player) player) := by
  have h := value_unroll reward schedule q hq (finRotate period (schedule.phase player))
    (period - 1) player
  have hend : quittingCyclicOrbit (finRotate period (schedule.phase player)) (period - 1) =
      schedule.phase player := by
    rw [orbit_next, Nat.sub_add_cancel (show 1 ≤ period by
      have := (schedule.phase player).pos
      omega), quittingCyclicOrbit_card]
  have hrows : wordRows reward schedule q (finRotate period (schedule.phase player))
      (period - 1) player = (quietRows reward schedule player).map fun row => row.specialize q := by
    simp only [wordRows, quietRows, List.map_ofFn]
    congr 1
    funext offset
    simp only [Function.comp_apply, orbit_next]
  rwa [hend, hrows] at h

theorem value_active_step (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (player : ι) :
    value reward schedule q hq (schedule.phase player) player =
      bellman (singleton reward player) (partnerReward reward schedule player)
        (jointReward reward schedule player) (q player) (q (schedule.partner player))
        (value reward schedule q hq (finRotate period (schedule.phase player)) player) := by
  have h := value_step reward schedule q hq (schedule.phase player) player
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side <;>
    simp only [Schedule.phase, Equiv.symm_apply_apply, singleton, partnerReward, jointReward,
      Schedule.partner, Bool.not_false, Bool.not_true] at h ⊢
  · simpa [indexedRow, IndexedRow.specialize, Row.apply, Schedule.first, Schedule.second] using h
  · simp only [indexedRow, IndexedRow.specialize, Row.apply, Schedule.first, Schedule.second] at h
    rw [h]
    unfold bellman contribution
    ring

/-- The simultaneous scalar zero identifies the actual active value, not an annotation. -/
theorem value_active_eq_selected (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (player : ι) :
    value reward schedule q hq (schedule.phase player) player =
      activeValue (singleton reward player) (jointReward reward schedule player)
        (q (schedule.partner player)) := by
  have hvalid := specialized_rows_valid (quietRows_passive reward schedule hregion player)
    (fun who => ⟨(hinterior who).1.le, (hinterior who).2.le⟩)
  have hactual := value_active_step reward schedule q hq player
  rw [value_post_eq_quiet_compose reward schedule q hq player] at hactual
  have hpost : postValue (singleton reward player) (partnerReward reward schedule player)
      (jointReward reward schedule player) (q (schedule.partner player)) =
      compose ((quietRows reward schedule player).map fun row => row.specialize q)
        (activeValue (singleton reward player) (jointReward reward schedule player)
          (q (schedule.partner player))) := sub_eq_zero.mp (hzero player)
  apply eq_of_active_cycle_fixed (fun row hrow => (hvalid row hrow).hazards)
    ⟨by linarith [(hinterior player).1], (hq player).2⟩ (hq (schedule.partner player)) hactual
  rw [← hpost]
  have hne : q (schedule.partner player) ≠ 1 := by
    linarith [(hinterior (schedule.partner player)).2]
  unfold bellman contribution activeValue postValue
  field_simp
  ring

theorem value_post_eq_selected (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (player : ι) :
    value reward schedule q hq (finRotate period (schedule.phase player)) player =
      postValue (singleton reward player) (partnerReward reward schedule player)
        (jointReward reward schedule player) (q (schedule.partner player)) := by
  rw [value_post_eq_quiet_compose,
    value_active_eq_selected reward schedule hregion q hq hinterior hzero]
  exact (sub_eq_zero.mp (hzero player)).symm

theorem value_bounds_of_selected (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (phase : Fin period) (player : ι) :
    singleton reward player < value reward schedule q hq phase player ∧
      value reward schedule q hq phase player ≤ 21 / 10 := by
  let steps := phaseSteps phase (schedule.phase player)
  have hsteps : steps < period := phaseSteps_lt phase (schedule.phase player)
  have hend : quittingCyclicOrbit phase steps = schedule.phase player :=
    orbit_phaseSteps phase (schedule.phase player)
  have hrows : ∀ row ∈ wordRows reward schedule q phase steps player, row.Valid := by
    intro row hrow
    obtain ⟨offset, rfl⟩ := List.mem_ofFn.mp hrow
    have hquiet : quittingCyclicOrbit phase offset.val ≠ schedule.phase player := by
      intro heq
      have hdates := orbit_injective_below_period phase (offset.isLt.trans hsteps) hsteps
        (heq.trans hend.symm)
      omega
    refine ⟨hregion.passive player _ hquiet, ?_, ?_⟩
    · exact ⟨(hinterior _).1.le, (hinterior _).2.le⟩
    · exact ⟨(hinterior _).1.le, (hinterior _).2.le⟩
  have hunroll := value_unroll reward schedule q hq phase steps player
  rw [hend, value_active_eq_selected reward schedule hregion q hq hinterior hzero] at hunroll
  rw [hunroll]
  constructor
  · exact compose_gt_singleton hrows (hregion.own player).singleton_upper
      (active_gt_singleton (hregion.own player)
        (by linarith [(hinterior (schedule.partner player)).1]))
  · apply compose_le_upper hrows
    have hx := active_le_eight_fifths (hregion.own player)
      ⟨(hq (schedule.partner player)).1, (hinterior (schedule.partner player)).2.le⟩
    linarith

end GameTheory.PairedCycle
