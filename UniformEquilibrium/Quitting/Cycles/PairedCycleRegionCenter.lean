import UniformEquilibrium.Quitting.Cycles.PairedCycleSchedule

/-! # A literal center table for the paired raw reward region -/

noncomputable section

namespace GameTheory.PairedCycle

variable {ι : Type} [DecidableEq ι] {period : ℕ}

theorem Schedule.mem_pair_iff_phase_eq (schedule : Schedule ι period)
    (phase : Fin period) (player : ι) :
    player ∈ schedule.pair phase ↔ schedule.phase player = phase := by
  constructor
  · intro hmem
    simp only [Schedule.pair, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl <;> simp
  · intro hphase
    rw [← hphase]
    rcases schedule.player_eq_first_or_second player with hfirst | hsecond
    · exact Finset.mem_insert.mpr (Or.inl hfirst)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hsecond))

theorem Schedule.pair_card (schedule : Schedule ι period) (phase : Fin period) :
    (schedule.pair phase).card = 2 := by
  simp [Schedule.pair, schedule.first_ne_second phase]

/-- Singleton rewards are owner one, partner zero and outsiders two; own-pair
participants get two, passive pair observers zero, and other nonsingleton entries one. -/
def centerReward (schedule : Schedule ι period)
    (coalition : {S : Finset ι // S.Nonempty}) (player : ι) : ℝ :=
  if coalition.1.card = 1 then
    if player ∈ coalition.1 then 1 else if schedule.partner player ∈ coalition.1 then 0 else 2
  else if player ∈ coalition.1 then
    if coalition.1 = schedule.pair (schedule.phase player) then 2 else 1
  else if ∃ phase, coalition.1 = schedule.pair phase then 0 else 1

theorem centerReward_singleton (schedule : Schedule ι period) (owner player : ι) :
    centerReward schedule (quittingSingletonTerminal owner) player =
      if player = owner then 1 else if schedule.partner player = owner then 0 else 2 := by
  simp [centerReward, quittingSingletonTerminal]

theorem centerReward_pair (schedule : Schedule ι period) (phase : Fin period) (player : ι) :
    centerReward schedule ⟨schedule.pair phase, schedule.pair_nonempty phase⟩ player =
      if schedule.phase player = phase then 2 else 0 := by
  by_cases hphase : schedule.phase player = phase
  · simp [centerReward, schedule.pair_card, schedule.mem_pair_iff_phase_eq, hphase]
  · simp [centerReward, schedule.pair_card, schedule.mem_pair_iff_phase_eq, hphase]

theorem centerReward_joining (schedule : Schedule ι period) (phase : Fin period) (player : ι)
    (hquiet : phase ≠ schedule.phase player) (coalition : Finset ι)
    (hnonempty : coalition.Nonempty) (hsubset : coalition ⊆ schedule.pair phase) :
    centerReward schedule ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player = 1 := by
  have hnot : player ∉ coalition := by
    intro hmem
    exact hquiet ((schedule.mem_pair_iff_phase_eq phase player).mp (hsubset hmem)).symm
  have hcard : (insert player coalition).card ≠ 1 := by
    rw [Finset.card_insert_of_notMem hnot]
    have := Finset.card_pos.mpr hnonempty
    omega
  have hne : insert player coalition ≠ schedule.pair (schedule.phase player) := by
    intro heq
    obtain ⟨other, hother⟩ := hnonempty
    have hfirst := (schedule.mem_pair_iff_phase_eq phase other).mp (hsubset hother)
    have hsecond := (schedule.mem_pair_iff_phase_eq (schedule.phase player) other).mp
      (heq ▸ Finset.mem_insert_of_mem hother)
    exact hquiet (hfirst.symm.trans hsecond)
  simp [centerReward, hcard, hne]

theorem centerReward_own (schedule : Schedule ι period) (player : ι) :
    singleton (centerReward schedule) player = 1 ∧
      partnerReward (centerReward schedule) schedule player = 0 ∧
      jointReward (centerReward schedule) schedule player = 2 := by
  constructor
  · rw [singleton, centerReward_singleton]
    simp
  constructor
  · rw [partnerReward, centerReward_singleton]
    simp [Ne.symm (schedule.partner_ne player)]
  · exact by simp [jointReward, centerReward_pair]

theorem centerReward_passive (schedule : Schedule ι period) (phase : Fin period) (player : ι)
    (hquiet : phase ≠ schedule.phase player) :
    centerReward schedule (quittingSingletonTerminal (schedule.first phase)) player = 2 ∧
      centerReward schedule (quittingSingletonTerminal (schedule.second phase)) player = 2 ∧
      centerReward schedule ⟨schedule.pair phase, schedule.pair_nonempty phase⟩ player = 0 := by
  have hfirst := schedule.player_ne_first_of_phase_ne hquiet
  have hsecond := schedule.player_ne_second_of_phase_ne hquiet
  have hpartner : phase ≠ schedule.phase (schedule.partner player) := by simpa using hquiet
  have hpfirst := schedule.player_ne_first_of_phase_ne hpartner
  have hpsecond := schedule.player_ne_second_of_phase_ne hpartner
  simp [centerReward_singleton, hfirst, hsecond, hpfirst, hpsecond,
    centerReward_pair, Ne.symm hquiet]

theorem centerReward_rawRegion (schedule : Schedule ι period) :
    RawRegion (centerReward schedule) schedule := by
  constructor
  · intro player
    have h := centerReward_own schedule player
    rw [h.1, h.2.1, h.2.2]
    constructor <;> norm_num
  · intro player phase hquiet
    have h := centerReward_passive schedule phase player hquiet
    rw [h.1, h.2.1, h.2.2]
    constructor <;> norm_num
  · intro player phase hquiet coalition hnonempty hsubset
    rw [centerReward_joining schedule phase player hquiet coalition hnonempty hsubset,
      (centerReward_own schedule player).1]
    norm_num

end GameTheory.PairedCycle
