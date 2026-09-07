import UniformEquilibrium.Quitting.Cycles.PairedCycleRegionCenter
import Mathlib.Topology.Instances.Real.Lemmas

/-! # A nonempty open paired raw reward region in the full reward space -/

noncomputable section

namespace GameTheory.PairedCycle

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

/-- Strict raw reward inequalities; no other reward coordinates are restricted. -/
def StrictRawRegion (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) : Prop :=
  (∀ player, singleton reward player ∈ Set.Ioo (9 / 10 : ℝ) (11 / 10) ∧
    partnerReward reward schedule player ∈ Set.Ioo (-(1 / 10) : ℝ) (1 / 10) ∧
    jointReward reward schedule player ∈ Set.Ioo (19 / 10 : ℝ) (21 / 10)) ∧
  (∀ player phase, phase ≠ schedule.phase player →
    reward (quittingSingletonTerminal (schedule.first phase)) player ∈
      Set.Ioo (19 / 10 : ℝ) (21 / 10) ∧
    reward (quittingSingletonTerminal (schedule.second phase)) player ∈
      Set.Ioo (19 / 10 : ℝ) (21 / 10) ∧
    reward ⟨schedule.pair phase, schedule.pair_nonempty phase⟩ player ∈
      Set.Ioo (-(1 / 10) : ℝ) (1 / 10)) ∧
  (∀ player phase, phase ≠ schedule.phase player → ∀ coalition : Finset ι,
    coalition.Nonempty → coalition ⊆ schedule.pair phase →
    reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player <
      singleton reward player + 1 / 50)

omit [Fintype ι] in
theorem StrictRawRegion.rawRegion
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {schedule : Schedule ι period}
    (hregion : StrictRawRegion reward schedule) : RawRegion reward schedule := by
  constructor
  · intro player
    rcases hregion.1 player with ⟨hs, hb, hp⟩
    exact ⟨hs.1.le, hs.2.le, hb.1.le, hb.2.le, hp.1.le, hp.2.le⟩
  · intro player phase hquiet
    rcases hregion.2.1 player phase hquiet with ⟨hl, hr, ht⟩
    exact ⟨hl.1.le, hl.2.le, hr.1.le, hr.2.le, ht.1.le, ht.2.le⟩
  · intro player phase hquiet coalition hnonempty hsubset
    exact (hregion.2.2 player phase hquiet coalition hnonempty hsubset).le

omit [Fintype ι] in
theorem centerReward_strictRawRegion (schedule : Schedule ι period) :
    StrictRawRegion (centerReward schedule) schedule := by
  constructor
  · intro player
    rcases centerReward_own schedule player with ⟨hs, hb, hp⟩
    rw [hs, hb, hp]
    norm_num
  constructor
  · intro player phase hquiet
    rcases centerReward_passive schedule phase player hquiet with ⟨hl, hr, ht⟩
    rw [hl, hr, ht]
    norm_num
  · intro player phase hquiet coalition hnonempty hsubset
    rw [centerReward_joining schedule phase player hquiet coalition hnonempty hsubset,
      (centerReward_own schedule player).1]
    norm_num

theorem isOpen_strictRawRegion (schedule : Schedule ι period) :
    IsOpen {reward : {S : Finset ι // S.Nonempty} → Payoff ι | StrictRawRegion reward schedule} := by
  have hcoordinate (terminal : {S : Finset ι // S.Nonempty}) (player : ι) :
      Continuous (fun reward : {S : Finset ι // S.Nonempty} → Payoff ι =>
        reward terminal player) :=
    (continuous_apply player).comp (continuous_apply terminal)
  unfold StrictRawRegion
  have hforall {α : Type} [Finite α]
      {p : α → ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop}
      (h : ∀ a, IsOpen {r | p a r}) : IsOpen {r | ∀ a, p a r} := by
    simpa only [Set.iInter_setOf] using isOpen_iInter_of_finite h
  apply IsOpen.inter
  · apply hforall
    intro player
    exact (isOpen_Ioo.preimage (hcoordinate (quittingSingletonTerminal player) player)).inter
      ((isOpen_Ioo.preimage (hcoordinate (quittingSingletonTerminal (schedule.partner player))
        player)).inter (isOpen_Ioo.preimage
          (hcoordinate ⟨schedule.pair (schedule.phase player), schedule.pair_nonempty _⟩ player)))
  apply IsOpen.inter
  · apply hforall
    intro player
    apply hforall
    intro phase
    by_cases hquiet : phase ≠ schedule.phase player
    · simp only [ne_eq, hquiet, not_false_eq_true, true_implies]
      exact (isOpen_Ioo.preimage (hcoordinate
        (quittingSingletonTerminal (schedule.first phase)) player)).inter
        ((isOpen_Ioo.preimage (hcoordinate
          (quittingSingletonTerminal (schedule.second phase)) player)).inter
          (isOpen_Ioo.preimage (hcoordinate
            ⟨schedule.pair phase, schedule.pair_nonempty phase⟩ player)))
    · simp [hquiet]
  · apply hforall
    intro player
    apply hforall
    intro phase
    by_cases hquiet : phase ≠ schedule.phase player
    · simp only [ne_eq, hquiet, not_false_eq_true, true_implies]
      apply hforall
      intro coalition
      by_cases hnonempty : coalition.Nonempty
      · simp only [hnonempty, true_implies]
        by_cases hsubset : coalition ⊆ schedule.pair phase
        · simp only [hsubset, true_implies]
          exact isOpen_lt
            (hcoordinate ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player)
            ((hcoordinate (quittingSingletonTerminal player) player).add continuous_const)
        · simp [hsubset]
      · simp [hnonempty]
    · simp [hquiet]

/-- A nonempty open subset of the entire reward-coordinate space satisfies
the paired reward hypotheses, with the explicit center as a witness. -/
theorem strictRawRegion_nonempty_open_subset_rawRegion (schedule : Schedule ι period) :
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι | StrictRawRegion reward schedule}.Nonempty ∧
      IsOpen {reward : {S : Finset ι // S.Nonempty} → Payoff ι | StrictRawRegion reward schedule} ∧
      {reward : {S : Finset ι // S.Nonempty} → Payoff ι | StrictRawRegion reward schedule} ⊆
        {reward | RawRegion reward schedule} := by
  exact ⟨⟨centerReward schedule, centerReward_strictRawRegion schedule⟩,
    isOpen_strictRawRegion schedule, fun _ h => h.rawRegion⟩

end GameTheory.PairedCycle
