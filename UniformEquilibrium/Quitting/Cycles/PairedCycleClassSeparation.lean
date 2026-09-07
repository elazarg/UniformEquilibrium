import UniformEquilibrium.Quitting.Cycles.PairedCycleFiniteSource
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionStep

/-! # Literal product-premium and finite-word exclusion failures of paired cycles -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

/-- Activating one literal pair already violates product-low premiums. -/
theorem not_productLow_of_rawRegion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule)
    (initial : Fin period) : ¬ HasProductLowQuittingPremium reward := by
  let q : ι → ℝ := fun _ => 1 / 4
  have hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1 := fun _ => by norm_num [q]
  have habsorption : 0 < quittingRootAbsorptionMass (cycle schedule q hq initial) := by
    unfold cycle
    rw [absorptionMass_root (schedule.first_ne_second initial)]
    norm_num [q, absorption]
  intro hlow
  obtain ⟨player, hactive, hquit⟩ := hlow (cycle schedule q hq initial) habsorption
  have hphase : initial = schedule.phase player := by
    by_contra hphase
    rw [cycle_outside schedule q hq hphase] at hactive
    simp at hactive
  rw [hphase, cycle_quit_active] at hquit
  have hstrict := active_gt_singleton (hregion.own player)
    (show 0 < q (schedule.partner player) by norm_num [q])
  exact (not_le_of_gt hstrict) hquit

/-- Literal finite cyclic truncations converge coordinatewise to the actual
periodic target under the selected strictly interior hazards. -/
theorem tendsto_finiteProfile_payoff_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (initial : Fin period) (player : ι) :
    Tendsto (fun turns => quittingTerminalPayoff reward
      (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial (turns * period)) player)
      atTop (nhds (value reward schedule q hq initial player)) := by
  have hcard : 0 < Fintype.card ι := by
    rw [schedule.card_players]
    have := initial.pos
    omega
  have hle := jointCycleSurvival_le_geometric q
    (fun player => ⟨(hinterior player).1.le, (hq player).2⟩)
  have hlt : jointCycleSurvival q < 1 := hle.trans_lt
    (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (jointCycleSurvival_nonneg q (fun player => (hq player).2)) hlt
  simp_rw [finiteProfile_payoff_eq]
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa using (hone.sub hpow).mul_const
    (value reward schedule q hq initial player)

/-- A single sufficiently long finite word lies strictly above every singleton;
the infinite equilibrium is not substituted for a finite-word witness. -/
theorem exists_finiteProfile_all_payoffs_gt_singleton_of_selected
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1)
    (hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2))
    (hzero : ∀ player, playerGap schedule.partner (singleton reward)
      (partnerReward reward schedule) (jointReward reward schedule)
      (quietRows reward schedule) q player = 0) (initial : Fin period) :
    ∃ turns : ℕ, 1 ≤ turns ∧ ∀ player, singleton reward player <
      quittingTerminalPayoff reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial
          (turns * period)) player := by
  have heventually (player : ι) : ∀ᶠ turns in atTop, singleton reward player <
      quittingTerminalPayoff reward
        (quittingCyclicFiniteProfile reward (cycle schedule q hq) initial
          (turns * period)) player :=
    (tendsto_finiteProfile_payoff_of_selected reward schedule q hq
      hinterior initial player).eventually
      (lt_mem_nhds (value_bounds_of_selected reward schedule hregion q hq
        hinterior hzero initial player).1)
  have hall := eventually_all.mpr heventually
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  exact ⟨max 1 cutoff, le_max_left _ _, hcutoff _ (le_max_right _ _)⟩

/-- The raw paired region fails the literal finite-word weak-exclusion predicate. -/
theorem not_finiteWordWeakSingletonExclusion_of_rawRegion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hperiod : 2 ≤ period) (hregion : RawRegion reward schedule) :
    ¬ QuittingFiniteWordWeakSingletonExclusion reward := by
  obtain ⟨q, hinterior, hzero⟩ := exists_hazards_of_rawRegion reward schedule hperiod hregion
  let hq := unitBoundsOfInterior q hinterior
  let initial : Fin period := ⟨0, by omega⟩
  obtain ⟨turns, _, hstrict⟩ := exists_finiteProfile_all_payoffs_gt_singleton_of_selected
    reward schedule hregion q hq hinterior hzero initial
  intro hweak
  obtain ⟨player, hplayer⟩ := hweak
    (quittingCyclicRootWord (cycle schedule q hq) initial (turns * period))
  exact (not_le_of_gt (hstrict player)) hplayer

end GameTheory.PairedCycle
