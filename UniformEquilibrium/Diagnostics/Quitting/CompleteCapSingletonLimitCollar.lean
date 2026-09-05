/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-! # Complete-cap singleton limits stay off the minimum fiber -/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Any actual source family whose named complete cap converges to that
player's singleton payoff eventually stays a fixed positive distance in total
debt above the global minimum fiber. No ancestry of the sources is assumed. -/
theorem exists_eventual_offMinimum_collar_of_completeCap_tendsto_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (profile : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (hcap : Tendsto (fun index ↦ quittingContinuationBestResponseValue reward
      (profile index) who) atTop
      (nhds (reward (quittingSingletonTerminal who) who))) :
    ∃ minimum : QuittingTerminalSemanticPair ι,
      minimum ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum minimum ∧
      ∃ collar : ℝ, 0 < collar ∧ ∀ᶠ index in atTop,
        quittingTerminalSemanticDebtSum minimum + collar ≤
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (profile index)) := by
  letI : Nonempty ι := ⟨who⟩
  obtain ⟨minimum, _, hminimumMem, _, hminimum, ⟨payer, hpayer⟩, _⟩ :=
    exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff reward hno
  have hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum :=
    hpayer.trans_le (Finset.single_le_sum
      (fun player _ ↦ quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hminimumMem player) (Finset.mem_univ payer))
  let solo := reward (quittingSingletonTerminal who) who
  let slab : Set (QuittingTerminalSemanticPair ι) :=
    quittingTerminalSemanticCarrier reward ∩
      {pair | |pair.2 who - solo| ≤ quittingTerminalSemanticDebtSum minimum / 2}
  have hslabCompact : IsCompact slab := by
    apply (quittingTerminalSemanticCarrier_isCompact reward).inter_right
    exact isClosed_le (continuous_abs.comp
      (((continuous_apply who).comp continuous_snd).sub continuous_const))
      continuous_const
  have hcapEventually : ∀ᶠ index in atTop,
      |(quittingTerminalSemanticPair reward (profile index)).2 who - solo| ≤
        quittingTerminalSemanticDebtSum minimum / 2 := by
    have hopen : 0 < quittingTerminalSemanticDebtSum minimum / 2 := half_pos hminimumPos
    exact hcap.eventually (Metric.closedBall_mem_nhds _ hopen) |>.mono fun _ h ↦ by
      simpa [solo, Metric.mem_closedBall, Real.dist_eq,
        quittingTerminalSemanticPair] using h
  have hslabNonempty : slab.Nonempty := by
    obtain ⟨index, hindex⟩ := hcapEventually.exists
    exact ⟨quittingTerminalSemanticPair reward (profile index),
      subset_closure (Set.mem_range_self (profile index)), hindex⟩
  obtain ⟨selected, hselected, hselectedMin⟩ :=
    hslabCompact.exists_isMinOn hslabNonempty
      continuous_quittingTerminalSemanticDebtSum.continuousOn
  have hstrict : quittingTerminalSemanticDebtSum minimum <
      quittingTerminalSemanticDebtSum selected := by
    have hle := hminimum selected hselected.1
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hmargin := minimumTerminalSemantic_singletonMargin
      selected hselected.1 (fun candidate hcandidate ↦ by
        rw [← heq]
        exact hminimum candidate hcandidate) (by rwa [← heq]) who
    have habsUpper : selected.2 who - solo ≤
        quittingTerminalSemanticDebtSum minimum / 2 :=
      (abs_le.mp (show |selected.2 who - solo| ≤
        quittingTerminalSemanticDebtSum minimum / 2 from hselected.2)).2
    dsimp only [solo] at hmargin habsUpper
    linarith
  let collar := (quittingTerminalSemanticDebtSum selected -
    quittingTerminalSemanticDebtSum minimum) / 2
  have hcollar : 0 < collar := by dsimp only [collar]; linarith
  refine ⟨minimum, hminimumMem, hminimum, hminimumPos, collar, hcollar, ?_⟩
  filter_upwards [hcapEventually] with index hindex
  have hpairSlab : quittingTerminalSemanticPair reward (profile index) ∈ slab :=
    ⟨subset_closure (Set.mem_range_self (profile index)), hindex⟩
  have hselectedLe := hselectedMin hpairSlab
  change quittingTerminalSemanticDebtSum selected ≤
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profile index)) at hselectedLe
  dsimp only [collar]
  linarith

end GameTheory
