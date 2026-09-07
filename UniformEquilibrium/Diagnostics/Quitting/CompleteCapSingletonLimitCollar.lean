/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CompleteCapSingletonSlabCollar

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
  obtain ⟨collar, hcollar, hfamily⟩ :=
    exists_uniform_offMinimum_collar_of_completeCap_tendsto_singleton
      reward (fun index (_ : Unit) => profile index) who
      (fun index => quittingContinuationBestResponseValue reward (profile index) who)
      hminimumPos hminimum (fun _ _ => rfl) hcap
  refine ⟨minimum, hminimumMem, hminimum, hminimumPos, collar, hcollar, ?_⟩
  exact hfamily.mono fun _ hindex => hindex ()

end GameTheory
