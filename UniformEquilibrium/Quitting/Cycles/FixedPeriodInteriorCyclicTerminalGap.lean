/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.FixedPeriodInteriorCyclicLimit
import UniformEquilibrium.Quitting.Cycles.InteriorCyclicTerminalDebtRatio

/-!
# Fixed-period exact cyclic limits under a terminal gap

At one fixed positive period, a vanishing-error family of interior cyclic
blocks in a game with a positive terminal exploitability gap has a fixed
debtor along a strict subsequence.  Its opponent absorption vanishes, so a
further compact subsequence converges to an exact cyclic Nash--Bellman word
on which every other player surely Continues at every phase.

The limit word may be all Continue or may retain only the selected player's
Quit probabilities.  It is not asserted to be an absorbing terminal Nash
profile.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- A positive terminal gap forces every fixed-period vanishing-error family
to have an exact cyclic Nash--Bellman cluster point on which at most one
player ever Quits.  The first selection fixes the debtor; the limit object
may take a further strict subsequence. -/
theorem exists_fixedPeriodExactNashCyclicLimit_of_terminalGap
    {m : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℕ → ℝ) (herrorNonneg : ∀ n, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (block : ∀ n, InteriorApproximateNashCyclicBlock reward m (error n))
    (initial : ∀ _n : ℕ, Fin (m + 1))
    {gap : ℝ} (hgap : 0 < gap)
    (exploit : HasTerminalExploitabilityGap reward gap) :
    ∃ (owner : ι) (select : ℕ → ℕ),
      StrictMono select ∧
        Nonempty (FixedPeriodExactNashCyclicLimit reward
          (error ∘ select) (fun n ↦ block (select n)) owner) := by
  have hperiodError : Tendsto (fun n ↦
      ((m + 1 : ℕ) : ℝ) * error n) atTop (nhds 0) := by
    simpa using herror.const_mul ((m + 1 : ℕ) : ℝ)
  let fixed := Classical.choice
    (nonempty_interiorCyclicFixedDebtorSubsequence
      reward (fun _ ↦ m) error herrorNonneg block initial hgap
      (fun n ↦ exploit.exists_cyclicProfile_debtor (block n) (initial n))
      hperiodError)
  have herrorSelected : Tendsto (error ∘ fixed.select) atTop (nhds 0) :=
    herror.comp fixed.select_strictMono.tendsto_atTop
  have hopponentSelected : Tendsto (fun n ↦
      quittingCyclicOpponentAbsorptionMass
        (block (fixed.select n)).cycle fixed.owner) atTop (nhds 0) :=
    fixed.opponentAbsorption_tendsto_zero
  exact ⟨fixed.owner, fixed.select, fixed.select_strictMono,
    nonempty_fixedPeriodExactNashCyclicLimit reward
      (error ∘ fixed.select) (fun n ↦ block (fixed.select n)) fixed.owner
      herrorSelected hopponentSelected⟩

end GameTheory
