/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FinFourHardDeadlineTimingNashUniqueness

/-!
# Worst-case Fin4 finite-deadline timing Nash exploitability

This file identifies the exact asymptotic worst-table value of the finite-deadline
timing-Nash architecture.  At each deadline, the supremum ranges over every normalized
Fin4 reward table and every exact mixed Nash law of its complete timing game.

The universal finite-deadline estimate gives the upper bound `1 / 4 + 2 / K`.
The hard-deadline table and its canonical actual Nash law give the lower bound `D_K`.
Consequently the exact worst-case value tends to `1 / 4` along positive deadlines.

This re-solves the timing game at every deadline.  It does not preserve a law selected
at an earlier deadline, and it is not a claim about arbitrary finite-clock profiles or
uniform equilibrium.
-/

noncomputable section

namespace GameTheory
namespace FinFourHardDeadlineTimingNashBarrier

open Filter Math.Probability
open scoped Topology

/-- Exploitabilities realized by exact mixed timing Nash laws of normalized Fin4 tables. -/
def finiteDeadlineTimingNashExploitabilityValues (deadline : ℕ) : Set ℝ :=
  {value | ∃ table : {S : Finset Player // S.Nonempty} → Payoff Player,
    (∀ terminal who, |table terminal who| ≤ 1) ∧
      ∃ mixed : Player → PMF (QuittingFiniteDeadlineTimingAction deadline),
        (quittingFiniteDeadlineTimingGame table deadline).mixedExtension.IsNash mixed ∧
          value = quittingTerminalSemanticExploitability
            (quittingTerminalSemanticPair table
              (quittingFiniteDeadlineTimingProfile table deadline mixed))}

/-- The exact worst-table, worst-equilibrium exploitability at a finite deadline. -/
def finiteDeadlineTimingNashWorstExploitability (deadline : ℕ) : ℝ :=
  sSup (finiteDeadlineTimingNashExploitabilityValues deadline)

/-- Every positive-deadline value in the defining set obeys the universal ceiling. -/
theorem finiteDeadlineTimingNashExploitabilityValues_le
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (value : ℝ) (hvalue : value ∈ finiteDeadlineTimingNashExploitabilityValues deadline) :
    value ≤ 1 / 4 + 2 / (deadline : ℝ) := by
  rcases hvalue with ⟨table, htable, mixed, hnash, rfl⟩
  unfold quittingTerminalSemanticExploitability
  apply QuittingBoundaryHolonomy.finitePlayerMax_le
  intro who
  apply max_le
  · positivity
  · have hdebt := quittingTerminalDeviationDebt_finiteDeadlineTimingProfile_le
        table deadline hdeadline mixed who (bound := 1) (by norm_num) htable hnash
    norm_num only [one_mul] at hdebt
    exact hdebt

/-- The defining set is bounded above at every positive deadline. -/
theorem finiteDeadlineTimingNashExploitabilityValues_bddAbove
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    BddAbove (finiteDeadlineTimingNashExploitabilityValues deadline) := by
  refine ⟨1 / 4 + 2 / (deadline : ℝ), ?_⟩
  intro value hvalue
  exact finiteDeadlineTimingNashExploitabilityValues_le
    deadline hdeadline value hvalue

/-- The hard-table canonical actual Nash law witnesses nonemptiness. -/
theorem finiteDeadlineTimingNashExploitabilityValues_nonempty (deadline : ℕ) :
    (finiteDeadlineTimingNashExploitabilityValues deadline).Nonempty := by
  refine ⟨quittingTerminalSemanticExploitability
    (quittingTerminalSemanticPair reward
      (quittingFiniteDeadlineTimingProfile reward deadline
        (hardDeadlineTimingNashLaw deadline))), reward, abs_reward_le_one,
      hardDeadlineTimingNashLaw deadline, hardDeadlineTimingNashLaw_isNash deadline, rfl⟩

/-- At a positive deadline, the hard table puts the exact value `D_K` in the set. -/
theorem hardDeadlineDebt_mem_finiteDeadlineTimingNashExploitabilityValues
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    hardDeadlineDebt deadline ∈ finiteDeadlineTimingNashExploitabilityValues deadline := by
  refine ⟨reward, abs_reward_le_one, hardDeadlineTimingNashLaw deadline,
    hardDeadlineTimingNashLaw_isNash deadline, ?_⟩
  exact (finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt
    deadline hdeadline (hardDeadlineTimingNashLaw deadline)
      (hardDeadlineTimingNashLaw_isNash deadline)).symm

/-- The exact hard-table value is a lower bound for the worst-table supremum. -/
theorem hardDeadlineDebt_le_finiteDeadlineTimingNashWorstExploitability
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    hardDeadlineDebt deadline ≤ finiteDeadlineTimingNashWorstExploitability deadline := by
  unfold finiteDeadlineTimingNashWorstExploitability
  exact le_csSup
    (finiteDeadlineTimingNashExploitabilityValues_bddAbove deadline hdeadline)
    (hardDeadlineDebt_mem_finiteDeadlineTimingNashExploitabilityValues
      deadline hdeadline)

/-- The exact worst-table value stays strictly above `1 / 4` at every positive deadline. -/
theorem quarter_lt_finiteDeadlineTimingNashWorstExploitability
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    1 / 4 < finiteDeadlineTimingNashWorstExploitability deadline :=
  (hardDeadlineDebt_gt_quarter deadline hdeadline).trans_le
    (hardDeadlineDebt_le_finiteDeadlineTimingNashWorstExploitability
      deadline hdeadline)

/-- The exact worst-table supremum obeys the universal finite-deadline ceiling. -/
theorem finiteDeadlineTimingNashWorstExploitability_le
    (deadline : ℕ) (hdeadline : 0 < deadline) :
    finiteDeadlineTimingNashWorstExploitability deadline ≤
      1 / 4 + 2 / (deadline : ℝ) := by
  unfold finiteDeadlineTimingNashWorstExploitability
  apply csSup_le (finiteDeadlineTimingNashExploitabilityValues_nonempty deadline)
  intro value hvalue
  exact finiteDeadlineTimingNashExploitabilityValues_le
    deadline hdeadline value hvalue

/-- The exact worst-table, worst-equilibrium value tends to `1 / 4`. -/
theorem tendsto_finiteDeadlineTimingNashWorstExploitability_succ_quarter :
    Tendsto (fun deadline : ℕ ↦
      finiteDeadlineTimingNashWorstExploitability (deadline + 1))
      atTop (nhds (1 / 4 : ℝ)) := by
  have hupper : Tendsto (fun deadline : ℕ ↦
      1 / 4 + 2 / ((deadline : ℝ) + 1)) atTop (nhds (1 / 4 : ℝ)) := by
    have hinv : Tendsto (fun deadline : ℕ ↦
        (1 : ℝ) / ((deadline : ℝ) + 1)) atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have htwo : Tendsto (fun deadline : ℕ ↦
        2 / ((deadline : ℝ) + 1)) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul 2
    simpa using tendsto_const_nhds.add htwo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_hardDeadlineDebt_succ_quarter hupper (fun deadline ↦ ?_)
      (fun deadline ↦ ?_)
  · exact hardDeadlineDebt_le_finiteDeadlineTimingNashWorstExploitability
      (deadline + 1) (by omega)
  · simpa only [Nat.cast_add, Nat.cast_one] using
      finiteDeadlineTimingNashWorstExploitability_le (deadline + 1) (by omega)

end FinFourHardDeadlineTimingNashBarrier
end GameTheory
