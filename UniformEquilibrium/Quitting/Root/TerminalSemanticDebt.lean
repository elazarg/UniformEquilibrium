/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Basic terminal semantic debt

This module collects the total-debt functional, its elementary continuity
bounds, and coordinatewise nonnegativity on the compact semantic carrier.
It does not state minimum-stratum rigidity or any prefix descent theorem.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total debt of a finite-dimensional terminal semantic pair. -/
def quittingTerminalSemanticDebtSum
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, quittingTerminalSemanticDebt pair who

omit [DecidableEq ι] in
/-- Total terminal semantic debt is Lipschitz for the coordinatewise
prescribed-payoff/cap `L¹` distance. -/
theorem abs_quittingTerminalSemanticDebtSum_sub_le
    (first second : QuittingTerminalSemanticPair ι) :
    |quittingTerminalSemanticDebtSum first -
        quittingTerminalSemanticDebtSum second| ≤
      ∑ who, (|first.1 who - second.1 who| +
        |first.2 who - second.2 who|) := by
  unfold quittingTerminalSemanticDebtSum
  calc
    |∑ who, quittingTerminalSemanticDebt first who -
        ∑ who, quittingTerminalSemanticDebt second who| =
      |∑ who, (quittingTerminalSemanticDebt first who -
        quittingTerminalSemanticDebt second who)| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ who, |quittingTerminalSemanticDebt first who -
        quittingTerminalSemanticDebt second who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ who, (|first.1 who - second.1 who| +
        |first.2 who - second.2 who|) := by
      exact Finset.sum_le_sum fun who _ =>
        abs_quittingTerminalSemanticDebt_sub_le first second who

omit [DecidableEq ι] in
/-- Summing one-sided coordinate implementation bounds gives the literal
total-debt implementation bound. -/
theorem quittingTerminalSemanticDebtSum_le_of_oneSidedImplementation
    (seed actual : QuittingTerminalSemanticPair ι)
    (eta : ι → ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta who)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤ actual.1 who)
    (hcap : ∀ who, actual.2 who ≤ seed.2 who + capError who) :
    quittingTerminalSemanticDebtSum actual ≤
      ∑ who, (eta who + payoffError who + capError who) := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_le_sum fun who _ =>
    quittingTerminalSemanticDebt_le_of_oneSidedImplementation
      seed actual who (eta who) (payoffError who) (capError who)
        (hseed who) (hpayoff who) (hcap who)

omit [Fintype ι] [DecidableEq ι] in
/-- Every semantic-debt coordinate is continuous. -/
theorem continuous_quittingTerminalSemanticDebt (who : ι) :
    Continuous (fun pair : QuittingTerminalSemanticPair ι =>
      quittingTerminalSemanticDebt pair who) := by
  unfold quittingTerminalSemanticDebt
  fun_prop

omit [DecidableEq ι] in
/-- Total terminal semantic debt is continuous. -/
theorem continuous_quittingTerminalSemanticDebtSum :
    Continuous (quittingTerminalSemanticDebtSum :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticDebtSum
  exact continuous_finsetSum
    (s := (Finset.univ : Finset ι)) fun who _ =>
      continuous_quittingTerminalSemanticDebt who

/-- Literal semantic pairs have nonnegative debt in every coordinate. -/
theorem quittingTerminalSemanticDebt_nonneg_of_attainable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingAttainableTerminalSemanticPairs reward) :
    ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
  rintro who
  obtain ⟨profile, rfl⟩ := hpair
  exact quittingTerminalDeviationDebt_nonneg reward profile who

/-- Nonnegative debt extends to the compact attainable-semantic closure. -/
theorem quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      ∀ who, 0 ≤ quittingTerminalSemanticDebt candidate who} := by
    rw [show {candidate : QuittingTerminalSemanticPair ι |
        ∀ who, 0 ≤ quittingTerminalSemanticDebt candidate who} =
      ⋂ who, {candidate | 0 ≤ quittingTerminalSemanticDebt candidate who} by
        ext candidate
        simp]
    exact isClosed_iInter fun who =>
      isClosed_le continuous_const
        (continuous_quittingTerminalSemanticDebt who)
  exact (closure_minimal
    (fun candidate hcandidate =>
      quittingTerminalSemanticDebt_nonneg_of_attainable reward hcandidate)
    hclosed) hpair

end GameTheory
