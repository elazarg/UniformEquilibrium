/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

/-!
# Terminal-semantic implementation barrier

A coordinatewise low-debt semantic seed constrains the literal terminal debt
of an actual behavior profile only when both prescribed payoff and unilateral
response cap are implemented one-sidedly.  Summing those errors gives the
global minimum-debt obstruction, its sharp cardinality-four constants, and an
average-coordinate error witness.

These are implementation inequalities.  They do not produce a semantic seed,
an implementing profile, or a uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- One-sided implementation of a low-debt seed bounds the actual profile's
literal debt in each player coordinate. -/
theorem quittingTerminalDeviationDebt_le_of_seedImplementation
    (seed : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (eta : ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff reward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue reward profile who ≤
        seed.2 who + capError who)
    (who : ι) :
    quittingTerminalDeviationDebt reward profile who ≤
      eta + payoffError who + capError who := by
  exact quittingTerminalSemanticDebt_le_of_oneSidedImplementation
    seed (quittingTerminalSemanticPair reward profile) who eta
      (payoffError who) (capError who) (hseed who) (hpayoff who) (hcap who)

/-- Summing the coordinate implementation inequalities gives the literal
actual-profile debt bound. -/
theorem quittingTerminalDebtSum_le_of_seedImplementation
    (seed : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (eta : ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff reward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue reward profile who ≤
        seed.2 who + capError who) :
    quittingTerminalDebtSum reward profile ≤
      (Fintype.card ι : ℝ) * eta +
        ∑ who, (payoffError who + capError who) := by
  rw [quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
  calc
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      ∑ who, (eta + payoffError who + capError who) :=
        quittingTerminalSemanticDebtSum_le_of_oneSidedImplementation
          seed (quittingTerminalSemanticPair reward profile)
          (fun _ => eta) payoffError capError hseed hpayoff hcap
    _ = (Fintype.card ι : ℝ) * eta +
        ∑ who, (payoffError who + capError who) := by
      simp_rw [add_assoc]
      rw [Finset.sum_add_distrib]
      simp

/-- Any explicit lower floor valid for every actual profile is bounded by the
seed debt allowance plus its implementation errors. -/
theorem minimumDebt_le_of_globalFloor_of_seedImplementation
    (minimumDebt : ℝ)
    (hfloor : ∀ actual : (quittingGame reward).BehaviorProfile,
      minimumDebt ≤ quittingTerminalDebtSum reward actual)
    (seed : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (eta : ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff reward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue reward profile who ≤
        seed.2 who + capError who) :
    minimumDebt ≤ (Fintype.card ι : ℝ) * eta +
      ∑ who, (payoffError who + capError who) :=
  (hfloor profile).trans
    (quittingTerminalDebtSum_le_of_seedImplementation
      seed profile eta payoffError capError hseed hpayoff hcap)

/-- The canonical infimum over actual profiles obeys the same implementation
barrier. -/
theorem quittingTerminalDebtSumInf_le_of_seedImplementation
    (seed : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (eta : ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff reward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue reward profile who ≤
        seed.2 who + capError who) :
    quittingTerminalDebtSumInf reward ≤
      (Fintype.card ι : ℝ) * eta +
        ∑ who, (payoffError who + capError who) :=
  (quittingTerminalDebtSumInf_le profile).trans
    (quittingTerminalDebtSum_le_of_seedImplementation
      seed profile eta payoffError capError hseed hpayoff hcap)

/-- For four players, separate payoff and cap errors bounded by `delta` cost
exactly the displayed `8 * delta` aggregate allowance. -/
theorem quittingTerminalDebtSumInf_le_four_eta_add_eight_delta
    (finFourReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (seed : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame finFourReward).BehaviorProfile)
    (eta delta : ℝ) (payoffError capError : Fin 4 → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff finFourReward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue finFourReward profile who ≤
        seed.2 who + capError who)
    (hpayoffError : ∀ who, payoffError who ≤ delta)
    (hcapError : ∀ who, capError who ≤ delta) :
    quittingTerminalDebtSumInf finFourReward ≤ 4 * eta + 8 * delta := by
  have hbase := quittingTerminalDebtSumInf_le_of_seedImplementation
    (reward := finFourReward) seed profile eta payoffError capError
      hseed hpayoff hcap
  have herrors :
      (∑ who, (payoffError who + capError who)) ≤ 8 * delta := by
    calc
      (∑ who, (payoffError who + capError who)) ≤
          ∑ _who : Fin 4, (delta + delta) :=
        Finset.sum_le_sum fun who _ => add_le_add
          (hpayoffError who) (hcapError who)
      _ = 8 * delta := by simp; ring
  norm_num at hbase
  linarith

/-- For four players, a bound on each combined payoff/cap error costs the
displayed `4 * delta` aggregate allowance. -/
theorem quittingTerminalDebtSumInf_le_four_eta_add_four_delta
    (finFourReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (seed : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame finFourReward).BehaviorProfile)
    (eta delta : ℝ) (payoffError capError : Fin 4 → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff finFourReward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue finFourReward profile who ≤
        seed.2 who + capError who)
    (hcombinedError : ∀ who,
      payoffError who + capError who ≤ delta) :
    quittingTerminalDebtSumInf finFourReward ≤ 4 * eta + 4 * delta := by
  have hbase := quittingTerminalDebtSumInf_le_of_seedImplementation
    (reward := finFourReward) seed profile eta payoffError capError
      hseed hpayoff hcap
  have herrors :
      (∑ who, (payoffError who + capError who)) ≤ 4 * delta := by
    calc
      (∑ who, (payoffError who + capError who)) ≤
          ∑ _who : Fin 4, delta :=
        Finset.sum_le_sum fun who _ => hcombinedError who
      _ = 4 * delta := by simp
  norm_num at hbase
  linarith

/-- If an explicit global debt floor exceeds the aggregate seed allowance,
one coordinate pays at least the average excess in implementation error. -/
theorem exists_seedImplementationError_ge_average_of_globalFloor
    [Nonempty ι]
    (minimumDebt : ℝ)
    (hfloor : ∀ actual : (quittingGame reward).BehaviorProfile,
      minimumDebt ≤ quittingTerminalDebtSum reward actual)
    (seed : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (eta : ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff reward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue reward profile who ≤
        seed.2 who + capError who) :
    ∃ who,
      (minimumDebt - (Fintype.card ι : ℝ) * eta) /
          Fintype.card ι ≤
        payoffError who + capError who := by
  have htotal := minimumDebt_le_of_globalFloor_of_seedImplementation
    minimumDebt hfloor seed profile eta payoffError capError
      hseed hpayoff hcap
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card ι ≠ 0)
  have hconstant :
      (∑ _who : ι,
        (minimumDebt - (Fintype.card ι : ℝ) * eta) /
          Fintype.card ι) =
        minimumDebt - (Fintype.card ι : ℝ) * eta := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hsum :
      (∑ _who : ι,
        (minimumDebt - (Fintype.card ι : ℝ) * eta) /
          Fintype.card ι) ≤
        ∑ who, (payoffError who + capError who) := by
    rw [hconstant]
    linarith
  obtain ⟨who, _hwho, hwho⟩ :=
    Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨who, hwho⟩

/-- Canonical-infimum specialization of the average-coordinate
implementation obstruction. -/
theorem exists_seedImplementationError_ge_average_of_debtSumInf
    [Nonempty ι]
    (seed : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (eta : ℝ) (payoffError capError : ι → ℝ)
    (hseed : ∀ who, quittingTerminalSemanticDebt seed who ≤ eta)
    (hpayoff : ∀ who,
      seed.1 who - payoffError who ≤
        quittingTerminalPayoff reward profile who)
    (hcap : ∀ who,
      quittingContinuationBestResponseValue reward profile who ≤
        seed.2 who + capError who) :
    ∃ who,
      (quittingTerminalDebtSumInf reward -
          (Fintype.card ι : ℝ) * eta) / Fintype.card ι ≤
        payoffError who + capError who := by
  exact exists_seedImplementationError_ge_average_of_globalFloor
    (quittingTerminalDebtSumInf reward)
    (fun actual => quittingTerminalDebtSumInf_le actual)
    seed profile eta payoffError capError hseed hpayoff hcap

end GameTheory
