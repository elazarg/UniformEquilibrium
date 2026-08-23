/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.CapPumpSecondPersistentLabelBoundary
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalDebtShadowing

/-!
# Eta-adaptive chronological sharpness of the one-label cap pump

This file checks the non-survival fields of the sharp two-player boundary.
It does not manufacture the missing mover-deleted survival field.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped BigOperators Topology

namespace CapPumpChronologicalSharpBoundary

open CapPumpSecondPersistentLabelBoundary

/-- The positive Continue probability used by the eta-adaptive example. -/
def adaptiveContinue (eta : ℝ) : ℝ := min (eta / 2) (1 / 2)

theorem adaptiveContinue_pos {eta : ℝ} (heta : 0 < eta) :
    0 < adaptiveContinue eta := by
  unfold adaptiveContinue
  exact lt_min (by linarith) (by norm_num)

theorem adaptiveContinue_le_half (eta : ℝ) :
    adaptiveContinue eta ≤ 1 / 2 := min_le_right _ _

theorem adaptiveContinue_le_eta {eta : ℝ} (heta : 0 < eta) :
    adaptiveContinue eta ≤ eta := by
  exact (min_le_left _ _).trans (by linarith)

/-- Player `0` Quits with probability `1-h`; player `1` always Continues. -/
def adaptiveRoots (eta : ℝ) (heta : 0 < eta)
    (_time : ℕ) (who : Fin 2) : PMF Bool :=
  if who = 0 then
    quittingHazardCoin (1 - adaptiveContinue eta)
      (by have := adaptiveContinue_le_half eta; linarith)
      (by have := adaptiveContinue_pos heta; linarith)
  else PMF.pure false

@[simp] theorem adaptiveRoots_mover_quit
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveRoots eta heta time (0 : Fin 2) true).toReal =
      1 - adaptiveContinue eta := by
  simp [adaptiveRoots]

@[simp] theorem adaptiveRoots_mover_continue
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveRoots eta heta time (0 : Fin 2) false).toReal =
      adaptiveContinue eta := by
  simp [adaptiveRoots]

@[simp] theorem adaptiveRoots_owner_quit
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveRoots eta heta time (1 : Fin 2) true).toReal = 0 := by
  simp [adaptiveRoots]

@[simp] theorem adaptive_owner_opponentContinue
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    quittingRootOpponentContinueMass
        (adaptiveRoots eta heta time) (1 : Fin 2) =
      adaptiveContinue eta := by
  unfold quittingRootOpponentContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp [quittingAllContinueAction, adaptiveRoots, Fin.prod_univ_two]

@[simp] theorem adaptive_mover_opponentContinue
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    quittingRootOpponentContinueMass
        (adaptiveRoots eta heta time) (0 : Fin 2) = 1 := by
  unfold quittingRootOpponentContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp [quittingAllContinueAction, adaptiveRoots, Fin.prod_univ_two]

theorem quittingTerminalSemanticPair_zeroReward
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (profile : (quittingGame (zeroReward (ι := ι))).BehaviorProfile) :
    quittingTerminalSemanticPair zeroReward profile =
      ((0 : Payoff ι), (0 : Payoff ι)) := by
  apply Prod.ext <;> funext who
  · have hbound := abs_quittingTerminalPayoff_le
      zeroReward profile who (M := 0) (by simp [zeroReward])
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  · have hbound := abs_quittingContinuationBestResponseValue_le
      zeroReward profile who (M := 0) (by simp [zeroReward])
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

/-- Prefixing a nonnegative candidate cap in the zero game multiplies it by
the literal deleted-player Continue mass. -/
theorem quittingTerminalSemanticPrefix_zeroReward_snd
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) (cap : Payoff ι) (who : ι)
    (hcap : 0 ≤ cap who) :
    (quittingTerminalSemanticPrefix zeroReward root
        ((0 : Payoff ι), cap)).2 who =
      quittingRootOpponentContinueMass root who * cap who := by
  unfold quittingTerminalSemanticPrefix quittingRootQuitPayoff
    quittingRootContinuePayoff
  dsimp only [Prod.fst, Prod.snd]
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp only [quittingRootAbsorbingContribution_zeroReward, zero_add,
    Pi.zero_apply, Function.update_self, mul_zero]
  rw [max_eq_right
    (mul_nonneg (quittingStationaryContinueMass_nonneg _) hcap)]
  rfl

@[simp] theorem quittingRootSuccessorPayoff_zeroReward_zero
    {ι : Type} [Fintype ι] [DecidableEq ι] (root : ι → PMF Bool) :
    quittingRootSuccessorPayoff zeroReward (0 : Payoff ι) root = 0 := by
  funext who
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp

@[simp] theorem quittingTerminalSemanticPrefix_zeroReward_fst
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) (cap : Payoff ι) :
    (quittingTerminalSemanticPrefix zeroReward root
      ((0 : Payoff ι), cap)).1 = 0 := by
  exact quittingRootSuccessorPayoff_zeroReward_zero root

/-- Candidate annotations: prescribed value zero, and debt/secant `h` only
in the observer coordinate. -/
def adaptiveData (eta : ℝ) (heta : 0 < eta) :
    QuittingChronologicalDebtData (Fin 2) where
  roots := adaptiveRoots eta heta
  prescribed := fun _ _ => 0
  debt := fun _ who => if who = 1 then adaptiveContinue eta else 0
  secant := fun _ who => if who = 1 then adaptiveContinue eta else 0

@[simp] theorem adaptiveData_root
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).root time = adaptiveRoots eta heta time := rfl

@[simp] theorem adaptiveData_semanticPair
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).semanticPair zeroReward time =
      ((0 : Payoff (Fin 2)), (0 : Payoff (Fin 2))) :=
  quittingTerminalSemanticPair_zeroReward _

@[simp] theorem adaptiveData_candidateSuccessorPair
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).candidateSuccessorPair time =
      ((0 : Payoff (Fin 2)),
        fun who => if who = 1 then adaptiveContinue eta else 0) := by
  apply Prod.ext <;> funext who <;>
    simp [QuittingChronologicalDebtData.candidateSuccessorPair, adaptiveData]

@[simp] theorem adaptiveData_prefix_candidate_mover
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (quittingTerminalSemanticPrefix zeroReward
      ((adaptiveData eta heta).root time)
      ((adaptiveData eta heta).candidateSuccessorPair time)).2 (0 : Fin 2) =
      0 := by
  rw [adaptiveData_candidateSuccessorPair]
  rw [quittingTerminalSemanticPrefix_zeroReward_snd]
  · simp
  · simp

@[simp] theorem adaptiveData_prefix_candidate_owner
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (quittingTerminalSemanticPrefix zeroReward
      ((adaptiveData eta heta).root time)
      ((adaptiveData eta heta).candidateSuccessorPair time)).2 (1 : Fin 2) =
      adaptiveContinue eta ^ 2 := by
  rw [adaptiveData_candidateSuccessorPair,
    quittingTerminalSemanticPrefix_zeroReward_snd]
  · change quittingRootOpponentContinueMass
        (adaptiveRoots eta heta time) 1 * adaptiveContinue eta = _
    rw [adaptive_owner_opponentContinue]
    ring
  · simp [(adaptiveContinue_pos heta).le]

@[simp] theorem adaptiveData_prescribedDefect
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).prescribedDefect zeroReward time = 0 := by
  funext who
  unfold QuittingChronologicalDebtData.prescribedDefect
  rw [adaptiveData_candidateSuccessorPair]
  change 0 -
    (quittingTerminalSemanticPrefix zeroReward _
      ((0 : Payoff (Fin 2)), _)).1 who = 0
  rw [quittingTerminalSemanticPrefix_zeroReward_fst]
  simp

@[simp] theorem adaptiveData_directDebtDefect_mover
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).directDebtDefect zeroReward time (0 : Fin 2) = 0 := by
  rw [QuittingChronologicalDebtData.directDebtDefect]
  unfold quittingTerminalSemanticDebt
  rw [adaptiveData_prefix_candidate_mover]
  change 0 - (0 - _) = 0
  rw [adaptiveData_candidateSuccessorPair,
    quittingTerminalSemanticPrefix_zeroReward_fst]
  simp

/-- The observer's exact global direct defect is `h-h^2`. -/
@[simp] theorem adaptiveData_directDebtDefect_owner
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).directDebtDefect zeroReward time (1 : Fin 2) =
      adaptiveContinue eta - adaptiveContinue eta ^ 2 := by
  rw [QuittingChronologicalDebtData.directDebtDefect]
  unfold quittingTerminalSemanticDebt
  rw [adaptiveData_prefix_candidate_owner]
  change adaptiveContinue eta - (adaptiveContinue eta ^ 2 - _) = _
  rw [adaptiveData_candidateSuccessorPair,
    quittingTerminalSemanticPrefix_zeroReward_fst]
  simp

@[simp] theorem adaptiveData_secant_owner
    {eta : ℝ} (heta : 0 < eta) (time : ℕ) :
    (adaptiveData eta heta).secant time (1 : Fin 2) =
      adaptiveContinue eta := rfl

/-- Every finite adverse forcing sum is already nonpositive. -/
theorem adaptiveData_adverseDirectForcing_nonpos
    {eta : ℝ} (heta : 0 < eta) (who : Fin 2) (start length : ℕ) :
    -∑ offset ∈ Finset.range length,
      Math.survivalProduct
          (fun time => (adaptiveData eta heta).secant time who)
          start offset *
        (adaptiveData eta heta).directDebtDefect zeroReward
          (start + offset) who ≤ 0 := by
  refine Fin.cases ?_ (fun remaining => ?_) who
  · have hsum : (∑ offset ∈ Finset.range length,
        Math.survivalProduct
            (fun time => (adaptiveData eta heta).secant time (0 : Fin 2))
            start offset *
          (adaptiveData eta heta).directDebtDefect zeroReward
            (start + offset) (0 : Fin 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro offset _
      rw [adaptiveData_directDebtDefect_mover, mul_zero]
    rw [hsum, neg_zero]
  · have hremaining : remaining = 0 := Subsingleton.elim _ _
    subst remaining
    apply neg_nonpos.mpr
    apply Finset.sum_nonneg
    intro offset _
    apply mul_nonneg
    · exact Math.survivalProduct_nonneg _
        (fun time => by
          simp [adaptiveData, (adaptiveContinue_pos heta).le]) start offset
    · change 0 ≤ (adaptiveData eta heta).directDebtDefect zeroReward
        (start + offset) (1 : Fin 2)
      rw [adaptiveData_directDebtDefect_owner]
      have hpositive := adaptiveContinue_pos heta
      have hhalf := adaptiveContinue_le_half eta
      nlinarith

/-- Deleting the sole mover leaves the observer's survival identically one,
so the eta-adaptive annotations cannot form a full chronological certificate. -/
@[simp] theorem adaptive_moverDeletedSurvival
    {eta : ℝ} (heta : 0 < eta) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight (adaptiveRoots eta heta)
      (0 : Fin 2) start fuel = 1 := by
  have hmass : ∀ time,
      quittingFixedOpponentsContinueMass (adaptiveRoots eta heta)
        (0 : Fin 2) time = 1 := by
    intro time
    change quittingRootOpponentContinueMass
      (adaptiveRoots eta heta time) (0 : Fin 2) = 1
    exact adaptive_mover_opponentContinue heta time
  simp [quittingOpponentSurvivalWeight, hmass]

/-- The fields of the chronological certificate other than the two survival
limits, isolated so the sharp obstruction cannot be mistaken for a full
certificate. -/
structure AnalyticFields (eta : ℝ) : Prop where
  eta_pos : 0 < eta
  debt_nonneg : ∀ time who, 0 ≤ (adaptiveData eta eta_pos).debt time who
  prescribed_bounded : ∃ bound : ℝ,
    ∀ time who, |(adaptiveData eta eta_pos).prescribed time who| ≤ bound
  debt_bounded : ∃ bound : ℝ,
    ∀ time who, |(adaptiveData eta eta_pos).debt time who| ≤ bound
  secant_nonneg : ∀ time who,
    0 ≤ (adaptiveData eta eta_pos).secant time who
  secant_le_opponentContinue : ∀ time who,
    (adaptiveData eta eta_pos).secant time who ≤
      quittingRootOpponentContinueMass
        ((adaptiveData eta eta_pos).root time) who
  secant_generated : ∀ time who,
    ((adaptiveData eta eta_pos).semanticPair zeroReward time).2 who -
        (quittingTerminalSemanticPrefix zeroReward
          ((adaptiveData eta eta_pos).root time)
          ((adaptiveData eta eta_pos).candidateSuccessorPair time)).2 who =
      (adaptiveData eta eta_pos).secant time who *
        (((adaptiveData eta eta_pos).semanticPair zeroReward (time + 1)).2 who -
          ((adaptiveData eta eta_pos).candidateSuccessorPair time).2 who)
  prescribed_discrepancy : ∀ who start length,
    |∑ offset ∈ Finset.range length,
      (adaptiveData eta eta_pos).prescribedDefect zeroReward
        (start + offset) who| ≤ eta
  adverse_direct_forcing : ∀ who start slack, 0 < slack →
    ∀ᶠ length in atTop,
      -∑ offset ∈ Finset.range length,
        Math.survivalProduct
            (fun time => (adaptiveData eta eta_pos).secant time who)
            start offset *
          (adaptiveData eta eta_pos).directDebtDefect zeroReward
            (start + offset) who ≤ eta + slack
  initial_debt_le : ∀ who, (adaptiveData eta eta_pos).debt 0 who ≤ eta

/-- Every non-survival chronological field holds for the eta-adaptive sharp
one-label boundary. -/
theorem analyticFields (eta : ℝ) (heta : 0 < eta) : AnalyticFields eta := by
  refine {
    eta_pos := heta
    debt_nonneg := ?_
    prescribed_bounded := ?_
    debt_bounded := ?_
    secant_nonneg := ?_
    secant_le_opponentContinue := ?_
    secant_generated := ?_
    prescribed_discrepancy := ?_
    adverse_direct_forcing := ?_
    initial_debt_le := ?_ }
  · intro time
    rw [Fin.forall_fin_two]
    constructor <;> simp [adaptiveData, (adaptiveContinue_pos heta).le]
  · exact ⟨0, by simp [adaptiveData]⟩
  · refine ⟨1 / 2, ?_⟩
    intro time
    rw [Fin.forall_fin_two]
    constructor
    · norm_num [adaptiveData]
    · change |adaptiveContinue eta| ≤ 1 / 2
      rw [abs_of_pos (adaptiveContinue_pos heta)]
      exact adaptiveContinue_le_half eta
  · intro time
    rw [Fin.forall_fin_two]
    constructor <;> simp [adaptiveData, (adaptiveContinue_pos heta).le]
  · intro time
    rw [Fin.forall_fin_two]
    constructor
    · exact quittingRootOpponentContinueMass_nonneg _ _
    · change adaptiveContinue eta ≤
        quittingRootOpponentContinueMass (adaptiveRoots eta heta time) 1
      rw [adaptive_owner_opponentContinue]
  · intro time
    rw [Fin.forall_fin_two]
    constructor
    · rw [adaptiveData_semanticPair, adaptiveData_prefix_candidate_mover,
        adaptiveData_semanticPair, adaptiveData_candidateSuccessorPair]
      simp [adaptiveData]
    · rw [adaptiveData_semanticPair, adaptiveData_prefix_candidate_owner,
        adaptiveData_semanticPair, adaptiveData_candidateSuccessorPair]
      simp [adaptiveData, pow_two]
  · intro who start length
    simp [heta.le]
  · intro who start slack hslack
    filter_upwards [] with length
    exact (adaptiveData_adverseDirectForcing_nonpos heta who start length).trans
      (by linarith)
  · rw [Fin.forall_fin_two]
    constructor
    · simp [adaptiveData, heta.le]
    · simpa [adaptiveData] using adaptiveContinue_le_eta heta

end CapPumpChronologicalSharpBoundary

end GameTheory
