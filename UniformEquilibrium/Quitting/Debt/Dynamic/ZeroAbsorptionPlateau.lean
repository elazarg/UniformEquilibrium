/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.SeamPriceResidual
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapBridge

/-!
# Zero-absorption exact dynamic-debt plateaus

An exact edge with zero absorption preserves prescribed payoff and dynamic
debt, and its current root is all-Continue. Two consecutive zero-absorption
edges therefore collapse to a literal all-Continue plateau. The successor's
stored root is not controlled by the first edge and remains a next-edge
control coordinate.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Exact diagnosis of the projective zero-scale limit -/

/-- At an all-Continue current state, the exact augmented edge imposes no
condition on the stored root of the successor.  Payoff and debt can stay
fixed while that successor root is chosen arbitrarily.  Thus the root
coordinate is a control for the next edge, not a state coordinate whose
increment is controlled by the current edge's absorption mass. -/
theorem allContinue_dynamicDebtEdge_ignores_successorRoot
    (value debt : Payoff ι) (successorRoot : QuittingRootSimplex ι)
    (hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ value who)
    (hdebt : 0 ≤ debt) :
    IsQuittingDynamicDebtEdge reward
      (((value, quittingAllContinueSimplexRoot), debt) :
        QuittingDebtPoint ι)
      (((value, successorRoot), debt) : QuittingDebtPoint ι) := by
  have hnash : IsεQuittingRootNash reward value 0
      (quittingAllContinueRoot : ι → PMF Bool) :=
    quittingAllContinueRoot_isZeroNash_of_singleton_le reward value hsolo
  have hbellman : IsQuittingNashBellmanEdge reward
      (value, quittingAllContinueSimplexRoot) (value, successorRoot) := by
    constructor
    · change value = quittingRootSuccessorPayoff reward value
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        quittingRootSuccessorPayoff_allContinueRoot_eq]
    · change IsεQuittingRootEndpointNash reward value 0
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
      exact hnash
  refine ⟨hbellman, fun who ↦ ?_⟩
  have hopponent : quittingDebtOpponentContinueMass
      (((value, quittingAllContinueSimplexRoot), debt) :
        QuittingDebtPoint ι) who = 1 := by
    rw [quittingDebtOpponentContinueMass_eq_stationary,
      quittingRootOfSimplex_allContinueSimplexRoot]
    rw [show Function.update quittingAllContinueRoot who (PMF.pure false) =
        quittingAllContinueRoot by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingAllContinueRoot]
      · simp [Function.update_of_ne hplayer, quittingAllContinueRoot]]
    have habs := quittingRootAbsorptionMass_allContinueRoot (ι := ι)
    unfold quittingRootAbsorptionMass at habs
    linarith
  unfold quittingDynamicDebtUpdate
  rw [quittingRootOfSimplex_allContinueSimplexRoot,
    quittingRootQuitPayoff_allContinueRoot,
    quittingRootContinuePayoff_allContinueRoot, hopponent]
  rw [max_eq_right]
  · ring
  · apply (hsolo who).trans
    apply le_add_of_nonneg_right
    simpa using hdebt who

/-- A zero-absorption exact dynamic-debt edge preserves both payoff and debt;
its current root is all-Continue.  Thus vanishing absorption does not identify
the common payoff with terminal semantics. -/
theorem zeroAbsorption_dynamicDebtEdge_plateau
    (current successor : QuittingDebtPoint ι)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hzero : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) = 0) :
    current.1.1 = successor.1.1 ∧
      current.2 = successor.2 ∧
      quittingRootOfSimplex current.1.2 = quittingAllContinueRoot := by
  have hmass : quittingStationaryContinueMass
      (quittingRootOfSimplex current.1.2) = 1 := by
    unfold quittingRootAbsorptionMass at hzero
    linarith
  have hroot : quittingRootOfSimplex current.1.2 =
      quittingAllContinueRoot :=
    eq_quittingAllContinueRoot_of_continueMass_eq_one _ hmass
  have hvalue : current.1.1 = successor.1.1 := by
    rw [hedge.1.1, hroot]
    exact quittingRootSuccessorPayoff_allContinueRoot_eq reward successor.1.1
  have hopponent (who : ι) :
      quittingDebtOpponentContinueMass current who = 1 := by
    rw [quittingDebtOpponentContinueMass_eq_stationary, hroot]
    rw [show Function.update quittingAllContinueRoot who (PMF.pure false) =
        quittingAllContinueRoot by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingAllContinueRoot]
      · simp [Function.update_of_ne hplayer, quittingAllContinueRoot]]
    have habs := quittingRootAbsorptionMass_allContinueRoot (ι := ι)
    unfold quittingRootAbsorptionMass at habs
    linarith
  have hdebt : current.2 = successor.2 := by
    funext who
    have hcontinue : 0 <
        (quittingRootOfSimplex current.1.2 who false).toReal := by
      rw [hroot]
      simp [quittingAllContinueRoot]
    have hpropagate :=
      quittingDynamicDebt_eq_opponentContinueMass_mul_of_continue_pos
        reward current successor hedge hsuccessorDebt who hcontinue
    rw [hopponent, one_mul] at hpropagate
    exact hpropagate
  exact ⟨hvalue, hdebt, hroot⟩

/-- Two consecutive zero-absorption edges collapse to a literal positive-debt
all-Continue self-loop.  This is exactly the phantom plateau obtained from a
two-scale compact limit; no terminal payoff is produced. -/
theorem two_zeroAbsorption_dynamicDebtEdges_collapse_to_plateau
    (first second third : QuittingDebtPoint ι)
    (hsecondDebt : 0 ≤ second.2) (hthirdDebt : 0 ≤ third.2)
    (hfirstEdge : IsQuittingDynamicDebtEdge reward first second)
    (hsecondEdge : IsQuittingDynamicDebtEdge reward second third)
    (hfirstZero : quittingRootAbsorptionMass
      (quittingRootOfSimplex first.1.2) = 0)
    (hsecondZero : quittingRootAbsorptionMass
      (quittingRootOfSimplex second.1.2) = 0)
    {gap : ℝ} (hgap : gap ≤ ∑ who, third.2 who) :
    first = second ∧
      gap ≤ ∑ who, second.2 who ∧
      quittingRootOfSimplex first.1.2 = quittingAllContinueRoot := by
  obtain ⟨hvalueFirst, hdebtFirst, hrootFirst⟩ :=
    zeroAbsorption_dynamicDebtEdge_plateau
      first second hsecondDebt hfirstEdge hfirstZero
  obtain ⟨_valueSecond, hdebtSecond, hrootSecond⟩ :=
    zeroAbsorption_dynamicDebtEdge_plateau
      second third hthirdDebt hsecondEdge hsecondZero
  have hsimplex : first.1.2 = second.1.2 := by
    funext who
    apply (stdSimplexEquiv (α := Bool)).symm.injective
    exact congrFun (hrootFirst.trans hrootSecond.symm) who
  have hstate : first = second := by
    apply Prod.ext
    · exact Prod.ext hvalueFirst hsimplex
    · exact hdebtFirst
  refine ⟨hstate, ?_, hrootFirst⟩
  rw [hdebtSecond]
  exact hgap

/-- Two consecutive literal all-Continue roots on an exact dynamic-debt tail
force equality of the complete augmented states. -/
theorem quittingDynamicDebtPoint_eq_successor_of_two_allContinue
    (current successor : QuittingDebtPoint ι)
    (hsuccessorDebt : 0 ≤ successor.2)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hcurrent : quittingRootOfSimplex current.1.2 =
      (quittingAllContinueRoot : ι → PMF Bool))
    (hsuccessor : quittingRootOfSimplex successor.1.2 =
      (quittingAllContinueRoot : ι → PMF Bool)) :
    current = successor := by
  have hzero : quittingRootAbsorptionMass
      (quittingRootOfSimplex current.1.2) = 0 := by
    rw [hcurrent]
    exact quittingRootAbsorptionMass_allContinueRoot
  obtain ⟨hvalue, hdebt, _⟩ :=
    zeroAbsorption_dynamicDebtEdge_plateau
      current successor hsuccessorDebt hedge hzero
  have hroot : current.1.2 = successor.1.2 := by
    funext who
    apply (stdSimplexEquiv (α := Bool)).symm.injective
    exact congrFun (hcurrent.trans hsuccessor.symm) who
  apply Prod.ext
  · exact Prod.ext hvalue hroot
  · exact hdebt

/-- An exact dynamic-debt tail which is literally all-Continue from a
threshold onward is a constant augmented state from that threshold onward. -/
theorem quittingDynamicDebtTail_eq_threshold_of_eventually_allContinue
    (tail : ℕ → QuittingDebtPoint ι)
    (hdebtNonneg : ∀ time, 0 ≤ (tail time).2)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (threshold : ℕ)
    (hroot : ∀ time, threshold ≤ time →
      quittingRootOfSimplex (tail time).1.2 =
        (quittingAllContinueRoot : ι → PMF Bool)) :
    ∀ time, threshold ≤ time → tail time = tail threshold := by
  intro time htime
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le htime
  induction offset with
  | zero => rfl
  | succ offset ih =>
      have hstep : tail (threshold + offset) =
          tail (threshold + offset + 1) :=
        quittingDynamicDebtPoint_eq_successor_of_two_allContinue
          (tail (threshold + offset)) (tail (threshold + offset + 1))
          (hdebtNonneg (threshold + offset + 1))
          (hedge (threshold + offset))
          (hroot (threshold + offset) (Nat.le_add_right _ _))
          (hroot (threshold + offset + 1) (by omega))
      rw [Nat.add_succ, ← hstep]
      exact ih (Nat.le_add_right _ _)

end GameTheory
