import UniformEquilibrium.Diagnostics.Quitting.PivotRepairRationalResponseCoefficients

noncomputable section

namespace GameTheory.PivotRepairRationalOptimizer

open Math.LinearProgramming
open PivotRepairRationalFixture
open PivotRepairRationalLowerBound
open PivotRepairRationalResponseCoefficients

def optimizerMass (N : ℕ) (hN : 1 ≤ N) : PivotRepairMass N
  | Sum.inl time => if time = tauIndex N hN then 88 / 107 else 0
  | Sum.inr .late => 19 / 107
  | Sum.inr .never => 0
  | Sum.inr .firstAtom => 19 / 214

theorem optimizerMass_feasible (N : ℕ) (hN : 1 ≤ N) :
    IsPivotRepairMassFeasible (optimizerMass N hN) := by
  refine ⟨?_, by norm_num [pivotRepairLate, optimizerMass],
    by norm_num [pivotRepairNever, optimizerMass],
    ?_, by norm_num [pivotRepairFirstAtom, pivotRepairLate, optimizerMass]⟩
  · intro time
    simp only [pivotRepairHead, optimizerMass]
    split <;> norm_num
  · rw [show (∑ time : Fin N, pivotRepairHead (optimizerMass N hN) time) =
        88 / 107 by
      unfold pivotRepairHead optimizerMass
      rw [Finset.sum_ite_eq' Finset.univ (tauIndex N hN)]
      norm_num]
    norm_num [pivotRepairLate, pivotRepairNever, optimizerMass]

@[simp] theorem optimizerMass_head_tau (N : ℕ) (hN : 1 ≤ N) :
    pivotRepairHead (optimizerMass N hN) (tauIndex N hN) = 88 / 107 := by
  simp [pivotRepairHead, optimizerMass]

@[simp] theorem optimizerMass_head_ne_tau (N : ℕ) (hN : 1 ≤ N)
    {time : Fin N} (hne : time ≠ tauIndex N hN) :
    pivotRepairHead (optimizerMass N hN) time = 0 := by
  simp [pivotRepairHead, optimizerMass, hne]

@[simp] theorem optimizerMass_late (N : ℕ) (hN : 1 ≤ N) :
    pivotRepairLate (optimizerMass N hN) = 19 / 107 := by
  norm_num [pivotRepairLate, optimizerMass]

@[simp] theorem optimizerMass_never (N : ℕ) (hN : 1 ≤ N) :
    pivotRepairNever (optimizerMass N hN) = 0 := by
  rfl

@[simp] theorem optimizerMass_firstAtom (N : ℕ) (hN : 1 ≤ N) :
    pivotRepairFirstAtom (optimizerMass N hN) = 19 / 214 := by
  norm_num [pivotRepairFirstAtom, optimizerMass]

theorem optimizerMass_beforeMass (N : ℕ) (hN : 1 ≤ N) :
    beforeMass hN (optimizerMass N hN) = 0 := by
  unfold beforeMass
  apply Finset.sum_eq_zero
  intro time htime
  exact optimizerMass_head_ne_tau N hN (Finset.mem_erase.mp htime).1

theorem optimizerMass_atMass (N : ℕ) (hN : 1 ≤ N) :
    atMass hN (optimizerMass N hN) = 88 / 107 := by
  exact optimizerMass_head_tau N hN

private theorem optimizerMass_headWeightedSum (N : ℕ) (hN : 1 ≤ N)
    (coefficient : Fin N → ℝ) :
    (∑ time, pivotRepairHead (optimizerMass N hN) time * coefficient time) =
      (88 / 107) * coefficient (tauIndex N hN) := by
  rw [Finset.sum_eq_single (tauIndex N hN)]
  · rw [optimizerMass_head_tau]
  · intro time _ hne
    rw [optimizerMass_head_ne_tau N hN hne]
    ring
  · simp

theorem optimizerMass_objective_ge (N : ℕ) (hN : 1 ≤ N) :
    1584 / 5243 ≤ (input N hN).objective (optimizerMass N hN) :=
  objective_ge_1584_div_5243 hN _ (optimizerMass_feasible N hN)

theorem optimizerMass_pivotGain (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).pivotCap -
        (input N hN).prescribedPayoff (optimizerMass N hN) 0 = 1584 / 5243 := by
  rw [pivotDebt_formula hN _ (optimizerMass_feasible N hN),
    optimizerMass_beforeMass, optimizerMass_atMass, optimizerMass_never]
  norm_num

theorem optimizerMass_playerOnePayoff (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).prescribedPayoff (optimizerMass N hN) 1 = 35117 / 5243 := by
  rw [playerOne_prescribedPayoff_formula, optimizerMass_beforeMass,
    optimizerMass_atMass, optimizerMass_late, optimizerMass_never]
  norm_num

theorem optimizerMass_playerOneNeverEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderNeverEndpoint (optimizerMass N hN) 1 = 7 := by
  rw [playerOne_neverEndpoint_formula hN _ (optimizerMass_feasible N hN),
    optimizerMass_never]
  norm_num

theorem optimizerMass_playerOneNeverGain (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderNeverEndpoint (optimizerMass N hN) 1 -
        (input N hN).prescribedPayoff (optimizerMass N hN) 1 = 1584 / 5243 := by
  rw [optimizerMass_playerOneNeverEndpoint, optimizerMass_playerOnePayoff]
  norm_num

private theorem playerOne_otherNeverProduct (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).otherNeverProduct 1 = 6 / 7 := by
  unfold QuittingPivotRepairLPInput.otherNeverProduct
  change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 1,
    ((opponents N hN j) none).toReal) = _
  rw [show (Finset.univ.erase (0 : Fin 4)).erase 1 = {2, 3} by decide]
  rw [Finset.prod_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
    Finset.prod_singleton]
  rw [opponents_two_never]
  simp [opponents]

theorem optimizerMass_playerOneFirstEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderFirstEndpoint (optimizerMass N hN) 1 = 4901 / 749 := by
  have hnever := optimizerMass_playerOneNeverEndpoint N hN
  unfold QuittingPivotRepairLPInput.responderFirstEndpoint
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint at hnever
  rw [playerOne_otherNeverProduct] at hnever
  change (input N hN).earlyContribution (optimizerMass N hN) 1 +
    6 / 7 * (7 * (19 / 107)) = 7 at hnever
  rw [playerOne_otherNeverProduct]
  simp [QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff, optimizerMass_late, optimizerMass_never,
    optimizerMass_firstAtom]
  norm_num at hnever ⊢
  linarith

theorem optimizerMass_playerOneLimitEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderLimitEndpoint (optimizerMass N hN) 1 = 7 := by
  have hnever := optimizerMass_playerOneNeverEndpoint N hN
  unfold QuittingPivotRepairLPInput.responderLimitEndpoint
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint at hnever
  rw [playerOne_otherNeverProduct] at hnever
  change (input N hN).earlyContribution (optimizerMass N hN) 1 +
    6 / 7 * (7 * (19 / 107)) = 7 at hnever
  rw [playerOne_otherNeverProduct]
  simp [QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff, optimizerMass_late, optimizerMass_never]
  norm_num at hnever ⊢
  linarith

theorem optimizerMass_playerTwoPayoff (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).prescribedPayoff (optimizerMass N hN) 2 = 35498 / 5243 := by
  unfold QuittingPivotRepairLPInput.prescribedPayoff
  change (∑ time : Fin N, pivotRepairHead (optimizerMass N hN) time *
      (input N hN).purePivotPayoff (some time.1) 2) +
    pivotRepairLate (optimizerMass N hN) * (input N hN).purePivotPayoff (some N) 2 +
    pivotRepairNever (optimizerMass N hN) * (input N hN).purePivotPayoff none 2 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (input N hN).purePivotPayoff (some (N - 1)) 2 +
    19 / 107 * (input N hN).purePivotPayoff (some N) 2 +
      0 * (input N hN).purePivotPayoff none 2 = _
  rw [playerTwoPayoff_at, playerTwoPayoff_after]
  norm_num

theorem optimizerMass_playerThreePayoff (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).prescribedPayoff (optimizerMass N hN) 3 = 31 / 49 := by
  unfold QuittingPivotRepairLPInput.prescribedPayoff
  change (∑ time : Fin N, pivotRepairHead (optimizerMass N hN) time *
      (input N hN).purePivotPayoff (some time.1) 3) +
    pivotRepairLate (optimizerMass N hN) * (input N hN).purePivotPayoff (some N) 3 +
    pivotRepairNever (optimizerMass N hN) * (input N hN).purePivotPayoff none 3 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (input N hN).purePivotPayoff (some (N - 1)) 3 +
    19 / 107 * (input N hN).purePivotPayoff (some N) 3 +
      0 * (input N hN).purePivotPayoff none 3 = _
  rw [playerThreePayoff_at, playerThreePayoff_after]
  norm_num

theorem optimizerMass_playerOneHeadGain_le (N : ℕ) (hN : 1 ≤ N)
    (time : Fin N) :
    (input N hN).pureResponsePayoff (optimizerMass N hN) 1 (some time.1) 1 -
        (input N hN).prescribedPayoff (optimizerMass N hN) 1 ≤ 1584 / 5243 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 1 (some headTime.1) (some time.1) 1) +
    pivotRepairLate (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 1 (some N) (some time.1) 1 +
    pivotRepairNever (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 1 none (some time.1) 1 -
    (input N hN).prescribedPayoff (optimizerMass N hN) 1 ≤ _
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (input N hN).purePivotResponderPayoff 1
        (some (N - 1)) (some (N - 1)) 1 +
      19 / 107 * (input N hN).purePivotResponderPayoff 1
        (some N) (some (N - 1)) 1 + 0 * _ - _ ≤ _
    rw [playerOneResponsePayoff_at_at, playerOneResponsePayoff_late_at,
      optimizerMass_playerOnePayoff]
    norm_num
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (input N hN).purePivotResponderPayoff 1
        (some (N - 1)) (some time.1) 1 +
      19 / 107 * (input N hN).purePivotResponderPayoff 1
        (some N) (some time.1) 1 + 0 * _ - _ ≤ _
    rw [playerOneResponsePayoff_before N hN (N - 1) time.1 htime (by omega),
      playerOneResponsePayoff_before N hN N time.1 htime (by omega),
      optimizerMass_playerOnePayoff]
    norm_num

theorem optimizerMass_playerTwoHeadGain_le (N : ℕ) (hN : 1 ≤ N)
    (time : Fin N) :
    (input N hN).pureResponsePayoff (optimizerMass N hN) 2 (some time.1) 2 -
        (input N hN).prescribedPayoff (optimizerMass N hN) 2 ≤ 1584 / 5243 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 2 (some headTime.1) (some time.1) 2) +
    pivotRepairLate (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 2 (some N) (some time.1) 2 +
    pivotRepairNever (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 2 none (some time.1) 2 -
    (input N hN).prescribedPayoff (optimizerMass N hN) 2 ≤ _
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (input N hN).purePivotResponderPayoff 2
        (some (N - 1)) (some (N - 1)) 2 +
      19 / 107 * (input N hN).purePivotResponderPayoff 2
        (some N) (some (N - 1)) 2 + 0 * _ - _ ≤ _
    rw [playerTwoResponsePayoff_at_at, playerTwoResponsePayoff_late_at,
      optimizerMass_playerTwoPayoff]
    norm_num
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (input N hN).purePivotResponderPayoff 2
        (some (N - 1)) (some time.1) 2 +
      19 / 107 * (input N hN).purePivotResponderPayoff 2
        (some N) (some time.1) 2 + 0 * _ - _ ≤ _
    rw [playerTwoResponsePayoff_before N hN (N - 1) time.1 htime (by omega),
      playerTwoResponsePayoff_before N hN N time.1 htime (by omega),
      optimizerMass_playerTwoPayoff]
    norm_num

theorem optimizerMass_playerThreeHeadGain_le (N : ℕ) (hN : 1 ≤ N)
    (time : Fin N) :
    (input N hN).pureResponsePayoff (optimizerMass N hN) 3 (some time.1) 3 -
        (input N hN).prescribedPayoff (optimizerMass N hN) 3 ≤ 1584 / 5243 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 3 (some headTime.1) (some time.1) 3) +
    pivotRepairLate (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 3 (some N) (some time.1) 3 +
    pivotRepairNever (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 3 none (some time.1) 3 -
    (input N hN).prescribedPayoff (optimizerMass N hN) 3 ≤ _
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (input N hN).purePivotResponderPayoff 3
        (some (N - 1)) (some (N - 1)) 3 +
      19 / 107 * (input N hN).purePivotResponderPayoff 3
        (some N) (some (N - 1)) 3 + 0 * _ - _ ≤ _
    rw [playerThreeResponsePayoff_at_at, playerThreeResponsePayoff_late_at,
      optimizerMass_playerThreePayoff]
    norm_num
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (input N hN).purePivotResponderPayoff 3
        (some (N - 1)) (some time.1) 3 +
      19 / 107 * (input N hN).purePivotResponderPayoff 3
        (some N) (some time.1) 3 + 0 * _ - _ ≤ _
    rw [playerThreeResponsePayoff_before N hN (N - 1) time.1 htime (by omega),
      playerThreeResponsePayoff_before N hN N time.1 htime (by omega),
      optimizerMass_playerThreePayoff]
    norm_num

private theorem playerTwo_otherNeverProduct (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).otherNeverProduct 2 = 3 / 7 := by
  unfold QuittingPivotRepairLPInput.otherNeverProduct
  change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 2,
    ((opponents N hN j) none).toReal) = _
  rw [show (Finset.univ.erase (0 : Fin 4)).erase 2 = {1, 3} by decide]
  rw [Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({3} : Finset (Fin 4))),
    Finset.prod_singleton, opponents_one_never]
  simp [opponents]

private theorem playerThree_otherNeverProduct (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).otherNeverProduct 3 = 18 / 49 := by
  unfold QuittingPivotRepairLPInput.otherNeverProduct
  change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 3,
    ((opponents N hN j) none).toReal) = _
  rw [show (Finset.univ.erase (0 : Fin 4)).erase 3 = {1, 2} by decide]
  rw [Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({2} : Finset (Fin 4))),
    Finset.prod_singleton, opponents_one_never, opponents_two_never]
  norm_num

theorem optimizerMass_playerTwoEarlyContribution (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).earlyContribution (optimizerMass N hN) 2 = 692 / 107 := by
  unfold QuittingPivotRepairLPInput.earlyContribution
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 2 (some headTime.1) none 2) +
    (pivotRepairLate (optimizerMass N hN) + pivotRepairNever (optimizerMass N hN)) *
      (input N hN).purePivotResponderPayoff 2 none none 2 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (input N hN).purePivotResponderPayoff 2
      (some (N - 1)) none 2 +
    (19 / 107 + 0) * (input N hN).purePivotResponderPayoff 2 none none 2 = _
  rw [playerTwoNeverResponsePayoff_at, playerTwoNeverResponsePayoff_never]
  norm_num

theorem optimizerMass_playerTwoNeverEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderNeverEndpoint (optimizerMass N hN) 2 = 7 := by
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint
  rw [optimizerMass_playerTwoEarlyContribution, playerTwo_otherNeverProduct]
  norm_num [pivotRepairLate, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem optimizerMass_playerTwoFirstEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderFirstEndpoint (optimizerMass N hN) 2 = 9973 / 1498 := by
  unfold QuittingPivotRepairLPInput.responderFirstEndpoint
  rw [optimizerMass_playerTwoEarlyContribution, playerTwo_otherNeverProduct]
  norm_num [pivotRepairLate, pivotRepairNever, pivotRepairFirstAtom, optimizerMass,
    QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem optimizerMass_playerTwoLimitEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderLimitEndpoint (optimizerMass N hN) 2 = 7 := by
  unfold QuittingPivotRepairLPInput.responderLimitEndpoint
  rw [optimizerMass_playerTwoEarlyContribution, playerTwo_otherNeverProduct]
  norm_num [pivotRepairLate, pivotRepairNever, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem optimizerMass_playerThreeEarlyContribution (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).earlyContribution (optimizerMass N hN) 3 = 31 / 49 := by
  unfold QuittingPivotRepairLPInput.earlyContribution
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 3 (some headTime.1) none 3) +
    (pivotRepairLate (optimizerMass N hN) + pivotRepairNever (optimizerMass N hN)) *
      (input N hN).purePivotResponderPayoff 3 none none 3 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (input N hN).purePivotResponderPayoff 3
      (some (N - 1)) none 3 +
    (19 / 107 + 0) * (input N hN).purePivotResponderPayoff 3 none none 3 = _
  rw [playerThreeNeverResponse_eq_purePivotPayoff,
    playerThreeNeverResponse_eq_purePivotPayoff, playerThreePayoff_at,
    playerThreePayoff_never]
  norm_num

theorem optimizerMass_playerThreeNeverEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderNeverEndpoint (optimizerMass N hN) 3 = 31 / 49 := by
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint
  rw [optimizerMass_playerThreeEarlyContribution, playerThree_otherNeverProduct]
  norm_num [pivotRepairLate, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem optimizerMass_playerThreeFirstEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderFirstEndpoint (optimizerMass N hN) 3 = 3146 / 5243 := by
  unfold QuittingPivotRepairLPInput.responderFirstEndpoint
  rw [optimizerMass_playerThreeEarlyContribution, playerThree_otherNeverProduct]
  norm_num [pivotRepairLate, pivotRepairNever, pivotRepairFirstAtom, optimizerMass,
    QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem optimizerMass_playerThreeLimitEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).responderLimitEndpoint (optimizerMass N hN) 3 = 31 / 49 := by
  unfold QuittingPivotRepairLPInput.responderLimitEndpoint
  rw [optimizerMass_playerThreeEarlyContribution, playerThree_otherNeverProduct]
  norm_num [pivotRepairLate, pivotRepairNever, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

private theorem optimizerMass_responderEndpointGain_le (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ (input N hN).pivot) (endpoint : Fin 3) :
    (match endpoint with
      | 0 => (input N hN).responderNeverEndpoint (optimizerMass N hN) responder
      | 1 => (input N hN).responderFirstEndpoint (optimizerMass N hN) responder
      | 2 => (input N hN).responderLimitEndpoint (optimizerMass N hN) responder) -
        (input N hN).prescribedPayoff (optimizerMass N hN) responder ≤ 1584 / 5243 := by
  have hresponder : responder = 1 ∨ responder = 2 ∨ responder = 3 := by
    fin_cases responder
    · exact (hne rfl).elim
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hendpoint : endpoint = 0 ∨ endpoint = 1 ∨ endpoint = 2 := by
    fin_cases endpoint <;> simp
  rcases hresponder with rfl | rfl | rfl
  · rcases hendpoint with rfl | rfl | rfl
    · rw [optimizerMass_playerOneNeverEndpoint, optimizerMass_playerOnePayoff]
      norm_num
    · rw [optimizerMass_playerOneFirstEndpoint, optimizerMass_playerOnePayoff]
      norm_num
    · rw [optimizerMass_playerOneLimitEndpoint, optimizerMass_playerOnePayoff]
      norm_num
  · rcases hendpoint with rfl | rfl | rfl
    · rw [optimizerMass_playerTwoNeverEndpoint, optimizerMass_playerTwoPayoff]
      norm_num
    · rw [optimizerMass_playerTwoFirstEndpoint, optimizerMass_playerTwoPayoff]
      norm_num
    · rw [optimizerMass_playerTwoLimitEndpoint, optimizerMass_playerTwoPayoff]
      norm_num
  · rcases hendpoint with rfl | rfl | rfl
    · rw [optimizerMass_playerThreeNeverEndpoint, optimizerMass_playerThreePayoff]
      norm_num
    · rw [optimizerMass_playerThreeFirstEndpoint, optimizerMass_playerThreePayoff]
      norm_num
    · rw [optimizerMass_playerThreeLimitEndpoint, optimizerMass_playerThreePayoff]
      norm_num

theorem optimizerMass_objective_le (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).objective (optimizerMass N hN) ≤ 1584 / 5243 := by
  unfold QuittingPivotRepairLPInput.objective
  apply Finset.sup'_le
  intro index _
  rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
  · norm_num [QuittingPivotRepairLPInput.constraintGain]
  · change (input N hN).pivotCap -
        (input N hN).prescribedPayoff (optimizerMass N hN) 0 ≤ _
    rw [optimizerMass_pivotGain]
  · change (input N hN).pureResponsePayoff (optimizerMass N hN) responder
        (some time.1) responder -
      (input N hN).prescribedPayoff (optimizerMass N hN) responder ≤ _
    obtain ⟨responder, hne⟩ := responder
    fin_cases responder
    · exact (hne rfl).elim
    · exact optimizerMass_playerOneHeadGain_le N hN time
    · exact optimizerMass_playerTwoHeadGain_le N hN time
    · exact optimizerMass_playerThreeHeadGain_le N hN time
  · exact optimizerMass_responderEndpointGain_le N hN responder
      responder.property endpoint

theorem optimizerMass_objective_eq (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).objective (optimizerMass N hN) = 1584 / 5243 := by
  exact le_antisymm (optimizerMass_objective_le N hN) (optimizerMass_objective_ge N hN)

theorem optimizerMass_pivotPayoff (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).prescribedPayoff (optimizerMass N hN) 0 = 23561 / 5243 := by
  have hgain := optimizerMass_pivotGain N hN
  rw [pivotCap] at hgain
  linarith

private theorem optimizerMass_playerTwoHeadPayoff_le (N : ℕ) (hN : 1 ≤ N)
    (time : Fin N) :
    (input N hN).pureResponsePayoff (optimizerMass N hN) 2 (some time.1) 2 ≤ 7 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 2 (some headTime.1) (some time.1) 2) +
    pivotRepairLate (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 2 (some N) (some time.1) 2 +
    pivotRepairNever (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 2 none (some time.1) 2 ≤ 7
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (input N hN).purePivotResponderPayoff 2
        (some (N - 1)) (some (N - 1)) 2 +
      19 / 107 * (input N hN).purePivotResponderPayoff 2
        (some N) (some (N - 1)) 2 + 0 * _ ≤ 7
    rw [playerTwoResponsePayoff_at_at, playerTwoResponsePayoff_late_at]
    norm_num
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (input N hN).purePivotResponderPayoff 2
        (some (N - 1)) (some time.1) 2 +
      19 / 107 * (input N hN).purePivotResponderPayoff 2
        (some N) (some time.1) 2 + 0 * _ ≤ 7
    rw [playerTwoResponsePayoff_before N hN (N - 1) time.1 htime (by omega),
      playerTwoResponsePayoff_before N hN N time.1 htime (by omega)]
    norm_num

private theorem optimizerMass_playerThreeHeadPayoff_le (N : ℕ) (hN : 1 ≤ N)
    (time : Fin N) :
    (input N hN).pureResponsePayoff (optimizerMass N hN) 3 (some time.1) 3 ≤
      31 / 49 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (input N hN).purePivotResponderPayoff 3 (some headTime.1) (some time.1) 3) +
    pivotRepairLate (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 3 (some N) (some time.1) 3 +
    pivotRepairNever (optimizerMass N hN) *
      (input N hN).purePivotResponderPayoff 3 none (some time.1) 3 ≤ 31 / 49
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (input N hN).purePivotResponderPayoff 3
        (some (N - 1)) (some (N - 1)) 3 +
      19 / 107 * (input N hN).purePivotResponderPayoff 3
        (some N) (some (N - 1)) 3 + 0 * _ ≤ 31 / 49
    rw [playerThreeResponsePayoff_at_at, playerThreeResponsePayoff_late_at]
    norm_num
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (input N hN).purePivotResponderPayoff 3
        (some (N - 1)) (some time.1) 3 +
      19 / 107 * (input N hN).purePivotResponderPayoff 3
        (some N) (some time.1) 3 + 0 * _ ≤ 31 / 49
    rw [playerThreeResponsePayoff_before N hN (N - 1) time.1 htime (by omega),
      playerThreeResponsePayoff_before N hN N time.1 htime (by omega)]
    norm_num

def optimizerGeometricLaws (N : ℕ) (hN : 1 ≤ N) : Fin 4 → PMF (Option ℕ) :=
  (input N hN).geometricLaws (optimizerMass N hN) (optimizerMass_feasible N hN)
    (1 / 2) (by norm_num) (by norm_num)

def optimizerGeometricProfile (N : ℕ) (hN : 1 ≤ N) :
    (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward (optimizerGeometricLaws N hN)

theorem optimizerGeometric_payoff (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingTerminalPayoff reward (optimizerGeometricProfile N hN) who =
      ![23561 / 5243, 35117 / 5243, 35498 / 5243, 31 / 49] who := by
  rw [optimizerGeometricProfile, optimizerGeometricLaws,
    (input N hN).geometric_payoff_eq_prescribedPayoff]
  fin_cases who
  · exact optimizerMass_pivotPayoff N hN
  · exact optimizerMass_playerOnePayoff N hN
  · exact optimizerMass_playerTwoPayoff N hN
  · exact optimizerMass_playerThreePayoff N hN

private theorem optimizerMass_half_match (N : ℕ) (hN : 1 ≤ N) :
    pivotRepairLate (optimizerMass N hN) * (1 / 2) =
      pivotRepairFirstAtom (optimizerMass N hN) := by
  norm_num [input, pivotRepairLate, pivotRepairFirstAtom, optimizerMass]

private theorem optimizerGeometric_neverEndpoint_le_cap (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ (input N hN).pivot) :
    (input N hN).responderNeverEndpoint (optimizerMass N hN) responder ≤
      quittingContinuationBestResponseValue reward (optimizerGeometricProfile N hN) responder := by
  have h := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
    (optimizerGeometricProfile N hN) responder
    (quittingPureTimeBehaviorStrategy reward responder none)
  unfold optimizerGeometricProfile at h
  rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at h
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (optimizerGeometricLaws N hN) responder (PMF.pure none))) responder ≤
    quittingContinuationBestResponseValue reward (optimizerGeometricProfile N hN) responder at h
  rw [optimizerGeometricLaws,
    (input N hN).geometric_neverResponse_eq (optimizerMass N hN)
      (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num) responder hne] at h
  exact h

theorem optimizerGeometric_cap (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingContinuationBestResponseValue reward (optimizerGeometricProfile N hN) who =
      ![235 / 49, 7, 7, 31 / 49] who := by
  have hwho : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hwho with rfl | rfl | rfl | rfl
  · have hlaws : optimizerGeometricLaws N hN = Function.update
        (input N hN).opponents (input N hN).pivot
          (optimizerGeometricLaws N hN (input N hN).pivot) := by
      unfold optimizerGeometricLaws QuittingPivotRepairLPInput.geometricLaws
      simp
    rw [optimizerGeometricProfile, hlaws]
    change quittingContinuationBestResponseValue reward
      (quittingStoppingLawProfile reward (Function.update (input N hN).opponents
        (input N hN).pivot (optimizerGeometricLaws N hN (input N hN).pivot)))
          (input N hN).pivot = 235 / 49
    rw [← (input N hN).pivotCap_eq_continuationBestResponseValue]
    exact pivotCap N hN
  · apply le_antisymm
    · have hne : (1 : Fin 4) ≠ (input N hN).pivot := by
        change (1 : Fin 4) ≠ 0
        decide
      apply (input N hN).geometric_cap_le_of_endpoints
        (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
        (by norm_num) (by norm_num) (optimizerMass_half_match N hN) 1 hne 7
      · intro time
        have h := optimizerMass_playerOneHeadGain_le N hN time
        rw [optimizerMass_playerOnePayoff] at h
        norm_num at h ⊢
        linarith
      · rw [optimizerMass_playerOneNeverEndpoint]
      · rw [optimizerMass_playerOneFirstEndpoint]
        norm_num
      · rw [optimizerMass_playerOneLimitEndpoint]
    · have hne : (1 : Fin 4) ≠ (input N hN).pivot := by
        change (1 : Fin 4) ≠ 0
        decide
      have h := optimizerGeometric_neverEndpoint_le_cap N hN 1 hne
      rw [optimizerMass_playerOneNeverEndpoint] at h
      exact h
  · apply le_antisymm
    · have hne : (2 : Fin 4) ≠ (input N hN).pivot := by
        change (2 : Fin 4) ≠ 0
        decide
      apply (input N hN).geometric_cap_le_of_endpoints
        (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
        (by norm_num) (by norm_num) (optimizerMass_half_match N hN) 2 hne 7
      · exact optimizerMass_playerTwoHeadPayoff_le N hN
      · rw [optimizerMass_playerTwoNeverEndpoint]
      · rw [optimizerMass_playerTwoFirstEndpoint]
        norm_num
      · rw [optimizerMass_playerTwoLimitEndpoint]
    · have hne : (2 : Fin 4) ≠ (input N hN).pivot := by
        change (2 : Fin 4) ≠ 0
        decide
      have h := optimizerGeometric_neverEndpoint_le_cap N hN 2 hne
      rw [optimizerMass_playerTwoNeverEndpoint] at h
      exact h
  · apply le_antisymm
    · have hne : (3 : Fin 4) ≠ (input N hN).pivot := by
        change (3 : Fin 4) ≠ 0
        decide
      apply (input N hN).geometric_cap_le_of_endpoints
        (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
        (by norm_num) (by norm_num) (optimizerMass_half_match N hN) 3 hne (31 / 49)
      · exact optimizerMass_playerThreeHeadPayoff_le N hN
      · rw [optimizerMass_playerThreeNeverEndpoint]
      · rw [optimizerMass_playerThreeFirstEndpoint]
        norm_num
      · rw [optimizerMass_playerThreeLimitEndpoint]
    · have hne : (3 : Fin 4) ≠ (input N hN).pivot := by
        change (3 : Fin 4) ≠ 0
        decide
      have h := optimizerGeometric_neverEndpoint_le_cap N hN 3 hne
      rw [optimizerMass_playerThreeNeverEndpoint] at h
      exact h

theorem optimizerGeometric_debt (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingTerminalDeviationDebt reward (optimizerGeometricProfile N hN) who =
      ![1584 / 5243, 1584 / 5243, 1203 / 5243, 0] who := by
  unfold quittingTerminalDeviationDebt
  rw [optimizerGeometric_cap, optimizerGeometric_payoff]
  fin_cases who <;> norm_num

theorem optimizerMass_geometric_exploitability_eq (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward
          ((input N hN).geometricLaws (optimizerMass N hN)
            (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num))) =
      1584 / 5243 := by
  rw [(input N hN).geometric_exploitability_eq_objective
    (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
    (by norm_num) (by norm_num) (optimizerMass_half_match N hN)]
  exact optimizerMass_objective_eq N hN

end GameTheory.PivotRepairRationalOptimizer
