import UniformEquilibrium.Diagnostics.Quitting.PivotRepairRationalLowerBound
import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition

/-! # Actual response coefficients for the rational pivot-repair example -/

noncomputable section

namespace GameTheory.PivotRepairRationalResponseCoefficients

open _root_.Math.Probability
open PivotRepairRationalFixture
open PivotRepairRationalLowerBound

/-- Deterministic stopping laws evaluate at their literal first outcome. -/
theorem pureTimesPayoff (times : Fin 4 → Option ℕ) (observer : Fin 4) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun player ↦ PMF.pure (times player))) observer =
      quittingTerminalOutcomeReward reward (quittingFirstStoppingOutcome times) observer := by
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  unfold quittingIndependentTerminalOutcomeLaw
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_map, expect_pure]

/-- A common-date deterministic coalition realizes its literal reward. -/
theorem pureCoalitionPayoff_eq_reward (coalition : Finset (Fin 4))
    (hne : coalition.Nonempty) (time : ℕ) (observer : Fin 4) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (pureCoalitionLaws coalition time)) observer =
      reward ⟨coalition, hne⟩ observer := by
  unfold pureCoalitionLaws
  rw [pureTimesPayoff, quittingFirstStoppingOutcome_one_date coalition hne time]
  rfl

private theorem allNeverPayoff (observer : Fin 4) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward neverLaws) observer = 0 := by
  rw [show neverLaws = fun _ : Fin 4 ↦ PMF.pure none by rfl, pureTimesPayoff]
  simp [quittingTerminalOutcomeReward]

private theorem pivotNeverPayoff_weighted (N : ℕ) (hN : 1 ≤ N)
    (observer : Fin 4) :
    (input N hN).purePivotPayoff none observer =
      (6 / 7) * ((3 / 7) * 0 + (4 / 7) * reward ⟨{1}, by simp⟩ observer) +
        (1 / 7) * ((3 / 7) * reward ⟨{2}, by simp⟩ observer +
          (4 / 7) * reward ⟨{1, 2}, by simp⟩ observer) := by
  rw [observerPayoff_conditioned N hN none observer]
  have hbase : Function.update neverLaws 0 (PMF.pure none) = neverLaws := by
    funext player
    fin_cases player <;> rfl
  rw [hbase, allNeverPayoff]
  have hone : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update neverLaws 1 (PMF.pure (some (N - 1))))) observer =
      reward ⟨{1}, by simp⟩ observer := by
    rw [show Function.update neverLaws 1 (PMF.pure (some (N - 1))) =
      pureCoalitionLaws {1} (N - 1) by funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {1} (by simp) (N - 1) observer
  have htwo : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update neverLaws 2 (PMF.pure (some (N - 1))))) observer =
      reward ⟨{2}, by simp⟩ observer := by
    rw [show Function.update neverLaws 2 (PMF.pure (some (N - 1))) =
      pureCoalitionLaws {2} (N - 1) by funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {2} (by simp) (N - 1) observer
  have hboth : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 1 (PMF.pure (some (N - 1)))) 2
        (PMF.pure (some (N - 1))))) observer =
      reward ⟨{1, 2}, by simp⟩ observer := by
    rw [show Function.update
        (Function.update neverLaws 1 (PMF.pure (some (N - 1)))) 2
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {1, 2} (N - 1) by
      funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {1, 2} (by simp) (N - 1) observer
  rw [hone, htwo, hboth]

private theorem pivotAtPayoff_weighted (N : ℕ) (hN : 1 ≤ N)
    (observer : Fin 4) :
    (input N hN).purePivotPayoff (some (N - 1)) observer =
      (6 / 7) * ((3 / 7) * reward ⟨{0}, by simp⟩ observer +
        (4 / 7) * reward ⟨{0, 1}, by simp⟩ observer) +
      (1 / 7) * ((3 / 7) * reward ⟨{0, 2}, by simp⟩ observer +
        (4 / 7) * reward ⟨{0, 1, 2}, by simp⟩ observer) := by
  rw [observerPayoff_conditioned N hN (some (N - 1)) observer]
  have hzero : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update neverLaws 0 (PMF.pure (some (N - 1))))) observer =
      reward ⟨{0}, by simp⟩ observer := by
    rw [show Function.update neverLaws 0 (PMF.pure (some (N - 1))) =
      pureCoalitionLaws {0} (N - 1) by funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {0} (by simp) (N - 1) observer
  have hone : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
        (PMF.pure (some (N - 1))))) observer = reward ⟨{0, 1}, by simp⟩ observer := by
    rw [show Function.update
        (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {0, 1} (N - 1) by
      funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {0, 1} (by simp) (N - 1) observer
  have htwo : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 2
        (PMF.pure (some (N - 1))))) observer = reward ⟨{0, 2}, by simp⟩ observer := by
    rw [show Function.update
        (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 2
          (PMF.pure (some (N - 1))) = pureCoalitionLaws {0, 2} (N - 1) by
      funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {0, 2} (by simp) (N - 1) observer
  have hboth : quittingTerminalPayoff reward (quittingStoppingLawProfile reward
      (Function.update (Function.update
          (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))))) observer =
      reward ⟨{0, 1, 2}, by simp⟩ observer := by
    rw [show Function.update
        (Function.update
          (Function.update neverLaws 0 (PMF.pure (some (N - 1)))) 1
            (PMF.pure (some (N - 1)))) 2 (PMF.pure (some (N - 1))) =
          pureCoalitionLaws {0, 1, 2} (N - 1) by
      funext player; fin_cases player <;> rfl]
    exact pureCoalitionPayoff_eq_reward {0, 1, 2} (by simp) (N - 1) observer
  rw [hzero, hone, htwo, hboth]

theorem playerTwoPayoff_never (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff none 2 = 200 / 49 := by
  rw [pivotNeverPayoff_weighted]
  norm_num [reward, Fin.ext_iff]

theorem playerTwoPayoff_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff (some (N - 1)) 2 = 333 / 49 := by
  rw [pivotAtPayoff_weighted]
  norm_num [reward, Fin.ext_iff]

theorem playerTwoPayoff_after (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff (some N) 2 = 326 / 49 := by
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update (opponents N hN) 0 (PMF.pure (some N)))) 2 = _
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward (opponents N hN) 0 2 N]
  · change (input N hN).purePivotPayoff none 2 + _ = _
    rw [playerTwoPayoff_never]
    have hproduct : (∏ j ∈ Finset.univ.erase (0 : Fin 4),
        ((opponents N hN j) none).toReal) = 18 / 49 := by
      rw [show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
      rw [Finset.prod_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
        Finset.prod_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))),
        Finset.prod_singleton, opponents_one_never, opponents_two_never]
      simp [opponents]
      norm_num
    rw [hproduct]
    norm_num [quittingSingletonTerminal, reward, Fin.ext_iff]
  · exact (input N hN).opponents_finite
  · omega

theorem playerThreePayoff_never (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff none 3 = 31 / 49 := by
  rw [pivotNeverPayoff_weighted]
  norm_num [reward, Fin.ext_iff]

theorem playerThreePayoff_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff (some (N - 1)) 3 = 31 / 49 := by
  rw [pivotAtPayoff_weighted]
  norm_num [reward, Fin.ext_iff]

theorem playerThreePayoff_after (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotPayoff (some N) 3 = 31 / 49 := by
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update (opponents N hN) 0 (PMF.pure (some N)))) 3 = _
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward (opponents N hN) 0 3 N]
  · change (input N hN).purePivotPayoff none 3 + _ = _
    rw [playerThreePayoff_never]
    simp [quittingSingletonTerminal, reward, Fin.ext_iff]
  · exact (input N hN).opponents_finite
  · omega

private def playerOneResponseTimes (N : ℕ) (pivotChoice response : Option ℕ)
    (twoQuits : Bool) : Fin 4 → Option ℕ
  | 0 => pivotChoice
  | 1 => response
  | 2 => if twoQuits then some (N - 1) else none
  | _ => none

private theorem playerOneResponse_conditioned (N : ℕ) (hN : 1 ≤ N)
    (pivotChoice response : Option ℕ) :
    (input N hN).purePivotResponderPayoff 1 pivotChoice response 1 =
      (6 / 7) * quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (fun player ↦ PMF.pure (playerOneResponseTimes N pivotChoice response false player))) 1 +
      (1 / 7) * quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (fun player ↦ PMF.pure (playerOneResponseTimes N pivotChoice response true player))) 1 := by
  unfold QuittingPivotRepairLPInput.purePivotResponderPayoff
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update (Function.update (opponents N hN) 0 (PMF.pure pivotChoice)) 1
      (PMF.pure response))) 1 = _
  rw [show Function.update
      (Function.update (opponents N hN) 0 (PMF.pure pivotChoice)) 1
        (PMF.pure response) = Function.update
      (Function.update
        (Function.update neverLaws 0 (PMF.pure pivotChoice)) 1 (PMF.pure response)) 2
      (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)) by
    funext player
    fin_cases player <;> rfl,
    quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_quitOrNever]
  norm_num
  congr 1
  · congr 2
    funext player
    fin_cases player <;> rfl
  · congr 2
    funext player
    fin_cases player <;> rfl

private def playerTwoResponseTimes (N : ℕ) (pivotChoice response : Option ℕ)
    (oneQuits : Bool) : Fin 4 → Option ℕ
  | 0 => pivotChoice
  | 1 => if oneQuits then some (N - 1) else none
  | 2 => response
  | _ => none

private theorem playerTwoResponse_conditioned (N : ℕ) (hN : 1 ≤ N)
    (pivotChoice response : Option ℕ) :
    (input N hN).purePivotResponderPayoff 2 pivotChoice response 2 =
      (3 / 7) * quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (fun player ↦ PMF.pure (playerTwoResponseTimes N pivotChoice response false player))) 2 +
      (4 / 7) * quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (fun player ↦ PMF.pure (playerTwoResponseTimes N pivotChoice response true player))) 2 := by
  unfold QuittingPivotRepairLPInput.purePivotResponderPayoff
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update (Function.update (opponents N hN) 0 (PMF.pure pivotChoice)) 2
      (PMF.pure response))) 2 = _
  rw [show Function.update
      (Function.update (opponents N hN) 0 (PMF.pure pivotChoice)) 2
        (PMF.pure response) = Function.update
      (Function.update
        (Function.update neverLaws 0 (PMF.pure pivotChoice)) 2 (PMF.pure response)) 1
      (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)) by
    funext player
    fin_cases player <;> rfl,
    quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_quitOrNever]
  norm_num
  congr 1
  · congr 2
    funext player
    fin_cases player <;> rfl
  · congr 2
    funext player
    fin_cases player <;> rfl

theorem playerOneResponsePayoff_before (N : ℕ) (hN : 1 ≤ N)
    (pivotTime response : ℕ) (hresponse : response < N - 1)
    (hpivot : response < pivotTime) :
    (input N hN).purePivotResponderPayoff 1 (some pivotTime) (some response) 1 = 0 := by
  rw [playerOneResponse_conditioned]
  have houtcome (twoQuits : Bool) : quittingFirstStoppingOutcome
      (playerOneResponseTimes N (some pivotTime) (some response) twoQuits) =
      some ⟨{1}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {1} (by simp) response
    · intro player hplayer
      fin_cases player <;> simp_all [playerOneResponseTimes]
    · intro player hplayer
      fin_cases player <;> fin_cases twoQuits <;>
        simp_all [playerOneResponseTimes, quittingStoppingTimeValue]
  rw [pureTimesPayoff, houtcome false, pureTimesPayoff, houtcome true]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem playerOneResponsePayoff_at_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 1 (some (N - 1)) (some (N - 1)) 1 =
      54 / 7 := by
  rw [playerOneResponse_conditioned]
  rw [show (fun player ↦ PMF.pure
        (playerOneResponseTimes N (some (N - 1)) (some (N - 1)) false player)) =
      pureCoalitionLaws {0, 1} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    show (fun player ↦ PMF.pure
        (playerOneResponseTimes N (some (N - 1)) (some (N - 1)) true player)) =
      pureCoalitionLaws {0, 1, 2} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    pureCoalitionPayoff_eq_reward {0, 1} (by simp) (N - 1) 1,
    pureCoalitionPayoff_eq_reward {0, 1, 2} (by simp) (N - 1) 1]
  norm_num [reward, Fin.ext_iff]

theorem playerOneResponsePayoff_late_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 1 (some N) (some (N - 1)) 1 = 5 / 7 := by
  rw [playerOneResponse_conditioned]
  have hfalse : quittingFirstStoppingOutcome
      (playerOneResponseTimes N (some N) (some (N - 1)) false) =
      some ⟨{1}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {1} (by simp) (N - 1)
    · intro player hplayer
      fin_cases player <;> simp_all [playerOneResponseTimes]
    · intro player hplayer
      fin_cases player <;> simp_all [playerOneResponseTimes, quittingStoppingTimeValue]
      exact hN
  have htrue : quittingFirstStoppingOutcome
      (playerOneResponseTimes N (some N) (some (N - 1)) true) =
      some ⟨{1, 2}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {1, 2}
      (by simp) (N - 1)
    · intro player hplayer
      fin_cases player <;> simp_all [playerOneResponseTimes]
    · intro player hplayer
      fin_cases player <;> simp_all [playerOneResponseTimes, quittingStoppingTimeValue]
      exact hN
  rw [pureTimesPayoff, hfalse, pureTimesPayoff, htrue]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem playerTwoResponsePayoff_before (N : ℕ) (hN : 1 ≤ N)
    (pivotTime response : ℕ) (hresponse : response < N - 1)
    (hpivot : response < pivotTime) :
    (input N hN).purePivotResponderPayoff 2 (some pivotTime) (some response) 2 = 0 := by
  rw [playerTwoResponse_conditioned]
  have houtcome (oneQuits : Bool) : quittingFirstStoppingOutcome
      (playerTwoResponseTimes N (some pivotTime) (some response) oneQuits) =
      some ⟨{2}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {2} (by simp) response
    · intro player hplayer
      fin_cases player <;> simp_all [playerTwoResponseTimes]
    · intro player hplayer
      fin_cases player <;> fin_cases oneQuits <;>
        simp_all [playerTwoResponseTimes, quittingStoppingTimeValue]
  rw [pureTimesPayoff, houtcome false, pureTimesPayoff, houtcome true]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem playerTwoResponsePayoff_at_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 2 (some (N - 1)) (some (N - 1)) 2 =
      39 / 7 := by
  rw [playerTwoResponse_conditioned]
  rw [show (fun player ↦ PMF.pure
        (playerTwoResponseTimes N (some (N - 1)) (some (N - 1)) false player)) =
      pureCoalitionLaws {0, 2} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    show (fun player ↦ PMF.pure
        (playerTwoResponseTimes N (some (N - 1)) (some (N - 1)) true player)) =
      pureCoalitionLaws {0, 1, 2} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    pureCoalitionPayoff_eq_reward {0, 2} (by simp) (N - 1) 2,
    pureCoalitionPayoff_eq_reward {0, 1, 2} (by simp) (N - 1) 2]
  norm_num [reward, Fin.ext_iff]

theorem playerTwoResponsePayoff_late_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 2 (some N) (some (N - 1)) 2 = 32 / 7 := by
  rw [playerTwoResponse_conditioned]
  have hfalse : quittingFirstStoppingOutcome
      (playerTwoResponseTimes N (some N) (some (N - 1)) false) =
      some ⟨{2}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {2} (by simp) (N - 1)
    · intro player hplayer
      fin_cases player <;> simp_all [playerTwoResponseTimes]
    · intro player hplayer
      fin_cases player <;> simp_all [playerTwoResponseTimes, quittingStoppingTimeValue]
      exact hN
  have htrue : quittingFirstStoppingOutcome
      (playerTwoResponseTimes N (some N) (some (N - 1)) true) =
      some ⟨{1, 2}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {1, 2}
      (by simp) (N - 1)
    · intro player hplayer
      fin_cases player <;> simp_all [playerTwoResponseTimes]
    · intro player hplayer
      fin_cases player <;> simp_all [playerTwoResponseTimes, quittingStoppingTimeValue]
      exact hN
  rw [pureTimesPayoff, hfalse, pureTimesPayoff, htrue]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem playerTwoNeverResponsePayoff_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 2 (some (N - 1)) none 2 = 7 := by
  rw [playerTwoResponse_conditioned]
  rw [show (fun player ↦ PMF.pure
        (playerTwoResponseTimes N (some (N - 1)) none false player)) =
      pureCoalitionLaws {0} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    show (fun player ↦ PMF.pure
        (playerTwoResponseTimes N (some (N - 1)) none true player)) =
      pureCoalitionLaws {0, 1} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    pureCoalitionPayoff_eq_reward {0} (by simp) (N - 1) 2,
    pureCoalitionPayoff_eq_reward {0, 1} (by simp) (N - 1) 2]
  norm_num [reward, Fin.ext_iff]

theorem playerTwoNeverResponsePayoff_never (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 2 none none 2 = 4 := by
  rw [playerTwoResponse_conditioned]
  have hnone : (fun player ↦ PMF.pure
      (playerTwoResponseTimes N none none false player)) = neverLaws := by
    funext player
    fin_cases player <;> rfl
  rw [hnone, allNeverPayoff]
  rw [show (fun player ↦ PMF.pure
        (playerTwoResponseTimes N none none true player)) =
      pureCoalitionLaws {1} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    pureCoalitionPayoff_eq_reward {1} (by simp) (N - 1) 2]
  norm_num [reward, Fin.ext_iff]

private def playerThreeResponseTimes (N : ℕ) (pivotChoice response : Option ℕ)
    (oneQuits twoQuits : Bool) : Fin 4 → Option ℕ
  | 0 => pivotChoice
  | 1 => if oneQuits then some (N - 1) else none
  | 2 => if twoQuits then some (N - 1) else none
  | _ => response

private theorem playerThreeResponse_conditioned (N : ℕ) (hN : 1 ≤ N)
    (pivotChoice response : Option ℕ) :
    (input N hN).purePivotResponderPayoff 3 pivotChoice response 3 =
      (6 / 7) * ((3 / 7) * quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (fun player ↦ PMF.pure
            (playerThreeResponseTimes N pivotChoice response false false player))) 3 +
        (4 / 7) * quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (fun player ↦ PMF.pure
            (playerThreeResponseTimes N pivotChoice response true false player))) 3) +
      (1 / 7) * ((3 / 7) * quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (fun player ↦ PMF.pure
            (playerThreeResponseTimes N pivotChoice response false true player))) 3 +
        (4 / 7) * quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (fun player ↦ PMF.pure
            (playerThreeResponseTimes N pivotChoice response true true player))) 3) := by
  unfold QuittingPivotRepairLPInput.purePivotResponderPayoff
  change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
    (Function.update (Function.update (opponents N hN) 0 (PMF.pure pivotChoice)) 3
      (PMF.pure response))) 3 = _
  rw [show Function.update
      (Function.update (opponents N hN) 0 (PMF.pure pivotChoice)) 3
        (PMF.pure response) = Function.update
      (Function.update
        (Function.update
          (Function.update neverLaws 0 (PMF.pure pivotChoice)) 3 (PMF.pure response)) 1
          (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
        (quitOrNever (N - 1) (1 / 7) (by norm_num) (by norm_num)) by
    funext player
    fin_cases player <;> rfl,
    quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
    expect_quitOrNever]
  congr 1
  · rw [show Function.update
        (Function.update
          (Function.update
            (Function.update neverLaws 0 (PMF.pure pivotChoice)) 3
              (PMF.pure response)) 1
            (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
          (PMF.pure none) = Function.update
        (Function.update
          (Function.update
            (Function.update neverLaws 0 (PMF.pure pivotChoice)) 3
              (PMF.pure response)) 2 (PMF.pure none)) 1
        (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)) by
      exact Function.update_comm (by decide : (1 : Fin 4) ≠ 2) _ _ _]
    rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
      expect_quitOrNever]
    norm_num
    congr 1 <;> congr 2 <;> funext player <;> fin_cases player <;> rfl
  · rw [show Function.update
        (Function.update
          (Function.update
            (Function.update neverLaws 0 (PMF.pure pivotChoice)) 3
              (PMF.pure response)) 1
            (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num))) 2
          (PMF.pure (some (N - 1))) = Function.update
        (Function.update
          (Function.update
            (Function.update neverLaws 0 (PMF.pure pivotChoice)) 3
              (PMF.pure response)) 2 (PMF.pure (some (N - 1)))) 1
        (quitOrNever (N - 1) (4 / 7) (by norm_num) (by norm_num)) by
      exact Function.update_comm (by decide : (1 : Fin 4) ≠ 2) _ _ _]
    rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
      expect_quitOrNever]
    norm_num
    congr 1 <;> congr 2 <;> funext player <;> fin_cases player <;> rfl

private def playerThreeAtCoalition (pivotAt oneQuits twoQuits : Bool) : Finset (Fin 4) :=
  {3} ∪ (if pivotAt then {0} else ∅) ∪ (if oneQuits then {1} else ∅) ∪
    (if twoQuits then {2} else ∅)

private theorem playerThreeAtCoalition_nonempty (pivotAt oneQuits twoQuits : Bool) :
    (playerThreeAtCoalition pivotAt oneQuits twoQuits).Nonempty := by
  exact ⟨3, by simp [playerThreeAtCoalition]⟩

private theorem playerThreeResponseOutcome_at (N : ℕ) (hN : 1 ≤ N)
    (pivotAt oneQuits twoQuits : Bool) :
    quittingFirstStoppingOutcome (playerThreeResponseTimes N
      (some (if pivotAt then N - 1 else N)) (some (N - 1)) oneQuits twoQuits) =
      some ⟨playerThreeAtCoalition pivotAt oneQuits twoQuits,
        playerThreeAtCoalition_nonempty pivotAt oneQuits twoQuits⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ _
    (playerThreeAtCoalition_nonempty pivotAt oneQuits twoQuits) (N - 1)
  · intro player hplayer
    fin_cases player <;> fin_cases pivotAt <;> fin_cases oneQuits <;>
      fin_cases twoQuits <;> simp_all [playerThreeAtCoalition, playerThreeResponseTimes]
  · intro player hplayer
    fin_cases player <;> fin_cases pivotAt <;> fin_cases oneQuits <;>
      fin_cases twoQuits <;> simp_all [playerThreeAtCoalition, playerThreeResponseTimes,
        quittingStoppingTimeValue]
    all_goals exact hN

theorem playerThreeResponsePayoff_before (N : ℕ) (hN : 1 ≤ N)
    (pivotTime response : ℕ) (hresponse : response < N - 1)
    (hpivot : response < pivotTime) :
    (input N hN).purePivotResponderPayoff 3 (some pivotTime) (some response) 3 = 0 := by
  rw [playerThreeResponse_conditioned]
  have houtcome (oneQuits twoQuits : Bool) : quittingFirstStoppingOutcome
      (playerThreeResponseTimes N (some pivotTime) (some response) oneQuits twoQuits) =
      some ⟨{3}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {3} (by simp) response
    · intro player hplayer
      fin_cases player <;> simp_all [playerThreeResponseTimes]
    · intro player hplayer
      fin_cases player <;> fin_cases oneQuits <;> fin_cases twoQuits <;>
        simp_all [playerThreeResponseTimes, quittingStoppingTimeValue]
  simp_rw [pureTimesPayoff, houtcome]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem playerThreeResponsePayoff_at_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 3 (some (N - 1)) (some (N - 1)) 3 = -1 := by
  rw [playerThreeResponse_conditioned]
  have h00 := playerThreeResponseOutcome_at N hN true false false
  have h10 := playerThreeResponseOutcome_at N hN true true false
  have h01 := playerThreeResponseOutcome_at N hN true false true
  have h11 := playerThreeResponseOutcome_at N hN true true true
  simp only [if_true] at h00 h10 h01 h11
  rw [pureTimesPayoff, h00, pureTimesPayoff, h10, pureTimesPayoff, h01,
    pureTimesPayoff, h11]
  norm_num [quittingTerminalOutcomeReward, playerThreeAtCoalition, reward, Fin.ext_iff]

theorem playerThreeResponsePayoff_late_at (N : ℕ) (hN : 1 ≤ N) :
    (input N hN).purePivotResponderPayoff 3 (some N) (some (N - 1)) 3 = -31 / 49 := by
  rw [playerThreeResponse_conditioned]
  have h00 := playerThreeResponseOutcome_at N hN false false false
  have h10 := playerThreeResponseOutcome_at N hN false true false
  have h01 := playerThreeResponseOutcome_at N hN false false true
  have h11 := playerThreeResponseOutcome_at N hN false true true
  simp only [Bool.false_eq_true, if_false] at h00 h10 h01 h11
  rw [pureTimesPayoff, h00, pureTimesPayoff, h10, pureTimesPayoff, h01,
    pureTimesPayoff, h11]
  norm_num [quittingTerminalOutcomeReward, playerThreeAtCoalition, reward, Fin.ext_iff]

theorem playerThreeNeverResponse_eq_purePivotPayoff (N : ℕ) (hN : 1 ≤ N)
    (choice : Option ℕ) :
    (input N hN).purePivotResponderPayoff 3 choice none 3 =
      (input N hN).purePivotPayoff choice 3 := by
  unfold QuittingPivotRepairLPInput.purePivotResponderPayoff
    QuittingPivotRepairLPInput.purePivotPayoff
  rw [show Function.update
      (Function.update (input N hN).opponents (input N hN).pivot (PMF.pure choice)) 3
        (PMF.pure none) =
      Function.update (input N hN).opponents (input N hN).pivot (PMF.pure choice) by
    funext player
    fin_cases player <;> simp [input, opponents]]

end GameTheory.PivotRepairRationalResponseCoefficients
