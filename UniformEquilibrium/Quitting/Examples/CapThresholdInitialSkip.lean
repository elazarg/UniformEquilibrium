import UniformEquilibrium.Quitting.Examples.CapThresholdRegressionCommon

/-! # Literal below-singleton initial skip: no solo block is required -/

namespace GameTheory.CapThresholdInitialSkip

open CapThresholdRegression QuittingSureSetOwnerRepair

def reward : RationalQuittingReward 2 := fun terminal =>
  if terminal.1 = {0} then ![1, 1]
  else if terminal.1 = {1} then ![-1, 1] else ![-1, -1]

def source : List (RationalQuittingRoot 2) := [pureRoot {0, 1}]
def exitRoot : RationalQuittingRoot 2 := pureRoot {0}

theorem reward_bound : ∀ terminal who, |reward terminal who| ≤ 1 := by decide

theorem source_pair : rationalQuittingFiniteWordSemanticPair reward source =
    (![-1, -1], ![-1, 1]) := by
  have hactual :
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (profile reward source) =
        RationalQuittingSemanticPair.toReal
          ((![-1, -1], ![-1, 1]) : RationalQuittingSemanticPair 2) := by
    unfold profile source
    rw [List.map_cons, List.map_nil, pureRoot_toPMF, quittingLiteralRootStackProfile_cons]
    rw [quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
      _ {0, 1} (by decide)]
    apply Prod.ext <;> funext who <;> fin_cases who <;>
      norm_num +decide [RationalQuittingSemanticPair.toReal, quittingSetReward,
        rationalQuittingRewardToReal, reward]
  apply RationalQuittingSemanticPair.toReal_injective
  exact (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward source).symm.trans hactual

theorem source_debt : rationalFiniteSourceDebt reward source = 2 := by
  rw [rationalFiniteSourceDebt, source_pair]
  norm_num [rationalQuittingSemanticDebtSum, Fin.sum_univ_succ]

theorem actual_source_pair :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
      (profile reward source) =
      RationalQuittingSemanticPair.toReal
        ((![-1, -1], ![-1, 1]) : RationalQuittingSemanticPair 2) :=
  actual_pair reward source _ source_pair

/-- Owner one is preempted; coordinate zero already has negative cap margin. -/
theorem initial_skip :
    reward (quittingSingletonTerminal 0) 0 - reward (quittingSingletonTerminal 1) 0 = 2 ∧
    (rationalQuittingFiniteWordSemanticPair reward source).2 0 -
      reward (quittingSingletonTerminal 0) 0 = -2 := by
  rw [source_pair]
  norm_num +decide [reward, quittingSingletonTerminal]

private theorem auxiliary_exact_root :
    IsεQuittingRootNash (rationalQuittingRewardToReal reward)
      (fun who => ((![-2, 0] : Fin 2 → ℚ) who : ℝ)) 0 exitRoot.toPMF := by
  rw [exitRoot, pureRoot_toPMF]
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash _ _ _).mp
  have hzero : quittingRootEndpointDifference (rationalQuittingRewardToReal reward)
      (fun who => ((![-2, 0] : Fin 2 → ℚ) who : ℝ))
      (quittingPureSetRoot {0}) 0 = 3 := by
    rw [quittingRootEndpointDifference, quittingRootQuitPayoff_pureSetRoot_eq_insert,
      quittingRootContinuePayoff_pureSingleton_eq_tail]
    norm_num +decide [quittingSetReward, rationalQuittingRewardToReal, reward]
  have hone : quittingRootEndpointDifference (rationalQuittingRewardToReal reward)
      (fun who => ((![-2, 0] : Fin 2 → ℚ) who : ℝ))
      (quittingPureSetRoot {0}) 1 = -2 := by
    rw [quittingRootEndpointDifference, quittingRootQuitPayoff_pureSetRoot_eq_insert,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty _ {0} 1 (by decide)]
    norm_num +decide [quittingSetReward, rationalQuittingRewardToReal, reward]
  unfold IsεQuittingRootEndpointNash
  intro who
  fin_cases who
  · change (quittingPureSetRoot ({0} : Finset (Fin 2)) 0 false).toReal *
        quittingRootEndpointDifference (rationalQuittingRewardToReal reward)
          (fun player => ((![-2, 0] : Fin 2 → ℚ) player : ℝ))
          (quittingPureSetRoot ({0} : Finset (Fin 2))) 0 ≤ 0 ∧
        -0 ≤ (quittingPureSetRoot ({0} : Finset (Fin 2)) 0 true).toReal *
          quittingRootEndpointDifference (rationalQuittingRewardToReal reward)
            (fun player => ((![-2, 0] : Fin 2 → ℚ) player : ℝ))
            (quittingPureSetRoot ({0} : Finset (Fin 2))) 0
    rw [hzero]
    norm_num [quittingPureSetRoot, quittingSetAction]
  · change (quittingPureSetRoot ({0} : Finset (Fin 2)) 1 false).toReal *
        quittingRootEndpointDifference (rationalQuittingRewardToReal reward)
          (fun player => ((![-2, 0] : Fin 2 → ℚ) player : ℝ))
          (quittingPureSetRoot ({0} : Finset (Fin 2))) 1 ≤ 0 ∧
        -0 ≤ (quittingPureSetRoot ({0} : Finset (Fin 2)) 1 true).toReal *
          quittingRootEndpointDifference (rationalQuittingRewardToReal reward)
            (fun player => ((![-2, 0] : Fin 2 → ℚ) player : ℝ))
            (quittingPureSetRoot ({0} : Finset (Fin 2))) 1
    rw [hone]
    norm_num [quittingPureSetRoot, quittingSetAction]

theorem auxiliary_defect_zero :
    Finite.rationalBooleanTotalNashDefect
      (rationalQuittingBooleanPayoff reward ![-2, 0]) exitRoot.probability = 0 := by
  have h := (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero _ _ _).mp auxiliary_exact_root
  rw [quittingRootTotalNashDefect_rationalQuitting_eq_cast] at h
  exact_mod_cast h

/-- The exact root is tested against B-1, not against a supplied cap oracle. -/
theorem actual_auxiliary_exact :
    IsεQuittingRootNash (rationalQuittingRewardToReal reward)
      (fun who => ((![-2, 0] : Fin 2 → ℚ) who : ℝ)) 0 exitRoot.toPMF :=
  auxiliary_exact_root

theorem exit_pair : rationalQuittingFiniteWordSemanticPair reward
    (exitRoot :: source) = (![1, 1], ![1, 1]) := by
  have hactual :
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (profile reward (exitRoot :: source)) =
        RationalQuittingSemanticPair.toReal
          ((![1, 1], ![1, 1]) : RationalQuittingSemanticPair 2) := by
    unfold profile
    rw [List.map_cons, quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation]
    change quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
        exitRoot.toPMF
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (profile reward source)) = _
    rw [actual_source_pair, exitRoot, pureRoot_toPMF]
    dsimp only [quittingTerminalSemanticPrefix, RationalQuittingSemanticPair.toReal]
    apply Prod.ext
    · funext who
      fin_cases who
      · change quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
          (fun player => ((![-1, -1] : Fin 2 → ℚ) player : ℝ))
          (quittingPureSetRoot ({0} : Finset (Fin 2))) 0 =
            ((![1, 1] : Fin 2 → ℚ) 0 : ℝ)
        rw [quittingRootSuccessorPayoff_eq_endpointMix,
          quittingRootQuitPayoff_pureSetRoot_eq_insert,
          quittingRootContinuePayoff_pureSingleton_eq_tail]
        norm_num +decide [quittingSetReward, rationalQuittingRewardToReal, reward,
          quittingPureSetRoot, quittingSetAction]
      · change quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
          (fun player => ((![-1, -1] : Fin 2 → ℚ) player : ℝ))
          (quittingPureSetRoot ({0} : Finset (Fin 2))) 1 =
            ((![1, 1] : Fin 2 → ℚ) 1 : ℝ)
        rw [quittingRootSuccessorPayoff_eq_endpointMix,
          quittingRootQuitPayoff_pureSetRoot_eq_insert,
          quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty _ {0} 1 (by decide)]
        norm_num +decide [quittingSetReward, rationalQuittingRewardToReal, reward,
          quittingPureSetRoot, quittingSetAction]
    · funext who
      fin_cases who
      · change max
          (quittingRootQuitPayoff (rationalQuittingRewardToReal reward)
            (fun player => ((![-1, -1] : Fin 2 → ℚ) player : ℝ))
            (quittingPureSetRoot ({0} : Finset (Fin 2))) 0)
          (quittingRootContinuePayoff (rationalQuittingRewardToReal reward)
            (Function.update (fun player => ((![-1, -1] : Fin 2 → ℚ) player : ℝ))
              0 ((![-1, 1] : Fin 2 → ℚ) 0 : ℝ))
            (quittingPureSetRoot ({0} : Finset (Fin 2))) 0) =
              ((![1, 1] : Fin 2 → ℚ) 0 : ℝ)
        rw [quittingRootQuitPayoff_pureSetRoot_eq_insert,
          quittingRootContinuePayoff_pureSingleton_eq_tail]
        norm_num +decide [quittingSetReward, rationalQuittingRewardToReal, reward]
      · change max
          (quittingRootQuitPayoff (rationalQuittingRewardToReal reward)
            (fun player => ((![-1, -1] : Fin 2 → ℚ) player : ℝ))
            (quittingPureSetRoot ({0} : Finset (Fin 2))) 1)
          (quittingRootContinuePayoff (rationalQuittingRewardToReal reward)
            (Function.update (fun player => ((![-1, -1] : Fin 2 → ℚ) player : ℝ))
              1 ((![-1, 1] : Fin 2 → ℚ) 1 : ℝ))
            (quittingPureSetRoot ({0} : Finset (Fin 2))) 1) =
              ((![1, 1] : Fin 2 → ℚ) 1 : ℝ)
        rw [quittingRootQuitPayoff_pureSetRoot_eq_insert,
          quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty _ {0} 1 (by decide)]
        norm_num +decide [quittingSetReward, rationalQuittingRewardToReal, reward]
  apply RationalQuittingSemanticPair.toReal_injective
  exact (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast
    reward (exitRoot :: source)).symm.trans hactual

theorem actual_exit_pair :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
      (profile reward (exitRoot :: source)) =
      RationalQuittingSemanticPair.toReal
        ((![1, 1], ![1, 1]) : RationalQuittingSemanticPair 2) :=
  actual_pair reward _ _ exit_pair

/-- All complete behavioral deviations, including Never, have zero debt. -/
theorem actual_exit_debt_zero :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (profile reward (exitRoot :: source))) = 0 := by
  simpa only [Rat.cast_zero] using
    (actual_debt reward (exitRoot :: source) 0 (by
      rw [rationalFiniteSourceDebt, exit_pair]
      norm_num [rationalQuittingSemanticDebtSum]))

end GameTheory.CapThresholdInitialSkip
