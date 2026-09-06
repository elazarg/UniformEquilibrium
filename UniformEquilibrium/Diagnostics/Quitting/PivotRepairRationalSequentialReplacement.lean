import UniformEquilibrium.Diagnostics.Quitting.PivotRepairRationalOptimizer

noncomputable section

namespace GameTheory.PivotRepairRationalSequentialReplacement

open Math.LinearProgramming
open PivotRepairRationalFixture
open PivotRepairRationalLowerBound
open PivotRepairRationalResponseCoefficients
open PivotRepairRationalOptimizer

/-- Fixed opponents after player 1 is replaced by Never. -/
def afterOneOpponents (N : ℕ) (hN : 1 ≤ N) : Fin 4 → PMF (Option ℕ) :=
  Function.update (opponents N hN) 1 (PMF.pure none)

def afterOneInput (N : ℕ) (hN : 1 ≤ N) : QuittingPivotRepairLPInput reward where
  opponents := afterOneOpponents N hN
  pivot := 0
  deadline := N
  deadline_pos := hN
  opponents_finite := by
    intro player hpivot choice hchoice
    by_cases hone : player = 1
    · subst player
      have hnone : choice = none := by
        simpa [afterOneOpponents, PMF.pure_apply] using hchoice
      exact Or.inl hnone
    · apply (input N hN).opponents_finite player hpivot choice
      simpa [afterOneOpponents, Function.update_of_ne hone] using hchoice

private def afterOnePureTimes (pivotChoice response : Option ℕ) :
    Fin 4 → Option ℕ
  | 0 => pivotChoice
  | 2 => response
  | _ => none

private theorem afterOnePurePayoff (N : ℕ) (hN : 1 ≤ N)
    (pivotChoice response : Option ℕ) :
    (afterOneInput N hN).purePivotResponderPayoff 2 pivotChoice response 2 =
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (fun player ↦ PMF.pure (afterOnePureTimes pivotChoice response player))) 2 := by
  unfold QuittingPivotRepairLPInput.purePivotResponderPayoff
  congr 3
  funext player
  fin_cases player <;> simp [afterOneInput, afterOneOpponents, opponents,
    afterOnePureTimes]

theorem afterOne_playerTwoResponse_at_at (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).purePivotResponderPayoff 2
      (some (N - 1)) (some (N - 1)) 2 = 5 := by
  rw [afterOnePurePayoff]
  rw [show (fun player ↦ PMF.pure
      (afterOnePureTimes (some (N - 1)) (some (N - 1)) player)) =
      pureCoalitionLaws {0, 2} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    pureCoalitionPayoff_eq_reward {0, 2} (by simp) (N - 1) 2]
  norm_num [reward, Fin.ext_iff]

theorem afterOne_playerTwoResponse_late_at (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).purePivotResponderPayoff 2 (some N) (some (N - 1)) 2 = 0 := by
  rw [afterOnePurePayoff, pureTimesPayoff]
  have hout : quittingFirstStoppingOutcome
      (afterOnePureTimes (some N) (some (N - 1))) = some ⟨{2}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {2}
      (by simp) (N - 1)
    · intro player hplayer
      fin_cases player <;> simp_all [afterOnePureTimes]
    · intro player hplayer
      fin_cases player <;> simp_all [afterOnePureTimes, quittingStoppingTimeValue]
      exact hN
  rw [hout]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem afterOne_playerTwoResponse_before (N : ℕ) (hN : 1 ≤ N)
    (pivotTime response : ℕ) (hpivot : response < pivotTime) :
    (afterOneInput N hN).purePivotResponderPayoff 2
      (some pivotTime) (some response) 2 = 0 := by
  rw [afterOnePurePayoff, pureTimesPayoff]
  have hout : quittingFirstStoppingOutcome
      (afterOnePureTimes (some pivotTime) (some response)) = some ⟨{2}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {2}
      (by simp) response
    · intro player hplayer
      fin_cases player <;> simp_all [afterOnePureTimes]
    · intro player hplayer
      fin_cases player <;> simp_all [afterOnePureTimes, quittingStoppingTimeValue]
  rw [hout]
  norm_num [quittingTerminalOutcomeReward, reward, Fin.ext_iff]

theorem afterOne_playerTwoNever_at (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).purePivotResponderPayoff 2 (some (N - 1)) none 2 = 7 := by
  rw [afterOnePurePayoff]
  rw [show (fun player ↦ PMF.pure
      (afterOnePureTimes (some (N - 1)) none player)) =
      pureCoalitionLaws {0} (N - 1) by
    funext player
    fin_cases player <;> rfl,
    pureCoalitionPayoff_eq_reward {0} (by simp) (N - 1) 2]
  norm_num [reward, Fin.ext_iff]

theorem afterOne_playerTwoNever_never (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).purePivotResponderPayoff 2 none none 2 = 0 := by
  rw [afterOnePurePayoff, pureTimesPayoff]
  rw [show afterOnePureTimes none none = fun _ : Fin 4 ↦ none by
    funext player
    fin_cases player <;> rfl,
    quittingFirstStoppingOutcome_all_never]
  rfl

private theorem afterOne_otherNeverProduct_two (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).otherNeverProduct 2 = 1 := by
  unfold QuittingPivotRepairLPInput.otherNeverProduct
  change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 2,
    ((afterOneOpponents N hN j) none).toReal) = _
  rw [show (Finset.univ.erase (0 : Fin 4)).erase 2 = {1, 3} by decide]
  simp [afterOneOpponents, opponents]

theorem afterOne_playerTwoEarlyContribution (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).earlyContribution (optimizerMass N hN) 2 = 616 / 107 := by
  unfold QuittingPivotRepairLPInput.earlyContribution
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (afterOneInput N hN).purePivotResponderPayoff 2 (some headTime.1) none 2) +
    (pivotRepairLate (optimizerMass N hN) + pivotRepairNever (optimizerMass N hN)) *
      (afterOneInput N hN).purePivotResponderPayoff 2 none none 2 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (afterOneInput N hN).purePivotResponderPayoff 2
      (some (N - 1)) none 2 +
    (19 / 107 + 0) * (afterOneInput N hN).purePivotResponderPayoff 2 none none 2 = _
  rw [afterOne_playerTwoNever_at, afterOne_playerTwoNever_never]
  norm_num

theorem afterOne_playerTwoNeverEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).responderNeverEndpoint (optimizerMass N hN) 2 = 7 := by
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint
  rw [afterOne_playerTwoEarlyContribution, afterOne_otherNeverProduct_two]
  norm_num [afterOneInput, pivotRepairLate, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterOne_playerTwoFirstEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).responderFirstEndpoint (optimizerMass N hN) 2 =
      1327 / 214 := by
  unfold QuittingPivotRepairLPInput.responderFirstEndpoint
  rw [afterOne_playerTwoEarlyContribution, afterOne_otherNeverProduct_two]
  norm_num [afterOneInput, pivotRepairLate, pivotRepairNever, pivotRepairFirstAtom,
    optimizerMass,
    QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterOne_playerTwoLimitEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterOneInput N hN).responderLimitEndpoint (optimizerMass N hN) 2 = 7 := by
  unfold QuittingPivotRepairLPInput.responderLimitEndpoint
  rw [afterOne_playerTwoEarlyContribution, afterOne_otherNeverProduct_two]
  norm_num [afterOneInput, pivotRepairLate, pivotRepairNever, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterOne_playerTwoHeadPayoff_le (N : ℕ) (hN : 1 ≤ N) (time : Fin N) :
    (afterOneInput N hN).pureResponsePayoff (optimizerMass N hN) 2
      (some time.1) 2 ≤ 7 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (afterOneInput N hN).purePivotResponderPayoff 2
        (some headTime.1) (some time.1) 2) +
    pivotRepairLate (optimizerMass N hN) *
      (afterOneInput N hN).purePivotResponderPayoff 2 (some N) (some time.1) 2 +
    pivotRepairNever (optimizerMass N hN) *
      (afterOneInput N hN).purePivotResponderPayoff 2 none (some time.1) 2 ≤ 7
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (afterOneInput N hN).purePivotResponderPayoff 2
        (some (N - 1)) (some (N - 1)) 2 +
      19 / 107 * (afterOneInput N hN).purePivotResponderPayoff 2
        (some N) (some (N - 1)) 2 + 0 * _ ≤ 7
    rw [afterOne_playerTwoResponse_at_at, afterOne_playerTwoResponse_late_at]
    norm_num
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (afterOneInput N hN).purePivotResponderPayoff 2
        (some (N - 1)) (some time.1) 2 +
      19 / 107 * (afterOneInput N hN).purePivotResponderPayoff 2
        (some N) (some time.1) 2 + 0 * _ ≤ 7
    rw [afterOne_playerTwoResponse_before N hN (N - 1) time.1 (by omega),
      afterOne_playerTwoResponse_before N hN N time.1 (by omega)]
    norm_num

def afterOneLaws (N : ℕ) (hN : 1 ≤ N) : Fin 4 → PMF (Option ℕ) :=
  (afterOneInput N hN).geometricLaws (optimizerMass N hN)
    (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num)

def afterOneProfile (N : ℕ) (hN : 1 ≤ N) : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward (afterOneLaws N hN)

theorem afterOneLaws_eq_update_optimizer (N : ℕ) (hN : 1 ≤ N) :
    afterOneLaws N hN =
      Function.update (optimizerGeometricLaws N hN) 1 (PMF.pure none) := by
  funext player
  fin_cases player <;>
    simp [afterOneLaws, optimizerGeometricLaws,
      QuittingPivotRepairLPInput.geometricLaws, afterOneInput, afterOneOpponents]

theorem afterOneProfile_eq_update_optimizer (N : ℕ) (hN : 1 ≤ N) :
    afterOneProfile N hN = Function.update (optimizerGeometricProfile N hN) 1
      (quittingStoppingLawBehaviorStrategy reward 1 (PMF.pure none)) := by
  rw [afterOneProfile, afterOneLaws_eq_update_optimizer]
  funext player
  by_cases hplayer : player = 1
  · subst player
    simp [quittingStoppingLawProfile]
  · simp [quittingStoppingLawProfile, optimizerGeometricProfile,
      Function.update_of_ne hplayer]

theorem afterOne_playerOne_payoff (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalPayoff reward (afterOneProfile N hN) 1 = 7 := by
  have hne : (1 : Fin 4) ≠ (input N hN).pivot := by
    change (1 : Fin 4) ≠ 0
    decide
  rw [afterOneProfile, afterOneLaws_eq_update_optimizer,
    optimizerGeometricLaws,
    (input N hN).geometric_neverResponse_eq (optimizerMass N hN)
      (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num) 1 hne,
    optimizerMass_playerOneNeverEndpoint]

theorem afterOne_playerOne_cap (N : ℕ) (hN : 1 ≤ N) :
    quittingContinuationBestResponseValue reward (afterOneProfile N hN) 1 = 7 := by
  rw [afterOneProfile_eq_update_optimizer,
    quittingContinuationBestResponseValue_update_self, optimizerGeometric_cap]
  norm_num

/-- Replacing player 1 by Never is an exact unrestricted behavioral best response. -/
theorem afterOne_playerOne_isFullBestResponse (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalPayoff reward (afterOneProfile N hN) 1 =
      quittingContinuationBestResponseValue reward (afterOneProfile N hN) 1 := by
  rw [afterOne_playerOne_payoff, afterOne_playerOne_cap]

theorem afterOne_playerTwo_cap (N : ℕ) (hN : 1 ≤ N) :
    quittingContinuationBestResponseValue reward (afterOneProfile N hN) 2 = 7 := by
  apply le_antisymm
  · have hne : (2 : Fin 4) ≠ (afterOneInput N hN).pivot := by
      change (2 : Fin 4) ≠ 0
      decide
    apply (afterOneInput N hN).geometric_cap_le_of_endpoints
      (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
      (by norm_num) (by norm_num) (by
        norm_num [afterOneInput, pivotRepairLate, pivotRepairFirstAtom,
          optimizerMass]) 2 hne 7
    · exact afterOne_playerTwoHeadPayoff_le N hN
    · rw [afterOne_playerTwoNeverEndpoint]
    · rw [afterOne_playerTwoFirstEndpoint]
      norm_num
    · rw [afterOne_playerTwoLimitEndpoint]
  · have hne : (2 : Fin 4) ≠ (afterOneInput N hN).pivot := by
      change (2 : Fin 4) ≠ 0
      decide
    have h := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
      (afterOneProfile N hN) 2 (quittingPureTimeBehaviorStrategy reward 2 none)
    unfold afterOneProfile at h
    rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at h
    change quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (Function.update (afterOneLaws N hN) 2 (PMF.pure none))) 2 ≤
      quittingContinuationBestResponseValue reward (afterOneProfile N hN) 2 at h
    rw [afterOneLaws,
      (afterOneInput N hN).geometric_neverResponse_eq (optimizerMass N hN)
        (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num) 2 hne,
      afterOne_playerTwoNeverEndpoint] at h
    exact h

/-- Fixed opponents after players 1 and 2 have both been replaced by Never. -/
def afterTwoOpponents (N : ℕ) (hN : 1 ≤ N) : Fin 4 → PMF (Option ℕ) :=
  Function.update (afterOneOpponents N hN) 2 (PMF.pure none)

def afterTwoInput (N : ℕ) (hN : 1 ≤ N) : QuittingPivotRepairLPInput reward where
  opponents := afterTwoOpponents N hN
  pivot := 0
  deadline := N
  deadline_pos := hN
  opponents_finite := by
    intro player hpivot choice hchoice
    have hplayer : player = 1 ∨ player = 2 ∨ player = 3 := by
      fin_cases player <;> simp_all
    rcases hplayer with rfl | rfl | rfl
    · left
      simpa [afterTwoOpponents, afterOneOpponents, opponents, PMF.pure_apply]
        using hchoice
    · left
      simpa [afterTwoOpponents, afterOneOpponents, opponents, PMF.pure_apply]
        using hchoice
    · left
      simpa [afterTwoOpponents, afterOneOpponents, opponents, PMF.pure_apply]
        using hchoice

/-- Actual stopping laws after subsequently replacing player 2 by Never. -/
def afterTwoLaws (N : ℕ) (hN : 1 ≤ N) : Fin 4 → PMF (Option ℕ) :=
  Function.update (afterOneLaws N hN) 2 (PMF.pure none)

def afterTwoProfile (N : ℕ) (hN : 1 ≤ N) : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward (afterTwoLaws N hN)

theorem afterTwoLaws_eq_geometric (N : ℕ) (hN : 1 ≤ N) :
    afterTwoLaws N hN =
      (afterTwoInput N hN).geometricLaws (optimizerMass N hN)
        (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num) := by
  funext player
  fin_cases player <;>
    simp [afterTwoLaws, afterOneLaws, afterTwoInput, afterTwoOpponents,
      afterOneInput, afterOneOpponents, QuittingPivotRepairLPInput.geometricLaws]

theorem afterTwo_purePivotPayoff_some (N : ℕ) (hN : 1 ≤ N) (time : ℕ)
    (who : Fin 4) :
    (afterTwoInput N hN).purePivotPayoff (some time) who = reward ⟨{0}, by simp⟩ who := by
  unfold QuittingPivotRepairLPInput.purePivotPayoff
  rw [show Function.update (afterTwoInput N hN).opponents
      (afterTwoInput N hN).pivot (PMF.pure (some time)) =
      pureCoalitionLaws {0} time by
    funext player
    fin_cases player <;>
      simp [afterTwoInput, afterTwoOpponents, afterOneOpponents, opponents,
        pureCoalitionLaws],
    pureCoalitionPayoff_eq_reward {0} (by simp) time who]

theorem afterTwo_purePivotPayoff_never (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    (afterTwoInput N hN).purePivotPayoff none who = 0 := by
  unfold QuittingPivotRepairLPInput.purePivotPayoff
  rw [show Function.update (afterTwoInput N hN).opponents
      (afterTwoInput N hN).pivot (PMF.pure none) =
      fun _ : Fin 4 ↦ PMF.pure none by
    funext player
    fin_cases player <;>
      simp [afterTwoInput, afterTwoOpponents, afterOneOpponents, opponents],
    pureTimesPayoff, quittingFirstStoppingOutcome_all_never]
  rfl

private def afterTwoPureTimes (responder : Fin 4)
    (pivotChoice response : Option ℕ) (player : Fin 4) : Option ℕ :=
  if player = 0 then pivotChoice else if player = responder then response else none

private theorem afterTwoPurePayoff (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ 0) (pivotChoice response : Option ℕ)
    (observer : Fin 4) :
    (afterTwoInput N hN).purePivotResponderPayoff responder pivotChoice response observer =
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward
        (fun player ↦ PMF.pure
          (afterTwoPureTimes responder pivotChoice response player))) observer := by
  unfold QuittingPivotRepairLPInput.purePivotResponderPayoff
  congr 3
  funext player
  by_cases hresponse : player = responder
  · subst player
    simp [afterTwoPureTimes, hne]
  · by_cases hpivot : player = 0
    · subst player
      simp [afterTwoInput, afterTwoPureTimes, hresponse]
    · fin_cases player <;>
        simp_all [afterTwoInput, afterTwoOpponents, afterOneOpponents, opponents,
          afterTwoPureTimes]

theorem afterTwo_responder_at_at (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ 0) (time : ℕ) (observer : Fin 4) :
    (afterTwoInput N hN).purePivotResponderPayoff responder
      (some time) (some time) observer = reward ⟨{0, responder}, by simp⟩ observer := by
  rw [afterTwoPurePayoff N hN responder hne]
  rw [show (fun player ↦ PMF.pure
      (afterTwoPureTimes responder (some time) (some time) player)) =
      pureCoalitionLaws {0, responder} time by
    funext player
    simp [afterTwoPureTimes, pureCoalitionLaws]
    aesop,
    pureCoalitionPayoff_eq_reward {0, responder} (by simp) time observer]

theorem afterTwo_responder_before (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ 0) (pivotTime response : ℕ)
    (hbefore : response < pivotTime) (observer : Fin 4) :
    (afterTwoInput N hN).purePivotResponderPayoff responder
      (some pivotTime) (some response) observer = reward ⟨{responder}, by simp⟩ observer := by
  rw [afterTwoPurePayoff N hN responder hne, pureTimesPayoff]
  have hout : quittingFirstStoppingOutcome
      (afterTwoPureTimes responder (some pivotTime) (some response)) =
      some ⟨{responder}, by simp⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later _ {responder}
      (by simp) response
    · intro player hplayer
      simp only [Finset.mem_singleton] at hplayer
      subst player
      simp [afterTwoPureTimes, hne]
    · intro player hplayer
      simp only [Finset.mem_singleton] at hplayer
      by_cases hpivot : player = 0
      · subst player
        simp [afterTwoPureTimes, quittingStoppingTimeValue, hbefore]
      · simp [afterTwoPureTimes, hpivot, hplayer, quittingStoppingTimeValue]
  rw [hout]
  rfl

theorem afterTwo_responder_never_at (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ 0) (time : ℕ) (observer : Fin 4) :
    (afterTwoInput N hN).purePivotResponderPayoff responder
      (some time) none observer = reward ⟨{0}, by simp⟩ observer := by
  rw [afterTwoPurePayoff N hN responder hne]
  rw [show (fun player ↦ PMF.pure
      (afterTwoPureTimes responder (some time) none player)) =
      pureCoalitionLaws {0} time by
    funext player
    simp [afterTwoPureTimes, pureCoalitionLaws],
    pureCoalitionPayoff_eq_reward {0} (by simp) time observer]

theorem afterTwo_responder_never_never (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ 0) (observer : Fin 4) :
    (afterTwoInput N hN).purePivotResponderPayoff responder none none observer = 0 := by
  rw [afterTwoPurePayoff N hN responder hne, pureTimesPayoff]
  rw [show afterTwoPureTimes responder none none = fun _ : Fin 4 ↦ none by
    funext player
    simp [afterTwoPureTimes],
    quittingFirstStoppingOutcome_all_never]
  rfl

theorem afterTwo_prescribedPayoff (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    (afterTwoInput N hN).prescribedPayoff (optimizerMass N hN) who =
      ![1, 7, 7, 0] who := by
  unfold QuittingPivotRepairLPInput.prescribedPayoff
  change (∑ time : Fin N, pivotRepairHead (optimizerMass N hN) time *
      (afterTwoInput N hN).purePivotPayoff (some time.1) who) +
    pivotRepairLate (optimizerMass N hN) *
      (afterTwoInput N hN).purePivotPayoff (some N) who +
    pivotRepairNever (optimizerMass N hN) *
      (afterTwoInput N hN).purePivotPayoff none who = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (afterTwoInput N hN).purePivotPayoff (some (N - 1)) who +
    19 / 107 * (afterTwoInput N hN).purePivotPayoff (some N) who +
    0 * (afterTwoInput N hN).purePivotPayoff none who = _
  rw [afterTwo_purePivotPayoff_some, afterTwo_purePivotPayoff_some,
    afterTwo_purePivotPayoff_never]
  fin_cases who <;> norm_num [reward, Fin.ext_iff]

theorem afterTwo_payoff (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingTerminalPayoff reward (afterTwoProfile N hN) who = ![1, 7, 7, 0] who := by
  rw [afterTwoProfile, afterTwoLaws_eq_geometric,
    (afterTwoInput N hN).geometric_payoff_eq_prescribedPayoff,
    afterTwo_prescribedPayoff]

private theorem afterTwo_otherNeverProduct (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ 0) :
    (afterTwoInput N hN).otherNeverProduct responder = 1 := by
  unfold QuittingPivotRepairLPInput.otherNeverProduct
  fin_cases responder
  · exact (hne rfl).elim
  · change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 1,
      ((afterTwoOpponents N hN j) none).toReal) = _
    rw [show (Finset.univ.erase (0 : Fin 4)).erase 1 = {2, 3} by decide]
    simp [afterTwoOpponents, afterOneOpponents, opponents]
  · change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 2,
      ((afterTwoOpponents N hN j) none).toReal) = _
    rw [show (Finset.univ.erase (0 : Fin 4)).erase 2 = {1, 3} by decide]
    simp [afterTwoOpponents, afterOneOpponents, opponents]
  · change (∏ j ∈ (Finset.univ.erase (0 : Fin 4)).erase 3,
      ((afterTwoOpponents N hN j) none).toReal) = _
    rw [show (Finset.univ.erase (0 : Fin 4)).erase 3 = {1, 2} by decide]
    simp [afterTwoOpponents, afterOneOpponents]

theorem afterTwo_earlyContribution_one (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).earlyContribution (optimizerMass N hN) 1 = 616 / 107 := by
  unfold QuittingPivotRepairLPInput.earlyContribution
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (afterTwoInput N hN).purePivotResponderPayoff 1 (some headTime.1) none 1) +
    (pivotRepairLate (optimizerMass N hN) + pivotRepairNever (optimizerMass N hN)) *
      (afterTwoInput N hN).purePivotResponderPayoff 1 none none 1 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (afterTwoInput N hN).purePivotResponderPayoff 1
      (some (N - 1)) none 1 + (19 / 107 + 0) *
      (afterTwoInput N hN).purePivotResponderPayoff 1 none none 1 = _
  rw [afterTwo_responder_never_at N hN 1 (by decide),
    afterTwo_responder_never_never N hN 1 (by decide)]
  norm_num [reward, Fin.ext_iff]

theorem afterTwo_earlyContribution_three (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).earlyContribution (optimizerMass N hN) 3 = 0 := by
  unfold QuittingPivotRepairLPInput.earlyContribution
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (afterTwoInput N hN).purePivotResponderPayoff 3 (some headTime.1) none 3) +
    (pivotRepairLate (optimizerMass N hN) + pivotRepairNever (optimizerMass N hN)) *
      (afterTwoInput N hN).purePivotResponderPayoff 3 none none 3 = _
  rw [optimizerMass_headWeightedSum]
  change (88 / 107) * (afterTwoInput N hN).purePivotResponderPayoff 3
      (some (N - 1)) none 3 + (19 / 107 + 0) *
      (afterTwoInput N hN).purePivotResponderPayoff 3 none none 3 = _
  rw [afterTwo_responder_never_at N hN 3 (by decide),
    afterTwo_responder_never_never N hN 3 (by decide)]
  norm_num [reward, Fin.ext_iff]

theorem afterTwo_playerOneNeverEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).responderNeverEndpoint (optimizerMass N hN) 1 = 7 := by
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint
  rw [afterTwo_earlyContribution_one, afterTwo_otherNeverProduct N hN 1 (by decide)]
  norm_num [afterTwoInput, pivotRepairLate, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterTwo_playerOneFirstEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).responderFirstEndpoint (optimizerMass N hN) 1 = 692 / 107 := by
  unfold QuittingPivotRepairLPInput.responderFirstEndpoint
  rw [afterTwo_earlyContribution_one, afterTwo_otherNeverProduct N hN 1 (by decide)]
  norm_num [afterTwoInput, pivotRepairLate, pivotRepairNever, pivotRepairFirstAtom,
    optimizerMass, QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterTwo_playerOneLimitEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).responderLimitEndpoint (optimizerMass N hN) 1 = 7 := by
  unfold QuittingPivotRepairLPInput.responderLimitEndpoint
  rw [afterTwo_earlyContribution_one, afterTwo_otherNeverProduct N hN 1 (by decide)]
  norm_num [afterTwoInput, pivotRepairLate, pivotRepairNever, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterTwo_playerThreeNeverEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).responderNeverEndpoint (optimizerMass N hN) 3 = 0 := by
  unfold QuittingPivotRepairLPInput.responderNeverEndpoint
  rw [afterTwo_earlyContribution_three, afterTwo_otherNeverProduct N hN 3 (by decide)]
  norm_num [afterTwoInput, pivotRepairLate, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterTwo_playerThreeFirstEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).responderFirstEndpoint (optimizerMass N hN) 3 = -19 / 214 := by
  unfold QuittingPivotRepairLPInput.responderFirstEndpoint
  rw [afterTwo_earlyContribution_three, afterTwo_otherNeverProduct N hN 3 (by decide)]
  norm_num [afterTwoInput, pivotRepairLate, pivotRepairNever, pivotRepairFirstAtom,
    optimizerMass, QuittingPivotRepairLPInput.responderTieReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterTwo_playerThreeLimitEndpoint (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).responderLimitEndpoint (optimizerMass N hN) 3 = 0 := by
  unfold QuittingPivotRepairLPInput.responderLimitEndpoint
  rw [afterTwo_earlyContribution_three, afterTwo_otherNeverProduct N hN 3 (by decide)]
  norm_num [afterTwoInput, pivotRepairLate, pivotRepairNever, optimizerMass,
    QuittingPivotRepairLPInput.responderEarlierReward,
    QuittingPivotRepairLPInput.responderLaterReward, quittingSingletonTerminal,
    reward, Fin.ext_iff]

theorem afterTwo_playerOneHeadPayoff_le (N : ℕ) (hN : 1 ≤ N) (time : Fin N) :
    (afterTwoInput N hN).pureResponsePayoff (optimizerMass N hN) 1
      (some time.1) 1 ≤ 7 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (afterTwoInput N hN).purePivotResponderPayoff 1
        (some headTime.1) (some time.1) 1) +
    pivotRepairLate (optimizerMass N hN) *
      (afterTwoInput N hN).purePivotResponderPayoff 1 (some N) (some time.1) 1 +
    pivotRepairNever (optimizerMass N hN) *
      (afterTwoInput N hN).purePivotResponderPayoff 1 none (some time.1) 1 ≤ 7
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (afterTwoInput N hN).purePivotResponderPayoff 1
        (some (N - 1)) (some (N - 1)) 1 +
      19 / 107 * (afterTwoInput N hN).purePivotResponderPayoff 1
        (some N) (some (N - 1)) 1 + 0 * _ ≤ 7
    rw [afterTwo_responder_at_at N hN 1 (by decide),
      afterTwo_responder_before N hN 1 (by decide) N (N - 1) (by omega)]
    norm_num [reward, Fin.ext_iff]
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (afterTwoInput N hN).purePivotResponderPayoff 1
        (some (N - 1)) (some time.1) 1 +
      19 / 107 * (afterTwoInput N hN).purePivotResponderPayoff 1
        (some N) (some time.1) 1 + 0 * _ ≤ 7
    rw [afterTwo_responder_before N hN 1 (by decide) (N - 1) time.1 htime,
      afterTwo_responder_before N hN 1 (by decide) N time.1 (by omega)]
    norm_num [reward, Fin.ext_iff]

theorem afterTwo_playerThreeHeadPayoff_le (N : ℕ) (hN : 1 ≤ N) (time : Fin N) :
    (afterTwoInput N hN).pureResponsePayoff (optimizerMass N hN) 3
      (some time.1) 3 ≤ 0 := by
  unfold QuittingPivotRepairLPInput.pureResponsePayoff
  change (∑ headTime : Fin N, pivotRepairHead (optimizerMass N hN) headTime *
      (afterTwoInput N hN).purePivotResponderPayoff 3
        (some headTime.1) (some time.1) 3) +
    pivotRepairLate (optimizerMass N hN) *
      (afterTwoInput N hN).purePivotResponderPayoff 3 (some N) (some time.1) 3 +
    pivotRepairNever (optimizerMass N hN) *
      (afterTwoInput N hN).purePivotResponderPayoff 3 none (some time.1) 3 ≤ 0
  rw [optimizerMass_headWeightedSum]
  by_cases heq : time = tauIndex N hN
  · subst time
    change (88 / 107) * (afterTwoInput N hN).purePivotResponderPayoff 3
        (some (N - 1)) (some (N - 1)) 3 +
      19 / 107 * (afterTwoInput N hN).purePivotResponderPayoff 3
        (some N) (some (N - 1)) 3 + 0 * _ ≤ 0
    rw [afterTwo_responder_at_at N hN 3 (by decide),
      afterTwo_responder_before N hN 3 (by decide) N (N - 1) (by omega)]
    norm_num [reward, Fin.ext_iff]
  · have htime : time.1 < N - 1 := by
      have hle : time.1 ≤ N - 1 := by omega
      exact lt_of_le_of_ne hle (fun h ↦ heq (Fin.ext h))
    change (88 / 107) * (afterTwoInput N hN).purePivotResponderPayoff 3
        (some (N - 1)) (some time.1) 3 +
      19 / 107 * (afterTwoInput N hN).purePivotResponderPayoff 3
        (some N) (some time.1) 3 + 0 * _ ≤ 0
    rw [afterTwo_responder_before N hN 3 (by decide) (N - 1) time.1 htime,
      afterTwo_responder_before N hN 3 (by decide) N time.1 (by omega)]
    norm_num [reward, Fin.ext_iff]

private theorem optimizerMass_half_match (N : ℕ) (hN : 1 ≤ N) :
    pivotRepairLate (optimizerMass N hN) * (1 / 2) =
      pivotRepairFirstAtom (optimizerMass N hN) := by
  norm_num [pivotRepairLate, pivotRepairFirstAtom, optimizerMass]

private theorem afterTwo_neverEndpoint_le_cap (N : ℕ) (hN : 1 ≤ N)
    (responder : Fin 4) (hne : responder ≠ (afterTwoInput N hN).pivot) :
    (afterTwoInput N hN).responderNeverEndpoint (optimizerMass N hN) responder ≤
      quittingContinuationBestResponseValue reward (afterTwoProfile N hN) responder := by
  have h := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
    (afterTwoProfile N hN) responder
    (quittingPureTimeBehaviorStrategy reward responder none)
  unfold afterTwoProfile at h
  rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at h
  rw [afterTwoLaws_eq_geometric,
    (afterTwoInput N hN).geometric_neverResponse_eq (optimizerMass N hN)
      (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num)
      responder hne] at h
  simpa only [afterTwoProfile, afterTwoLaws_eq_geometric] using h

theorem afterTwo_playerOne_cap (N : ℕ) (hN : 1 ≤ N) :
    quittingContinuationBestResponseValue reward (afterTwoProfile N hN) 1 = 7 := by
  apply le_antisymm
  · have hne : (1 : Fin 4) ≠ (afterTwoInput N hN).pivot := by
      change (1 : Fin 4) ≠ 0
      decide
    rw [afterTwoProfile, afterTwoLaws_eq_geometric]
    apply (afterTwoInput N hN).geometric_cap_le_of_endpoints
      (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
      (by norm_num) (by norm_num) (optimizerMass_half_match N hN) 1 hne 7
    · exact afterTwo_playerOneHeadPayoff_le N hN
    · rw [afterTwo_playerOneNeverEndpoint]
    · rw [afterTwo_playerOneFirstEndpoint]
      norm_num
    · rw [afterTwo_playerOneLimitEndpoint]
  · have hne : (1 : Fin 4) ≠ (afterTwoInput N hN).pivot := by
      change (1 : Fin 4) ≠ 0
      decide
    have h := afterTwo_neverEndpoint_le_cap N hN 1 hne
    rw [afterTwo_playerOneNeverEndpoint] at h
    exact h

theorem afterTwo_playerThree_cap (N : ℕ) (hN : 1 ≤ N) :
    quittingContinuationBestResponseValue reward (afterTwoProfile N hN) 3 = 0 := by
  apply le_antisymm
  · have hne : (3 : Fin 4) ≠ (afterTwoInput N hN).pivot := by
      change (3 : Fin 4) ≠ 0
      decide
    rw [afterTwoProfile, afterTwoLaws_eq_geometric]
    apply (afterTwoInput N hN).geometric_cap_le_of_endpoints
      (optimizerMass N hN) (optimizerMass_feasible N hN) (1 / 2)
      (by norm_num) (by norm_num) (optimizerMass_half_match N hN) 3 hne 0
    · exact afterTwo_playerThreeHeadPayoff_le N hN
    · rw [afterTwo_playerThreeNeverEndpoint]
    · rw [afterTwo_playerThreeFirstEndpoint]
      norm_num
    · rw [afterTwo_playerThreeLimitEndpoint]
  · have hne : (3 : Fin 4) ≠ (afterTwoInput N hN).pivot := by
      change (3 : Fin 4) ≠ 0
      decide
    have h := afterTwo_neverEndpoint_le_cap N hN 3 hne
    rw [afterTwo_playerThreeNeverEndpoint] at h
    exact h

theorem afterTwo_pivotLatePayoff (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).pivotLatePayoff = 1 := by
  unfold QuittingPivotRepairLPInput.pivotLatePayoff
  rw [show (afterTwoInput N hN).pivotNeverPayoff = 0 by
    unfold QuittingPivotRepairLPInput.pivotNeverPayoff
    exact afterTwo_purePivotPayoff_never N hN 0]
  change 0 + reward (quittingSingletonTerminal 0) 0 *
    (∏ j ∈ Finset.univ.erase (0 : Fin 4), ((afterTwoOpponents N hN j) none).toReal) = 1
  rw [show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
  norm_num [afterTwoOpponents, afterOneOpponents, quittingSingletonTerminal,
    opponents, reward, Fin.ext_iff]

theorem afterTwo_pivotCap (N : ℕ) (hN : 1 ≤ N) :
    (afterTwoInput N hN).pivotCap = 1 := by
  apply le_antisymm
  · unfold QuittingPivotRepairLPInput.pivotCap
    apply Finset.sup'_le
    intro candidate _
    cases candidate with
    | inl time =>
        simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
        rw [afterTwo_purePivotPayoff_some]
        norm_num [afterTwoInput, reward, Fin.ext_iff]
    | inr endpoint =>
        cases endpoint
        · simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue,
            QuittingPivotRepairLPInput.pivotNeverPayoff]
          rw [afterTwo_purePivotPayoff_never]
          norm_num
        · simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
          rw [afterTwo_pivotLatePayoff]
  · unfold QuittingPivotRepairLPInput.pivotCap
    rw [← afterTwo_pivotLatePayoff N hN]
    change (afterTwoInput N hN).pivotCapCandidateValue (Sum.inr true) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (afterTwoInput N hN).pivotCapCandidateValue
    exact Finset.le_sup' (afterTwoInput N hN).pivotCapCandidateValue
      (Finset.mem_univ (Sum.inr true : Fin N ⊕ Bool))

theorem afterTwo_pivot_cap (N : ℕ) (hN : 1 ≤ N) :
    quittingContinuationBestResponseValue reward (afterTwoProfile N hN) 0 = 1 := by
  rw [afterTwoProfile, afterTwoLaws_eq_geometric]
  change quittingContinuationBestResponseValue reward
    (quittingStoppingLawProfile reward
      (Function.update (afterTwoInput N hN).opponents (afterTwoInput N hN).pivot
        ((afterTwoInput N hN).geometricLaws (optimizerMass N hN)
          (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num)
            (afterTwoInput N hN).pivot))) (afterTwoInput N hN).pivot = 1
  rw [← (afterTwoInput N hN).pivotCap_eq_continuationBestResponseValue,
    afterTwo_pivotCap]

theorem afterTwoProfile_eq_update_afterOne (N : ℕ) (hN : 1 ≤ N) :
    afterTwoProfile N hN = Function.update (afterOneProfile N hN) 2
      (quittingStoppingLawBehaviorStrategy reward 2 (PMF.pure none)) := by
  funext player
  by_cases hplayer : player = 2
  · subst player
    simp [afterTwoProfile, afterTwoLaws, quittingStoppingLawProfile]
  · simp [afterTwoProfile, afterTwoLaws, afterOneProfile,
      quittingStoppingLawProfile, Function.update_of_ne hplayer]

theorem afterTwo_playerTwo_payoff (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalPayoff reward (afterTwoProfile N hN) 2 = 7 := by
  have hne : (2 : Fin 4) ≠ (afterOneInput N hN).pivot := by
    change (2 : Fin 4) ≠ 0
    decide
  rw [afterTwoProfile, afterTwoLaws, afterOneLaws,
    (afterOneInput N hN).geometric_neverResponse_eq (optimizerMass N hN)
      (optimizerMass_feasible N hN) (1 / 2) (by norm_num) (by norm_num) 2 hne,
    afterOne_playerTwoNeverEndpoint]

theorem afterTwo_playerTwo_cap (N : ℕ) (hN : 1 ≤ N) :
    quittingContinuationBestResponseValue reward (afterTwoProfile N hN) 2 = 7 := by
  rw [afterTwoProfile_eq_update_afterOne,
    quittingContinuationBestResponseValue_update_self, afterOne_playerTwo_cap]

/-- The second Never replacement is also an exact unrestricted behavioral best response. -/
theorem afterTwo_playerTwo_isFullBestResponse (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalPayoff reward (afterTwoProfile N hN) 2 =
      quittingContinuationBestResponseValue reward (afterTwoProfile N hN) 2 := by
  rw [afterTwo_playerTwo_payoff, afterTwo_playerTwo_cap]

theorem afterTwo_cap (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingContinuationBestResponseValue reward (afterTwoProfile N hN) who =
      ![1, 7, 7, 0] who := by
  fin_cases who
  · exact afterTwo_pivot_cap N hN
  · exact afterTwo_playerOne_cap N hN
  · exact afterTwo_playerTwo_cap N hN
  · exact afterTwo_playerThree_cap N hN

/-- Every displayed strategy in the twice-replaced profile attains its unrestricted cap. -/
theorem afterTwo_isFullBestResponse (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingTerminalPayoff reward (afterTwoProfile N hN) who =
      quittingContinuationBestResponseValue reward (afterTwoProfile N hN) who := by
  rw [afterTwo_payoff, afterTwo_cap]

theorem afterTwo_debt (N : ℕ) (hN : 1 ≤ N) (who : Fin 4) :
    quittingTerminalDeviationDebt reward (afterTwoProfile N hN) who = 0 := by
  unfold quittingTerminalDeviationDebt
  rw [afterTwo_cap, afterTwo_payoff]
  exact sub_self _

theorem afterTwo_exploitability (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalExploitability reward (afterTwoProfile N hN) = 0 := by
  rw [quittingTerminalExploitability_eq_max_debt]
  simp only [afterTwo_debt]
  unfold QuittingBoundaryHolonomy.finitePlayerMax
  simp

theorem afterTwo_isExactTerminalNash (N : ℕ) (hN : 1 ≤ N) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (afterTwoProfile N hN) := by
  apply isεAsymptoticNash_of_quittingTerminalExploitability_le
  rw [afterTwo_exploitability]

end GameTheory.PivotRepairRationalSequentialReplacement
