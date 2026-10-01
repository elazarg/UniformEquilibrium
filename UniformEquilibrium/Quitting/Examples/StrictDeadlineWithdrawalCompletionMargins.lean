import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalCoordinateCompletion
import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalCertificate
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalPerturbation

/-! # Actual fixed-child affine deadline margins

The child right sides and fresh floors are computed internally from the
thirty-three arbitrary child-recipient coordinates. They are independent
of the outsider's eleven entries. The affine margins equal the canonical
actual raw slacks, not a supplied linear surrogate.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open FinFourLastPlayerChild GuardedCrossedResponseExamples
open scoped BigOperators

def sourceChildTerminal (index : Fin 7) : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨(coalition index).image (fun who : Child => who.1),
    (coalition_nonempty index).image (fun who => who.1)⟩

def sourceJoinedTerminal (index : Fin 7) : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨insert 3 (sourceChildTerminal index).1, Finset.insert_nonempty 3 _⟩

def futureRight (free : ChildCollisionSpace) (index : Fin 7) : ℝ :=
  ∑ who, advanceWeight who * cappedClockExactLPDelta (childReward (completionReward free 0))
    (.future ⟨coalition index, coalition_nonempty index⟩) who

def joiningRight (free : ChildCollisionSpace) (index : Fin 7) : ℝ :=
  ∑ who, (advanceWeight who * cappedClockExactLPDelta (childReward (completionReward free 0))
      (.joining ⟨coalition index, coalition_nonempty index⟩) who +
    withdrawalWeight who * deadlineWithdrawalGainFloor (childReward (completionReward free 0))
      who (coalition index) (coalition_nonempty index))

theorem completionReward_zeroFloor_congr (free : ChildCollisionSpace)
    (first second : OutsiderCollisionSpace) (who : Child) :
    deadlineWithdrawalZeroFloor (childReward (completionReward free first)) who =
      deadlineWithdrawalZeroFloor (childReward (completionReward free second)) who :=
  deadlineWithdrawalZeroFloor_congr_recipient _ _ who
    (fun terminal => completionReward_childReward_recipient_congr free first second terminal who)

theorem completionReward_gain_congr (free : ChildCollisionSpace)
    (first second : OutsiderCollisionSpace) (who : Child) (A : Finset Child) (hA : A.Nonempty) :
    deadlineWithdrawalGainFloor (childReward (completionReward free first)) who A hA =
      deadlineWithdrawalGainFloor (childReward (completionReward free second)) who A hA :=
  deadlineWithdrawalGainFloor_congr_recipient _ _ who
    (fun terminal => completionReward_childReward_recipient_congr free first second terminal who)
    A hA

theorem completionReward_delta_congr (free : ChildCollisionSpace)
    (first second : OutsiderCollisionSpace) (row : CappedClockExactLPRow Child) (who : Child) :
    cappedClockExactLPDelta (childReward (completionReward free first)) row who =
      cappedClockExactLPDelta (childReward (completionReward free second)) row who := by
  cases row with
  | never => exact completionReward_childReward_recipient_congr free first second _ who
  | future terminal =>
      dsimp only [cappedClockExactLPDelta]
      rw [completionReward_childReward_recipient_congr free first second,
        completionReward_childReward_recipient_congr free first second]
  | joining terminal =>
      dsimp only [cappedClockExactLPDelta]
      rw [completionReward_childReward_recipient_congr free first second,
        completionReward_childReward_recipient_congr free first second]

theorem completionReward_neverSlack_eq (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) : neverSlack (completionReward free outside) = 1 / 16 := by
  rw [neverSlack_reduced]
  simp only [quittingChildWithOutsiderReward_singleton_original,
    quittingChildWithOutsiderOriginalEmbedding_some,
    quittingChildWithOutsiderOriginalEmbedding_none, completionReward_singleton]
  norm_num [reward, integerReward, terminalShift, coalitionCode, child,
    FinFourLastPlayerChild.outside]

theorem completionReward_futureSlack_formula (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (index : Fin 7) :
    futureSlack (completionReward free outside) (coalition index) (coalition_nonempty index) =
      futureRight free index - reward ⟨{3}, Finset.singleton_nonempty 3⟩ 3 +
        completionReward free outside (sourceChildTerminal index) 3 := by
  have hsum : (∑ who, advanceWeight who * cappedClockExactLPDelta
      (childReward (completionReward free outside))
      (.future ⟨coalition index, coalition_nonempty index⟩) who) = futureRight free index := by
    unfold futureRight
    apply Finset.sum_congr rfl
    intro who _
    rw [completionReward_delta_congr free outside 0]
  unfold futureSlack
  rw [hsum]
  have hchild : childReward (completionReward free outside)
      ⟨cappedClockChildCoalition (coalition index),
        cappedClockChildCoalition_nonempty (coalition_nonempty index)⟩ none =
      completionReward free outside (sourceChildTerminal index) 3 := by
    simpa only [sourceChildTerminal, quittingChildWithOutsiderOriginalEmbedding_none] using
      quittingChildWithOutsiderReward_childCoalition_image (completionReward free outside)
        (· = 3) FinFourLastPlayerChild.outside (coalition index)
        (coalition_nonempty index) none
  simp only [cappedClockExactLPBase, quittingChildWithOutsiderReward_singleton_original,
    hchild,
    quittingChildWithOutsiderOriginalEmbedding_none, completionReward_singleton]
  change futureRight free index -
      (reward ⟨{3}, Finset.singleton_nonempty 3⟩ 3 -
        completionReward free outside (sourceChildTerminal index) 3) = _
  ring

theorem completionReward_joiningSlack_formula (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (index : Fin 7) :
    joiningSlack (completionReward free outside) (coalition index) (coalition_nonempty index) =
      joiningRight free index - completionReward free outside (sourceJoinedTerminal index) 3 +
        completionReward free outside (sourceChildTerminal index) 3 := by
  have hsum : (∑ who, (advanceWeight who * cappedClockExactLPDelta
      (childReward (completionReward free outside))
      (.joining ⟨coalition index, coalition_nonempty index⟩) who +
    withdrawalWeight who * deadlineWithdrawalGainFloor
      (childReward (completionReward free outside)) who
      (coalition index) (coalition_nonempty index))) = joiningRight free index := by
    unfold joiningRight
    apply Finset.sum_congr rfl
    intro who _
    rw [completionReward_delta_congr free outside 0, completionReward_gain_congr free outside 0]
  unfold joiningSlack
  rw [hsum]
  have hchild : childReward (completionReward free outside)
      ⟨cappedClockChildCoalition (coalition index),
        cappedClockChildCoalition_nonempty (coalition_nonempty index)⟩ none =
      completionReward free outside (sourceChildTerminal index) 3 := by
    simpa only [sourceChildTerminal, quittingChildWithOutsiderOriginalEmbedding_none] using
      quittingChildWithOutsiderReward_childCoalition_image (completionReward free outside)
        (· = 3) FinFourLastPlayerChild.outside (coalition index)
        (coalition_nonempty index) none
  simp only [cappedClockExactLPBase, hchild,
    quittingChildWithOutsiderReward_joinedCoalition_image,
    quittingChildWithOutsiderOriginalEmbedding_none]
  change joiningRight free index -
      (completionReward free outside (sourceJoinedTerminal index) 3 -
        completionReward free outside (sourceChildTerminal index) 3) = _
  ring

/-- The three singleton future rows are fixed by the sixteen fixed singleton coordinates. -/
theorem completionReward_futureSingletonSlack_eq (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (index : Fin 7)
    (hsingle : (sourceChildTerminal index).1.card = 1) :
    futureSlack (completionReward free outside) (coalition index) (coalition_nonempty index) =
      futureSlacks index := by
  rw [futureSlack_reduced]
  fin_cases index
  all_goals norm_num [sourceChildTerminal, coalition, child] at hsingle
  all_goals dsimp only [cappedClockExactLPDelta, cappedClockExactLPBase]
  all_goals norm_num +decide [quittingChildWithOutsiderReward_singleton_original,
    quittingChildWithOutsiderReward_childCoalition_image,
    quittingChildWithOutsiderOriginalEmbedding_some,
    quittingChildWithOutsiderOriginalEmbedding_none, completionReward_singleton,
    reward, integerReward, terminalShift, coalitionCode, child, coalition,
    futureSlacks, FinFourLastPlayerChild.outside]

def futureMarginAffine (free : ChildCollisionSpace) (index : Fin 7) :
    OutsiderCollisionSpace →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ OutsiderCollisionSpace
      (futureRight free index - reward ⟨{3}, Finset.singleton_nonempty 3⟩ 3) +
    completionRewardAffine free (sourceChildTerminal index) 3

def joiningMarginAffine (free : ChildCollisionSpace) (index : Fin 7) :
    OutsiderCollisionSpace →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ OutsiderCollisionSpace (joiningRight free index) -
    completionRewardAffine free (sourceJoinedTerminal index) 3 +
    completionRewardAffine free (sourceChildTerminal index) 3

theorem futureMarginAffine_apply (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (index : Fin 7) :
    futureMarginAffine free index outside =
      futureSlack (completionReward free outside) (coalition index) (coalition_nonempty index) := by
  rw [completionReward_futureSlack_formula]
  rfl

theorem joiningMarginAffine_apply (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (index : Fin 7) :
    joiningMarginAffine free index outside =
      joiningSlack (completionReward free outside) (coalition index)
        (coalition_nonempty index) := by
  rw [completionReward_joiningSlack_formula]
  rfl

end GameTheory.StrictDeadlineWithdrawal
