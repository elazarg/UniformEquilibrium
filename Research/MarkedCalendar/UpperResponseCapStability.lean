import Research.MarkedCalendar.Order
import Research.MarkedCalendar.ChronologicalCellSignedVariation

/-! # Early opponents and upper response kernels

Once one actual opponent clock is strictly earlier than both tested responses,
the complete first-label coalition is identical. Ties among early opponents are
retained, and a tested response may be Never. Actual legal finite-source late
conditionals then scale every upper response difference by one positive factor,
giving one common additive constant for all upper replies, including Never.

The marked-limit affine identity, compact lower-region stability, and final
closed-upper conditional full-cap bound are not yet supplied here. Finite-source
selected response identities do not assert an actual endpoint minimum or cap.
-/

noncomputable section

namespace MathUE.MarkedCalendar

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual earlier opponent makes both upper responses produce the same full coalition. -/
theorem responseLabels_eq_of_opponent_lt_both
    (C : Calendar) (who : ι) (sample : {j : ι // j ≠ who} → unitInterval)
    (first second : WithTop ℝ) (early : {j : ι // j ≠ who})
    (hfirst : C.collapseClock (sample early) < first)
    (hsecond : C.collapseClock (sample early) < second) :
    responseLabels C who first sample = responseLabels C who second sample := by
  classical
  have hearly (reply : WithTop ℝ) :
      responseClock C who reply sample early.val = C.collapseClock (sample early) := by
    simp only [responseClock, dite_eq_right early.property]
  have hwho (reply : WithTop ℝ) : responseClock C who reply sample who = reply := by
    simp [responseClock]
  ext i
  simp only [responseLabels, minimumLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i = who
  · subst i
    have hnotFirst : ¬ ∀ j, responseClock C who first sample who ≤
        responseClock C who first sample j := by
      intro h
      have hle := h early.val
      rw [hwho, hearly] at hle
      exact not_le_of_gt hfirst hle
    have hnotSecond : ¬ ∀ j, responseClock C who second sample who ≤
        responseClock C who second sample j := by
      intro h
      have hle := h early.val
      rw [hwho, hearly] at hle
      exact not_le_of_gt hsecond hle
    simp only [hnotFirst, hnotSecond, and_false]
  · have hiClock (reply : WithTop ℝ) :
        responseClock C who reply sample i = C.collapseClock (sample ⟨i, hi⟩) := by
      simp only [responseClock, dite_eq_right hi]
    simp only [hiClock]
    apply and_congr_right
    intro _
    constructor
    · intro h j
      by_cases hj : j = who
      · subst j
        rw [hwho]
        have hle := h early.val
        rw [hearly] at hle
        exact hle.trans hsecond.le
      · simpa only [responseClock, dite_eq_right hj] using h j
    · intro h j
      by_cases hj : j = who
      · subst j
        rw [hwho]
        have hle := h early.val
        rw [hearly] at hle
        exact hle.trans hfirst.le
      · simpa only [responseClock, dite_eq_right hj] using h j

/-- Every reward observable has the same upper response kernel, including literal Never. -/
theorem responsePayoffKernel_eq_of_opponent_lt_both
    (C : Calendar) (who : ι) (sample : {j : ι // j ≠ who} → unitInterval)
    (first second : WithTop ℝ) (early : {j : ι // j ≠ who})
    (hfirst : C.collapseClock (sample early) < first)
    (hsecond : C.collapseClock (sample early) < second) (reward : Finset ι → ℝ) :
    responsePayoffKernel C who first reward sample =
      responsePayoffKernel C who second reward sample := by
  exact congrArg reward (responseLabels_eq_of_opponent_lt_both
    C who sample first second early hfirst hsecond)

end MathUE.MarkedCalendar

open Set GameTheory.Math.Probability
open scoped BigOperators

namespace GameTheory.MarkedCalendarChart

private theorem expect_signed_product_eq_mul_of_zero_off_late
    {κ : Type*} [Fintype κ] {A : κ → Type*} [∀ i, Fintype (A i)]
    (laws : ∀ i, FinDist (A i)) (events : ∀ i, Set (A i))
    (hmass : ∀ i, 0 < (laws i).probOf (events i)) (parameters : κ → ℝ)
    (hlegal : ∀ i, |parameters i| ≤ (laws i).signedCondRadius (events i))
    (test : (∀ i, A i) → ℝ)
    (hzero : ∀ sample, (∃ i, sample i ∉ events i) → test sample = 0) :
    (FinDist.pi (fun i => (laws i).signedCond (events i) (hmass i)
      (parameters i) (hlegal i))).expect test =
        (∏ i : κ, ((1 - parameters i) + parameters i / (laws i).probOf (events i))) *
          (FinDist.pi laws).expect test := by
  classical
  rw [FinDist.expect_eq_sum, FinDist.expect_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases hlate : ∀ i, sample i ∈ events i
  · simp only [FinDist.prob_pi, FinDist.prob_signedCond, FinDist.signedCondWeight,
      hlate, ite_true]
    rw [Finset.prod_mul_distrib]
    ring
  · have htest := hzero sample (not_forall.mp hlate)
    rw [htest, mul_zero, mul_zero, mul_zero]

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

private def cellMidpointPoint (laws : ι → FinDist (Option ℕ)) (cell : Cell laws) :
    unitInterval :=
  ⟨(left laws cell + right laws cell) / 2, by
    have hleft := left_nonneg laws cell
    have hright := left_lt_right laws cell
    constructor
    · linarith
    · linarith [right_le_one laws cell]⟩

omit [DecidableEq ι] in
private theorem collapseClock_cellMidpointPoint
    (laws : ι → FinDist (Option ℕ)) (cell : Cell laws) :
    (calendar laws).collapseClock (cellMidpointPoint laws cell) = cellMark laws cell := by
  apply collapseClock_of_mem_cellInterior
  · change left laws cell < (left laws cell + right laws cell) / 2
    linarith [left_lt_right laws cell]
  · change (left laws cell + right laws cell) / 2 < right laws cell
    linarith [left_lt_right laws cell]

/-- An original finite or Never reply is evaluated against the literal old cell clocks. -/
def upperCellReplyPayoff (laws : ι → FinDist (Option ℕ)) (who : ι)
    (choice : Option ℕ) (reward : Finset ι → ℝ)
    (sample : {j : ι // j ≠ who} → Cell laws) : ℝ :=
  reward (outcomeLabelsEquiv (quittingFirstStoppingOutcome
    ((Equiv.funSplitAt who (Option ℕ)).symm
      (choice, fun j => originalChoice (sample j)))))

private theorem upperCellReplyPayoff_eq_kernel
    (laws : ι → FinDist (Option ℕ)) (who : ι) (choice : Option ℕ)
    (reward : Finset ι → ℝ) (sample : {j : ι // j ≠ who} → Cell laws) :
    upperCellReplyPayoff laws who choice reward sample =
      MathUE.MarkedCalendar.responsePayoffKernel (calendar laws) who
        (markedClock laws (quittingStoppingTimeValue choice)) reward
        (fun j => cellMidpointPoint laws (sample j)) := by
  rw [upperCellReplyPayoff, MathUE.MarkedCalendar.responsePayoffKernel,
    ← minimumLabels_responseCellClock_eq_originalOutcome laws who choice sample]
  apply congrArg (fun clock => reward (MathUE.MarkedCalendar.minimumLabels clock))
  funext i
  by_cases hi : i = who
  · simp only [Equiv.funSplitAt_symm_apply, MathUE.MarkedCalendar.responseClock,
      dite_eq_left hi]
  · simp only [Equiv.funSplitAt_symm_apply, MathUE.MarkedCalendar.responseClock,
      dite_eq_right hi, collapseClock_cellMidpointPoint]

omit [DecidableEq ι] in
private theorem cellMark_lt_cut_of_notMem_after
    (laws : ι → FinDist (Option ℕ)) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (hcutoff : cut ≤ (cutoff laws : ℝ))
    (cell : Cell laws) (hearly : cell ∉ cellCutEvent laws .after cut) :
    cellMark laws cell < (cut : WithTop ℝ) := by
  have hleft : left laws cell < cut := lt_of_not_ge hearly
  have hfinite : (cell : WithTop ℕ) ≠ ⊤ := by
    intro htop
    exact (not_le_of_gt hleft) (hcutoff.trans_eq (cutoff_eq_left_of_top laws cell htop))
  have hright : right laws cell ≤ cut := by
    rcases (isGap_interval laws cell).2.2.2 cut hcut with h | h
    · exact (not_le_of_gt hleft h).elim
    · exact h
  rw [cellMark, ite_eq_right hfinite]
  exact WithTop.coe_lt_coe.mpr (by linarith)

private theorem upperCellReplyPayoff_eq_of_early_cell
    (laws : ι → FinDist (Option ℕ)) (who : ι) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (hcutoff : cut ≤ (cutoff laws : ℝ))
    (first second : Option ℕ)
    (hfirst : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue first))
    (hsecond : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue second))
    (reward : Finset ι → ℝ) (sample : {j : ι // j ≠ who} → Cell laws)
    (j : {j : ι // j ≠ who}) (hj : sample j ∉ cellCutEvent laws .after cut) :
    upperCellReplyPayoff laws who first reward sample =
      upperCellReplyPayoff laws who second reward sample := by
  have hclock := cellMark_lt_cut_of_notMem_after laws cut hcut hcutoff (sample j) hj
  have hkernel := MathUE.MarkedCalendar.responsePayoffKernel_eq_of_opponent_lt_both
    (calendar laws) who (fun j => cellMidpointPoint laws (sample j))
    _ _ j (by rw [collapseClock_cellMidpointPoint]; exact hclock.trans_le hfirst)
    (by rw [collapseClock_cellMidpointPoint]; exact hclock.trans_le hsecond) reward
  rw [upperCellReplyPayoff_eq_kernel, upperCellReplyPayoff_eq_kernel, hkernel]

/-- The multiplier on every upper response difference is strictly positive, including
mass-one directions whose early complement is empty. -/
theorem signedLate_responseMultiplier_pos
    (laws : ι → FinDist (Option ℕ)) (who : ι) (cut : ℝ)
    (parameters : {j : ι // j ≠ who} → ℝ)
    (hmass : ∀ j : {j : ι // j ≠ who},
      0 < (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
    (hlegal : ∀ j : {j : ι // j ≠ who}, |parameters j| ≤
      (cellLaw laws j.val).signedCondRadius (cellCutEvent laws .after cut)) :
    0 < ∏ j : {j : ι // j ≠ who},
      ((1 - parameters j) + parameters j /
        (cellLaw laws j.val).probOf (cellCutEvent laws .after cut)) := by
  classical
  apply Finset.prod_pos
  intro j _
  have hbound := _root_.Math.Probability.signedConditioningLikelihood_bounds
    _ (hmass j) (FinDist.probOf_le_one _ _) (parameters j) (hlegal j) True
  simp only [ite_true] at hbound
  linarith [hbound.1]

/-- Actual legal signed late-cell laws scale differences between ALL upper original replies
by one positive factor. Never is included, and no early-event positive-mass premise is needed. -/
theorem expect_signedLate_upperCellReplyPayoff_sub
    (laws : ι → FinDist (Option ℕ)) (who : ι) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (hcutoff : cut ≤ (cutoff laws : ℝ))
    (parameters : {j : ι // j ≠ who} → ℝ)
    (hmass : ∀ j : {j : ι // j ≠ who},
      0 < (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
    (hlegal : ∀ j : {j : ι // j ≠ who}, |parameters j| ≤
      (cellLaw laws j.val).signedCondRadius (cellCutEvent laws .after cut))
    (first second : Option ℕ)
    (hfirst : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue first))
    (hsecond : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue second))
    (reward : Finset ι → ℝ) :
    (FinDist.pi (fun j : {j : ι // j ≠ who} =>
      signedCutCellLaw laws .after cut j.val (parameters j))).expect
        (upperCellReplyPayoff laws who first reward) -
      (FinDist.pi (fun j : {j : ι // j ≠ who} =>
        signedCutCellLaw laws .after cut j.val (parameters j))).expect
          (upperCellReplyPayoff laws who second reward) =
    (∏ j : {j : ι // j ≠ who}, ((1 - parameters j) + parameters j /
      (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))) *
      ((FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
        (upperCellReplyPayoff laws who first reward) -
        (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
          (upperCellReplyPayoff laws who second reward)) := by
  classical
  simp only [signedCutCellLaw,
    FinDist.signedCondOrSelf_eq_signedCond _ _ (hmass _) _ (hlegal _)]
  rw [← FinDist.expect_sub, ← FinDist.expect_sub]
  apply expect_signed_product_eq_mul_of_zero_off_late
  intro sample hearly
  obtain ⟨j, hj⟩ := hearly
  rw [upperCellReplyPayoff_eq_of_early_cell laws who cut hcut hcutoff
    first second hfirst hsecond reward sample j hj, sub_self]

/-- One additive constant works for every upper reply, not one separately chosen constant per
test. Its reference reply is literal Never; no unique maximizer is assumed. -/
theorem exists_signedLate_upperCellReplyPayoff_affine
    (laws : ι → FinDist (Option ℕ)) (who : ι) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (hcutoff : cut ≤ (cutoff laws : ℝ))
    (parameters : {j : ι // j ≠ who} → ℝ)
    (hmass : ∀ j : {j : ι // j ≠ who},
      0 < (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
    (hlegal : ∀ j : {j : ι // j ≠ who}, |parameters j| ≤
      (cellLaw laws j.val).signedCondRadius (cellCutEvent laws .after cut))
    (reward : Finset ι → ℝ) :
    ∃ constant : ℝ, ∀ choice : Option ℕ,
      (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue choice) →
      (FinDist.pi (fun j : {j : ι // j ≠ who} =>
        signedCutCellLaw laws .after cut j.val (parameters j))).expect
          (upperCellReplyPayoff laws who choice reward) =
        (∏ j : {j : ι // j ≠ who}, ((1 - parameters j) + parameters j /
          (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))) *
          (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
            (upperCellReplyPayoff laws who choice reward) + constant := by
  let original (choice : Option ℕ) :=
    (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
      (upperCellReplyPayoff laws who choice reward)
  let modified (choice : Option ℕ) :=
    (FinDist.pi (fun j : {j : ι // j ≠ who} =>
      signedCutCellLaw laws .after cut j.val (parameters j))).expect
        (upperCellReplyPayoff laws who choice reward)
  let factor := ∏ j : {j : ι // j ≠ who}, ((1 - parameters j) + parameters j /
    (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
  refine ⟨modified none - factor * original none, ?_⟩
  intro choice hchoice
  have hnever : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue none) := by
    simp only [quittingStoppingTimeValue, markedClock, WithTop.map_top, le_top]
  have h := expect_signedLate_upperCellReplyPayoff_sub laws who cut hcut hcutoff
    parameters hmass hlegal choice none hchoice hnever reward
  change modified choice - modified none = factor * (original choice - original none) at h
  change modified choice = factor * original choice + (modified none - factor * original none)
  linarith

/-- Inactive coordinates remain exactly original, even when their late-event mass is zero. -/
def partialSignedLateCellLaw (laws : ι → FinDist (Option ℕ))
    (active : Finset ι) (cut : ℝ) (parameters : ι → ℝ) (i : ι) : FinDist (Cell laws) :=
  if i ∈ active then signedCutCellLaw laws .after cut i (parameters i) else cellLaw laws i

def partialSignedLateResponseMultiplier (laws : ι → FinDist (Option ℕ))
    (who : ι) (active : Finset ι) (cut : ℝ) (parameters : ι → ℝ) : ℝ :=
  ∏ j : {j : ι // j ≠ who},
    (if j.val ∈ active then (1 - parameters j.val) + parameters j.val /
      (cellLaw laws j.val).probOf (cellCutEvent laws .after cut) else 1)

theorem partialSignedLateResponseMultiplier_pos
    (laws : ι → FinDist (Option ℕ)) (who : ι) (active : Finset ι) (cut : ℝ)
    (parameters : ι → ℝ)
    (hmass : ∀ j : {j : ι // j ≠ who}, j.val ∈ active →
      0 < (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
    (hlegal : ∀ j : {j : ι // j ≠ who}, j.val ∈ active → |parameters j.val| ≤
      (cellLaw laws j.val).signedCondRadius (cellCutEvent laws .after cut)) :
    0 < partialSignedLateResponseMultiplier laws who active cut parameters := by
  classical
  unfold partialSignedLateResponseMultiplier
  apply Finset.prod_pos
  intro j _
  by_cases hj : j.val ∈ active
  · rw [ite_eq_left hj]
    have hb := _root_.Math.Probability.signedConditioningLikelihood_bounds
      _ (hmass j hj) (FinDist.probOf_le_one _ _) (parameters j.val) (hlegal j hj) True
    simp only [ite_true] at hb
    linarith [hb.1]
  · rw [ite_eq_right hj]
    exact zero_lt_one

/-- Partial-active late variations have one positive multiplier and one common constant
before all upper replies. Only active opponents require positive late mass or legality;
the active set and the opponent index may be empty. -/
theorem exists_partialSignedLate_upperCellReplyPayoff_affine
    (laws : ι → FinDist (Option ℕ)) (who : ι) (active : Finset ι) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (hcutoff : cut ≤ (cutoff laws : ℝ))
    (parameters : ι → ℝ)
    (hmass : ∀ j : {j : ι // j ≠ who}, j.val ∈ active →
      0 < (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
    (hlegal : ∀ j : {j : ι // j ≠ who}, j.val ∈ active → |parameters j.val| ≤
      (cellLaw laws j.val).signedCondRadius (cellCutEvent laws .after cut))
    (reward : Finset ι → ℝ) :
    0 < partialSignedLateResponseMultiplier laws who active cut parameters ∧
    ∃ constant : ℝ, ∀ choice : Option ℕ,
      (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue choice) →
      (FinDist.pi (fun j : {j : ι // j ≠ who} =>
        partialSignedLateCellLaw laws active cut parameters j.val)).expect
          (upperCellReplyPayoff laws who choice reward) =
        partialSignedLateResponseMultiplier laws who active cut parameters *
          (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
            (upperCellReplyPayoff laws who choice reward) + constant := by
  classical
  let event (j : {j : ι // j ≠ who}) : Set (Cell laws) :=
    if j.val ∈ active then cellCutEvent laws .after cut else univ
  let parameter (j : {j : ι // j ≠ who}) : ℝ :=
    if j.val ∈ active then parameters j.val else 0
  have huniv (j : {j : ι // j ≠ who}) : (cellLaw laws j.val).probOf univ = 1 := by
    rw [← FinDist.expect_indicator_eq_probOf]
    simp [FinDist.expect_const]
  have he (j : {j : ι // j ≠ who}) : 0 < (cellLaw laws j.val).probOf (event j) := by
    by_cases hj : j.val ∈ active
    · simpa only [event, ite_eq_left hj] using hmass j hj
    · simp only [event, ite_eq_right hj, huniv, zero_lt_one]
  have hp (j : {j : ι // j ≠ who}) :
      |parameter j| ≤ (cellLaw laws j.val).signedCondRadius (event j) := by
    by_cases hj : j.val ∈ active
    · simpa only [event, parameter, ite_eq_left hj] using hlegal j hj
    · simp only [parameter, ite_eq_right hj, abs_zero]
      exact (FinDist.signedCondRadius_pos _ _ (he j)).le
  have hlaw (j : {j : ι // j ≠ who}) :
      (cellLaw laws j.val).signedCond (event j) (he j) (parameter j) (hp j) =
        partialSignedLateCellLaw laws active cut parameters j.val := by
    by_cases hj : j.val ∈ active
    · simp only [event, parameter, partialSignedLateCellLaw, ite_eq_left hj,
        signedCutCellLaw,
        FinDist.signedCondOrSelf_eq_signedCond _ _ (hmass j hj) _ (hlegal j hj)]
    · simp only [partialSignedLateCellLaw, parameter, ite_eq_right hj]
      exact FinDist.signedCond_zero ..
  have hfactor : (∏ j : {j : ι // j ≠ who},
      ((1 - parameter j) + parameter j / (cellLaw laws j.val).probOf (event j))) =
      partialSignedLateResponseMultiplier laws who active cut parameters := by
    unfold partialSignedLateResponseMultiplier
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j.val ∈ active <;> simp [event, parameter, hj]
  let original (choice : Option ℕ) :=
    (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
      (upperCellReplyPayoff laws who choice reward)
  let modified (choice : Option ℕ) :=
    (FinDist.pi (fun j : {j : ι // j ≠ who} =>
      partialSignedLateCellLaw laws active cut parameters j.val)).expect
        (upperCellReplyPayoff laws who choice reward)
  let factor := partialSignedLateResponseMultiplier laws who active cut parameters
  refine ⟨partialSignedLateResponseMultiplier_pos laws who active cut parameters hmass hlegal,
    modified none - factor * original none, ?_⟩
  intro choice hchoice
  have hnever : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue none) := by
    simp only [quittingStoppingTimeValue, markedClock, WithTop.map_top, le_top]
  have hzero (sample : {j : ι // j ≠ who} → Cell laws)
      (hearly : ∃ j, sample j ∉ event j) :
      upperCellReplyPayoff laws who choice reward sample -
        upperCellReplyPayoff laws who none reward sample = 0 := by
    obtain ⟨j, hj⟩ := hearly
    by_cases ha : j.val ∈ active
    · have hcell : sample j ∉ cellCutEvent laws .after cut := by
        simpa only [event, ite_eq_left ha] using hj
      rw [upperCellReplyPayoff_eq_of_early_cell laws who cut hcut hcutoff
        choice none hchoice hnever reward sample j hcell, sub_self]
    · exact (hj (by simp only [event, ite_eq_right ha, mem_univ])).elim
  have h := expect_signed_product_eq_mul_of_zero_off_late
    (fun j : {j : ι // j ≠ who} => cellLaw laws j.val) event he parameter hp
    (fun sample => upperCellReplyPayoff laws who choice reward sample -
      upperCellReplyPayoff laws who none reward sample) hzero
  simp only [hlaw, hfactor, FinDist.expect_sub] at h
  change modified choice - modified none = factor * (original choice - original none) at h
  change modified choice = factor * original choice + (modified none - factor * original none)
  linarith

/-- The partial-active difference identity exposes the same actual multiplier without an
inactive late-mass premise. Both upper tests may be finite or Never. -/
theorem expect_partialSignedLate_upperCellReplyPayoff_sub
    (laws : ι → FinDist (Option ℕ)) (who : ι) (active : Finset ι) (cut : ℝ)
    (hcut : cut ∈ (calendar laws).endpoints) (hcutoff : cut ≤ (cutoff laws : ℝ))
    (parameters : ι → ℝ)
    (hmass : ∀ j : {j : ι // j ≠ who}, j.val ∈ active →
      0 < (cellLaw laws j.val).probOf (cellCutEvent laws .after cut))
    (hlegal : ∀ j : {j : ι // j ≠ who}, j.val ∈ active → |parameters j.val| ≤
      (cellLaw laws j.val).signedCondRadius (cellCutEvent laws .after cut))
    (first second : Option ℕ)
    (hfirst : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue first))
    (hsecond : (cut : WithTop ℝ) ≤ markedClock laws (quittingStoppingTimeValue second))
    (reward : Finset ι → ℝ) :
    (FinDist.pi (fun j : {j : ι // j ≠ who} =>
      partialSignedLateCellLaw laws active cut parameters j.val)).expect
        (upperCellReplyPayoff laws who first reward) -
      (FinDist.pi (fun j : {j : ι // j ≠ who} =>
        partialSignedLateCellLaw laws active cut parameters j.val)).expect
          (upperCellReplyPayoff laws who second reward) =
    partialSignedLateResponseMultiplier laws who active cut parameters *
      ((FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
        (upperCellReplyPayoff laws who first reward) -
        (FinDist.pi (fun j : {j : ι // j ≠ who} => cellLaw laws j.val)).expect
          (upperCellReplyPayoff laws who second reward)) := by
  obtain ⟨_, constant, hconstant⟩ := exists_partialSignedLate_upperCellReplyPayoff_affine
    laws who active cut hcut hcutoff parameters hmass hlegal reward
  rw [hconstant first hfirst, hconstant second hsecond]
  ring

end GameTheory.MarkedCalendarChart
