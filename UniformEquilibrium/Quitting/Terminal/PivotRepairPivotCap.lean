import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLP

/-! # Exact fixed-opponent pivot cap in the finite repair LP -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Every late finite pivot date has the displayed signed singleton value. -/
theorem purePivotPayoff_late_eq {time : ℕ} (htime : input.deadline ≤ time) :
    input.purePivotPayoff (some time) input.pivot = input.pivotLatePayoff := by
  rw [purePivotPayoff,
    quittingTerminalPayoff_stoppingLawProfile_late_pure_eq_never_add reward input.opponents
      input.pivot input.deadline input.opponents_finite htime]
  unfold pivotLatePayoff pivotNeverPayoff purePivotPayoff
  ring

/-- The finite pivot candidate maximum is exactly the unrestricted behavioral
cap against the actual fixed finite opponent laws, independently of the
pivot law currently prescribed. -/
theorem pivotCap_eq_continuationBestResponseValue (law : PMF (Option ℕ)) :
    input.pivotCap = quittingContinuationBestResponseValue reward
      (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law))
      input.pivot := by
  have hpure (choice : Option ℕ) : input.purePivotPayoff choice input.pivot ≤
      quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law))
        input.pivot := by
    have h := quittingTerminalPayoff_update_le_continuationBestResponseValue reward
      (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law))
      input.pivot (quittingPureTimeBehaviorStrategy reward input.pivot choice)
    rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at h
    simpa only [Function.update_idem, purePivotPayoff] using h
  apply le_antisymm
  · unfold pivotCap
    apply Finset.sup'_le
    intro candidate _
    cases candidate with
    | inl time => exact hpure (some time.val)
    | inr endpoint =>
        cases endpoint with
        | false => exact hpure none
        | true =>
            change input.pivotLatePayoff ≤ _
            rw [← input.purePivotPayoff_late_eq (time := input.deadline) le_rfl]
            exact hpure (some input.deadline)
  · unfold quittingContinuationBestResponseValue
    rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
    apply csSup_le
    · exact ⟨_, ⟨none, rfl⟩⟩
    · rintro value ⟨choice, rfl⟩
      dsimp only
      rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
      simp only [Function.update_idem]
      change input.purePivotPayoff choice input.pivot ≤ input.pivotCap
      cases choice with
      | none =>
          have h := Finset.le_sup' input.pivotCapCandidateValue
            (Finset.mem_univ (Sum.inr false : Fin input.deadline ⊕ Bool))
          exact h
      | some time =>
          by_cases htime : time < input.deadline
          · have h := Finset.le_sup' input.pivotCapCandidateValue
              (Finset.mem_univ (Sum.inl ⟨time, htime⟩ : Fin input.deadline ⊕ Bool))
            exact h
          · rw [input.purePivotPayoff_late_eq (show input.deadline ≤ time by omega)]
            exact Finset.le_sup' input.pivotCapCandidateValue
              (Finset.mem_univ (Sum.inr true))

end GameTheory.QuittingPivotRepairLPInput
