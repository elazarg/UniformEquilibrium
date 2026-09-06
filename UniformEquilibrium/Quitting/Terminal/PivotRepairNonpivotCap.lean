import UniformEquilibrium.Quitting.Terminal.PivotRepairExactObjective

/-! # Exact three-endpoint nonpivot cap -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Head responses, Never, the first late date, and the limiting late response. -/
def responderCapCandidateValue (mass : PivotRepairMass input.deadline) (responder : ι) :
    Fin input.deadline ⊕ Fin 3 → ℝ
  | .inl time => input.pureResponsePayoff mass responder (some time.val) responder
  | .inr endpoint => match endpoint with
    | 0 => input.responderNeverEndpoint mass responder
    | 1 => input.responderFirstEndpoint mass responder
    | 2 => input.responderLimitEndpoint mass responder

/-- The full behavioral nonpivot cap is exactly the maximum of the finite
head and three signed endpoints; the limiting endpoint need not be attained. -/
theorem geometric_nonpivot_cap_eq
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : pivotRepairLate mass * hazard = pivotRepairFirstAtom mass)
    (responder : ι) (hne : responder ≠ input.pivot) :
    quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward
          (input.geometricLaws mass hfeasible hazard hpositive hle)) responder =
      Finset.univ.sup' Finset.univ_nonempty (input.responderCapCandidateValue mass responder) := by
  have hpure (choice : Option ℕ) : quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (input.geometricLaws mass hfeasible hazard hpositive hle)
          responder (PMF.pure choice))) responder ≤
      quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward
          (input.geometricLaws mass hfeasible hazard hpositive hle)) responder := by
    rw [quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward _ _ _
  apply le_antisymm
  · apply input.geometric_cap_le_of_endpoints
      mass hfeasible hazard hpositive hle hmatch responder hne
    · intro time
      exact Finset.le_sup' (input.responderCapCandidateValue mass responder)
        (Finset.mem_univ (.inl time))
    · exact Finset.le_sup' (input.responderCapCandidateValue mass responder)
        (Finset.mem_univ (.inr 0))
    · exact Finset.le_sup' (input.responderCapCandidateValue mass responder)
        (Finset.mem_univ (.inr 1))
    · exact Finset.le_sup' (input.responderCapCandidateValue mass responder)
        (Finset.mem_univ (.inr 2))
  · apply Finset.sup'_le
    intro candidate _
    cases candidate with
    | inl time =>
        change input.pureResponsePayoff mass responder (some time.val) responder ≤ _
        rw [← input.geometric_pureResponse_eq_of_head_or_never mass hfeasible hazard hpositive
          hle responder hne (some time.val) (Or.inr ⟨_, time.isLt, rfl⟩) responder]
        exact hpure _
    | inr endpoint =>
        fin_cases endpoint
        · change input.responderNeverEndpoint mass responder ≤ _
          rw [← input.geometric_neverResponse_eq mass hfeasible hazard hpositive hle responder hne]
          exact hpure none
        · change input.responderFirstEndpoint mass responder ≤ _
          rw [← input.geometric_firstResponse_eq mass hfeasible hazard hpositive hle hmatch
            responder hne]
          exact hpure (some input.deadline)
        · change input.responderLimitEndpoint mass responder ≤ _
          rw [← input.geometric_lateLimit_eq mass hfeasible hazard hpositive hle responder hne]
          exact quittingPivotLateLimitValue_le_continuationBestResponseValue reward input.opponents
            input.pivot responder hne input.deadline input.deadline_pos
            (fun j hjp _ ↦ input.opponents_finite j hjp)
            (geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible)
              input.deadline hazard hpositive hle)

end GameTheory.QuittingPivotRepairLPInput
