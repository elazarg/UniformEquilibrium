import UniformEquilibrium.Quitting.Terminal.PivotRepairSemanticRealization
import UniformEquilibrium.Quitting.Terminal.PivotRepairPivotCap
import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLPBoundary

/-! # The finite repair objective is actual geometric exploitability -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

private theorem actual_pure_le_cap (laws : ι → PMF (Option ℕ))
    (responder : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update laws responder (PMF.pure choice)))
        responder ≤
      quittingContinuationBestResponseValue reward (quittingStoppingLawProfile reward laws)
        responder := by
  rw [quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
  exact quittingTerminalPayoff_update_le_continuationBestResponseValue reward _ _ _

/-- Head responses and the three literal geometric endpoints bound every
behavioral response, without sign restrictions on any terminal coefficient. -/
theorem geometric_cap_le_of_endpoints
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : pivotRepairLate mass * hazard = pivotRepairFirstAtom mass)
    (responder : ι) (hne : responder ≠ input.pivot) (bound : ℝ)
    (hhead : ∀ time : Fin input.deadline,
      input.pureResponsePayoff mass responder (some time.val) responder ≤ bound)
    (hnever : input.responderNeverEndpoint mass responder ≤ bound)
    (hfirst : input.responderFirstEndpoint mass responder ≤ bound)
    (hlimit : input.responderLimitEndpoint mass responder ≤ bound) :
    quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward
          (input.geometricLaws mass hfeasible hazard hpositive hle)) responder ≤ bound := by
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply csSup_le
  · exact ⟨_, ⟨none, rfl⟩⟩
  · rintro value ⟨choice, rfl⟩
    dsimp only
    rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
    cases choice with
    | none =>
        rw [input.geometric_neverResponse_eq mass hfeasible hazard hpositive hle responder hne]
        exact hnever
    | some time =>
        by_cases htime : time < input.deadline
        · rw [input.geometric_pureResponse_eq_of_head_or_never mass hfeasible hazard
            hpositive hle responder hne (some time) (Or.inr ⟨time, htime, rfl⟩) responder]
          exact hhead ⟨time, htime⟩
        · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (show input.deadline ≤ time by omega)
          rw [input.geometric_lateResponse_eq_affine mass hfeasible hazard hpositive hle
            hmatch responder hne offset]
          have hnonneg : 0 ≤ (1 - hazard) ^ offset := pow_nonneg (by linarith) _
          have hone : (1 - hazard) ^ offset ≤ 1 :=
            pow_le_one₀ (by linarith) (by linarith)
          nlinarith [mul_le_mul_of_nonneg_left hfirst hnonneg,
            mul_le_mul_of_nonneg_left hlimit (sub_nonneg.mpr hone)]

/-- Whenever the geometric first atom matches the feasible LP coordinate,
the finite objective equals full behavioral terminal exploitability. -/
theorem geometric_exploitability_eq_objective
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (hmatch : pivotRepairLate mass * hazard = pivotRepairFirstAtom mass) :
    letI : Nonempty ι := ⟨input.pivot⟩
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward
          (input.geometricLaws mass hfeasible hazard hpositive hle)) = input.objective mass := by
  letI : Nonempty ι := ⟨input.pivot⟩
  let profile := quittingStoppingLawProfile reward
    (input.geometricLaws mass hfeasible hazard hpositive hle)
  have hpayoff (who : ι) : quittingTerminalPayoff reward profile who =
      input.prescribedPayoff mass who :=
    input.geometric_payoff_eq_prescribedPayoff mass hfeasible hazard hpositive hle who
  have hpivot : quittingContinuationBestResponseValue reward profile input.pivot =
      input.pivotCap :=
    (input.pivotCap_eq_continuationBestResponseValue _).symm
  have hconstraint (index : input.ConstraintIndex) :
      input.constraintGain mass index ≤ input.objective mass :=
    Finset.le_sup' (input.constraintGain mass) (Finset.mem_univ index)
  have hdebt (who : ι) :
      quittingContinuationBestResponseValue reward profile who -
        input.prescribedPayoff mass who ≤ quittingTerminalExploitability reward profile := by
    rw [← hpayoff]
    exact quittingTerminalDeviationDebt_le_exploitability reward profile who
  apply le_antisymm
  · change quittingTerminalExploitability reward profile ≤ _
    unfold quittingTerminalExploitability
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    apply max_le (input.objective_nonneg mass)
    rw [hpayoff]
    by_cases hwho : who = input.pivot
    · subst who
      rw [hpivot]
      exact hconstraint (.inr (.inl ()))
    · have hcap := input.geometric_cap_le_of_endpoints mass hfeasible hazard hpositive hle
        hmatch who hwho (input.prescribedPayoff mass who + input.objective mass)
        (fun time ↦ by
          have h := hconstraint (.inr (.inr (⟨who, hwho⟩, .inl time)))
          change input.pureResponsePayoff mass who (some time.val) who -
            input.prescribedPayoff mass who ≤ _ at h
          linarith)
        (by
          have h := hconstraint (.inr (.inr (⟨who, hwho⟩, .inr 0)))
          change input.responderNeverEndpoint mass who -
            input.prescribedPayoff mass who ≤ _ at h
          linarith)
        (by
          have h := hconstraint (.inr (.inr (⟨who, hwho⟩, .inr 1)))
          change input.responderFirstEndpoint mass who -
            input.prescribedPayoff mass who ≤ _ at h
          linarith)
        (by
          have h := hconstraint (.inr (.inr (⟨who, hwho⟩, .inr 2)))
          change input.responderLimitEndpoint mass who -
            input.prescribedPayoff mass who ≤ _ at h
          linarith)
      exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hcap)
  · change input.objective mass ≤ quittingTerminalExploitability reward profile
    unfold objective
    apply Finset.sup'_le
    intro index _
    rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
    · exact quittingTerminalExploitability_nonneg reward profile
    · change input.pivotCap - input.prescribedPayoff mass input.pivot ≤ _
      rw [← hpivot]
      exact hdebt input.pivot
    · change input.pureResponsePayoff mass responder (some time.val) responder -
        input.prescribedPayoff mass responder ≤ _
      rw [← input.geometric_pureResponse_eq_of_head_or_never mass hfeasible hazard hpositive
        hle responder responder.property (some time.val) (Or.inr ⟨_, time.isLt, rfl⟩) responder]
      exact (sub_le_sub_right (actual_pure_le_cap _ _ _) _).trans (hdebt responder)
    · fin_cases endpoint
      · change input.responderNeverEndpoint mass responder -
          input.prescribedPayoff mass responder ≤ _
        rw [← input.geometric_neverResponse_eq mass hfeasible hazard hpositive hle
          responder responder.property]
        exact (sub_le_sub_right (actual_pure_le_cap _ _ _) _).trans (hdebt responder)
      · change input.responderFirstEndpoint mass responder -
          input.prescribedPayoff mass responder ≤ _
        rw [← input.geometric_firstResponse_eq mass hfeasible hazard hpositive hle hmatch
          responder responder.property]
        exact (sub_le_sub_right (actual_pure_le_cap _ _ _) _).trans (hdebt responder)
      · change input.responderLimitEndpoint mass responder -
          input.prescribedPayoff mass responder ≤ _
        rw [← input.geometric_lateLimit_eq mass hfeasible hazard hpositive hle
          responder responder.property]
        have h := quittingPivotLateLimitValue_le_continuationBestResponseValue reward
          input.opponents input.pivot responder responder.property input.deadline
          input.deadline_pos (fun j hjp _ ↦ input.opponents_finite j hjp)
          (geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible)
            input.deadline hazard hpositive hle)
        exact (sub_le_sub_right h _).trans (hdebt responder)

end GameTheory.QuittingPivotRepairLPInput
