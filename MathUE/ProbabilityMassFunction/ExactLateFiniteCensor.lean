import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawCensor
import MathUE.ProbabilityMassFunction.MapSupport

/-! # Exact Never increment under finite-tail censoring -/

noncomputable section

namespace Math.Probability

/-- A law supported in the retained prefix has no late finite mass. -/
theorem stoppingLawLateFiniteMass_eq_zero_of_support_prefix
    (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hsupport : law.support ⊆ ↑(stoppingLawFinitePrefix cutoff)) :
    stoppingLawLateFiniteMass law cutoff = 0 := by
  rw [stoppingLawLateFiniteMass_eq_tsum_compl]
  have hzero (choice : ↑((↑(stoppingLawFinitePrefix cutoff) : Set (Option ℕ))ᶜ)) :
      (law choice).toReal = 0 := by
    have h : law choice = 0 := by
      by_contra hnonzero
      exact choice.property (hsupport hnonzero)
    rw [h, ENNReal.toReal_zero]
  simp only [hzero, tsum_zero]

/-- Censoring is the identity whenever all finite support is already retained. -/
theorem censorLateFiniteStoppingLaw_eq_self_of_support_prefix
    (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hsupport : law.support ⊆ ↑(stoppingLawFinitePrefix cutoff)) :
    censorLateFiniteStoppingLaw law cutoff = law := by
  unfold censorLateFiniteStoppingLaw
  calc
    law.map (censorLateFiniteStoppingOutcome cutoff) = law.map id := by
      apply pmf_map_eq_of_eq_on_support
      intro choice hchoice
      have hmem := hsupport hchoice
      cases choice with
      | none => rfl
      | some time =>
          have htime : time ≤ cutoff := (some_mem_stoppingLawFinitePrefix cutoff time).mp hmem
          simp [censorLateFiniteStoppingOutcome, htime]
    _ = law := PMF.map_id law

/-- The retained finite head is unchanged by the actual censor map. -/
theorem stoppingLawFiniteHeadMass_censor_eq (law : PMF (Option ℕ)) (cutoff : ℕ) :
    stoppingLawFiniteHeadMass (censorLateFiniteStoppingLaw law cutoff) cutoff =
      stoppingLawFiniteHeadMass law cutoff := by
  unfold stoppingLawFiniteHeadMass
  apply Finset.sum_congr rfl
  intro time htime
  rw [censorLateFiniteStoppingLaw_apply_some_of_le law
    (show time ≤ cutoff by simpa using htime)]

/-- Exactly the discarded finite mass, and no other mass, is added to Never. -/
theorem censorLateFiniteStoppingLaw_none_toReal_eq (law : PMF (Option ℕ)) (cutoff : ℕ) :
    (censorLateFiniteStoppingLaw law cutoff none).toReal =
      (law none).toReal + stoppingLawLateFiniteMass law cutoff := by
  have htail := stoppingLawLateFiniteMass_eq_zero_of_support_prefix
    (censorLateFiniteStoppingLaw law cutoff) cutoff
    (censorLateFiniteStoppingLaw_support_subset law cutoff)
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead,
    stoppingLawFiniteHeadMass_censor_eq] at htail
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead]
  linarith

end Math.Probability
