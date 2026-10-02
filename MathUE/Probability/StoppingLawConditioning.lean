import MathUE.ProbabilityMassFunction.ConditioningTotalVariation
import MathUE.Probability.StoppingLawFirstCrossing

/-! # Conditioning a complete clock while retaining its absolute dates -/

noncomputable section

namespace Math.Probability.DiscreteHazard.StoppingLaw

open Math.ProbabilityMassFunction

/-- Survive every date strictly before the cutoff. Never always survives. -/
def survivesUntil (cutoff : ℕ) : Option ℕ → Prop
  | none => True
  | some time => cutoff ≤ time

theorem pmfMass_survivesUntil_toReal (law : PMF (Option ℕ)) (cutoff : ℕ) :
    (pmfMass law (survivesUntil cutoff)).toReal = survival law cutoff := by
  classical
  cases cutoff with
  | zero =>
      have hevent : survivesUntil 0 = fun _ => True := by
        funext choice
        cases choice <;> simp [survivesUntil]
      rw [hevent, pmfMass_true, ENNReal.toReal_one, survival_zero]
  | succ previous =>
      have hevent : (fun choice => ¬survivesUntil (previous + 1) choice) =
          (fun choice => ∃ time ≤ previous, choice = some time) := by
        funext choice
        apply propext
        cases choice <;> simp [survivesUntil]
      have hcomplement :=
        pmfMass_complement_toReal_eq_one_sub law (survivesUntil (previous + 1))
      rw [hevent] at hcomplement
      change stoppingLawCumulativeFiniteMass law previous = _ at hcomplement
      rw [stoppingLawCumulativeFiniteMass_eq_one_sub_survival] at hcomplement
      linarith

theorem pmfMass_survivesUntil_ne_zero (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : 0 < survival law cutoff) :
    pmfMass law (survivesUntil cutoff) ≠ 0 := by
  intro hzero
  have hreal := pmfMass_survivesUntil_toReal law cutoff
  rw [hzero, ENNReal.toReal_zero] at hreal
  linarith

/-- The conditional law remains on absolute dates; it is not shifted to zero. -/
def conditionAt (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : 0 < survival law cutoff) : PMF (Option ℕ) :=
  pmfCond law (survivesUntil cutoff)
    (pmfMass_survivesUntil_ne_zero law cutoff hpositive)

theorem conditionAt_support (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : 0 < survival law cutoff) :
    (conditionAt law cutoff hpositive).support ⊆ {choice | survivesUntil cutoff choice} := by
  intro choice hchoice
  exact pmfCond_ne_zero_implies law (survivesUntil cutoff)
    (pmfMass_survivesUntil_ne_zero law cutoff hpositive)
    (((conditionAt law cutoff hpositive).mem_support_iff choice).mp hchoice)

theorem conditionAt_apply_of_before (law : PMF (Option ℕ)) (cutoff time : ℕ)
    (hpositive : 0 < survival law cutoff) (hbefore : time < cutoff) :
    conditionAt law cutoff hpositive (some time) = 0 := by
  simp [conditionAt, pmfMask, survivesUntil, Nat.not_le.mpr hbefore]

theorem conditionAt_finiteMass (law : PMF (Option ℕ)) (cutoff time : ℕ)
    (hpositive : 0 < survival law cutoff) (htime : cutoff ≤ time) :
    finiteMass (conditionAt law cutoff hpositive) time =
      finiteMass law time / survival law cutoff := by
  simp only [finiteMass, conditionAt, pmfCond_apply, pmfMask,
    survivesUntil, htime, ite_true, ENNReal.toReal_div, pmfMass_survivesUntil_toReal]

theorem conditionAt_none (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : 0 < survival law cutoff) :
    (conditionAt law cutoff hpositive none).toReal =
      (law none).toReal / survival law cutoff := by
  simp [conditionAt, pmfMask, survivesUntil, ENNReal.toReal_div,
    pmfMass_survivesUntil_toReal]

theorem pmfGeneralTV_conditionAt (law : PMF (Option ℕ)) (cutoff : ℕ)
    (hpositive : 0 < survival law cutoff) :
    pmfGeneralTV law (conditionAt law cutoff hpositive) = 1 - survival law cutoff := by
  rw [conditionAt, pmfGeneralTV_pmfCond_eq, pmfMass_survivesUntil_toReal]

end Math.Probability.DiscreteHazard.StoppingLaw
