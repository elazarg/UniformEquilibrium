import MathUE.ProbabilityMassFunction
import MathUE.ProbabilityMassFunction.GeneralTotalVariation

/-! # Conditioning and total variation for arbitrary discrete laws -/

noncomputable section

namespace Math.ProbabilityMassFunction

open Classical in
/-- Real event mass is the sum of the masked real coordinates, without any
finiteness assumption on the sample type. -/
theorem pmfMass_toReal_eq_tsum_mask {Ω : Type*}
    (law : PMF Ω) (event : Ω → Prop) :
    (pmfMass law event).toReal =
      ∑' point, if event point then (law point).toReal else 0 := by
  classical
  rw [pmfMass, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro point
    by_cases hpoint : event point <;> simp [pmfMask, hpoint]
  · intro point
    by_cases hpoint : event point
    · simpa [pmfMask, hpoint] using PMF.apply_ne_top law point
    · simp [pmfMask, hpoint]

theorem pmfMass_complement_toReal_eq_one_sub {Ω : Type*}
    (law : PMF Ω) (event : Ω → Prop) :
    (pmfMass law fun point => ¬event point).toReal =
      1 - (pmfMass law event).toReal := by
  classical
  have htotal : pmfMass law event + pmfMass law (fun point => ¬event point) = 1 := by
    have hpointwise :
        (fun point : Ω => pmfMask law event point +
          pmfMask law (fun other => ¬event other) point) = fun point => law point := by
      funext point
      by_cases hpoint : event point <;> simp [pmfMask, hpoint]
    rw [pmfMass, pmfMass, ← ENNReal.tsum_add, hpointwise, PMF.tsum_coe]
  have hreal := congrArg ENNReal.toReal htotal
  rw [ENNReal.toReal_add (pmfMass_ne_top law event)
    (pmfMass_ne_top law fun point => ¬event point), ENNReal.toReal_one] at hreal
  linarith

end Math.ProbabilityMassFunction

namespace Math.Probability

open ProbabilityMassFunction

/-- Conditioning increases each retained coordinate and discards exactly the
complement event, so its total variation cost equals the discarded mass. -/
theorem pmfGeneralTV_pmfCond_eq {Ω : Type*}
    (law : PMF Ω) (event : Ω → Prop) (hmass : pmfMass law event ≠ 0) :
    pmfGeneralTV law (pmfCond law event hmass) = 1 - (pmfMass law event).toReal := by
  classical
  have hmassPos : 0 < (pmfMass law event).toReal :=
    ENNReal.toReal_pos hmass (pmfMass_ne_top law event)
  have hmassLe : (pmfMass law event).toReal ≤ 1 := by
    have hmassLeOne : pmfMass law event ≤ 1 := by
      simpa only [pmfMass_true] using
        pmfMass_mono law (E := event) (F := fun _ => True) (fun _ _ => trivial)
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top hmassLeOne
  have hoverlap : ∀ point,
      min ((law point).toReal) ((pmfCond law event hmass point).toReal) =
        if event point then (law point).toReal else 0 := by
    intro point
    by_cases hpoint : event point
    · rw [pmfCond_apply]
      simp only [pmfMask, hpoint, ite_true, ENNReal.toReal_div]
      apply min_eq_left
      apply (le_div_iff₀ hmassPos).2
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmassLe
          (ENNReal.toReal_nonneg : 0 ≤ (law point).toReal)
    · simp [pmfCond_apply, pmfMask, hpoint, ENNReal.toReal_nonneg]
  unfold pmfGeneralTV
  simp_rw [hoverlap]
  rw [← pmfMass_toReal_eq_tsum_mask]

theorem pmfGeneralTV_pmfCond_eq_complement {Ω : Type*}
    (law : PMF Ω) (event : Ω → Prop) (hmass : pmfMass law event ≠ 0) :
    pmfGeneralTV law (pmfCond law event hmass) =
      (pmfMass law fun point => ¬event point).toReal := by
  rw [pmfGeneralTV_pmfCond_eq, pmfMass_complement_toReal_eq_one_sub]

end Math.Probability
