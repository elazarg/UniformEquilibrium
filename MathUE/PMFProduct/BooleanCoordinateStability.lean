import MathUE.PMFProduct.TotalVariation

/-! # Boolean-coordinate stability of finite product laws -/

noncomputable section

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

/-- Coordinatewise closeness of probabilities of the Boolean value `true` controls total
variation of their finite product law by cardinality times the common bound. -/
theorem pmfTV_pmfPi_bool_le_card_mul_of_trueProbability_close
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (first second : ι → PMF Bool) {d : ℝ}
    (hclose : ∀ who,
      |(first who true).toReal - (second who true).toReal| ≤ d) :
    pmfTV (pmfPi first) (pmfPi second) ≤ (Fintype.card ι : ℝ) * d := by
  classical
  have hreplace := pmfTV_pmfPi_replaceOn_le_sum first second Finset.univ
  have hsum :
      (∑ who : ι, pmfTV (first who) (second who)) ≤ ∑ _who : ι, d := by
    apply Finset.sum_le_sum
    intro who _
    rw [pmfTV_bool_eq_abs_apply_true]
    exact hclose who
  calc
    pmfTV (pmfPi first) (pmfPi second) ≤
        ∑ who : ι, pmfTV (first who) (second who) := by
      simpa using hreplace
    _ ≤ ∑ _who : ι, d := hsum
    _ = (Fintype.card ι : ℝ) * d := by
      simp [nsmul_eq_mul]

end Math.PMFProduct
