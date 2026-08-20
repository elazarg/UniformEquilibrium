import Research.Quitting.BlockPair.K11.ConditionalData
import MathUE.PMFProduct.FiniteFubini

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

theorem expect_quittingHazardCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

end GameTheory.BlockPairK11.ConditionalData
