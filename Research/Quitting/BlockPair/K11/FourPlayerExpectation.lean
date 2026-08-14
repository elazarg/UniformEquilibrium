import Research.Quitting.BlockPair.K11.ConditionalData

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

@[simp] theorem vector4_quitters_nonempty (a b c d : Bool) :
    ({who | ![a, b, c, d] who = true} : Finset Player).Nonempty ↔
      a = true ∨ b = true ∨ c = true ∨ d = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all
  · rintro (ha | hb | hc | hd)
    · exact ⟨0, by simp [ha]⟩
    · exact ⟨1, by simp [hb]⟩
    · exact ⟨2, by simp [hc]⟩
    · exact ⟨3, by simp [hd]⟩

end GameTheory.BlockPairK11.ConditionalData
