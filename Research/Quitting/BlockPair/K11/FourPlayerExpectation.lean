import Research.Quitting.BlockPair.K11.ConditionalData

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

theorem expect_pmfPi_fin4_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun c ↦
            expect (sigma 3) fun d ↦ f ![a, b, c, d] := by
  classical
  have h0 : Function.update sigma 0 (sigma 0) = sigma :=
    Function.update_eq_self 0 sigma
  rw [← h0, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 0))
  funext a
  have h1 : Function.update (Function.update sigma 0 (PMF.pure a))
      1 (sigma 1) = Function.update sigma 0 (PMF.pure a) := by
    funext who
    fin_cases who <;> simp
  rw [← h1, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 1))
  funext b
  have h2 : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (sigma 2) =
        Function.update (Function.update sigma 0 (PMF.pure a))
          1 (PMF.pure b) := by
    funext who
    fin_cases who <;> simp
  rw [← h2, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 2))
  funext c
  have h3 : Function.update
      (Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c)) 3 (sigma 3) =
      Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c) := by
    funext who
    fin_cases who <;> simp
  rw [← h3, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 3))
  funext d
  have hpure : Function.update
      (Function.update
        (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
        2 (PMF.pure c)) 3 (PMF.pure d) =
      fun who ↦ PMF.pure (![a, b, c, d] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

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
