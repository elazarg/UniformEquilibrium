import Sorin1986CompactGameScratch

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace SequenceForm

/-- On its intended domain, clamping leaves a mixing coefficient unchanged. -/
theorem clamp01_eq_of_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    clamp01 t = t := by
  simp [clamp01, ht0, ht1]

/-- Joint realization mass is affine in each player's realization plan. -/
theorem actionMass_update_mix {G : FiniteStageGame}
    (profile : RealizationProfile G) (who : G.Player)
    (x y : RealizationPlan G who) (t : ℝ)
    (h : History G) (a : JointAction G)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    actionMass (Function.update profile who (RealizationPlan.mix t x y)) h a =
      t * actionMass (Function.update profile who x) h a +
        (1 - t) * actionMass (Function.update profile who y) h a := by
  classical
  unfold actionMass actionWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ who]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ who]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ who]
  simp only [Function.update_same]
  have hotherMix :
      (∏ j : {j // j ≠ who},
        ↑((Function.update profile who (RealizationPlan.mix t x y) j.1).1.2 h
          (a j.1))) =
      ∏ j : {j // j ≠ who}, ↑((profile j.1).1.2 h (a j.1)) := by
    apply Fintype.prod_congr
    intro j
    simp [Function.update_noteq j.2]
  have hotherX :
      (∏ j : {j // j ≠ who},
        ↑((Function.update profile who x j.1).1.2 h (a j.1))) =
      ∏ j : {j // j ≠ who}, ↑((profile j.1).1.2 h (a j.1)) := by
    apply Fintype.prod_congr
    intro j
    simp [Function.update_noteq j.2]
  have hotherY :
      (∏ j : {j // j ≠ who},
        ↑((Function.update profile who y j.1).1.2 h (a j.1))) =
      ∏ j : {j // j ≠ who}, ↑((profile j.1).1.2 h (a j.1)) := by
    apply Fintype.prod_congr
    intro j
    simp [Function.update_noteq j.2]
  rw [hotherMix, hotherX, hotherY]
  simp [RealizationPlan.mix, RawRealizationPlan.mix, intervalMix,
    clamp01_eq_of_bounds ht0 ht1]
  ring

/-- Expected payoff at one stage of the public-history repeated game. -/
def stagePayoff (G : FiniteStageGame)
    (profile : RealizationProfile G) (t : ℕ)
    (observer : G.Player) : ℝ :=
  ∑ h : PublicHistory G t, ∑ a : JointAction G,
    actionMass profile ⟨t, h⟩ a * G.payoff a observer

@[fun_prop] theorem continuous_stagePayoff (G : FiniteStageGame)
    (t : ℕ) (observer : G.Player) :
    Continuous fun profile : RealizationProfile G =>
      stagePayoff G profile t observer := by
  classical
  unfold stagePayoff
  fun_prop

/-- Stage payoff is affine in one player's realization plan. -/
theorem stagePayoff_update_mix (G : FiniteStageGame)
    (profile : RealizationProfile G) (who : G.Player)
    (x y : RealizationPlan G who) (t : ℝ)
    (observer : G.Player) (stage : ℕ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    stagePayoff G
        (Function.update profile who (RealizationPlan.mix t x y))
        stage observer =
      t * stagePayoff G (Function.update profile who x) stage observer +
        (1 - t) *
          stagePayoff G (Function.update profile who y) stage observer := by
  classical
  unfold stagePayoff
  simp_rw [actionMass_update_mix profile who x y t _ _ ht0 ht1]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro h _ <;>
    rw [← Finset.mul_sum]

/-- Average payoff through a finite horizon, in realization-plan form. -/
def finiteRealizationPayoff (G : FiniteStageGame) (n : ℕ)
    (profile : RealizationProfile G) : Payoff G.Player :=
  fun observer => (n : ℝ)⁻¹ *
    ∑ stage ∈ Finset.range n, stagePayoff G profile stage observer

@[fun_prop] theorem continuous_finiteRealizationPayoff
    (G : FiniteStageGame) (n : ℕ) (observer : G.Player) :
    Continuous fun profile : RealizationProfile G =>
      finiteRealizationPayoff G n profile observer := by
  classical
  unfold finiteRealizationPayoff
  fun_prop

/-- Finite-horizon payoff is affine in one player's realization plan. -/
theorem finiteRealizationPayoff_update_mix
    (G : FiniteStageGame) (n : ℕ)
    (profile : RealizationProfile G) (who : G.Player)
    (x y : RealizationPlan G who) (t : ℝ)
    (observer : G.Player) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteRealizationPayoff G n
        (Function.update profile who (RealizationPlan.mix t x y)) observer =
      t * finiteRealizationPayoff G n
          (Function.update profile who x) observer +
        (1 - t) * finiteRealizationPayoff G n
          (Function.update profile who y) observer := by
  classical
  unfold finiteRealizationPayoff
  simp_rw [stagePayoff_update_mix G profile who x y t observer _ ht0 ht1]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end SequenceForm

end Literature.Sorin1986
