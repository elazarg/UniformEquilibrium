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
  simp
  have updateMixOff (j : {j // j ≠ who}) :
      Function.update profile who (RealizationPlan.mix t x y) j.1 =
        profile j.1 :=
    Function.update_of_ne j.2
  have updateXOff (j : {j // j ≠ who}) :
      Function.update profile who x j.1 = profile j.1 :=
    Function.update_of_ne j.2
  have updateYOff (j : {j // j ≠ who}) :
      Function.update profile who y j.1 = profile j.1 :=
    Function.update_of_ne j.2
  simp_rw [updateMixOff, updateXOff, updateYOff]
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
  simp_rw [add_mul, mul_assoc]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]

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
