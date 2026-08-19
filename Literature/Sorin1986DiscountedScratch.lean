import Sorin1986EvaluationScratch

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace SequenceForm

/-- A uniform absolute bound for one observer's pure stage payoffs. -/
def payoffAbsBound (G : FiniteStageGame) (observer : G.Player) : ℝ :=
  ∑ a : JointAction G, |G.payoff a observer|

/-- Every pure stage payoff is bounded by `payoffAbsBound`. -/
theorem abs_payoff_le_payoffAbsBound (G : FiniteStageGame)
    (observer : G.Player) (a : JointAction G) :
    |G.payoff a observer| ≤ payoffAbsBound G observer := by
  classical
  unfold payoffAbsBound
  exact Finset.single_le_sum (fun b _ => abs_nonneg (G.payoff b observer))
    (Finset.mem_univ a)

/-- The expected payoff at every stage has the same finite absolute bound. -/
theorem abs_stagePayoff_le (G : FiniteStageGame)
    (profile : RealizationProfile G) (stage : ℕ)
    (observer : G.Player) :
    |stagePayoff G profile stage observer| ≤ payoffAbsBound G observer := by
  classical
  calc
    |stagePayoff G profile stage observer| ≤
        ∑ h : PublicHistory G stage, ∑ a : JointAction G,
          |actionMass profile ⟨stage, h⟩ a * G.payoff a observer| := by
      unfold stagePayoff
      exact (abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun h _ => abs_sum_le_sum_abs _ _
    _ = ∑ h : PublicHistory G stage, ∑ a : JointAction G,
          actionMass profile ⟨stage, h⟩ a * |G.payoff a observer| := by
      apply Fintype.sum_congr
      intro h
      apply Fintype.sum_congr
      intro a
      rw [abs_mul, abs_of_nonneg (actionMass_nonneg profile ⟨stage, h⟩ a)]
    _ ≤ ∑ h : PublicHistory G stage, ∑ a : JointAction G,
          actionMass profile ⟨stage, h⟩ a * payoffAbsBound G observer := by
      gcongr with h a
      exact abs_payoff_le_payoffAbsBound G observer a
    _ = payoffAbsBound G observer := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_stageMass]
      ring

/-- The continuation factor corresponding to the paper's current-stage
weight `λ`. -/
def continuationFactor {G : FiniteStageGame} (lam : G.DiscountRate) : ℝ :=
  1 - lam.1

/-- The continuation factor lies in `[0,1)`. -/
theorem continuationFactor_nonneg {G : FiniteStageGame}
    (lam : G.DiscountRate) : 0 ≤ continuationFactor lam := by
  exact sub_nonneg.mpr lam.2.2

theorem continuationFactor_lt_one {G : FiniteStageGame}
    (lam : G.DiscountRate) : continuationFactor lam < 1 := by
  linarith [lam.2.1]

theorem abs_continuationFactor_lt_one {G : FiniteStageGame}
    (lam : G.DiscountRate) : |continuationFactor lam| < 1 := by
  rw [abs_of_nonneg (continuationFactor_nonneg lam)]
  exact continuationFactor_lt_one lam

/-- Geometric weights in the paper's convention. -/
def discountWeight {G : FiniteStageGame}
    (lam : G.DiscountRate) (stage : ℕ) : ℝ :=
  lam.1 * continuationFactor lam ^ stage

/-- Discounted payoff of a realization-plan profile. -/
def discountedRealizationPayoff (G : FiniteStageGame)
    (lam : G.DiscountRate) (profile : RealizationProfile G) :
    Payoff G.Player :=
  fun observer => ∑' stage : ℕ,
    discountWeight lam stage * stagePayoff G profile stage observer

private theorem summable_discount_powers {G : FiniteStageGame}
    (lam : G.DiscountRate) :
    Summable fun stage : ℕ => continuationFactor lam ^ stage := by
  exact summable_geometric_of_norm_lt_one
    (by simpa [Real.norm_eq_abs] using abs_continuationFactor_lt_one lam)

private theorem summable_discount_bound {G : FiniteStageGame}
    (lam : G.DiscountRate) (C : ℝ) :
    Summable fun stage : ℕ => lam.1 * continuationFactor lam ^ stage * C := by
  simpa [mul_assoc] using
    (summable_discount_powers lam).mul_left (lam.1 * C)

/-- Discounted payoff is continuous on the compact realization-plan space. -/
@[fun_prop] theorem continuous_discountedRealizationPayoff
    (G : FiniteStageGame) (lam : G.DiscountRate)
    (observer : G.Player) :
    Continuous fun profile : RealizationProfile G =>
      discountedRealizationPayoff G lam profile observer := by
  unfold discountedRealizationPayoff
  apply continuous_tsum
  · intro stage
    exact (continuous_stagePayoff G stage observer).const_mul
      (discountWeight lam stage)
  · exact summable_discount_bound lam (payoffAbsBound G observer)
  · intro stage profile
    rw [Real.norm_eq_abs, abs_mul]
    have hw0 : 0 ≤ discountWeight lam stage := by
      exact mul_nonneg lam.2.1.le
        (pow_nonneg (continuationFactor_nonneg lam) _)
    rw [abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left
      (abs_stagePayoff_le G profile stage observer) hw0

private theorem summable_discounted_stagePayoff
    (G : FiniteStageGame) (lam : G.DiscountRate)
    (profile : RealizationProfile G) (observer : G.Player) :
    Summable fun stage : ℕ =>
      discountWeight lam stage * stagePayoff G profile stage observer := by
  apply Summable.of_norm_bounded (summable_discount_bound lam
    (payoffAbsBound G observer))
  intro stage
  rw [Real.norm_eq_abs, abs_mul]
  have hw0 : 0 ≤ discountWeight lam stage := by
    exact mul_nonneg lam.2.1.le
      (pow_nonneg (continuationFactor_nonneg lam) _)
  rw [abs_of_nonneg hw0]
  exact mul_le_mul_of_nonneg_left
    (abs_stagePayoff_le G profile stage observer) hw0

/-- Discounted payoff is affine in each player's realization plan. -/
theorem discountedRealizationPayoff_update_mix
    (G : FiniteStageGame) (lam : G.DiscountRate)
    (profile : RealizationProfile G) (who : G.Player)
    (x y : RealizationPlan G who) (t : ℝ)
    (observer : G.Player) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    discountedRealizationPayoff G lam
        (Function.update profile who (RealizationPlan.mix t x y)) observer =
      t * discountedRealizationPayoff G lam
          (Function.update profile who x) observer +
        (1 - t) * discountedRealizationPayoff G lam
          (Function.update profile who y) observer := by
  unfold discountedRealizationPayoff
  let fx : ℕ → ℝ := fun stage =>
    discountWeight lam stage *
      stagePayoff G (Function.update profile who x) stage observer
  let fy : ℕ → ℝ := fun stage =>
    discountWeight lam stage *
      stagePayoff G (Function.update profile who y) stage observer
  have hx : Summable fx :=
    summable_discounted_stagePayoff G lam
      (Function.update profile who x) observer
  have hy : Summable fy :=
    summable_discounted_stagePayoff G lam
      (Function.update profile who y) observer
  calc
    ∑' stage : ℕ, discountWeight lam stage *
        stagePayoff G
          (Function.update profile who (RealizationPlan.mix t x y))
          stage observer =
        ∑' stage : ℕ, (t * fx stage + (1 - t) * fy stage) := by
          apply tsum_congr
          intro stage
          rw [stagePayoff_update_mix G profile who x y t observer stage ht0 ht1]
          simp [fx, fy]
          ring
    _ = ∑' stage : ℕ, t * fx stage +
          ∑' stage : ℕ, (1 - t) * fy stage := by
          rw [tsum_add (hx.mul_left t) (hy.mul_left (1 - t))]
    _ = t * ∑' stage : ℕ, fx stage +
          (1 - t) * ∑' stage : ℕ, fy stage := by
          rw [tsum_mul_left, tsum_mul_left]
    _ = _ := rfl

end SequenceForm

end Literature.Sorin1986
