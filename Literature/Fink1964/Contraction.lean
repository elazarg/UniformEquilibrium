import Literature.Fink1964.Basic
import MathUE.Finset.SupNonexpansive

/-!
# Fink 1964: contraction lemmas

This file formalizes Lemma 1, Theorem 1, and its two corollaries.  The finite
minimum in Fink's operator is represented as the negative of a finite maximum;
`optimalityOperator_le_mixed` and `exists_mixed_eq_optimalityOperator` show
that this is exactly the minimum over mixed actions used in the paper.
-/

noncomputable section

namespace Literature.Fink1964

open GameTheory
open Math.Probability
open Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

namespace Game

/-- Expected current cost under the deviating mixed action. -/
def currentCostEU (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (s : P.State) : ℝ :=
  expect (pmfPi (Function.update (x s) who y))
    (fun a => P.paddedCostGame.stagePayoff s a who)

/-- Expected continuation value after one transition. -/
def continuationEU (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) : ℝ :=
  expect (pmfPi (Function.update (x s) who y))
    (fun a => expect (P.paddedCostGame.transition s a)
      (fun s' => e s' who))

theorem f_eq_currentCostEU_add_continuationEU
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) :
    P.f x who y e s =
      P.currentCostEU x who y s +
        P.discount who * P.continuationEU x who y e s := by
  unfold f oneStepCost currentCostEU continuationEU
  simp_rw [expect_add, expect_const_mul]

/-- Continuation expectation is nonexpansive in the value vector. -/
theorem abs_continuationEU_sub_le
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e u : P.State → Payoff ι) (s : P.State) :
    |P.continuationEU x who y e s -
        P.continuationEU x who y u s| ≤ dist e u := by
  unfold continuationEU
  rw [← expect_sub]
  refine abs_expect_le_of_abs_le _ _ fun a => ?_
  rw [← expect_sub]
  refine abs_expect_le_of_abs_le _ _ fun s' => ?_
  rw [← Real.dist_eq]
  exact (dist_le_pi_dist (e s') (u s') who).trans
    (dist_le_pi_dist e u s')

/-- Property (b): one coordinate of `f` is `α_h`-Lipschitz in the value
vector. -/
theorem abs_f_sub_le
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e u : P.State → Payoff ι) (s : P.State) :
    |P.f x who y e s - P.f x who y u s| ≤
      P.discount who * dist e u := by
  rw [P.f_eq_currentCostEU_add_continuationEU,
    P.f_eq_currentCostEU_add_continuationEU,
    add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
    abs_of_nonneg (P.discount_nonneg who)]
  exact mul_le_mul_of_nonneg_left
    (P.abs_continuationEU_sub_le x who y e u s)
    (P.discount_nonneg who)

/-- Property (c): `f` is affine in the deviating mixed action. -/
theorem f_eq_expect_pure
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    (x : P.StationaryMixedProfile) (who : ι) (y : PMF (P.Act who))
    (e : P.State → Payoff ι) (s : P.State) :
    P.f x who y e s =
      expect y (fun a => P.f x who (PMF.pure a) e s) := by
  unfold f
  rw [pmfPi_update_bind, expect_bind]

/-- The largest player discount, Fink's common contraction coefficient
`α = max_h α_h`. -/
def maxDiscount (P : Game ι) [Fintype ι] [Nonempty ι] : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty P.discount

theorem discount_le_maxDiscount
    (P : Game ι) [Fintype ι] [Nonempty ι] (who : ι) :
    P.discount who ≤ P.maxDiscount :=
  Finset.le_sup' (f := P.discount) (Finset.mem_univ who)

theorem maxDiscount_nonneg
    (P : Game ι) [Fintype ι] [Nonempty ι] : 0 ≤ P.maxDiscount := by
  obtain ⟨who⟩ := ‹Nonempty ι›
  exact (P.discount_nonneg who).trans (P.discount_le_maxDiscount who)

theorem maxDiscount_lt_one
    (P : Game ι) [Fintype ι] [Nonempty ι] : P.maxDiscount < 1 := by
  simp [maxDiscount, Finset.sup'_lt_iff, P.discount_lt_one]

/-- The largest discount as a nonnegative Lipschitz constant. -/
def maxDiscountNNReal (P : Game ι) [Fintype ι] [Nonempty ι] : ℝ≥0 :=
  ⟨P.maxDiscount, P.maxDiscount_nonneg⟩

theorem maxDiscountNNReal_lt_one
    (P : Game ι) [Fintype ι] [Nonempty ι] :
    P.maxDiscountNNReal < 1 := by
  exact P.maxDiscount_lt_one

/-- The linear evaluation operator for a fixed stationary profile. -/
def valueOperator (P : Game ι) [Fintype ι] [DecidableEq ι]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) :
    P.State → Payoff ι :=
  fun s who => P.f x who (x s who) e s

theorem lipschitzWith_valueOperator
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    (x : P.StationaryMixedProfile) :
    LipschitzWith P.maxDiscountNNReal (P.valueOperator x) := by
  refine LipschitzWith.of_dist_le_mul fun e u => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro s
  rw [dist_pi_le_iff (by positivity)]
  intro who
  rw [Real.dist_eq]
  calc
    |P.valueOperator x e s who - P.valueOperator x u s who|
        ≤ P.discount who * dist e u :=
          P.abs_f_sub_le x who (x s who) e u s
    _ ≤ P.maxDiscount * dist e u :=
      mul_le_mul_of_nonneg_right (P.discount_le_maxDiscount who) dist_nonneg
    _ = (P.maxDiscountNNReal : ℝ) * dist e u := rfl

/-- The fixed-profile operator in Lemma 1 is a contraction. -/
theorem contractingWith_valueOperator
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    (x : P.StationaryMixedProfile) :
    ContractingWith P.maxDiscountNNReal (P.valueOperator x) :=
  ⟨P.maxDiscountNNReal_lt_one, P.lipschitzWith_valueOperator x⟩

/-- Lemma 1: every stationary profile has a unique value vector satisfying
equation (4). -/
theorem existsUnique_valueVector
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    (x : P.StationaryMixedProfile) :
    ∃! e : P.State → Payoff ι, P.IsValueVector x e := by
  letI : Fintype P.State := Fintype.ofFinite P.State
  letI : ∀ i, Fintype (P.Act i) := fun i => Fintype.ofFinite (P.Act i)
  have hc := P.contractingWith_valueOperator x
  let e := ContractingWith.fixedPoint (P.valueOperator x) hc
  refine ⟨e, ?_, ?_⟩
  · intro s who
    exact congrFun (congrFun hc.fixedPoint_isFixedPt s) who
  · intro u hu
    apply hc.fixedPoint_unique
    funext s who
    exact hu s who

/-- Fink's `T_x`: the finite minimum over pure actions, written as the
negative of a finite maximum. -/
def optimalityOperator
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (P.Act i)] [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι) :
    P.State → Payoff ι :=
  fun s who =>
    -Finset.sup' Finset.univ Finset.univ_nonempty
      (fun a : P.Act who => -P.f x who (PMF.pure a) e s)

theorem optimalityOperator_le_pure
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (P.Act i)] [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι)
    (s : P.State) (who : ι) (a : P.Act who) :
    P.optimalityOperator x e s who ≤ P.f x who (PMF.pure a) e s := by
  unfold optimalityOperator
  have h := Finset.le_sup'
    (f := fun a : P.Act who => -P.f x who (PMF.pure a) e s)
    (Finset.mem_univ a)
  linarith

theorem exists_pure_eq_optimalityOperator
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (P.Act i)] [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι)
    (s : P.State) (who : ι) :
    ∃ a : P.Act who,
      P.f x who (PMF.pure a) e s = P.optimalityOperator x e s who := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun a : P.Act who => -P.f x who (PMF.pure a) e s)
  refine ⟨a, ?_⟩
  unfold optimalityOperator
  rw [ha]
  ring

/-- The finite pure minimum is a lower bound for every mixed action. -/
theorem optimalityOperator_le_mixed
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Fintype (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι)
    (s : P.State) (who : ι) (y : PMF (P.Act who)) :
    P.optimalityOperator x e s who ≤ P.f x who y e s := by
  rw [P.f_eq_expect_pure, expect_eq_sum]
  calc
    P.optimalityOperator x e s who =
        ∑ a : P.Act who,
          (y a).toReal * P.optimalityOperator x e s who := by
      rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]
    _ ≤ ∑ a : P.Act who,
          (y a).toReal * P.f x who (PMF.pure a) e s := by
      exact Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left
          (P.optimalityOperator_le_pure x e s who a)
          ENNReal.toReal_nonneg

/-- The minimum over mixed actions is attained by a pure action. -/
theorem exists_mixed_eq_optimalityOperator
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (P.Act i)] [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) (e : P.State → Payoff ι)
    (s : P.State) (who : ι) :
    ∃ y : PMF (P.Act who),
      P.f x who y e s = P.optimalityOperator x e s who := by
  obtain ⟨a, ha⟩ := P.exists_pure_eq_optimalityOperator x e s who
  exact ⟨PMF.pure a, ha⟩

/-- One coordinate of `T_x` has Fink's contraction bound. -/
theorem abs_optimalityOperator_sub_le
    (P : Game ι) [Fintype ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Fintype (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) (e u : P.State → Payoff ι)
    (s : P.State) (who : ι) :
    |P.optimalityOperator x e s who -
        P.optimalityOperator x u s who| ≤
      P.discount who * dist e u := by
  unfold optimalityOperator
  have h := Math.Finset.abs_sup'_sub_sup'_le_const
    (indices := (Finset.univ : Finset (P.Act who)))
    Finset.univ_nonempty
    (fun a => -P.f x who (PMF.pure a) e s)
    (fun a => -P.f x who (PMF.pure a) u s)
    (bound := P.discount who * dist e u)
    (fun a _ => by
      simpa [abs_sub_comm] using
        P.abs_f_sub_le x who (PMF.pure a) e u s)
  simpa [abs_sub_comm] using h

/-- Theorem 1: for every stationary profile `x`, `T_x` is a contraction. -/
theorem lipschitzWith_optimalityOperator
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Fintype (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) :
    LipschitzWith P.maxDiscountNNReal (P.optimalityOperator x) := by
  refine LipschitzWith.of_dist_le_mul fun e u => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro s
  rw [dist_pi_le_iff (by positivity)]
  intro who
  rw [Real.dist_eq]
  calc
    |P.optimalityOperator x e s who - P.optimalityOperator x u s who|
        ≤ P.discount who * dist e u :=
          P.abs_optimalityOperator_sub_le x e u s who
    _ ≤ P.maxDiscount * dist e u :=
      mul_le_mul_of_nonneg_right (P.discount_le_maxDiscount who) dist_nonneg
    _ = (P.maxDiscountNNReal : ℝ) * dist e u := rfl

theorem contractingWith_optimalityOperator
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Fintype (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) :
    ContractingWith P.maxDiscountNNReal (P.optimalityOperator x) :=
  ⟨P.maxDiscountNNReal_lt_one, P.lipschitzWith_optimalityOperator x⟩

/-- Corollary 1: `T_x` has a unique fixed point. -/
theorem existsUnique_fixedPoint_optimalityOperator
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) :
    ∃! e : P.State → Payoff ι, P.optimalityOperator x e = e := by
  letI : Fintype P.State := Fintype.ofFinite P.State
  letI : ∀ i, Fintype (P.Act i) := fun i => Fintype.ofFinite (P.Act i)
  have hc := P.contractingWith_optimalityOperator x
  exact ⟨ContractingWith.fixedPoint (P.optimalityOperator x) hc,
    hc.fixedPoint_isFixedPt,
    fun e he => hc.fixedPoint_unique he⟩

/-- Fink's single-valued map `β(x)`. -/
def beta
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) : P.State → Payoff ι := by
  letI : Fintype P.State := Fintype.ofFinite P.State
  letI : ∀ i, Fintype (P.Act i) := fun i => Fintype.ofFinite (P.Act i)
  exact ContractingWith.fixedPoint (P.optimalityOperator x)
    (P.contractingWith_optimalityOperator x)

theorem optimalityOperator_beta
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Finite (P.Act i)]
    [∀ i, Nonempty (P.Act i)]
    (x : P.StationaryMixedProfile) :
    P.optimalityOperator x (P.beta x) = P.beta x := by
  letI : Fintype P.State := Fintype.ofFinite P.State
  letI : ∀ i, Fintype (P.Act i) := fun i => Fintype.ofFinite (P.Act i)
  exact (P.contractingWith_optimalityOperator x).fixedPoint_isFixedPt

/-- Corollary 2 in its stronger uniform-Lipschitz form. -/
theorem optimalityOperators_uniformly_lipschitz
    (P : Game ι) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Finite P.State] [∀ i, Fintype (P.Act i)]
    [∀ i, Nonempty (P.Act i)] :
    ∀ x : P.StationaryMixedProfile,
      LipschitzWith P.maxDiscountNNReal (P.optimalityOperator x) :=
  fun x => P.lipschitzWith_optimalityOperator x

end Game

end Literature.Fink1964
