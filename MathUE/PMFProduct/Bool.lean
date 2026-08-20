/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Update

/-!
# Boolean product PMFs

Small closed-form facts for Boolean marginals and two-coordinate Boolean
product distributions, together with the powerset expansion of an expectation
against an independent Boolean product.

`expect_pmfPi_boolFamily_eq_sum_powerset` peels the independent coordinates of
a carrier finset `t` one at a time, holding every coordinate outside `t` fixed
at a default value, and turns the expectation of a function of the joint
Boolean draw into a `Finset.prod_add`-style sum over `t.powerset`: the subset
`J` is the set of coordinates that came up `true`, weighted by the product of
the `true` masses on `J` against the `false` masses on `t \ J`.
`expect_pmfPi_boolFamily_eq_sum_powerset'` is the same identity with the
survival factor written as `1 - (true mass)`.
-/

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

/-- The mass of `false` in a Boolean PMF is one minus the mass of `true`. -/
lemma pmfBool_false_toReal (mu : PMF Bool) :
    (mu false).toReal = 1 - (mu true).toReal := by
  have h := expect_const mu (1 : ℝ)
  rw [expect_eq_sum, Fintype.sum_bool] at h
  norm_num at h ⊢
  linarith

/-- Fubini expansion of a product of two Boolean PMFs. -/
lemma expect_pmfPi_bool (m : Bool → PMF Bool)
    (f : (Bool → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun a ↦
        expect (m true) (fun b ↦ f (fun coordinate ↦
          if coordinate then b else a))) := by
  classical
  have hfalse : Function.update m false (m false) = m :=
    Function.update_eq_self false m
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m false))
  funext a
  have htrue : Function.update (Function.update m false (PMF.pure a))
      true (m true) = Function.update m false (PMF.pure a) := by
    funext coordinate
    cases coordinate <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m true))
  funext b
  have hpure : Function.update (Function.update m false (PMF.pure a))
        true (PMF.pure b) =
      fun coordinate ↦ PMF.pure (if coordinate then b else a) := by
    funext coordinate
    cases coordinate <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- Fubini expansion of a dependent product over the two Boolean coordinates. -/
lemma expect_pmfPi_boolFamily {A : Bool → Type*} [∀ i, Fintype (A i)]
    (m : ∀ i, PMF (A i)) (f : (∀ i, A i) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun a ↦
        expect (m true) (fun b ↦ f (fun i ↦ Bool.rec a b i))) := by
  classical
  have hfalse : Function.update m false (m false) = m :=
    Function.update_eq_self false m
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m false))
  funext a
  have htrue : Function.update (Function.update m false (PMF.pure a))
      true (m true) = Function.update m false (PMF.pure a) := by
    funext coordinate
    cases coordinate <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m true))
  funext b
  have hpure : Function.update (Function.update m false (PMF.pure a))
        true (PMF.pure b) =
      fun coordinate ↦ PMF.pure (Bool.rec a b coordinate) := by
    funext coordinate
    cases coordinate <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-! ## Powerset expansion of a Boolean product expectation -/

/-- **Powerset expansion of a Boolean product expectation.** Peeling the
independent Bernoulli coordinates of a carrier finset `t` one at a time turns
the expectation of a function of the joint Boolean draw into a
`Finset.prod_add`-style sum over the powerset of `t`, weighted by the Bernoulli
mass of the subset that came up `true`, holding the coordinates outside `t`
fixed at the default `rest`. -/
theorem expect_pmfPi_boolFamily_eq_sum_powerset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : Finset ι) (q : ι → PMF Bool)
    (rest : ι → Bool) (k : (ι → Bool) → ℝ) :
    expect (pmfPi (fun i => if i ∈ t then q i else PMF.pure (rest i))) k =
      ∑ J ∈ t.powerset,
        (∏ i ∈ J, (q i true).toReal) * (∏ i ∈ t \ J, (q i false).toReal) *
          k (fun i => if i ∈ J then true else if i ∈ t then false else rest i) := by
  induction t using Finset.induction_on generalizing rest with
  | empty =>
      simp [pmfPi_pure]
  | insert a s ha ih =>
      have hσ : (fun i => if i ∈ insert a s then q i else PMF.pure (rest i)) =
          Function.update (fun i => if i ∈ s then q i else PMF.pure (rest i)) a (q a) := by
        funext i
        by_cases hia : i = a
        · subst hia; simp [ha]
        · simp [hia, Finset.mem_insert]
      rw [hσ, pmfPi_update_bind, expect_bind]
      have hσb : ∀ b : Bool,
          Function.update (fun i => if i ∈ s then q i else PMF.pure (rest i)) a (PMF.pure b) =
            fun i => if i ∈ s then q i else PMF.pure ((Function.update rest a b) i) := by
        intro b
        funext i
        by_cases hia : i = a
        · subst hia; simp [ha]
        · simp [hia]
      simp_rw [hσb, ih]
      -- `rw [add_comm]` below rewrites the *first* `_+_` it finds, which is
      -- the left-hand `f true + f false`; it becomes `f false + f true`,
      -- matching the right-hand `∑ g J + ∑ g (insert a J)` order.
      rw [expect_eq_sum, Fintype.sum_bool, Finset.sum_powerset_insert ha, add_comm]
      congr 1
      · -- the `false` branch: `a` stays out, so the `true` subset is `J`.
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [Finset.mem_powerset] at hJ
        have haJ : a ∉ J := fun h => ha (hJ h)
        have haNotSdiff : a ∉ s \ J := fun h => ha (Finset.mem_sdiff.mp h).1
        have hprodfalse : ∏ i ∈ insert a s \ J, ((q i) false).toReal =
            (q a false).toReal * ∏ i ∈ s \ J, ((q i) false).toReal := by
          have hd : insert a s \ J = insert a (s \ J) := by
            ext i
            by_cases hia : i = a
            · subst hia; simp [ha, haJ]
            · simp [hia, Finset.mem_insert, Finset.mem_sdiff]
          rw [hd, Finset.prod_insert haNotSdiff]
        have hkeq :
            (fun i => if i ∈ J then true else if i ∈ s then false else
                (Function.update rest a false) i) =
            (fun i => if i ∈ J then true else if i ∈ insert a s then false else rest i) := by
          funext i
          by_cases hia : i = a
          · subst hia; simp [haJ, ha]
          · simp [hia, Finset.mem_insert]
        rw [hprodfalse, hkeq]; ring
      · -- the `true` branch: `a` joins the `true` subset, giving `insert a J`.
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [Finset.mem_powerset] at hJ
        have haJ : a ∉ J := fun h => ha (hJ h)
        have hprodtrue : ∏ i ∈ insert a J, ((q i) true).toReal =
            (q a true).toReal * ∏ i ∈ J, ((q i) true).toReal :=
          Finset.prod_insert haJ
        have hd : insert a s \ insert a J = s \ J := by
          ext i
          by_cases hia : i = a
          · subst hia; simp [ha, haJ]
          · simp [hia, Finset.mem_insert, Finset.mem_sdiff]
        have hkeq :
            (fun i => if i ∈ J then true else if i ∈ s then false else
                (Function.update rest a true) i) =
            (fun i => if i ∈ insert a J then true else if i ∈ insert a s then false else
                rest i) := by
          funext i
          by_cases hia : i = a
          · subst hia; simp [haJ, ha]
          · simp [hia, Finset.mem_insert]
        rw [hprodtrue, hd, hkeq]; ring

/-- Restatement of `expect_pmfPi_boolFamily_eq_sum_powerset` with the
complementary factor written as one minus the mass of `true`, the shape
carried by `Math.Finset.bernoulliWeight`. -/
theorem expect_pmfPi_boolFamily_eq_sum_powerset' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : Finset ι) (q : ι → PMF Bool)
    (rest : ι → Bool) (k : (ι → Bool) → ℝ) :
    expect (pmfPi (fun i => if i ∈ t then q i else PMF.pure (rest i))) k =
      ∑ J ∈ t.powerset,
        (∏ i ∈ J, (q i true).toReal) * (∏ i ∈ t \ J, (1 - (q i true).toReal)) *
          k (fun i => if i ∈ J then true else if i ∈ t then false else rest i) := by
  rw [expect_pmfPi_boolFamily_eq_sum_powerset]
  apply Finset.sum_congr rfl
  intro J _
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  rw [pmfBool_false_toReal]

end Math.PMFProduct
