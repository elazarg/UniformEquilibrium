/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability

/-!
# Total Variation Distance for Finite PMFs

This file promotes the positive-variation quantity from `Math.Probability` to a
compositional distance API. For probability mass functions it is the usual
half-`L¹` total variation distance.

## Main definitions

* `pmfTV` — total variation distance between finite PMFs
* `pmfTVChain` — accumulated distance through a list of intermediate laws

## Main results

* `pmfTV_eq_zero_iff` — identity of indiscernibles
* `pmfTV_symm` / `pmfTV_triangle` — symmetry and triangle inequality
* `pmfTV_map_le` — deterministic data processing
* `pmfTV_bind_le` — Markov-kernel data processing
* `pmfTV_le_chain` — finite hybrid-chain bound
-/

namespace Math
namespace Probability

/-- Total variation distance between two PMFs on a finite type. -/
noncomputable abbrev pmfTV {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) : ℝ :=
  pmfPositiveVariation μ ν

theorem pmfTV_nonneg {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    0 ≤ pmfTV μ ν :=
  pmfPositiveVariation_nonneg μ ν

theorem pmfTV_le_one {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTV μ ν ≤ 1 := by
  change (∑ ω : Ω, max ((μ ω).toReal - (ν ω).toReal) 0) ≤ 1
  calc
    (∑ ω : Ω, max ((μ ω).toReal - (ν ω).toReal) 0)
        ≤ ∑ ω : Ω, (μ ω).toReal := by
          apply Finset.sum_le_sum
          intro ω _
          exact max_le
            (by
              have hν : 0 ≤ (ν ω).toReal := ENNReal.toReal_nonneg
              linarith)
            (show 0 ≤ (μ ω).toReal from ENNReal.toReal_nonneg)
    _ = 1 := pmf_toReal_sum_one μ

@[simp] theorem pmfTV_self {Ω : Type*} [Fintype Ω] (μ : PMF Ω) :
    pmfTV μ μ = 0 := by
  change pmfPositiveVariation μ μ = 0
  rw [pmfPositiveVariation_eq_half_sum_abs]
  simp

theorem pmfTV_symm {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTV μ ν = pmfTV ν μ := by
  change pmfPositiveVariation μ ν = pmfPositiveVariation ν μ
  rw [pmfPositiveVariation_eq_half_sum_abs,
    pmfPositiveVariation_eq_half_sum_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  exact abs_sub_comm (μ ω).toReal (ν ω).toReal

/-- On `Bool`, total variation is the absolute displacement of either one
coordinate. -/
theorem pmfTV_bool_eq_abs_apply_true (μ ν : PMF Bool) :
    pmfTV μ ν = |(μ true).toReal - (ν true).toReal| := by
  change pmfPositiveVariation μ ν = _
  rw [pmfPositiveVariation_eq_half_sum_abs, Fintype.sum_bool]
  have hμ := pmf_toReal_sum_one μ
  have hν := pmf_toReal_sum_one ν
  simp only [Fintype.sum_bool] at hμ hν
  have hfalse :
      (μ false).toReal - (ν false).toReal =
        -((μ true).toReal - (ν true).toReal) := by
    linarith
  rw [hfalse, abs_neg]
  ring

@[simp] theorem pmfTV_eq_zero_iff {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTV μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    change pmfPositiveVariation μ ν = 0 at h
    have hsum :
        (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal|) = 0 := by
      have hhalf :
          (1 / 2 : ℝ) * ∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal| = 0 := by
        rw [← pmfPositiveVariation_eq_half_sum_abs]
        exact h
      nlinarith
    ext ω
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top μ ω) (PMF.apply_ne_top ν ω)).1
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => abs_nonneg ((μ x).toReal - (ν x).toReal))).mp hsum
        ω (Finset.mem_univ ω)
  · rintro rfl
    exact pmfTV_self μ

theorem pmfTV_triangle {Ω : Type*} [Fintype Ω] (μ ν ρ : PMF Ω) :
    pmfTV μ ρ ≤ pmfTV μ ν + pmfTV ν ρ := by
  change pmfPositiveVariation μ ρ ≤
    pmfPositiveVariation μ ν + pmfPositiveVariation ν ρ
  rw [pmfPositiveVariation_eq_half_sum_abs,
    pmfPositiveVariation_eq_half_sum_abs,
    pmfPositiveVariation_eq_half_sum_abs]
  have hsum :
      (∑ ω : Ω, |(μ ω).toReal - (ρ ω).toReal|) ≤
        (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal|) +
          ∑ ω : Ω, |(ν ω).toReal - (ρ ω).toReal| := by
    calc
      (∑ ω : Ω, |(μ ω).toReal - (ρ ω).toReal|)
          ≤ ∑ ω : Ω,
              (|(μ ω).toReal - (ν ω).toReal| +
                |(ν ω).toReal - (ρ ω).toReal|) := by
            apply Finset.sum_le_sum
            intro ω _
            exact abs_sub_le (μ ω).toReal (ν ω).toReal (ρ ω).toReal
      _ = (∑ ω : Ω, |(μ ω).toReal - (ν ω).toReal|) +
            ∑ ω : Ω, |(ν ω).toReal - (ρ ω).toReal| :=
        Finset.sum_add_distrib
  nlinarith

theorem pmfTV_map_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (μ ν : PMF α) :
    pmfTV (μ.map f) (ν.map f) ≤ pmfTV μ ν := by
  let w : β → ℝ := pmfPositiveVariationWitness (μ.map f) (ν.map f) 1
  change pmfPositiveVariation (μ.map f) (ν.map f) ≤ pmfPositiveVariation μ ν
  calc
    pmfPositiveVariation (μ.map f) (ν.map f)
        = expect (μ.map f) w - expect (ν.map f) w := by
          symm
          simpa [w] using
            expect_sub_pmfPositiveVariationWitness (μ.map f) (ν.map f) 1
    _ = expect μ (w ∘ f) - expect ν (w ∘ f) := by
      rw [expect_map, expect_map]
      rfl
    _ ≤ 1 * pmfPositiveVariation μ ν := by
      apply expect_sub_le_mul_pmfPositiveVariation
      · intro a
        exact pmfPositiveVariationWitness_nonneg
          (μ.map f) (ν.map f) zero_le_one (f a)
      · intro a
        exact pmfPositiveVariationWitness_le
          (μ.map f) (ν.map f) zero_le_one (f a)
    _ = pmfPositiveVariation μ ν := one_mul _

theorem pmfTV_bind_le {α β : Type*} [Fintype α] [Fintype β]
    (k : α → PMF β) (μ ν : PMF α) :
    pmfTV (μ.bind k) (ν.bind k) ≤ pmfTV μ ν := by
  let w : β → ℝ := pmfPositiveVariationWitness (μ.bind k) (ν.bind k) 1
  let g : α → ℝ := fun a => expect (k a) w
  change pmfPositiveVariation (μ.bind k) (ν.bind k) ≤ pmfPositiveVariation μ ν
  calc
    pmfPositiveVariation (μ.bind k) (ν.bind k)
        = expect (μ.bind k) w - expect (ν.bind k) w := by
          symm
          simpa [w] using
            expect_sub_pmfPositiveVariationWitness (μ.bind k) (ν.bind k) 1
    _ = expect μ g - expect ν g := by
      rw [expect_bind, expect_bind]
    _ ≤ 1 * pmfPositiveVariation μ ν := by
      apply expect_sub_le_mul_pmfPositiveVariation
      · intro a
        apply expect_nonneg
        intro b
        exact pmfPositiveVariationWitness_nonneg
          (μ.bind k) (ν.bind k) zero_le_one b
      · intro a
        have hle := expect_mono (k a) w (fun _ => 1) (fun b =>
          pmfPositiveVariationWitness_le
            (μ.bind k) (ν.bind k) zero_le_one b)
        simpa using hle
    _ = pmfPositiveVariation μ ν := one_mul _

/-- On `Bool`, the distance to the point mass at `true` is the mass at
`false`. -/
@[simp] theorem pmfTV_pure_true (marginal : PMF Bool) :
    pmfTV marginal (PMF.pure true) = (marginal false).toReal := by
  have htrue : (marginal true).toReal ≤ 1 := by
    simpa using
      ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one marginal true)
  change (∑ action : Bool,
      max ((marginal action).toReal -
        ((PMF.pure true : PMF Bool) action).toReal) 0) = _
  rw [Fintype.sum_bool]
  simp only [PMF.pure_apply, Bool.false_eq_true, ↓reduceIte]
  norm_num
  exact htrue

/-- Sum of total-variation distances through a finite list of intermediate
laws. The empty list is the direct distance between the endpoints. -/
noncomputable def pmfTVChain {Ω : Type*} [Fintype Ω] :
    PMF Ω → List (PMF Ω) → PMF Ω → ℝ
  | μ, [], ν => pmfTV μ ν
  | μ, ρ :: rest, ν => pmfTV μ ρ + pmfTVChain ρ rest ν

@[simp] theorem pmfTVChain_nil {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) :
    pmfTVChain μ [] ν = pmfTV μ ν := rfl

@[simp] theorem pmfTVChain_cons {Ω : Type*} [Fintype Ω]
    (μ ρ ν : PMF Ω) (rest : List (PMF Ω)) :
    pmfTVChain μ (ρ :: rest) ν = pmfTV μ ρ + pmfTVChain ρ rest ν := rfl

theorem pmfTV_le_chain {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (intermediates : List (PMF Ω)) :
    pmfTV μ ν ≤ pmfTVChain μ intermediates ν := by
  induction intermediates generalizing μ with
  | nil => exact le_rfl
  | cons ρ rest ih =>
      calc
        pmfTV μ ν ≤ pmfTV μ ρ + pmfTV ρ ν := pmfTV_triangle μ ρ ν
        _ ≤ pmfTV μ ρ + pmfTVChain ρ rest ν :=
          add_le_add (le_refl _) (ih ρ)
        _ = pmfTVChain μ (ρ :: rest) ν := rfl

theorem abs_expect_sub_le_range_mul_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (f : Ω → ℝ) {L U : ℝ}
    (hf_lower : ∀ ω, L ≤ f ω) (hf_upper : ∀ ω, f ω ≤ U) :
    |expect μ f - expect ν f| ≤ (U - L) * pmfTV μ ν := by
  have hshift (d : PMF Ω) :
      expect d (fun ω => f ω - L) = expect d f - L := by
    rw [expect_sub, expect_const]
  have hforward := expect_sub_le_mul_pmfPositiveVariation
    μ ν (fun ω => f ω - L) (U := U - L)
    (fun ω => by linarith [hf_lower ω])
    (fun ω => by linarith [hf_upper ω])
  have hreverse := expect_sub_le_mul_pmfPositiveVariation
    ν μ (fun ω => f ω - L) (U := U - L)
    (fun ω => by linarith [hf_lower ω])
    (fun ω => by linarith [hf_upper ω])
  rw [hshift μ, hshift ν] at hforward
  rw [hshift ν, hshift μ] at hreverse
  change expect ν f - L - (expect μ f - L) ≤
    (U - L) * pmfTV ν μ at hreverse
  rw [pmfTV_symm ν μ] at hreverse
  rw [abs_le]
  constructor <;> linarith

/-- If a finite observable has pairwise oscillation at most `C`, changing the
law changes its expectation by at most `C` times total variation. -/
theorem abs_expect_sub_le_pairwise_mul_pmfTV {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (μ ν : PMF Ω) (f : Ω → ℝ) {C : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ C) :
    |expect μ f - expect ν f| ≤ C * pmfTV μ ν := by
  classical
  let values : Finset ℝ := Finset.univ.image f
  have hvalues : values.Nonempty := Finset.univ_nonempty.image f
  let lower := values.min' hvalues
  let upper := values.max' hvalues
  have hrange : ∀ x, lower ≤ f x ∧ f x ≤ upper := by
    intro x
    have hx : f x ∈ values := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    exact ⟨Finset.min'_le values (f x) hx, Finset.le_max' values (f x) hx⟩
  have hwidth : upper - lower ≤ C := by
    have hlower := Finset.min'_mem values hvalues
    have hupper := Finset.max'_mem values hvalues
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hlower
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hupper
    change values.max' hvalues - values.min' hvalues ≤ C
    rw [← hx, ← hy]
    exact (le_abs_self (f y - f x)).trans (hf y x)
  exact (abs_expect_sub_le_range_mul_pmfTV μ ν f
    (fun x => (hrange x).1) (fun x => (hrange x).2)).trans
      (mul_le_mul_of_nonneg_right hwidth (pmfTV_nonneg μ ν))

/-- The oscillation bound need only hold on a common support containing both
laws. Values of the observable outside that support are immaterial. -/
theorem abs_expect_sub_le_pairwise_on_common_support_mul_pmfTV
    {Ω : Type*} [Fintype Ω] (μ ν : PMF Ω) (f : Ω → ℝ)
    (P : Ω → Prop) {C : ℝ}
    (hμ : ∀ x, μ x ≠ 0 → P x) (hν : ∀ x, ν x ≠ 0 → P x)
    (hf : ∀ x, P x → ∀ y, P y → |f x - f y| ≤ C) :
    |expect μ f - expect ν f| ≤ C * pmfTV μ ν := by
  classical
  obtain ⟨base, hbaseSupport⟩ := μ.support_nonempty
  have hbase : P base := hμ base (by simpa [PMF.mem_support_iff] using hbaseSupport)
  let g : Ω → ℝ := fun x => if P x then f x else f base
  have hμeq : expect μ f = expect μ g := by
    rw [expect_eq_sum, expect_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : μ x = 0
    · simp [hx]
    · simp [g, hμ x hx]
  have hνeq : expect ν f = expect ν g := by
    rw [expect_eq_sum, expect_eq_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ν x = 0
    · simp [hx]
    · simp [g, hν x hx]
  rw [hμeq, hνeq]
  letI : Nonempty Ω := ⟨base⟩
  apply abs_expect_sub_le_pairwise_mul_pmfTV
  intro x y
  by_cases hx : P x
  · by_cases hy : P y
    · simpa [g, hx, hy] using hf x hx y hy
    · simpa [g, hx, hy] using hf x hx base hbase
  · by_cases hy : P y
    · rw [abs_sub_comm]
      simpa [g, hx, hy] using hf y hy base hbase
    · simp only [g, hx, hy, ↓reduceIte, sub_self, abs_zero]
      exact (abs_nonneg _).trans (hf base hbase base hbase)

theorem abs_expect_sub_le_two_mul_pmfTV {Ω : Type*} [Fintype Ω]
    (μ ν : PMF Ω) (f : Ω → ℝ) {C : ℝ}
    (hf : ∀ ω, |f ω| ≤ C) :
    |expect μ f - expect ν f| ≤ (2 * C) * pmfTV μ ν := by
  have h := abs_expect_sub_le_range_mul_pmfTV μ ν f
    (L := -C) (U := C)
    (fun ω => (abs_le.mp (hf ω)).1)
    (fun ω => (abs_le.mp (hf ω)).2)
  simpa [show C - -C = 2 * C by ring] using h

end Probability
end Math
