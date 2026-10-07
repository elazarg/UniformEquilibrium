module

public import MathUE.Complex.HolomorphicInjectiveInverse
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-! # Algebraically controlled boundedization of an actual univalent disk map

Milnor §15.3 reduces unbounded maps to bounded ones by a square root followed
by a fractional linear map. Unlike an arbitrary disk embedding, the producer
here retains the literal algebraic relation needed for landing-fiber transport.
The omitted value is derived from the actual inverse and Liouville's theorem;
the square root and an omitted ball are produced, not supplied.
Source: https://legacy-www.math.harvard.edu/archive/118r_spring_05/docs/milnor.pdf

Null landing fibers and boundary extension are separate results.
-/

public section

noncomputable section

namespace Math.ComplexAnalysis

open Complex Filter Function Metric Set
open scoped Topology

theorem image_disk_ne_univ_of_holomorphic_injOn
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1)) :
    g '' ball 0 1 ≠ univ := by
  intro hsurj
  have hd := differentiableOn_invFunOn_of_holomorphic_injOn isOpen_ball hg hinj
  rw [hsurj, differentiableOn_univ] at hd
  have hbounded : Bornology.IsBounded (range (invFunOn g (ball 0 1))) :=
    isBounded_ball.subset (by
      rintro _ ⟨w, rfl⟩
      have hw : w ∈ g '' ball 0 1 := by rw [hsurj]; exact mem_univ w
      exact invFunOn_mem hw)
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hhalf : (1 / 2 : ℂ) ∈ ball 0 1 := by norm_num [mem_ball_zero_iff]
  have heq := hd.apply_eq_apply_of_bounded hbounded (g 0) (g (1 / 2))
  rw [hinj.leftInvOn_invFunOn hzero, hinj.leftInvOn_invFunOn hhalf] at heq
  norm_num at heq

theorem exists_algebraic_boundedization_of_holomorphic_injOn
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1)) (hinj : InjOn g (ball 0 1)) :
    ∃ (a b : ℂ) (c : ℝ) (F : ℂ → ℂ), 0 < c ∧
      DifferentiableOn ℂ F (ball 0 1) ∧ InjOn F (ball 0 1) ∧
      ∀ z ∈ ball 0 1, F z ≠ 0 ∧ ‖F z‖ < 1 ∧
        g z = a + (b + (c : ℂ) / F z) ^ 2 := by
  obtain ⟨a, ha⟩ := (ne_univ_iff_exists_notMem _).mp
    (image_disk_ne_univ_of_holomorphic_injOn hg hinj)
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hconnected : IsSimplyConnected (ball (0 : ℂ) 1) := by
    let : ContractibleSpace (ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, hzero⟩
    change SimplyConnectedSpace (ball (0 : ℂ) 1)
    infer_instance
  have hnonzero : ∀ z ∈ ball 0 1, g z - a ≠ 0 := by
    intro z hz heq
    exact ha ⟨z, hz, sub_eq_zero.mp heq⟩
  obtain ⟨root, hrootContinuous, hsquare⟩ := Complex.exists_continuousOn_pow_eq
    hconnected isOpen_ball (hg.continuousOn.sub continuousOn_const)
    (by rintro ⟨z, hz, heq⟩; exact hnonzero z hz heq) (by decide : 2 ≠ 0)
  change ∀ z, root z ^ 2 = g z - a at hsquare
  have hrootZero : ∀ z ∈ ball 0 1, root z ≠ 0 := by
    intro z hz heq
    apply hnonzero z hz
    rw [← hsquare z, heq]
    simp
  have hrootDiff : DifferentiableOn ℂ root (ball 0 1) := by
    intro z hz
    have h := (hasDerivAt_pow 2 (root z)).of_comp_left
      (hrootContinuous.continuousAt (isOpen_ball.mem_nhds hz))
      ((hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const a)
      (by simpa using mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) (hrootZero z hz))
      (.of_forall hsquare)
    exact h.differentiableAt.differentiableWithinAt
  have hrootInj : InjOn root (ball 0 1) := by
    intro z hz w hw heq
    apply hinj hz hw
    have := congrArg (fun t : ℂ => t ^ 2) heq
    rw [hsquare, hsquare] at this
    linear_combination this
  have hopen : IsOpen (root '' ball 0 1) := by
    simpa only [range_domRestrict] using
      (isOpenMap_domRestrict_of_holomorphic_injOn isOpen_ball hrootDiff hrootInj).isOpen_range
  have hnear : ∀ᶠ w in 𝓝 (-root 0), -w ∈ root '' ball 0 1 := by
    have h : Tendsto (fun w : ℂ => -w) (𝓝 (-root 0)) (𝓝 (root 0)) := by
      simpa only [neg_neg] using continuous_neg.tendsto (-root 0)
    exact h (hopen.mem_nhds ⟨0, hzero, rfl⟩)
  have hmissing : ∀ᶠ w in 𝓝 (-root 0), w ∉ root '' ball 0 1 := by
    filter_upwards [hnear] with w hw
    rintro ⟨z, hz, rfl⟩
    obtain ⟨v, hv, heq⟩ := hw
    have hvalues : g v = g z := by
      have hsq := congrArg (fun t : ℂ => t ^ 2) heq
      rw [hsquare, neg_sq, hsquare] at hsq
      linear_combination hsq
    have hvz := hinj hv hz hvalues
    subst v
    exact hrootZero z hz (by linear_combination heq / 2)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmissing
  let b : ℂ := -root 0
  let c : ℝ := ε / 2
  have hc : 0 < c := half_pos hε
  have hden (z : ℂ) (hz : z ∈ ball 0 1) : ε ≤ ‖root z - b‖ := by
    by_contra! hlt
    exact hball (by simpa only [mem_ball, dist_eq_norm, b] using hlt) ⟨z, hz, rfl⟩
  have hdenzero (z : ℂ) (hz : z ∈ ball 0 1) : root z - b ≠ 0 :=
    norm_pos_iff.mp (hε.trans_le (hden z hz))
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let F : ℂ → ℂ := fun z => (c : ℂ) / (root z - b)
  refine ⟨a, b, c, F, hc, ?_, ?_, ?_⟩
  · exact (differentiableOn_const (c : ℂ)).div (hrootDiff.sub_const b) hdenzero
  · intro z hz w hw heq
    apply hrootInj hz hw
    have hcancel : root z - b = root w - b := by
      apply inv_injective
      apply mul_left_cancel₀ hcC
      simpa only [F, div_eq_mul_inv] using heq
    linear_combination hcancel
  · intro z hz
    have hFzero : F z ≠ 0 := div_ne_zero hcC (hdenzero z hz)
    refine ⟨hFzero, ?_, ?_⟩
    · change ‖(c : ℂ) / (root z - b)‖ < 1
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
        div_lt_one (hε.trans_le (hden z hz))]
      exact (half_lt_self hε).trans_le (hden z hz)
    · have hrecover : b + (c : ℂ) / F z = root z := by
        dsimp [F]
        field_simp [hcC, hdenzero z hz]
        ring
      rw [hrecover, hsquare]
      ring

end Math.ComplexAnalysis
