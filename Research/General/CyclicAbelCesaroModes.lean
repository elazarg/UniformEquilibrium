import Mathlib

/-!
# Cyclic Fourier Abel/Cesàro mode asymmetry

This file formalizes the closed-form claim behind the numerical experiment
`E20` (`experiments/cyclic_fourier_abel_cesaro.py`), described in
`ideas/wild/RepresentationTheory.md` §8: for a slow cyclic kernel
`P_λ = (1 - c*λ) * I + c*λ * C` (`C` the cyclic shift), every nontrivial
Fourier mode `μ(λ) = 1 - c*λ + c*λ*ω` (on the character with value `ω`)
retains a *nonzero* Abel boundary-layer multiplier as `λ ↓ 0`, while its
fixed-policy Cesàro multiplier *vanishes* as the horizon `N → ∞`.  The whole
argument lives on a single complex eigenvalue: no matrices, no general
transition algebra, and no diagonalization machinery is used or claimed.

Nonclaims: this file does **not** formalize the general-game
diagonalization statement (only the single-mode scalar calculation), does
**not** produce a matrix-level statement about `P_λ` or `C` themselves, and
does **not** draw any consequence about retargeting behavior beyond the
Abel/Cesàro asymmetry for one mode.
-/

noncomputable section

namespace Research.CyclicAbelCesaroModes

/-- The slow-kernel Fourier multiplier on the character with value `ω`:
`μ(λ) = 1 - c*λ + c*λ*ω`, i.e. `(1-t) + t*ω` with `t = c*λ`. -/
def mode (c : ℝ) (ω : ℂ) (lam : ℝ) : ℂ :=
  1 - (c : ℂ) * (lam : ℂ) + (c : ℂ) * (lam : ℂ) * ω

/-! ## Strict convexity of the unit disc -/

/-- A unit complex number decomposes into real and imaginary parts summing
(via squares) to `1`. -/
theorem re_sq_add_im_sq_of_norm_one {ω : ℂ} (hω : ‖ω‖ = 1) :
    ω.re * ω.re + ω.im * ω.im = 1 := by
  have h1 : ‖ω‖ ^ 2 = Complex.normSq ω := Complex.sq_norm ω
  rw [Complex.normSq_apply, hω] at h1
  norm_num at h1
  linarith [h1]

/-- A unit complex number has real part at most `1`. -/
theorem re_le_one_of_norm_one {ω : ℂ} (hω : ‖ω‖ = 1) : ω.re ≤ 1 := by
  have h := re_sq_add_im_sq_of_norm_one hω
  nlinarith [mul_self_nonneg ω.im, sq_nonneg (ω.re - 1), h]

/-- A convex combination `(1-t) + t*ω` of `1` and a unit `ω ≠ 1` lies
strictly inside the unit disc for `t ∈ (0,1)`.  This is the geometric heart
of the mode norm bound: the circle is strictly convex. -/
theorem norm_one_sub_add_mul_lt_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {ω : ℂ} (hω : ‖ω‖ = 1) (hω1 : ω ≠ 1) :
    ‖(1 - (t : ℂ)) + (t : ℂ) * ω‖ < 1 := by
  have hnormSqω : ω.re * ω.re + ω.im * ω.im = 1 := re_sq_add_im_sq_of_norm_one hω
  have hre_le : ω.re ≤ 1 := re_le_one_of_norm_one hω
  have hre : ω.re < 1 := by
    rcases hre_le.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hω1
      rw [h] at hnormSqω
      have hsq0 : ω.im * ω.im = 0 := by nlinarith [hnormSqω]
      have him0 : ω.im = 0 := mul_self_eq_zero.mp hsq0
      apply Complex.ext
      · simpa using h
      · simpa using him0
  set z : ℂ := (1 - (t : ℂ)) + (t : ℂ) * ω with hz
  have hzre : z.re = (1 - t) + t * ω.re := by simp [hz]
  have hzim : z.im = t * ω.im := by simp [hz]
  have hsq : ‖z‖ ^ 2 < 1 := by
    have hexpand : Complex.normSq z =
        (1 - t) ^ 2 + 2 * t * (1 - t) * ω.re + t ^ 2 * (ω.re * ω.re + ω.im * ω.im) := by
      rw [Complex.normSq_apply, hzre, hzim]; ring
    rw [Complex.sq_norm z, hexpand, hnormSqω]
    have hcube : 0 < t * (1 - t) * (1 - ω.re) :=
      mul_pos (mul_pos ht0 (sub_pos.mpr ht1)) (sub_pos.mpr hre)
    nlinarith [hcube]
  have hsqrt : Real.sqrt (‖z‖ ^ 2) < Real.sqrt 1 :=
    Real.sqrt_lt_sqrt (sq_nonneg _) hsq
  rwa [Real.sqrt_sq (norm_nonneg z), Real.sqrt_one] at hsqrt

/-- **Mode norm bound.**  For a positive slow-time step with `c*λ < 1`, the
Fourier multiplier `μ(λ)` of a nontrivial character lies strictly inside the
unit disc. -/
theorem norm_mode_lt_one (c : ℝ) (ω : ℂ) (lam : ℝ)
    (hω : ‖ω‖ = 1) (hω1 : ω ≠ 1)
    (hc0 : 0 < c) (hlam0 : 0 < lam) (hlam1 : c * lam < 1) :
    ‖mode c ω lam‖ < 1 := by
  have ht0 : 0 < c * lam := mul_pos hc0 hlam0
  have hcast : mode c ω lam = (1 - ((c * lam : ℝ) : ℂ)) + ((c * lam : ℝ) : ℂ) * ω := by
    simp only [mode]; push_cast; ring
  rw [hcast]
  exact norm_one_sub_add_mul_lt_one ht0 hlam1 hω hω1

/-! ## The Cesàro multiplier vanishes -/

/-- **Cesàro multiplier vanishes.**  For a fixed slow-time step, the
fixed-policy Cesàro average of the mode's powers tends to zero as the
horizon grows: the mode has no persistent Cesàro-average signature. -/
theorem cesaro_mode_tendsto_zero (c : ℝ) (ω : ℂ) (lam : ℝ)
    (hω : ‖ω‖ = 1) (hω1 : ω ≠ 1)
    (hc0 : 0 < c) (hlam0 : 0 < lam) (hlam1 : c * lam < 1) :
    Filter.Tendsto
      (fun N : ℕ => (1 / (N : ℂ)) * ∑ t ∈ Finset.range N, mode c ω lam ^ t)
      Filter.atTop (nhds 0) := by
  set q : ℂ := mode c ω lam with hq
  have hqnorm : ‖q‖ < 1 := norm_mode_lt_one c ω lam hω hω1 hc0 hlam0 hlam1
  set r : ℝ := ‖q‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg q
  have hr1 : r < 1 := hqnorm
  have hsummable : Summable (fun t : ℕ => r ^ t) := summable_geometric_of_lt_one hr0 hr1
  have htsum : ∑' t : ℕ, r ^ t = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hbound : ∀ N : ℕ,
      ‖(1 / (N : ℂ)) * ∑ t ∈ Finset.range N, q ^ t‖ ≤ (1 - r)⁻¹ / (N : ℝ) := by
    intro N
    have hsum_bound : ‖∑ t ∈ Finset.range N, q ^ t‖ ≤ (1 - r)⁻¹ := by
      calc ‖∑ t ∈ Finset.range N, q ^ t‖
          ≤ ∑ t ∈ Finset.range N, ‖q ^ t‖ := norm_sum_le _ _
        _ = ∑ t ∈ Finset.range N, r ^ t := by simp [norm_pow, hr]
        _ ≤ ∑' t : ℕ, r ^ t :=
            Summable.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg hr0 i) hsummable
        _ = (1 - r)⁻¹ := htsum
    calc ‖(1 / (N : ℂ)) * ∑ t ∈ Finset.range N, q ^ t‖
        = ‖(1 / (N : ℂ))‖ * ‖∑ t ∈ Finset.range N, q ^ t‖ := norm_mul _ _
      _ = (1 / (N : ℝ)) * ‖∑ t ∈ Finset.range N, q ^ t‖ := by
          rw [one_div, one_div, norm_inv, Complex.norm_natCast]
      _ ≤ (1 / (N : ℝ)) * (1 - r)⁻¹ :=
          mul_le_mul_of_nonneg_left hsum_bound (by positivity)
      _ = (1 - r)⁻¹ / (N : ℝ) := by ring
  refine squeeze_zero_norm hbound ?_
  have hg : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.div_atTop tendsto_const_nhds hg

/-! ## The Abel multiplier has a nonzero limit -/

/-- Exact algebraic identity behind the Abel-limit computation: factor `λ`
out of `1 - (1-λ)*μ(λ)`. -/
theorem one_sub_mul_mode_eq (c : ℝ) (ω : ℂ) (lam : ℝ) :
    1 - (1 - (lam : ℂ)) * mode c ω lam =
      (lam : ℂ) * ((1 + (c : ℂ) * (1 - ω)) - (lam : ℂ) * ((c : ℂ) * (1 - ω))) := by
  simp only [mode]; ring

/-- The Abel limit's denominator never vanishes: `re(1 + c(1-ω)) ≥ 1 > 0`. -/
theorem one_add_mul_one_sub_ne_zero (c : ℝ) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hc0 : 0 < c) (_hc1 : c ≤ 1) :
    (1 : ℂ) + (c : ℂ) * (1 - ω) ≠ 0 := by
  have hre_le : ω.re ≤ 1 := re_le_one_of_norm_one hω
  intro hzero
  have hre0 : (1 + (c : ℂ) * (1 - ω)).re = 0 := by rw [hzero]; simp
  have hre_eq : 1 + c * (1 - ω.re) = 0 := by
    simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im] using hre0
  nlinarith [mul_nonneg hc0.le (sub_nonneg.mpr hre_le)]

/-- **Abel multiplier's nonzero limit.**  As `λ ↓ 0`, the Abel/resolvent
multiplier of a nontrivial mode converges to `1/(1+c(1-ω))`, a nonzero
value: unlike the Cesàro average, the Abel boundary layer retains a
persistent trace of the mode. -/
theorem abel_mode_tendsto (c : ℝ) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Filter.Tendsto (fun lam : ℝ => (lam : ℂ) / (1 - (1 - (lam : ℂ)) * mode c ω lam))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / (1 + (c : ℂ) * (1 - ω)))) := by
  set A : ℂ := 1 + (c : ℂ) * (1 - ω) with hA
  have hAne : A ≠ 0 := one_add_mul_one_sub_ne_zero c ω hω hc0 hc1
  have hcont : Continuous (fun lam : ℝ => A - (lam : ℂ) * ((c : ℂ) * (1 - ω))) := by fun_prop
  have htendstoA : Filter.Tendsto (fun lam : ℝ => A - (lam : ℂ) * ((c : ℂ) * (1 - ω)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A) := by
    have hcontAt : Filter.Tendsto (fun lam : ℝ => A - (lam : ℂ) * ((c : ℂ) * (1 - ω)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (A - ((0 : ℝ) : ℂ) * ((c : ℂ) * (1 - ω)))) :=
      (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa using hcontAt
  have htendstog :
      Filter.Tendsto (fun lam : ℝ => (1 : ℂ) / (A - (lam : ℂ) * ((c : ℂ) * (1 - ω))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 / A)) :=
    Filter.Tendsto.div tendsto_const_nhds htendstoA hAne
  have heqF :
      (fun lam : ℝ => (1 : ℂ) / (A - (lam : ℂ) * ((c : ℂ) * (1 - ω)))) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun lam : ℝ => (lam : ℂ) / (1 - (1 - (lam : ℂ)) * mode c ω lam)) := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    have hlamne : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)
    rw [one_sub_mul_mode_eq, ← hA]
    field_simp
  exact htendstog.congr' heqF

/-! ## The asymmetry, packaged -/

/-- **Abel/Cesàro mode asymmetry** (E20, closed form).  For any nontrivial
character value `ω` on the cyclic state space, the slow-kernel mode
`μ(λ) = 1-c*λ+c*λ*ω`:

* has a **nonzero** Abel boundary-layer limit `1/(1+c(1-ω))` as `λ ↓ 0`
  (`abel_mode_tendsto`, nonzero by `abel_ne_zero_limit`), while
* its fixed-policy Cesàro average `(1/N) ∑_{t<N} μ(λ)^t` **vanishes** as
  `N → ∞` for every fixed `0 < λ` with `c*λ < 1` (`cesaro_mode_tendsto_zero`).

This is a scalar, single-mode calculation: it does not diagonalize a
general game, does not produce a matrix-level statement about `P_λ` or the
cyclic shift `C`, and does not draw any further retargeting consequence. -/
theorem abel_ne_zero_limit (c : ℝ) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (1 : ℂ) / (1 + (c : ℂ) * (1 - ω)) ≠ 0 :=
  one_div_ne_zero (one_add_mul_one_sub_ne_zero c ω hω hc0 hc1)

end Research.CyclicAbelCesaroModes
