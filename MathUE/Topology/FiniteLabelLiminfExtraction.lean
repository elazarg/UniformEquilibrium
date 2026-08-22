/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.Ring

/-!
# Fixed-label extraction for scale-normalized lower limits

The predicate below is the eventual-lower-bound formulation of
`liminf value / scale >= lower`.  It avoids any extended-real coercions and
is stable under strict subsequences.  For finitely many labels, one label
occurs along a strict subsequence and the same lower bound survives there.
-/

noncomputable section

namespace Math

open Filter

/-- Eventual lower bounds arbitrarily below `lower` for a scale-normalized
real sequence. -/
def HasScaleNormalizedLiminfLower
    (value scale : ℕ → ℝ) (lower : ℝ) : Prop :=
  ∀ target, target < lower →
    ∀ᶠ n in atTop, target ≤ value n / scale n

/-- A positive constant-factor lower bound on the numerator scales a
normalized liminf lower bound by the same factor. -/
theorem HasScaleNormalizedLiminfLower.of_factor_le
    {source target scale : ℕ → ℝ} {lower factor : ℝ}
    (hfactor : 0 < factor)
    (hscale : ∀ n, 0 < scale n)
    (hsource : HasScaleNormalizedLiminfLower source scale lower)
    (hle : ∀ n, factor * source n ≤ target n) :
    HasScaleNormalizedLiminfLower target scale (factor * lower) := by
  intro requested hrequested
  have hbelow : requested / factor < lower := by
    exact (div_lt_iff₀ hfactor).2 (by simpa [mul_comm] using hrequested)
  filter_upwards [hsource (requested / factor) hbelow] with n hn
  have hscaled := div_le_div_of_nonneg_right (hle n) (hscale n).le
  have hfactorScale :
      factor * (source n / scale n) ≤ target n / scale n := by
    calc
      factor * (source n / scale n) =
          (factor * source n) / scale n := by ring
      _ ≤ _ := hscaled
  have hrequest : requested ≤ factor * (source n / scale n) := by
    have hrequest' := (div_le_iff₀ hfactor).mp hn
    simpa [mul_comm, mul_left_comm, mul_assoc] using hrequest'
  exact hrequest.trans hfactorScale

/-- A scale-normalized liminf lower bound is inherited by every reindexing
which tends to infinity. -/
theorem HasScaleNormalizedLiminfLower.comp_tendsto_atTop
    {value scale : ℕ → ℝ} {lower : ℝ}
    (h : HasScaleNormalizedLiminfLower value scale lower)
    {subseq : ℕ → ℕ} (hsubseq : Tendsto subseq atTop atTop) :
    HasScaleNormalizedLiminfLower (value ∘ subseq) (scale ∘ subseq) lower := by
  intro target htarget
  simpa [Function.comp_apply] using hsubseq.eventually (h target htarget)

/-- From finitely many labels, extract one fixed label along a strict
subsequence while preserving a scale-normalized liminf lower bound. -/
theorem exists_fixedLabel_subsequence_of_scaleNormalizedLiminfLower
    {Label : Type*} [Finite Label]
    (label : ℕ → Label) (value scale : ℕ → ℝ) (lower : ℝ)
    (hlower : HasScaleNormalizedLiminfLower value scale lower) :
    ∃ fixed : Label, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧ (∀ n, label (subseq n) = fixed) ∧
        HasScaleNormalizedLiminfLower (value ∘ subseq) (scale ∘ subseq) lower := by
  obtain ⟨fixed, hfixedInfinite⟩ := Finite.exists_infinite_fiber label
  have hfrequent : ∃ᶠ n in atTop, label n = fixed := by
    rw [Nat.frequently_atTop_iff_infinite]
    have hinfinite : (label ⁻¹' ({fixed} : Set Label)).Infinite :=
      Set.infinite_coe_iff.mp hfixedInfinite
    convert hinfinite using 1
    ext n
    simp
  obtain ⟨subseq, hsubseq, hfixed⟩ :=
    extraction_of_frequently_atTop hfrequent
  exact ⟨fixed, subseq, hsubseq, hfixed,
    hlower.comp_tendsto_atTop hsubseq.tendsto_atTop⟩

end Math
