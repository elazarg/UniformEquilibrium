import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Real polynomial sign-cell interpolation

Analytic foundations for Cohen-Hormander sign-diagram reconstruction. These
theorems do not construct a quantifier-elimination algorithm.
-/

namespace MathUE.RealSignCell

open Set
open Filter

/-- An increasing continuous cell has an interior root exactly when its endpoint
values straddle zero strictly. Endpoint roots alone do not create an interior root. -/
theorem exists_root_iff_of_strictMonoOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    (∃ x ∈ Ioo a b, f x = 0) ↔ f a < 0 ∧ 0 < f b := by
  constructor
  · rintro ⟨x, hx, hzero⟩
    have hax := hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1
    have hxb := hm (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hab.le) hx.2
    exact ⟨by simpa [hzero] using hax, by simpa [hzero] using hxb⟩
  · intro hsign
    exact intermediate_value_Ioo hab.le hc hsign

/-- A decreasing continuous cell has the reversed endpoint-sign criterion. -/
theorem exists_root_iff_of_strictAntiOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hc : ContinuousOn f (Icc a b)) (hm : StrictAntiOn f (Icc a b)) :
    (∃ x ∈ Ioo a b, f x = 0) ↔ 0 < f a ∧ f b < 0 := by
  constructor
  · rintro ⟨x, hx, hzero⟩
    have hax := hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1
    have hxb := hm (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hab.le) hx.2
    exact ⟨by simpa [hzero] using hax, by simpa [hzero] using hxb⟩
  · intro hsign
    exact intermediate_value_Ioo' hab.le hc ⟨hsign.2, hsign.1⟩

/-- A root in an increasing cell determines every sign on that cell. In particular,
the root is unique, and the two intervals created by its insertion have strict signs. -/
theorem signs_iff_of_strictMonoOn_root {f : ℝ → ℝ} {s : Set ℝ} {c x : ℝ}
    (hm : StrictMonoOn f s) (hc : c ∈ s) (hzero : f c = 0) (hx : x ∈ s) :
    (f x < 0 ↔ x < c) ∧ (f x = 0 ↔ x = c) ∧ (0 < f x ↔ c < x) := by
  constructor
  · simpa only [hzero] using hm.lt_iff_lt hx hc
  constructor
  · simpa only [hzero] using hm.eq_iff_eq hx hc
  · simpa only [hzero] using hm.lt_iff_lt hc hx

/-- A root in a decreasing cell determines every sign on that cell. -/
theorem signs_iff_of_strictAntiOn_root {f : ℝ → ℝ} {s : Set ℝ} {c x : ℝ}
    (hm : StrictAntiOn f s) (hc : c ∈ s) (hzero : f c = 0) (hx : x ∈ s) :
    (f x < 0 ↔ c < x) ∧ (f x = 0 ↔ x = c) ∧ (0 < f x ↔ x < c) := by
  constructor
  · simpa only [hzero] using hm.lt_iff_gt hx hc
  constructor
  · simpa only [hzero, eq_comm] using hm.eq_iff_eq hx hc
  · simpa only [hzero] using hm.lt_iff_gt hc hx

/-- The right unbounded increasing cell has an interior root exactly when its
finite endpoint is negative, provided the function tends to positive infinity. -/
theorem exists_right_root_iff_of_strictMonoOn {f : ℝ → ℝ} {a : ℝ}
    (hc : ContinuousOn f (Ici a)) (hm : StrictMonoOn f (Ici a))
    (hinf : Tendsto f atTop atTop) :
    (∃ x ∈ Ioi a, f x = 0) ↔ f a < 0 := by
  constructor
  · rintro ⟨x, hx, hz⟩
    have hax : a < x := hx
    simpa only [hz] using hm (mem_Ici.mpr (le_refl a)) (mem_Ici.mpr hax.le) hax
  · intro ha
    obtain ⟨b, hab, hb⟩ := ((eventually_gt_atTop a).and
      (hinf (eventually_gt_atTop 0))).exists
    obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo hab.le
      (hc.mono (fun _ hy => hy.1)) ⟨ha, hb⟩
    exact ⟨x, hx.1, hz⟩

/-- The right unbounded decreasing cell has the reversed endpoint criterion. -/
theorem exists_right_root_iff_of_strictAntiOn {f : ℝ → ℝ} {a : ℝ}
    (hc : ContinuousOn f (Ici a)) (hm : StrictAntiOn f (Ici a))
    (hinf : Tendsto f atTop atBot) :
    (∃ x ∈ Ioi a, f x = 0) ↔ 0 < f a := by
  constructor
  · rintro ⟨x, hx, hz⟩
    have hax : a < x := hx
    simpa only [hz] using hm (mem_Ici.mpr (le_refl a)) (mem_Ici.mpr hax.le) hax
  · intro ha
    obtain ⟨b, hab, hb⟩ := ((eventually_gt_atTop a).and
      (hinf (eventually_lt_atBot 0))).exists
    obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo' hab.le
      (hc.mono (fun _ hy => hy.1)) ⟨hb, ha⟩
    exact ⟨x, hx.1, hz⟩

/-- The left unbounded increasing cell has an interior root exactly when its
finite endpoint is positive, provided the function tends to negative infinity. -/
theorem exists_left_root_iff_of_strictMonoOn {f : ℝ → ℝ} {b : ℝ}
    (hc : ContinuousOn f (Iic b)) (hm : StrictMonoOn f (Iic b))
    (hinf : Tendsto f atBot atBot) :
    (∃ x ∈ Iio b, f x = 0) ↔ 0 < f b := by
  constructor
  · rintro ⟨x, hx, hz⟩
    have hxb : x < b := hx
    simpa only [hz] using hm (mem_Iic.mpr hxb.le) (mem_Iic.mpr (le_refl b)) hxb
  · intro hb
    obtain ⟨a, hab, ha⟩ := ((eventually_lt_atBot b).and
      (hinf (eventually_lt_atBot 0))).exists
    obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo hab.le
      (hc.mono (fun _ hy => hy.2)) ⟨ha, hb⟩
    exact ⟨x, hx.2, hz⟩

/-- The left unbounded decreasing cell has the reversed endpoint criterion. -/
theorem exists_left_root_iff_of_strictAntiOn {f : ℝ → ℝ} {b : ℝ}
    (hc : ContinuousOn f (Iic b)) (hm : StrictAntiOn f (Iic b))
    (hinf : Tendsto f atBot atTop) :
    (∃ x ∈ Iio b, f x = 0) ↔ f b < 0 := by
  constructor
  · rintro ⟨x, hx, hz⟩
    have hxb : x < b := hx
    simpa only [hz] using hm (mem_Iic.mpr hxb.le) (mem_Iic.mpr (le_refl b)) hxb
  · intro hb
    obtain ⟨a, hab, ha⟩ := ((eventually_lt_atBot b).and
      (hinf (eventually_gt_atTop 0))).exists
    obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo' hab.le
      (hc.mono (fun _ hy => hy.2)) ⟨hb, ha⟩
    exact ⟨x, hx.2, hz⟩

/-- Strict positivity of the formal polynomial derivative suffices for strict
monotonicity, including both endpoints of a bounded cell. -/
theorem polynomial_strictMonoOn_of_derivative_pos (p : Polynomial ℝ) {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) :
    StrictMonoOn p.eval (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn
  simpa only [interior_Icc, Polynomial.deriv] using hd

/-- Strict negativity of the formal polynomial derivative gives the decreasing case. -/
theorem polynomial_strictAntiOn_of_derivative_neg (p : Polynomial ℝ) {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) :
    StrictAntiOn p.eval (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) p.continuous.continuousOn
  simpa only [interior_Icc, Polynomial.deriv] using hd

/-- Bounded-cell root insertion for a positive derivative: the output identifies
the unique inserted root and all three polynomial signs throughout the old cell. -/
theorem polynomial_exists_increasing_root_split (p : Polynomial ℝ) {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c ∈ Ioo a b, p.eval c = 0 ∧
      ∀ x ∈ Icc a b,
        (p.eval x < 0 ↔ x < c) ∧ (p.eval x = 0 ↔ x = c) ∧
          (0 < p.eval x ↔ c < x) := by
  have hm := polynomial_strictMonoOn_of_derivative_pos p hd
  obtain ⟨c, hc, hz⟩ :=
    (exists_root_iff_of_strictMonoOn hab p.continuous.continuousOn hm).mpr ⟨ha, hb⟩
  exact ⟨c, hc, hz, fun _ hx =>
    signs_iff_of_strictMonoOn_root hm (Ioo_subset_Icc_self hc) hz hx⟩

/-- Bounded-cell root insertion for a negative derivative. -/
theorem polynomial_exists_decreasing_root_split (p : Polynomial ℝ) {a b : ℝ}
    (hab : a < b) (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0)
    (ha : 0 < p.eval a) (hb : p.eval b < 0) :
    ∃ c ∈ Ioo a b, p.eval c = 0 ∧
      ∀ x ∈ Icc a b,
        (p.eval x < 0 ↔ c < x) ∧ (p.eval x = 0 ↔ x = c) ∧
          (0 < p.eval x ↔ x < c) := by
  have hm := polynomial_strictAntiOn_of_derivative_neg p hd
  obtain ⟨c, hc, hz⟩ :=
    (exists_root_iff_of_strictAntiOn hab p.continuous.continuousOn hm).mpr ⟨ha, hb⟩
  exact ⟨c, hc, hz, fun _ hx =>
    signs_iff_of_strictAntiOn_root hm (Ioo_subset_Icc_self hc) hz hx⟩

end MathUE.RealSignCell
