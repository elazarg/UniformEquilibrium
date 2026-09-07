import MathUE.Polynomial.RealSignCell
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Sign.Basic

/-!
# Polynomial signs at infinity and root-free cells

Polynomial leading terms supply the asymptotic signs used by real sign-diagram
reconstruction. Root-free cells and globally monotone polynomials are treated
without taking limits as additional input hypotheses.
-/

namespace MathUE.RealSignCell

open Filter Set SignType

/-- Executable parity correction of the leading sign at negative infinity. -/
def negativeInfinitySign (degree : ℕ) (leadingSign : SignType) : SignType :=
  if Even degree then leadingSign else -leadingSign

/-- At positive infinity every polynomial eventually has its leading coefficient's sign.
The statement includes zero and constant polynomials. -/
theorem polynomial_eventually_sign_atTop (p : Polynomial ℝ) :
    ∀ᶠ x in atTop, sign (p.eval x) = sign p.leadingCoeff := by
  obtain ⟨factor, hfactor, heq⟩ := p.isEquivalent_atTop_lead.exists_pos_eq_mul
  filter_upwards [hfactor, heq, eventually_gt_atTop (0 : ℝ)] with x hpos hx hxp
  change p.eval x = factor x * (p.leadingCoeff * x ^ p.natDegree) at hx
  rw [hx, sign_mul, sign_pos hpos, one_mul, sign_mul, sign_pow, sign_pos hxp]
  simp

/-- At negative infinity the degree parity corrects the leading coefficient's sign. -/
theorem polynomial_eventually_sign_atBot (p : Polynomial ℝ) :
    ∀ᶠ x in atBot,
      sign (p.eval x) = negativeInfinitySign p.natDegree (sign p.leadingCoeff) := by
  obtain ⟨factor, hfactor, heq⟩ := p.isEquivalent_atBot_lead.exists_pos_eq_mul
  filter_upwards [hfactor, heq, eventually_lt_atBot (0 : ℝ)] with x hpos hx hxn
  change p.eval x = factor x * (p.leadingCoeff * x ^ p.natDegree) at hx
  rw [hx, sign_mul, sign_pos hpos, one_mul, sign_mul, sign_pow, sign_neg hxn]
  simp only [negativeInfinitySign, neg_one_pow_eq_ite]
  split <;> simp_all

/-- Reflection derives the left-end positive-infinity limit from degree and coefficient data. -/
theorem polynomial_tendsto_atBot_atTop (p : Polynomial ℝ) (hdeg : 0 < p.degree)
    (hlead : 0 ≤ p.leadingCoeff * (-1) ^ p.natDegree) : Tendsto p.eval atBot atTop := by
  have h := (p.comp (-Polynomial.X)).tendsto_atTop_of_leadingCoeff_nonneg
    (by simpa using hdeg)
    (by simpa [Polynomial.comp_neg_X_leadingCoeff_eq, mul_comm] using hlead)
  simpa [Function.comp_def] using h.comp tendsto_neg_atBot_atTop

/-- The left-end negative-infinity limit is likewise determined by the reflected leading term. -/
theorem polynomial_tendsto_atBot_atBot (p : Polynomial ℝ) (hdeg : 0 < p.degree)
    (hlead : p.leadingCoeff * (-1) ^ p.natDegree ≤ 0) : Tendsto p.eval atBot atBot := by
  have h := (p.comp (-Polynomial.X)).tendsto_atBot_of_leadingCoeff_nonpos
    (by simpa using hdeg)
    (by simpa [Polynomial.comp_neg_X_leadingCoeff_eq, mul_comm] using hlead)
  simpa [Function.comp_def] using h.comp tendsto_neg_atBot_atTop

/-- A nonconstant polynomial and its derivative have the same leading sign. -/
theorem polynomial_derivative_leading_sign (p : Polynomial ℝ)
    (hdegree : 0 < p.natDegree) : sign p.derivative.leadingCoeff = sign p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_derivative, sign_mul,
    sign_pos (show (0 : ℝ) < p.natDegree from Nat.cast_pos.mpr hdegree), mul_one]

/-- Negative-infinity signs reverse when the positive degree is lowered by one. -/
theorem negativeInfinitySign_sub_one (degree : ℕ) (leadingSign : SignType)
    (hdegree : degree ≠ 0) :
    negativeInfinitySign degree leadingSign =
      -negativeInfinitySign (degree - 1) leadingSign := by
  cases degree with
  | zero => exact False.elim (hdegree rfl)
  | succ degree =>
      by_cases heven : Even degree <;>
        simp [negativeInfinitySign, Nat.even_add_one, heven]

/-- On the far left, the polynomial and its derivative have opposite signs. -/
theorem polynomial_eventually_opposite_derivative_sign_atBot (p : Polynomial ℝ)
    (hdegree : 0 < p.natDegree) :
    ∀ᶠ x in atBot, sign (p.eval x) = -sign (p.derivative.eval x) := by
  filter_upwards [polynomial_eventually_sign_atBot p,
    polynomial_eventually_sign_atBot p.derivative] with x hp hd
  rw [hp, hd, polynomial_derivative_leading_sign p hdegree, Polynomial.natDegree_derivative]
  exact negativeInfinitySign_sub_one p.natDegree (sign p.leadingCoeff) hdegree.ne'

/-- A positive derivative on a right ray forces the polynomial to tend to positive infinity. -/
theorem polynomial_tendsto_atTop_of_right_derivative_pos (p : Polynomial ℝ) {a : ℝ}
    (hd : ∀ x ∈ Ioi a, 0 < p.derivative.eval x) : Tendsto p.eval atTop atTop := by
  have hder : p.derivative ≠ 0 := by
    intro hz
    have hpos := hd (a + 1) (by change a < a + 1; linarith)
    simp only [hz, Polynomial.eval_zero, lt_self_iff_false] at hpos
  have hdegree : 0 < p.natDegree := Nat.pos_of_ne_zero (Polynomial.derivative_ne_zero.mp hder)
  obtain ⟨x, hx, hsign⟩ := ((eventually_gt_atTop a).and
    (polynomial_eventually_sign_atTop p.derivative)).exists
  rw [sign_pos (hd x hx), polynomial_derivative_leading_sign p hdegree] at hsign
  have hlead : 0 < p.leadingCoeff := sign_eq_one_iff.mp hsign.symm
  exact p.tendsto_atTop_of_leadingCoeff_nonneg
    (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree) hlead.le

/-- A negative derivative on a right ray forces the polynomial to tend to negative infinity. -/
theorem polynomial_tendsto_atTop_of_right_derivative_neg (p : Polynomial ℝ) {a : ℝ}
    (hd : ∀ x ∈ Ioi a, p.derivative.eval x < 0) : Tendsto p.eval atTop atBot := by
  have hneg : ∀ x ∈ Ioi a, 0 < (-p).derivative.eval x := by
    intro x hx
    simpa only [Polynomial.derivative_neg, Polynomial.eval_neg, neg_pos] using hd x hx
  have h := polynomial_tendsto_atTop_of_right_derivative_pos (-p) hneg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp h

/-- A positive derivative on a left ray forces a negative-infinity limit there. -/
theorem polynomial_tendsto_atBot_of_left_derivative_pos (p : Polynomial ℝ) {b : ℝ}
    (hd : ∀ x ∈ Iio b, 0 < p.derivative.eval x) : Tendsto p.eval atBot atBot := by
  have hreflect : ∀ x ∈ Ioi (-b), (p.comp (-Polynomial.X)).derivative.eval x < 0 := by
    intro x hx
    have hxb : -x < b := by change -b < x at hx; linarith
    simpa [Polynomial.derivative_comp] using neg_lt_zero.mpr (hd (-x) hxb)
  have h := polynomial_tendsto_atTop_of_right_derivative_neg
    (p.comp (-Polynomial.X)) hreflect
  simpa [Function.comp_def] using h.comp tendsto_neg_atBot_atTop

/-- A negative derivative on a left ray forces a positive-infinity limit there. -/
theorem polynomial_tendsto_atBot_of_left_derivative_neg (p : Polynomial ℝ) {b : ℝ}
    (hd : ∀ x ∈ Iio b, p.derivative.eval x < 0) : Tendsto p.eval atBot atTop := by
  have hreflect : ∀ x ∈ Ioi (-b), 0 < (p.comp (-Polynomial.X)).derivative.eval x := by
    intro x hx
    have hxb : -x < b := by change -b < x at hx; linarith
    simpa [Polynomial.derivative_comp] using neg_pos.mpr (hd (-x) hxb)
  have h := polynomial_tendsto_atTop_of_right_derivative_pos
    (p.comp (-Polynomial.X)) hreflect
  simpa [Function.comp_def] using h.comp tendsto_neg_atBot_atTop

/-- The right increasing polynomial ray has a root precisely for a negative finite endpoint. -/
theorem polynomial_right_root_iff_of_derivative_pos (p : Polynomial ℝ) {a : ℝ}
    (hd : ∀ x ∈ Ioi a, 0 < p.derivative.eval x) :
    (∃ x ∈ Ioi a, p.eval x = 0) ↔ p.eval a < 0 := by
  have hm : StrictMonoOn p.eval (Ici a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici a) p.continuous.continuousOn
    simpa only [interior_Ici, Polynomial.deriv] using hd
  exact exists_right_root_iff_of_strictMonoOn p.continuous.continuousOn hm
    (polynomial_tendsto_atTop_of_right_derivative_pos p hd)

/-- The right decreasing ray has a root precisely for a positive finite endpoint. -/
theorem polynomial_right_root_iff_of_derivative_neg (p : Polynomial ℝ) {a : ℝ}
    (hd : ∀ x ∈ Ioi a, p.derivative.eval x < 0) :
    (∃ x ∈ Ioi a, p.eval x = 0) ↔ 0 < p.eval a := by
  have hm : StrictAntiOn p.eval (Ici a) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici a) p.continuous.continuousOn
    simpa only [interior_Ici, Polynomial.deriv] using hd
  exact exists_right_root_iff_of_strictAntiOn p.continuous.continuousOn hm
    (polynomial_tendsto_atTop_of_right_derivative_neg p hd)

/-- The left increasing ray has a root precisely for a positive finite endpoint. -/
theorem polynomial_left_root_iff_of_derivative_pos (p : Polynomial ℝ) {b : ℝ}
    (hd : ∀ x ∈ Iio b, 0 < p.derivative.eval x) :
    (∃ x ∈ Iio b, p.eval x = 0) ↔ 0 < p.eval b := by
  have hm : StrictMonoOn p.eval (Iic b) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic b) p.continuous.continuousOn
    simpa only [interior_Iic, Polynomial.deriv] using hd
  exact exists_left_root_iff_of_strictMonoOn p.continuous.continuousOn hm
    (polynomial_tendsto_atBot_of_left_derivative_pos p hd)

/-- The left decreasing ray has a root precisely for a negative finite endpoint. -/
theorem polynomial_left_root_iff_of_derivative_neg (p : Polynomial ℝ) {b : ℝ}
    (hd : ∀ x ∈ Iio b, p.derivative.eval x < 0) :
    (∃ x ∈ Iio b, p.eval x = 0) ↔ p.eval b < 0 := by
  have hm : StrictAntiOn p.eval (Iic b) := by
    apply strictAntiOn_of_deriv_neg (convex_Iic b) p.continuous.continuousOn
    simpa only [interior_Iic, Polynomial.deriv] using hd
  exact exists_left_root_iff_of_strictAntiOn p.continuous.continuousOn hm
    (polynomial_tendsto_atBot_of_left_derivative_neg p hd)

/-- A continuous function with no zero on a closed interval has equal endpoint signs. -/
theorem sign_eq_of_no_zero_on_interval {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hn : ∀ x ∈ Icc a b, f x ≠ 0) : sign (f a) = sign (f b) := by
  have ha := hn a (left_mem_Icc.mpr hab)
  have hb := hn b (right_mem_Icc.mpr hab)
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · rw [sign_neg ha, sign_neg hb]
  · obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo hab hc ⟨ha, hb⟩
    exact False.elim (hn x (Ioo_subset_Icc_self hx) hz)
  · obtain ⟨x, hx, hz⟩ := intermediate_value_Ioo' hab hc ⟨hb, ha⟩
    exact False.elim (hn x (Ioo_subset_Icc_self hx) hz)
  · rw [sign_pos ha, sign_pos hb]

/-- A root-free right ray has throughout the sign dictated by the leading coefficient. -/
theorem polynomial_sign_on_rootFree_right_ray (p : Polynomial ℝ) {a : ℝ}
    (hn : ∀ x ∈ Ioi a, p.eval x ≠ 0) {x : ℝ} (hx : x ∈ Ioi a) :
    sign (p.eval x) = sign p.leadingCoeff := by
  obtain ⟨b, hxb, hb⟩ := ((eventually_gt_atTop x).and
    (polynomial_eventually_sign_atTop p)).exists
  have heq := sign_eq_of_no_zero_on_interval hxb.le p.continuous.continuousOn
    (fun y hy => hn y (lt_of_lt_of_le hx hy.1))
  exact heq.trans hb

/-- A root-free left ray has throughout the parity-corrected leading sign. -/
theorem polynomial_sign_on_rootFree_left_ray (p : Polynomial ℝ) {b : ℝ}
    (hn : ∀ x ∈ Iio b, p.eval x ≠ 0) {x : ℝ} (hx : x ∈ Iio b) :
    sign (p.eval x) = negativeInfinitySign p.natDegree (sign p.leadingCoeff) := by
  obtain ⟨a, hax, ha⟩ := ((eventually_lt_atBot x).and
    (polynomial_eventually_sign_atBot p)).exists
  have heq := sign_eq_of_no_zero_on_interval hax.le p.continuous.continuousOn
    (fun y hy => hn y (lt_of_le_of_lt hy.2 hx))
  exact heq.symm.trans ha

/-- Executable sign inference on a root-free increasing interval from its left endpoint. -/
def increasingNoRootSign : SignType → SignType
  | .neg => .neg
  | _ => .pos

/-- Executable sign inference on a root-free decreasing interval from its left endpoint. -/
def decreasingNoRootSign : SignType → SignType
  | .pos => .pos
  | _ => .neg

/-- If an increasing polynomial cell has no interior root, this rule determines every sign.
An endpoint root is allowed and gives a strictly positive interior. -/
theorem polynomial_increasing_noRoot_sign (p : Polynomial ℝ) {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x)
    (hn : ∀ x ∈ Ioo a b, p.eval x ≠ 0) {x : ℝ} (hx : x ∈ Ioo a b) :
    sign (p.eval x) = increasingNoRootSign (sign (p.eval a)) := by
  have hab : a < b := lt_trans hx.1 hx.2
  have hm := polynomial_strictMonoOn_of_derivative_pos p hd
  rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha
  · have hb : p.eval b ≤ 0 := by
      by_contra hneg
      obtain ⟨y, hy, hz⟩ :=
        (exists_root_iff_of_strictMonoOn hab p.continuous.continuousOn hm).mpr
          ⟨ha, lt_of_not_ge hneg⟩
      exact hn y hy hz
    have hxb := hm (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hab.le) hx.2
    rw [sign_neg (lt_of_lt_of_le hxb hb), sign_neg ha]
    rfl
  · have hax := hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1
    dsimp only at hax
    rw [ha] at hax
    rw [sign_pos hax, ha, sign_zero]
    rfl
  · have hax := hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1
    rw [sign_pos (lt_trans ha hax), sign_pos ha]
    rfl

/-- The decreasing cell rule includes a zero left endpoint, giving a negative interior. -/
theorem polynomial_decreasing_noRoot_sign (p : Polynomial ℝ) {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0)
    (hn : ∀ x ∈ Ioo a b, p.eval x ≠ 0) {x : ℝ} (hx : x ∈ Ioo a b) :
    sign (p.eval x) = decreasingNoRootSign (sign (p.eval a)) := by
  have hab : a < b := lt_trans hx.1 hx.2
  have hm := polynomial_strictAntiOn_of_derivative_neg p hd
  rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha
  · have hax := hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1
    rw [sign_neg (lt_trans hax ha), sign_neg ha]
    rfl
  · have hax := hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hx) hx.1
    dsimp only at hax
    rw [ha] at hax
    rw [sign_neg hax, ha, sign_zero]
    rfl
  · have hb : 0 ≤ p.eval b := by
      by_contra hneg
      obtain ⟨y, hy, hz⟩ :=
        (exists_root_iff_of_strictAntiOn hab p.continuous.continuousOn hm).mpr
          ⟨ha, lt_of_not_ge hneg⟩
      exact hn y hy hz
    have hxb := hm (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hab.le) hx.2
    rw [sign_pos (lt_of_le_of_lt hb hxb), sign_pos ha]
    rfl

/-- A polynomial whose derivative is everywhere positive has one global root,
and that root determines its sign everywhere. No asymptotic hypothesis is supplied. -/
theorem polynomial_exists_wholeLine_increasing_root (p : Polynomial ℝ)
    (hd : ∀ x : ℝ, 0 < p.derivative.eval x) :
    ∃ c, p.eval c = 0 ∧ ∀ x : ℝ,
      (p.eval x < 0 ↔ x < c) ∧ (p.eval x = 0 ↔ x = c) ∧
        (0 < p.eval x ↔ c < x) := by
  have hm : StrictMono p.eval := strictMono_of_deriv_pos (fun x => by simpa using hd x)
  have hder : p.derivative ≠ 0 := by
    intro hz
    have := hd 0
    simp only [hz, Polynomial.eval_zero, lt_self_iff_false] at this
  have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp
    (Nat.pos_of_ne_zero (Polynomial.derivative_ne_zero.mp hder))
  obtain ⟨a, ha, habs⟩ := ((eventually_lt_atBot (0 : ℝ)).and
    (p.abs_tendsto_atBot hdeg (eventually_gt_atTop (|p.eval 0| + 1)))).exists
  change |p.eval 0| + 1 < |p.eval a| at habs
  have hpa : p.eval a < 0 := by
    by_contra hneg
    have hn : 0 ≤ p.eval a := le_of_not_gt hneg
    rw [abs_of_nonneg hn] at habs
    have ham := hm ha
    linarith [le_abs_self (p.eval 0)]
  obtain ⟨b, hb, habs⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (p.abs_tendsto_atTop hdeg (eventually_gt_atTop (|p.eval 0| + 1)))).exists
  change |p.eval 0| + 1 < |p.eval b| at habs
  have hpb : 0 < p.eval b := by
    by_contra hneg
    have hn : p.eval b ≤ 0 := le_of_not_gt hneg
    rw [abs_of_nonpos hn] at habs
    have hbm := hm hb
    linarith [neg_le_abs (p.eval 0)]
  obtain ⟨c, _, hz⟩ := intermediate_value_Ioo (lt_trans ha hb).le
    p.continuous.continuousOn ⟨hpa, hpb⟩
  refine ⟨c, hz, fun x => ?_⟩
  exact signs_iff_of_strictMonoOn_root (hm.strictMonoOn univ) (mem_univ c) hz (mem_univ x)

/-- The whole-line decreasing case also supplies its root without additional limits. -/
theorem polynomial_exists_wholeLine_decreasing_root (p : Polynomial ℝ)
    (hd : ∀ x : ℝ, p.derivative.eval x < 0) :
    ∃ c, p.eval c = 0 ∧ ∀ x : ℝ,
      (p.eval x < 0 ↔ c < x) ∧ (p.eval x = 0 ↔ x = c) ∧
        (0 < p.eval x ↔ x < c) := by
  have hneg : ∀ x : ℝ, 0 < (-p).derivative.eval x := by
    intro x
    simpa only [Polynomial.derivative_neg, Polynomial.eval_neg, neg_pos] using hd x
  obtain ⟨c, hz, hsigns⟩ := polynomial_exists_wholeLine_increasing_root (-p) hneg
  refine ⟨c, by simpa using hz, fun x => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Polynomial.eval_neg, neg_pos] using (hsigns x).2.2
  · simpa only [Polynomial.eval_neg, neg_eq_zero] using (hsigns x).2.1
  · simpa only [Polynomial.eval_neg, neg_lt_zero] using (hsigns x).1

end MathUE.RealSignCell
