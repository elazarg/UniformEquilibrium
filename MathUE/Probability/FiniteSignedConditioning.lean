import GameTheory.Math.Probability.FinDist
import MathUE.Probability.SignedConditioningLikelihood

/-! # Signed conditioning of finite probability laws

An event of positive mass admits a two-sided affine variation toward its
conditional law. On the closed radius `min (1/2) (eventMass/2)`, every likelihood
factor lies between one half and three halves. Normalization, exact support
preservation, and affine expectations are derived from the original law.

The singleton specialization resets toward an existing positive atom using
the same constructor. Event mass one is allowed and gives a redundant
direction. The distant parameter one is not claimed to lie in this small
signed interval; ordinary conditioning already supplies that endpoint.

The safe event wrapper leaves the original law unchanged outside the positive
legal branch. Its support, likelihood bounds, and zero identity are unconditional;
affine conditional identities apply only on the actual positive legal branch.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory.Math.Probability.FinDist

variable {α : Type*}

theorem probOf_le_one (p : FinDist α) (A : Set α) : p.probOf A ≤ 1 := by
  classical
  rw [← expect_indicator_eq_probOf]
  apply expect_le_of_forall
  intro a _
  split_ifs <;> norm_num

/-- Positive event mass supplies conditioning's support witness. -/
theorem exists_mem_support_of_probOf_pos (p : FinDist α) (A : Set α)
    (he : 0 < p.probOf A) : ∃ a ∈ A, a ∈ p.support := by
  classical
  by_contra hnot
  have hzero : p.probOf A = 0 := by
    rw [← expect_indicator_eq_probOf]
    calc
      p.expect (fun a => if a ∈ A then 1 else 0) = p.expect (fun _ => 0) := by
        apply expect_congr
        intro a ha
        exact ite_eq_right (fun hA => hnot ⟨a, hA, ha⟩)
      _ = 0 := expect_const p 0
  exact he.ne' hzero

/-- A uniform two-sided legal radius, including the redundant mass-one case. -/
def signedCondRadius (p : FinDist α) (A : Set α) : ℝ :=
  min (1 / 2) (p.probOf A / 2)

theorem signedCondRadius_pos (p : FinDist α) (A : Set α) (he : 0 < p.probOf A) :
    0 < signedCondRadius p A :=
  lt_min (by norm_num) (half_pos he)

/-- Literal real weights of the signed affine conditional variation. -/
def signedCondWeight (p : FinDist α) (A : Set α) (parameter : ℝ) (a : α) : ℝ := by
  classical
  exact p.prob a * ((1 - parameter) + if a ∈ A then parameter / p.probOf A else 0)

open Classical in
private theorem signedCond_likelihood_bounds (p : FinDist α) (A : Set α)
    (he : 0 < p.probOf A) (parameter : ℝ)
    (hparameter : |parameter| ≤ signedCondRadius p A) (a : α) :
    (1 / 2 : ℝ) ≤ (1 - parameter) +
        (if a ∈ A then parameter / p.probOf A else 0) ∧
      (1 - parameter) + (if a ∈ A then parameter / p.probOf A else 0) ≤ 3 / 2 := by
  classical
  exact _root_.Math.Probability.signedConditioningLikelihood_bounds
    (p.probOf A) he (probOf_le_one p A) parameter hparameter (a ∈ A)

/-- Closed-radius bounds imply that every old positive atom stays positive. -/
theorem signedCondWeight_bounds (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) (a : α) :
    (1 / 2 : ℝ) * p.prob a ≤ signedCondWeight p A parameter a ∧
      signedCondWeight p A parameter a ≤ (3 / 2 : ℝ) * p.prob a := by
  classical
  obtain ⟨hlower, hupper⟩ := signedCond_likelihood_bounds p A he parameter hparameter a
  unfold signedCondWeight
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlower (p.prob_nonneg a)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hupper (p.prob_nonneg a)

theorem signedCondWeight_eq_affine (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (a : α) :
    signedCondWeight p A parameter a = (1 - parameter) * p.prob a +
      parameter * (p.condOn A (exists_mem_support_of_probOf_pos p A he)).prob a := by
  classical
  rw [signedCondWeight, prob_condOn]
  by_cases ha : a ∈ A <;> simp only [ha, ite_true, ite_false] <;> ring

section Finite

variable [Fintype α]

/-- Normalization is an affine identity for every real parameter, independently of legality. -/
theorem sum_signedCondWeight (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) : ∑ a, signedCondWeight p A parameter a = 1 := by
  simp_rw [signedCondWeight_eq_affine p A he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_prob, sum_prob]
  ring

/-- One probability constructor for signed conditioning; no negative convex-mixture operation
and no external normalization or support certificate is used. -/
def signedCond (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) : FinDist α :=
  ofWeights (signedCondWeight p A parameter)
    (fun a => (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (p.prob_nonneg a)).trans
      (signedCondWeight_bounds p A he parameter hparameter a).1)
    (sum_signedCondWeight p A he parameter)

theorem prob_signedCond (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) (a : α) :
    (signedCond p A he parameter hparameter).prob a = signedCondWeight p A parameter a :=
  prob_ofWeights ..

theorem prob_signedCond_eq_affine (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) (a : α) :
    (signedCond p A he parameter hparameter).prob a = (1 - parameter) * p.prob a +
      parameter * (p.condOn A (exists_mem_support_of_probOf_pos p A he)).prob a := by
  rw [prob_signedCond, signedCondWeight_eq_affine p A he]

theorem prob_signedCond_bounds (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) (a : α) :
    (1 / 2 : ℝ) * p.prob a ≤ (signedCond p A he parameter hparameter).prob a ∧
      (signedCond p A he parameter hparameter).prob a ≤ (3 / 2 : ℝ) * p.prob a := by
  rw [prob_signedCond]
  exact signedCondWeight_bounds p A he parameter hparameter a

theorem prob_signedCond_le_two_mul (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) (a : α) :
    (signedCond p A he parameter hparameter).prob a ≤ 2 * p.prob a := by
  have hbound := (prob_signedCond_bounds p A he parameter hparameter a).2
  linarith [p.prob_nonneg a]

/-- Support equality holds on the closed signed radius, not only on its interior. -/
theorem support_signedCond (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) :
    (signedCond p A he parameter hparameter).support = p.support := by
  ext a
  rw [← prob_pos_iff, ← prob_pos_iff]
  have hbound := prob_signedCond_bounds p A he parameter hparameter a
  constructor <;> intro hpositive <;> linarith

theorem signedCond_zero (p : FinDist α) (A : Set α) (he : 0 < p.probOf A) :
    signedCond p A he 0 (by simpa only [abs_zero] using (signedCondRadius_pos p A he).le) =
      p := by
  apply ext_of_prob
  intro a
  rw [prob_signedCond_eq_affine]
  ring

/-- A mass-one event gives the identical law; no nontrivial-event hypothesis is required. -/
theorem signedCond_eq_self_of_probOf_eq_one (p : FinDist α) (A : Set α)
    (parameter : ℝ)
    (hparameter : |parameter| ≤ signedCondRadius p A) (heone : p.probOf A = 1) :
    signedCond p A (by rw [heone]; norm_num) parameter hparameter = p := by
  classical
  have hsupport : p.support ⊆ A := by
    intro a ha
    have hvalue := p.eq_of_expect_eq_of_le (fun b => if b ∈ A then (1 : ℝ) else 0) 1
      (by intro b _; split_ifs <;> norm_num)
      ((expect_indicator_eq_probOf p A).trans heone) ha
    by_contra hnot
    simp only [ite_eq_right hnot] at hvalue
    norm_num at hvalue
  apply ext_of_prob
  intro a
  rw [prob_signedCond_eq_affine, condOn_of_support_subset p A _ hsupport]
  ring

/-- The existing-positive-atom reset is the singleton specialization of the same constructor. -/
theorem prob_signedCond_singleton (p : FinDist α) (a : α) (ha : 0 < p.prob a)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p {a}) (b : α) :
    (signedCond p {a} (by simpa only [probOf_singleton] using ha)
      parameter hparameter).prob b =
      (1 - parameter) * p.prob b + parameter * (pure a).prob b := by
  classical
  rw [prob_signedCond_eq_affine, prob_condOn, probOf_singleton, prob_pure_eq_ite]
  by_cases hba : b = a
  · subst b
    simp only [Set.mem_singleton_iff, ite_true, div_self ha.ne']
  · simp only [Set.mem_singleton_iff, hba, ite_false, mul_zero, add_zero]

/-- Every observable has the exact affine expectation, for either parameter sign. -/
theorem expect_signedCond (p : FinDist α) (A : Set α) (he : 0 < p.probOf A)
    (parameter : ℝ) (hparameter : |parameter| ≤ signedCondRadius p A) (u : α → ℝ) :
    (signedCond p A he parameter hparameter).expect u =
      (1 - parameter) * p.expect u +
        parameter * (p.condOn A (exists_mem_support_of_probOf_pos p A he)).expect u := by
  simp only [expect_eq_sum, prob_signedCond_eq_affine, add_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- A total signed-event source law, retaining the original law when the event or radius is
unavailable. This does not identify a distant parameter with ordinary conditioning. -/
def signedCondOrSelf (p : FinDist α) (A : Set α) (parameter : ℝ) : FinDist α := by
  classical
  exact if h : 0 < p.probOf A ∧ |parameter| ≤ p.signedCondRadius A then
    p.signedCond A h.1 parameter h.2
  else p

/-- Only the positive legal branch is identified with the affine signed constructor. -/
theorem signedCondOrSelf_eq_signedCond (p : FinDist α) (A : Set α)
    (he : 0 < p.probOf A) (parameter : ℝ)
    (hparameter : |parameter| ≤ p.signedCondRadius A) :
    p.signedCondOrSelf A parameter = p.signedCond A he parameter hparameter := by
  rw [signedCondOrSelf, dite_eq_left ⟨he, hparameter⟩]

theorem signedCondOrSelf_eq_self_of_not (p : FinDist α) (A : Set α) (parameter : ℝ)
    (h : ¬(0 < p.probOf A ∧ |parameter| ≤ p.signedCondRadius A)) :
    p.signedCondOrSelf A parameter = p := by
  rw [signedCondOrSelf, dite_eq_right h]

/-- Support equality includes every fallback index and every real parameter. -/
theorem support_signedCondOrSelf (p : FinDist α) (A : Set α) (parameter : ℝ) :
    (p.signedCondOrSelf A parameter).support = p.support := by
  classical
  unfold signedCondOrSelf
  split
  · exact support_signedCond ..
  · rfl

/-- The positive legal branch and the fallback have the same unconditional probability bounds. -/
theorem prob_signedCondOrSelf_bounds (p : FinDist α) (A : Set α)
    (parameter : ℝ) (a : α) :
    (1 / 2 : ℝ) * p.prob a ≤ (p.signedCondOrSelf A parameter).prob a ∧
      (p.signedCondOrSelf A parameter).prob a ≤ (3 / 2 : ℝ) * p.prob a := by
  classical
  unfold signedCondOrSelf
  split
  · exact prob_signedCond_bounds ..
  · have hnonneg := p.prob_nonneg a
    constructor <;> linarith

theorem signedCondOrSelf_zero (p : FinDist α) (A : Set α) :
    p.signedCondOrSelf A 0 = p := by
  classical
  unfold signedCondOrSelf
  split
  · exact signedCond_zero ..
  · rfl

end Finite

end GameTheory.Math.Probability.FinDist
