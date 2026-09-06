import MathUE.Probability.OverlappingFirstStoppingEquality
import MathUE.SqrtQuadraticChordEquality

/-! # One-row square-root equality with positive continuation -/

noncomputable section

namespace Math.Probability.DiscreteHazard

private theorem firstSecond_endpoint_le_sharp
    {first second third : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt ((1 - third) *
        (first * second + (1 - first) * (1 - second))) +
      Real.sqrt (third * (first * (1 - second))) ≤
        Real.sqrt (1 - (1 - first) * second) := by
  have hmiddle : 0 ≤ first * second + (1 - first) * (1 - second) :=
    add_nonneg (mul_nonneg hfirst.1 hsecond.1)
      (mul_nonneg (sub_nonneg.mpr hfirst.2) (sub_nonneg.mpr hsecond.2))
  have hother : 0 ≤ first * (1 - second) :=
    mul_nonneg hfirst.1 (sub_nonneg.mpr hsecond.2)
  have hcs := sqrt_mul_add_sqrt_mul_le_sqrt_add_mul_add
    (sub_nonneg.mpr hthird.2) hthird.1 hmiddle hother
  have hinside :
      ((1 - third) + third) *
        ((first * second + (1 - first) * (1 - second)) +
          first * (1 - second)) = 1 - (1 - first) * second := by ring
  rw [hinside] at hcs
  exact hcs

/-- Equality at the first endpoint, away from zero common continuation,
forces the first exclusive hazard to vanish and the other to equal the common
hazard. -/
theorem firstSecond_endpoint_eq_one_of_commonContinue_pos
    {first second third : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hcontinue : 0 < (1 - first) * (1 - second) * (1 - third))
    (heq : Real.sqrt
          (first * second * (1 - third) +
            (1 - first) * (1 - second) * (1 - third)) +
        Real.sqrt (first * third * (1 - second)) = 1) :
    second = 0 ∧ third = first := by
  have hfirstLt : first < 1 := by
    apply lt_of_le_of_ne hfirst.2
    intro h
    rw [h] at hcontinue
    simp at hcontinue
  have hsharp := firstSecond_endpoint_le_sharp hfirst hsecond hthird
  have hrewrite :
      Real.sqrt
          (first * second * (1 - third) +
            (1 - first) * (1 - second) * (1 - third)) +
        Real.sqrt (first * third * (1 - second)) =
      Real.sqrt ((1 - third) *
          (first * second + (1 - first) * (1 - second))) +
        Real.sqrt (third * (first * (1 - second))) := by
    congr 1 <;> ring_nf
  rw [hrewrite] at heq
  have hsqrtGe : 1 ≤ Real.sqrt (1 - (1 - first) * second) := by linarith
  have hinsideNonneg : 0 ≤ 1 - (1 - first) * second := by
    have hproduct : (1 - first) * second ≤ 1 :=
      (mul_le_of_le_one_left hsecond.1 (sub_le_self 1 hfirst.1)).trans hsecond.2
    linarith
  have hinsideGe : 1 ≤ 1 - (1 - first) * second := by
    nlinarith [Real.sq_sqrt hinsideNonneg]
  have hsecondZero : second = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfirst.2) hsecond.1]
  refine ⟨hsecondZero, ?_⟩
  subst second
  simp only [mul_zero, sub_zero, zero_add, mul_one] at heq
  let u := Real.sqrt ((1 - third) * (1 - first))
  let v := Real.sqrt (third * first)
  have huSq : u ^ 2 = (1 - third) * (1 - first) := by
    exact Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hthird.2)
      (sub_nonneg.mpr hfirst.2))
  have hvSq : v ^ 2 = third * first :=
    Real.sq_sqrt (mul_nonneg hthird.1 hfirst.1)
  have huv : u + v = 1 := by simpa [u, v, mul_comm] using heq
  have hfactor :
      (third - first) ^ 2 =
        (1 - (1 - third) * (1 - first) - third * first) ^ 2 -
          4 * ((1 - third) * (1 - first)) * (third * first) := by ring
  have hzero : (third - first) ^ 2 = 0 := by
    rw [hfactor, ← huSq, ← hvSq]
    have hvEq : v = 1 - u := by linarith
    rw [hvEq]
    ring
  nlinarith

/-- Symmetric endpoint equality condition. -/
theorem firstThird_endpoint_eq_one_of_commonContinue_pos
    {first second third : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hcontinue : 0 < (1 - first) * (1 - second) * (1 - third))
    (heq : Real.sqrt (first * second * (1 - third)) +
        Real.sqrt
          (first * third * (1 - second) +
            (1 - first) * (1 - second) * (1 - third)) = 1) :
    third = 0 ∧ second = first := by
  have hcontinue' : 0 < (1 - first) * (1 - third) * (1 - second) := by
    nlinarith [hcontinue]
  have heq' :
      Real.sqrt
          (first * third * (1 - second) +
            (1 - first) * (1 - third) * (1 - second)) +
        Real.sqrt (first * second * (1 - third)) = 1 := by
    rw [add_comm]
    convert heq using 1
    ring_nf
  have h := firstSecond_endpoint_eq_one_of_commonContinue_pos
    hfirst hthird hsecond hcontinue' heq'
  exact h

/-- At a positive-continuation row, equality is possible only at the all-zero
row or through one of the two deterministic future endpoints. -/
theorem overlappingFirstStopping_squareRoot_step_eq_one_of_commonContinue_pos
    {first second third futureFirstSecond futureFirstThird : ℝ}
    (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1)
    (hthird : third ∈ Set.Icc (0 : ℝ) 1)
    (hfutureFirstSecond : 0 ≤ futureFirstSecond)
    (hfutureFirstThird : 0 ≤ futureFirstThird)
    (hfuture : Real.sqrt futureFirstSecond +
      Real.sqrt futureFirstThird ≤ 1)
    (hcontinue : 0 < (1 - first) * (1 - second) * (1 - third))
    (hequality :
      Real.sqrt
          (first * second * (1 - third) +
            (1 - first) * (1 - second) * (1 - third) * futureFirstSecond) +
        Real.sqrt
          (first * third * (1 - second) +
            (1 - first) * (1 - second) * (1 - third) * futureFirstThird) = 1) :
    (first = 0 ∧ second = 0 ∧ third = 0) ∨
      (second = 0 ∧ third = first ∧ futureFirstSecond = 1 ∧
          futureFirstThird = 0) ∨
        (third = 0 ∧ second = first ∧ futureFirstSecond = 0 ∧
          futureFirstThird = 1) := by
  let c := (1 - first) * (1 - second) * (1 - third)
  let d₁ := first * second * (1 - third)
  let d₂ := first * third * (1 - second)
  let u := Real.sqrt futureFirstSecond
  let v := Real.sqrt futureFirstThird
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Real.sqrt_nonneg _
    · dsimp only [u]
      linarith [Real.sqrt_nonneg futureFirstThird]
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hc : 0 < c := hcontinue
  have hd₁ : 0 ≤ d₁ := by
    exact mul_nonneg (mul_nonneg hfirst.1 hsecond.1) (sub_nonneg.mpr hthird.2)
  have hd₂ : 0 ≤ d₂ := by
    exact mul_nonneg (mul_nonneg hfirst.1 hthird.1) (sub_nonneg.mpr hsecond.2)
  have hfutureFirstSecondEq : futureFirstSecond = u ^ 2 := by
    exact (Real.sq_sqrt hfutureFirstSecond).symm
  have hfutureFirstThirdBound : futureFirstThird ≤ (1 - u) ^ 2 := by
    have hsqrtBound : Real.sqrt futureFirstThird ≤ 1 - u := by
      dsimp only [u]
      linarith
    nlinarith [Real.sq_sqrt hfutureFirstThird]
  have houtputLeF :
      Real.sqrt (d₁ + c * futureFirstSecond) +
          Real.sqrt (d₂ + c * futureFirstThird) ≤
        Real.sqrt (d₁ + c * u ^ 2) +
          Real.sqrt (d₂ + c * (1 - u) ^ 2) := by
    rw [hfutureFirstSecondEq]
    gcongr
  have hchord₁ := sqrt_quadratic_chord hd₁ hc.le hu
  have hchord₂ := sqrt_quadratic_chord hd₂ hc.le
    (show 1 - u ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [hu.1, hu.2])
  let endpoint₁ := Real.sqrt (d₁ + c) + Real.sqrt d₂
  let endpoint₂ := Real.sqrt d₁ + Real.sqrt (d₂ + c)
  have hendpoint₁ : endpoint₁ ≤ 1 := by
    dsimp only [endpoint₁, d₁, d₂, c]
    simpa [mul_assoc] using firstSecond_endpoint_le_one hfirst hsecond hthird
  have hendpoint₂ : endpoint₂ ≤ 1 := by
    dsimp only [endpoint₂, d₁, d₂, c]
    simpa [mul_assoc] using firstThird_endpoint_le_one hfirst hsecond hthird
  have hFleChord :
      Real.sqrt (d₁ + c * u ^ 2) + Real.sqrt (d₂ + c * (1 - u) ^ 2) ≤
        u * endpoint₁ + (1 - u) * endpoint₂ := by
    dsimp only [endpoint₁, endpoint₂]
    linarith
  have hChordLeOne : u * endpoint₁ + (1 - u) * endpoint₂ ≤ 1 := by
    have hu0 := hu.1
    have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
    nlinarith
  have hequality' :
      Real.sqrt (d₁ + c * futureFirstSecond) +
        Real.sqrt (d₂ + c * futureFirstThird) = 1 := by
    simpa [d₁, d₂, c] using hequality
  have hFone :
      Real.sqrt (d₁ + c * u ^ 2) + Real.sqrt (d₂ + c * (1 - u) ^ 2) = 1 := by
    linarith
  have hChordOne : u * endpoint₁ + (1 - u) * endpoint₂ = 1 := by linarith
  have hallZeroOrSome :
      (first = 0 ∧ second = 0 ∧ third = 0) ∨ 0 < d₁ ∨ 0 < d₂ := by
    by_cases hd₁pos : 0 < d₁
    · exact Or.inr (Or.inl hd₁pos)
    by_cases hd₂pos : 0 < d₂
    · exact Or.inr (Or.inr hd₂pos)
    · have hd₁zero : d₁ = 0 := le_antisymm (le_of_not_gt hd₁pos) hd₁
      have hd₂zero : d₂ = 0 := le_antisymm (le_of_not_gt hd₂pos) hd₂
      have hFone' := hFone
      rw [hd₁zero, hd₂zero, zero_add, Real.sqrt_mul (le_of_lt hc),
        Real.sqrt_sq_eq_abs, abs_of_nonneg hu.1, zero_add,
        Real.sqrt_mul (le_of_lt hc), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by linarith [hu.2])] at hFone'
      have hsqrtc : Real.sqrt c = 1 := by
        nlinarith [Real.sqrt_nonneg c]
      have hcOne : c = 1 := by
        nlinarith [Real.sq_sqrt hc.le]
      have hbc : (1 - second) * (1 - third) ≤ 1 := by
        exact mul_le_one₀ (sub_le_self 1 hsecond.1)
          (sub_nonneg.mpr hthird.2) (sub_le_self 1 hthird.1)
      have hca : (1 - first) * (1 - third) ≤ 1 := by
        exact mul_le_one₀ (sub_le_self 1 hfirst.1)
          (sub_nonneg.mpr hthird.2) (sub_le_self 1 hthird.1)
      have hab : (1 - first) * (1 - second) ≤ 1 := by
        exact mul_le_one₀ (sub_le_self 1 hfirst.1)
          (sub_nonneg.mpr hsecond.2) (sub_le_self 1 hsecond.1)
      have hcFirst : c ≤ 1 - first := by
        dsimp only [c]
        calc
          (1 - first) * (1 - second) * (1 - third) =
              (1 - first) * ((1 - second) * (1 - third)) := by ring
          _ ≤ (1 - first) * 1 :=
            mul_le_mul_of_nonneg_left hbc (sub_nonneg.mpr hfirst.2)
          _ = 1 - first := mul_one _
      have hcSecond : c ≤ 1 - second := by
        dsimp only [c]
        calc
          (1 - first) * (1 - second) * (1 - third) =
              ((1 - first) * (1 - third)) * (1 - second) := by ring
          _ ≤ 1 * (1 - second) :=
            mul_le_mul_of_nonneg_right hca (sub_nonneg.mpr hsecond.2)
          _ = 1 - second := one_mul _
      have hcThird : c ≤ 1 - third := by
        dsimp only [c]
        exact (mul_le_mul_of_nonneg_right hab
          (sub_nonneg.mpr hthird.2)).trans_eq (one_mul _)
      rw [hcOne] at hcFirst hcSecond hcThird
      exact Or.inl ⟨le_antisymm (by linarith) hfirst.1,
        le_antisymm (by linarith) hsecond.1,
        le_antisymm (by linarith) hthird.1⟩
  rcases hallZeroOrSome with hallZero | hsome
  · exact Or.inl hallZero
  have hfirstChordEq : Real.sqrt (d₁ + c * u ^ 2) =
      u * Real.sqrt (d₁ + c) + (1 - u) * Real.sqrt d₁ := by linarith
  have hsecondChordEq : Real.sqrt (d₂ + c * (1 - u) ^ 2) =
      (1 - u) * Real.sqrt (d₂ + c) + u * Real.sqrt d₂ := by linarith
  have huEndpoint : u = 0 ∨ u = 1 := by
    rcases hsome with hd₁pos | hd₂pos
    · exact Math.sqrt_quadratic_chord_eq_imp_endpoint hd₁pos hc hu hfirstChordEq
    · have h := Math.sqrt_quadratic_chord_eq_imp_endpoint hd₂pos hc
        (show 1 - u ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith [hu.1, hu.2])
        (by simpa only [sub_sub_cancel] using hsecondChordEq)
      rcases h with h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  rcases huEndpoint with huZero | huOne
  · have hfutureFirstSecondZero : futureFirstSecond = 0 := by
      rw [hfutureFirstSecondEq, huZero]
      norm_num
    have hfutureFirstThirdOne : futureFirstThird = 1 := by
      have hsqrtEq : Real.sqrt (d₂ + c * futureFirstThird) =
          Real.sqrt (d₂ + c) := by
        rw [hfutureFirstSecondZero] at hequality'
        rw [huZero] at hFone
        norm_num at hequality' hFone
        linarith
      have hleft : 0 ≤ d₂ + c * futureFirstThird :=
        add_nonneg hd₂ (mul_nonneg hc.le hfutureFirstThird)
      have hright : 0 ≤ d₂ + c := add_nonneg hd₂ hc.le
      have hsquare := congrArg (fun value : ℝ => value ^ 2) hsqrtEq
      rw [Real.sq_sqrt hleft, Real.sq_sqrt hright] at hsquare
      have hm : c * futureFirstThird = c := by linarith only [hsquare]
      apply (mul_left_cancel₀ hc.ne')
      simpa using hm
    have hendpointEq : endpoint₂ = 1 := by rw [huZero] at hChordOne; simpa using hChordOne
    have hendpointEq' :
        Real.sqrt (first * second * (1 - third)) +
          Real.sqrt
            (first * third * (1 - second) +
              (1 - first) * (1 - second) * (1 - third)) = 1 := by
      dsimp only [endpoint₂, d₁, d₂, c] at hendpointEq
      simpa only [mul_assoc] using hendpointEq
    have hshape := firstThird_endpoint_eq_one_of_commonContinue_pos hfirst hsecond
      hthird hcontinue hendpointEq'
    exact Or.inr (Or.inr ⟨hshape.1, hshape.2, hfutureFirstSecondZero,
      hfutureFirstThirdOne⟩)
  · have hfutureFirstSecondOne : futureFirstSecond = 1 := by
      rw [hfutureFirstSecondEq, huOne]
      norm_num
    have hfutureFirstThirdZero : futureFirstThird = 0 := by
      have := hfutureFirstThirdBound
      rw [huOne] at this
      exact le_antisymm (by norm_num at this ⊢; exact this) hfutureFirstThird
    have hendpointEq : endpoint₁ = 1 := by rw [huOne] at hChordOne; simpa using hChordOne
    have hendpointEq' :
        Real.sqrt
            (first * second * (1 - third) +
              (1 - first) * (1 - second) * (1 - third)) +
          Real.sqrt (first * third * (1 - second)) = 1 := by
      dsimp only [endpoint₁, d₁, d₂, c] at hendpointEq
      simpa only [mul_assoc] using hendpointEq
    have hshape := firstSecond_endpoint_eq_one_of_commonContinue_pos hfirst hsecond
      hthird hcontinue hendpointEq'
    exact Or.inr (Or.inl ⟨hshape.1, hshape.2, hfutureFirstSecondOne,
      hfutureFirstThirdZero⟩)

end Math.Probability.DiscreteHazard
