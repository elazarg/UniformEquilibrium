import MathUE.Probability.OverlappingFirstStopping

/-! # Mass-one overlapping first-stopping events have one deterministic finite tie -/

noncomputable section

namespace Math.Probability.DiscreteHazard.StoppingLaw

private theorem tsum_finiteMass_upper (law : PMF (Option ℕ)) :
    (∑' time, finiteMass law time) ≤ 1 := by
  have h := none_add_tsum_finiteMass law
  linarith [ENNReal.toReal_nonneg (a := law none)]

private theorem finiteMass_zero_of_other_eq_one
    (law : PMF (Option ℕ)) {time other : ℕ}
    (hone : finiteMass law time = 1) (hne : other ≠ time) :
    finiteMass law other = 0 := by
  have hsum := (summable_finiteMass law).sum_le_tsum
    ({other, time} : Finset ℕ) (fun t _ => finiteMass_nonneg law t)
  have hupper := tsum_finiteMass_upper law
  simp only [Finset.mem_singleton, hne, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, hone] at hsum
  linarith [finiteMass_nonneg law other]

/-- A mass-one first-pair event forces a common deterministic finite atom;
the remaining clock survives strictly beyond that atom. -/
theorem exists_deterministicFiniteAtom_of_equalFirstSecondBeforeThirdMass_eq_one
    (first second third : PMF (Option ℕ))
    (hone : equalFirstSecondBeforeThirdMass first second third = 1) :
    ∃ time, finiteMass first time = 1 ∧ finiteMass second time = 1 ∧
      survival third (time + 1) = 1 := by
  let term : ℕ → ℝ := fun time =>
    finiteMass first time * finiteMass second time * survival third (time + 1)
  have hterm : Summable term :=
    summable_equalFirstSecondBeforeThirdMass_terms first second third
  have htermOne : (∑' time, term time) = 1 := hone
  have htermLe : ∀ time, term time ≤ finiteMass first time := by
    intro time
    exact (mul_le_of_le_one_right
      (mul_nonneg (finiteMass_nonneg first time) (finiteMass_nonneg second time))
      (survival_le_one third (time + 1))).trans
        (mul_le_of_le_one_right (finiteMass_nonneg first time)
          (finiteMass_le_one second time))
  have hfirstSum : (∑' time, finiteMass first time) = 1 := by
    have hle := hterm.tsum_le_tsum htermLe (summable_finiteMass first)
    linarith [tsum_finiteMass_upper first]
  have hdeficit : Summable (fun time => finiteMass first time - term time) :=
    (summable_finiteMass first).sub hterm
  have hdeficitNonneg : ∀ time, 0 ≤ finiteMass first time - term time :=
    fun time => sub_nonneg.mpr (htermLe time)
  have hdeficitSum : (∑' time, (finiteMass first time - term time)) = 0 := by
    rw [(summable_finiteMass first).tsum_sub hterm, hfirstSum, htermOne, sub_self]
  have htermEq : ∀ time, term time = finiteMass first time := by
    intro time
    have hsingle := hdeficit.sum_le_tsum ({time} : Finset ℕ)
      (fun t _ => hdeficitNonneg t)
    simp only [Finset.sum_singleton, hdeficitSum] at hsingle
    linarith [htermLe time]
  obtain ⟨time, hpositive⟩ : ∃ time, 0 < finiteMass first time := by
    by_contra hnone
    have hzero : ∀ time, finiteMass first time = 0 := by
      intro time
      apply le_antisymm _ (finiteMass_nonneg first time)
      exact le_of_not_gt (fun h => hnone ⟨time, h⟩)
    simp only [hzero, tsum_zero] at hfirstSum
    norm_num at hfirstSum
  have hproduct : finiteMass second time * survival third (time + 1) = 1 := by
    apply (mul_left_cancel₀ hpositive.ne')
    have h := htermEq time
    dsimp only [term] at h
    nlinarith only [h]
  have hsecondOne : finiteMass second time = 1 := by
    have hle := mul_le_of_le_one_right (finiteMass_nonneg second time)
      (survival_le_one third (time + 1))
    linarith [finiteMass_le_one second time]
  have hsurvivalOne : survival third (time + 1) = 1 := by
    simpa only [hsecondOne, one_mul] using hproduct
  have hsingle : (∑' t, term t) = term time := by
    apply tsum_eq_single time
    intro other hne
    dsimp only [term]
    rw [finiteMass_zero_of_other_eq_one second hsecondOne hne, mul_zero, zero_mul]
  refine ⟨time, ?_, hsecondOne, hsurvivalOne⟩
  rw [htermOne] at hsingle
  simpa only [term, hsecondOne, hsurvivalOne, mul_one] using hsingle.symm

/-- A deterministic finite tie strictly before the third clock has mass one. -/
theorem equalFirstSecondBeforeThirdMass_eq_one_of_deterministicFiniteAtom
    (first second third : PMF (Option ℕ)) (time : ℕ)
    (hfirst : finiteMass first time = 1) (hsecond : finiteMass second time = 1)
    (hthird : survival third (time + 1) = 1) :
    equalFirstSecondBeforeThirdMass first second third = 1 := by
  unfold equalFirstSecondBeforeThirdMass
  rw [tsum_eq_single time]
  · rw [hfirst, hsecond, hthird]
    norm_num
  · intro other hne
    rw [finiteMass_zero_of_other_eq_one first hfirst hne, zero_mul, zero_mul]

/-- Exact deterministic-atom characterization, with the strict tail condition
retaining arbitrary later finite stopping and Never. -/
theorem equalFirstSecondBeforeThirdMass_eq_one_iff_deterministicFiniteAtom
    (first second third : PMF (Option ℕ)) :
    equalFirstSecondBeforeThirdMass first second third = 1 ↔
      ∃ time, finiteMass first time = 1 ∧ finiteMass second time = 1 ∧
        survival third (time + 1) = 1 := by
  constructor
  · exact exists_deterministicFiniteAtom_of_equalFirstSecondBeforeThirdMass_eq_one
      first second third
  · rintro ⟨time, hfirst, hsecond, hthird⟩
    exact equalFirstSecondBeforeThirdMass_eq_one_of_deterministicFiniteAtom
      first second third time hfirst hsecond hthird

theorem equalFirstThirdBeforeSecondMass_eq_one_iff_deterministicFiniteAtom
    (first second third : PMF (Option ℕ)) :
    equalFirstThirdBeforeSecondMass first second third = 1 ↔
      ∃ time, finiteMass first time = 1 ∧ finiteMass third time = 1 ∧
        survival second (time + 1) = 1 :=
  equalFirstSecondBeforeThirdMass_eq_one_iff_deterministicFiniteAtom first third second

end Math.Probability.DiscreteHazard.StoppingLaw
