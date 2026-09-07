import Mathlib.Algebra.Order.Archimedean.Real.Basic
import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion

/-! # Reciprocal parameters for finite-calendar payoff exclusion

Positive real strict-deficit margins and ordered-pair parameters can be
replaced by a smaller parameter of the literal rational form `1 / k`.  These
results prove that the corresponding enumeration contains a successful
candidate; they do not implement or bound a search procedure.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem cast_rat_nat_reciprocal (k : ℕ) :
    ((((k : ℚ)⁻¹ : ℚ) : ℝ)) = (k : ℝ)⁻¹ := by
  exact Rat.cast_inv_nat k

omit [Nonempty ι] in
/-- Weakening a uniform strict-deficit margin preserves the raw calendar
condition. -/
theorem hasQuittingFiniteCalendarRawStrictSingletonDeficit_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {small large : ℝ} (hsmallLarge : small ≤ large)
    (hlarge : HasQuittingFiniteCalendarRawStrictSingletonDeficit reward large) :
    HasQuittingFiniteCalendarRawStrictSingletonDeficit reward small := by
  intro x
  obtain ⟨who, hwho⟩ := hlarge x
  exact ⟨who, by linarith⟩

/-- A raw strict exclusion has a positive reciprocal rational margin.  This
is the termination witness for enumerating `1 / k`, not an implemented
enumerator. -/
theorem exists_nat_reciprocal_finiteCalendarRawStrictSingletonDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstrict : HasQuittingFiniteCalendarRawStrictExclusion reward) :
    ∃ k : ℕ, 0 < k ∧ 0 < ((((k : ℚ)⁻¹ : ℚ) : ℝ)) ∧
      HasQuittingFiniteCalendarRawStrictSingletonDeficit reward
        (((k : ℚ)⁻¹ : ℚ) : ℝ) := by
  obtain ⟨gap, hgap, hactual⟩ :=
    exists_positive_actual_strictSingletonDeficit_of_rawStrictExclusion
      reward hstrict
  have hraw : HasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap :=
    (hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual
      reward gap).mpr hactual
  obtain ⟨k, hk, hreciprocal⟩ := Real.exists_nat_pos_inv_lt hgap
  refine ⟨k, hk, ?_, ?_⟩
  · rw [cast_rat_nat_reciprocal]
    exact inv_pos.mpr (Nat.cast_pos.mpr hk)
  · apply hasQuittingFiniteCalendarRawStrictSingletonDeficit_of_le
      reward (le_of_lt ?_) hraw
    rwa [cast_rat_nat_reciprocal]

omit [DecidableEq ι] [Nonempty ι] in
/-- Increasing the capped-simplex cap preserves actual group exclusion. -/
private theorem hasQuittingActualNonconcentratedGroupExclusion_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {small large : ℝ} (hsmallLarge : small ≤ large)
    (hsmall : HasQuittingActualNonconcentratedGroupExclusion reward small) :
    HasQuittingActualNonconcentratedGroupExclusion reward large := by
  intro profile
  obtain ⟨weight, hnonnegative, hsum, hcapped, hweighted⟩ := hsmall profile
  exact ⟨weight, hnonnegative, hsum,
    fun who => (hcapped who).trans hsmallLarge, hweighted⟩

omit [Nonempty ι] in
/-- The ordered-pair group-exclusion condition is preserved when its positive
parameter is decreased within `(0, 1/2]`. -/
theorem hasQuittingActualOrderedPairGroupExclusion_of_pos_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {small large : ℝ} (hsmall : 0 < small) (hsmallLarge : small ≤ large)
    (hlargeHalf : large ≤ (1 : ℝ) / 2)
    (hlarge : HasQuittingActualOrderedPairGroupExclusion reward large) :
    HasQuittingActualOrderedPairGroupExclusion reward small := by
  have hlargePos : 0 < large := hsmall.trans_le hsmallLarge
  have hlargeCap : HasQuittingActualNonconcentratedGroupExclusion
      reward (1 - large) := by
    apply (hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair
      reward (1 - large) (by linarith) (by linarith)).mpr
    simpa only [sub_sub_cancel] using hlarge
  have hsmallCap : HasQuittingActualNonconcentratedGroupExclusion
      reward (1 - small) :=
    hasQuittingActualNonconcentratedGroupExclusion_of_le reward
      (by linarith) hlargeCap
  apply (hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair
    reward (1 - small) (by linarith) (by linarith)).mp at hsmallCap
  simpa only [sub_sub_cancel] using hsmallCap

/-- Raw finite-calendar ordered-pair exclusion has the same downward
monotonicity in its positive parameter. -/
theorem hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_of_pos_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {small large : ℝ} (hsmall : 0 < small) (hsmallLarge : small ≤ large)
    (hlargeHalf : large ≤ (1 : ℝ) / 2)
    (hlarge : HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
      reward large) :
    HasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward small := by
  apply (hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_iff_actual
    reward small).mpr
  apply hasQuittingActualOrderedPairGroupExclusion_of_pos_le
    reward hsmall hsmallLarge hlargeHalf
  exact (hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_iff_actual
    reward large).mp hlarge

/-- A positive raw ordered-pair parameter has a successful reciprocal rational
candidate `1 / k`, with `k ≥ 2`. -/
theorem exists_nat_reciprocal_finiteCalendarRawOrderedPairGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hlambdaHalf : lambda ≤ (1 : ℝ) / 2)
    (hexclusion : HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
      reward lambda) :
    ∃ k : ℕ, 2 ≤ k ∧ 0 < ((((k : ℚ)⁻¹ : ℚ) : ℝ)) ∧
      (((k : ℚ)⁻¹ : ℚ) : ℝ) ≤ (1 : ℝ) / 2 ∧
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward
        (((k : ℚ)⁻¹ : ℚ) : ℝ) := by
  obtain ⟨k, hk, hreciprocal⟩ := Real.exists_nat_pos_inv_lt hlambda
  have hkTwo : 2 ≤ k := by
    have hinvHalf : (k : ℝ)⁻¹ < (1 : ℝ) / 2 :=
      hreciprocal.trans_le hlambdaHalf
    have htwoCast : (2 : ℝ) < (k : ℝ) := by
      apply (inv_lt_inv₀ (Nat.cast_pos.mpr hk) (by norm_num)).mp
      simpa only [one_div] using hinvHalf
    exact_mod_cast htwoCast.le
  have hpositive : 0 < ((((k : ℚ)⁻¹ : ℚ) : ℝ)) := by
    rw [cast_rat_nat_reciprocal]
    exact inv_pos.mpr (Nat.cast_pos.mpr hk)
  have hle : (((k : ℚ)⁻¹ : ℚ) : ℝ) ≤ lambda := by
    rw [cast_rat_nat_reciprocal]
    exact hreciprocal.le
  refine ⟨k, hkTwo, hpositive, hle.trans hlambdaHalf, ?_⟩
  exact hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_of_pos_le
    reward hpositive hle hlambdaHalf hexclusion

/-- The existential raw group-exclusion hypothesis admits a reciprocal
rational ordered-pair parameter. -/
theorem exists_nat_reciprocal_orderedPairGroupExclusion_of_finiteCalendarRaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hexclusion : ∃ beta < 1,
      HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) :
    ∃ k : ℕ, 2 ≤ k ∧ 0 < ((((k : ℚ)⁻¹ : ℚ) : ℝ)) ∧
      (((k : ℚ)⁻¹ : ℚ) : ℝ) ≤ (1 : ℝ) / 2 ∧
      HasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward
        (((k : ℚ)⁻¹ : ℚ) : ℝ) := by
  obtain ⟨lambda, hlambda, hlambdaHalf, hpairs⟩ :=
    (exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair
      reward).mp hexclusion
  exact exists_nat_reciprocal_finiteCalendarRawOrderedPairGroupExclusion
    reward hlambda hlambdaHalf hpairs

end GameTheory
