import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakHalfResidual

/-! # Weak polynomial half-face guards and their literal strictification

The hypotheses are signs of the actual residual on the closed outsider square,
not lower reward rankings or Bernstein coefficient conditions. The lower face
excludes only the all-zero outsider row. Boundary hazards remain admissible.
-/

noncomputable section

namespace GameTheory

open Filter Set QuittingLCPClassification
open scoped Topology

/-- The broader polynomial-face variant in packet Section 6.2. -/
structure QuittingHalfWeakPolynomialGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop where
  lower : ∀ recipient : Fin 4, recipient = 0 ∨ recipient = 1 →
    ∀ x y : ℝ, 0 ≤ x ∧ x ≤ 1 → 0 ≤ y ∧ y ≤ 1 → x ≠ 0 ∨ y ≠ 0 →
      0 ≤ quittingDiscountedDisplacement reward 0 ![0, 0, x, y] recipient
  upperFirst : ∀ x y : ℝ, 0 ≤ x ∧ x ≤ 1 → 0 ≤ y ∧ y ≤ 1 →
    quittingHalfFirstResidual reward x y ≤ 0
  upperSecond : ∀ x y : ℝ, 0 ≤ x ∧ x ≤ 1 → 0 ≤ y ∧ y ≤ 1 →
    quittingHalfSecondResidual reward x y ≤ 0

/-- Nonnegative actual residuals along a positive opponent axis force the
corresponding singleton comparison to be nonpositive. The exact existing
axis expansion supplies the right derivative without a new Taylor proof. -/
theorem quittingSingletonMatrix_nonpos_of_axis_displacement_nonneg
    {n : ℕ} (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient outsider : Fin n) (hne : recipient ≠ outsider)
    (haxis : ∀ rate : ℝ, 0 < rate → rate ≤ 1 →
      0 ≤ quittingDiscountedDisplacement reward 0 (singletonRow rate outsider) recipient) :
    quittingSingletonMatrix reward recipient outsider ≤ 0 := by
  let bracket : ℝ → ℝ := fun rate =>
    (1 - rate) * weightOfReward reward {recipient} recipient +
      rate * weightOfReward reward {recipient, outsider} recipient -
        weightOfReward reward {outsider} recipient
  have hcontinuous : Continuous bracket := by
    dsimp [bracket]
    fun_prop
  have hsmall : ∀ᶠ rate : ℝ in 𝓝[>] (0 : ℝ), rate < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hnonneg : ∀ᶠ rate : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ bracket rate := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with rate hrate hsmall
    have h := haxis rate hrate hsmall.le
    rw [quittingDiscountedDisplacement_singletonRow_of_ne reward hne rate] at h
    exact nonneg_of_mul_nonneg_right h hrate
  have hlimit : 0 ≤ bracket 0 :=
    ge_of_tendsto (hcontinuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hnonneg
  simpa [bracket, quittingSingletonMatrix, weightOfReward, sub_nonneg, sub_nonpos] using hlimit

/-- Reciprocity uses only invertibility, a nonnegative inverse, and
nonpositive external singleton comparisons, not a finite lower-ranking test. -/
theorem quittingCrossed_reciprocal_pos_of_nonpositive_externals_nonnegativeInverse
    {n : ℕ} (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n)
    (hdet : (quittingSingletonMatrix reward).det ≠ 0)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hexternal : ∀ outsider, outsider ≠ recipient → outsider ≠ partner →
      quittingSingletonMatrix reward recipient outsider ≤ 0) :
    0 < quittingSingletonMatrix reward recipient partner := by
  by_contra hnot
  have hpartner := le_of_not_gt hnot
  have hrow : ∀ column, quittingSingletonMatrix reward recipient column ≤ 0 := by
    intro column
    by_cases hself : column = recipient
    · subst column
      simp [quittingSingletonMatrix]
    by_cases hcol : column = partner
    · subst column
      exact hpartner
    exact hexternal column hself hcol
  have hproduct : (quittingSingletonMatrix reward *
      (quittingSingletonMatrix reward)⁻¹) recipient recipient ≤ 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonpos fun column _ =>
      mul_nonpos_of_nonpos_of_nonneg (hrow column) (hinverse column recipient)
  have hidentity := congrFun (congrFun
    (Matrix.mul_nonsing_inv (quittingSingletonMatrix reward)
      (isUnit_iff_ne_zero.mpr hdet)) recipient) recipient
  simp only [Matrix.one_apply_eq] at hidentity
  linarith

/-- The weak polynomial lower face determines every selected external sign. -/
theorem QuittingHalfWeakPolynomialGuards.external_nonpos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hguard : QuittingHalfWeakPolynomialGuards reward)
    (recipient outsider : Fin 4) (hrecipient : recipient = 0 ∨ recipient = 1)
    (houtsider : outsider = 2 ∨ outsider = 3) :
    quittingSingletonMatrix reward recipient outsider ≤ 0 := by
  have hne : recipient ≠ outsider := by
    rcases hrecipient with rfl | rfl <;> rcases houtsider with rfl | rfl <;> decide
  apply quittingSingletonMatrix_nonpos_of_axis_displacement_nonneg reward recipient outsider hne
  intro rate hrate hone
  rcases houtsider with rfl | rfl
  · have hrow : singletonRow rate (2 : Fin 4) = ![0, 0, rate, 0] := by
      funext coordinate
      fin_cases coordinate <;> simp [singletonRow]
    rw [hrow]
    exact hguard.lower recipient hrecipient rate 0 ⟨hrate.le, hone⟩
      ⟨le_rfl, zero_le_one⟩ (Or.inl hrate.ne')
  · have hrow : singletonRow rate (3 : Fin 4) = ![0, 0, 0, rate] := by
      funext coordinate
      fin_cases coordinate <;> simp [singletonRow]
    rw [hrow]
    exact hguard.lower recipient hrecipient 0 rate ⟨le_rfl, zero_le_one⟩
      ⟨hrate.le, hone⟩ (Or.inr hrate.ne')

/-- Both reciprocal entries are produced from the original weak polynomial
guards and nonnegative inverse. No reciprocal sign is an additional input. -/
theorem QuittingHalfWeakPolynomialGuards.reciprocal_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hguard : QuittingHalfWeakPolynomialGuards reward)
    (hdet : (quittingSingletonMatrix reward).det ≠ 0)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column) :
    0 < quittingSingletonMatrix reward 0 1 ∧ 0 < quittingSingletonMatrix reward 1 0 := by
  constructor
  · apply quittingCrossed_reciprocal_pos_of_nonpositive_externals_nonnegativeInverse
      reward 0 1 hdet hinverse
    intro outsider hzero hone
    have hout : outsider = 2 ∨ outsider = 3 := by
      fin_cases outsider <;> simp_all
    exact hguard.external_nonpos 0 outsider (Or.inl rfl) hout
  · apply quittingCrossed_reciprocal_pos_of_nonpositive_externals_nonnegativeInverse
      reward 1 0 hdet hinverse
    intro outsider hone hzero
    have hout : outsider = 2 ∨ outsider = 3 := by
      fin_cases outsider <;> simp_all
    exact hguard.external_nonpos 1 outsider (Or.inr rfl) hout

/-- The same actual reward perturbation adds exactly epsilon times outsider
absorption on the partner-zero face, for every ambient outsider rate. -/
theorem quittingLowerResidual_weakHalfPerturb
    (epsilon : ℝ)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (recipient : Fin 4) (hrecipient : recipient = 0 ∨ recipient = 1) (x y : ℝ) :
    quittingDiscountedDisplacement (quittingCrossedWeakHalfPerturb epsilon reward)
        0 ![0, 0, x, y] recipient =
      quittingDiscountedDisplacement reward 0 ![0, 0, x, y] recipient +
        epsilon * (1 - (1 - x) * (1 - y)) := by
  have hpowerset : ({2, 3} : Finset (Fin 4)).powerset =
      {∅, {2}, {3}, {2, 3}} := by decide
  have hdiffTwo : ({2, 3} : Finset (Fin 4)) \ {2} = {3} := by decide
  have hdiffThree : ({2, 3} : Finset (Fin 4)) \ {3} = {2} := by decide
  rcases hrecipient with rfl | rfl
  · rw [quittingCrossed_displacement_partner_zero_eq_sums _ _ 0 1 (by decide) (by simp),
      quittingCrossed_displacement_partner_zero_eq_sums _ _ 0 1 (by decide) (by simp)]
    rw [show quittingCrossedRawOutsiders (0 : Fin 4) 1 = {2, 3} by decide, hpowerset]
    norm_num +decide [Math.Finset.bernoulliWeight, hdiffTwo, hdiffThree,
      weightOfReward, quittingCrossedWeakHalfPerturb]
    ring_nf
  · rw [quittingCrossed_displacement_partner_zero_eq_sums _ _ 1 0 (by decide) (by simp),
      quittingCrossed_displacement_partner_zero_eq_sums _ _ 1 0 (by decide) (by simp)]
    rw [show quittingCrossedRawOutsiders (1 : Fin 4) 0 = {2, 3} by decide, hpowerset]
    norm_num +decide [Math.Finset.bernoulliWeight, hdiffTwo, hdiffThree,
      weightOfReward, quittingCrossedWeakHalfPerturb]
    ring_nf

private theorem outsider_survival_bounds (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ (1 - x) * (1 - y) ∧ (1 - x) * (1 - y) ≤ 1 := by
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
  · nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]

private theorem outsider_absorption_pos (x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < 1 - (1 - x) * (1 - y) := by
  rcases hne with hxne | hyne
  · have hxpos := lt_of_le_of_ne hx.1 (Ne.symm hxne)
    nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hx.2)]
  · have hypos := lt_of_le_of_ne hy.1 (Ne.symm hyne)
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hy.2)]

/-- Strict source guards on the perturbed table follow from polynomial weak
guards directly, without passing through sufficient coefficient tests. -/
theorem quittingCrossedSourceGuards_of_weakPolynomialPerturb
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hguard : QuittingHalfWeakPolynomialGuards reward) :
    QuittingCrossedSourceGuards (quittingCrossedWeakHalfPerturb epsilon reward) 0 1 (1 / 2) := by
  have hrow (a b : ℝ) (z : QuittingCrossedOutsider (0 : Fin 4) 1 → ℝ) :
      quittingCrossedGuardRow 0 1 a b z =
        ![a, b, z ⟨2, by decide, by decide⟩, z ⟨3, by decide, by decide⟩] := by
    funext coordinate
    fin_cases coordinate <;> simp [quittingCrossedGuardRow]
  have hnonzero (z : QuittingCrossedOutsider (0 : Fin 4) 1 → ℝ) (hne : z ≠ 0) :
      z ⟨2, by decide, by decide⟩ ≠ 0 ∨ z ⟨3, by decide, by decide⟩ ≠ 0 := by
    by_contra hnot
    push Not at hnot
    apply hne
    funext outsider
    obtain ⟨coordinate, hzero, hone⟩ := outsider
    change coordinate ≠ 0 at hzero
    change coordinate ≠ 1 at hone
    fin_cases coordinate
    · exact False.elim (hzero rfl)
    · exact False.elim (hone rfl)
    · exact hnot.1
    · exact hnot.2
  constructor
  · intro z hz hne
    rw [hrow, quittingLowerResidual_weakHalfPerturb epsilon reward 0 (Or.inl rfl)]
    exact add_pos_of_nonneg_of_pos
      (hguard.lower 0 (Or.inl rfl) _ _ (hz _) (hz _) (hnonzero z hne))
      (mul_pos hepsilon (outsider_absorption_pos _ _ (hz _) (hz _) (hnonzero z hne)))
  · intro z hz hne
    rw [hrow, quittingLowerResidual_weakHalfPerturb epsilon reward 1 (Or.inr rfl)]
    exact add_pos_of_nonneg_of_pos
      (hguard.lower 1 (Or.inr rfl) _ _ (hz _) (hz _) (hnonzero z hne))
      (mul_pos hepsilon (outsider_absorption_pos _ _ (hz _) (hz _) (hnonzero z hne)))
  · intro z hz
    rw [hrow]
    change quittingHalfFirstResidual (quittingCrossedWeakHalfPerturb epsilon reward)
      (z ⟨2, by decide, by decide⟩) (z ⟨3, by decide, by decide⟩) < 0
    rw [quittingHalfFirstResidual_weakHalfPerturb]
    have hupper := hguard.upperFirst _ _ (hz ⟨2, by decide, by decide⟩)
      (hz ⟨3, by decide, by decide⟩)
    have hsurvival := outsider_survival_bounds _ _ (hz ⟨2, by decide, by decide⟩)
      (hz ⟨3, by decide, by decide⟩)
    nlinarith [mul_nonneg hepsilon.le (sub_nonneg.mpr hsurvival.2)]
  · intro z hz
    rw [hrow]
    change quittingHalfSecondResidual (quittingCrossedWeakHalfPerturb epsilon reward)
      (z ⟨2, by decide, by decide⟩) (z ⟨3, by decide, by decide⟩) < 0
    rw [quittingHalfSecondResidual_weakHalfPerturb]
    have hupper := hguard.upperSecond _ _ (hz ⟨2, by decide, by decide⟩)
      (hz ⟨3, by decide, by decide⟩)
    have hsurvival := outsider_survival_bounds _ _ (hz ⟨2, by decide, by decide⟩)
      (hz ⟨3, by decide, by decide⟩)
    nlinarith [mul_nonneg hepsilon.le (sub_nonneg.mpr hsurvival.2)]

end GameTheory
