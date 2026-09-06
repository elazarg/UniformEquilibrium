import MathUE.ProbabilityMassFunction.StoppingLawLateIndicators
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Replacing an actual stopping law's finite tail by a geometric tail -/

noncomputable section

namespace Math.Probability

open Filter
open scoped BigOperators Topology

private theorem hasSum_geometric_hazard {hazard : ℝ}
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    HasSum (fun offset : ℕ ↦ hazard * (1 - hazard) ^ offset) 1 := by
  have hsum := (hasSum_geometric_of_lt_one (sub_nonneg.mpr hle)
    (show 1 - hazard < 1 by linarith)).mul_left hazard
  simpa [show 1 - (1 - hazard) = hazard by ring, ne_of_gt hpositive] using hsum

/-- A geometric PMF with a strictly positive success probability, including
the point-mass boundary at success probability one. -/
def geometricOffsetLaw (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) : PMF ℕ :=
  ⟨fun offset ↦ ENNReal.ofReal (hazard * (1 - hazard) ^ offset), by
    apply ENNReal.hasSum_coe.mpr
    rw [← ENNReal.toNNReal_one]
    simpa using (hasSum_geometric_hazard hpositive hle).toNNReal
      (fun offset ↦ mul_nonneg hpositive.le (pow_nonneg (sub_nonneg.mpr hle) offset))⟩

@[simp] theorem geometricOffsetLaw_apply_toReal
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (offset : ℕ) :
    (geometricOffsetLaw hazard hpositive hle offset).toReal =
      hazard * (1 - hazard) ^ offset := by
  exact ENNReal.toReal_ofReal
    (mul_nonneg hpositive.le (pow_nonneg (sub_nonneg.mpr hle) offset))

/-- A geometric law on finite dates starting at the displayed deadline. -/
def geometricFiniteStoppingLaw (deadline : ℕ) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) : PMF (Option ℕ) :=
  (geometricOffsetLaw hazard hpositive hle).map (fun offset ↦ some (deadline + offset))

@[simp] theorem geometricFiniteStoppingLaw_none
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    geometricFiniteStoppingLaw deadline hazard hpositive hle none = 0 := by
  simp [geometricFiniteStoppingLaw, PMF.map_apply]

theorem geometricFiniteStoppingLaw_some_of_lt
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    {time : ℕ} (htime : time < deadline) :
    geometricFiniteStoppingLaw deadline hazard hpositive hle (some time) = 0 := by
  rw [geometricFiniteStoppingLaw, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro offset
  rw [if_neg]
  simp only [Option.some.injEq]
  omega

@[simp] theorem geometricFiniteStoppingLaw_add_apply_toReal
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (offset : ℕ) :
    (geometricFiniteStoppingLaw deadline hazard hpositive hle (some (deadline + offset))).toReal =
      hazard * (1 - hazard) ^ offset := by
  rw [geometricFiniteStoppingLaw, PMF.map_apply, tsum_eq_single offset]
  · simp
  · intro other hother
    simp [hother.symm]

/-- Retain the head and Never choices literally; redirect a finite late
choice to an independent geometric finite clock. -/
def geometricPivotStoppingKernel (deadline : ℕ) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) : Option ℕ → PMF (Option ℕ)
  | none => PMF.pure none
  | some time => if time < deadline then PMF.pure (some time)
      else geometricFiniteStoppingLaw deadline hazard hpositive hle

/-- Actual complete marginal law obtained by geometrically redistributing
only the source's late finite mass. Its Never atom is not redistributed. -/
def geometricPivotStoppingLaw (source : PMF (Option ℕ)) (deadline : ℕ) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) : PMF (Option ℕ) :=
  source.bind (geometricPivotStoppingKernel deadline hazard hpositive hle)

@[simp] theorem geometricPivotStoppingLaw_none
    (source : PMF (Option ℕ)) (deadline : ℕ) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    geometricPivotStoppingLaw source deadline hazard hpositive hle none = source none := by
  rw [geometricPivotStoppingLaw, PMF.bind_apply, tsum_eq_single none]
  · simp [geometricPivotStoppingKernel]
  · intro choice hchoice
    cases choice with
    | none => exact (hchoice rfl).elim
    | some chosen =>
        simp only [geometricPivotStoppingKernel]
        split_ifs <;> simp

theorem geometricPivotStoppingLaw_some_of_lt
    (source : PMF (Option ℕ)) (deadline : ℕ) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) {time : ℕ} (htime : time < deadline) :
    geometricPivotStoppingLaw source deadline hazard hpositive hle (some time) =
      source (some time) := by
  rw [geometricPivotStoppingLaw, PMF.bind_apply, tsum_eq_single (some time)]
  · simp [geometricPivotStoppingKernel, htime]
  · intro choice hchoice
    cases choice with
    | none => simp [geometricPivotStoppingKernel]
    | some chosen =>
        simp only [geometricPivotStoppingKernel]
        split_ifs with hchosen
        · simp [PMF.pure_apply, hchoice.symm]
        · rw [geometricFiniteStoppingLaw_some_of_lt deadline hazard hpositive hle htime]
          simp

/-- Censoring immediately before the deadline erases precisely the geometric
redistribution and returns the source's actual censored law. -/
theorem censorLateFiniteStoppingLaw_geometricPivotStoppingLaw
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    censorLateFiniteStoppingLaw
        (geometricPivotStoppingLaw source deadline hazard hpositive hle) (deadline - 1) =
      censorLateFiniteStoppingLaw source (deadline - 1) := by
  unfold censorLateFiniteStoppingLaw geometricPivotStoppingLaw
  rw [PMF.map_bind, ← PMF.bind_pure_comp]
  apply congrArg (PMF.bind source)
  funext choice
  cases choice with
  | none =>
      simp [geometricPivotStoppingKernel, censorLateFiniteStoppingOutcome, PMF.pure_map]
  | some chosen =>
      by_cases hchosen : chosen < deadline
      · simp [geometricPivotStoppingKernel, hchosen, PMF.pure_map]
      · simp only [geometricPivotStoppingKernel, if_neg hchosen,
          geometricFiniteStoppingLaw, PMF.map_comp]
        have hmap : censorLateFiniteStoppingOutcome (deadline - 1) ∘
            (fun offset ↦ some (deadline + offset)) = fun _ : ℕ ↦ none := by
          funext offset
          simp [Function.comp_apply, censorLateFiniteStoppingOutcome,
            show ¬ deadline + offset ≤ deadline - 1 by omega]
        rw [hmap]
        change (geometricOffsetLaw hazard hpositive hle).map
          (Function.const ℕ (none : Option ℕ)) = _
        rw [PMF.map_const]
        simp [censorLateFiniteStoppingOutcome, show ¬ chosen ≤ deadline - 1 by omega]

private theorem expect_late_finite_indicator
    (source : PMF (Option ℕ)) (cutoff : ℕ) :
    expect source (fun choice ↦ if choice ∈ stoppingLawFinitePrefix cutoff then 0 else 1) =
      stoppingLawLateFiniteMass source cutoff := by
  rw [stoppingLawLateFiniteMass_eq_tsum_compl,
    tsum_subtype ((↑(stoppingLawFinitePrefix cutoff) : Set (Option ℕ))ᶜ)
      (fun choice ↦ (source choice).toReal), expect]
  apply tsum_congr
  intro choice
  by_cases hchoice : choice ∈ stoppingLawFinitePrefix cutoff <;> simp [hchoice]

/-- The actual geometric replacement retains the source's total late finite
mass; equality follows from its unchanged head and Never atom. -/
theorem geometricPivotStoppingLaw_lateFiniteMass
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    stoppingLawLateFiniteMass
        (geometricPivotStoppingLaw source deadline hazard hpositive hle) (deadline - 1) =
      stoppingLawLateFiniteMass source (deadline - 1) := by
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead,
    stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead, geometricPivotStoppingLaw_none]
  congr 1
  unfold stoppingLawFiniteHeadMass
  apply Finset.sum_congr rfl
  intro time htime
  rw [geometricPivotStoppingLaw_some_of_lt source deadline hazard hpositive hle]
  have hmem := Finset.mem_range.mp htime
  omega

/-- Each actual replacement atom is the source's finite-tail mass times the
geometric probability. No normalization equation is assumed as input. -/
theorem geometricPivotStoppingLaw_add_apply_toReal
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (offset : ℕ) :
    (geometricPivotStoppingLaw source deadline hazard hpositive hle
      (some (deadline + offset))).toReal =
      stoppingLawLateFiniteMass source (deadline - 1) *
        hazard * (1 - hazard) ^ offset := by
  have hkernel (choice : Option ℕ) :
      (geometricPivotStoppingKernel deadline hazard hpositive hle choice
        (some (deadline + offset))).toReal =
      (hazard * (1 - hazard) ^ offset) *
        (if choice ∈ stoppingLawFinitePrefix (deadline - 1) then 0 else 1) := by
    cases choice with
    | none => simp [geometricPivotStoppingKernel]
    | some chosen =>
        by_cases hchosen : chosen < deadline
        · simp [geometricPivotStoppingKernel, hchosen,
            show chosen ≤ deadline - 1 by omega, PMF.pure_apply,
            show deadline + offset ≠ chosen by omega]
        · simp [geometricPivotStoppingKernel, hchosen,
            show ¬ chosen ≤ deadline - 1 by omega]
  rw [geometricPivotStoppingLaw, PMF.bind_apply,
    ENNReal.tsum_toReal_eq (fun choice ↦ ENNReal.mul_ne_top
      (PMF.apply_ne_top source choice) (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul, hkernel]
  change expect source (fun choice ↦ (hazard * (1 - hazard) ^ offset) *
    (if choice ∈ stoppingLawFinitePrefix (deadline - 1) then 0 else 1)) = _
  rw [expect_const_mul, expect_late_finite_indicator]
  ring

/-- The displayed geometric prefix has its exact complementary-power mass. -/
theorem geometricPivotStoppingLaw_sum_Ico_add
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (offset : ℕ) :
    (∑ time ∈ Finset.Ico deadline (deadline + offset),
      (geometricPivotStoppingLaw source deadline hazard hpositive hle (some time)).toReal) =
      stoppingLawLateFiniteMass source (deadline - 1) * (1 - (1 - hazard) ^ offset) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left,
    geometricPivotStoppingLaw_add_apply_toReal source hdeadline hazard hpositive hle]
  induction offset with
  | zero => simp
  | succ offset ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- Positive actual finite-tail mass supplies its first positive finite
atom, together with the vanishing interval before that atom. -/
theorem exists_first_positive_late_stoppingAtom
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (htail : 0 < stoppingLawLateFiniteMass source (deadline - 1)) :
    ∃ first : ℕ, deadline ≤ first ∧ 0 < (source (some first)).toReal ∧
      ∀ time, deadline ≤ time → time < first → (source (some time)).toReal = 0 := by
  have hexists : ∃ time : ℕ, deadline ≤ time ∧ 0 < (source (some time)).toReal := by
    by_contra hnone
    have hzero : stoppingLawLateFiniteMass source (deadline - 1) = 0 := by
      rw [stoppingLawLateFiniteMass_eq_tsum_compl]
      have hmass (choice : ↑((↑(stoppingLawFinitePrefix (deadline - 1)) : Set (Option ℕ))ᶜ)) :
          (source choice).toReal = 0 := by
        obtain ⟨time, htime, heq⟩ := stoppingLawFinitePrefix_compl_is_late_finite choice
        rw [heq]
        apply le_antisymm
        · apply le_of_not_gt
          intro hpositive
          exact hnone ⟨time, by omega, hpositive⟩
        · exact ENNReal.toReal_nonneg
      simp only [hmass, tsum_zero]
    exact htail.ne' hzero
  refine ⟨Nat.find hexists, (Nat.find_spec hexists).1, (Nat.find_spec hexists).2, ?_⟩
  intro time htime hbefore
  apply le_antisymm
  · apply le_of_not_gt
    intro hpositive
    exact (not_le_of_gt hbefore) (Nat.find_min' hexists ⟨htime, hpositive⟩)
  · exact ENNReal.toReal_nonneg

/-- Any positive actual late atom divided by the actual total finite tail
is a valid strictly positive geometric hazard. -/
theorem late_stoppingAtom_div_tail_mem_Ioc
    (source : PMF (Option ℕ)) {deadline time : ℕ} (hdeadline : 0 < deadline)
    (htime : deadline ≤ time) (hpositive : 0 < (source (some time)).toReal) :
    0 < (source (some time)).toReal / stoppingLawLateFiniteMass source (deadline - 1) ∧
      (source (some time)).toReal / stoppingLawLateFiniteMass source (deadline - 1) ≤ 1 := by
  have hle := stoppingLaw_atom_le_lateFiniteMass source (deadline - 1) time (by omega)
  have htail : 0 < stoppingLawLateFiniteMass source (deadline - 1) := hpositive.trans_le hle
  exact ⟨div_pos hpositive htail, (div_le_one htail).mpr hle⟩

/-- If there is no late finite source mass, geometric redistribution is
literally the identity law. -/
theorem geometricPivotStoppingLaw_eq_of_lateFiniteMass_eq_zero
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline)
    (htail : stoppingLawLateFiniteMass source (deadline - 1) = 0)
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    geometricPivotStoppingLaw source deadline hazard hpositive hle = source := by
  apply PMF.ext
  intro choice
  cases choice with
  | none => exact geometricPivotStoppingLaw_none source deadline hazard hpositive hle
  | some time =>
      by_cases htime : time < deadline
      · exact geometricPivotStoppingLaw_some_of_lt source deadline hazard hpositive hle htime
      · obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (show deadline ≤ time by omega)
        apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
          (PMF.apply_ne_top _ _)).mp
        rw [geometricPivotStoppingLaw_add_apply_toReal source hdeadline hazard hpositive hle,
          htail, zero_mul, zero_mul]
        symm
        apply le_antisymm
        · simpa only [htail] using stoppingLaw_atom_le_lateFiniteMass source
            (deadline - 1) (deadline + offset) (by omega)
        · exact ENNReal.toReal_nonneg

/-- Finite atoms of an arbitrary complete stopping law vanish at infinity. -/
theorem stoppingLaw_finite_atom_tendsto_zero (source : PMF (Option ℕ)) :
    Tendsto (fun time ↦ (source (some time)).toReal) atTop (nhds 0) := by
  exact ((pmf_toReal_summable source).comp_injective
    (Option.some_injective ℕ)).tendsto_atTop_zero

/-- Finite interval masses converge to the actual late-finite mass, without
requiring that the source law be proper or finitely supported. -/
theorem stoppingLaw_sum_Ico_tendsto_lateFiniteMass
    (source : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline) :
    Tendsto (fun time ↦ ∑ chosen ∈ Finset.Ico deadline time,
      (source (some chosen)).toReal) atTop
      (nhds (stoppingLawLateFiniteMass source (deadline - 1))) := by
  have hlimit : Tendsto (fun time ↦ DiscreteHazard.StoppingLaw.survival source deadline -
      DiscreteHazard.StoppingLaw.survival source time) atTop
      (nhds (DiscreteHazard.StoppingLaw.survival source deadline - (source none).toReal)) :=
    tendsto_const_nhds.sub (DiscreteHazard.StoppingLaw.tendsto_survival_none source)
  have hevent : ∀ᶠ time in atTop,
      DiscreteHazard.StoppingLaw.survival source deadline -
          DiscreteHazard.StoppingLaw.survival source time =
        ∑ chosen ∈ Finset.Ico deadline time, (source (some chosen)).toReal := by
    filter_upwards [eventually_ge_atTop deadline] with time htime
    have hsum := Finset.sum_range_add_sum_Ico
      (fun chosen ↦ (source (some chosen)).toReal) htime
    unfold DiscreteHazard.StoppingLaw.survival DiscreteHazard.StoppingLaw.finiteMass
    linarith
  have h := hlimit.congr' hevent
  simpa [stoppingLaw_survival_eq_lateFiniteMass_add_none source hdeadline] using h

end Math.Probability
