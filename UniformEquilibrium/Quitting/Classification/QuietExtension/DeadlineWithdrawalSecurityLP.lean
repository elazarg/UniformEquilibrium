import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalRaw
import Mathlib.Topology.Order.Lattice

/-!
# Finite stationary-security optimization

Section 5 of `WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md` maximizes the lower
envelope of finitely many affine reward rows on the unit hazard interval.
This file constructs its optimum from the reward table alone. LP attainment
does not assert attainment by an actual stopping law: a zero optimal hazard
can require positive-hazard approximation for terminal security.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The singleton constraint and every nonempty opponent-coalition constraint.
The `none` row makes the indexing type nonempty even for a one-player child. -/
def deadlineWithdrawalSecurityRow
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard : ℝ)
    (row : Option {A : Finset ι // A.Nonempty ∧ i ∉ A}) : ℝ :=
  match row with
  | none => reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  | some B =>
      (1 - hazard) * reward ⟨cappedClockChildCoalition B.1,
          cappedClockChildCoalition_nonempty B.2.1⟩ (some i) +
        hazard * reward ⟨cappedClockChildCoalition (insert i B.1),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i B.1)⟩ (some i)

/-- The largest feasible value at a fixed hazard, including at zero. -/
def deadlineWithdrawalSecurityEnvelope
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (deadlineWithdrawalSecurityRow reward i hazard)

/-- Exactly the two-variable LP constraints from Section 5. -/
def DeadlineWithdrawalSecurityFeasible
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard value : ℝ) : Prop :=
  hazard ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ row, value ≤ deadlineWithdrawalSecurityRow reward i hazard row

theorem deadlineWithdrawalSecurity_le_envelope_iff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (hazard value : ℝ) :
    value ≤ deadlineWithdrawalSecurityEnvelope reward i hazard ↔
      ∀ row, value ≤ deadlineWithdrawalSecurityRow reward i hazard row := by
  rw [deadlineWithdrawalSecurityEnvelope, Finset.le_inf'_iff]
  simp

theorem continuous_deadlineWithdrawalSecurityEnvelope
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : Continuous (deadlineWithdrawalSecurityEnvelope reward i) := by
  apply Continuous.finset_inf'_apply
    (f := fun row hazard => deadlineWithdrawalSecurityRow reward i hazard row)
    Finset.univ_nonempty
  intro row _
  cases row <;> simp only [deadlineWithdrawalSecurityRow] <;> fun_prop

/-- The reward table alone produces an LP optimizer. This includes empty
opponent-coalition families and optimizers at hazard zero. -/
theorem exists_deadlineWithdrawalSecurity_optimizer
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) :
    ∃ hazard value,
      DeadlineWithdrawalSecurityFeasible reward i hazard value ∧
      ∀ otherHazard otherValue,
        DeadlineWithdrawalSecurityFeasible reward i otherHazard otherValue →
        otherValue ≤ value := by
  obtain ⟨hazard, hmem, hmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_isMaxOn
      ⟨0, by constructor <;> norm_num⟩
      (continuous_deadlineWithdrawalSecurityEnvelope reward i).continuousOn
  refine ⟨hazard, deadlineWithdrawalSecurityEnvelope reward i hazard, ?_, ?_⟩
  · exact ⟨hmem,
      (deadlineWithdrawalSecurity_le_envelope_iff reward i hazard _).mp le_rfl⟩
  · intro otherHazard otherValue hother
    exact ((deadlineWithdrawalSecurity_le_envelope_iff reward i otherHazard
      otherValue).mpr hother.2).trans (hmax hother.1)

/-- The canonical LP value uses the optimizer furnished by compactness,
without any supplied security strategy or cap hypothesis. -/
def deadlineWithdrawalSecurityValue
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : ℝ :=
  Classical.choose
    (Classical.choose_spec (exists_deadlineWithdrawalSecurity_optimizer reward i))

theorem deadlineWithdrawalSecurityValue_spec
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) :
    ∃ hazard,
      DeadlineWithdrawalSecurityFeasible reward i hazard
        (deadlineWithdrawalSecurityValue reward i) ∧
      ∀ otherHazard otherValue,
        DeadlineWithdrawalSecurityFeasible reward i otherHazard otherValue →
        otherValue ≤ deadlineWithdrawalSecurityValue reward i := by
  exact ⟨Classical.choose (exists_deadlineWithdrawalSecurity_optimizer reward i),
    Classical.choose_spec (Classical.choose_spec
      (exists_deadlineWithdrawalSecurity_optimizer reward i))⟩

theorem deadlineWithdrawalSecurityValue_le_singleton
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) :
    deadlineWithdrawalSecurityValue reward i ≤
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  obtain ⟨hazard, hfeasible, _⟩ := deadlineWithdrawalSecurityValue_spec reward i
  exact hfeasible.2 none

/-- Even when every LP optimizer has zero hazard, strictly positive hazards
approach its value. This is an LP statement, before stopping-law realization. -/
theorem exists_deadlineWithdrawalSecurity_positive_approximation
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (error : ℝ) (herror : 0 < error) :
    ∃ hazard, 0 < hazard ∧
      DeadlineWithdrawalSecurityFeasible reward i hazard
        (deadlineWithdrawalSecurityValue reward i - error) := by
  obtain ⟨hazard, hfeasible, _⟩ := deadlineWithdrawalSecurityValue_spec reward i
  by_cases hpositive : 0 < hazard
  · refine ⟨hazard, hpositive, hfeasible.1, ?_⟩
    intro row
    exact (sub_le_self _ herror.le).trans (hfeasible.2 row)
  have hzero : hazard = 0 := le_antisymm (le_of_not_gt hpositive) hfeasible.1.1
  subst hazard
  have hcontinuous :=
    (continuous_deadlineWithdrawalSecurityEnvelope reward i).continuousAt (x := 0)
  obtain ⟨radius, hradius, hnear⟩ := Metric.continuousAt_iff.mp hcontinuous error herror
  let positiveHazard : ℝ := min 1 (radius / 2)
  have hpos : 0 < positiveHazard := lt_min zero_lt_one (by positivity)
  have hle : positiveHazard ≤ 1 := min_le_left _ _
  have hsmall : positiveHazard < radius :=
    (min_le_right _ _).trans_lt (by linarith)
  have hdist : dist positiveHazard 0 < radius := by
    simpa [Real.dist_eq, abs_of_pos hpos] using hsmall
  have hclose := hnear hdist
  rw [Real.dist_eq] at hclose
  have hlower := (abs_lt.mp hclose).1
  have hvalue : deadlineWithdrawalSecurityValue reward i ≤
      deadlineWithdrawalSecurityEnvelope reward i 0 :=
    (deadlineWithdrawalSecurity_le_envelope_iff reward i 0 _).mpr hfeasible.2
  refine ⟨positiveHazard, hpos, ⟨hpos.le, hle⟩, ?_⟩
  apply (deadlineWithdrawalSecurity_le_envelope_iff reward i positiveHazard _).mp
  linarith

/-- Terminal security improvement. Its actual-plan interpretation still
requires the positive-hazard approximation and restart adapters. -/
def deadlineWithdrawalSecurityFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) : ℝ :=
  max (deadlineWithdrawalZeroFloor reward i) (deadlineWithdrawalSecurityValue reward i)

/-- A nonpositive feasible value at hazard zero is already below the Never
floor. In particular, zero LP hazards add no nonpositive security value. -/
theorem deadlineWithdrawalSecurity_zeroHazard_le_zeroFloor
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (value : ℝ) (hvalue : value ≤ 0)
    (hfeasible : DeadlineWithdrawalSecurityFeasible reward i 0 value) :
    value ≤ deadlineWithdrawalZeroFloor reward i := by
  classical
  unfold deadlineWithdrawalZeroFloor
  apply Finset.le_min'
  intro candidate hcandidate
  rcases Finset.mem_insert.mp hcandidate with hzero | hpassive
  · simpa [hzero] using hvalue
  · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hpassive
    simpa [deadlineWithdrawalSecurityRow] using hfeasible.2 (some B)

/-- An exact witness selection for the nonpositive improved floor: either
Never has sufficient passive rewards, or a positive feasible hazard does.
No limiting strategy is asserted to attain a positive terminal value. -/
theorem deadlineWithdrawalSecurity_nonpositive_witness
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) :
    min (deadlineWithdrawalSecurityFloor reward i) 0 ≤
        deadlineWithdrawalZeroFloor reward i ∨
      ∃ hazard, 0 < hazard ∧
        DeadlineWithdrawalSecurityFeasible reward i hazard
          (min (deadlineWithdrawalSecurityFloor reward i) 0) := by
  obtain ⟨hazard, hfeasible, _⟩ := deadlineWithdrawalSecurityValue_spec reward i
  by_cases hpassive : deadlineWithdrawalSecurityValue reward i ≤
      deadlineWithdrawalZeroFloor reward i
  · left
    simp only [deadlineWithdrawalSecurityFloor, max_eq_left hpassive]
    exact min_le_left _ _
  have hfloor : deadlineWithdrawalSecurityFloor reward i =
      deadlineWithdrawalSecurityValue reward i :=
    max_eq_right (le_of_not_ge hpassive)
  by_cases hpositive : 0 < hazard
  · right
    refine ⟨hazard, hpositive, hfeasible.1, ?_⟩
    intro row
    rw [hfloor]
    exact (min_le_left _ _).trans (hfeasible.2 row)
  have hzero : hazard = 0 := le_antisymm (le_of_not_gt hpositive) hfeasible.1.1
  subst hazard
  have hvalue : 0 < deadlineWithdrawalSecurityValue reward i := by
    by_contra h
    exact hpassive (deadlineWithdrawalSecurity_zeroHazard_le_zeroFloor reward i _
      (le_of_not_gt h) hfeasible)
  left
  rw [hfloor, min_eq_right hvalue.le]
  exact deadlineWithdrawalSecurity_zeroHazard_le_zeroFloor reward i 0 le_rfl
    ⟨hfeasible.1, fun row => hvalue.le.trans (hfeasible.2 row)⟩

end GameTheory
