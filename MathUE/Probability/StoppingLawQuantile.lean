import MathUE.Probability.StoppingLawReconstruction

/-! # First finite quantiles of complete stopping laws

This file isolates the quantile facts used for the sure-anchor concentration
argument. The stopping law may have unbounded finite support and Never mass,
and the selected date may be zero.
-/

noncomputable section

namespace Math.Probability.DiscreteHazard.StoppingLaw

open Filter

/-- A complete stopping law whose Never mass lies strictly below a threshold
eventually has survival below that threshold. -/
theorem exists_survival_succ_le_of_none_lt
    (law : PMF (Option ℕ)) {threshold : ℝ}
    (hnone : (law none).toReal < threshold) :
    ∃ time, survival law (time + 1) ≤ threshold := by
  have heventually : ∀ᶠ cutoff in atTop, survival law cutoff < threshold :=
    (tendsto_order.1 (tendsto_survival_none law)).2 threshold hnone
  obtain ⟨cutoff, hcutoff⟩ := (eventually_atTop.1 heventually)
  have hselected := hcutoff cutoff le_rfl
  exact ⟨cutoff,
    (survival_antitone law (Nat.le_add_right cutoff 1)).trans hselected.le⟩

/-- First date whose inclusive cumulative stopping mass reaches
`1 - threshold`, expressed through survival after that date. -/
def firstFiniteQuantileIndex
    (law : PMF (Option ℕ)) (threshold : ℝ)
    (hexists : ∃ time, survival law (time + 1) ≤ threshold) : ℕ :=
  Nat.find hexists

theorem survival_succ_firstFiniteQuantileIndex_le
    (law : PMF (Option ℕ)) (threshold : ℝ)
    (hexists : ∃ time, survival law (time + 1) ≤ threshold) :
    survival law (firstFiniteQuantileIndex law threshold hexists + 1) ≤ threshold := by
  exact Nat.find_spec hexists

/-- Minimality gives strictly more than threshold mass surviving to the
selected date, including when that date is zero. -/
theorem threshold_lt_survival_firstFiniteQuantileIndex
    (law : PMF (Option ℕ)) {threshold : ℝ} (hthreshold : threshold < 1)
    (hexists : ∃ time, survival law (time + 1) ≤ threshold) :
    threshold < survival law (firstFiniteQuantileIndex law threshold hexists) := by
  let index := firstFiniteQuantileIndex law threshold hexists
  change threshold < survival law index
  cases hindex : index with
  | zero =>
      rw [survival_zero]
      exact hthreshold
  | succ previous =>
      have hprevious : previous < index := by omega
      have hminimal := Nat.find_min hexists hprevious
      change ¬survival law (previous + 1) ≤ threshold at hminimal
      exact lt_of_not_ge hminimal

/-- A single selected date has both the inclusive upper-tail bound and the
strict pre-date survival lower bound. -/
theorem exists_firstFiniteQuantile_bounds
    (law : PMF (Option ℕ)) {threshold : ℝ}
    (hnone : (law none).toReal < threshold) (hthreshold : threshold < 1) :
    ∃ time, survival law (time + 1) ≤ threshold ∧
      threshold < survival law time := by
  let hexists := exists_survival_succ_le_of_none_lt law hnone
  exact ⟨firstFiniteQuantileIndex law threshold hexists,
    survival_succ_firstFiniteQuantileIndex_le law threshold hexists,
    threshold_lt_survival_firstFiniteQuantileIndex law hthreshold hexists⟩

/-- The mass strictly before a cutoff is the complement of survival there. -/
theorem sum_finiteMass_range_eq_one_sub_survival
    (law : PMF (Option ℕ)) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, finiteMass law time) =
      1 - survival law cutoff := by
  unfold survival
  ring

/-- An independent crossing-event bound controls another clock's mass before
the selected quantile date. -/
theorem beforeMass_le_error_div_of_crossing_le
    (active anchor : PMF (Option ℕ)) (time : ℕ) {error threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hanchor : threshold < survival anchor time)
    (hcrossing :
      (∑ date ∈ Finset.range time, finiteMass active date) *
          survival anchor time ≤ error) :
    (∑ date ∈ Finset.range time, finiteMass active date) ≤ error / threshold := by
  have hbefore : 0 ≤ ∑ date ∈ Finset.range time, finiteMass active date :=
    Finset.sum_nonneg fun date _ => finiteMass_nonneg active date
  rw [le_div_iff₀ hthreshold]
  calc
    (∑ date ∈ Finset.range time, finiteMass active date) * threshold =
        threshold * (∑ date ∈ Finset.range time, finiteMass active date) := by ring
    _ ≤
        survival anchor time *
          (∑ date ∈ Finset.range time, finiteMass active date) := by
      exact mul_le_mul_of_nonneg_right hanchor.le hbefore
    _ = (∑ date ∈ Finset.range time, finiteMass active date) *
          survival anchor time := by ring
    _ ≤ error := hcrossing

/-- At the square-root scale, the same crossing estimate bounds the active
clock's pre-date mass by the threshold itself. -/
theorem beforeMass_le_threshold_of_crossing_le
    (active anchor : PMF (Option ℕ)) (time : ℕ) {error threshold : ℝ}
    (hthreshold : 0 < threshold)
    (herror : error ≤ threshold ^ 2)
    (hanchor : threshold < survival anchor time)
    (hcrossing :
      (∑ date ∈ Finset.range time, finiteMass active date) *
          survival anchor time ≤ error) :
    (∑ date ∈ Finset.range time, finiteMass active date) ≤ threshold := by
  have hbound := beforeMass_le_error_div_of_crossing_le
    active anchor time hthreshold hanchor hcrossing
  calc
    (∑ date ∈ Finset.range time, finiteMass active date) ≤
        error / threshold := hbound
    _ ≤ threshold := by
      rw [div_le_iff₀ hthreshold]
      nlinarith

end Math.Probability.DiscreteHazard.StoppingLaw
