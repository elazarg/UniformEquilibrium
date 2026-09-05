import MathUE.ProbabilityMassFunction.StoppingLawFiniteTail

/-! # Censoring late finite stopping atoms to Never -/

noncomputable section

namespace Math.Probability

/-- Keep finite stopping dates through `horizon` and send every later finite
date to `Never`. The original `Never` outcome is retained. -/
def censorLateFiniteStoppingOutcome (horizon : ℕ) : Option ℕ → Option ℕ
  | none => none
  | some time => if time ≤ horizon then some time else none

/-- Censor only the late finite atoms of a complete stopping law. -/
def censorLateFiniteStoppingLaw (law : PMF (Option ℕ)) (horizon : ℕ) :
    PMF (Option ℕ) :=
  law.map (censorLateFiniteStoppingOutcome horizon)

@[simp] theorem censorLateFiniteStoppingLaw_apply_some_of_le
    (law : PMF (Option ℕ)) {horizon time : ℕ} (htime : time ≤ horizon) :
    censorLateFiniteStoppingLaw law horizon (some time) = law (some time) := by
  classical
  rw [censorLateFiniteStoppingLaw, PMF.map_apply, tsum_eq_single (some time)]
  · simp [censorLateFiniteStoppingOutcome, htime]
  · intro choice hchoice
    cases choice with
    | none => simp [censorLateFiniteStoppingOutcome]
    | some other =>
        by_cases hother : other ≤ horizon
        · have hotherNe : other ≠ time := by
            intro heq
            subst other
            exact hchoice rfl
          rw [if_neg]
          intro heq
          rw [censorLateFiniteStoppingOutcome, if_pos hother] at heq
          exact hotherNe (Option.some.inj heq).symm
        · simp [censorLateFiniteStoppingOutcome, hother]

theorem censorLateFiniteStoppingLaw_support_subset
    (law : PMF (Option ℕ)) (horizon : ℕ) :
    (censorLateFiniteStoppingLaw law horizon).support ⊆
      ↑(stoppingLawFinitePrefix horizon) := by
  intro outcome houtcome
  obtain ⟨source, _hsource, rfl⟩ :=
    (PMF.mem_support_map_iff
      (censorLateFiniteStoppingOutcome horizon) law outcome).1 houtcome
  cases source with
  | none => simp [censorLateFiniteStoppingOutcome]
  | some time =>
      by_cases htime : time ≤ horizon
      · simp [censorLateFiniteStoppingOutcome, htime]
      · simp [censorLateFiniteStoppingOutcome, htime]

theorem censorLateFiniteStoppingLaw_none_ge
    (law : PMF (Option ℕ)) (horizon : ℕ) :
    (law none).toReal ≤
      (censorLateFiniteStoppingLaw law horizon none).toReal := by
  classical
  have hne : censorLateFiniteStoppingLaw law horizon none ≠ ⊤ :=
    PMF.apply_ne_top _ _
  rw [censorLateFiniteStoppingLaw, PMF.map_apply] at hne ⊢
  apply ENNReal.toReal_mono
  · exact hne
  · convert ENNReal.le_tsum
      (f := fun choice : Option ℕ =>
        if none = censorLateFiniteStoppingOutcome horizon choice then law choice else 0)
      none using 1
    · simp [censorLateFiniteStoppingOutcome]
    · apply tsum_congr
      intro choice
      split <;> rfl

/-- Censoring late finite atoms costs at most their total mass in general
total variation. -/
theorem pmfGeneralTV_censorLateFiniteStoppingLaw_le
    (law : PMF (Option ℕ)) (horizon : ℕ) :
    pmfGeneralTV law (censorLateFiniteStoppingLaw law horizon) ≤
      stoppingLawLateFiniteMass law horizon := by
  let overlap : Option ℕ → ℝ := fun outcome =>
    min ((law outcome).toReal)
      ((censorLateFiniteStoppingLaw law horizon outcome).toReal)
  have hoverlapSummable : Summable overlap := by
    exact Summable.of_nonneg_of_le
      (fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun _ => min_le_left _ _) (pmf_toReal_summable law)
  have hprefixOverlap :
      ∑ outcome ∈ stoppingLawFinitePrefix horizon, overlap outcome =
        1 - stoppingLawLateFiniteMass law horizon := by
    have hpoint : ∀ outcome ∈ stoppingLawFinitePrefix horizon,
        overlap outcome = (law outcome).toReal := by
      intro outcome houtcome
      have hle : (law outcome).toReal ≤
          ((censorLateFiniteStoppingLaw law horizon) outcome).toReal := by
        rcases outcome with _ | time
        · exact censorLateFiniteStoppingLaw_none_ge law horizon
        · rw [censorLateFiniteStoppingLaw_apply_some_of_le law]
          exact (some_mem_stoppingLawFinitePrefix horizon time).1 houtcome
      exact min_eq_left hle
    rw [Finset.sum_congr rfl hpoint]
    simp [stoppingLawLateFiniteMass, pmfFiniteComplementMass]
  have hfinite := hoverlapSummable.sum_le_tsum
    (stoppingLawFinitePrefix horizon)
    (fun _ _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  rw [hprefixOverlap] at hfinite
  unfold pmfGeneralTV overlap at *
  linarith

end Math.Probability
