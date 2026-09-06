import UniformEquilibrium.Quitting.Terminal.PivotRepairUniformPayoffCharacterization
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuCompletion

/-! # Canonical finite-menu scalar selection and nonpivot-law LP selection -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The existing canonical finite-menu source shape: one actual law controls
both menu exploitability and the exceptional pivot late-response scalar.
The displayed deadline may be zero; no exact menu Nash premise is imposed. -/
def HasSinglePivotFiniteMenuScalarSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) : Prop :=
  letI : Nonempty ι := ⟨pivot⟩
  ∀ error : ℝ, 0 < error →
    ∃ deadline : ℕ, ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      quittingFiniteDeadlineMenuExploitability reward deadline mixed ≤ error ∧
      quittingFiniteDeadlineNeverPayoff reward deadline mixed pivot +
          quittingFiniteDeadlineOpponentNeverProduct deadline mixed pivot -
          quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) pivot ≤ error

/-- Full finite-menu error control gives both canonical source inequalities
on the very same actual menu profile. -/
theorem singlePivotFiniteMenuScalarSource_of_fullEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) :
    letI : Nonempty ι := ⟨pivot⟩
    HasQuittingFiniteMenuFullEarlyAbsorption reward →
      HasSinglePivotFiniteMenuScalarSource reward pivot := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hsource error herror
  obtain ⟨deadline, _, mixed, hexploit, _⟩ := hsource error herror 1 le_rfl 1 zero_lt_one 1
  refine ⟨deadline, mixed, ?_, ?_⟩
  · have hmax := hexploit.le
    rw [singlePivot_fullExploitability_eq_max_menuExploitability_scalar
      reward pivot hcanonical deadline mixed] at hmax
    exact (le_max_left _ _).trans hmax
  · have hmax := hexploit.le
    rw [singlePivot_fullExploitability_eq_max_menuExploitability_scalar
      reward pivot hcanonical deadline mixed] at hmax
    exact (le_max_right _ _).trans hmax

/-- For a canonical table the actual finite-menu scalar source is equivalent
to selecting only nonpivot laws with arbitrarily small inner-LP value.
For Fin4 this eliminates the pivot from the remaining three-law outer source. -/
theorem singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) :
    HasSinglePivotFiniteMenuScalarSource reward pivot ↔
      HasQuittingSmallPivotRepairValue reward pivot := by
  letI : Nonempty ι := ⟨pivot⟩
  constructor
  · intro hsource
    obtain ⟨target, huniform⟩ :=
      exists_uniformEquilibriumPayoff_of_singlePivot_finiteMenu_scalar_source
        reward pivot hcanonical hsource
    exact smallPivotRepairValue_of_uniformEquilibriumPayoff reward pivot target huniform
  · intro hsource
    have hpositive : 0 < reward (quittingSingletonTerminal pivot) pivot := by
      rw [hcanonical pivot, if_pos rfl]
      exact zero_lt_one
    exact singlePivotFiniteMenuScalarSource_of_fullEarlyAbsorption reward pivot hcanonical
      (finiteMenuFullEarlyAbsorption_of_smallPivotRepairValue reward pivot hpositive hsource)

/-- The canonical finite-menu scalar source and full finite-menu early
absorption source are equivalent, without selecting either source universally. -/
theorem singlePivotFiniteMenuScalarSource_iff_fullEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot) :
    letI : Nonempty ι := ⟨pivot⟩
    HasSinglePivotFiniteMenuScalarSource reward pivot ↔
      HasQuittingFiniteMenuFullEarlyAbsorption reward := by
  letI : Nonempty ι := ⟨pivot⟩
  have hpositive : 0 < reward (quittingSingletonTerminal pivot) pivot := by
    rw [hcanonical pivot, if_pos rfl]
    exact zero_lt_one
  exact (singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue reward pivot hcanonical).trans
    (smallPivotRepairValue_iff_finiteMenuFullEarlyAbsorption reward pivot hpositive)

end GameTheory
