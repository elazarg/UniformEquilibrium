import UniformEquilibrium.Quitting.Terminal.PivotRepairUniformPayoffCharacterization
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuCompletion

/-! # Canonical finite-menu scalar selection and nonpivot-law LP selection -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

omit [Fintype ι] in
theorem responderLaterReward_eq_zero_of_singlePivot
    (hcanonical : IsSinglePivotSingletonTable reward input.pivot)
    (responder : ι) (hne : responder ≠ input.pivot) :
    responderLaterReward (reward := reward) responder = 0 := by
  unfold responderLaterReward
  rw [hcanonical responder, if_neg hne]

/-- In a canonical single-pivot table the nonpivot limit endpoint is
literally the Never endpoint, so the third signed endpoint is redundant. -/
theorem responderLimitEndpoint_eq_neverEndpoint_of_singlePivot
    (hcanonical : IsSinglePivotSingletonTable reward input.pivot)
    (mass : PivotRepairMass input.deadline)
    (responder : ι) (hne : responder ≠ input.pivot) :
    input.responderLimitEndpoint mass responder =
      input.responderNeverEndpoint mass responder := by
  apply input.responderLimitEndpoint_eq_neverEndpoint_of_later_zero
  exact input.responderLaterReward_eq_zero_of_singlePivot hcanonical responder hne

/-- In a canonical single-pivot table the first late endpoint is the early
contribution plus the tie reward weighted by opponent survival and the first atom. -/
theorem responderFirstEndpoint_eq_of_singlePivot
    (hcanonical : IsSinglePivotSingletonTable reward input.pivot)
    (mass : PivotRepairMass input.deadline)
    (responder : ι) (hne : responder ≠ input.pivot) :
    input.responderFirstEndpoint mass responder =
      input.earlyContribution mass responder +
        input.otherNeverProduct responder * input.responderTieReward responder *
          pivotRepairFirstAtom mass := by
  unfold responderFirstEndpoint
  rw [input.responderLaterReward_eq_zero_of_singlePivot hcanonical responder hne]
  ring

/-- A supplied coordinate bound gives the canonical sharp `M alpha`
objective perturbation bound. -/
theorem abs_objective_withFirstAtom_sub_le_of_singlePivot_reward_bound
    (hcanonical : IsSinglePivotSingletonTable reward input.pivot)
    (mass : PivotRepairMass input.deadline) (firstAtom bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |input.objective (pivotRepairMassWithFirstAtom mass firstAtom) -
        input.objective mass| ≤
      bound * |firstAtom - pivotRepairFirstAtom mass| := by
  apply input.abs_objective_withFirstAtom_sub_le_of_reward_bound_of_later_zero
    mass firstAtom bound hreward
  intro responder hne
  exact input.responderLaterReward_eq_zero_of_singlePivot hcanonical responder hne

/-- A canonical boundary point admits actual laws with the same payoff and
the sharp `M alpha` error under any supplied coordinate reward bound. -/
theorem exists_law_boundary_approximation_of_singlePivot_reward_bound
    (hcanonical : IsSinglePivotSingletonTable reward input.pivot)
    (mass : PivotRepairMass input.deadline)
    (hfeasible : IsPivotRepairMassFeasible mass)
    (hzero : pivotRepairFirstAtom mass = 0) (firstAtom bound : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward
            (Function.update input.opponents input.pivot law)) ≤
        input.objective mass + bound * firstAtom ∧
      (law none).toReal = pivotRepairNever mass := by
  apply input.exists_law_boundary_approximation_of_reward_bound_of_later_zero
    mass hfeasible hzero firstAtom bound hpositive hle hreward
  intro responder hne
  exact input.responderLaterReward_eq_zero_of_singlePivot hcanonical responder hne

end QuittingPivotRepairLPInput

/-- The canonical finite-menu source shape: one actual law controls
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
