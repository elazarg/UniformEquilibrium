import UniformEquilibrium.Quitting.Terminal.PivotRepairSourceCompression
import UniformEquilibrium.Quitting.Terminal.TerminalProfileFiniteEarlyAbsorption

/-! # The remaining outer selection source has only nonpivot laws -/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPivotRepairLPInput

/-- Build the actual inner LP from just the nonpivot marginals. The unused
pivot coordinate is fixed to Never, not selected by the outer source. -/
def ofNonpivotLaws (pivot : ι) (deadline : ℕ) (hdeadline : 0 < deadline)
    (opponents : {who : ι // who ≠ pivot} → PMF (Option ℕ))
    (hfinite : ∀ who, IsFiniteClockStoppingLaw deadline (opponents who)) :
    QuittingPivotRepairLPInput reward where
  opponents who := if hwho : who = pivot then PMF.pure none else opponents ⟨who, hwho⟩
  pivot := pivot
  deadline := deadline
  deadline_pos := hdeadline
  opponents_finite who hwho := by simpa only [dif_neg hwho] using hfinite ⟨who, hwho⟩

end QuittingPivotRepairLPInput

/-- The unresolved outer source: select only finite nonpivot laws so that
some feasible inner-LP point has arbitrarily small objective. For Fin4 this
selects three actual marginal laws. No vanishing-value producer is assumed. -/
def HasQuittingSmallPivotRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) : Prop :=
  ∀ error : ℝ, 0 < error →
    ∃ (deadline : ℕ) (hdeadline : 0 < deadline)
      (opponents : {who : ι // who ≠ pivot} → PMF (Option ℕ))
      (hfinite : ∀ who, IsFiniteClockStoppingLaw deadline (opponents who)),
      ∃ mass : PivotRepairMass deadline, IsPivotRepairMassFeasible mass ∧
        (QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
          pivot deadline hdeadline opponents hfinite).objective mass < error

omit [Fintype ι] [DecidableEq ι] in
theorem isFiniteClockStoppingLaw_finiteDeadlineTimingLaw
    {deadline : ℕ} (mixed : PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    IsFiniteClockStoppingLaw deadline (quittingFiniteDeadlineTimingLaw mixed).toPMF := by
  intro choice hchoice
  cases choice with
  | none => exact Or.inl rfl
  | some time =>
      refine Or.inr ⟨time, ?_, rfl⟩
      by_contra htime
      exact hchoice (quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le mixed (by omega))

/-- A single actual finite-menu law with small full exploitability supplies
an inner-LP point with no larger value for its actual nonpivot marginals. -/
theorem exists_pivotRepairMass_objective_le_finiteMenu_exploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    letI : Nonempty ι := ⟨pivot⟩
    let opponents := fun who : {who : ι // who ≠ pivot} ↦
      (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
    let hfinite := fun who : {who : ι // who ≠ pivot} ↦
      isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who)
    ∃ mass : PivotRepairMass deadline, IsPivotRepairMassFeasible mass ∧
      (QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
        pivot deadline hdeadline opponents hfinite).objective mass ≤
        quittingTerminalExploitability reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  letI : Nonempty ι := ⟨pivot⟩
  dsimp only
  let input := QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
    pivot deadline hdeadline
    (fun who : {who : ι // who ≠ pivot} ↦ (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF)
    (fun who ↦ isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who))
  obtain ⟨mass, hmass, _, hobjective⟩ :=
    input.exists_feasible_mass_payoff_eq_and_objective_le
      (quittingFiniteDeadlineTimingLaw (mixed pivot)).toPMF
  refine ⟨mass, hmass, ?_⟩
  have hlaws : Function.update input.opponents input.pivot
      (quittingFiniteDeadlineTimingLaw (mixed pivot)).toPMF =
      fun who ↦ (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF := by
    funext who
    by_cases hwho : who = pivot
    · subst who
      simp [input, QuittingPivotRepairLPInput.ofNonpivotLaws]
    · simp [input, QuittingPivotRepairLPInput.ofNonpivotLaws, hwho]
  rw [hlaws] at hobjective
  have hprofile := finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws reward deadline mixed
    (fun who ↦ (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF) (fun _ ↦ rfl)
  rwa [← hprofile] at hobjective

/-- The full finite-menu early-absorption source in particular produces
arbitrarily small values of the actual nonpivot-law inner LP. -/
theorem smallPivotRepairValue_of_finiteMenuFullEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    letI : Nonempty ι := ⟨pivot⟩
    HasQuittingFiniteMenuFullEarlyAbsorption reward → HasQuittingSmallPivotRepairValue reward pivot := by
  letI : Nonempty ι := ⟨pivot⟩
  intro hsource error herror
  obtain ⟨deadline, hdeadline, mixed, hexploit, _⟩ :=
    hsource error herror 1 le_rfl 1 zero_lt_one 1
  have hpositive : 0 < deadline := by omega
  obtain ⟨mass, hmass, hobjective⟩ :=
    exists_pivotRepairMass_objective_le_finiteMenu_exploitability
      reward pivot deadline hpositive mixed
  refine ⟨deadline, hpositive,
    (fun who ↦ (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF),
    (fun who ↦ isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who)), mass, hmass, ?_⟩
  exact hobjective.trans_lt hexploit

end GameTheory
