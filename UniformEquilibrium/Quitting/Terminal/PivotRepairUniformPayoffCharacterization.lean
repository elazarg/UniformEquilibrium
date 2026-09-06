import UniformEquilibrium.Quitting.Terminal.PivotRepairSmallValueConsumer
import UniformEquilibrium.Quitting.Terminal.FiniteMenuFullProfileApproximation

/-! # The actual small-repair source characterizes fixed uniform payoff existence -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A fixed uniform payoff target supplies arbitrarily small actual
nonpivot-law inner LP values, for any distinguished pivot and signed table. -/
theorem smallPivotRepairValue_of_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (target : Payoff ι) (huniform : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    HasQuittingSmallPivotRepairValue reward pivot := by
  letI : Nonempty ι := ⟨pivot⟩
  intro error herror
  obtain ⟨deadline, hdeadline, mixed, hexploit, _⟩ :=
    (isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation
      reward target).mp huniform error herror 1
  have hpositive : 0 < deadline := by omega
  obtain ⟨mass, hmass, hobjective⟩ :=
    exists_pivotRepairMass_objective_le_finiteMenu_exploitability
      reward pivot deadline hpositive mixed
  refine ⟨deadline, hpositive,
    (fun who ↦ (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF),
    (fun who ↦ isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who)), mass, hmass, ?_⟩
  exact hobjective.trans_lt hexploit

/-- For every signed finite quitting game and distinguished pivot, selecting
arbitrarily small actual nonpivot-law repair values is equivalent to existence
of one fixed uniform-equilibrium payoff target. Neither side is asserted here. -/
theorem smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    HasQuittingSmallPivotRepairValue reward pivot ↔
      ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · exact exists_uniformEquilibriumPayoff_of_smallPivotRepairValue reward pivot
  · rintro ⟨target, huniform⟩
    exact smallPivotRepairValue_of_uniformEquilibriumPayoff reward pivot target huniform

end GameTheory
