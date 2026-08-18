import Literature.Papers.SolanAndVieille2001
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.SoloExitPreferenceScreen
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# Research consumption of the Solan--Vieille existence claim

The paper module states the equilibrium-existence half of Theorem 1.2 as an
open proposition.  This module consumes it as a screen on the quitting
counterexample regime: granting the claim, a counterexample table with unit
solo exit must pay some player strictly more for a joint exit than its own
solo exit pays it.

The source's own Section 3 table meets both assumptions, checked here.  The
resulting exclusion is not recorded, because
`GameTheory.SolanVieilleBoundary.boundaryReward_isEmpty_counterexampleRegime`
already excludes that table unconditionally; the assumption check is kept as
the agreement test between the screen and that independent exclusion.
-/

namespace Research.Literature.SolanAndVieille2001

open GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Conditional necessary condition.**  Granting the source claim, a
counterexample table with unit solo exit carries a strictly attractive joint
exit. -/
theorem strictJointExitAttraction_of_source_claim
    (hclaim :
      Literature.Papers.SolanAndVieille2001.UniformεEquilibriumUnderSoloExitAssumptionsClaim
        ι)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    (hunit : QuittingUnitSoloExit reward) :
    QuittingStrictJointExitAttraction reward :=
  regime.strictJointExitAttraction_of_unitSoloExit hclaim hunit

/-- **Conditional necessary condition, cap form.**  Granting the source claim,
no counterexample table satisfies both source assumptions. -/
theorem not_source_assumptions_of_source_claim
    (hclaim :
      Literature.Papers.SolanAndVieille2001.UniformεEquilibriumUnderSoloExitAssumptionsClaim
        ι)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ¬ (QuittingUnitSoloExit reward ∧ QuittingCappedJointExit reward) :=
  regime.not_unitSoloExit_and_cappedJointExit hclaim

/-- The source's Section 3 table satisfies both assumptions of the source's own
existence theorem, so that table is inside the theorem's scope and is not
evidence against it. -/
theorem boundaryReward_source_assumptions :
    QuittingUnitSoloExit SolanVieilleBoundary.boundaryReward ∧
      QuittingCappedJointExit SolanVieilleBoundary.boundaryReward :=
  ⟨SolanVieilleBoundary.boundaryReward_unitSoloExit,
    SolanVieilleBoundary.boundaryReward_cappedJointExit⟩

end Research.Literature.SolanAndVieille2001
