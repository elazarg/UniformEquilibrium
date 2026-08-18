/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Classification.SoloExitPreferenceExistence

/-!
# A solo-exit preference screen on the counterexample regime

Everything in this module is conditional on
`QuittingCappedJointExitUniformεExistence`, an open proposition stating the
existence law of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Theorem 1.2.  Nothing here proves that law, and
nothing here is an unconditional restriction on the counterexample regime.

Granting the law, a counterexample table cannot satisfy both source
assumptions.  A table already known to have unit solo exit therefore carries a
strictly attractive joint exit: some player is paid strictly more by a
coalition it belongs to than by its own solo exit.  This is a necessary
condition on the reward table alone, with no strategic content, and it is
logically independent of the terminal-gap consequences packaged in
`QuittingCounterexampleRegime`.

The screen is a table condition, so it constrains only the table.  It says
nothing about which profiles a counterexample admits.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- **Conditional.**  Granting the existence law, no counterexample table
satisfies both source assumptions. -/
theorem not_unitSoloExit_and_cappedJointExit
    (hlaw : QuittingCappedJointExitUniformεExistence ι)
    (regime : QuittingCounterexampleRegime reward) :
    ¬ (QuittingUnitSoloExit reward ∧ QuittingCappedJointExit reward) := by
  rintro ⟨hunit, hcapped⟩
  exact regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_of_cappedJointExit hlaw hunit hcapped)

/-- **Conditional.**  Granting the existence law, a counterexample table with
unit solo exit carries a strictly attractive joint exit. -/
theorem strictJointExitAttraction_of_unitSoloExit
    (hlaw : QuittingCappedJointExitUniformεExistence ι)
    (regime : QuittingCounterexampleRegime reward)
    (hunit : QuittingUnitSoloExit reward) :
    QuittingStrictJointExitAttraction reward :=
  quittingStrictJointExitAttraction_of_unitSoloExit hunit
    fun hcapped ↦
      regime.not_unitSoloExit_and_cappedJointExit hlaw ⟨hunit, hcapped⟩

/-- **Conditional.**  Granting the existence law, a counterexample table with
unit solo exit fails weak solo-exit preference. -/
theorem not_weakSoloExitPreference_of_unitSoloExit
    (hlaw : QuittingCappedJointExitUniformεExistence ι)
    (regime : QuittingCounterexampleRegime reward)
    (hunit : QuittingUnitSoloExit reward) :
    ¬ QuittingWeakSoloExitPreference reward :=
  (not_quittingWeakSoloExitPreference_iff reward).2
    (regime.strictJointExitAttraction_of_unitSoloExit hlaw hunit)

end QuittingCounterexampleRegime

/-- **Conditional exclusion.**  Granting the existence law, a table with unit
solo exit and capped joint exit is in no counterexample regime. -/
theorem isEmpty_quittingCounterexampleRegime_of_cappedJointExit
    (hlaw : QuittingCappedJointExitUniformεExistence ι)
    (hunit : QuittingUnitSoloExit reward)
    (hcapped : QuittingCappedJointExit reward) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime ↦
    regime.not_unitSoloExit_and_cappedJointExit hlaw ⟨hunit, hcapped⟩⟩

/-- **Conditional exclusion, scale-free form.**  Granting the existence law, a
table with unit solo exit and weak solo-exit preference is in no counterexample
regime.  Unit solo exit is not removable here: it is what turns the scale-free
preference into the source's cap. -/
theorem isEmpty_quittingCounterexampleRegime_of_weakSoloExitPreference
    (hlaw : QuittingCappedJointExitUniformεExistence ι)
    (hunit : QuittingUnitSoloExit reward)
    (hweak : QuittingWeakSoloExitPreference reward) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_cappedJointExit hlaw hunit
    (quittingCappedJointExit_of_unitSoloExit hunit hweak)

end GameTheory
