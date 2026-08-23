/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Classification.Existence.PerfectSequenceExtraction
import UniformEquilibrium.Quitting.Classification.SoloExitPreferenceExistence

/-!
# A solo-exit preference screen on the terminal exploitability witness

`QuittingCappedJointExitUniformεExistence`, the existence law of Solan and
Vieille, *Quitting games*, Math. Oper. Res. 26 (2001), Theorem 1.2, is proved
in Lean by `quittingCappedJointExitUniformεExistence_holds` in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
The theorems below discharge it internally, so each is an unconditional
restriction on the terminal exploitability witness.

A counterexample table cannot satisfy both paper's two assumptions.  A table
already known to have unit solo exit therefore carries a strictly attractive
joint exit: some player is paid strictly more by a coalition it belongs to
than by its own solo exit.  This is a necessary condition on the reward table
alone, with no strategic content, and it is logically independent of the
terminal-gap consequences packaged in `QuittingTerminalExploitabilityWitness`.

The screen is a table condition, so it constrains only the table.  It says
nothing about which profiles a counterexample admits.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- No counterexample table satisfies both paper's two assumptions. -/
theorem not_unitSoloExit_and_cappedJointExit
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ¬ (QuittingUnitSoloExit reward ∧ QuittingCappedJointExit reward) := by
  rintro ⟨hunit, hcapped⟩
  exact witness.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_of_soloExitPreference hunit hcapped)

/-- A counterexample table with unit solo exit carries a strictly attractive
joint exit. -/
theorem strictJointExitAttraction_of_unitSoloExit
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hunit : QuittingUnitSoloExit reward) :
    QuittingStrictJointExitAttraction reward :=
  quittingStrictJointExitAttraction_of_unitSoloExit hunit
    fun hcapped ↦
      witness.not_unitSoloExit_and_cappedJointExit ⟨hunit, hcapped⟩

/-- A counterexample table with unit solo exit fails weak solo-exit
preference. -/
theorem not_weakSoloExitPreference_of_unitSoloExit
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hunit : QuittingUnitSoloExit reward) :
    ¬ QuittingWeakSoloExitPreference reward :=
  (not_quittingWeakSoloExitPreference_iff reward).2
    (witness.strictJointExitAttraction_of_unitSoloExit hunit)

end QuittingTerminalExploitabilityWitness

/-- A table with unit solo exit and capped joint exit is in no counterexample
regime. -/
theorem isEmpty_quittingTerminalExploitabilityWitness_of_cappedJointExit
    (hunit : QuittingUnitSoloExit reward)
    (hcapped : QuittingCappedJointExit reward) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  ⟨fun witness ↦
    witness.not_unitSoloExit_and_cappedJointExit ⟨hunit, hcapped⟩⟩

/-- **Scale-free form.**  A table with unit solo exit and weak solo-exit
preference is in no terminal exploitability witness.  Unit solo exit is not removable
here: it is what turns the scale-free preference into the paper's cap. -/
theorem isEmpty_quittingTerminalExploitabilityWitness_of_weakSoloExitPreference
    (hunit : QuittingUnitSoloExit reward)
    (hweak : QuittingWeakSoloExitPreference reward) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  isEmpty_quittingTerminalExploitabilityWitness_of_cappedJointExit hunit
    (quittingCappedJointExit_of_unitSoloExit hunit hweak)

end GameTheory
