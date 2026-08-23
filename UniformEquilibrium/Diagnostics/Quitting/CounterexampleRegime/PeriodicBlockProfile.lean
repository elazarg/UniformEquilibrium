/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.UniformPayoffBridge
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Cycles.SoloPeriodicBlockCompiler

/-!
# Periodic block profiles against a terminal exploitability witness

The periodic-profile machinery of `UniformEquilibrium/Quitting/Cycles/` is
stated without reference to `QuittingTerminalExploitabilityWitness`.  This module reads
it against the regime, in both directions.

*Necessary conditions.*  A terminal exploitability witness leaves, against every periodic
cycle of Boolean product rows, some player a gain of at least the regime's
terminal gap over the cycle's on-path value.  The gain is measured by the exact
finite best-response statistic, by the supremum over all behavior deviations,
or by any solution of the max-linear response system, and the first two forms
use no absorption hypothesis on the cycle.

*Exclusions.*  A cycle whose best-response statistic never beats its on-path
value, and a table carrying a certified single-quitter or block periodic
profile, admit no regime at all.

## Main results

* `QuittingTerminalExploitabilityWitness.exists_quittingCyclicDeviationSup_gain`
* `QuittingTerminalExploitabilityWitness.exists_quittingCyclicResponse_gain`
* `QuittingTerminalExploitabilityWitness.exists_quittingBlockResponse_gain`
* `isEmpty_terminalExploitabilityWitness_of_quittingCyclicResponseCap_le`
* `isEmpty_terminalExploitabilityWitness_of_soloPeriodicBlock`
* `isEmpty_terminalExploitabilityWitness_of_isQuittingBlockCertificate`
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Periodic cycles of product rows -/

namespace QuittingTerminalExploitabilityWitness

/-- **Every periodic cycle is exposed at the full terminal gap.**  A
terminal exploitability witness leaves some player a gain of at least its terminal gap
over the cycle's on-path value, measured by the exact finite best-response
statistic. -/
theorem exists_quittingCyclicCap_gain
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) :
    ∃ who,
      quittingCyclicTerminalValue reward cycle phase who + witness.terminalGap ≤
        quittingCyclicResponseCap reward cycle phase who := by
  obtain ⟨who, hgain⟩ := witness.exists_periodicCap_gain
    (quittingCyclicBehaviorProfile reward cycle phase) (m + 1)
    (quittingProfileLiveRoot_cyclicBehaviorProfile_add_period reward cycle phase)
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_cyclicBehaviorProfile] at hgain
  rw [quittingCyclicResponseCap]
  rwa [quittingProfileLiveRoot_cyclicBehaviorProfile] at hgain

/-- **The periodic necessary condition.**  A terminal exploitability witness leaves some
player a behavior deviation against the periodic profile of `cycle` whose
supremum value beats the cycle's on-path value by at least the regime's
terminal gap.  No absorption hypothesis on the cycle is used. -/
theorem exists_quittingCyclicDeviationSup_gain
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1)) :
    ∃ who,
      quittingCyclicTerminalValue reward cycle phase who + witness.terminalGap ≤
        sSup (Set.range fun deviation : (quittingGame reward).BehaviorStrategy who ↦
          quittingTerminalPayoff reward
            (Function.update (quittingCyclicBehaviorProfile reward cycle phase) who
              deviation) who) := by
  obtain ⟨who, hgain⟩ := witness.exists_quittingCyclicCap_gain cycle phase
  exact ⟨who, by
    rwa [sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile]⟩

/-- **The same statement read through the max-linear system.**  If `W` solves
the response system and the cycle is admissible, a terminal exploitability witness forces
some player's response value to beat the on-path value by at least the terminal
gap. -/
theorem exists_quittingCyclicResponse_gain
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1))
    {W : Fin (m + 1) → Payoff ι}
    (hW : IsQuittingCyclicResponseSolution reward cycle W)
    (hadmissible : IsQuittingCycleAdmissible reward cycle) :
    ∃ who,
      quittingCyclicTerminalValue reward cycle phase who + witness.terminalGap ≤
        W phase who := by
  obtain ⟨who, hgain⟩ := witness.exists_quittingCyclicCap_gain cycle phase
  exact ⟨who, hgain.trans
    (quittingCyclicResponseCap_le_of_isQuittingCyclicResponseSolution hW phase who
      (hadmissible who))⟩

end QuittingTerminalExploitabilityWitness

/-- A cycle whose exact finite best-response statistic never beats its on-path
value rules out every terminal exploitability witness. -/
theorem isEmpty_terminalExploitabilityWitness_of_quittingCyclicResponseCap_le
    (cycle : Fin (m + 1) → ι → PMF Bool) (phase : Fin (m + 1))
    (hcap : ∀ who, quittingCyclicResponseCap reward cycle phase who ≤
      quittingCyclicTerminalValue reward cycle phase who) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) := by
  refine ⟨fun witness ↦ ?_⟩
  obtain ⟨who, hgain⟩ := witness.exists_quittingCyclicCap_gain cycle phase
  have hpos := witness.terminalGap_pos
  linarith [hcap who]

/-! ## Certified single-quitter periodic profiles -/

open SoloPeriodicBlockCompiler in
/-- A table carrying a certified single-quitter periodic profile lies in no
terminal exploitability witness. -/
theorem isEmpty_terminalExploitabilityWitness_of_soloPeriodicBlock
    {w : Fin (m + 1) → ι} {marginal : Fin (m + 1) → PMF Bool}
    {value : Fin (m + 2) → Payoff ι}
    (hcert : IsSoloPeriodicCertificate reward w marginal value) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  isEmpty_quittingTerminalExploitabilityWitness_of_exists_uniformEquilibriumPayoff _
    ⟨value 0, isUniformEquilibriumPayoff_of_soloPeriodicBlock hcert⟩

/-! ## Certified block periodic profiles -/

variable {hazard : Fin (m + 1) → ι → ℝ}

/-- A table carrying a certified block profile lies in no counterexample
regime. -/
theorem isEmpty_terminalExploitabilityWitness_of_isQuittingBlockCertificate
    {U : Fin (m + 2) → Payoff ι}
    (hcert : IsQuittingBlockCertificate reward hazard U) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  isEmpty_quittingTerminalExploitabilityWitness_of_exists_uniformEquilibriumPayoff _
    ⟨U 0, isUniformEquilibriumPayoff_of_isQuittingBlockCertificate hcert⟩

/-! ## The block necessary condition -/

namespace QuittingTerminalExploitabilityWitness

/-- **Every periodic block profile is exposed at the full terminal gap.**  A
terminal exploitability witness leaves some player a gain of at least its terminal gap
over the block profile's on-path value, measured by the exact finite
best-response statistic. -/
theorem exists_quittingBlockCap_gain
    (witness : QuittingTerminalExploitabilityWitness reward)
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (phase : Fin (m + 1)) {U : Fin (m + 1) → Payoff ι}
    (hU : IsQuittingBlockOnPathValue reward hazard U)
    (habsorb : (∏ k : Fin (m + 1), continueMass (hazard k)) < 1) :
    ∃ who, U phase who + witness.terminalGap ≤
      quittingCyclicResponseCap reward (quittingBlockCycle hazard h0 h1) phase
        who := by
  obtain ⟨who, hgain⟩ := witness.exists_quittingCyclicCap_gain
    (quittingBlockCycle hazard h0 h1) phase
  refine ⟨who, ?_⟩
  rwa [eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue_of_absorbing h0 h1 hU
    habsorb]

/-- **Every periodic block profile is exposed at the full terminal gap.**  A
terminal exploitability witness forces some player's response value to exceed the block
profile's on-path value by at least the regime's terminal gap. -/
theorem exists_quittingBlockResponse_gain
    (witness : QuittingTerminalExploitabilityWitness reward)
    (h0 : ∀ k i, 0 ≤ hazard k i) (h1 : ∀ k i, hazard k i ≤ 1)
    (phase : Fin (m + 1)) {U W : Fin (m + 1) → Payoff ι}
    (hU : IsQuittingBlockOnPathValue reward hazard U)
    (hW : IsQuittingBlockResponseSolution reward hazard W)
    (habsorb : (∏ k : Fin (m + 1), continueMass (hazard k)) < 1)
    (hadmissible : IsQuittingCycleAdmissible reward
      (quittingBlockCycle hazard h0 h1)) :
    ∃ who, U phase who + witness.terminalGap ≤ W phase who := by
  have hvalue := eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue_of_absorbing h0 h1
    hU habsorb
  obtain ⟨who, hgain⟩ := witness.exists_quittingCyclicResponse_gain
    (quittingBlockCycle hazard h0 h1) phase
    (isQuittingCyclicResponseSolution_of_isQuittingBlockResponseSolution h0 h1 hW)
    hadmissible
  refine ⟨who, ?_⟩
  rwa [hvalue]

end QuittingTerminalExploitabilityWitness

end GameTheory
