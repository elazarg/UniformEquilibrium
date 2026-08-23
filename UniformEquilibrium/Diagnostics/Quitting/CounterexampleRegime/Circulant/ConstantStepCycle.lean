/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicBlockProfile
import UniformEquilibrium.Quitting.Classification.Circulant.ConstantStepCycle

/-!
# Constant-step cyclic equilibria, against the terminal exploitability witness

`UniformEquilibrium/Quitting/Classification/Circulant/ConstantStepCycle.lean`
supplies the finite certificate of the constant-step cyclic profile without
reference to `QuittingTerminalExploitabilityWitness`.  This module reads it against the
regime, through `isEmpty_terminalExploitabilityWitness_of_soloPeriodicBlock`.

## Main results

* `isEmpty_terminalExploitabilityWitness_constantStep`
-/

noncomputable section

namespace GameTheory
namespace CirculantConstantStepCycle

variable {m J : ZMod 5 → ℝ} {c c' : ZMod 5} {q s : ℝ}
  {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}

/-- **A table with a constant-step cyclic equilibrium is in no counterexample
regime.** -/
theorem isEmpty_terminalExploitabilityWitness_constantStep
    (htable : IsCirculantPairTable reward s m J)
    (hcc' : c * c' = -1) (hs : 0 ≤ s)
    (h0 : 0 ≤ q) (h1 : q < 1) (hroot : stepAnchor m c q = 0)
    (hfloor₁ : J c ≤ 0)
    (hfloor₂ : J (2 * c) ≤ m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c))
    (hfloor₃ : J (3 * c) ≤ m (3 * c) + q * m (4 * c))
    (hfloor₄ : J (4 * c) ≤ m (4 * c)) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  isEmpty_terminalExploitabilityWitness_of_soloPeriodicBlock
    (isSoloPeriodicCertificate_constantStep htable hcc' hs h0 h1 hroot
      hfloor₁ hfloor₂ hfloor₃ hfloor₄)

end CirculantConstantStepCycle
end GameTheory
