/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SoloExitPreference
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# The existence law carried by the two solo-exit source assumptions

`QuittingCappedJointExitUniformεExistence` states the quitting existence
theorem of Solan and Vieille, *Quitting games*, Math. Oper. Res. 26 (2001),
Theorem 1.2, in this development's semantics.  It is proved in Lean by
`quittingCappedJointExitUniformεExistence_holds` in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.

Its conclusion is the source's, namely a uniform `ε`-equilibrium for each
positive `ε`, with the profile and its payoff vector free to move with `ε`.
That is weaker than one fixed uniform-equilibrium payoff, which is the notion
the quitting conjecture and the terminal exploitability witness are stated at.  For
finite quitting games the two are nonetheless equivalent, by
`quittingGame_exists_uniformEquilibriumPayoff_iff_uniformεEquilibrium_all_errors`;
`exists_uniformEquilibriumPayoff_of_cappedJointExit` is that bridge applied to
the law, and is conditional on the law alone.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every finite quitting game with unit solo exit and capped joint exit has
a uniform `ε`-equilibrium at every positive `ε`.

This is the conclusion of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Theorem 1.2, restricted to the profile-level
equilibrium property and dropping the source's additional cyclic
subgame-perfection.  It is proved in Lean by
`quittingCappedJointExitUniformεExistence_holds` in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`. -/
def QuittingCappedJointExitUniformεExistence
    (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
    QuittingUnitSoloExit reward → QuittingCappedJointExit reward →
      ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsUniformεEquilibrium none ε profile

/-- **Conditional.**  Granting the existence law, a table with unit solo exit
and capped joint exit has one fixed uniform-equilibrium payoff.

The law delivers a profile per error, with no fixed payoff target; the
quitting notion-alignment equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_uniformεEquilibrium_all_errors`
is what supplies the single target. -/
theorem exists_uniformEquilibriumPayoff_of_cappedJointExit
    (hlaw : QuittingCappedJointExitUniformεExistence ι)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcapped : QuittingCappedJointExit reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_uniformεEquilibrium_all_errors
    reward (hlaw reward hunit hcapped)

end GameTheory
