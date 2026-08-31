import UniformEquilibrium.Quitting.Classification.Existence.ChronologicalTerminalJumpS2
import UniformEquilibrium.Quitting.Classification.Existence.SequentiallyPerfectAbsorptionPathS3

/-!
# The actual chronological absorption path enters S.2 or S.3

This is only the terminal/no-terminal dispatch.  It assumes the existing
chronological limit source; the upstream stationary-versus-vanishing-Never
selector remains separate.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

/-- The actual chronological source enters literal S.2 or S.3 according to
whether its absorption path has a terminal total jump. -/
theorem instantPunishment_or_wellSupportedAbsorbingSequenceExistence
    (limit : diagonal.ChronologicalLimit) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward := by
  classical
  by_cases hnoTerminalJump :
      QuittingAbsorptionPath.HasNoTerminalTotalJump limit.absorptionPath
  · exact Or.inr
      (limit.wellSupportedAbsorbingSequenceExistence_of_noTerminalTotalJump
        hnoTerminalJump)
  · left
    simp only [QuittingAbsorptionPath.HasNoTerminalTotalJump, not_forall,
      not_lt] at hnoTerminalJump
    obtain ⟨time, htime, hone⟩ := hnoTerminalJump
    apply limit.instantPunishmentEquilibriumExistence_of_terminalPathJump htime
    exact le_antisymm (limit.pathTotal_le_one time htime.1) hone

end ChronologicalLimit
end QuittingRootSequenceAbsorbingCompletionDiagonal
end GameTheory
