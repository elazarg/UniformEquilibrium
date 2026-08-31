/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.NormalSequentiallyPerfectAbsorbingUniformPayoff
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual

/-!
# Fin4 normal sequentially perfect absorbing source compiler

A quantitative Fin4 full-support hard residual supplies the all-player
punishment normality consumed by the generic delayed-switch compiler. The
source sequence remains an explicit hypothesis: the residual does not produce
a sequentially perfect or well-supported completely absorbing source.
-/

noncomputable section

namespace GameTheory

namespace FinFourQuantitativeFullSupportHardResidual

/-- A four-player full-support hard residual carrying branch S.3 has a
uniform-equilibrium payoff, because the residual supplies the all-player
punishment normality required by the dimension-free delayed-switch compiler. -/
theorem exists_uniformEquilibriumPayoff_of_sequentiallyPerfectAbsorbing
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hS3 : QuittingSequentiallyεPerfectAbsorbingExistence reward) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing
    reward residual.all_punishmentNormal hS3

/-- A Fin4 full-support hard residual with a well-supported completely
absorbing source has terminal approximate Nash profiles at every error. -/
theorem exists_terminalNash_of_wellSupportedAbsorbing
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hwellSupported : QuittingWellSupportedAbsorbingSequenceExistence reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile :=
  exists_terminalNash_of_all_normal_of_wellSupportedAbsorbing
    reward residual.all_punishmentNormal hwellSupported hε

/-- A Fin4 full-support hard residual with the equivalent well-supported
source has a fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_wellSupportedAbsorbing
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hwellSupported : QuittingWellSupportedAbsorbingSequenceExistence reward) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_all_normal_of_wellSupportedAbsorbing
    reward residual.all_punishmentNormal hwellSupported

/-- In the explicit no-uniform-payoff branch, the same Fin4 residual cannot
also carry branch S.3.  The no-payoff premise is kept literal because it is
not a field of `FinFourQuantitativeFullSupportHardResidual`. -/
theorem not_sequentiallyPerfectAbsorbing_of_no_uniformEquilibriumPayoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ QuittingSequentiallyεPerfectAbsorbingExistence reward := by
  intro hS3
  exact hnot (residual.exists_uniformEquilibriumPayoff_of_sequentiallyPerfectAbsorbing hS3)

/-- In the explicit no-uniform-payoff branch, a Fin4 full-support hard residual
cannot carry the equivalent well-supported completely absorbing source. -/
theorem not_wellSupportedAbsorbing_of_no_uniformEquilibriumPayoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ QuittingWellSupportedAbsorbingSequenceExistence reward := by
  intro hwellSupported
  exact hnot (residual.exists_uniformEquilibriumPayoff_of_wellSupportedAbsorbing
    hwellSupported)

end FinFourQuantitativeFullSupportHardResidual

end GameTheory

