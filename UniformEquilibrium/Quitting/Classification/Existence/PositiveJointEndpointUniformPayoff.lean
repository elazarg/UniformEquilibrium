/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointPrefixReachEndpoint
import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier

/-!
# Uniform payoff at a positive-joint punishment endpoint

A reached positive-joint punishment endpoint has zero terminal-semantic debt,
so its prescribed payoff and best-response envelope agree.  Since the
endpoint belongs to the literal terminal-semantic carrier, this diagonal
point is an actual uniform-equilibrium payoff target.

This identifies the endpoint's prescribed coordinate as a specific
uniform-equilibrium payoff target without using its exact-prefix orbit or a
summability assumption.  Source-level uniform-payoff existence was already
available from the source's approximate-equilibrium family and the generic
compiler.  This result does not place the source in one of the stationary,
instant-punishment, or absorbing sequentially perfect branches of AGKRS
Theorem 3.4.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- A reached diagonal punishment endpoint is an actual uniform-equilibrium
payoff target. -/
theorem
    QuittingPositiveJointPrefixReachPunishmentEndpoint.isUniformEquilibriumPayoff
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none endpoint.endpoint.1 := by
  letI : Nonempty iota := ⟨endpoint.punished⟩
  apply isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
  have hdiagonal : endpoint.endpoint =
      (endpoint.endpoint.1, endpoint.endpoint.1) := by
    apply Prod.ext
    · rfl
    · funext who
      exact (endpoint.payoff_eq_envelope who).symm
  rw [← hdiagonal]
  exact endpoint.endpoint_mem

/-- Every positive-joint prefix-reach source therefore supplies an actual
uniform-equilibrium payoff, independently of the endpoint's exact-prefix
charge behavior. -/
theorem QuittingPositiveJointPrefixReachSource.exists_uniformEquilibriumPayoff
    (source : QuittingPositiveJointPrefixReachSource reward) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨endpoint⟩ := source.exists_punishmentEndpoint
  exact ⟨endpoint.endpoint.1, endpoint.isUniformEquilibriumPayoff⟩

/-- Forgetting the sure-exit obstruction does not lose the source's actual
uniform-equilibrium payoff. -/
theorem
    QuittingPositiveJointPrefixReachNoSureExitResidual.exists_uniformEquilibriumPayoff
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  residual.source.exists_uniformEquilibriumPayoff

end GameTheory
