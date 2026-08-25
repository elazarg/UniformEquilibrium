/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointEndpointSequentialReduction
import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier

/-!
# Diagonality of the positive-joint exact-prefix orbit

The exact semantic-prefix orbit of a reached positive-joint punishment
endpoint never leaves the zero-debt stratum.  The selected root is exact Nash
against the current prescribed coordinate, so exact prefixing sends each
diagonal semantic pair to another diagonal semantic pair.

Consequently the limit of any summable all-Continue port on this orbit is a
diagonal point of the literal terminal-semantic carrier and is therefore an
actual uniform-equilibrium payoff.  This does not classify that payoff into
an AGKRS stationary, instant-punishment, or absorbing sequentially perfect
branch.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Every semantic pair in the canonical exact-prefix orbit is diagonal. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixPair_eq_diagonal
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (time : ℕ) :
    quittingTerminalSemanticExactPrefixOrbit reward endpoint.endpoint time =
      (endpoint.exactPrefixOrbit.value time,
        endpoint.exactPrefixOrbit.value time) := by
  induction time with
  | zero =>
      apply Prod.ext
      · rfl
      · funext who
        exact (endpoint.payoff_eq_envelope who).symm
  | succ time ih =>
      rw [quittingTerminalSemanticExactPrefixOrbit_succ, ih]
      exact quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
        reward (endpoint.exactPrefixOrbit.value time)
          (quittingTerminalSemanticSelectedExactRoot reward
            (endpoint.exactPrefixOrbit.value time,
              endpoint.exactPrefixOrbit.value time))
          (quittingTerminalSemanticSelectedExactRoot_isZeroNash reward _)

/-- Every payoff annotation in the canonical exact-prefix orbit is already a
diagonal point of the literal terminal-semantic carrier. -/
theorem
    QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixValue_mem_diagonal
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (time : ℕ) :
    (endpoint.exactPrefixOrbit.value time,
        endpoint.exactPrefixOrbit.value time) ∈
      quittingTerminalSemanticCarrier reward := by
  rw [← endpoint.exactPrefixPair_eq_diagonal time]
  exact quittingTerminalSemanticExactPrefixOrbit_mem_carrier
    reward endpoint.endpoint endpoint.endpoint_mem time

namespace QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort

/-- The limit of a summable port on the canonical endpoint orbit remains a
diagonal point of the literal terminal-semantic carrier. -/
theorem limit_mem_diagonal_of_endpoint
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (port : endpoint.exactPrefixOrbit.SummableChargeAllContinuePort) :
    (port.limit, port.limit) ∈ quittingTerminalSemanticCarrier reward := by
  have hvalue : Tendsto endpoint.exactPrefixOrbit.value atTop
      (nhds port.limit) := tendsto_pi_nhds.2 port.value_tendsto
  have hpair : Tendsto
      (fun time ↦
        (endpoint.exactPrefixOrbit.value time,
          endpoint.exactPrefixOrbit.value time))
      atTop (nhds (port.limit, port.limit)) := by
    simpa only [nhds_prod_eq] using hvalue.prodMk hvalue
  exact (quittingTerminalSemanticCarrier_isCompact reward).isClosed.mem_of_tendsto
    hpair (Filter.Eventually.of_forall endpoint.exactPrefixValue_mem_diagonal)

/-- A summable canonical endpoint port has an actual uniform-equilibrium
payoff at its all-Continue limit. -/
theorem limit_isUniformEquilibriumPayoff_of_endpoint
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (port : endpoint.exactPrefixOrbit.SummableChargeAllContinuePort) :
    (quittingGame reward).IsUniformEquilibriumPayoff none port.limit := by
  letI : Nonempty iota := ⟨endpoint.punished⟩
  exact isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
    port.limit (port.limit_mem_diagonal_of_endpoint endpoint)

end QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort

end GameTheory
