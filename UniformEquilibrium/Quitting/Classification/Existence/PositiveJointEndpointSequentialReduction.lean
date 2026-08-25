/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitChargeDichotomy
import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointPrefixReachEndpoint
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockMonopoly
import UniformEquilibrium.Quitting.Root.SemanticExactPrefixOrbit

/-!
# Sequential reduction of the positive-joint endpoint

The existing single-seam projective-lasso compiler returns more than a
uniform-payoff witness: its periodic path is support-locally approximately
Nash and has nonsummable absorption.  Hence lassos at every accuracy give the
well-supported form of branch `S.3` directly.

Applying this observation to the canonical exact semantic-prefix orbit of a
positive-joint punishment endpoint leaves only the summable-charge case.  For
the maintained no-sure-exit residual, the surviving endpoint therefore has
both no exact sure-exit Nash prefix and a summable canonical exact-prefix
orbit.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Single-seam projective lassos at every positive accuracy give literal
branch `S.3`, not merely a uniform-equilibrium payoff. -/
theorem
    quittingWellSupportedAbsorbingSequenceExistence_of_singleSeamProjectiveLassos
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hproducer : ∀ error : ℝ, 0 < error →
      ∃ K : ℕ,
        Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error)) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  intro delta hdelta
  obtain ⟨K, ⟨lasso⟩⟩ := hproducer (delta / 2) (by linarith)
  obtain ⟨plan, hsupport, hdiverges, _hrational⟩ :=
    lasso.exists_supportRationalDivergentPath
  have hcomplete : IsCompletelyAbsorbing plan := by
    have hdiverges' : ¬Summable (fun time ↦
        quittingRootAbsorptionMass (plan time)) := by
      change ¬Summable (fun time ↦
        quittingRootAbsorptionMass (plan time)) at hdiverges
      exact hdiverges
    have hzero :=
      tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
        plan 0 (by simpa using hdiverges')
    have heq : quittingJointSurvivalWeight plan 0 =
        quittingSurvivalPrefix plan := by
      funext fuel
      simpa using
        (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix plan 0 fuel)
    unfold IsCompletelyAbsorbing
    rw [← heq]
    exact hzero
  refine ⟨plan, hcomplete, ?_⟩
  have herror : 2 * (delta / 2) = delta := by ring
  rwa [herror] at hsupport

/-- A nonsummable exact punishment-floor orbit reaches literal branch `S.3`.
Compact recurrence supplies single-seam lassos; their already checked
support-local divergent paths supply complete absorption. -/
theorem
    QuittingPunishmentFloorInfiniteOrbit.wellSupported_of_not_summable_absorption
    [Nonempty iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (hdiverges : ¬Summable (fun time ↦
      quittingRootAbsorptionMass (orbit.roots time))) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  apply
    quittingWellSupportedAbsorbingSequenceExistence_of_singleSeamProjectiveLassos
      reward
  intro error herror
  have hhalfError : 0 < error / 2 := by linarith
  let charge : ℕ → ℝ := fun time ↦
    quittingRootAbsorptionMass (orbit.roots time)
  obtain ⟨first, second, hfirstSecond, hclose, hgap⟩ :=
    Math.exists_close_pair_with_large_charge_gap_of_compact
      (quittingPunishmentFloorForwardCarrier reward)
      (quittingPunishmentFloorForwardCarrier_isCompact reward)
      orbit.value orbit.value_mem charge
      (fun time ↦ orbit.absorptionMass_nonneg time) hdiverges
      (error / 2) 1 hhalfError
  have hfirstLe : first ≤ second := hfirstSecond.le
  let horizon := second - first
  have hhorizon : 0 < horizon := by
    dsimp only [horizon]
    omega
  let segment := orbit.toFiniteSegment first horizon
  have hsegmentCharge : 1 ≤ segment.charge := by
    have hsumSplit :
        (∑ time ∈ Finset.range second, charge time) =
          (∑ time ∈ Finset.range first, charge time) +
            ∑ offset ∈ Finset.range horizon, charge (first + offset) := by
      simpa [horizon, Nat.add_sub_of_le hfirstLe] using
        (Finset.sum_range_add charge first (second - first))
    rw [hsumSplit] at hgap
    have hblock : 1 ≤
        ∑ offset ∈ Finset.range horizon, charge (first + offset) := by
      linarith
    simpa [segment, QuittingPunishmentFloorFinitePrefix.charge,
      QuittingPunishmentFloorInfiniteOrbit.toFiniteSegment, charge] using
      hblock
  have hsegmentClose : ∀ who,
      |segment.value 0 who - segment.value segment.horizon who| ≤
        error / 2 := by
    intro who
    have hcoordinate :
        dist (orbit.value first who) (orbit.value second who) < error / 2 :=
      lt_of_le_of_lt (dist_le_pi_dist _ _ who) hclose
    have hend : first + horizon = second := by
      dsimp only [horizon]
      omega
    have hsegmentEnd : segment.value segment.horizon = orbit.value second := by
      change orbit.value (first + horizon) = orbit.value second
      rw [hend]
    rw [show segment.value 0 = orbit.value first by simp [segment],
      hsegmentEnd]
    simpa [Real.dist_eq] using hcoordinate.le
  apply
    exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn
      segment 1 (error / 2) error (by norm_num) hsegmentCharge
        (by linarith)
  · norm_num [div_eq_mul_inv]
  · exact hsegmentClose

/-- The canonical exact semantic-prefix orbit starting at a reached
positive-joint punishment endpoint. -/
def QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    QuittingPunishmentFloorInfiniteOrbit reward where
  roots time := quittingTerminalSemanticSelectedExactRoot reward
    (quittingTerminalSemanticExactPrefixOrbit reward endpoint.endpoint time)
  value time :=
    (quittingTerminalSemanticExactPrefixOrbit reward endpoint.endpoint time).1
  value_mem := by
    intro time
    have hpair := quittingTerminalSemanticExactPrefixOrbit_mem_carrier
      reward endpoint.endpoint endpoint.endpoint_mem time
    exact (quittingTerminalSemanticCarrier_mem_box reward _
      (abs_reward_le_quittingRewardBound reward) hpair).1
  anchor_floor := by
    intro who
    change quittingPunishmentValue reward who ≤ endpoint.endpoint.1 who
    rw [endpoint.payoff_eq_envelope who]
    exact quittingPunishmentValue_le_terminalSemanticEnvelope_of_mem_carrier
      reward endpoint.endpoint_mem who
  policy := by
    intro time
    rw [quittingTerminalSemanticExactPrefixOrbit_succ]
    rfl
  exactNash := fun time ↦
    quittingTerminalSemanticSelectedExactRoot_isZeroNash reward _

/-- A reached positive-joint endpoint either gives branch `S.3`, or its
canonical exact semantic-prefix orbit enters the summable all-Continue port. -/
theorem
    QuittingPositiveJointPrefixReachPunishmentEndpoint.wellSupported_or_summableExactPrefixPort
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      Nonempty
        (QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
          endpoint.exactPrefixOrbit) := by
  letI : Nonempty iota := ⟨endpoint.punished⟩
  by_cases hsummable : Summable (fun time ↦ quittingRootAbsorptionMass
      (endpoint.exactPrefixOrbit.roots time))
  · exact Or.inr
      (endpoint.exactPrefixOrbit.nonempty_summableChargeAllContinuePort_of_summable_absorption
        hsummable)
  · exact Or.inl
      (endpoint.exactPrefixOrbit.wellSupported_of_not_summable_absorption
        hsummable)

/-- The positive-joint no-sure-exit residual is reduced to branch `S.3` or
an actual reached endpoint which simultaneously has no exact sure-exit Nash
prefix and a summable canonical exact-prefix orbit. -/
theorem
    QuittingPositiveJointPrefixReachNoSureExitResidual.wellSupported_or_summableExactPrefixPort
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      ∃ endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward,
        ¬endpoint.HasSureExitNashPrefix ∧
          Nonempty
            (QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
              endpoint.exactPrefixOrbit) := by
  obtain ⟨endpoint⟩ := residual.source.exists_punishmentEndpoint
  rcases endpoint.wellSupported_or_summableExactPrefixPort with
    hwellSupported | hport
  · exact Or.inl hwellSupported
  · exact Or.inr ⟨endpoint, residual.noSureExitNashPrefix endpoint,
      hport⟩

end GameTheory
