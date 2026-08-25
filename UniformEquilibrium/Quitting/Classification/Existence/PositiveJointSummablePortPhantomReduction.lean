/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointEndpointSequentialReduction
import UniformEquilibrium.Quitting.Classification.Existence.PositiveRhoLandingClassificationBoundary

/-!
# Phantom reduction of a positive-joint summable port

The limit of a summable exact-prefix port is an exact all-Continue
Nash--Bellman self-loop.  Repeating that self-loop gives the constant
positive-survival support--Bellman boundary.  Consequently either every
singleton self-reward is nonpositive, which is the stationary all-Continue
branch, or the port supplies the same positive-singleton suffix defect that
occurs in the corrected pointwise residual.

Thus the summable positive-joint seam and one arm of the prioritized
pointwise seam share a literal checked obstruction.  This does not consume
that obstruction and does not turn the formal Bellman limit into an
executable stationary payoff.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A diagonal point of the literal terminal semantic carrier is an actual
uniform-equilibrium payoff target.  Carrier membership supplies executable
profiles; convergence of both semantic coordinates makes their terminal
Nash errors and prescribed-payoff errors vanish together. -/
theorem isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
    [Nonempty iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (target : Payoff iota)
    (hmem : (target, target) ∈ quittingTerminalSemanticCarrier reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair
      reward (target, target) hmem
  let error : ℕ → ℝ := fun n ↦ quittingTerminalSemanticExploitability
    (quittingTerminalSemanticPair reward (profiles n))
  have hzero : quittingTerminalSemanticExploitability
      (target, target) = 0 := by
    unfold quittingTerminalSemanticExploitability
      QuittingBoundaryHolonomy.finitePlayerMax
      quittingTerminalSemanticDebt
    simp
  have herror : Tendsto error atTop (nhds 0) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp
        hprofiles
    rw [hzero] at hcontinuous
    exact hcontinuous
  have hnash : ∀ n,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error n) (profiles n) := by
    intro n who deviation
    have hgain := quittingTerminalPayoff_update_sub_le_terminalSemanticDebt
      reward (profiles n) who deviation
    have hdebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who ≤ error n := by
      dsimp only [error]
      unfold quittingTerminalSemanticExploitability
      exact (le_max_right 0 _).trans
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun player ↦ max 0 (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) player)) who)
    linarith
  have htarget : Tendsto
      (fun n ↦ quittingTerminalPayoff reward (profiles n)) atTop
      (nhds target) := by
    apply tendsto_pi_nhds.2
    intro who
    have hcoordinate :=
      (((continuous_apply who).comp continuous_fst).tendsto
        (target, target)).comp hprofiles
    exact hcoordinate
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward target error profiles herror (Frequently.of_forall hnash) htarget

namespace QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort

variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
variable {orbit : QuittingPunishmentFloorInfiniteOrbit reward}

/-- The formal all-Continue limit of a summable port gives a constant
positive-survival support--Bellman boundary at every nonnegative tolerance. -/
theorem nonempty_positiveSurvivalBoundary
    (port : orbit.SummableChargeAllContinuePort) {delta : ℝ}
    (hdelta : 0 ≤ delta) :
    Nonempty (QuittingSupportBellmanPositiveSurvivalBoundary reward delta) := by
  let value : ℕ → Payoff iota := fun _ ↦ port.limit
  let roots : ℕ → iota → PMF Bool := fun _ ↦ quittingAllContinueRoot
  have hsurvival : 0 < quittingJointSurvivalLimit roots 0 := by
    have hweight : quittingJointSurvivalWeight roots 0 = fun _ ↦ 1 := by
      funext fuel
      simp [roots, quittingJointSurvivalWeight_eq_prod,
        quittingStationaryContinueMass_eq_prod_continueProbability,
        quittingAllContinueRoot]
    have hlimit : quittingJointSurvivalLimit roots 0 = 1 := by
      apply tendsto_nhds_unique (tendsto_quittingJointSurvivalLimit roots 0)
      rw [hweight]
      exact tendsto_const_nhds
    rw [hlimit]
    norm_num
  apply exists_quittingSupportBellmanPositiveSurvivalBoundary
    reward value roots delta 0 hsurvival
  · intro time who
    exact abs_le.2 ⟨(port.limit_mem.1 who), port.limit_mem.2 who⟩
  · intro time
    change port.limit = quittingRootSuccessorPayoff reward port.limit
      quittingAllContinueRoot
    rw [← quittingRootOfSimplex_allContinueSimplexRoot]
    exact port.selfLoop.1
  · intro time
    have hexact : IsQuittingRootSupportApproxNash reward port.limit 0
        quittingAllContinueRoot :=
      isQuittingRootSupportApproxNash_zero_of_isZeroNash reward port.limit
        quittingAllContinueRoot
        (quittingAllContinueRoot_isZeroNash_of_singleton_le
          reward port.limit port.singleton_le)
    exact hexact.mono hdelta

/-- A summable all-Continue port either closes the stationary branch or
produces the literal positive-singleton suffix-defect residual at the chosen
tolerance. -/
theorem stationaryExistence_or_positiveSingletonDefectResidual
    [Nonempty iota]
    (port : orbit.SummableChargeAllContinuePort) {delta : ℝ}
    (hdelta : 0 ≤ delta) :
    QuittingStationaryεEquilibriumExistence reward ∨
      Nonempty
        (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta) := by
  obtain ⟨boundary⟩ := port.nonempty_positiveSurvivalBoundary hdelta
  exact boundary.stationary_or_defect

/-- More directly, failure of the zero-solo stationary branch turns the
summable port limit into the existing nonzero all-Continue phantom. -/
theorem stationaryExistence_or_allContinuePhantom
    [Nonempty iota]
    (port : orbit.SummableChargeAllContinuePort) :
    QuittingStationaryεEquilibriumExistence reward ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom reward) := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact Or.inl fun delta hdelta ↦
      quittingStationaryεEquilibriumAt_of_zeroSolo reward hzero hdelta.le
  · right
    have hlimitNe : port.limit ≠ 0 := by
      intro hlimit
      apply hzero
      intro who
      have hsolo := port.singleton_le who
      rw [hlimit] at hsolo
      simpa using hsolo
    refine ⟨{
      value := port.limit
      value_ne_zero := hlimitNe
      notZeroSolo := hzero
      value_mem := port.limit_mem
      rational := ?_
      support := ?_ }⟩
    · intro who
      simpa using port.punishment_le who
    · exact isQuittingRootSupportApproxNash_zero_of_isZeroNash
        reward port.limit quittingAllContinueRoot
          (quittingAllContinueRoot_isZeroNash_of_singleton_le
            reward port.limit port.singleton_le)

end QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort

namespace QuittingPositiveJointPrefixReachNoSureExitResidual

/-- The positive-joint endpoint seam reduces to S.3, S.1, or the canonical
nonzero all-Continue phantom.  This is the finite-dimensional obstruction
shared with the zero-absorption positive-rho boundary. -/
theorem wellSupported_or_stationary_or_allContinuePhantom
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      QuittingStationaryεEquilibriumExistence reward ∨
        Nonempty (QuittingLowSurvivalAllContinuePhantom reward) := by
  rcases residual.wellSupported_or_summableExactPrefixPort with
    hwellSupported | ⟨endpoint, _hnoSureExit, ⟨port⟩⟩
  · exact Or.inl hwellSupported
  · letI : Nonempty iota := ⟨endpoint.punished⟩
    rcases port.stationaryExistence_or_allContinuePhantom with
      hstationary | hphantom
    · exact Or.inr (Or.inl hstationary)
    · exact Or.inr (Or.inr hphantom)

/-- The positive-joint residual reaches S.3, S.1, or the exact
positive-singleton phantom arm already present in the corrected pointwise
boundary.  The no-sure-exit field is not needed after the summable port has
been selected. -/
theorem wellSupported_or_stationary_or_singletonDefect
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      QuittingStationaryεEquilibriumExistence reward ∨
        Nonempty
          (QuittingSupportBellmanPositiveSingletonDefectResidual
            reward delta) := by
  rcases residual.wellSupported_or_summableExactPrefixPort with
    hwellSupported | ⟨endpoint, _hnoSureExit, ⟨port⟩⟩
  · exact Or.inl hwellSupported
  · letI : Nonempty iota := ⟨endpoint.punished⟩
    rcases port.stationaryExistence_or_positiveSingletonDefectResidual
        hdelta with hstationary | hdefect
    · exact Or.inr (Or.inl hstationary)
    · exact Or.inr (Or.inr hdefect)

/-- Equivalently, the summable positive-joint seam contracts to S.3, S.1,
or the existing corrected pointwise residual.  Only its
positive-singleton-defect arm is used. -/
theorem wellSupported_or_stationary_or_refinedResidualAt
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      QuittingStationaryεEquilibriumExistence reward ∨
        QuittingCorrectedPointwiseRefinedSourceResidualAt reward delta := by
  rcases residual.wellSupported_or_stationary_or_singletonDefect
      hdelta with hwellSupported | hstationary | hdefect
  · exact Or.inl hwellSupported
  · exact Or.inr (Or.inl hstationary)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hdefect)))

end QuittingPositiveJointPrefixReachNoSureExitResidual

end GameTheory
