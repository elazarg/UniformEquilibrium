/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumFiberIsolation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.SimpleBranches
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Finite atoms in four-player minimum joint terminal laws

A globally minimizing positive-debt joint semantic/law point cannot be concentrated at `Never`
when every player is punishment-normal: pure `Never` forces negative singleton rewards, making
literal all-Continue an exact behavioral terminal Nash profile with zero uniform payoff.  The
four-player hard residual excludes that payoff and hence forces a positive finite law atom.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Pure `Never` mass in a positive, punishment-normal minimum joint-law point forces zero
prescribed payoff, strict negative singleton rewards, exact all-Continue terminal Nash, and the
zero uniform-equilibrium payoff.  The Nash quantifier uses the full behavioral strategy class. -/
theorem minimumTerminalSemanticLaw_pureNever_strictSingleton_exactNash_zeroUniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hpureNever : point.2 none = 1) :
    point.1.1 = 0 ∧
      (∀ who, reward (quittingSingletonTerminal who) who < 0) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingAlwaysContinueProfile reward) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none 0 := by
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hfiniteSum : (∑ terminal, point.2 (some terminal)) = 0 := by
    have hsum := hmass.2
    rw [Fintype.sum_option, hpureNever] at hsum
    linarith
  have hfiniteZero : ∀ terminal, point.2 (some terminal) = 0 := by
    intro terminal
    have hnonneg : 0 ≤ point.2 (some terminal) := hmass.1 (some terminal)
    have hle : point.2 (some terminal) ≤
        ∑ other, point.2 (some other) := by
      exact Finset.single_le_sum
        (fun other _ => hmass.1 (some other)) (Finset.mem_univ terminal)
    linarith
  have hprescribed : point.1.1 = 0 := by
    have hmoment := terminalSemanticLawCarrier_rewardMoment reward point hpoint
    rw [← hmoment]
    funext who
    simp [quittingTerminalRewardMoment, quittingTerminalOutcomeReward, hfiniteZero]
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hstrict := minimumTerminalSemantic_strictSingleton_of_punishmentNormal
    point.1 hcarrier hminimum hpositive hnormal
  have hsingleton : ∀ who,
      reward (quittingSingletonTerminal who) who < 0 := by
    intro who
    have hwho := hstrict who
    rw [hprescribed] at hwho
    exact hwho
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAlwaysContinueProfile reward) :=
    (isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl).mpr
      fun who => (hsingleton who).le
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (quittingAlwaysContinueProfile reward) hnash
  refine ⟨hprescribed, hsingleton, hnash, ?_⟩
  have hpayoff : quittingTerminalPayoff reward
      (quittingAlwaysContinueProfile reward) = (0 : Payoff ι) := by
    funext who
    exact quittingTerminalPayoff_quittingAlwaysContinue reward who
  simpa only [hpayoff] using huniform

/-- In any finite punishment-normal quitting game without a uniform-equilibrium payoff, every
globally minimizing joint terminal law gives positive mass to a finite terminal coalition. -/
theorem exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      0 < point.2 (some terminal) := by
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hno
  have hminimumValue :=
    quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum
  have hpositive : 0 < quittingTerminalSemanticDebtSum point.1 := by
    rw [← hminimumValue]
    exact hinf
  by_contra hnone
  push Not at hnone
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hfiniteZero : ∀ terminal, point.2 (some terminal) = 0 := by
    intro terminal
    exact le_antisymm (hnone terminal) (hmass.1 (some terminal))
  have hpureNever : point.2 none = 1 := by
    have hsum := hmass.2
    rw [Fintype.sum_option] at hsum
    simp only [hfiniteZero, Finset.sum_const_zero, add_zero] at hsum
    exact hsum
  obtain ⟨_, _, _, huniform⟩ :=
    minimumTerminalSemanticLaw_pureNever_strictSingleton_exactNash_zeroUniform
      reward point hpoint hminimum hpositive hnormal hpureNever
  exact hno ⟨0, huniform⟩

/-- The positive finite atom at a supplied punishment-normal minimum joint law has the checked
same-point causal realization behind arbitrarily deep exact cap--Nash prefixes. -/
theorem nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    Nonempty (QuittingMinimumLawCausalSuffixAtom reward point) := by
  obtain ⟨terminal, hmass⟩ :=
    exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  refine ⟨{
    terminal := terminal
    terminalMass_pos := hmass
    chronology := ?_ }⟩
  exact exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
    reward point terminal hpoint hmass hinf hminimumValue

/-- Every globally minimizing joint law in the four-player hard residual has a positive finite
coalition coordinate.  Positivity of the minimum is derived from the residual witness. -/
theorem exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
      0 < point.2 (some terminal) := by
  have hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who := by
    intro who
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using residual.all_punishmentNormal who
  exact
    exists_positive_finiteLawAtom_of_punishmentNormal_minimum_of_not_uniformPayoff
      reward residual.witness.not_exists_uniformEquilibriumPayoff hnormal
      point hpoint hminimum

/-! ## Same-point causalization -/

/-- The finite atom of a supplied four-player hard-residual minimum joint law enters the checked
deep causal suffix-atom construction at that same carrier point. -/
theorem finFourHardResidual_minimumLaw_causalSuffixAtom
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    Nonempty (QuittingMinimumLawCausalSuffixAtom reward point) := by
  have hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who := by
    intro who
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using residual.all_punishmentNormal who
  exact
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward residual.witness.not_exists_uniformEquilibriumPayoff hnormal
      point hpoint hminimum

/-- A four-player hard residual alone selects a globally minimizing joint-law point, proves its
positive finite atom, and causalizes that atom while preserving the selected point and minimum
provenance. -/
theorem exists_finFourHardResidual_minimumLaw_causalSuffixAtom
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ point : QuittingTerminalSemanticLawPoint (Fin 4),
      point ∈ quittingTerminalSemanticLawCarrier reward ∧
      point.1 ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum point.1 ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalDebtSumInf reward ∧
      quittingTerminalSemanticDebtSum point.1 =
        quittingTerminalDebtSumInf reward ∧
      Nonempty (QuittingMinimumLawCausalSuffixAtom reward point) := by
  obtain ⟨point, hpoint, hcarrier, hminimum, hminimumValue⟩ :=
    exists_minimum_terminalSemanticLawCarrier_of_not_uniformPayoff reward
      residual.witness.not_exists_uniformEquilibriumPayoff
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      residual.witness.not_exists_uniformEquilibriumPayoff
  exact ⟨point, hpoint, hcarrier, hminimum, hinf, hminimumValue,
    finFourHardResidual_minimumLaw_causalSuffixAtom
      reward bound residual point hpoint hminimum⟩

end GameTheory
