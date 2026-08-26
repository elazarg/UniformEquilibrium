/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumPlateauPacket
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonTightMinimumFaceIteration
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Finite atoms in punishment-normal minimum joint terminal laws

In a finite punishment-normal quitting game, a positive-debt minimum joint
semantic/law point cannot be concentrated at `Never`.  Pure `Never` would
force negative singleton rewards, making literal all-Continue an exact
behavioral terminal Nash profile with zero uniform payoff.  Consequently, in
the absence of a uniform-equilibrium payoff, every minimum joint law has a
positive finite atom, and that same atom admits the checked causal suffix
realization.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Same-table punishment normality excludes a singleton-tight coordinate at
every positive global minimum, not only at one selected plateau point. -/
theorem minimumTerminalSemantic_strictSingleton_of_punishmentNormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∀ who, reward (quittingSingletonTerminal who) who < pair.1 who := by
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  intro who
  letI : Nonempty ι := ⟨who⟩
  have hdebtLe : quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hpair hminimum hpositive who
  have hsingletonLe :
      reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
    unfold quittingTerminalSemanticDebt at hdebtLe
    linarith
  refine lt_of_le_of_ne hsingletonLe ?_
  intro heq
  have htight : pair.1 who =
      reward (quittingSingletonTerminal who) who := heq.symm
  have hownerDebt :=
    minimumTerminalSemantic_debt_eq_sum_of_singleton_tight
      (reward := reward) pair who hpair hminimum hpositive htight
  have houtside : ∀ other, other ≠ who →
      quittingTerminalSemanticDebt pair other = 0 := by
    intro other hother
    have hsumErase : ∑ player ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebt pair player = 0 := by
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun player : ι => quittingTerminalSemanticDebt pair player)
        (Finset.mem_univ who)
      change (∑ player ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebt pair player) +
          quittingTerminalSemanticDebt pair who =
        ∑ player ∈ (Finset.univ : Finset ι),
          quittingTerminalSemanticDebt pair player at hsplit
      rw [show (∑ player ∈ (Finset.univ : Finset ι),
          quittingTerminalSemanticDebt pair player) =
        quittingTerminalSemanticDebtSum pair by rfl, hownerDebt] at hsplit
      linarith
    have hotherLe : quittingTerminalSemanticDebt pair other ≤
        ∑ player ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebt pair player := by
      exact Finset.single_le_sum
        (fun player _ => hdebtNonneg player)
        (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
    rw [hsumErase] at hotherLe
    exact le_antisymm hotherLe (hdebtNonneg other)
  have hface : QuittingSingletonTightMinimumFace reward pair who := {
    mem_carrier := hpair
    minimum := hminimum
    debt_pos := hpositive
    owner_tight := by
      simpa [quittingSoloReward, quittingSingletonTerminal] using htight
    outsider_debt := houtside }
  let gain := quittingSingletonCollisionGainMax reward who
  have hgain : 0 ≤ gain := by
    dsimp only [gain, quittingSingletonCollisionGainMax]
    exact le_trans (by simp)
      (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun other : ι => if other = who then 0 else
          max 0 (quittingSingletonCollisionReward reward who other -
            quittingSoloReward reward who other)) who)
  have hdenom : 0 < quittingTerminalSemanticDebtSum pair + gain := by
    linarith
  let ratio := quittingTerminalSemanticDebtSum pair /
    (quittingTerminalSemanticDebtSum pair + gain)
  have hratioPos : 0 < ratio := div_pos hpositive hdenom
  have hratioOne : ratio ≤ 1 := (div_le_one hdenom).2 (by linarith)
  let rate := ratio / 2
  have hratePos : 0 < rate := by
    dsimp only [rate]
    linarith
  have hrateOne : rate ≤ 1 := by
    dsimp only [rate]
    linarith
  have hrateBound : rate ≤ quittingTerminalSemanticDebtSum pair /
      (quittingTerminalSemanticDebtSum pair +
        quittingSingletonCollisionGainMax reward who) := by
    change rate ≤ ratio
    dsimp only [rate]
    linarith
  have hcontrolled : QuittingSoloRateControlled reward who pair rate :=
    quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax
      pair who hpositive hratePos hrateOne hrateBound
  have hendpoint : ∀ other, other ≠ who →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward who other ≤
        quittingSoloReward reward who other := by
    intro other hother
    exact quittingControlledSolo_outsiderEndpoint_le_solo
      pair who other hface hcontrolled hother
  have hsign := singletonTight_soloReward_lt_punishmentValue_and_nonpos
    pair who hface hratePos hrateOne hendpoint
  have hnormalWho := hnormal who
  change quittingPunishmentValue reward who ≤
    quittingSoloReward reward who who at hnormalWho
  exact (not_lt_of_ge hnormalWho hsign.1).elim

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

end GameTheory
