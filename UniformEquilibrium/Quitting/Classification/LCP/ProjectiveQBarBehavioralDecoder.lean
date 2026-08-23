/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Classification.Existence.NoHarmSingletonGenerated
import UniformEquilibrium.Quitting.AbsorptionPath.PunishmentNormalPathEmbedding
import UniformEquilibrium.Quitting.Classification.LCP.NormalPrincipalReward
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Pure-time fixed-target decoder for quitting games

This file isolates the final strategic consumer needed by continuum and
projective constructions.  A source supplies ordinary behavioral profiles
whose prescribed payoff approaches one fixed target and whose payoff after
every deterministic finite Quit time, or Never, is bounded by that target.
The pure-time extremality theorem then upgrades the bound to every unilateral
behavior strategy.

The pure-time certificate itself contains no absorption-path or matrix
hypothesis. Constructing its profiles and uniform pure-time estimates is a
separate source obligation; packaging those estimates here does not claim
such a producer.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open QuittingAbsorptionPath
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One profile whose prescribed payoff and every pure-time deviation are
controlled by the same fixed target.  `none` in `Option ℕ` is Never. -/
structure QuittingPureTimeTargetApproximationAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (error : ℝ) where
  profile : (quittingGame reward).BehaviorProfile
  prescribed_close : ∀ who,
    |quittingTerminalPayoff reward profile who - target who| ≤ error
  pureTime_le : ∀ who (quitTime : Option ℕ),
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤
      target who + error

/-- A pure-time target approximation remains valid after increasing its error
budget. -/
def QuittingPureTimeTargetApproximationAt.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : Payoff ι} {small large : ℝ}
    (approximation : QuittingPureTimeTargetApproximationAt reward target small)
    (herror : small ≤ large) :
    QuittingPureTimeTargetApproximationAt reward target large where
  profile := approximation.profile
  prescribed_close who := (approximation.prescribed_close who).trans herror
  pureTime_le who quitTime :=
    (approximation.pureTime_le who quitTime).trans (by linarith)

/-- A uniform pure-time target approximation controls every behavioral
deviation, with twice the displayed error. -/
theorem QuittingPureTimeTargetApproximationAt.isTwoMulAsymptoticNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : Payoff ι} {error : ℝ}
    (approximation : QuittingPureTimeTargetApproximationAt reward target error) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (2 * error) approximation.profile := by
  intro who deviation
  have hbehavior := quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
    reward approximation.profile who deviation
  have hpureNonempty :
      (Set.range fun quitTime : Option ℕ =>
        quittingTerminalPayoff reward
          (Function.update approximation.profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who).Nonempty := by
    exact ⟨_, ⟨none, rfl⟩⟩
  have hpureCap : sSup (Set.range fun quitTime : Option ℕ =>
      quittingTerminalPayoff reward
        (Function.update approximation.profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who) ≤
      target who + error := by
    apply csSup_le hpureNonempty
    rintro _ ⟨quitTime, rfl⟩
    exact approximation.pureTime_le who quitTime
  have hlower := (abs_le.mp (approximation.prescribed_close who)).1
  exact hbehavior.trans (by linarith)

/-- Fixed-target approximations at every positive error.  The target is chosen
once; only the approximating profile may depend on the error. -/
structure QuittingPureTimeTargetApproximationCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) where
  approximation : ∀ error : ℝ, 0 < error →
    Nonempty (QuittingPureTimeTargetApproximationAt reward target error)

/-- Cofinal arbitrarily small pure-time approximations supply the literal
every-positive-error certificate consumed by terminal uniform semantics. -/
theorem quittingPureTimeTargetApproximationCertificate_of_cofinal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (hcofinal : ∀ upper : ℝ, 0 < upper →
      ∃ error : ℝ, 0 ≤ error ∧ error < upper ∧
        Nonempty (QuittingPureTimeTargetApproximationAt reward target error)) :
    QuittingPureTimeTargetApproximationCertificate reward target where
  approximation upper hupper := by
    obtain ⟨error, herror, hsmall, ⟨approximation⟩⟩ :=
      hcofinal upper hupper
    exact ⟨approximation.mono hsmall.le⟩

/-- Uniform pure-time target approximation is already a complete
unrestricted-behavior producer for the declared uniform payoff. -/
theorem QuittingPureTimeTargetApproximationCertificate.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : Payoff ι}
    (certificate : QuittingPureTimeTargetApproximationCertificate reward target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  intro ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨approximation⟩ := certificate.approximation (ε / 3) hthird
  refine ⟨approximation.profile,
    approximation.isTwoMulAsymptoticNash.mono ?_, ?_⟩
  · linarith
  · intro who
    exact (approximation.prescribed_close who).trans (by linarith)

/-- A normal singleton owner whose terminal row weakly dominates every
player's own singleton payoff.  This is the exact raw output of the harmful
deleted-clock transversality branch. -/
def QuittingNormalNoHarmSingletonOwner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ owner : ι,
    (∀ who,
      quittingSoloReward reward who who ≤
        quittingSoloReward reward owner who) ∧
      quittingPunishmentValue reward owner ≤
        quittingSoloReward reward owner owner

/-- Construct the harmful-branch owner certificate from the natural outsider
no-harm inequalities and the owner's punishment normality. -/
theorem quittingNormalNoHarmSingletonOwner_of_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hnoHarm : ∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other)
    (hnormal : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    QuittingNormalNoHarmSingletonOwner reward := by
  refine ⟨owner, ?_, hnormal⟩
  intro who
  by_cases hwho : who = owner
  · subst who
    exact le_rfl
  · exact hnoHarm who hwho

/-- A normal no-harm singleton owner supplies the checked stationarily
generated branch, including actual punishment after a finite prefix. -/
theorem QuittingNormalNoHarmSingletonOwner.stationarilyGenerated
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (howner : QuittingNormalNoHarmSingletonOwner reward) :
    QuittingStationarilyGeneratedApproximateEquilibria reward := by
  obtain ⟨owner, hfloor, hnormal⟩ := howner
  apply quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
    reward owner _ hnormal
  intro other hother
  exact hfloor other

/-- A normal no-harm singleton owner therefore supplies a uniform-equilibrium
payoff against arbitrary behavioral deviations. -/
theorem exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (howner : QuittingNormalNoHarmSingletonOwner reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence
      reward
      (quittingApproximateEquilibriumExistence_of_stationarilyGenerated
        howner.stationarilyGenerated)

/-- The semantic outputs of the normal-subtype projective construction.  The
first two are established quitting-game branches; the last is the direct
fixed-target decoder interface above.  A raw no-harm singleton owner is not a
separate outcome: the checked theorem above already converts it to the
stationarily generated branch. -/
def QuittingProjectiveDecoderOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  IsQuittingZeroSolo reward ∨
    QuittingStationarilyGeneratedApproximateEquilibria reward ∨
      ∃ target : Payoff ι,
        Nonempty (QuittingPureTimeTargetApproximationCertificate reward target)

/-- The harmful deleted-clock transversality output enters the decoder through
its checked stationarily generated producer, rather than as a redundant fourth
outcome. -/
theorem QuittingNormalNoHarmSingletonOwner.projectiveDecoderOutcome
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (howner : QuittingNormalNoHarmSingletonOwner reward) :
    QuittingProjectiveDecoderOutcome reward :=
  Or.inr (Or.inl howner.stationarilyGenerated)

/-- The fixed ambient payoff target carried by a punishment-normal singleton
path.  It is chosen before any approximation accuracy. -/
def punishmentNormalPathTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) : Payoff ι :=
  fun who => absorptionPathPayoff reward witness.ambientPath 0 who

/-- Exact source-level strategic fork for one punishment-normal path.

The left branch is the harmful exceptional-owner output and the right branch
is the harmless fixed-target product approximation.  Both branches already
have checked unrestricted-behavior consumers; the analytic path analysis and
product discretization need only establish this disjunction. -/
def QuittingPunishmentNormalPathStrategicForkAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)) : Prop :=
  QuittingNormalNoHarmSingletonOwner reward ∨
    Nonempty (QuittingPureTimeTargetApproximationCertificate reward
      (punishmentNormalPathTarget reward witness))

/-- The checked strategic consumers turn either side of the exact path fork
into a projective-decoder outcome. -/
theorem QuittingPunishmentNormalPathStrategicForkAt.projectiveDecoderOutcome
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)}
    (hfork : QuittingPunishmentNormalPathStrategicForkAt reward witness) :
    QuittingProjectiveDecoderOutcome reward := by
  rcases hfork with howner | hcertificate
  · exact howner.projectiveDecoderOutcome
  · exact Or.inr (Or.inr ⟨punishmentNormalPathTarget reward witness,
      hcertificate⟩)

/-- Every output of the projective decoder gives a uniform-equilibrium payoff.
This is a consumer only: no matrix predicate is asserted to produce the
disjunction. -/
theorem exists_uniformEquilibriumPayoff_of_quittingProjectiveDecoderOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (houtcome : QuittingProjectiveDecoderOutcome reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases houtcome with hzero | hgenerated | ⟨target, ⟨certificate⟩⟩
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · exact
      quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence
        reward
        (quittingApproximateEquilibriumExistence_of_stationarilyGenerated hgenerated)
  · exact ⟨target, certificate.isUniformEquilibriumPayoff⟩

/-- Either branch of the exact path-level strategic fork already gives a
uniform-equilibrium payoff against arbitrary behavioral deviations. -/
theorem QuittingPunishmentNormalPathStrategicForkAt.exists_uniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward)}
    (hfork : QuittingPunishmentNormalPathStrategicForkAt reward witness) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_quittingProjectiveDecoderOutcome
    reward hfork.projectiveDecoderOutcome

/-- Outcome-valued compatibility interface for earlier callers.  It packages
away which of the established strategic consumers is used.  New source work
should prove `QuittingPunishmentNormalPathStrategicFork` below, whose two
alternatives are the exact outputs of the deleted-clock analysis. -/
def QuittingPunishmentNormalPathDecoder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ _witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward),
    QuittingProjectiveDecoderOutcome reward

/-- The one remaining source theorem after separating all checked strategic
consumers: every punishment-normal path satisfies the literal exceptional-
owner versus fixed-target-approximation fork. -/
def QuittingPunishmentNormalPathStrategicFork
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ witness : ContinuousZeroPerfectSingletonPath
      (quittingPunishmentNormalReward reward),
    QuittingPunishmentNormalPathStrategicForkAt reward witness

/-- The minimal strategic fork implies the older outcome-valued decoder
interface. -/
theorem QuittingPunishmentNormalPathStrategicFork.pathDecoder
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hfork : QuittingPunishmentNormalPathStrategicFork reward) :
    QuittingPunishmentNormalPathDecoder reward :=
  fun witness => (hfork witness).projectiveDecoderOutcome

/-- Projective Q-bar on the punishment-normal principal matrix is sufficient
once the single exact strategic fork is supplied. -/
theorem exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_of_strategicFork
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hfork : QuittingPunishmentNormalPathStrategicFork reward)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · obtain ⟨witness⟩ :=
      exists_punishmentNormal_singletonPath_of_projectiveQBar
        reward hzero hQ
    exact exists_uniformEquilibriumPayoff_of_quittingProjectiveDecoderOutcome
      reward (hfork witness).projectiveDecoderOutcome

/-- Compatibility form using the coarser outcome-valued path decoder. -/
theorem exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_of_pathDecoder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (decoder : QuittingPunishmentNormalPathDecoder reward)
    (hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_cases hzero : IsQuittingZeroSolo reward
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · obtain ⟨witness⟩ :=
      exists_punishmentNormal_singletonPath_of_projectiveQBar
        reward hzero hQ
    exact exists_uniformEquilibriumPayoff_of_quittingProjectiveDecoderOutcome
      reward (decoder witness)

/-- Full ambient projective Q-bar is a special case of the stronger
punishment-normal-principal result. -/
theorem exists_uniformEquilibriumPayoff_of_projectiveQBar_of_pathDecoder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (decoder : QuittingPunishmentNormalPathDecoder reward)
    (hQ : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_of_pathDecoder
      reward decoder
      (isProjectiveQBarMatrix_normalizedPunishmentNormalPlayerMatrix reward hQ)

/-- Ambient projective Q-bar is a special case of the stronger theorem driven
by the exact punishment-normal path fork. -/
theorem exists_uniformEquilibriumPayoff_of_projectiveQBar_of_strategicFork
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hfork : QuittingPunishmentNormalPathStrategicFork reward)
    (hQ : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_of_strategicFork
      reward hfork
      (isProjectiveQBarMatrix_normalizedPunishmentNormalPlayerMatrix reward hQ)

/-- Compatibility form of the residual classification using the coarser
outcome-valued decoder. -/
theorem punishmentNormalResidualHardClass_of_pathDecoder_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (decoder : QuittingPunishmentNormalPathDecoder reward)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    PunishmentNormalResidualHardClass reward := by
  apply
    punishmentNormalResidualHardClass_of_producer_of_not_exists_uniformEquilibriumPayoff
      reward _ hnot
  exact
    exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_of_pathDecoder
      reward decoder

/-- Strategic-fork form of the residual classification: a counterexample must
fail projective Q on its punishment-normal principal matrix. -/
theorem punishmentNormalResidualHardClass_of_strategicFork_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hfork : QuittingPunishmentNormalPathStrategicFork reward)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    PunishmentNormalResidualHardClass reward :=
  punishmentNormalResidualHardClass_of_pathDecoder_of_not_exists_uniformEquilibriumPayoff
    reward hfork.pathDecoder hnot

/-- The corresponding literal ambient obstruction: some nonempty principal
subset consists entirely of punishment-normal players and fails projective Q.
-/
theorem exists_normal_nonprojectivePrincipal_of_pathDecoder_of_counterexample
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (decoder : QuittingPunishmentNormalPathDecoder reward)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ players : Finset ι, players.Nonempty ∧
      (∀ who ∈ players, IsQuittingNormalPlayer reward who) ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) :=
  (punishmentNormalResidualHardClass_of_pathDecoder_of_not_exists_uniformEquilibriumPayoff
    reward decoder hnot).exists_ambient_allNormal_nonprojectivePrincipal

/-- Literal ambient obstruction obtained from the exact strategic fork. -/
theorem exists_normal_nonprojectivePrincipal_of_strategicFork_of_counterexample
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hfork : QuittingPunishmentNormalPathStrategicFork reward)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ players : Finset ι, players.Nonempty ∧
      (∀ who ∈ players, IsQuittingNormalPlayer reward who) ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) :=
  (punishmentNormalResidualHardClass_of_strategicFork_of_not_exists_uniformEquilibriumPayoff
    reward hfork hnot).exists_ambient_allNormal_nonprojectivePrincipal

end GameTheory
