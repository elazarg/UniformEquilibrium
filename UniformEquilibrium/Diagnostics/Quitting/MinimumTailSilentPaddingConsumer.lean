import UniformEquilibrium.Diagnostics.Quitting.MinimumTailProfileSource
import UniformEquilibrium.Diagnostics.Quitting.SilentPaddingTwoCutSource

/-!
# Silent-padding consumption of a compactified minimum-tail source

Joint convergence supplies eventual persistence of one positive finite-law
coordinate and eventual cap neutrality of the all-Continue padding row.  The
checked two-cut consumer can therefore be applied to every sufficiently late
profile in the retained literal subsequence.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- The exact silent-padded block and checked debt-or-paid-splice alternative
at one literal four-player tail profile. -/
structure FinFourSilentPaddingTwoCutRealization
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (threshold : ℝ) (minimum : QuittingTerminalSemanticPair (Fin 4)) where
  window : ℕ
  window_pos : 0 < window
  windowTerminalMass_gt : threshold < ∑ time ∈ Finset.range window,
    quittingStageCoalitionMass reward profile time terminal
  block : QuittingUniformlyReachedPostMarkTwoCutBlock reward
  roots_eq : block.roots =
    quittingSilentPrefixRoots (quittingProfileLiveRoot reward profile)
  markedRow_eq : block.markedRow = 0
  entryCut_eq : block.entryCut = 1
  exitCut_eq : block.exitCut = window + 1
  hazardFloor_eq : block.hazardFloor = threshold
  reachFloor_eq : block.reachFloor = 1
  entryReach_eq : quittingJointSurvivalWeight block.roots 0 block.entryCut = 1
  minimum_eq : block.minimum = minimum
  entryPair_eq : block.entryPair = quittingTerminalSemanticPair reward profile
  exitPair_eq : block.exitPair =
    quittingRootSequenceTerminalSemanticPairAt reward
      (quittingProfileLiveRoot reward profile) window
  parentPair_eq : quittingTerminalSemanticPair reward block.parentProfile =
    quittingTerminalSemanticPair reward profile
  parentLaw_eq : ∀ terminal',
    quittingAbsorbedMassLimit reward block.parentProfile terminal' =
      quittingAbsorbedMassLimit reward profile terminal'
  parentOutcomeLaw_eq : ∀ outcome,
    quittingTerminalOutcomeMass reward block.parentProfile outcome =
      quittingTerminalOutcomeMass reward profile outcome
  alternative :
    quittingTerminalSemanticDebtSum block.exitPair ≥
        quittingTerminalSemanticDebtSum block.minimum +
          (Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum ∨
      ∃ payer : Fin 4,
        ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
          quittingTerminalPayoff reward
                (Function.update block.entryProfile payer deviation) payer -
              quittingTerminalPayoff reward block.entryProfile payer >
            block.coerciveConstant / 16 ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update block.entryProfile payer deviation)) payer ≤
            block.coerciveConstant / 16 ∧
          quittingTerminalPayoff reward
                (Function.update block.entryProfile payer deviation) payer =
            quittingTerminalPayoff reward
                (Function.update profile payer deviation) payer ∧
          quittingTerminalSemanticPair reward
                (Function.update block.entryProfile payer deviation) =
            quittingTerminalSemanticPair reward
                (Function.update profile payer deviation) ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update block.entryProfile payer deviation)) payer =
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (Function.update profile payer deviation)) payer ∧
          block.paidSpliceProfile payer deviation =
            Function.update block.parentProfile payer
              (block.paidSpliceDeviation payer deviation) ∧
          quittingTerminalPayoff reward
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward block.parentProfile payer >
            block.coerciveConstant / 16 ∧
          quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) payer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (block.paidSpliceProfile payer deviation)) payer =
            quittingTerminalPayoff reward
                (block.paidSpliceProfile payer deviation) payer -
              quittingTerminalPayoff reward profile payer ∧
          quittingProfileLiveRoot reward
              (block.paidSpliceProfile payer deviation) 0 =
            (quittingAllContinueRoot : Fin 4 → PMF Bool)

namespace FinFourMinimumTailFiniteAtomCompactification

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourHardResidualMinimumTailProfileSource reward bound}

/-- The literal profile at one retained joint-compactification rank. -/
def retainedProfile
    (compactification : FinFourMinimumTailFiniteAtomCompactification source)
    (rank : ℕ) : (quittingGame reward).BehaviorProfile :=
  source.tailSource.profiles
    (compactification.compactification.subsequence rank)

/-- The selected semantic pairs converge to the semantic coordinate of the
same joint compactification. -/
theorem tendsto_retainedProfile_semanticPair
    (compactification : FinFourMinimumTailFiniteAtomCompactification source) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (compactification.retainedProfile rank)) atTop
        (nhds compactification.compactification.point.1) :=
  continuous_fst.continuousAt.tendsto.comp
    compactification.compactification.point_tendsto

/-- The fixed positive finite-law coordinate persists eventually along the
same literal retained profiles. -/
theorem tendsto_retainedProfile_terminalMass
    (compactification : FinFourMinimumTailFiniteAtomCompactification source) :
    Tendsto (fun rank ↦ quittingAbsorbedMassLimit reward
      (compactification.retainedProfile rank) compactification.terminal) atTop
        (nhds (compactification.compactification.point.2
          (some compactification.terminal))) := by
  have hcontinuous : Continuous
      (fun point : QuittingTerminalSemanticLawPoint (Fin 4) ↦
        point.2 (some compactification.terminal)) :=
    (continuous_apply (some compactification.terminal)).comp continuous_snd
  have hmass := hcontinuous.continuousAt.tendsto.comp
    compactification.compactification.point_tendsto
  change Tendsto (fun rank ↦ quittingTerminalOutcomeMass reward
      (compactification.retainedProfile rank)
        (some compactification.terminal)) atTop
    (nhds (compactification.compactification.point.2
      (some compactification.terminal))) at hmass
  simpa only [quittingTerminalOutcomeMass] using hmass

/-- Every sufficiently late retained profile supplies the exact silent-padded
two-cut block and its checked off-minimum-or-paid-splice alternative. -/
theorem eventually_nonempty_silentPaddingTwoCutRealization
    (compactification : FinFourMinimumTailFiniteAtomCompactification source)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hthreshold_lt : threshold <
      compactification.compactification.point.2
        (some compactification.terminal)) :
    ∀ᶠ rank in atTop, Nonempty (FinFourSilentPaddingTwoCutRealization
      reward (compactification.retainedProfile rank)
        compactification.terminal threshold
          compactification.compactification.point.1) := by
  have hlaw : ∀ᶠ rank in atTop,
      threshold < quittingAbsorbedMassLimit reward
        (compactification.retainedProfile rank)
          compactification.terminal :=
    compactification.tendsto_retainedProfile_terminalMass.eventually_const_lt
      hthreshold_lt
  have hnear : ∀ᶠ rank in atTop, ∀ who,
      compactification.compactification.point.1.2 who -
          quittingTerminalSemanticDebtSum
            compactification.compactification.point.1 <
        (quittingTerminalSemanticPair reward
          (compactification.retainedProfile rank)).2 who := by
    apply Filter.eventually_all.mpr
    intro who
    have hcap : Tendsto (fun rank ↦
        (quittingTerminalSemanticPair reward
          (compactification.retainedProfile rank)).2 who) atTop
        (nhds (compactification.compactification.point.1.2 who)) :=
      (((continuous_apply who).comp continuous_snd).continuousAt.tendsto.comp
        compactification.tendsto_retainedProfile_semanticPair)
    apply hcap.eventually_const_lt
    linarith [compactification.compactification.pointDebt_pos]
  filter_upwards [hlaw, hnear] with rank hlawRank hnearRank
  obtain ⟨window, hwindow, hmass, block, hroots, hmark, hentry, hexit, hhazard,
      hreach, hentryReach, hminimum, hentryPair, hexitPair, hparentPair,
      hparentLaw, hparentOutcomeLaw, halternative⟩ :=
    exists_finFour_silentPaddingTwoCutBlock_with_paidSpliceAlternative
      reward (compactification.retainedProfile rank)
        compactification.terminal hthreshold hlawRank
          compactification.compactification.point.1
            compactification.compactification.point_semantic_mem
            compactification.compactification.point_minimum
            compactification.compactification.pointDebt_pos hnearRank
  exact ⟨{
    window := window
    window_pos := hwindow
    windowTerminalMass_gt := hmass
    block := block
    roots_eq := hroots
    markedRow_eq := hmark
    entryCut_eq := hentry
    exitCut_eq := hexit
    hazardFloor_eq := hhazard
    reachFloor_eq := hreach
    entryReach_eq := hentryReach
    minimum_eq := hminimum
    entryPair_eq := hentryPair
    exitPair_eq := hexitPair
    parentPair_eq := hparentPair
    parentLaw_eq := hparentLaw
    parentOutcomeLaw_eq := hparentOutcomeLaw
    alternative := halternative }⟩

end FinFourMinimumTailFiniteAtomCompactification

end GameTheory
