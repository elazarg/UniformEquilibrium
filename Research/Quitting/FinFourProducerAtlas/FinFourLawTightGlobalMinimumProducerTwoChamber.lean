import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtCapBandTargetDispatch
import UniformEquilibrium.Diagnostics.Quitting.FinFourLawTightCapNashStrictMinimum

/-!
# Same-point producer entrance from the law-tight Fin4 classifier

The existing no-uniform-payoff classifier selects a positive global minimum
and returns either full coordinate debt or its reset-rigid chamber.  This
module independently selects a hard residual from the same hypothesis and
causalizes a finite atom at that exact classifier minimum.  Thus only the
full-debt arm packages a `FinFourMinimumAtomProducer` and feeds the supplied
full-debt compact-target dispatch.  The reset-rigid arm is unchanged.

The independently selected residual is not asserted to equal the residual
used internally by the classifier.  No renewal, terminal-exit, Nash, or new
uniform-equilibrium conclusion is made.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- The two surviving classifier arms, with a same-point producer attached
only to the full-debt arm. -/
inductive FinFourLawTightGlobalMinimumProducerAlternative
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (origin minimum : QuittingTerminalSemanticLawPoint (Fin 4)) : Prop
  | fullDebt
      (source : FinFourMinimumAtomProducer reward
        (quittingRewardBound reward))
      (source_point_eq : source.point = minimum)
      (all_debt_pos : ∀ who,
        0 < quittingTerminalSemanticDebt source.point.1 who) :
      FinFourLawTightGlobalMinimumProducerAlternative reward origin minimum
  | resetRigid
      (chamber : QuittingLawTightResetRigidChamber
        reward origin minimum minimum origin.1) :
      FinFourLawTightGlobalMinimumProducerAlternative reward origin minimum

/-- The canonical classifier data with its full-debt arm strengthened by a
same-point minimum-atom producer. -/
structure FinFourLawTightGlobalMinimumProducerTwoChamber
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  origin : QuittingTerminalSemanticLawPoint (Fin 4)
  minimum : QuittingTerminalSemanticLawPoint (Fin 4)
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  origin_mem : origin ∈ quittingTerminalSemanticLawCarrier reward
  saturationMinimum :
    IsQuittingLawTightCapNashSaturationMinimum reward origin minimum
  originDebt_pos : 0 < quittingTerminalSemanticDebtSum origin.1
  minimumDebt_pos : 0 < quittingTerminalSemanticDebtSum minimum.1
  terminalMass_pos : 0 < minimum.2 (some terminal)
  origin_globalMinimum : ∀ candidate ∈
      quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum origin.1 ≤
      quittingTerminalSemanticDebtSum candidate
  originDebt_eq_minimumDebt :
    quittingTerminalSemanticDebtSum origin.1 =
      quittingTerminalSemanticDebtSum minimum.1
  minimum_globalMinimum : ∀ candidate ∈
      quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum.1 ≤
      quittingTerminalSemanticDebtSum candidate
  originDebt_le_singletonGap : ∀ who,
    quittingTerminalSemanticDebtSum origin.1 ≤
      minimum.1.2 who - reward (quittingSingletonTerminal who) who
  alternative : FinFourLawTightGlobalMinimumProducerAlternative
    reward origin minimum

/-- The no-uniform-payoff classifier admits a same-point causal
minimum-atom producer exactly in its full-debt arm. -/
theorem nonempty_finFourLawTightGlobalMinimumProducerTwoChamber
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    Nonempty (FinFourLawTightGlobalMinimumProducerTwoChamber reward) := by
  obtain ⟨origin, minimum, terminal, horigin, hsaturation,
      horiginPositive, hminimumPositive, hatom, horiginGlobal, heq,
      hminimumGlobal, hmoat, hbranch⟩ :=
    finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber
      reward hno
  obtain ⟨residual⟩ :=
    nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
      reward (abs_reward_le_quittingRewardBound reward) hno
  have hminimumLaw : minimum ∈
      quittingTerminalSemanticLawCarrier reward :=
    quittingLawTightCapNashSaturationHull_subset_carrier
      reward origin horigin hsaturation.mem
  have hminimumSemantic : minimum.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier minimum hminimumLaw
  obtain ⟨causalAtom⟩ :=
    finFourHardResidual_minimumLaw_causalSuffixAtom
      reward (quittingRewardBound reward) residual minimum hminimumLaw
        hminimumGlobal
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hdebtInf : quittingTerminalSemanticDebtSum minimum.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      minimum.1 hminimumSemantic hminimumGlobal).symm
  let source : FinFourMinimumAtomProducer reward
      (quittingRewardBound reward) := {
    residual := residual
    point := minimum
    point_mem := hminimumLaw
    semantic_mem := hminimumSemantic
    minimum := hminimumGlobal
    inf_pos := hinf
    debt_eq_inf := hdebtInf
    atom := causalAtom
  }
  have halternative : FinFourLawTightGlobalMinimumProducerAlternative
      reward origin minimum := by
    rcases hbranch with hfullDebt | hresetRigid
    · exact .fullDebt source rfl (by simpa only [source] using hfullDebt)
    · obtain ⟨chamber⟩ := hresetRigid
      exact .resetRigid chamber
  exact ⟨{
    origin := origin
    minimum := minimum
    terminal := terminal
    origin_mem := horigin
    saturationMinimum := hsaturation
    originDebt_pos := horiginPositive
    minimumDebt_pos := hminimumPositive
    terminalMass_pos := hatom
    origin_globalMinimum := horiginGlobal
    originDebt_eq_minimumDebt := heq
    minimum_globalMinimum := hminimumGlobal
    originDebt_le_singletonGap := hmoat
    alternative := halternative
  }⟩

namespace FinFourLawTightGlobalMinimumProducerTwoChamber

/-- Only the full-debt classifier arm enters the supplied-source cap-band
dispatch; the original reset-rigid chamber is returned unchanged. -/
theorem nonempty_fullDebtTargetDispatch_or_resetRigid
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (result : FinFourLawTightGlobalMinimumProducerTwoChamber reward)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    (∃ source : FinFourMinimumAtomProducer reward
        (quittingRewardBound reward),
      source.point = result.minimum ∧
      Nonempty (FinFourFullDebtCapBandTargetDispatch
        source M weight hweight0 hweight1)) ∨
      Nonempty (QuittingLawTightResetRigidChamber reward result.origin
        result.minimum result.minimum result.origin.1) := by
  cases result.alternative with
  | fullDebt source hsource hfullDebt =>
      left
      refine ⟨source, hsource, ?_⟩
      exact nonempty_finFourFullDebtCapBandTargetDispatch
        source hfullDebt M hM hreward weight hweight0 hweight1
  | resetRigid chamber =>
      exact Or.inr ⟨chamber⟩

end FinFourLawTightGlobalMinimumProducerTwoChamber

/-- Direct no-uniform-payoff entrance: the same classifier result either
feeds the supplied-source full-debt target dispatch or retains its original
reset-rigid chamber. -/
theorem finFour_noUniformPayoff_exists_fullDebtTargetDispatch_or_resetRigid
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    ∃ result : FinFourLawTightGlobalMinimumProducerTwoChamber reward,
      ((∃ source : FinFourMinimumAtomProducer reward
          (quittingRewardBound reward),
        source.point = result.minimum ∧
        Nonempty (FinFourFullDebtCapBandTargetDispatch
          source M weight hweight0 hweight1)) ∨
        Nonempty (QuittingLawTightResetRigidChamber reward result.origin
          result.minimum result.minimum result.origin.1)) := by
  obtain ⟨result⟩ :=
    nonempty_finFourLawTightGlobalMinimumProducerTwoChamber reward hno
  exact ⟨result,
    result.nonempty_fullDebtTargetDispatch_or_resetRigid
      M hM hreward weight hweight0 hweight1⟩

end GameTheory
