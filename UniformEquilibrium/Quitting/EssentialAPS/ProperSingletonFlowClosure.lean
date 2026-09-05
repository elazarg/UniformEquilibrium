/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCarrierBridge
import UniformEquilibrium.Quitting.EssentialAPS.Basic

/-!
# Proper viable singleton-flow closure

A proper singleton arc from a uniform-payoff continuation is executable when
both endpoints are viable and the active owner's coordinate is pinned to its
singleton payoff.  The implementation is the limit of literal finite
positive-hazard singleton blocks, so deviations remain unrestricted.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open IdealSingletonCarrierBridge
open IdealSingletonBlockApproximation
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A proper viable singleton segment leading to a uniform-payoff tail has a
uniform-payoff source. -/
theorem isUniformEquilibriumPayoff_singletonArc_of_viable_proper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (source tail : Payoff ι)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (hactive : source owner = quittingSoloReward reward owner owner)
    (hsourceViable : QuittingEssentialAPSViable reward source)
    (htailViable : QuittingEssentialAPSViable reward tail)
    (htail : (quittingGame reward).IsUniformEquilibriumPayoff none tail) :
    (quittingGame reward).IsUniformEquilibriumPayoff none source := by
  let α := 1 - p
  have hα0 : 0 < α := sub_pos.mpr hp.2
  have hα1 : α ≤ 1 := by linarith [hp.1]
  let pair : QuittingTerminalSemanticPair ι := (tail, tail)
  have hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who := by
    intro who
    exact sub_nonneg.mpr (htailViable who)
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward :=
    diagonal_mem_terminalSemanticCarrier_of_isUniformEquilibriumPayoff
      reward tail htail
  have hideal : idealSingletonSemanticPair reward owner α pair ∈
      quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair owner α hα0 hα1
      hclearance hpair
  have hownerTail : tail owner = quittingSoloReward reward owner owner := by
    have hcoordinate := congrFun harc owner
    simp only [quittingSingletonArcPayoff] at hcoordinate
    rw [hactive] at hcoordinate
    nlinarith [sub_pos.mpr hp.2]
  have hterminal (who : ι) :
      reward (quittingProjectiveSingletonTerminal owner) who =
        quittingSoloReward reward owner who := by
    congr 2
  have hsolo (who : ι) : quittingSoloReward reward owner who =
      reward (quittingSingletonTerminal owner) who := rfl
  have hidealEq : idealSingletonSemanticPair reward owner α pair =
      (source, source) := by
    apply Prod.ext
    · funext who
      rw [harc]
      simp [idealSingletonSemanticPair, pair, α,
        quittingSingletonArcPayoff, quittingProjectiveSingletonTerminal]
      change (1 - p) * tail who + p *
          reward (quittingProjectiveSingletonTerminal owner) who = _
      rw [hterminal]
      rw [hsolo]
      ring
    · funext who
      by_cases hwho : who = owner
      · subst who
        simp [idealSingletonSemanticPair, idealSingletonClearance, pair,
          capClearance, ownSingleton, hownerTail, hactive]
      · have hsourceLower := hsourceViable who
        have hsourceFormula := congrFun harc who
        simp only [quittingSingletonArcPayoff] at hsourceFormula
        unfold idealSingletonSemanticPair idealSingletonClearance
        dsimp only [Prod.snd, pair]
        rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
        simp [capClearance, ownSingleton, hwho,
          quittingProjectiveLCPMatrix]
        rw [hterminal]
        rw [max_eq_right]
        · dsimp only [α]
          linarith
        · dsimp only [α]
          have hbaseline :
              reward (quittingProjectiveSingletonTerminal who) who =
                quittingSoloBaseline reward who := by
            congr 2
          rw [hbaseline]
          nlinarith
  apply isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
  rw [← hidealEq]
  exact hideal

/-- A finite chronological list of proper viable singleton segments.  The
zero-length chain is included; every nontrivial step stores both endpoint
viability and the active-owner equality needed by the executable closure. -/
inductive IsProperViableSingletonFlowChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Payoff ι → Payoff ι → Prop
  | refl (tail : Payoff ι) :
      IsProperViableSingletonFlowChain reward tail tail
  | cons (source middle tail : Payoff ι) (owner : ι) (p : ℝ)
      (hp : p ∈ Set.Ioo (0 : ℝ) 1)
      (harc : source = quittingSingletonArcPayoff p
        (quittingSoloReward reward owner) middle)
      (hactive : source owner = quittingSoloReward reward owner owner)
      (hsourceViable : QuittingEssentialAPSViable reward source)
      (hmiddleViable : QuittingEssentialAPSViable reward middle)
      (rest : IsProperViableSingletonFlowChain reward middle tail) :
      IsProperViableSingletonFlowChain reward source tail

/-- Any finite list of proper viable singleton segments may be prefixed to a
uniform-payoff tail. -/
theorem IsProperViableSingletonFlowChain.isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {source tail : Payoff ι}
    (hchain : IsProperViableSingletonFlowChain reward source tail)
    (htail : (quittingGame reward).IsUniformEquilibriumPayoff none tail) :
    (quittingGame reward).IsUniformEquilibriumPayoff none source := by
  induction hchain with
  | refl => exact htail
  | cons source middle tail owner p hp harc hactive hsource hmiddle rest ih =>
      exact isUniformEquilibriumPayoff_singletonArc_of_viable_proper
        reward owner p source middle hp harc hactive hsource hmiddle (ih htail)

end GameTheory
