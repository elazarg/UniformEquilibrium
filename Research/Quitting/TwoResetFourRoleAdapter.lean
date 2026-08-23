/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawGlobalRetention
import Research.General.FiveCycleIncidenceSupportRigidity

/-!
# Two-reset four-role adapter for a five-player minimum

This file combines two facts:

1. a minimum half reset followed through a positive recipient either creates
   a quantitative total-debt excess, or gives a second directed half reset
   while retaining one quarter of every original chronological atom;
2. two composable directed edges with one fixed incidence player use at most
   four of five labels.

The result is the strongest honest local cardinal packet currently available.
It does **not** construct a four-player reward table and does not prove that a
five-player counterexample yields a four-player counterexample.  The omitted
player may still affect the conditional payoff table and the excess branch
still needs a strategic consumer.
-/


noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

/-- **Two directed resets give a four-role window or a first-target excess
charge.**  The returned targets are literal behavior profiles.  In the
four-role branch every original finite atom is retained at quarter strength. -/
theorem exists_twoReset_fourRoleWindow_or_excessCharge
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (profile : (quittingGame reward).BehaviorProfile)
    (firstMover incidenceLabel : Fin 5)
    (hfirstDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) firstMover)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ firstTargetProfile : (quittingGame reward).BehaviorProfile,
      let source := quittingTerminalSemanticPair reward profile
      let firstTarget := quittingTerminalSemanticPair reward firstTargetProfile
      let excess := quittingTerminalSemanticDebtSum firstTarget -
        quittingTerminalSemanticDebtSum source
      ∃ secondMover ∈ Finset.univ.erase firstMover,
        0 < quittingTerminalSemanticDebtChange source firstTarget secondMover ∧
        0 < quittingTerminalSemanticDebt firstTarget secondMover ∧
        0 ≤ excess ∧
        (∀ terminal time,
          (1 / 2) * quittingStageCoalitionMass reward profile time terminal ≤
            quittingStageCoalitionMass reward firstTargetProfile time terminal) ∧
        (quittingTerminalSemanticDebt firstTarget secondMover / 4 ≤ excess ∨
          ∃ secondTargetProfile : (quittingGame reward).BehaviorProfile,
            ∃ thirdMover ∈ Finset.univ.erase secondMover,
              0 < quittingTerminalSemanticDebtChange firstTarget
                (quittingTerminalSemanticPair reward secondTargetProfile)
                thirdMover ∧
              ∃ omitted,
                omitted ∉
                    ({firstMover, secondMover, incidenceLabel} :
                      Finset (Fin 5)) ∪
    {secondMover, thirdMover, incidenceLabel} ∧
                ∀ terminal time,
                  (1 / 4) *
                      quittingStageCoalitionMass reward profile time terminal ≤
                    quittingStageCoalitionMass reward secondTargetProfile
                      time terminal) := by
  obtain ⟨firstBestResponse, hfirst⟩ :=
    exists_twoMatchedHalfResets_or_firstExcessCharge
      reward profile firstMover hfirstDebt hminimum
  dsimp only at hfirst
  let firstMixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward firstMover (profile firstMover) firstBestResponse
      (1 / 2) (by norm_num) (by norm_num)
  let firstTargetProfile :=
    Function.update profile firstMover firstMixedStrategy
  obtain ⟨secondMover, hsecondMem, hsecondChange, hsecondDebt, hexcess,
      hhalfRetention, hcase⟩ := hfirst
  refine ⟨firstTargetProfile, secondMover, hsecondMem, hsecondChange,
    hsecondDebt, hexcess, hhalfRetention, ?_⟩
  rcases hcase with hexcessCharge | htwo
  · exact Or.inl hexcessCharge
  · right
    obtain ⟨secondBestResponse, hsecond⟩ := htwo
    let secondMixedStrategy :=
      quittingStoppingLawMixtureBehaviorStrategy reward secondMover
        (firstTargetProfile secondMover) secondBestResponse
        (1 / 2) (by norm_num) (by norm_num)
    let secondTargetProfile :=
      Function.update firstTargetProfile secondMover secondMixedStrategy
    obtain ⟨thirdMover, hthirdMem, hthirdChange, hquarterRetention⟩ := hsecond
    obtain ⟨omitted, homitted⟩ :=
      exists_omitted_matchedTwoEdgeWindow_of_constantIncidence
        firstMover secondMover thirdMover incidenceLabel
    exact ⟨secondTargetProfile, thirdMover, hthirdMem, hthirdChange,
      omitted, homitted, hquarterRetention⟩

end GameTheory
