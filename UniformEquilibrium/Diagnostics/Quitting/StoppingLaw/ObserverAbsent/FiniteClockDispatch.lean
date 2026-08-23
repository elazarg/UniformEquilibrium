/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticForcedOwnerRefusalCollector
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ForcedOwnerRectangleBaseline
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ForcedOwnerDefectPolarity

/-!
# Observer-absent finite-clock strategic dispatch

This module applies the generic finite forced-owner polarity dispatch to an
observer-absent stopping-law rectangle packet, then refines its rectangle arm
by the source/baseline decomposition.  The remaining alternatives retain their
literal carrier, terminal label, and finite chronology.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Complete finite observer-absent consumer.**  On a finite preemption
clock the observer-absent wall reaches, with literal-profile provenance,
either the fixed owner's refusal deviation, a fixed-player Continue
deviation, a fixed Quit-directed coalition atom, or a fixed outsider/action
same-witness rectangle.  The last alternative is the sole uncompiled term. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_finiteClock_defectPolarity
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    let charge := quittingStoppingLawObserverAbsentMassLower packet *
      witness.terminalGap
    (∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      charge / 2 - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner) ∨
    (∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      charge / 12 ≤ (Fintype.card ι : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who)) ∨
    (∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      charge / 12 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) stop who coalition)) ∨
    (∃ who action, who ≠ owner ∧
      charge / 12 ≤ (Fintype.card (ι × Bool) : ℝ) *
        quittingFiniteForcedOwnerRectangleOccupation reward profile
          packet.terminal owner who action stop) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    witness.terminalGap
  have hchargePos : 0 < charge := mul_pos
    packet.observerAbsentMassLower_pos witness.terminalGap_pos
  have hsplit := packet.observerAbsent_finiteClock_strategicSplit
    (witness := witness) habsent n stop hstop δ hδ
  rcases hsplit with houtside | ⟨deviation, hdeviation⟩
  · have hdispatch :=
      exists_continueDeviation_or_fixedQuitAtom_or_fixedRectangle_of_forcedOwnerOccupation
        reward profile packet.terminal owner
        (quittingStoppingLawObserverAbsentOwner_mem packet) stop
        (charge / 2) (div_pos hchargePos (by norm_num))
        (by simpa only [profile, owner, charge] using houtside)
    rcases hdispatch with hcontinue | hquit | hrectangle
    · right; left
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hcontinue
    · right; right; left
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hquit
    · right; right; right
      simpa only [show (charge / 2) / 6 = charge / 12 by ring] using hrectangle
  · left
    exact ⟨deviation, by simpa only [profile, owner, charge] using hdeviation⟩

/-- **Complete finite-clock baseline dispatch.**  The fixed-rectangle arm of
the polarity dispatch is replaced by a source-matched action consumer or one
explicit signed owner-Continue-face loss.  The last line is therefore the
sole residual of the observer-absent finite clock. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_finiteClock_faceLoss
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n stop : ℕ) (hstop : packet.quitTime n = some stop)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    let charge := quittingStoppingLawObserverAbsentMassLower packet *
      witness.terminalGap
    (∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      charge / 2 - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner) ∨
    (∃ who : ι, ∃ deviation : (quittingGame reward).BehaviorStrategy who,
      charge / 12 ≤ (Fintype.card ι : ℝ) *
        (quittingTerminalPayoff reward
            (Function.update profile who deviation) who -
          quittingTerminalPayoff reward profile who)) ∨
    (∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      charge / 12 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) stop who coalition)) ∨
    (∃ who action, who ≠ owner ∧
      ((action = false ∧
        ∃ deviation : (quittingGame reward).BehaviorStrategy who,
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who) ∨
       (action = true ∧
        ∃ coalition ∈ (Finset.univ.erase who).powerset,
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            (((Finset.univ.erase who).powerset.card : ℝ) *
              quittingFiniteQuitDefectAtomOccupationAt reward
                (fun time => (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).1)
                (quittingProfileLiveRoot reward profile)
                (quittingLiveMass reward profile) stop who coalition)) ∨
       charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
        quittingFiniteForcedOwnerContinueFaceLossOccupation reward profile
          owner who action stop)) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    witness.terminalGap
  have hdispatch := packet.observerAbsent_finiteClock_defectPolarity
    (witness := witness) habsent n stop hstop δ hδ
  rcases hdispatch with hrefusal | hcontinue | hquit | hrectangle
  · exact Or.inl hrefusal
  · exact Or.inr (Or.inl hcontinue)
  · exact Or.inr (Or.inr (Or.inl hquit))
  · rcases hrectangle with ⟨who, action, hwho, hcharge⟩
    have hlabelCard : 0 < (Fintype.card (ι × Bool) : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨(owner, false)⟩
    have hrectangleLower :
        charge / (12 * (Fintype.card (ι × Bool) : ℝ)) ≤
          quittingFiniteForcedOwnerRectangleOccupation reward profile
            packet.terminal owner who action stop := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hlabelCard)).2
      calc
        charge = 12 * (charge / 12) := by ring
        _ ≤ 12 * ((Fintype.card (ι × Bool) : ℝ) *
            quittingFiniteForcedOwnerRectangleOccupation reward profile
              packet.terminal owner who action stop) :=
          mul_le_mul_of_nonneg_left hcharge (by norm_num)
        _ = quittingFiniteForcedOwnerRectangleOccupation reward profile
              packet.terminal owner who action stop *
            (12 * (Fintype.card (ι × Bool) : ℝ)) := by ring
    have hrefined :=
      exists_sourceConsumer_or_continueFaceLoss_of_rectangleOccupation
        reward profile packet.terminal owner who hwho.symm
        (quittingStoppingLawObserverAbsentOwner_mem packet) action stop
        (charge / (12 * (Fintype.card (ι × Bool) : ℝ))) hrectangleLower
    right; right; right
    refine ⟨who, action, hwho, ?_⟩
    simpa only [show
      (charge / (12 * (Fintype.card (ι × Bool) : ℝ))) / 2 =
        charge / (24 * (Fintype.card (ι × Bool) : ℝ)) by ring] using hrefined

end GameTheory
