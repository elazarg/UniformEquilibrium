/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CertifiedForcedOwnerEndpointFlip
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow

/-!
# The observer-absent Never clock has a finite charged prefix

The `quitTime = none` branch is not intrinsically infinitary.  Its selected
terminal mass is a nonnegative chronological sum.  Since that mass has a
uniform positive lower bound, a finite prefix already carries half of the
lower bound.  The forced-owner row barrier and the finite refusal collector
can therefore be applied on that prefix.

The only loss relative to a literal finite stopping time is a factor two.
After truncation, the residual is the same certified owner/outsider endpoint
flip as in the finite-clock theorem.  This file deliberately does not claim
that the selected cutoff is uniform in the packet index, nor that the
endpoint-flip labels are compatible across indices.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Never-clock finite-prefix strategic split.**  Half of the terminal
mass lower bound is captured by one finite prefix.  On that prefix, either
one quarter of the original wall charge is forced-outsider defect, or one
legal owner deviation collects one quarter up to the requested approximation
loss. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_neverClock_strategicSplit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n : ℕ) (hnever : packet.quitTime n = none)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    ∃ cutoff : ℕ,
      quittingStoppingLawObserverAbsentMassLower packet *
            regime.terminalGap / 4 ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time packet.terminal *
              quittingForcedOwnerOutsiderDefect reward
                (Function.update
                  (quittingProfileLiveRoot reward profile time) owner
                  (PMF.pure true)) owner ∨
        ∃ deviation : (quittingGame reward).BehaviorStrategy owner,
          quittingStoppingLawObserverAbsentMassLower packet *
                regime.terminalGap / 4 - δ ≤
            quittingTerminalPayoff reward
                (Function.update profile owner deviation) owner -
              quittingTerminalPayoff reward profile owner := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  have hdispatch := packet.observerAbsent_forcedOwnerDispatch habsent
  unfold HasQuittingStoppingLawObserverAbsentForcedOwnerDispatch at hdispatch
  rcases hdispatch with
    ⟨howner, _hownerNe, hlowerPos, _hside, hmassLower,
      _hweightedLower, _hclock, hrows⟩
  have hhalf : quittingStoppingLawObserverAbsentMassLower packet / 2 <
      quittingTerminalOutcomeMass reward profile
        (some packet.terminal) := by
    have hlower := hmassLower n
    dsimp only [profile] at hlower ⊢
    linarith
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_finiteWindow_sum_stageCoalitionMass_gt
      profile packet.terminal hhalf
  refine ⟨cutoff, ?_⟩
  let outsiderCharge := ∑ time ∈ Finset.range cutoff,
    quittingStageCoalitionMass reward profile time packet.terminal *
      quittingForcedOwnerOutsiderDefect reward
        (Function.update (quittingProfileLiveRoot reward profile time)
          owner (PMF.pure true)) owner
  let refusalCharge := ∑ time ∈ Finset.range cutoff,
    quittingStageCoalitionMass reward profile time packet.terminal *
      max 0 (-quittingAtomicBlockerBalance reward
        (Function.update (quittingProfileLiveRoot reward profile time)
          owner (PMF.pure true)) owner)
  have hrowSum :
      (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time
            packet.terminal) * regime.terminalGap ≤
        outsiderCharge + refusalCharge := by
    rw [Finset.sum_mul]
    have hsum :
        (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time packet.terminal *
              regime.terminalGap) ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time packet.terminal *
              (quittingForcedOwnerOutsiderDefect reward
                  (Function.update
                    (quittingProfileLiveRoot reward profile time) owner
                    (PMF.pure true)) owner +
                max 0 (-quittingAtomicBlockerBalance reward
                  (Function.update
                    (quittingProfileLiveRoot reward profile time) owner
                    (PMF.pure true)) owner)) :=
      Finset.sum_le_sum fun time _htime => by
      have hrow := hrows n time (by simp [hnever])
      dsimp only at hrow
      rcases hrow with
        ⟨_hobserver, _hforcedProfile, _hmassCylinder, _hbarrier,
          hweightedBarrier, _halternative⟩
      let mass := quittingStageCoalitionMass reward profile time
        packet.terminal
      let forcedRoot := Function.update
        (quittingProfileLiveRoot reward profile time) owner
          (PMF.pure true)
      have hout0 : 0 ≤
          quittingForcedOwnerOutsiderDefect reward forcedRoot owner :=
        quittingForcedOwnerOutsiderDefect_nonneg reward forcedRoot owner
      have hrefusal0 : 0 ≤
          max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) :=
        le_max_left _ _
      have hmax : max
          (quittingForcedOwnerOutsiderDefect reward forcedRoot owner)
          (max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner)) ≤
        quittingForcedOwnerOutsiderDefect reward forcedRoot owner +
          max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) :=
        max_le (le_add_of_nonneg_right hrefusal0)
          (le_add_of_nonneg_left hout0)
      have hmass0 : 0 ≤ mass :=
        quittingStageCoalitionMass_nonneg reward profile time
          packet.terminal
      exact hweightedBarrier.trans
        (mul_le_mul_of_nonneg_left hmax hmass0)
    simpa [outsiderCharge, refusalCharge, mul_add,
      Finset.sum_add_distrib] using hsum
  have htotal :
      quittingStoppingLawObserverAbsentMassLower packet *
          regime.terminalGap / 2 ≤ outsiderCharge + refusalCharge := by
    calc
      quittingStoppingLawObserverAbsentMassLower packet *
            regime.terminalGap / 2 =
          (quittingStoppingLawObserverAbsentMassLower packet / 2) *
            regime.terminalGap := by ring
      _ ≤ (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time
            packet.terminal) * regime.terminalGap :=
        mul_le_mul_of_nonneg_right (le_of_lt hcutoff)
          regime.terminalGap_pos.le
      _ ≤ outsiderCharge + refusalCharge := hrowSum
  by_cases hout : quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap / 4 ≤ outsiderCharge
  · exact Or.inl hout
  · right
    have hrefusal : quittingStoppingLawObserverAbsentMassLower packet *
        regime.terminalGap / 4 ≤ refusalCharge := by
      linarith
    obtain ⟨deviation, hdeviation⟩ :=
      exists_behaviorDeviation_gain_ge_sum_forcedRefusal_sub reward
        profile packet.terminal owner howner cutoff δ hδ
    refine ⟨deviation, ?_⟩
    dsimp only [refusalCharge] at hrefusal hdeviation
    exact (sub_le_sub_right hrefusal δ).trans hdeviation

/-- **Never-clock endpoint-flip frontier.**  After finite truncation, the
complete Never clock has exactly the same four strategic outputs as a finite
clock.  The constants lose only the factor two used to capture a finite
prefix of the terminal mass. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_neverClock_certifiedEndpointFlip
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n : ℕ) (hnever : packet.quitTime n = none)
    (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    let charge := quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap
    (∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      charge / 4 - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner) ∨
    (∃ _cutoff : ℕ, ∃ who : ι,
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        charge / 24 ≤ (Fintype.card ι : ℝ) *
          (quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who)) ∨
    (∃ cutoff : ℕ, ∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      charge / 24 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) cutoff who coalition)) ∨
    (∃ cutoff : ℕ, ∃ who action, who ≠ owner ∧
      ((action = false ∧
        ∃ deviation : (quittingGame reward).BehaviorStrategy who,
          charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who) ∨
       (action = true ∧
        ∃ coalition ∈ (Finset.univ.erase who).powerset,
          charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
            (((Finset.univ.erase who).powerset.card : ℝ) *
              quittingFiniteQuitDefectAtomOccupationAt reward
                (fun time => (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).1)
                (quittingProfileLiveRoot reward profile)
                (quittingLiveMass reward profile) cutoff who coalition)) ∨
       charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
        quittingFiniteCertifiedPacketContinueFaceLoss reward profile
          packet.terminal owner who action cutoff)) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  have hchargePos : 0 < charge := mul_pos
    packet.observerAbsentMassLower_pos regime.terminalGap_pos
  obtain ⟨cutoff, hforced | hrefusal⟩ :=
    packet.observerAbsent_neverClock_strategicSplit habsent n hnever δ hδ
  · have hdispatch :=
      exists_continueDeviation_or_fixedQuitAtom_or_certifiedRectanglePacket
        reward profile packet.terminal owner cutoff (charge / 4)
          (div_pos hchargePos (by norm_num)) hforced
    rcases hdispatch with hcontinue | hquit | hcertified
    · right; left
      refine ⟨cutoff, ?_⟩
      simpa only [show (charge / 4) / 6 = charge / 24 by ring]
        using hcontinue
    · right; right; left
      refine ⟨cutoff, ?_⟩
      simpa only [show (charge / 4) / 6 = charge / 24 by ring]
        using hquit
    · rcases hcertified with ⟨who, action, hwho, hpacket⟩
      have hlabelCard : 0 < (Fintype.card (ι × Bool) : ℝ) := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨(owner, false)⟩
      have hpacketLower :
          charge / (24 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile
              packet.terminal owner who action cutoff := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hlabelCard)).2
        calc
          charge = 24 * (charge / 24) := by ring
          _ ≤ 24 * ((Fintype.card (ι × Bool) : ℝ) *
              quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile
                packet.terminal owner who action cutoff) :=
            mul_le_mul_of_nonneg_left (by
              simpa only [show (charge / 4) / 6 = charge / 24 by ring]
                using hpacket) (by norm_num)
          _ = quittingFiniteCertifiedForcedOwnerRectanglePacket reward profile
                packet.terminal owner who action cutoff *
              (24 * (Fintype.card (ι × Bool) : ℝ)) := by ring
      have hrefined := exists_sourceConsumer_or_certifiedEndpointFlipLoss
        reward profile packet.terminal owner who action cutoff hwho.symm
          (quittingStoppingLawObserverAbsentOwner_mem packet)
          (charge / (24 * (Fintype.card (ι × Bool) : ℝ))) hpacketLower
      right; right; right
      refine ⟨cutoff, who, action, hwho, ?_⟩
      simpa only [show
        (charge / (24 * (Fintype.card (ι × Bool) : ℝ))) / 2 =
          charge / (48 * (Fintype.card (ι × Bool) : ℝ)) by ring]
        using hrefined
  · left
    exact hrefusal

/-- **Clock-free endpoint-flip frontier.**  The finite-stop and complete-Never
branches have one common statement.  Every packet index has a finite
certificate with the Never-clock constants; no residual alternative refers
to the stopping time being infinite. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.observerAbsent_anyClock_certifiedEndpointFlip
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (habsent : packet.observer ∉ packet.terminal.val)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
    let owner := quittingStoppingLawObserverAbsentOwner packet
    let charge := quittingStoppingLawObserverAbsentMassLower packet *
      regime.terminalGap
    (∃ deviation : (quittingGame reward).BehaviorStrategy owner,
      charge / 4 - δ ≤
        quittingTerminalPayoff reward
            (Function.update profile owner deviation) owner -
          quittingTerminalPayoff reward profile owner) ∨
    (∃ _cutoff : ℕ, ∃ who : ι,
      ∃ deviation : (quittingGame reward).BehaviorStrategy who,
        charge / 24 ≤ (Fintype.card ι : ℝ) *
          (quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who)) ∨
    (∃ cutoff : ℕ, ∃ who coalition,
      coalition ∈ (Finset.univ.erase who).powerset ∧
      charge / 24 ≤
        (Fintype.card ι : ℝ) *
          (((Finset.univ.erase who).powerset.card : ℝ) *
            quittingFiniteQuitDefectAtomOccupationAt reward
              (fun time => (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (time + 1))).1)
              (quittingProfileLiveRoot reward profile)
              (quittingLiveMass reward profile) cutoff who coalition)) ∨
    (∃ cutoff : ℕ, ∃ who action, who ≠ owner ∧
      ((action = false ∧
        ∃ deviation : (quittingGame reward).BehaviorStrategy who,
          charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
            quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who) ∨
       (action = true ∧
        ∃ coalition ∈ (Finset.univ.erase who).powerset,
          charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
            (((Finset.univ.erase who).powerset.card : ℝ) *
              quittingFiniteQuitDefectAtomOccupationAt reward
                (fun time => (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).1)
                (quittingProfileLiveRoot reward profile)
                (quittingLiveMass reward profile) cutoff who coalition)) ∨
       charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
        quittingFiniteCertifiedPacketContinueFaceLoss reward profile
          packet.terminal owner who action cutoff)) := by
  classical
  dsimp only
  let profile := quittingStoppingLawObserverAbsentCarrierProfile packet n
  let owner := quittingStoppingLawObserverAbsentOwner packet
  let charge := quittingStoppingLawObserverAbsentMassLower packet *
    regime.terminalGap
  have hchargePos : 0 < charge := mul_pos
    packet.observerAbsentMassLower_pos regime.terminalGap_pos
  cases htime : packet.quitTime n with
  | none =>
      exact packet.observerAbsent_neverClock_certifiedEndpointFlip habsent n
        htime δ hδ
  | some stop =>
      have hfinite := packet.observerAbsent_finiteClock_certifiedEndpointFlip
        habsent n stop htime δ hδ
      rcases hfinite with howner | hcontinue | hquit | hflip
      · left
        obtain ⟨deviation, hgain⟩ := howner
        exact ⟨deviation, by linarith⟩
      · right; left
        obtain ⟨who, deviation, hgain⟩ := hcontinue
        exact ⟨stop, who, deviation, by linarith⟩
      · right; right; left
        obtain ⟨who, coalition, hcoalition, hgain⟩ := hquit
        exact ⟨stop, who, coalition, hcoalition, by linarith⟩
      · right; right; right
        have hlabelCard : 0 < (Fintype.card (ι × Bool) : ℝ) := by
          exact_mod_cast Fintype.card_pos_iff.mpr ⟨(owner, false)⟩
        have hlabelLower :
            charge / (48 * (Fintype.card (ι × Bool) : ℝ)) ≤
              charge / (24 * (Fintype.card (ι × Bool) : ℝ)) := by
          have hbasePos : 0 <
              charge / (24 * (Fintype.card (ι × Bool) : ℝ)) :=
            div_pos hchargePos (mul_pos (by norm_num) hlabelCard)
          rw [show charge / (48 * (Fintype.card (ι × Bool) : ℝ)) =
            (charge / (24 * (Fintype.card (ι × Bool) : ℝ))) / 2 by ring]
          linarith
        obtain ⟨who, action, hwho, hsource | hsource | hloss⟩ := hflip
        · refine ⟨stop, who, action, hwho, Or.inl ?_⟩
          obtain ⟨haction, deviation, hgain⟩ := hsource
          exact ⟨haction, deviation, hlabelLower.trans hgain⟩
        · refine ⟨stop, who, action, hwho, Or.inr (Or.inl ?_)⟩
          obtain ⟨haction, coalition, hcoalition, hgain⟩ := hsource
          exact ⟨haction, coalition, hcoalition, hlabelLower.trans hgain⟩
        · refine ⟨stop, who, action, hwho, Or.inr (Or.inr ?_)⟩
          exact hlabelLower.trans hloss

end GameTheory
