/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticBoundedSelfReset
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSelfTailClosure
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.Collision.BoundedSelfResetLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawFiniteSpliceMarkedLaw
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Finite pure-time reset arrival

This file turns the uniform terminal-debt floor into a finite profitable path
of literal pure-time updates.  Once one player has a finite stopping deadline,
every other player's behavioral best-reply value is attained by `Never` or by
one of the finitely many stopping times through that deadline.  At most two
exact best responses then produce a zero-debt player with positive opponent
incidence.
-/

noncomputable section

namespace GameTheory

open Finset Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A pure stopping time strictly after a distinct opponent's literal finite
deadline has exactly the payoff of `Never`. -/
theorem quittingTerminalPayoff_update_pureTime_eq_none_of_opponent_stops_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who stopper : ι) (deadline time : ℕ) (hne : stopper ≠ who)
    (hstopper : profile stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline))
    (hlt : deadline < time) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  have htransport := quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
    reward (quittingProfileLiveRoot reward profile) who 0 time
  simp only [Nat.zero_add] at htransport
  have hsurvival : quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward profile) who 0 time = 0 := by
    unfold quittingOpponentSurvivalWeight
    apply Finset.prod_eq_zero (show deadline ∈ Finset.range time by simpa)
    unfold quittingFixedOpponentsContinueMass
      quittingStationaryContinueMass
    rw [pmfPi_apply, ENNReal.toReal_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ stopper)
    rw [Function.update_of_ne hne]
    simp only [quittingProfileLiveRoot, quittingAllContinueAction]
    rw [hstopper]
    simp [quittingPureTimeBehaviorStrategy]
  rw [hsurvival, zero_mul] at htransport
  linarith

/-- Against a distinct player who literally Quits at a finite deadline, the
full behavioral best-reply envelope is attained by `Never` or by a pure time
no later than that deadline. -/
theorem exists_pureTime_bestReply_of_opponent_quitsAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who stopper : ι) (deadline : ℕ) (hne : stopper ≠ who)
    (hstopper : profile stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline)) :
    ∃ choice : Option ℕ,
      (choice = none ∨ ∃ time ≤ deadline, choice = some time) ∧
      quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice)) who =
        quittingContinuationBestResponseValue reward profile who := by
  let candidates : Finset (Option ℕ) :=
    insert none ((Finset.range (deadline + 1)).image some)
  let payoff : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hcandidates : candidates.Nonempty := by
    exact ⟨none, by simp [candidates]⟩
  have hvalues : (candidates.image payoff).Nonempty := hcandidates.image payoff
  let bestValue := (candidates.image payoff).max' hvalues
  have hbestMem : bestValue ∈ candidates.image payoff :=
    Finset.max'_mem _ _
  obtain ⟨choice, hchoiceMem, hchoiceValue⟩ := Finset.mem_image.mp hbestMem
  refine ⟨choice, ?_, ?_⟩
  · simp only [candidates, Finset.mem_insert, Finset.mem_image,
      Finset.mem_range] at hchoiceMem
    rcases hchoiceMem with rfl | ⟨time, htime, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨time, by omega, rfl⟩
  · have hpureLe : ∀ other : Option ℕ, payoff other ≤ payoff choice := by
      intro other
      have hother : payoff other ≤ bestValue := by
        cases other with
        | none =>
            apply Finset.le_max' (candidates.image payoff) (payoff none)
            exact Finset.mem_image.mpr ⟨none, by simp [candidates], rfl⟩
        | some time =>
            by_cases htime : time ≤ deadline
            · apply Finset.le_max' (candidates.image payoff) (payoff (some time))
              exact Finset.mem_image.mpr ⟨some time, by
                simp [candidates, htime], rfl⟩
            · rw [show payoff (some time) = payoff none by
                dsimp only [payoff]
                exact quittingTerminalPayoff_update_pureTime_eq_none_of_opponent_stops_before
                  reward profile who stopper deadline time hne hstopper
                    (by omega)]
              apply Finset.le_max' (candidates.image payoff) (payoff none)
              exact Finset.mem_image.mpr ⟨none, by simp [candidates], rfl⟩
      simpa only [hchoiceValue] using hother
    have hsupLe : quittingContinuationBestResponseValue reward profile who ≤
        payoff choice := by
      unfold quittingContinuationBestResponseValue
      rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
      apply csSup_le
      · exact Set.range_nonempty _
      · rintro _ ⟨other, rfl⟩
        exact hpureLe other
    have hchoiceLe : payoff choice ≤
        quittingContinuationBestResponseValue reward profile who := by
      dsimp only [payoff]
      exact quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who
          (quittingPureTimeBehaviorStrategy reward who choice)
    exact le_antisymm hchoiceLe hsupLe

omit [DecidableEq ι] in
/-- The canonical first-stage adapter copies every actual live root, not only
the terminal semantic pair. -/
theorem quittingProfileLiveRoot_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingFirstStageAdapter reward profile) =
      quittingProfileLiveRoot reward profile := by
  funext time player
  cases time with
  | zero =>
      simp [quittingProfileLiveRoot, quittingFirstStageAdapter,
        quittingProfileRoot, quittingRootThenContinuationProfile]
  | succ time =>
      change (quittingProfileAllContinueContinuation reward profile) player time
          (Fin.tail (quittingLiveHist reward (time + 1)).1,
            (quittingLiveHist reward (time + 1)).2) =
        profile player (time + 1) (quittingLiveHist reward (time + 1))
      have htail :
          ((Fin.tail (quittingLiveHist reward (time + 1)).1,
              (quittingLiveHist reward (time + 1)).2) :
            (quittingGame reward).Hist time) =
            quittingLiveHist reward time := by
        apply Prod.ext
        · funext index
          rfl
        · rfl
      unfold quittingProfileAllContinueContinuation StochasticGame.shiftProfile
      rw [htail, consHist_allContinue_quittingLiveHist]

omit [DecidableEq ι] in
/-- The first-stage adapter also preserves the complete terminal law. -/
@[simp] theorem quittingTerminalOutcomeMass_firstStageAdapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward
        (quittingFirstStageAdapter reward profile) =
      quittingTerminalOutcomeMass reward profile :=
  funext fun outcome ↦ quittingTerminalOutcomeMass_eq_of_profileLiveRoot_eq
    reward reward _ _
      (quittingProfileLiveRoot_firstStageAdapter reward profile) outcome

/-- Fresh time-zero incidence is bounded by the complete incidence of the
same actual profile. -/
theorem quittingRootOpponentIncidenceMass_profileRoot_le_terminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who other : ι) :
    quittingRootOpponentIncidenceMass who other
        (quittingProfileRoot reward profile) ≤
      quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeMass reward profile) := by
  let root := quittingProfileRoot reward profile
  let continuation := quittingProfileAllContinueContinuation reward profile
  have hlaw := quittingTerminalOutcomeLawPrefix_outcomeMass
    reward root continuation
  have hadapter := quittingTerminalOutcomeMass_firstStageAdapter reward profile
  have htailNonneg : 0 ≤ quittingTerminalOpponentIncidenceMass who other
      (quittingTerminalOutcomeMass reward continuation) :=
    quittingTerminalOpponentIncidenceMass_outcomeMass_nonneg
      reward continuation who other
  have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  change quittingRootOpponentIncidenceMass who other root ≤ _
  rw [← hadapter]
  change quittingRootOpponentIncidenceMass who other root ≤
    quittingTerminalOpponentIncidenceMass who other
      (quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation))
  rw [← hlaw,
    quittingTerminalOpponentIncidenceMass_lawPrefix]
  exact le_add_of_nonneg_right (mul_nonneg hcontinueNonneg htailNonneg)

/-- If no opponent-incidence coordinate of an actual law is positive, every
opponent uses pure Continue at the actual time-zero root. -/
theorem quittingProfileRoot_eq_pureContinue_of_no_positive_terminalIncidence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hincidence : ∀ other, other ≠ who → ¬ 0 <
      quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeMass reward profile)) :
    ∀ other, other ≠ who →
      quittingProfileRoot reward profile other = PMF.pure false := by
  intro other hother
  have hterminalNonneg : 0 ≤
      quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeMass reward profile) :=
    quittingTerminalOpponentIncidenceMass_outcomeMass_nonneg
      reward profile who other
  have hterminalZero :
      quittingTerminalOpponentIncidenceMass who other
          (quittingTerminalOutcomeMass reward profile) = 0 :=
    le_antisymm (le_of_not_gt (hincidence other hother)) hterminalNonneg
  have hrootLe := quittingRootOpponentIncidenceMass_profileRoot_le_terminal
    reward profile who other
  have hrootNonneg : 0 ≤ quittingRootOpponentIncidenceMass who other
      (quittingProfileRoot reward profile) := by
    unfold quittingRootOpponentIncidenceMass
    exact Finset.sum_nonneg fun terminal _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        (quittingProfileRoot reward profile) terminal.val
  have hrootZero : quittingRootOpponentIncidenceMass who other
      (quittingProfileRoot reward profile) = 0 := by
    rw [hterminalZero] at hrootLe
    exact le_antisymm hrootLe hrootNonneg
  exact root_eq_pureContinue_of_opponentIncidence_eq_zero
    who other (quittingProfileRoot reward profile) hother hrootZero

/-- Certain absorption plus absence of opponent incidence concentrates the
complete law on the displayed player's singleton and fixes that player's
payoff to the corresponding solo reward. -/
theorem quittingTerminalPayoff_eq_singleton_of_finitePureTimePlayer_of_no_incidence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who finitePlayer : ι) (stop : ℕ)
    (hfinite : profile finitePlayer =
      quittingPureTimeBehaviorStrategy reward finitePlayer (some stop))
    (hincidence : ∀ other, other ≠ who → ¬ 0 <
      quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeMass reward profile)) :
    quittingTerminalPayoff reward profile who =
      reward (quittingSingletonTerminal who) who := by
  let mass := quittingTerminalOutcomeMass reward profile
  have hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) :=
    quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hnone : mass none = 0 := by
    exact quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer
      reward profile finitePlayer stop hfinite
  have hzero : ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal ≠ quittingSingletonTerminal who → mass (some terminal) = 0 := by
    intro terminal hterminal
    have hsetNe : terminal.val ≠ {who} := by
      intro heq
      apply hterminal
      apply Subtype.ext
      exact heq
    obtain ⟨other, hotherMem, hotherNe⟩ :
        ∃ other ∈ terminal.val, other ≠ who := by
      by_contra hnot
      push Not at hnot
      have hall : ∀ player ∈ terminal.val, player = who := by
        exact fun player hplayer => hnot player hplayer
      obtain ⟨member, hmember⟩ := terminal.property
      have hmemberEq : member = who := hall member hmember
      have hwhoMem : who ∈ terminal.val := hmemberEq ▸ hmember
      exact hsetNe (Finset.eq_singleton_iff_unique_mem.mpr ⟨hwhoMem, hall⟩)
    have hterminalFilter : terminal ∈ Finset.univ.filter
        (fun candidate : {S : Finset ι // S.Nonempty} =>
          other ∈ candidate.val ∧ other ≠ who) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ terminal, hotherMem, hotherNe⟩
    have hle : mass (some terminal) ≤
        quittingTerminalOpponentIncidenceMass who other mass := by
      unfold quittingTerminalOpponentIncidenceMass
      exact Finset.single_le_sum
        (fun candidate _ => hmass.1 (some candidate)) hterminalFilter
    have hincidenceLe :
        quittingTerminalOpponentIncidenceMass who other mass ≤ 0 :=
      le_of_not_gt (hincidence other hotherNe)
    exact le_antisymm (hle.trans hincidenceLe) (hmass.1 (some terminal))
  have hfiniteSum : ∑ terminal : {S : Finset ι // S.Nonempty},
      mass (some terminal) = 1 := by
    have htotal := hmass.2
    rw [Fintype.sum_option, hnone, zero_add] at htotal
    exact htotal
  have hsingleton : mass (some (quittingSingletonTerminal who)) = 1 := by
    rw [Finset.sum_eq_single (quittingSingletonTerminal who)] at hfiniteSum
    · exact hfiniteSum
    · intro terminal _ hne
      exact hzero terminal hne
    · simp
  unfold quittingTerminalPayoff
  change (∑ terminal : {S : Finset ι // S.Nonempty},
    mass (some terminal) * reward terminal who) = _
  rw [Finset.sum_eq_single (quittingSingletonTerminal who)]
  · rw [hsingleton, one_mul]
  · intro terminal _ hne
    rw [hzero terminal hne, zero_mul]
  · simp

/-- If every opponent Continues purely at time zero, updating `who` to Quit
there pays the literal singleton reward. -/
theorem quittingTerminalPayoff_update_pureTime_zero_eq_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hopponents : ∀ other, other ≠ who →
      quittingProfileRoot reward profile other = PMF.pure false) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      reward (quittingSingletonTerminal who) who := by
  let target := Function.update profile who
    (quittingPureTimeBehaviorStrategy reward who (some 0))
  have hroot : quittingProfileRoot reward target =
      quittingPureSetRoot ({who} : Finset ι) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [target, quittingProfileRoot, quittingPureTimeBehaviorStrategy,
        quittingPureSetRoot, quittingSetAction]
    · rw [show quittingProfileRoot reward target player =
          quittingProfileRoot reward profile player by
        simp [target, quittingProfileRoot, Function.update_of_ne hplayer]]
      rw [hopponents player hplayer]
      simp [quittingPureSetRoot, quittingSetAction, hplayer]
  change quittingTerminalPayoff reward target who = _
  rw [← quittingTerminalPayoff_firstStageAdapter reward target who]
  unfold quittingFirstStageAdapter
  rw [hroot,
    quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
      ({who} : Finset ι) (Finset.singleton_nonempty who)]
  simp [quittingSetReward, quittingSingletonTerminal]

/-- A product root in which a genuine opponent Quits surely has one full unit
of fresh incidence in that opponent. -/
theorem quittingRootOpponentIncidenceMass_eq_one_of_pureQuit
    (root : ι → PMF Bool) (owner other : ι) (hne : other ≠ owner)
    (hother : root other = PMF.pure true) :
    quittingRootOpponentIncidenceMass owner other root = 1 := by
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hother
  have hzero : ∀ terminal : {S : Finset ι // S.Nonempty},
      other ∉ terminal.val → quittingRootCoalitionMass root terminal.val = 0 := by
    intro terminal hnot
    have hupper := quittingRootCoalitionMass_le_continueProbability_of_not_mem
      root terminal.val other hnot
    rw [hother] at hupper
    norm_num at hupper
    exact le_antisymm hupper
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        root terminal.val)
  have hfilter :
      (∑ terminal ∈ (Finset.univ.filter fun terminal :
          {S : Finset ι // S.Nonempty} => other ∈ terminal.val),
        quittingRootCoalitionMass root terminal.val) =
        ∑ terminal : {S : Finset ι // S.Nonempty},
          quittingRootCoalitionMass root terminal.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro terminal _
    by_cases hmem : other ∈ terminal.val
    · simp [hmem]
    · simp [hmem, hzero terminal hmem]
  unfold quittingRootOpponentIncidenceMass
  have hevent : (Finset.univ.filter fun terminal :
      {S : Finset ι // S.Nonempty} =>
        other ∈ terminal.val ∧ other ≠ owner) =
      Finset.univ.filter fun terminal : {S : Finset ι // S.Nonempty} =>
        other ∈ terminal.val := by
    ext terminal
    simp [hne]
  rw [hevent, hfilter]
  rw [← Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))
    (fun coalition => by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Finset.nonempty_iff_ne_empty.symm)
    (quittingRootCoalitionMass root)]
  rw [quittingRootCoalitionMass_sum_nonempty, hcontinue]
  norm_num

/-- A literal time-zero stopper belongs to every terminal coalition, so every
distinct owner sees unit incidence in that stopper. -/
theorem quittingTerminalOpponentIncidenceMass_eq_one_of_pureTime_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner stopper : ι) (hne : stopper ≠ owner)
    (hstopper : profile stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some 0)) :
    quittingTerminalOpponentIncidenceMass owner stopper
        (quittingTerminalOutcomeMass reward profile) = 1 := by
  let root := quittingProfileRoot reward profile
  let continuation := quittingProfileAllContinueContinuation reward profile
  have hrootQuit : root stopper = PMF.pure true := by
    dsimp only [root, quittingProfileRoot]
    rw [hstopper]
    simp [quittingPureTimeBehaviorStrategy]
  have hrootIncidence : quittingRootOpponentIncidenceMass owner stopper root = 1 :=
    quittingRootOpponentIncidenceMass_eq_one_of_pureQuit
      root owner stopper hne hrootQuit
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hrootQuit
  have hlaw := quittingTerminalOutcomeLawPrefix_outcomeMass
    reward root continuation
  have hadapter := quittingTerminalOutcomeMass_firstStageAdapter reward profile
  rw [← hadapter]
  change quittingTerminalOpponentIncidenceMass owner stopper
      (quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root continuation)) = 1
  rw [← hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix,
    hrootIncidence, hcontinue, zero_mul, add_zero]

/-- If a probability law has neither `Never` mass nor mass on the owner's
singleton, its total displayed opponent incidence is at least one.  A
coalition with several opponents is counted several times, so the inequality
is the exact robust statement needed by deadline recursion. -/
theorem one_le_totalOpponentIncidence_of_none_zero_singleton_zero
    (mass : QuittingTerminalOutcome ι → ℝ) (owner : ι)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι))
    (hnone : mass none = 0)
    (hsingleton : mass (some (quittingSingletonTerminal owner)) = 0) :
    1 ≤ quittingTerminalTotalOpponentIncidenceMass owner mass := by
  have htotalMass :
      ∑ terminal : {S : Finset ι // S.Nonempty}, mass (some terminal) = 1 := by
    have hsum := hmass.2
    rw [Fintype.sum_option, hnone, zero_add] at hsum
    exact hsum
  have hrewrite : quittingTerminalTotalOpponentIncidenceMass owner mass =
      ∑ terminal : {S : Finset ι // S.Nonempty},
        ∑ other ∈ Finset.univ.erase owner,
          if other ∈ terminal.val then mass (some terminal) else 0 := by
    unfold quittingTerminalTotalOpponentIncidenceMass
      quittingTerminalOpponentIncidenceMass
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro terminal _
    apply Finset.sum_congr rfl
    intro other hother
    have hne : other ≠ owner := (Finset.mem_erase.mp hother).1
    by_cases hmem : other ∈ terminal.val <;> simp [hmem, hne]
  rw [hrewrite, ← htotalMass]
  apply Finset.sum_le_sum
  intro terminal _
  by_cases hterminal : terminal = quittingSingletonTerminal owner
  · subst terminal
    rw [hsingleton]
    exact Finset.sum_nonneg fun other _ => by split <;> positivity
  · obtain ⟨other, hotherMem, hotherNe⟩ :
        ∃ other ∈ terminal.val, other ≠ owner := by
      by_contra hnot
      push Not at hnot
      have hall : ∀ player ∈ terminal.val, player = owner :=
        fun player hplayer => hnot player hplayer
      obtain ⟨member, hmember⟩ := terminal.property
      have hmemberEq : member = owner := hall member hmember
      have hownerMem : owner ∈ terminal.val := hmemberEq ▸ hmember
      apply hterminal
      apply Subtype.ext
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hownerMem, hall⟩
    have hotherErase : other ∈ Finset.univ.erase owner :=
      Finset.mem_erase.mpr ⟨hotherNe, Finset.mem_univ other⟩
    have hnonneg : ∀ candidate ∈ Finset.univ.erase owner,
        0 ≤ if candidate ∈ terminal.val then mass (some terminal) else 0 := by
      intro candidate _
      split
      · exact hmass.1 (some terminal)
      · exact le_rfl
    have hsingle := Finset.single_le_sum hnonneg hotherErase
    simpa only [hotherMem, ↓reduceIte] using hsingle

/-! ## Profitable paths and the exact finite-stopper finish -/

/-- A finite path of literal unilateral pure-time updates, each paying at
least `minimumGain` to its mover. -/
inductive QuittingProfitablePureTimePath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumGain : ℝ) :
    (quittingGame reward).BehaviorProfile → ℕ →
      (quittingGame reward).BehaviorProfile → Prop
  | nil (profile : (quittingGame reward).BehaviorProfile) :
      QuittingProfitablePureTimePath reward minimumGain profile 0 profile
  | cons {source middle finalProfile :
        (quittingGame reward).BehaviorProfile} {length : ℕ}
      (player : ι) (quitTime : Option ℕ)
      (middle_eq : middle = Function.update source player
        (quittingPureTimeBehaviorStrategy reward player quitTime))
      (gain : minimumGain ≤
        quittingTerminalPayoff reward middle player -
          quittingTerminalPayoff reward source player)
      (tail : QuittingProfitablePureTimePath reward minimumGain
        middle length finalProfile) :
      QuittingProfitablePureTimePath reward minimumGain
        source (length + 1) finalProfile

namespace QuittingProfitablePureTimePath

/-- Concatenation of literal profitable paths. -/
theorem append
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {minimumGain : ℝ} {first middle finalProfile}
    {firstLength secondLength : ℕ}
    (firstPath : QuittingProfitablePureTimePath reward minimumGain
      first firstLength middle)
    (suffix : QuittingProfitablePureTimePath reward minimumGain
      middle secondLength finalProfile) :
    QuittingProfitablePureTimePath reward minimumGain
      first (firstLength + secondLength) finalProfile := by
  induction firstPath with
  | nil => simpa using suffix
  | @cons source next middle length player quitTime hnext hgain tail ih =>
      have path := QuittingProfitablePureTimePath.cons
        player quitTime hnext hgain (ih suffix)
      convert path using 1
      omega

/-- Lowering the advertised gain threshold preserves a profitable path. -/
theorem mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {smaller larger : ℝ} {source finalProfile} {length : ℕ}
    (path : QuittingProfitablePureTimePath reward larger
      source length finalProfile)
    (hthreshold : smaller ≤ larger) :
    QuittingProfitablePureTimePath reward smaller
      source length finalProfile := by
  induction path with
  | nil => exact .nil _
  | cons player quitTime htarget hgain tail ih =>
      exact .cons player quitTime htarget (hthreshold.trans hgain) ih

end QuittingProfitablePureTimePath

/-- One approximate pure-time reset indexed by the player it actually
updates.  This is the role-preserving sibling of the older existential step,
whose player is stored only as an output field. -/
structure QuittingPureTimePlayerResetStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℝ) (source : (quittingGame reward).BehaviorProfile)
    (player : ι) where
  quitTime : Option ℕ
  target : (quittingGame reward).BehaviorProfile
  target_eq : target = Function.update source player
    (quittingPureTimeBehaviorStrategy reward player quitTime)
  target_debt_le_error : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward target) player ≤ error
  payoff_gain_eq_debt_sub :
    quittingTerminalPayoff reward target player -
        quittingTerminalPayoff reward source player =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) player -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) player

/-- Pure-time extremality supplies a role-preserving approximate reset for
any named player. -/
theorem exists_quittingPureTimePlayerResetStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℝ) (herror : 0 < error)
    (source : (quittingGame reward).BehaviorProfile) (player : ι) :
    Nonempty (QuittingPureTimePlayerResetStep reward error source player) := by
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward source player
      (half_pos herror)
  obtain ⟨quitTime, hpure⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward source player deviation (half_pos herror)
  let target := Function.update source player
    (quittingPureTimeBehaviorStrategy reward player quitTime)
  have hpayoff : quittingContinuationBestResponseValue reward source player -
      error ≤ quittingTerminalPayoff reward target player := by
    dsimp only [target]
    linarith
  have hdebtLe : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward target) player ≤ error := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    change quittingContinuationBestResponseValue reward target player -
      quittingTerminalPayoff reward target player ≤ error
    dsimp only [target]
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  have hgain : quittingTerminalPayoff reward target player -
        quittingTerminalPayoff reward source player =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) player -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) player := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    dsimp only [target]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  exact ⟨{
    quitTime := quitTime
    target := target
    target_eq := rfl
    target_debt_le_error := hdebtLe
    payoff_gain_eq_debt_sub := hgain
  }⟩

/-- An own-strategy update which attains the old unrestricted envelope has
exactly zero terminal semantic debt at the updated profile. -/
theorem quittingTerminalSemanticDebt_update_eq_zero_of_payoff_eq_bestReply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who)
    (hbest : quittingTerminalPayoff reward
        (Function.update profile who strategy) who =
      quittingContinuationBestResponseValue reward profile who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile who strategy)) who = 0 := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (Function.update profile who strategy) who -
        quittingTerminalPayoff reward
          (Function.update profile who strategy) who = 0
  rw [quittingContinuationBestResponseValue_update_self, hbest]
  ring

/-- One literal pure-time update which attains the named player's unrestricted
behavioral cap.  The source-debt floor is retained so the exact gain is at
least `gap`. -/
structure QuittingExactPureTimeCapStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (source : (quittingGame reward).BehaviorProfile)
    (player : ι) where
  quitTime : Option ℕ
  target : (quittingGame reward).BehaviorProfile
  target_eq : target = Function.update source player
    (quittingPureTimeBehaviorStrategy reward player quitTime)
  source_debt_floor : gap ≤ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward source) player
  cap_attained : quittingTerminalPayoff reward target player =
    quittingContinuationBestResponseValue reward source player

namespace QuittingExactPureTimeCapStep

/-- Exact cap attainment resets the updated player's debt literally to zero. -/
theorem target_reset
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap : ℝ} {source : (quittingGame reward).BehaviorProfile}
    {player : ι} (step : QuittingExactPureTimeCapStep reward gap source player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward step.target) player = 0 := by
  rw [step.target_eq]
  exact quittingTerminalSemanticDebt_update_eq_zero_of_payoff_eq_bestReply
    reward source player
      (quittingPureTimeBehaviorStrategy reward player step.quitTime)
      (by simpa only [step.target_eq] using step.cap_attained)

/-- The payoff gain of an exact cap step is exactly its source debt. -/
theorem payoff_gain_eq_source_debt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap : ℝ} {source : (quittingGame reward).BehaviorProfile}
    {player : ι} (step : QuittingExactPureTimeCapStep reward gap source player) :
    quittingTerminalPayoff reward step.target player -
        quittingTerminalPayoff reward source player =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source) player := by
  have htransport := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward source player
      (quittingPureTimeBehaviorStrategy reward player step.quitTime)
  rw [← step.target_eq, step.target_reset] at htransport
  linarith

/-- Every retained exact cap edge gains at least the unweakened threshold. -/
theorem gap_le_payoff_gain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap : ℝ} {source : (quittingGame reward).BehaviorProfile}
    {player : ι} (step : QuittingExactPureTimeCapStep reward gap source player) :
    gap ≤ quittingTerminalPayoff reward step.target player -
      quittingTerminalPayoff reward source player := by
  rw [step.payoff_gain_eq_source_debt]
  exact step.source_debt_floor

end QuittingExactPureTimeCapStep

/-- A path whose every literal pure-time edge attains the updated player's
full behavioral cap and starts from debt at least `gap`. -/
inductive QuittingExactPureTimeCapPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) :
    (quittingGame reward).BehaviorProfile → ℕ →
      (quittingGame reward).BehaviorProfile → Type
  | nil (profile : (quittingGame reward).BehaviorProfile) :
      QuittingExactPureTimeCapPath reward gap profile 0 profile
  | cons {source middle finalProfile :
        (quittingGame reward).BehaviorProfile} {length : ℕ} {player : ι}
      (step : QuittingExactPureTimeCapStep reward gap source player)
      (middle_eq : middle = step.target)
      (tail : QuittingExactPureTimeCapPath reward gap middle length finalProfile) :
      QuittingExactPureTimeCapPath reward gap source (length + 1) finalProfile

namespace QuittingExactPureTimeCapPath

/-- Forgetting exact cap attainment gives the profitable path at the same,
unweakened threshold. -/
theorem toProfitablePath
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    {source finalProfile : (quittingGame reward).BehaviorProfile}
    {length : ℕ}
    (path : QuittingExactPureTimeCapPath reward gap source length finalProfile) :
    QuittingProfitablePureTimePath reward gap source length finalProfile := by
  induction path with
  | nil profile => exact .nil profile
  | @cons source middle finalProfile length player step hmiddle tail ih =>
      subst middle
      exact .cons player step.quitTime step.target_eq
        step.gap_le_payoff_gain ih

end QuittingExactPureTimeCapPath

/-- The exact finite-stopper finish, before any global threshold weakening.
It contains one or two literal pure-time cap-attaining edges. -/
structure QuittingFiniteStopperExactFinish
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (source : (quittingGame reward).BehaviorProfile) where
  length : ℕ
  length_pos : 0 < length
  length_le_two : length ≤ 2
  finalProfile : (quittingGame reward).BehaviorProfile
  owner : ι
  other : ι
  owner_ne_other : owner ≠ other
  exactPath : QuittingExactPureTimeCapPath reward gap source length finalProfile
  owner_reset : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward finalProfile) owner = 0
  incidence_pos : 0 < quittingTerminalOpponentIncidenceMass owner other
    (quittingTerminalOutcomeMass reward finalProfile)

/-- Once a low-debt finite stopper exists, at most two exact pure-time best
responses reach a zero-debt owner with positive opponent incidence.  This API
retains literal per-edge cap attainment and the full `gap` threshold. -/
theorem nonempty_finiteStopperExactFinish
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (hgap : 0 < gap)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (source : (quittingGame reward).BehaviorProfile)
    (stopper : ι) (deadline : ℕ)
    (hstopper : source stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline))
    (hstopperDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source) stopper < gap) :
    Nonempty (QuittingFiniteStopperExactFinish reward gap source) := by
  obtain ⟨who, hwhoDebt⟩ := hfloor source
  have hwhoNe : who ≠ stopper := by
    intro heq
    subst who
    linarith
  obtain ⟨choice, _hchoiceBound, hchoiceBest⟩ :=
    exists_pureTime_bestReply_of_opponent_quitsAt reward source
      who stopper deadline hwhoNe.symm hstopper
  let diagnostic := Function.update source who
    (quittingPureTimeBehaviorStrategy reward who choice)
  have hdiagnosticBest : quittingTerminalPayoff reward diagnostic who =
      quittingContinuationBestResponseValue reward source who := by
    exact hchoiceBest
  have hdiagnosticDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward diagnostic) who = 0 := by
    exact quittingTerminalSemanticDebt_update_eq_zero_of_payoff_eq_bestReply
      reward source who
        (quittingPureTimeBehaviorStrategy reward who choice)
        hdiagnosticBest
  have hdiagnosticGain : gap ≤
      quittingTerminalPayoff reward diagnostic who -
        quittingTerminalPayoff reward source who := by
    have htransport := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
      reward source who
        (quittingPureTimeBehaviorStrategy reward who choice)
    change quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward diagnostic) who = _ at htransport
    rw [hdiagnosticDebt] at htransport
    linarith
  let diagnosticStep : QuittingExactPureTimeCapStep reward gap source who := {
    quitTime := choice
    target := diagnostic
    target_eq := rfl
    source_debt_floor := hwhoDebt
    cap_attained := hdiagnosticBest
  }
  by_cases hpositive : ∃ other, other ≠ who ∧
      0 < quittingTerminalOpponentIncidenceMass who other
        (quittingTerminalOutcomeMass reward diagnostic)
  · obtain ⟨other, hother, hincidence⟩ := hpositive
    exact ⟨{
      length := 1
      length_pos := by omega
      length_le_two := by omega
      finalProfile := diagnostic
      owner := who
      other := other
      owner_ne_other := hother.symm
      exactPath := .cons diagnosticStep rfl (.nil diagnostic)
      owner_reset := hdiagnosticDebt
      incidence_pos := hincidence
    }⟩
  · have hnoIncidence : ∀ other, other ≠ who → ¬ 0 <
        quittingTerminalOpponentIncidenceMass who other
          (quittingTerminalOutcomeMass reward diagnostic) := by
      intro other hother hincidence
      exact hpositive ⟨other, hother, hincidence⟩
    have hdiagnosticStopper : diagnostic stopper =
        quittingPureTimeBehaviorStrategy reward stopper (some deadline) := by
      dsimp only [diagnostic]
      rw [Function.update_of_ne hwhoNe.symm, hstopper]
    have hdiagnosticPayoff : quittingTerminalPayoff reward diagnostic who =
        reward (quittingSingletonTerminal who) who :=
      quittingTerminalPayoff_eq_singleton_of_finitePureTimePlayer_of_no_incidence
        reward diagnostic who stopper deadline hdiagnosticStopper hnoIncidence
    have hsourceOpponents : ∀ other, other ≠ who →
        quittingProfileRoot reward source other = PMF.pure false := by
      intro other hother
      have hroot :=
        quittingProfileRoot_eq_pureContinue_of_no_positive_terminalIncidence
          reward diagnostic who hnoIncidence other hother
      have hsame : quittingProfileRoot reward diagnostic other =
          quittingProfileRoot reward source other := by
        dsimp only [diagnostic, quittingProfileRoot]
        rw [Function.update_of_ne hother]
      rw [hsame] at hroot
      exact hroot
    let zeroProfile := Function.update source who
      (quittingPureTimeBehaviorStrategy reward who (some 0))
    have hzeroPayoff : quittingTerminalPayoff reward zeroProfile who =
        reward (quittingSingletonTerminal who) who :=
      quittingTerminalPayoff_update_pureTime_zero_eq_singleton
        reward source who hsourceOpponents
    have hzeroBest : quittingTerminalPayoff reward zeroProfile who =
        quittingContinuationBestResponseValue reward source who := by
      rw [hzeroPayoff, ← hdiagnosticPayoff]
      exact hdiagnosticBest
    have hzeroDebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward zeroProfile) who = 0 := by
      exact quittingTerminalSemanticDebt_update_eq_zero_of_payoff_eq_bestReply
        reward source who
          (quittingPureTimeBehaviorStrategy reward who (some 0)) hzeroBest
    have hzeroGain : gap ≤ quittingTerminalPayoff reward zeroProfile who -
        quittingTerminalPayoff reward source who := by
      rw [hzeroPayoff, ← hdiagnosticPayoff]
      exact hdiagnosticGain
    let zeroStep : QuittingExactPureTimeCapStep reward gap source who := {
      quitTime := some 0
      target := zeroProfile
      target_eq := rfl
      source_debt_floor := hwhoDebt
      cap_attained := hzeroBest
    }
    obtain ⟨nextOwner, hnextDebt⟩ := hfloor zeroProfile
    have hnextNe : nextOwner ≠ who := by
      intro heq
      subst nextOwner
      linarith
    have hzeroStopper : zeroProfile who =
        quittingPureTimeBehaviorStrategy reward who (some 0) := by
      simp [zeroProfile]
    obtain ⟨nextChoice, _hnextChoiceBound, hnextBest⟩ :=
      exists_pureTime_bestReply_of_opponent_quitsAt reward zeroProfile
        nextOwner who 0 hnextNe.symm hzeroStopper
    let finalProfile := Function.update zeroProfile nextOwner
      (quittingPureTimeBehaviorStrategy reward nextOwner nextChoice)
    have hfinalDebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward finalProfile) nextOwner = 0 := by
      exact quittingTerminalSemanticDebt_update_eq_zero_of_payoff_eq_bestReply
        reward zeroProfile nextOwner
          (quittingPureTimeBehaviorStrategy reward nextOwner nextChoice)
          hnextBest
    have hfinalGain : gap ≤
        quittingTerminalPayoff reward finalProfile nextOwner -
          quittingTerminalPayoff reward zeroProfile nextOwner := by
      have htransport := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
        reward zeroProfile nextOwner
          (quittingPureTimeBehaviorStrategy reward nextOwner nextChoice)
      change quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward finalProfile) nextOwner = _
        at htransport
      rw [hfinalDebt] at htransport
      linarith
    let finalStep : QuittingExactPureTimeCapStep reward gap zeroProfile
        nextOwner := {
      quitTime := nextChoice
      target := finalProfile
      target_eq := rfl
      source_debt_floor := hnextDebt
      cap_attained := hnextBest
    }
    have hfinalStopper : finalProfile who =
        quittingPureTimeBehaviorStrategy reward who (some 0) := by
      dsimp only [finalProfile]
      rw [Function.update_of_ne hnextNe.symm, hzeroStopper]
    have hfinalIncidence : quittingTerminalOpponentIncidenceMass
        nextOwner who (quittingTerminalOutcomeMass reward finalProfile) = 1 :=
      quittingTerminalOpponentIncidenceMass_eq_one_of_pureTime_zero
        reward finalProfile nextOwner who hnextNe.symm hfinalStopper
    exact ⟨{
      length := 2
      length_pos := by omega
      length_le_two := by omega
      finalProfile := finalProfile
      owner := nextOwner
      other := who
      owner_ne_other := hnextNe
      exactPath := .cons zeroStep rfl
        (.cons finalStep rfl (.nil finalProfile))
      owner_reset := hfinalDebt
      incidence_pos := by rw [hfinalIncidence]; norm_num
    }⟩

/-- Backward-compatible existential view of the exact finish.  The threshold
is weakened to `3 * gap / 4` only at this global composition boundary. -/
theorem exists_exactZeroDebt_positiveIncidence_of_finiteStopper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (hgap : 0 < gap)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (source : (quittingGame reward).BehaviorProfile)
    (stopper : ι) (deadline : ℕ)
    (hstopper : source stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline))
    (hstopperDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source) stopper < gap) :
    ∃ (length : ℕ) (finalProfile : (quittingGame reward).BehaviorProfile)
        (owner other : ι),
      QuittingProfitablePureTimePath reward (3 * gap / 4)
          source length finalProfile ∧
        length ≤ 2 ∧ owner ≠ other ∧
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward finalProfile) owner = 0 ∧
        0 < quittingTerminalOpponentIncidenceMass owner other
          (quittingTerminalOutcomeMass reward finalProfile) := by
  obtain ⟨finish⟩ := nonempty_finiteStopperExactFinish reward gap hgap hfloor
    source stopper deadline hstopper hstopperDebt
  refine ⟨finish.length, finish.finalProfile, finish.owner, finish.other,
    finish.exactPath.toProfitablePath.mono ?_, finish.length_le_two,
    finish.owner_ne_other, finish.owner_reset, finish.incidence_pos⟩
  linarith

/-! ## Deadline-recursive quantitative incidence selection -/

/-- If a named opponent and the updated player both stop at the same literal
deadline, the updated player's singleton has zero terminal mass: the opponent
Quits surely at that date and is absent from the singleton coalition. -/
theorem quittingTerminalOutcomeMass_singleton_eq_zero_of_sameDeadlineOpponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner stopper : ι) (deadline : ℕ) (hne : stopper ≠ owner)
    (hstopper : profile stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline)) :
    quittingTerminalOutcomeMass reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner (some deadline)))
        (some (quittingSingletonTerminal owner)) = 0 := by
  let target := Function.update profile owner
    (quittingPureTimeBehaviorStrategy reward owner (some deadline))
  rw [quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at reward
    profile owner deadline (quittingSingletonTerminal owner)
      (Finset.mem_singleton_self owner)]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  apply mul_eq_zero_of_right
  have hstopperRoot : quittingProfileLiveRoot reward target deadline stopper =
      PMF.pure true := by
    dsimp only [target, quittingProfileLiveRoot]
    rw [Function.update_of_ne hne, hstopper]
    simp [quittingPureTimeBehaviorStrategy]
  have hnotMem : stopper ∉ (quittingSingletonTerminal owner).val := by
    exact fun hmem => hne (Finset.mem_singleton.mp hmem)
  have hupper := quittingRootCoalitionMass_le_continueProbability_of_not_mem
    (quittingProfileLiveRoot reward target deadline)
      (quittingSingletonTerminal owner).val stopper hnotMem
  rw [hstopperRoot] at hupper
  norm_num at hupper
  exact le_antisymm hupper
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (quittingProfileLiveRoot reward target deadline)
      (quittingSingletonTerminal owner).val)

/-- The separate finite-deadline selector.  It follows a strictly decreasing
deadline whenever the exact response stops earlier, so after at most
`deadline + 1` cap-attaining updates it reaches a reset owner whose terminal
law carries total opponent incidence at least one.  This is independent of
the shorter cardinality-bounded reset arrival. -/
structure QuittingFiniteDeadlineIncidenceSelection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (source : (quittingGame reward).BehaviorProfile)
    (stopper : ι) (deadline : ℕ) where
  length : ℕ
  finalProfile : (quittingGame reward).BehaviorProfile
  owner : ι
  exactPath : QuittingExactPureTimeCapPath reward gap source length finalProfile
  length_le : length ≤ deadline + 1
  owner_reset : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward finalProfile) owner = 0
  total_incidence_ge_one : 1 ≤
    quittingTerminalTotalOpponentIncidenceMass owner
      (quittingTerminalOutcomeMass reward finalProfile)

/-- Deadline induction constructs the quantitative exact selector. -/
theorem nonempty_finiteDeadlineIncidenceSelection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (hgap : 0 < gap)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (source : (quittingGame reward).BehaviorProfile)
    (stopper : ι) (deadline : ℕ)
    (hstopper : source stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline))
    (hstopperDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source) stopper < gap) :
    Nonempty (QuittingFiniteDeadlineIncidenceSelection reward gap source
      stopper deadline) := by
  induction deadline using Nat.strong_induction_on generalizing source stopper with
  | h deadline ih =>
      obtain ⟨who, hwhoDebt⟩ := hfloor source
      have hwhoNe : who ≠ stopper := by
        intro heq
        subst who
        linarith
      obtain ⟨choice, hchoiceBound, hchoiceBest⟩ :=
        exists_pureTime_bestReply_of_opponent_quitsAt reward source
          who stopper deadline hwhoNe.symm hstopper
      let target := Function.update source who
        (quittingPureTimeBehaviorStrategy reward who choice)
      let step : QuittingExactPureTimeCapStep reward gap source who := {
        quitTime := choice
        target := target
        target_eq := rfl
        source_debt_floor := hwhoDebt
        cap_attained := hchoiceBest
      }
      have htargetReset : quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) who = 0 :=
        step.target_reset
      have htargetStopper : target stopper =
          quittingPureTimeBehaviorStrategy reward stopper (some deadline) := by
        dsimp only [target]
        rw [Function.update_of_ne hwhoNe.symm, hstopper]
      have hnone : quittingTerminalOutcomeMass reward target none = 0 :=
        quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer
          reward target stopper deadline htargetStopper
      rcases hchoiceBound with hnever | ⟨time, htimeLe, htime⟩
      · subst choice
        have hsingleton : quittingTerminalOutcomeMass reward target
            (some (quittingSingletonTerminal who)) = 0 := by
          dsimp only [target]
          exact quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
            reward source who (quittingSingletonTerminal who)
              (Finset.mem_singleton_self who)
        have htotal :=
          one_le_totalOpponentIncidence_of_none_zero_singleton_zero
            (quittingTerminalOutcomeMass reward target) who
            (quittingTerminalOutcomeMass_mem_stdSimplex reward target)
            hnone hsingleton
        exact ⟨{
          length := 1
          finalProfile := target
          owner := who
          exactPath := .cons step rfl (.nil target)
          length_le := by omega
          owner_reset := htargetReset
          total_incidence_ge_one := htotal
        }⟩
      · subst choice
        by_cases htimeLt : time < deadline
        · have htargetWho : target who =
              quittingPureTimeBehaviorStrategy reward who (some time) := by
            simp [target]
          obtain ⟨tail⟩ := ih time htimeLt target who htargetWho (by
            rw [htargetReset]
            exact hgap)
          exact ⟨{
            length := tail.length + 1
            finalProfile := tail.finalProfile
            owner := tail.owner
            exactPath := .cons step rfl tail.exactPath
            length_le := by
              have htailLength := tail.length_le
              omega
            owner_reset := tail.owner_reset
            total_incidence_ge_one := tail.total_incidence_ge_one
          }⟩
        · have htimeEq : time = deadline := by omega
          subst time
          have hsingleton : quittingTerminalOutcomeMass reward target
              (some (quittingSingletonTerminal who)) = 0 := by
            dsimp only [target]
            exact
              quittingTerminalOutcomeMass_singleton_eq_zero_of_sameDeadlineOpponent
                reward source who stopper deadline hwhoNe.symm hstopper
          have htotal :=
            one_le_totalOpponentIncidence_of_none_zero_singleton_zero
              (quittingTerminalOutcomeMass reward target) who
              (quittingTerminalOutcomeMass_mem_stdSimplex reward target)
              hnone hsingleton
          exact ⟨{
            length := 1
            finalProfile := target
            owner := who
            exactPath := .cons step rfl (.nil target)
            length_le := by omega
            owner_reset := htargetReset
            total_incidence_ge_one := htotal
          }⟩

namespace QuittingFiniteDeadlineIncidenceSelection

/-- With at least two players, total incidence at least one selects an actual
opponent coordinate carrying at least the reciprocal number of opponents. -/
theorem exists_other_card_sub_one_le_incidence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap : ℝ} {source : (quittingGame reward).BehaviorProfile}
    {stopper : ι} {deadline : ℕ}
    (selection : QuittingFiniteDeadlineIncidenceSelection reward gap source
      stopper deadline)
    (hcard : 2 ≤ Fintype.card ι) :
    ∃ other : ι, other ≠ selection.owner ∧
      1 / ((Fintype.card ι : ℝ) - 1) ≤
        quittingTerminalOpponentIncidenceMass selection.owner other
          (quittingTerminalOutcomeMass reward selection.finalProfile) := by
  let opponents : Finset ι := Finset.univ.erase selection.owner
  have hownerMem : selection.owner ∈ (Finset.univ : Finset ι) :=
    Finset.mem_univ selection.owner
  have hopponentsCard : opponents.card = Fintype.card ι - 1 := by
    dsimp only [opponents]
    rw [Finset.card_erase_of_mem hownerMem, Finset.card_univ]
  have hopponents : opponents.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hzero : opponents.card = 0 := by rw [hempty, Finset.card_empty]
    rw [hopponentsCard] at hzero
    omega
  have hdenPos : 0 < (Fintype.card ι : ℝ) - 1 := by
    have hcardReal : (1 : ℝ) < Fintype.card ι := by
      exact_mod_cast (show 1 < Fintype.card ι by omega)
    linarith
  have haverage :
      ∑ _other ∈ opponents, 1 / ((Fintype.card ι : ℝ) - 1) ≤
        ∑ other ∈ opponents,
          quittingTerminalOpponentIncidenceMass selection.owner other
            (quittingTerminalOutcomeMass reward selection.finalProfile) := by
    have hconstant :
        (∑ _other ∈ opponents, 1 / ((Fintype.card ι : ℝ) - 1)) = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, hopponentsCard]
      push_cast [show 1 ≤ Fintype.card ι by omega]
      field_simp
    rw [hconstant]
    simpa only [opponents, quittingTerminalTotalOpponentIncidenceMass] using
      selection.total_incidence_ge_one
  obtain ⟨other, hotherMem, hother⟩ :=
    Finset.exists_le_of_sum_le hopponents haverage
  exact ⟨other, (Finset.mem_erase.mp hotherMem).1, hother⟩

end QuittingFiniteDeadlineIncidenceSelection

/-- Capstone quantitative deadline selection, with the player-cardinality
hypothesis explicit and the selected opponent coordinate retained. -/
theorem exists_finiteDeadlineIncidenceSelection_with_selectedOpponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (hgap : 0 < gap)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (source : (quittingGame reward).BehaviorProfile)
    (stopper : ι) (deadline : ℕ)
    (hcard : 2 ≤ Fintype.card ι)
    (hstopper : source stopper =
      quittingPureTimeBehaviorStrategy reward stopper (some deadline))
    (hstopperDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source) stopper < gap) :
    ∃ selection : QuittingFiniteDeadlineIncidenceSelection reward gap source
        stopper deadline,
      ∃ other : ι, other ≠ selection.owner ∧
        1 / ((Fintype.card ι : ℝ) - 1) ≤
          quittingTerminalOpponentIncidenceMass selection.owner other
            (quittingTerminalOutcomeMass reward selection.finalProfile) := by
  obtain ⟨selection⟩ := nonempty_finiteDeadlineIncidenceSelection reward gap
    hgap hfloor source stopper deadline hstopper hstopperDebt
  exact ⟨selection, selection.exists_other_card_sub_one_le_incidence hcard⟩

/-! ## Remaining-set acquisition and the complete arrival -/

/-- A self-reset to literal `Never` strictly enlarges every finite certificate
of players already using literal `Never`.  The updated target preserves the
old certificate and adjoins the reset player as a genuinely new label. -/
theorem QuittingPureTimeSelfResetStep.literalNever_certificate_strictGrowth
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source : (quittingGame reward).BehaviorProfile}
    (step : QuittingPureTimeSelfResetStep reward gap error source)
    (herror : error < gap) (htime : step.quitTime = none)
    (certified : Finset ι)
    (hcertified : ∀ player ∈ certified,
      source player = quittingPureTimeBehaviorStrategy reward player none) :
    certified ⊂ insert step.player certified ∧
      ∀ player ∈ insert step.player certified,
        step.target player =
          quittingPureTimeBehaviorStrategy reward player none := by
  have hnotMem : step.player ∉ certified := by
    intro hmem
    exact step.player_not_literalNever_of_quitTime_eq_none herror htime
      (hcertified step.player hmem)
  have hstrict : certified ⊂ insert step.player certified := by
    exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_insert _ _, by
      intro heq
      have hmem : step.player ∈ certified := by
        rw [heq]
        exact Finset.mem_insert_self step.player certified
      exact hnotMem hmem⟩
  refine ⟨hstrict, ?_⟩
  intro player hplayer
  rw [Finset.mem_insert] at hplayer
  rcases hplayer with rfl | hplayer
  · rw [step.target_eq, htime, Function.update_self]
  · have hne : player ≠ step.player := by
      intro heq
      subst player
      exact hnotMem hplayer
    rw [step.target_eq, Function.update_of_ne hne]
    exact hcertified player hplayer

namespace QuittingPureTimeSelfResetChain

/-- Every checked approximate-reset chain is a profitable pure-time path at
any threshold below `gap - error`. -/
theorem toProfitablePath
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error minimumGain : ℝ} {source finalProfile}
    {length : ℕ} {finalPlayer : ι} {stop : ℕ}
    (chain : QuittingPureTimeSelfResetChain reward gap error source length
      finalProfile finalPlayer stop)
    (hgain : minimumGain ≤ gap - error) :
    QuittingProfitablePureTimePath reward minimumGain
      source length finalProfile := by
  induction chain with
  | final step stop htime =>
      exact .cons step.player step.quitTime step.target_eq
        (hgain.trans step.gap_sub_error_le_payoff_gain)
        (.nil step.target)
  | cons step htime tail ih =>
      exact .cons step.player step.quitTime step.target_eq
        (hgain.trans step.gap_sub_error_le_payoff_gain) ih

end QuittingPureTimeSelfResetChain

/-- Public remaining-set form of bounded finite-stopper acquisition.  Players
outside `remaining` are already certified to play literal `Never`, so only a
new label from `remaining` can be consumed by each further Never update. -/
theorem exists_bounded_quittingPureTimeSelfResetChain_of_literalNever_outside
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap error : ℝ) (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (herrorPos : 0 < error) (herrorLt : error < gap)
    (remaining : Finset ι)
    (start : (quittingGame reward).BehaviorProfile)
    (hnever : ∀ who, who ∉ remaining →
      start who = quittingPureTimeBehaviorStrategy reward who none) :
    ∃ (length : ℕ) (finalProfile : (quittingGame reward).BehaviorProfile)
        (finalPlayer : ι) (stop : ℕ),
      QuittingPureTimeSelfResetChain reward gap error start length
          finalProfile finalPlayer stop ∧
        length ≤ remaining.card + 1 := by
  let motive := fun candidates : Finset ι =>
    ∀ profile : (quittingGame reward).BehaviorProfile,
      (∀ who, who ∉ candidates →
        profile who = quittingPureTimeBehaviorStrategy reward who none) →
      ∃ (length : ℕ) (finalProfile : (quittingGame reward).BehaviorProfile)
          (finalPlayer : ι) (stop : ℕ),
        QuittingPureTimeSelfResetChain reward gap error profile length
            finalProfile finalPlayer stop ∧
          length ≤ candidates.card + 1
  have haux : ∀ candidates : Finset ι, motive candidates := by
    intro candidates
    induction hcard : candidates.card using Nat.strong_induction_on
        generalizing candidates with
    | h card ih =>
        intro profile hcertified
        obtain ⟨who, hwhoDebt⟩ := hfloor profile
        obtain ⟨step⟩ := exists_quittingPureTimeSelfResetStep
          reward gap error herrorPos profile who hwhoDebt
        cases htime : step.quitTime with
        | some stop =>
            exact ⟨1, step.target, step.player, stop,
              .final step stop htime, by omega⟩
        | none =>
            have hwhoMem : step.player ∈ candidates := by
              by_contra hwhoNot
              exact step.player_not_literalNever_of_quitTime_eq_none
                herrorLt htime (hcertified step.player hwhoNot)
            have heraseCard : (candidates.erase step.player).card < card := by
              rw [← hcard]
              exact Finset.card_erase_lt_of_mem hwhoMem
            have htargetCertified : ∀ other,
                other ∉ candidates.erase step.player →
                step.target other =
                  quittingPureTimeBehaviorStrategy reward other none := by
              intro other hother
              by_cases heq : other = step.player
              · subst other
                rw [step.target_eq, htime, Function.update_self]
              · rw [step.target_eq]
                simp only [Function.update, dif_neg heq]
                exact hcertified other fun hmem =>
                  hother (Finset.mem_erase.mpr ⟨heq, hmem⟩)
            obtain ⟨length, finalProfile, finalPlayer, stop,
                tail, hlength⟩ :=
              ih (candidates.erase step.player).card heraseCard
                (candidates.erase step.player) rfl step.target htargetCertified
            exact ⟨length + 1, finalProfile, finalPlayer, stop,
              .cons step htime tail, by
                rw [Finset.card_erase_of_mem hwhoMem] at hlength
                omega⟩
  exact haux remaining start hnever

/-- The remaining-set acquisition exposed directly as a profitable path. -/
theorem exists_profitable_finiteStopper_of_literalNever_outside
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (hgap : 0 < gap)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (remaining : Finset ι)
    (start : (quittingGame reward).BehaviorProfile)
    (hnever : ∀ who, who ∉ remaining →
      start who = quittingPureTimeBehaviorStrategy reward who none) :
    ∃ (length : ℕ) (finiteProfile : (quittingGame reward).BehaviorProfile)
        (stopper : ι) (deadline : ℕ),
      QuittingProfitablePureTimePath reward (3 * gap / 4)
          start length finiteProfile ∧
        length ≤ remaining.card + 1 ∧
        finiteProfile stopper =
          quittingPureTimeBehaviorStrategy reward stopper (some deadline) ∧
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward finiteProfile) stopper ≤ gap / 4 := by
  have herrorPos : 0 < gap / 4 := by linarith
  have herrorLt : gap / 4 < gap := by linarith
  obtain ⟨length, finiteProfile, stopper, deadline, chain, hlength⟩ :=
    exists_bounded_quittingPureTimeSelfResetChain_of_literalNever_outside
      reward gap (gap / 4) hfloor herrorPos herrorLt remaining start hnever
  refine ⟨length, finiteProfile, stopper, deadline,
    chain.toProfitablePath ?_, hlength, chain.final_player_strategy,
    chain.final_debt_le_error⟩
  ring_nf
  exact le_rfl

/-- **Finite reset arrival.**  From every actual profile, a path of at most
`card ι + 3` literal pure-time updates, each gaining at least `3 * gap / 4`,
reaches a zero-debt owner with positive incidence in a distinct opponent. -/
theorem nonempty_pureTimeResetArrival_of_uniformDebtFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (hgap : 0 < gap)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (start : (quittingGame reward).BehaviorProfile) :
    ∃ (length : ℕ) (finalProfile : (quittingGame reward).BehaviorProfile)
        (owner other : ι),
      QuittingProfitablePureTimePath reward (3 * gap / 4)
          start length finalProfile ∧
        length ≤ Fintype.card ι + 3 ∧ owner ≠ other ∧
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward finalProfile) owner = 0 ∧
        0 < quittingTerminalOpponentIncidenceMass owner other
          (quittingTerminalOutcomeMass reward finalProfile) := by
  obtain ⟨firstLength, finiteProfile, stopper, deadline, firstPath,
      hfirstLength, hstopper, hstopperDebt⟩ :=
    exists_profitable_finiteStopper_of_literalNever_outside
      reward gap hgap hfloor Finset.univ start (by simp)
  obtain ⟨secondLength, finalProfile, owner, other, secondPath,
      hsecondLength, howner, hreset, hincidence⟩ :=
    exists_exactZeroDebt_positiveIncidence_of_finiteStopper
      reward gap hgap hfloor finiteProfile stopper deadline hstopper (by
        linarith)
  refine ⟨firstLength + secondLength, finalProfile, owner, other,
    firstPath.append secondPath, ?_, howner, hreset, hincidence⟩
  simpa using Nat.add_le_add hfirstLength hsecondLength

/-- A reset arrival whose first mover is fixed in advance.  The first edge
has its own quantitative floor `eta / 2`; all later edges have the uniform
debt-floor scale `3 * gap / 4`. -/
structure QuittingFirstPlayerResetArrival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap eta : ℝ) (start : (quittingGame reward).BehaviorProfile)
    (firstPlayer : ι) where
  firstQuitTime : Option ℕ
  firstProfile : (quittingGame reward).BehaviorProfile
  firstProfile_eq : firstProfile = Function.update start firstPlayer
    (quittingPureTimeBehaviorStrategy reward firstPlayer firstQuitTime)
  first_gain : eta / 2 <
    quittingTerminalPayoff reward firstProfile firstPlayer -
      quittingTerminalPayoff reward start firstPlayer
  first_debt_lt_gap : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward firstProfile) firstPlayer < gap
  tailLength : ℕ
  length : ℕ
  length_eq : length = tailLength + 1
  finalProfile : (quittingGame reward).BehaviorProfile
  owner : ι
  other : ι
  owner_ne_other : owner ≠ other
  tailPath : QuittingProfitablePureTimePath reward
    (min (eta / 2) (3 * gap / 4)) firstProfile tailLength finalProfile
  length_le : length ≤ Fintype.card ι + 3
  owner_reset : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward finalProfile) owner = 0
  incidence_pos : 0 < quittingTerminalOpponentIncidenceMass owner other
    (quittingTerminalOutcomeMass reward finalProfile)

namespace QuittingFirstPlayerResetArrival

/-- The full stored path is assembled from the advertised first-player edge
and its retained suffix.  Consequently the recipient-first edge cannot be
unrelated to, or omitted from, the bounded path. -/
theorem path
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap eta : ℝ} {start : (quittingGame reward).BehaviorProfile}
    {firstPlayer : ι}
    (arrival : QuittingFirstPlayerResetArrival reward gap eta start
      firstPlayer) :
    QuittingProfitablePureTimePath reward
      (min (eta / 2) (3 * gap / 4)) start arrival.length
      arrival.finalProfile := by
  rw [arrival.length_eq]
  exact .cons firstPlayer arrival.firstQuitTime arrival.firstProfile_eq
    ((min_le_left _ _).trans arrival.first_gain.le) arrival.tailPath

end QuittingFirstPlayerResetArrival

/-- A named coordinate strictly above `3 * eta / 4` can be forced to move
first, after which remaining-set acquisition and the exact two-step finish
retain the global `card ι + 3` bound. -/
theorem nonempty_pureTimeResetArrival_with_firstPlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap eta : ℝ) (hgap : 0 < gap) (heta : 0 < eta)
    (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (start : (quittingGame reward).BehaviorProfile) (firstPlayer : ι)
    (hfirstDebt : 3 * eta / 4 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward start) firstPlayer) :
    Nonempty (QuittingFirstPlayerResetArrival reward gap eta start
      firstPlayer) := by
  let error := min (eta / 4) (gap / 4)
  have herrorPos : 0 < error := lt_min (by linarith) (by linarith)
  obtain ⟨firstStep⟩ := exists_quittingPureTimePlayerResetStep
    reward error herrorPos start firstPlayer
  have herrorEta : error ≤ eta / 4 := min_le_left _ _
  have herrorGap : error ≤ gap / 4 := min_le_right _ _
  have hfirstGain : eta / 2 <
      quittingTerminalPayoff reward firstStep.target firstPlayer -
        quittingTerminalPayoff reward start firstPlayer := by
    rw [firstStep.payoff_gain_eq_debt_sub]
    linarith [firstStep.target_debt_le_error]
  have hfirstDebtSmall : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward firstStep.target) firstPlayer < gap := by
    linarith [firstStep.target_debt_le_error]
  cases htime : firstStep.quitTime with
  | some deadline =>
      obtain ⟨tailLength, finalProfile, owner, other, tailPath,
          htailLength, howner, hreset, hincidence⟩ :=
        exists_exactZeroDebt_positiveIncidence_of_finiteStopper
          reward gap hgap hfloor firstStep.target firstPlayer deadline (by
            rw [firstStep.target_eq, htime, Function.update_self])
          hfirstDebtSmall
      have htail := tailPath.mono (min_le_right (eta / 2) (3 * gap / 4))
      refine ⟨{
        firstQuitTime := firstStep.quitTime
        firstProfile := firstStep.target
        firstProfile_eq := firstStep.target_eq
        first_gain := hfirstGain
        first_debt_lt_gap := hfirstDebtSmall
        tailLength := tailLength
        length := tailLength + 1
        length_eq := rfl
        finalProfile := finalProfile
        owner := owner
        other := other
        owner_ne_other := howner
        tailPath := htail
        length_le := by omega
        owner_reset := hreset
        incidence_pos := hincidence
      }⟩
  | none =>
      let remaining : Finset ι := Finset.univ.erase firstPlayer
      have hnever : ∀ player, player ∉ remaining →
          firstStep.target player =
            quittingPureTimeBehaviorStrategy reward player none := by
        intro player hplayer
        have heq : player = firstPlayer := by
          simpa [remaining] using hplayer
        subst player
        rw [firstStep.target_eq, htime, Function.update_self]
      obtain ⟨acquireLength, finiteProfile, stopper, deadline,
          acquirePath, hacquireLength, hstopper, hstopperDebt⟩ :=
        exists_profitable_finiteStopper_of_literalNever_outside
          reward gap hgap hfloor remaining firstStep.target hnever
      obtain ⟨finishLength, finalProfile, owner, other, finishPath,
          hfinishLength, howner, hreset, hincidence⟩ :=
        exists_exactZeroDebt_positiveIncidence_of_finiteStopper
          reward gap hgap hfloor finiteProfile stopper deadline hstopper (by
            linarith)
      have htail : QuittingProfitablePureTimePath reward (3 * gap / 4)
          firstStep.target (acquireLength + finishLength) finalProfile :=
        acquirePath.append finishPath
      have htailSmall := htail.mono (min_le_right (eta / 2) (3 * gap / 4))
      have hcardPos : 0 < Fintype.card ι :=
        Fintype.card_pos_iff.mpr ⟨firstPlayer⟩
      have hremainingCard : remaining.card = Fintype.card ι - 1 := by
        dsimp only [remaining]
        rw [Finset.card_erase_of_mem (Finset.mem_univ firstPlayer),
          Finset.card_univ]
      refine ⟨{
        firstQuitTime := firstStep.quitTime
        firstProfile := firstStep.target
        firstProfile_eq := firstStep.target_eq
        first_gain := hfirstGain
        first_debt_lt_gap := hfirstDebtSmall
        tailLength := acquireLength + finishLength
        length := acquireLength + finishLength + 1
        length_eq := rfl
        finalProfile := finalProfile
        owner := owner
        other := other
        owner_ne_other := howner
        tailPath := htailSmall
        length_le := by
          rw [hremainingCard] at hacquireLength
          omega
        owner_reset := hreset
        incidence_pos := hincidence
      }⟩

/-! ## Actual-profile fixed-law handoff -/

/-- A fixed-law reset dispatch reached from one literal starting profile by a
bounded profitable pure-time path.  The final semantic point and complete law
are definitionally those of `finalProfile`; no carrier representative is
substituted. -/
structure QuittingActualProfileFixedLawResetHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap : ℝ) (source : QuittingTerminalSemanticPair ι)
    (start : (quittingGame reward).BehaviorProfile) where
  length : ℕ
  finalProfile : (quittingGame reward).BehaviorProfile
  owner : ι
  other : ι
  owner_ne_other : owner ≠ other
  path : QuittingProfitablePureTimePath reward (3 * gap / 4)
    start length finalProfile
  length_le : length ≤ Fintype.card ι + 3
  final_joint :
    (quittingTerminalSemanticPair reward finalProfile,
        quittingTerminalOutcomeMass reward finalProfile) ∈
      quittingTerminalSemanticLawCarrier reward
  owner_reset : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward finalProfile) owner = 0
  incidence_pos : 0 < quittingTerminalOpponentIncidenceMass owner other
    (quittingTerminalOutcomeMass reward finalProfile)
  returned : QuittingTerminalSemanticPair ι
  dispatch : QuittingFixedLawResetDispatch (reward := reward) source
    (quittingTerminalSemanticPair reward finalProfile)
    (quittingTerminalOutcomeMass reward finalProfile) owner other returned

/-- A terminal exploitability witness turns the general arrival into a
same-source fixed-law reset dispatch while retaining its literal final
profile, law, and complete profitable path. -/
theorem nonempty_actualProfileFixedLawResetHandoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (witness : QuittingTerminalExploitabilityWitness reward)
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (start : (quittingGame reward).BehaviorProfile) :
    Nonempty (QuittingActualProfileFixedLawResetHandoff reward
      witness.terminalGap source start) := by
  obtain ⟨length, finalProfile, owner, other, path, hlength,
      howner, hreset, hincidence⟩ :=
    nonempty_pureTimeResetArrival_of_uniformDebtFloor reward
      witness.terminalGap witness.terminalGap_pos
        witness.hasUniformTerminalDebtFloor start
  have hjoint :
      (quittingTerminalSemanticPair reward finalProfile,
          quittingTerminalOutcomeMass reward finalProfile) ∈
        quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward finalProfile
  obtain ⟨returned, dispatch⟩ := witness.exists_fixedLawResetDispatch
    source (quittingTerminalSemanticPair reward finalProfile)
      (quittingTerminalOutcomeMass reward finalProfile) owner other
      hminimum hsourcePositive hjoint hreset hincidence
  exact ⟨{
    length := length
    finalProfile := finalProfile
    owner := owner
    other := other
    owner_ne_other := howner
    path := path
    length_le := hlength
    final_joint := hjoint
    owner_reset := hreset
    incidence_pos := hincidence
    returned := returned
    dispatch := dispatch
  }⟩

end GameTheory
