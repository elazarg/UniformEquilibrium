/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSplice
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau

/-!
# Sharpness of the two-seed finite-cap threshold

Two zero-Never seeds suffice for reward-uniform all-player finite capping.  The
results below show that one seed is genuinely insufficient for preserving the
full behavioral semantic port, not merely insufficient for the splice estimate.

Give every absorbing coalition payoff `-1`.  In a profile where one designated
player quits surely and every opponent Continues forever, that player can
deviate to Never and obtain `0`; its best-response envelope is therefore `0`.
In any profile which finitely caps every coordinate, some opponent quits surely
at a finite date under every deviation by the designated player.  Absorption is
then certain, every deviation pays `-1`, and its envelope is `-1`.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- Every absorbing terminal pays every player `-1`; Never still pays `0` by
the quitting game's terminal convention. -/
def quittingNegativeTerminalReward :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun _ _ => -1

/-- The one-seed profile: `seed` quits immediately, while every other player
Continues forever. -/
def quittingSingleSeedProfile (seed : ι) :
    (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile :=
  Function.update
    (quittingAlwaysContinueProfile
      (quittingNegativeTerminalReward (ι := ι))) seed
    (quittingPureTimeBehaviorStrategy
      (quittingNegativeTerminalReward (ι := ι)) seed (some 0))

omit [DecidableEq ι] [Nontrivial ι] in
/-- A sure quitter on the live path makes terminal live mass zero. -/
theorem quittingLiveMassLimit_eq_zero_of_live_sureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (sentinel : ι) (sureTime : ℕ)
    (hsure : profile sentinel sureTime
      (quittingLiveHist reward sureTime) = PMF.pure true) :
    quittingLiveMassLimit reward profile = 0 := by
  have hcontinue : quittingJointContinueMass reward profile sureTime = 0 := by
    rw [quittingJointContinueMass_eq_product]
    apply Finset.prod_eq_zero (Finset.mem_univ sentinel)
    rw [hsure]
    change ((PMF.pure true : PMF Bool) false).toReal = 0
    simp
  have hlive : quittingLiveMass reward profile (sureTime + 1) = 0 := by
    rw [quittingLiveMass_succ, hcontinue, mul_zero]
  exact le_antisymm
    ((quittingLiveMassLimit_le reward profile (sureTime + 1)).trans_eq hlive)
    (quittingLiveMassLimit_nonneg reward profile)

omit [DecidableEq ι] [Nontrivial ι] in
/-- Under the constant negative terminal table, certain absorption means
terminal payoff exactly `-1`. -/
theorem quittingTerminalPayoff_negative_eq_neg_one_of_liveMassLimit_zero
    (profile :
      (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile)
    (who : ι)
    (hlive : quittingLiveMassLimit
      (quittingNegativeTerminalReward (ι := ι)) profile = 0) :
    quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
      profile who = -1 := by
  have hconservation := quittingLiveMassLimit_add_sum_absorbedMassLimit
    (quittingNegativeTerminalReward (ι := ι)) profile
  unfold quittingTerminalPayoff
  change (∑ S, quittingAbsorbedMassLimit
    (quittingNegativeTerminalReward (ι := ι)) profile S * (-1)) = -1
  calc
    _ = -(∑ S, quittingAbsorbedMassLimit
        (quittingNegativeTerminalReward (ι := ι)) profile S) := by
      rw [← Finset.sum_mul]
      ring
    _ = -1 := by linarith

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- All terminal outcome atoms in the negative table are at most zero. -/
theorem quittingNegativeTerminalOutcomeReward_le_zero
    (outcome : QuittingTerminalOutcome ι) (who : ι) :
    quittingTerminalOutcomeReward
      (quittingNegativeTerminalReward (ι := ι)) outcome who ≤ 0 := by
  cases outcome <;> simp [quittingTerminalOutcomeReward,
    quittingNegativeTerminalReward]

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
theorem quittingHazardNeverMass_alwaysContinue_eq_one :
    quittingHazardNeverMass (fun _ : ℕ => (PMF.pure false : PMF Bool)) = 1 := by
  have hsurvival : ∀ fuel,
      quittingHazardSurvival
        (fun _ : ℕ => (PMF.pure false : PMF Bool)) fuel = 1 := by
    intro fuel
    simp [quittingHazardSurvival_eq_prod]
  apply tendsto_nhds_unique
    (tendsto_quittingHazardSurvival_neverMass
      (fun _ : ℕ => (PMF.pure false : PMF Bool)))
  convert (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
  funext fuel
  exact hsurvival fuel

omit [Nontrivial ι] in
/-- The designated seed has zero Never mass. -/
theorem quittingSingleSeedProfile_seed_neverMass_eq_zero (seed : ι) :
    quittingHazardNeverMass
      (quittingBehaviorLiveHazard
        (quittingNegativeTerminalReward (ι := ι))
        (quittingSingleSeedProfile seed seed)) = 0 := by
  have hhazard : quittingBehaviorLiveHazard
      (quittingNegativeTerminalReward (ι := ι))
      (quittingSingleSeedProfile seed seed) =
        quittingPureTimeHazard (some 0) := by
    funext time
    unfold quittingBehaviorLiveHazard quittingSingleSeedProfile
    rw [Function.update_self]
    rfl
  rw [hhazard]
  apply le_antisymm
  · calc
      quittingHazardNeverMass (quittingPureTimeHazard (some 0)) ≤
          quittingHazardSurvival (quittingPureTimeHazard (some 0)) 1 :=
        quittingHazardNeverMass_le_survival _ _
      _ = 0 := by
        simp [quittingHazardSurvival_eq_prod]
  · exact quittingHazardNeverMass_nonneg _

omit [Nontrivial ι] in
/-- Every nonseed coordinate Continues forever and has Never mass one. -/
theorem quittingSingleSeedProfile_other_neverMass_eq_one
    (seed player : ι) (hplayer : player ≠ seed) :
    quittingHazardNeverMass
      (quittingBehaviorLiveHazard
        (quittingNegativeTerminalReward (ι := ι))
        (quittingSingleSeedProfile seed player)) = 1 := by
  have hhazard : quittingBehaviorLiveHazard
      (quittingNegativeTerminalReward (ι := ι))
      (quittingSingleSeedProfile seed player) =
        (fun _ : ℕ => (PMF.pure false : PMF Bool)) := by
    funext time
    unfold quittingBehaviorLiveHazard quittingSingleSeedProfile
    rw [Function.update_of_ne hplayer]
    rfl
  rw [hhazard]
  exact quittingHazardNeverMass_alwaysContinue_eq_one

omit [DecidableEq ι] [Nontrivial ι] in
/-- The zero-seed all-Continue source has Never mass one at every coordinate. -/
theorem quittingAlwaysContinueProfile_neverMass_eq_one (player : ι) :
    quittingHazardNeverMass
      (quittingBehaviorLiveHazard
        (quittingNegativeTerminalReward (ι := ι))
        (quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι)) player)) = 1 := by
  have hhazard : quittingBehaviorLiveHazard
      (quittingNegativeTerminalReward (ι := ι))
      (quittingAlwaysContinueProfile
        (quittingNegativeTerminalReward (ι := ι)) player) =
        (fun _ : ℕ => (PMF.pure false : PMF Bool)) := by
    rfl
  rw [hhazard]
  exact quittingHazardNeverMass_alwaysContinue_eq_one

omit [Nontrivial ι] in
/-- Under the negative table, the zero-seed all-Continue source has envelope
zero: Never attains zero and all absorbing outcomes pay negatively. -/
theorem quittingNegative_allContinue_envelope_eq_zero (observer : ι) :
    quittingContinuationBestResponseValue
      (quittingNegativeTerminalReward (ι := ι))
      (quittingAlwaysContinueProfile
        (quittingNegativeTerminalReward (ι := ι))) observer = 0 := by
  apply le_antisymm
  · exact quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      (quittingAlwaysContinueProfile
        (quittingNegativeTerminalReward (ι := ι))) observer 0
      (fun outcome => quittingNegativeTerminalOutcomeReward_le_zero
        outcome observer)
  · have hlower :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        (quittingNegativeTerminalReward (ι := ι))
        (quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι))) observer
        (quittingAlwaysContinueStrategy
          (quittingNegativeTerminalReward (ι := ι)) observer)
    have hupdate : Function.update
        (quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι))) observer
        (quittingAlwaysContinueStrategy
          (quittingNegativeTerminalReward (ι := ι)) observer) =
        quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι)) := by
      funext player time history
      by_cases hplayer : player = observer
      · subst player
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne hplayer]
    rw [hupdate, quittingTerminalPayoff_quittingAlwaysContinue] at hlower
    exact hlower

omit [Nontrivial ι] in
/-- The source one-seed profile gives the seed a Never deviation worth zero,
and no terminal outcome pays positively. -/
theorem quittingSingleSeedProfile_envelope_eq_zero (seed : ι) :
    quittingContinuationBestResponseValue
      (quittingNegativeTerminalReward (ι := ι))
      (quittingSingleSeedProfile seed) seed = 0 := by
  apply le_antisymm
  · exact quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      (quittingSingleSeedProfile seed) seed 0
        (fun outcome => quittingNegativeTerminalOutcomeReward_le_zero
          outcome seed)
  · have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        (quittingNegativeTerminalReward (ι := ι))
        (quittingSingleSeedProfile seed) seed
        (quittingAlwaysContinueStrategy
          (quittingNegativeTerminalReward (ι := ι)) seed)
    have hprofile : Function.update (quittingSingleSeedProfile seed) seed
        (quittingAlwaysContinueStrategy
          (quittingNegativeTerminalReward (ι := ι)) seed) =
        quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι)) := by
      funext player time history
      by_cases hplayer : player = seed
      · subst player
        simp [quittingSingleSeedProfile, quittingAlwaysContinueProfile,
          quittingAlwaysContinueStrategy,
          StochasticGame.stationaryBehaviorProfile]
      · simp [quittingSingleSeedProfile, quittingAlwaysContinueProfile,
          StochasticGame.stationaryBehaviorProfile,
          Function.update_of_ne hplayer]
    rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue] at hdeviation
    exact hdeviation

omit [Nontrivial ι] in
/-- The seed's prescribed payoff in the source is `-1`: it quits immediately
under the constant negative terminal table. -/
theorem quittingSingleSeedProfile_payoff_eq_neg_one (seed : ι) :
    quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
      (quittingSingleSeedProfile seed) seed = -1 := by
  have hsure : quittingSingleSeedProfile seed seed 0
      (quittingLiveHist (quittingNegativeTerminalReward (ι := ι)) 0) =
        PMF.pure true := by
    simp [quittingSingleSeedProfile, quittingPureTimeBehaviorStrategy,
      quittingPureTimeHazard]
  exact quittingTerminalPayoff_negative_eq_neg_one_of_liveMassLimit_zero
    (quittingSingleSeedProfile seed) seed
    (quittingLiveMassLimit_eq_zero_of_live_sureQuitter
      (quittingNegativeTerminalReward (ι := ι))
      (quittingSingleSeedProfile seed) seed 0 hsure)

/-- Every all-player finite cap has envelope `-1` for every observer: an
undeviated opponent supplies certain finite absorption. -/
theorem quittingAllPlayersFiniteCap_negative_envelope_eq_neg_one
    (source capped :
      (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover = quittingStoppingLawFiniteCapBehaviorStrategy
        (quittingNegativeTerminalReward (ι := ι)) mover
          (source mover) cutoff)
    (observer : ι) :
    quittingContinuationBestResponseValue
      (quittingNegativeTerminalReward (ι := ι)) capped observer = -1 := by
  obtain ⟨opponent, hopponent⟩ : ∃ opponent : ι, opponent ≠ observer :=
    exists_ne observer
  obtain ⟨cutoff, hcap⟩ := hcapped opponent
  have hdeviationPayoff : ∀ deviation,
      quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
        (Function.update capped observer deviation) observer = -1 := by
    intro deviation
    have hsure : (Function.update capped observer deviation) opponent cutoff
        (quittingLiveHist (quittingNegativeTerminalReward (ι := ι)) cutoff) =
        PMF.pure true := by
      rw [Function.update_of_ne hopponent, hcap]
      change quittingHazardCapAt
        (quittingBehaviorLiveHazard
          (quittingNegativeTerminalReward (ι := ι)) (source opponent))
        cutoff cutoff = PMF.pure true
      exact quittingHazardCapAt_self _ cutoff
    exact quittingTerminalPayoff_negative_eq_neg_one_of_liveMassLimit_zero
      (Function.update capped observer deviation) observer
      (quittingLiveMassLimit_eq_zero_of_live_sureQuitter
        (quittingNegativeTerminalReward (ι := ι))
        (Function.update capped observer deviation) opponent cutoff hsure)
  unfold quittingContinuationBestResponseValue
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨capped observer, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact le_of_eq (hdeviationPayoff deviation)
  · have hlower :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        (quittingNegativeTerminalReward (ι := ι)) capped observer
        (capped observer)
    rw [hdeviationPayoff (capped observer)] at hlower
    exact hlower

omit [DecidableEq ι] [Nontrivial ι] in
/-- A fully finitely capped profile also gives every player prescribed payoff
`-1`, because that player's own cap already forces absorption. -/
theorem quittingAllPlayersFiniteCap_negative_payoff_eq_neg_one
    (source capped :
      (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover = quittingStoppingLawFiniteCapBehaviorStrategy
        (quittingNegativeTerminalReward (ι := ι)) mover
          (source mover) cutoff)
    (observer : ι) :
    quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
      capped observer = -1 := by
  obtain ⟨cutoff, hcap⟩ := hcapped observer
  have hsure : capped observer cutoff
      (quittingLiveHist (quittingNegativeTerminalReward (ι := ι)) cutoff) =
        PMF.pure true := by
    rw [hcap]
    change quittingHazardCapAt
      (quittingBehaviorLiveHazard
        (quittingNegativeTerminalReward (ι := ι)) (source observer))
      cutoff cutoff = PMF.pure true
    exact quittingHazardCapAt_self _ cutoff
  exact quittingTerminalPayoff_negative_eq_neg_one_of_liveMassLimit_zero
    capped observer
    (quittingLiveMassLimit_eq_zero_of_live_sureQuitter
      (quittingNegativeTerminalReward (ι := ι)) capped observer cutoff hsure)

/-- **Sharp one-seed obstruction.**  No coordinatewise all-player finite cap
can approximate the one-seed source's full behavioral envelope at the seed:
the distance is exactly one, independently of every selected cap date. -/
theorem quittingSingleSeed_allFiniteCaps_envelope_distance_eq_one
    (seed : ι)
    (capped :
      (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover = quittingStoppingLawFiniteCapBehaviorStrategy
        (quittingNegativeTerminalReward (ι := ι)) mover
          (quittingSingleSeedProfile seed mover) cutoff) :
    |quittingContinuationBestResponseValue
          (quittingNegativeTerminalReward (ι := ι))
          (quittingSingleSeedProfile seed) seed -
        quittingContinuationBestResponseValue
          (quittingNegativeTerminalReward (ι := ι)) capped seed| = 1 := by
  rw [quittingSingleSeedProfile_envelope_eq_zero,
    quittingAllPlayersFiniteCap_negative_envelope_eq_neg_one
      (quittingSingleSeedProfile seed) capped hcapped seed]
  norm_num

/-- The same obstruction appears as an exact unit semantic-debt gap: source
debt is one and every all-player finite cap has zero debt at the seed. -/
theorem quittingSingleSeed_allFiniteCaps_debt_distance_eq_one
    (seed : ι)
    (capped :
      (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover = quittingStoppingLawFiniteCapBehaviorStrategy
        (quittingNegativeTerminalReward (ι := ι)) mover
          (quittingSingleSeedProfile seed mover) cutoff) :
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair
            (quittingNegativeTerminalReward (ι := ι))
            (quittingSingleSeedProfile seed)) seed -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair
            (quittingNegativeTerminalReward (ι := ι)) capped) seed| = 1 := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change |(quittingContinuationBestResponseValue
        (quittingNegativeTerminalReward (ι := ι))
        (quittingSingleSeedProfile seed) seed -
      quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
        (quittingSingleSeedProfile seed) seed) -
    (quittingContinuationBestResponseValue
        (quittingNegativeTerminalReward (ι := ι)) capped seed -
      quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
        capped seed)| = 1
  rw [quittingSingleSeedProfile_envelope_eq_zero,
    quittingSingleSeedProfile_payoff_eq_neg_one,
    quittingAllPlayersFiniteCap_negative_envelope_eq_neg_one
      (quittingSingleSeedProfile seed) capped hcapped seed,
    quittingAllPlayersFiniteCap_negative_payoff_eq_neg_one
      (quittingSingleSeedProfile seed) capped hcapped seed]
  norm_num

/-- **Sharp zero-seed obstruction.**  Starting from all Continue, every
coordinate has positive Never mass and every all-player finite cap moves both
prescribed payoff and behavioral envelope by exactly one. -/
theorem quittingZeroSeed_allFiniteCaps_payoff_envelope_distance_eq_one
    (observer : ι)
    (capped :
      (quittingGame (quittingNegativeTerminalReward (ι := ι))).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover = quittingStoppingLawFiniteCapBehaviorStrategy
        (quittingNegativeTerminalReward (ι := ι)) mover
          (quittingAlwaysContinueProfile
            (quittingNegativeTerminalReward (ι := ι)) mover) cutoff) :
    |quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
          (quittingAlwaysContinueProfile
            (quittingNegativeTerminalReward (ι := ι))) observer -
        quittingTerminalPayoff (quittingNegativeTerminalReward (ι := ι))
          capped observer| = 1 ∧
      |quittingContinuationBestResponseValue
          (quittingNegativeTerminalReward (ι := ι))
          (quittingAlwaysContinueProfile
            (quittingNegativeTerminalReward (ι := ι))) observer -
        quittingContinuationBestResponseValue
          (quittingNegativeTerminalReward (ι := ι)) capped observer| = 1 := by
  constructor
  · rw [quittingTerminalPayoff_quittingAlwaysContinue,
      quittingAllPlayersFiniteCap_negative_payoff_eq_neg_one
        (quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι))) capped hcapped observer]
    norm_num
  · rw [quittingNegative_allContinue_envelope_eq_zero,
      quittingAllPlayersFiniteCap_negative_envelope_eq_neg_one
        (quittingAlwaysContinueProfile
          (quittingNegativeTerminalReward (ι := ι))) capped hcapped observer]
    norm_num

end GameTheory
