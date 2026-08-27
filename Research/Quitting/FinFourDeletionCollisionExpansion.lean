/-
Copyright (c) 2026 UniformEquilibrium contributors.
Released under the MIT license as described in the file LICENSE.
-/

import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Classification.BlockDeletionInequality
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiveWeightedCollisionTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourOffMinimumChargedBlockerGate
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargePersistentBaseActualAdapter
import
  UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawExploitabilityFloor
import MathUE.FinitePaidCollision
import Research.Quitting.FinFourDeletionNearCap

/-!
# Finite deletion collision expansion

This Research module isolates the game-semantic algebra needed by the
four-player deletion producer.  It proves literal root identities and keeps
the deletion profile, date, and collision atom explicit.  It includes both a
verifier for supplied collision data and a small-solo-premium producer that
constructs such data from the near-cap deletion hypotheses.  The downstream
chronological composition problem remains outside this module.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev FinFourReward := {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

/-- The payoff increment from adding a distinguished quitter to an opponent
coalition.  The empty coalition is deliberately retained: its value is the
solo-versus-tail term, while the seven nonempty coalitions are the collision
terms in the Fin4 deletion expansion. -/
def quittingDeletionInsertionIncrement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (j : ι) (S : Finset ι) : ℝ :=
  quittingEndpointInsertionToggle reward tail j S

omit [Fintype ι] in
@[simp] theorem quittingDeletionInsertionIncrement_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (j : ι) (S : Finset ι) (hS : S.Nonempty) :
    quittingDeletionInsertionIncrement reward tail j S =
      reward ⟨insert j S, Finset.insert_nonempty j S⟩ j - reward ⟨S, hS⟩ j := by
  simp [quittingDeletionInsertionIncrement, quittingEndpointInsertionToggle,
    quittingStageCoalitionPayoff, hS]

theorem quittingDeletionSurvivorCoalition_card_finFour (j : Fin 4) :
    ((Finset.univ.erase j).powerset.erase ∅).card = 7 := by
  have hcard : (Finset.univ.erase j : Finset (Fin 4)).card = 3 := by simp
  rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset _)]
  rw [Finset.card_powerset, hcard]
  norm_num

theorem quittingRootEndpointDifference_eq_finFour_deletionExpansion
    (reward : FinFourReward) (tail : Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (j : Fin 4) :
    quittingRootEndpointDifference reward tail root j =
      quittingOpponentCoalitionMass root j ∅ *
          quittingDeletionInsertionIncrement reward tail j ∅ +
        ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
          quittingOpponentCoalitionMass root j S *
            quittingDeletionInsertionIncrement reward tail j S := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  let carrier := (Finset.univ.erase j).powerset
  let term := fun S : Finset (Fin 4) ↦
    quittingOpponentCoalitionMass root j S *
      quittingDeletionInsertionIncrement reward tail j S
  have hempty : (∅ : Finset (Fin 4)) ∈ carrier := by simp [carrier]
  change ∑ S ∈ carrier, term S = _
  rw [← Finset.add_sum_erase carrier term hempty]

theorem quittingFinFourDeletionExpansion_nonempty_term_eq_reward_difference
    (reward : FinFourReward) (tail : Payoff (Fin 4)) (j : Fin 4)
    {S : Finset (Fin 4)} (hS : S ∈ (Finset.univ.erase j).powerset.erase ∅) :
    quittingDeletionInsertionIncrement reward tail j S =
      reward ⟨insert j S, Finset.insert_nonempty j S⟩ j -
        reward ⟨S, Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1⟩ j := by
  apply quittingDeletionInsertionIncrement_nonempty

def quittingDeletionUnconditionalSurvivorMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : ι) (S : Finset ι) : ℝ :=
  quittingStageCoalitionMass reward profile stage
    ⟨insert j S, Finset.insert_nonempty j S⟩

theorem quittingDeletionUnconditionalSurvivorMass_eq_live_mul_opponentMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : ι) (S : Finset ι)
    (hS : S ⊆ Finset.univ.erase j)
    (hroot : (quittingProfileLiveRoot reward profile stage) j = PMF.pure true) :
    quittingDeletionUnconditionalSurvivorMass reward profile stage j S =
      quittingLiveMass reward profile stage *
        quittingOpponentCoalitionMass (quittingProfileLiveRoot reward profile stage)
          j S := by
  unfold quittingDeletionUnconditionalSurvivorMass
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hjtrue : ((quittingProfileLiveRoot reward profile stage) j true).toReal = 1 := by
    rw [hroot]
    simp
  have hjfalse : ((quittingProfileLiveRoot reward profile stage) j false).toReal = 0 := by
    rw [hroot]
    simp
  have hjnot : j ∉ S := by
    intro hj
    exact (Finset.mem_erase.mp (hS hj)).1 rfl
  unfold quittingRootCoalitionMass quittingRootQuitRates
  unfold quittingOpponentCoalitionMass
  unfold coalitionMass
  rw [Finset.prod_insert hjnot]
  simp only [hjtrue, one_mul, pmfBool_false_toReal]
  congr 2
  rw [show (insert j S)ᶜ = Finset.univ.erase j \ S by
    ext player
    simp]

theorem quittingFinFourDeletion_pureTimeGain_eq_survival_mul_endpoint
    (reward : FinFourReward)
    (profile : (quittingGame reward).BehaviorProfile) (j : Fin 4) (stage : ℕ)
    (hnever : profile j = quittingPureTimeBehaviorStrategy reward j none) :
    quittingTerminalPayoff reward
        (Function.update profile j
          (quittingPureTimeBehaviorStrategy reward j (some stage))) j -
        quittingTerminalPayoff reward profile j =
      quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward profile)
          j 0 stage *
    quittingRootEndpointDifference reward
          (fun _ => quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward profile) j none (stage + 1))
          (quittingProfileLiveRoot reward profile stage) j := by
  have hupdate : Function.update profile j
      (quittingPureTimeBehaviorStrategy reward j none) = profile := by
    rw [← hnever]
    exact Function.update_eq_self j profile
  calc
    quittingTerminalPayoff reward
          (Function.update profile j
            (quittingPureTimeBehaviorStrategy reward j (some stage))) j -
        quittingTerminalPayoff reward profile j =
      quittingTerminalPayoff reward
          (Function.update profile j
            (quittingPureTimeBehaviorStrategy reward j (some stage))) j -
        quittingTerminalPayoff reward
          (Function.update profile j
            (quittingPureTimeBehaviorStrategy reward j none)) j := by
      rw [hupdate]
    _ = quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward profile) j (some stage) 0 -
        quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward profile) j none 0 := by
      rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
        quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    _ = _ := by
      simpa using quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
        reward (quittingProfileLiveRoot reward profile) j 0 stage

theorem quittingFinFourDeletion_pureTimeGain_eq_liveMass_mul_endpoint
    (reward : FinFourReward)
    (profile : (quittingGame reward).BehaviorProfile) (j : Fin 4) (stage : ℕ)
    (hnever : profile j = quittingPureTimeBehaviorStrategy reward j none)
    (hsurvival : quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) j 0 stage =
      quittingLiveMass reward profile stage) :
    quittingTerminalPayoff reward
        (Function.update profile j
          (quittingPureTimeBehaviorStrategy reward j (some stage))) j -
        quittingTerminalPayoff reward profile j =
      quittingLiveMass reward profile stage *
        quittingRootEndpointDifference reward
          (fun _ => quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward profile) j none (stage + 1))
          (quittingProfileLiveRoot reward profile stage) j := by
  rw [quittingFinFourDeletion_pureTimeGain_eq_survival_mul_endpoint
    reward profile j stage hnever, hsurvival]

theorem quittingFinFourDeletion_gain_eq_stageMass_expansion
    (reward : FinFourReward)
    (source target : (quittingGame reward).BehaviorProfile)
    (j : Fin 4) (stage : ℕ)
    (hnever : source j = quittingPureTimeBehaviorStrategy reward j none)
    (htarget : target = Function.update source j
      (quittingPureTimeBehaviorStrategy reward j (some stage)))
    (hlive : quittingLiveMass reward target stage =
      quittingLiveMass reward source stage)
    (hroot : (quittingProfileLiveRoot reward target stage) j = PMF.pure true)
    (hopponents : ∀ player, player ≠ j →
      (quittingProfileLiveRoot reward target stage) player =
        (quittingProfileLiveRoot reward source stage) player)
    (hsurvival : quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward source) j 0 stage =
      quittingLiveMass reward source stage) :
    quittingTerminalPayoff reward target j - quittingTerminalPayoff reward source j =
      quittingStageCoalitionMass reward target stage
          (quittingSingletonTerminal j) *
          quittingDeletionInsertionIncrement reward
            (fun _ => quittingRootSequencePureTimeTerminalValue reward
              (quittingProfileLiveRoot reward source) j none (stage + 1)) j ∅ +
        ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
          quittingStageCoalitionMass reward target stage
            ⟨insert j S, Finset.insert_nonempty j S⟩ *
            quittingDeletionInsertionIncrement reward
              (fun _ => quittingRootSequencePureTimeTerminalValue reward
                (quittingProfileLiveRoot reward source) j none (stage + 1)) j S := by
  let tail : Payoff (Fin 4) := fun _ =>
    quittingRootSequencePureTimeTerminalValue reward
      (quittingProfileLiveRoot reward source) j none (stage + 1)
  have hgain := quittingFinFourDeletion_pureTimeGain_eq_liveMass_mul_endpoint
    reward source j stage hnever hsurvival
  rw [show (fun _ => quittingRootSequencePureTimeTerminalValue reward
      (quittingProfileLiveRoot reward source) j none (stage + 1)) = tail by
    rfl] at hgain ⊢
  rw [quittingRootEndpointDifference_eq_finFour_deletionExpansion] at hgain
  have hrootMass (S : Finset (Fin 4))
      (hS : S ⊆ Finset.univ.erase j) :
      quittingStageCoalitionMass reward target stage
          ⟨insert j S, Finset.insert_nonempty j S⟩ =
        quittingLiveMass reward source stage *
          quittingOpponentCoalitionMass
            (quittingProfileLiveRoot reward source stage) j S := by
    have hmass := quittingDeletionUnconditionalSurvivorMass_eq_live_mul_opponentMass
      reward target stage j S hS hroot
    rw [hlive] at hmass
    unfold quittingDeletionUnconditionalSurvivorMass at hmass
    rw [hmass]
    unfold quittingOpponentCoalitionMass
    apply congrArg₂ (· * ·)
    · rfl
    · apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro player hplayer
        rw [hopponents player (by
          intro hplayerj
          subst player
          exact (Finset.mem_erase.mp (hS hplayer)).1 rfl)]
      · apply Finset.prod_congr rfl
        intro player hplayer
        rw [hopponents player (by
          exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hplayer).1).1)]
  have hrootMassEmpty : quittingStageCoalitionMass reward target stage
      (quittingSingletonTerminal j) =
    quittingLiveMass reward source stage *
      quittingOpponentCoalitionMass
        (quittingProfileLiveRoot reward source stage) j ∅ := by
    simpa [quittingSingletonTerminal] using hrootMass ∅ (by simp)
  have hrootMassS : ∀ S ∈ (Finset.univ.erase j).powerset.erase ∅,
      quittingStageCoalitionMass reward target stage
          ⟨insert j S, Finset.insert_nonempty j S⟩ =
        quittingLiveMass reward source stage *
          quittingOpponentCoalitionMass
            (quittingProfileLiveRoot reward source stage) j S := by
    intro S hS
    exact hrootMass S (Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2)
  have hsum :
      (∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
        quittingStageCoalitionMass reward target stage
          ⟨insert j S, Finset.insert_nonempty j S⟩ *
          quittingDeletionInsertionIncrement reward tail j S) =
        quittingLiveMass reward source stage *
          ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
            quittingOpponentCoalitionMass
              (quittingProfileLiveRoot reward source stage) j S *
              quittingDeletionInsertionIncrement reward tail j S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [hrootMassS S hS]
    ring
  rw [hrootMassEmpty, hsum, htarget]
  calc
    quittingTerminalPayoff reward
          (Function.update source j
            (quittingPureTimeBehaviorStrategy reward j (some stage))) j -
        quittingTerminalPayoff reward source j =
      quittingLiveMass reward source stage *
        (quittingOpponentCoalitionMass
            (quittingProfileLiveRoot reward source stage) j ∅ *
            quittingDeletionInsertionIncrement reward tail j ∅ +
          ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
            quittingOpponentCoalitionMass
              (quittingProfileLiveRoot reward source stage) j S *
              quittingDeletionInsertionIncrement reward tail j S) := hgain
    _ = quittingLiveMass reward source stage *
          quittingOpponentCoalitionMass
            (quittingProfileLiveRoot reward source stage) j ∅ *
          quittingDeletionInsertionIncrement reward tail j ∅ +
        quittingLiveMass reward source stage *
          ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
            quittingOpponentCoalitionMass
              (quittingProfileLiveRoot reward source stage) j S *
              quittingDeletionInsertionIncrement reward tail j S := by ring

theorem quittingFinFourDeletion_continuationTail_ge_floor
    (reward : FinFourReward) (roots : ℕ → Fin 4 → PMF Bool) (j : Fin 4)
    (start : ℕ) :
    quittingContinueFloor reward j ≤
      quittingRootSequencePureTimeTerminalValue reward roots j none start := by
  apply continueFloor_le_neverTail_of_quiet reward {j} roots j
    (quittingContinueFloor reward j)
    (quittingRootsBlockQuiet_singleton j roots)
  · intro S hS hdisjoint
    exact quittingContinueFloor_le reward j S hS
      (Finset.disjoint_singleton_right.mp hdisjoint)
  · exact quittingContinueFloor_nonpos reward j

theorem quittingFinFourDeletion_soloTerm_le_floor_premium
    (reward : FinFourReward) (tail : Payoff (Fin 4))
    (j : Fin 4) (floor : ℝ) (mass : ℝ)
    (hmass0 : 0 ≤ mass) (hmass1 : mass ≤ 1)
    (hfloor : floor ≤ tail j) :
    mass * (reward (quittingSingletonTerminal j) j - tail j) ≤
      max 0 (reward (quittingSingletonTerminal j) j - floor) := by
  by_cases hgap : 0 ≤ reward (quittingSingletonTerminal j) j - tail j
  · have hle : reward (quittingSingletonTerminal j) j - tail j ≤
        reward (quittingSingletonTerminal j) j - floor := by linarith
    calc
      mass * (reward (quittingSingletonTerminal j) j - tail j) ≤
          1 * (reward (quittingSingletonTerminal j) j - tail j) := by
        gcongr
      _ ≤ max 0 (reward (quittingSingletonTerminal j) j - floor) := by
        rw [one_mul]
        exact le_max_of_le_right hle
  · have hle : mass * (reward (quittingSingletonTerminal j) j - tail j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hmass0 (le_of_not_ge hgap)
    exact hle.trans (le_max_left 0 _)

theorem quittingDeletionInsertionIncrement_le_finFourDeletionCollisionCap
    (reward : FinFourReward) (tail : Payoff (Fin 4)) (j : Fin 4)
    {S : Finset (Fin 4)}
    (hS : S ∈ (Finset.univ.erase j).powerset.erase ∅) :
    quittingDeletionInsertionIncrement reward tail j S ≤
      finFourDeletionCollisionCap reward j := by
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp hS).1
  have hjnot : j ∉ S := by
    intro hj
    exact (Finset.mem_erase.mp (Finset.mem_powerset.mp
      (Finset.mem_erase.mp hS).2 hj)).1 rfl
  let terminal : FinFourDeletionSurvivorTerminal j :=
    ⟨⟨S, hSne⟩, hjnot⟩
  have hmem : reward (finFourDeletionJoinTerminal j terminal) j -
      reward terminal.1 j ∈ Set.range (fun candidate :
        FinFourDeletionSurvivorTerminal j =>
          reward (finFourDeletionJoinTerminal j candidate) j - reward candidate.1 j) :=
    Set.mem_range_self terminal
  have hcap : reward (finFourDeletionJoinTerminal j terminal) j -
      reward terminal.1 j ≤ sSup (Set.range (fun candidate :
        FinFourDeletionSurvivorTerminal j =>
          reward (finFourDeletionJoinTerminal j candidate) j - reward candidate.1 j)) := by
    apply le_csSup
    · exact Finite.bddAbove_range _
    · exact hmem
  have hincrement : quittingDeletionInsertionIncrement reward tail j S =
      reward (finFourDeletionJoinTerminal j terminal) j - reward terminal.1 j := by
    rw [quittingDeletionInsertionIncrement,
      quittingEndpointInsertionToggle_of_nonempty reward tail j S hSne]
    have hjoin : (⟨insert j S, Finset.insert_nonempty j S⟩ :
        {T : Finset (Fin 4) // T.Nonempty}) = finFourDeletionJoinTerminal j terminal := by
      apply Subtype.ext
      simp [terminal, finFourDeletionJoinTerminal]
    rw [hjoin]
  rw [hincrement]
  unfold finFourDeletionCollisionCap
  exact hcap.trans (le_max_right _ _)

theorem finFourDeletionFloor_le_quittingContinueFloor
    (reward : FinFourReward) (j : Fin 4) :
    finFourDeletionFloor reward j ≤ quittingContinueFloor reward j := by
  unfold finFourDeletionFloor
  apply le_quittingBlockContinueFloor reward {j} j
  · exact min_le_left _ _
  · intro S hS hdisjoint
    have hjnot : j ∉ S := Finset.disjoint_singleton_right.mp hdisjoint
    let survivor : FinFourDeletionSurvivorTerminal j := ⟨⟨S, hS⟩, hjnot⟩
    have hmem : reward survivor.1 j ∈
        Set.range (fun candidate : FinFourDeletionSurvivorTerminal j =>
          reward candidate.1 j) := Set.mem_range_self survivor
    have hinf : sInf (Set.range (fun candidate : FinFourDeletionSurvivorTerminal j =>
        reward candidate.1 j)) ≤ reward ⟨S, hS⟩ j := by
      apply csInf_le
      · exact Finite.bddBelow_range _
      · simpa [survivor] using hmem
    exact (min_le_right _ _).trans (by simpa [survivor] using hinf)

theorem finFourDeletionNearCapData_sigma_player_never
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    data.sigma j = quittingPureTimeBehaviorStrategy reward j none := by
  rw [data.sigma_eq]
  have hlift := Function.update_liftDeletedProfile_never reward
    (fun who => who = j) data.rho (howner := rfl)
  funext time history
  have hpoint := congrFun (congrFun (congrFun hlift j) time) history
  simpa [quittingLiftDeletedProfile] using hpoint.symm

theorem finFourDeletionNearCapData_survival_eq_liveMass
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward data.sigma)
        j 0 data.t = quittingLiveMass reward data.sigma data.t := by
  have hnever := finFourDeletionNearCapData_sigma_player_never reward j data
  have hprofile : quittingOpponentOnlyProfile reward data.sigma j = data.sigma := by
    unfold quittingOpponentOnlyProfile
    rw [← quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue, ← hnever]
    exact Function.update_eq_self j data.sigma
  rw [quittingOpponentSurvivalWeight_profileLiveRoot_eq_liveMass
    reward data.sigma j data.t, hprofile]

theorem finFourDeletionNearCapData_tau_root_player_quits
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    quittingProfileLiveRoot reward data.tau data.t j = PMF.pure true := by
  rw [quittingProfileLiveRoot, data.tau_eq]
  simp [quittingPureTimeBehaviorStrategy]

theorem finFourDeletionNearCapData_tau_source_liveMass_eq
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    quittingLiveMass reward data.tau data.t =
      quittingLiveMass reward data.sigma data.t := by
  have hnever := finFourDeletionNearCapData_sigma_player_never reward j data
  have hagree : (quittingGame reward).ProfilesAgreeBefore data.sigma data.tau data.t := by
    intro player time history htime
    by_cases hplayer : player = j
    · subst player
      rw [data.tau_eq]
      simp [hnever, quittingPureTimeBehaviorStrategy]
      rw [quittingPureTimeHazard_some_of_ne (by omega)]
    · simp [data.tau_eq, Function.update_of_ne hplayer]
  unfold quittingLiveMass
  rw [(quittingGame reward).histDist_eq_of_profilesAgreeBefore hagree data.t le_rfl]

theorem quittingStageCoalitionMass_singleton_le_one
    (reward : FinFourReward) (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : Fin 4) :
    quittingStageCoalitionMass reward profile stage (quittingSingletonTerminal j) ≤ 1 := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hmass := quittingRootCoalitionMass_le_quitProbability_of_mem
    (quittingProfileLiveRoot reward profile stage) {j} j (by simp)
  have hprob : (quittingProfileLiveRoot reward profile stage j true).toReal ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((quittingProfileLiveRoot reward profile stage j).coe_le_one true)
  have hroot : quittingRootCoalitionMass
      (quittingProfileLiveRoot reward profile stage) {j} ≤ 1 := hmass.trans hprob
  have hlive := quittingLiveMass_le_one reward profile stage
  have hroot' : quittingRootCoalitionMass
      (quittingProfileLiveRoot reward profile stage)
        (quittingSingletonTerminal j) ≤ 1 := by
    simpa [quittingSingletonTerminal] using hroot
  nlinarith [quittingLiveMass_nonneg reward profile stage,
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (quittingProfileLiveRoot reward profile stage) (quittingSingletonTerminal j).val]

theorem finFourDeletionNearCapData_tau_root_eq_source_off_player
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    ∀ player, player ≠ j →
      quittingProfileLiveRoot reward data.tau data.t player =
        quittingProfileLiveRoot reward data.sigma data.t player := by
  intro player hplayer
  rw [quittingProfileLiveRoot, data.tau_eq]
  simp [Function.update_of_ne hplayer]
  rfl

theorem finFourDeletionNearCapData_tau_root_eq_source_after
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    ∀ offset player,
      quittingProfileLiveRoot reward data.tau (data.t + 1 + offset) player =
        quittingProfileLiveRoot reward data.sigma (data.t + 1 + offset) player := by
  intro offset player
  by_cases hplayer : player = j
  · subst player
    rw [quittingProfileLiveRoot, data.tau_eq]
    simp only [Function.update_self, quittingPureTimeBehaviorStrategy]
    rw [quittingPureTimeHazard_some_of_ne (by omega)]
    have hnever := finFourDeletionNearCapData_sigma_player_never reward j data
    have hpoint := congrFun (congrFun hnever (data.t + 1 + offset))
      (quittingLiveHist reward (data.t + 1 + offset))
    change PMF.pure false = data.sigma j (data.t + 1 + offset)
      (quittingLiveHist reward (data.t + 1 + offset))
    exact hpoint.symm
  · rw [quittingProfileLiveRoot, data.tau_eq]
    simp [Function.update_of_ne hplayer]
    rfl

theorem finFourDeletionNearCapData_consumerTail_coord_eq_neverTail
    (reward : FinFourReward) (j : Fin 4)
    {epsilon delta gamma : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma) :
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1 j =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1) := by
  have htail := quittingTerminalPayoff_allContinueSpine_eq_rootSequenceTerminalValue
    reward data.tau j (data.t + 1)
  change quittingTerminalPayoff reward
      (quittingAllContinueProfileSpine reward data.tau (data.t + 1)) j = _
  rw [htail]
  unfold quittingRootSequencePureTimeTerminalValue
  have hnever := finFourDeletionNearCapData_sigma_player_never reward j data
  have hroots : quittingRootSequenceUpdate
      (quittingProfileLiveRoot reward data.sigma) j
        (quittingPureTimeHazard none) =
      quittingProfileLiveRoot reward data.sigma := by
    funext time player
    by_cases hplayer : player = j
    · subst player
      rw [quittingRootSequenceUpdate, Function.update_self,
        quittingPureTimeHazard_none]
      unfold quittingProfileLiveRoot
      rw [hnever]
      rfl
    · simp [quittingRootSequenceUpdate, hplayer]
  unfold quittingRootSequenceHazardTerminalValue
  rw [hroots]
  rw [quittingRootSequenceTerminalValue_eq_shift reward
    (quittingProfileLiveRoot reward data.tau) j (data.t + 1)]
  rw [quittingRootSequenceTerminalValue_eq_shift reward
    (quittingProfileLiveRoot reward data.sigma) j (data.t + 1)]
  congr 1
  funext offset player
  exact finFourDeletionNearCapData_tau_root_eq_source_after reward j data offset player

structure QuittingFinFourPaidCollisionAtom
    (reward : FinFourReward)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : Fin 4) (tail : Payoff (Fin 4)) where
  survivor : Finset (Fin 4)
  survivor_mem : survivor ∈ (Finset.univ.erase j).powerset.erase ∅
  mass : ℝ
  mass_eq : mass = quittingDeletionUnconditionalSurvivorMass
    reward profile stage j survivor
  mass_pos : 0 < mass
  increment : ℝ
  increment_eq : increment =
    quittingDeletionInsertionIncrement reward tail j survivor
  increment_pos : 0 < increment
  carrier_nonempty : (insert j survivor).Nonempty
  collision : 1 < (insert j survivor).card

structure QuittingFinFourPaidCollisionPacket
    (reward : FinFourReward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : Fin 4) (tail : Payoff (Fin 4)) where
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_debt_pos : 0 < quittingTerminalSemanticDebtSum minimum
  atom : QuittingFinFourPaidCollisionAtom reward profile stage j tail

theorem quittingFinFourPaidCollisionAtom_stageMass_eq_mass
    (reward : FinFourReward) (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : Fin 4) (tail : Payoff (Fin 4))
    (atom : QuittingFinFourPaidCollisionAtom reward profile stage j tail) :
    quittingStageCoalitionMass reward profile stage
        ⟨insert j atom.survivor, atom.carrier_nonempty⟩ = atom.mass := by
  change quittingDeletionUnconditionalSurvivorMass reward profile stage j
    atom.survivor = atom.mass
  exact atom.mass_eq.symm

theorem exists_finFour_deletionNearCapPaidCollision
    (reward : FinFourReward) (j : Fin 4)
    {gamma epsilon delta : ℝ}
    (hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j) :
    ∃ data : FinFourDeletionNearCapData reward j epsilon delta gamma,
      ∃ atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)),
        (gamma - finFourDeletionSoloPremium reward j - delta) / 7 ≤
            atom.mass * atom.increment ∧
          atom.mass ≥
            (gamma - finFourDeletionSoloPremium reward j - delta) /
              (7 * finFourDeletionCollisionCap reward j) := by
  obtain ⟨data⟩ := exists_finFour_deletionNearCapData reward j hgamma hexploit hPi
    hepsilon hepsilon_lt hdelta hdelta_ltPi
  let tail : Payoff (Fin 4) := fun _ =>
    quittingRootSequencePureTimeTerminalValue reward
      (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)
  have hnever := finFourDeletionNearCapData_sigma_player_never reward j data
  have hsurvival := finFourDeletionNearCapData_survival_eq_liveMass reward j data
  have hroot := finFourDeletionNearCapData_tau_root_player_quits reward j data
  have hlive := finFourDeletionNearCapData_tau_source_liveMass_eq reward j data
  have hopponents := finFourDeletionNearCapData_tau_root_eq_source_off_player
    reward j data
  have hdecomp := quittingFinFourDeletion_gain_eq_stageMass_expansion
    reward data.sigma data.tau j data.t hnever data.tau_eq hlive hroot hopponents
      hsurvival
  have hresidual : 0 < gamma - finFourDeletionSoloPremium reward j - delta := by
    linarith [hPi, hdelta_ltPi]
  let solo := quittingStageCoalitionMass reward data.tau data.t
    (quittingSingletonTerminal j) * quittingDeletionInsertionIncrement reward tail j ∅
  let increment : Finset (Fin 4) → ℝ := quittingDeletionInsertionIncrement reward tail j
  let mass : Finset (Fin 4) → ℝ := fun S =>
    quittingStageCoalitionMass reward data.tau data.t
      ⟨insert j S, Finset.insert_nonempty j S⟩
  have hdecomp' : quittingTerminalPayoff reward data.tau j -
      quittingTerminalPayoff reward data.sigma j =
      solo + ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
        mass S * increment S := by
    simpa only [solo, mass, increment, tail] using hdecomp
  have hsolo : solo ≤ finFourDeletionSoloPremium reward j := by
    have hmass0 := quittingStageCoalitionMass_nonneg reward data.tau data.t
      (quittingSingletonTerminal j)
    have hmass1 := quittingStageCoalitionMass_singleton_le_one reward data.tau data.t j
    have hfloor : finFourDeletionFloor reward j ≤ tail j := by
      exact (finFourDeletionFloor_le_quittingContinueFloor reward j).trans
        (quittingFinFourDeletion_continuationTail_ge_floor reward
          (quittingProfileLiveRoot reward data.sigma) j (data.t + 1))
    have hbound := quittingFinFourDeletion_soloTerm_le_floor_premium reward
      tail j (finFourDeletionFloor reward j)
      (quittingStageCoalitionMass reward data.tau data.t
        (quittingSingletonTerminal j)) hmass0 hmass1 hfloor
    dsimp [solo]
    rw [quittingDeletionInsertionIncrement, quittingEndpointInsertionToggle_empty]
    simpa [finFourDeletionSoloPremium] using hbound
  have hincrement : ∀ S ∈ (Finset.univ.erase j).powerset.erase ∅,
      increment S ≤ finFourDeletionCollisionCap reward j := by
    intro S hS
    exact quittingDeletionInsertionIncrement_le_finFourDeletionCollisionCap
      reward tail j hS
  have hgain : gamma - delta ≤ quittingTerminalPayoff reward data.tau j -
      quittingTerminalPayoff reward data.sigma j := data.near_cap_gain
  have hcap : 0 < finFourDeletionCollisionCap reward j := by
    by_contra hcap
    have hcap' : finFourDeletionCollisionCap reward j = 0 := by
      exact le_antisymm (le_of_not_gt hcap) (by
        unfold finFourDeletionCollisionCap
        exact le_max_left _ _)
    have hnonpos : ∀ S ∈ (Finset.univ.erase j).powerset.erase ∅,
        increment S ≤ 0 := by
      intro S hS
      have hbound := hincrement S hS
      rw [hcap'] at hbound
      exact hbound
    have hsum : ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
        mass S * increment S ≤ 0 := by
      apply Finset.sum_nonpos
      intro S hS
      exact mul_nonpos_of_nonneg_of_nonpos
        (quittingStageCoalitionMass_nonneg reward data.tau data.t
          ⟨insert j S, Finset.insert_nonempty j S⟩) (hnonpos S hS)
    linarith [hPi, hdelta_ltPi, hgain, hdecomp', hsolo, hsum]
  let coalitions := (Finset.univ.erase j).powerset.erase ∅
  have hcard : coalitions.card = 7 := by
    dsimp [coalitions]
    exact quittingDeletionSurvivorCoalition_card_finFour j
  have hmass : ∀ S ∈ coalitions, 0 ≤ mass S := by
    intro S hS
    exact quittingStageCoalitionMass_nonneg reward data.tau data.t _
  obtain ⟨S, hS, hprod, hinc, hlower⟩ :=
    Math.FinitePaidCollision.exists_paid_collision_of_gain_ge_sub_with_product coalitions
      mass increment gamma delta (finFourDeletionSoloPremium reward j) solo
      (quittingTerminalPayoff reward data.tau j -
        quittingTerminalPayoff reward data.sigma j)
      (finFourDeletionCollisionCap reward j) hcard hmass hgain hsolo
      (by simpa only [coalitions, mass, increment] using hdecomp') hresidual
      (by simpa only [coalitions, increment] using hincrement) hcap
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp hS).1
  have hjnot : j ∉ S := by
    intro hj
    exact (Finset.mem_erase.mp (Finset.mem_powerset.mp
      (Finset.mem_erase.mp hS).2 hj)).1 rfl
  have hcollision : 1 < (insert j S).card := by
    rw [Finset.card_insert_of_notMem hjnot]
    have hcardS : 0 < S.card := Finset.card_pos.mpr hSne
    omega
  have hmassPos : 0 < mass S := by
    nlinarith [hprod, hinc]
  let atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j tail :=
    { survivor := S
      survivor_mem := hS
      mass := mass S
      mass_eq := rfl
      mass_pos := hmassPos
      increment := increment S
      increment_eq := rfl
      increment_pos := hinc
      carrier_nonempty := Finset.insert_nonempty j S
      collision := hcollision }
  refine ⟨data, atom, ?_, ?_⟩
  · simpa only [atom] using hprod
  · simpa only [atom] using hlower

theorem finFourDeletionNearCap_collisionCap_pos
    (reward : FinFourReward) (j : Fin 4)
    {gamma epsilon delta : ℝ}
    (hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j) :
    0 < finFourDeletionCollisionCap reward j := by
  obtain ⟨data, atom, _hproduct, _hmass⟩ :=
    exists_finFour_deletionNearCapPaidCollision
    reward j hgamma hexploit hPi hepsilon hepsilon_lt hdelta hdelta_ltPi
  have hcap := quittingDeletionInsertionIncrement_le_finFourDeletionCollisionCap
    reward (fun _ => quittingRootSequencePureTimeTerminalValue reward
      (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)) j
      (S := atom.survivor) atom.survivor_mem
  rw [← atom.increment_eq] at hcap
  linarith [atom.increment_pos]

theorem finFourDeletionNearCap_collisionDispatch
    (reward : FinFourReward) (j : Fin 4)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    {gamma epsilon delta : ℝ}
    (hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j)
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_debt : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ data : FinFourDeletionNearCapData reward j epsilon delta gamma,
      ∃ atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)),
        let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
          ⟨insert j atom.survivor, atom.carrier_nonempty⟩
        let minimumDebt := quittingTerminalSemanticDebtSum minimum
        let stageMass := quittingStageCoalitionMass reward data.tau data.t terminal
        let liveMass := quittingLiveMass reward data.tau data.t
        let excess := quittingSpineDebtExcess reward data.tau minimumDebt (data.t + 1)
        liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
          ∃ who,
            let tail := quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward data.tau (data.t + 1))
            let root := quittingProfileLiveRoot reward data.tau data.t
            let action := quittingRootBestEndpointAction reward tail.1 root who
            let targetProfile := Function.update data.tau who
              (quittingStagePureEndpointBehaviorDeviation
                reward data.tau who data.t action)
            let gain := quittingTerminalPayoff reward targetProfile who -
              quittingTerminalPayoff reward data.tau who
            gain = liveMass * quittingRootCoordinateNashDefect reward tail.1 root who ∧
              0 < gain ∧ stageMass * minimumDebt / 8 ≤ gain := by
  obtain ⟨data, atom, _hproduct, _hmass⟩ :=
    exists_finFour_deletionNearCapPaidCollision
    reward j hgamma hexploit hPi hepsilon hepsilon_lt hdelta hdelta_ltPi
  let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨insert j atom.survivor, atom.carrier_nonempty⟩
  have hmass : 0 < quittingStageCoalitionMass reward data.tau data.t terminal := by
    dsimp [terminal]
    change 0 < quittingDeletionUnconditionalSurvivorMass reward data.tau data.t
      j atom.survivor
    rw [← atom.mass_eq]
    exact atom.mass_pos
  have hresult := quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain
    reward minimum data.tau data.t terminal hminimum hminimum_le hminimum_debt
      atom.collision hmass
  refine ⟨data, atom, ?_⟩
  dsimp [terminal]
  simpa only using hresult

/-! The consumer's positive endpoint mover is distinct from the deleted player.

The point requiring a separate lemma is that the consumer sees the updated root
`tau`, whereas the deletion expansion is computed at the source root `sigma`.
The continuation coordinate is transported by the literal all-Continue/root
shift identity, and the other root coordinates are unchanged. -/
theorem finFourDeletionNearCap_collisionResult_distinct
    (reward : FinFourReward) (j : Fin 4)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    {gamma epsilon delta : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma)
    (atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)))
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_debt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j) :
    let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
      ⟨insert j atom.survivor, atom.carrier_nonempty⟩
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward data.tau data.t terminal
    let liveMass := quittingLiveMass reward data.tau data.t
    let excess := quittingSpineDebtExcess reward data.tau minimumDebt (data.t + 1)
    liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
      ∃ who,
        let tail := quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward data.tau (data.t + 1))
        let root := quittingProfileLiveRoot reward data.tau data.t
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let targetProfile := Function.update data.tau who
          (quittingStagePureEndpointBehaviorDeviation
            reward data.tau who data.t action)
        let gain := quittingTerminalPayoff reward targetProfile who -
          quittingTerminalPayoff reward data.tau who
        gain = liveMass * quittingRootCoordinateNashDefect reward tail.1 root who ∧
          0 < gain ∧ stageMass * minimumDebt / 8 ≤ gain ∧ who ≠ j := by
  let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨insert j atom.survivor, atom.carrier_nonempty⟩
  have hmass : 0 < quittingStageCoalitionMass reward data.tau data.t terminal := by
    dsimp [terminal]
    change 0 < quittingDeletionUnconditionalSurvivorMass reward data.tau data.t
      j atom.survivor
    rw [← atom.mass_eq]
    exact atom.mass_pos
  have hresult := quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain
    reward minimum data.tau data.t terminal hminimum hminimum_le hminimum_debt
      atom.collision hmass
  have htail := finFourDeletionNearCapData_consumerTail_coord_eq_neverTail
    reward j data
  have hroot := finFourDeletionNearCapData_tau_root_player_quits reward j data
  have hoff := finFourDeletionNearCapData_tau_root_eq_source_off_player reward j data
  have hcontinuation := quittingRootEndpointDifference_continuation_congr
    reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1))
      (quittingProfileLiveRoot reward data.tau data.t) j htail
  have hoffEndpoint := quittingRootEndpointDifference_eq_of_eq_off_self
    reward
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1))
      (quittingProfileLiveRoot reward data.tau data.t)
      (quittingProfileLiveRoot reward data.sigma data.t) j hoff
  have hendpoint : quittingRootEndpointDifference reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
      (quittingProfileLiveRoot reward data.tau data.t) j =
      quittingRootEndpointDifference reward
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1))
        (quittingProfileLiveRoot reward data.sigma data.t) j :=
    hcontinuation.trans hoffEndpoint
  have hnever := finFourDeletionNearCapData_sigma_player_never reward j data
  have hsurvival := finFourDeletionNearCapData_survival_eq_liveMass reward j data
  have hfactor : quittingTerminalPayoff reward data.tau j -
      quittingTerminalPayoff reward data.sigma j =
      quittingLiveMass reward data.sigma data.t *
        quittingRootEndpointDifference reward
          (fun _ => quittingRootSequencePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1))
          (quittingProfileLiveRoot reward data.sigma data.t) j := by
    calc
      quittingTerminalPayoff reward data.tau j -
          quittingTerminalPayoff reward data.sigma j =
        quittingTerminalPayoff reward
            (Function.update data.sigma j
              (quittingPureTimeBehaviorStrategy reward j (some data.t))) j -
          quittingTerminalPayoff reward data.sigma j := by
            rw [data.payoff_update]
      _ = _ := quittingFinFourDeletion_pureTimeGain_eq_liveMass_mul_endpoint
        reward data.sigma j data.t hnever hsurvival
  have hgainPos : 0 < quittingTerminalPayoff reward data.tau j -
      quittingTerminalPayoff reward data.sigma j := by
    have hPi_nonneg : 0 ≤ finFourDeletionSoloPremium reward j := le_max_left _ _
    linarith [data.near_cap_gain, hdelta_ltPi]
  have hsourceEndpointPos : 0 < quittingRootEndpointDifference reward
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1))
      (quittingProfileLiveRoot reward data.sigma data.t) j := by
    have hnonneg := quittingLiveMass_nonneg reward data.sigma data.t
    nlinarith [hfactor, hgainPos]
  have hconsumerEndpointPos : 0 < quittingRootEndpointDifference reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
      (quittingProfileLiveRoot reward data.tau data.t) j := by
    rw [hendpoint]
    exact hsourceEndpointPos
  dsimp [terminal] at hresult ⊢
  rcases hresult with hescape | ⟨who, hgain, hgainPos', hbound⟩
  · exact Or.inl hescape
  · right
    refine ⟨who, hgain, hgainPos', hbound, ?_⟩
    have hlive := quittingLiveMass_nonneg reward data.tau data.t
    have hdefectNonneg := quittingRootCoordinateNashDefect_nonneg reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
      (quittingProfileLiveRoot reward data.tau data.t) who
    have hdefectPos : 0 < quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
        (quittingProfileLiveRoot reward data.tau data.t) who := by
      nlinarith [hgain, hgainPos']
    intro hwho
    subst who
    have hjzero : quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
        (quittingProfileLiveRoot reward data.tau data.t) j = 0 := by
      rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
      have hjtrue :
          (quittingProfileLiveRoot reward data.tau data.t j true).toReal = 1 := by
        rw [hroot]
        simp
      have hjfalse :
          (quittingProfileLiveRoot reward data.tau data.t j false).toReal = 0 := by
        rw [hroot]
        simp
      rw [hjtrue, hjfalse]
      simp [le_of_lt hconsumerEndpointPos]
    rw [hjzero] at hdefectPos
    linarith

theorem finFourDeletionNearCap_collisionDispatch_distinct
    (reward : FinFourReward) (j : Fin 4)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    {gamma epsilon delta : ℝ}
    (hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j)
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_debt : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ data : FinFourDeletionNearCapData reward j epsilon delta gamma,
      ∃ atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)),
        let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
          ⟨insert j atom.survivor, atom.carrier_nonempty⟩
        let minimumDebt := quittingTerminalSemanticDebtSum minimum
        let stageMass := quittingStageCoalitionMass reward data.tau data.t terminal
        let liveMass := quittingLiveMass reward data.tau data.t
        let excess := quittingSpineDebtExcess reward data.tau minimumDebt (data.t + 1)
        liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
          ∃ who,
            let tail := quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward data.tau (data.t + 1))
            let root := quittingProfileLiveRoot reward data.tau data.t
            let action := quittingRootBestEndpointAction reward tail.1 root who
            let targetProfile := Function.update data.tau who
              (quittingStagePureEndpointBehaviorDeviation
                reward data.tau who data.t action)
            let gain := quittingTerminalPayoff reward targetProfile who -
              quittingTerminalPayoff reward data.tau who
            gain = liveMass * quittingRootCoordinateNashDefect reward tail.1 root who ∧
              0 < gain ∧ stageMass * minimumDebt / 8 ≤ gain ∧ who ≠ j := by
  obtain ⟨data, atom, _hproduct, _hmass⟩ :=
    exists_finFour_deletionNearCapPaidCollision
    reward j hgamma hexploit hPi hepsilon hepsilon_lt hdelta hdelta_ltPi
  refine ⟨data, atom, ?_⟩
  exact finFourDeletionNearCap_collisionResult_distinct reward j minimum data atom
    hminimum hminimum_le hminimum_debt hdelta_ltPi

theorem finFourDeletionNearCap_tailFormula_six
    (reward : FinFourReward) (j : Fin 4)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    {gamma epsilon delta : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma)
    (atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)))
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    {residual cap : ℝ}
    (hdebt : 0 ≤ quittingTerminalSemanticDebtSum minimum)
    (hcap : 0 < cap)
    (hmass : residual / (7 * cap) ≤ atom.mass)
    (htail : quittingLiveMass reward data.tau data.t *
        quittingSpineDebtExcess reward data.tau
            (quittingTerminalSemanticDebtSum minimum) (data.t + 1) ≥
        quittingStageCoalitionMass reward data.tau data.t
          ⟨insert j atom.survivor, atom.carrier_nonempty⟩ *
            quittingTerminalSemanticDebtSum minimum / 2) :
    residual * quittingTerminalSemanticDebtSum minimum / (14 * cap) ≤
      quittingSpineDebtExcess reward data.tau
        (quittingTerminalSemanticDebtSum minimum) (data.t + 1) := by
  have hstage := quittingFinFourPaidCollisionAtom_stageMass_eq_mass
    reward data.tau data.t j _ atom
  have htail' : atom.mass * quittingTerminalSemanticDebtSum minimum / 2 ≤
      quittingLiveMass reward data.tau data.t *
        quittingSpineDebtExcess reward data.tau
          (quittingTerminalSemanticDebtSum minimum) (data.t + 1) := by
    rw [← hstage]
    exact htail
  have hscale := Math.FinitePaidCollision.tail_scale_of_paid_collision
    hcap hdebt hmass htail'
  have hexcess := quittingSpineDebtExcess_nonneg_of_minimum reward data.tau
    minimum hminimum_le (data.t + 1)
  have hlive := quittingLiveMass_le_one reward data.tau data.t
  have hle : quittingLiveMass reward data.tau data.t *
      quittingSpineDebtExcess reward data.tau
        (quittingTerminalSemanticDebtSum minimum) (data.t + 1) ≤
        quittingSpineDebtExcess reward data.tau
          (quittingTerminalSemanticDebtSum minimum) (data.t + 1) := by
    nlinarith
  exact hscale.trans hle

theorem finFourDeletionNearCap_collisionDispatch_distinct_with_bounds
    (reward : FinFourReward) (j : Fin 4)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    {gamma epsilon delta : ℝ}
    (hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j)
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ data : FinFourDeletionNearCapData reward j epsilon delta gamma,
      ∃ atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)),
        (gamma - finFourDeletionSoloPremium reward j - delta) / 7 ≤
            atom.mass * atom.increment ∧
          atom.mass ≥
            (gamma - finFourDeletionSoloPremium reward j - delta) /
              (7 * finFourDeletionCollisionCap reward j) ∧
        let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
          ⟨insert j atom.survivor, atom.carrier_nonempty⟩
        let minimumDebt := quittingTerminalSemanticDebtSum minimum
        let stageMass := quittingStageCoalitionMass reward data.tau data.t terminal
        let liveMass := quittingLiveMass reward data.tau data.t
        let excess := quittingSpineDebtExcess reward data.tau minimumDebt (data.t + 1)
        liveMass * excess ≥ stageMass * minimumDebt / 2 ∧
          (gamma - finFourDeletionSoloPremium reward j - delta) * minimumDebt /
              (14 * finFourDeletionCollisionCap reward j) ≤ excess ∨
          ∃ who,
            let tail := quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward data.tau (data.t + 1))
            let root := quittingProfileLiveRoot reward data.tau data.t
            let action := quittingRootBestEndpointAction reward tail.1 root who
            let targetProfile := Function.update data.tau who
              (quittingStagePureEndpointBehaviorDeviation
                reward data.tau who data.t action)
            let gain := quittingTerminalPayoff reward targetProfile who -
              quittingTerminalPayoff reward data.tau who
            gain = liveMass * quittingRootCoordinateNashDefect reward tail.1 root who ∧
              0 < gain ∧ stageMass * minimumDebt / 8 ≤ gain ∧
              (gamma - finFourDeletionSoloPremium reward j - delta) * minimumDebt /
                  (56 * finFourDeletionCollisionCap reward j) ≤ gain ∧
              who ≠ j ∧
              let source := quittingTerminalSemanticPair reward data.tau
              let target := quittingTerminalSemanticPair reward targetProfile
              let routed := quittingPureEndpointRoutedCoalition terminal.val who action
              target ∈ quittingTerminalSemanticCarrier reward ∧
                quittingTerminalSemanticDebt target who =
                  quittingTerminalSemanticDebt source who - gain ∧
                quittingTerminalDebt reward targetProfile who =
                  quittingTerminalDebt reward data.tau who - gain ∧
                ∃ hrouted : routed.Nonempty,
                  stageMass ≤ quittingStageCoalitionMass reward targetProfile data.t
                    ⟨routed, hrouted⟩ := by
  obtain ⟨data, atom, hproduct, hmass⟩ :=
    exists_finFour_deletionNearCapPaidCollision
    reward j hgamma hexploit hPi hepsilon hepsilon_lt hdelta hdelta_ltPi
  have hminimum_debt := terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier
    reward minimum hexploit hminimum
  have hdebt : 0 < quittingTerminalSemanticDebtSum minimum :=
    lt_of_lt_of_le hgamma hminimum_debt
  have hcap := finFourDeletionNearCap_collisionCap_pos reward j hgamma hexploit hPi
    hepsilon hepsilon_lt hdelta hdelta_ltPi
  have hresult := finFourDeletionNearCap_collisionResult_distinct reward j minimum data atom
    hminimum hminimum_le hdebt hdelta_ltPi
  refine ⟨data, atom, hproduct, hmass, ?_⟩
  dsimp at hresult ⊢
  rcases hresult with hescape | ⟨who, hgain, hgainPos, hbound, hwho⟩
  · left
    refine ⟨hescape, ?_⟩
    exact finFourDeletionNearCap_tailFormula_six reward j minimum data atom
      hminimum_le (le_of_lt hdebt)
      (finFourDeletionNearCap_collisionCap_pos reward j hgamma hexploit hPi
        hepsilon hepsilon_lt hdelta hdelta_ltPi)
      hmass hescape
  · right
    refine ⟨who, hgain, hgainPos, hbound, ?_, hwho, ?_⟩
    have hstageAtom : quittingStageCoalitionMass reward data.tau data.t
        ⟨insert j atom.survivor, atom.carrier_nonempty⟩ = atom.mass := by
      change quittingDeletionUnconditionalSurvivorMass reward data.tau data.t
        j atom.survivor = atom.mass
      exact atom.mass_eq.symm
    rw [hstageAtom] at hbound
    have hexact := Math.FinitePaidCollision.endpoint_scale_of_paid_collision hcap
      (le_of_lt hdebt) hmass hbound
    exact hexact
    let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
      ⟨insert j atom.survivor, atom.carrier_nonempty⟩
    let action := quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward data.tau (data.t + 1))).1
      (quittingProfileLiveRoot reward data.tau data.t) who
    let targetProfile := Function.update data.tau who
      (quittingStagePureEndpointBehaviorDeviation
        reward data.tau who data.t action)
    let source := quittingTerminalSemanticPair reward data.tau
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward data.tau who
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    have htarget : target ∈ quittingTerminalSemanticCarrier reward := by
      exact quittingTerminalSemanticPair_mem_carrier reward targetProfile
    have hmover : quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain := by
      simpa only [target, source, gain] using
        (quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain
          reward data.tau who data.t)
    have hliteral : quittingTerminalDebt reward targetProfile who =
        quittingTerminalDebt reward data.tau who - gain := by
      change quittingBestReplyValue reward targetProfile who -
          quittingTerminalPayoff reward targetProfile who =
        quittingBestReplyValue reward data.tau who -
          quittingTerminalPayoff reward data.tau who - gain
      rw [← quittingContinuationBestResponseValue_eq_bestReplyValue reward
          targetProfile who,
        ← quittingContinuationBestResponseValue_eq_bestReplyValue reward
          data.tau who]
      exact hmover
    have hrouting := quittingStageCoalitionMass_le_stagePureEndpointRouted
      reward data.tau who data.t terminal action atom.collision
    have hrouting' : ∃ hrouted : routed.Nonempty,
        quittingStageCoalitionMass reward data.tau data.t terminal ≤
          quittingStageCoalitionMass reward targetProfile data.t
            ⟨routed, hrouted⟩ := by
      simpa only [action, targetProfile, routed, terminal] using hrouting
    simpa only [action, targetProfile, source, target, gain, routed, terminal,
      quittingTerminalDebt] using
      (show target ∈ quittingTerminalSemanticCarrier reward ∧
          quittingTerminalSemanticDebt target who =
            quittingTerminalSemanticDebt source who - gain ∧
          quittingTerminalDebt reward targetProfile who =
            quittingTerminalDebt reward data.tau who - gain ∧
          ∃ hrouted : routed.Nonempty,
            quittingStageCoalitionMass reward data.tau data.t terminal ≤
              quittingStageCoalitionMass reward targetProfile data.t
                ⟨routed, hrouted⟩ from ⟨htarget, hmover, hliteral, hrouting'⟩)

theorem exists_quittingFinFourPaidCollisionPacket
    (reward : FinFourReward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : Fin 4) (tail : Payoff (Fin 4))
    (gamma delta Pi solo gain cap : ℝ)
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_debt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hgain : gamma - delta ≤ gain)
    (hsolo : solo ≤ Pi)
    (hdecomp : gain = solo +
      ∑ S ∈ (Finset.univ.erase j).powerset.erase ∅,
        quittingStageCoalitionMass reward profile stage
          ⟨insert j S, Finset.insert_nonempty j S⟩ *
          quittingDeletionInsertionIncrement reward tail j S)
    (hresidual : 0 < gamma - Pi - delta)
    (hincrement : ∀ S ∈ (Finset.univ.erase j).powerset.erase ∅,
      quittingDeletionInsertionIncrement reward tail j S ≤ cap)
    (hcap : 0 < cap) :
    ∃ packet : QuittingFinFourPaidCollisionPacket reward minimum profile stage j tail,
      (gamma - Pi - delta) / 7 ≤ packet.atom.mass * packet.atom.increment ∧
        (gamma - Pi - delta) / (7 * cap) ≤ packet.atom.mass := by
  let coalitions := (Finset.univ.erase j).powerset.erase ∅
  let mass : Finset (Fin 4) → ℝ := fun S =>
    quittingStageCoalitionMass reward profile stage
      ⟨insert j S, Finset.insert_nonempty j S⟩
  let increment : Finset (Fin 4) → ℝ :=
    quittingDeletionInsertionIncrement reward tail j
  have hcard : coalitions.card = 7 := by
    dsimp [coalitions]
    exact quittingDeletionSurvivorCoalition_card_finFour j
  have hmass : ∀ S ∈ coalitions, 0 ≤ mass S := by
    intro S hS
    exact quittingStageCoalitionMass_nonneg reward profile stage _
  have hsum : gain = solo + ∑ S ∈ coalitions, mass S * increment S := by
    simpa only [coalitions, mass, increment] using hdecomp
  obtain ⟨S, hS, hprod, hinc, hlower⟩ :=
    Math.FinitePaidCollision.exists_paid_collision_of_card_seven_with_product coalitions
      mass increment (gamma - Pi - delta) cap hcard hmass hresidual
      (by linarith [hgain, hsolo, hsum]) hincrement hcap
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp hS).1
  have hjnot : j ∉ S := by
    intro hj
    exact (Finset.mem_erase.mp (Finset.mem_powerset.mp
      (Finset.mem_erase.mp hS).2 hj)).1 rfl
  have hcardCollision : 1 < (insert j S).card := by
    rw [Finset.card_insert_of_notMem hjnot]
    have hcardS : 0 < S.card := Finset.card_pos.mpr hSne
    omega
  have hmassPos : 0 < mass S := by
    nlinarith [hprod, hinc]
  let atom : QuittingFinFourPaidCollisionAtom reward profile stage j tail :=
    { survivor := S
      survivor_mem := hS
      mass := mass S
      mass_eq := rfl
      mass_pos := hmassPos
      increment := increment S
      increment_eq := rfl
      increment_pos := hinc
      carrier_nonempty := Finset.insert_nonempty j S
      collision := hcardCollision }
  let packet : QuittingFinFourPaidCollisionPacket reward minimum profile stage j tail :=
    { minimum_mem := hminimum
      minimum_le := hminimum_le
      minimum_debt_pos := hminimum_debt
      atom := atom }
  refine ⟨packet, ?_, ?_⟩
  · simpa only [packet, atom] using hprod
  · simpa only [packet, atom] using hlower

theorem quittingFinFourPaidCollisionAtom_carrier_contains_selected
    {reward : FinFourReward}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {j : Fin 4}
    (tail : Payoff (Fin 4))
    (atom : QuittingFinFourPaidCollisionAtom reward profile stage j tail) :
    j ∈ insert j atom.survivor := Finset.mem_insert_self j atom.survivor

theorem quittingRootCoordinateNashDefect_eq_zero_of_pureQuit
    (reward : FinFourReward) (tail : Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (j : Fin 4)
    (hroot : root j = PMF.pure true)
    (hendpoint : 0 ≤ quittingRootEndpointDifference reward tail root j) :
    quittingRootCoordinateNashDefect reward tail root j = 0 := by
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart]
  have hjtrue : (root j true).toReal = 1 := by
    rw [hroot]
    simp
  have hjfalse : (root j false).toReal = 0 := by
    rw [hroot]
    simp
  rw [hjtrue, hjfalse]
  simp [hendpoint]

theorem quittingRootCoordinateNashDefect_pos_player_ne_pureQuit
    (reward : FinFourReward) (tail : Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (j who : Fin 4)
    (hroot : root j = PMF.pure true)
    (hendpoint : 0 ≤ quittingRootEndpointDifference reward tail root j)
    (hpos : 0 < quittingRootCoordinateNashDefect reward tail root who) :
    who ≠ j := by
  intro heq
  subst who
  rw [quittingRootCoordinateNashDefect_eq_zero_of_pureQuit
    reward tail root j hroot hendpoint] at hpos
  linarith

theorem quittingFinFourPaidCollisionPacket_stageMass_pos
    (reward : FinFourReward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (j : Fin 4) (tail : Payoff (Fin 4))
    (packet : QuittingFinFourPaidCollisionPacket reward minimum profile stage j tail) :
    0 < quittingStageCoalitionMass reward profile stage
      ⟨insert j packet.atom.survivor, packet.atom.carrier_nonempty⟩ := by
  change 0 < quittingDeletionUnconditionalSurvivorMass reward profile stage j
    packet.atom.survivor
  rw [← packet.atom.mass_eq]
  exact packet.atom.mass_pos

theorem finFourDeletionNearCapPaidCollisionAtom_mass_eq_source_survival_mul_opponent
    (reward : FinFourReward) (j : Fin 4)
    {gamma epsilon delta : ℝ}
    (data : FinFourDeletionNearCapData reward j epsilon delta gamma)
    (atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1))) :
    atom.mass =
      quittingOpponentSurvivalWeight (quittingProfileLiveRoot reward data.sigma)
          j 0 data.t *
        quittingOpponentCoalitionMass
          (quittingProfileLiveRoot reward data.sigma data.t) j atom.survivor := by
  have hsubset : atom.survivor ⊆ Finset.univ.erase j := by
    exact Finset.mem_powerset.mp (Finset.mem_erase.mp atom.survivor_mem).2
  have hroot := finFourDeletionNearCapData_tau_root_player_quits reward j data
  have hstage := quittingDeletionUnconditionalSurvivorMass_eq_live_mul_opponentMass
    reward data.tau data.t j atom.survivor hsubset hroot
  have hoff := finFourDeletionNearCapData_tau_root_eq_source_off_player reward j data
  have hcoal : quittingOpponentCoalitionMass
      (quittingProfileLiveRoot reward data.tau data.t) j atom.survivor =
      quittingOpponentCoalitionMass
        (quittingProfileLiveRoot reward data.sigma data.t) j atom.survivor := by
    unfold quittingOpponentCoalitionMass
    congr 1
    · apply Finset.prod_congr rfl
      intro player hplayer
      rw [hoff player]
      exact (Finset.mem_erase.mp (hsubset hplayer)).1
    · apply Finset.prod_congr rfl
      intro player hplayer
      rw [hoff player]
      exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hplayer).1).1
  rw [atom.mass_eq]
  change quittingDeletionUnconditionalSurvivorMass reward data.tau data.t j
      atom.survivor = _
  rw [hstage, finFourDeletionNearCapData_tau_source_liveMass_eq reward j data, hcoal]
  rw [← finFourDeletionNearCapData_survival_eq_liveMass reward j data]

theorem finFourDeletionNearCap_collisionDispatch_distinct_of_gap
    (reward : FinFourReward) (j : Fin 4)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    {gamma epsilon delta : ℝ}
    (hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j)
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ data : FinFourDeletionNearCapData reward j epsilon delta gamma,
      ∃ atom : QuittingFinFourPaidCollisionAtom reward data.tau data.t j
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward data.sigma) j none (data.t + 1)),
        let terminal : {S : Finset (Fin 4) // S.Nonempty} :=
          ⟨insert j atom.survivor, atom.carrier_nonempty⟩
        let minimumDebt := quittingTerminalSemanticDebtSum minimum
        let stageMass := quittingStageCoalitionMass reward data.tau data.t terminal
        let liveMass := quittingLiveMass reward data.tau data.t
        let excess := quittingSpineDebtExcess reward data.tau minimumDebt (data.t + 1)
        liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
          ∃ who,
            let tail := quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward data.tau (data.t + 1))
            let root := quittingProfileLiveRoot reward data.tau data.t
            let action := quittingRootBestEndpointAction reward tail.1 root who
            let targetProfile := Function.update data.tau who
              (quittingStagePureEndpointBehaviorDeviation
                reward data.tau who data.t action)
            let gain := quittingTerminalPayoff reward targetProfile who -
              quittingTerminalPayoff reward data.tau who
            gain = liveMass * quittingRootCoordinateNashDefect reward tail.1 root who ∧
              0 < gain ∧ stageMass * minimumDebt / 8 ≤ gain ∧ who ≠ j := by
  have hminimum_debt := terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier
    reward minimum hexploit hminimum
  exact finFourDeletionNearCap_collisionDispatch_distinct reward j minimum hgamma hexploit
    hPi hepsilon hepsilon_lt hdelta hdelta_ltPi hminimum hminimum_le
    (lt_of_lt_of_le hgamma hminimum_debt)

theorem finFourDeletionNearCap_terminalDebt_eq_semanticDebt
    (reward : FinFourReward) (profile : (quittingGame reward).BehaviorProfile)
    (who : Fin 4) :
    quittingTerminalDebt reward profile who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  change quittingBestReplyValue reward profile who -
      quittingTerminalPayoff reward profile who =
    quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who
  rw [quittingContinuationBestResponseValue_eq_bestReplyValue]

end GameTheory
