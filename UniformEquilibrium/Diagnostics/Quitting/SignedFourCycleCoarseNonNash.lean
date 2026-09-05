import UniformEquilibrium.Diagnostics.Quitting.SignedFourCycleValueFixtures
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import UniformEquilibrium.Quitting.Stationary.MinMax

noncomputable section

namespace GameTheory.SignedFourCycleCoarseNonNash

open SignedFourCycleRawSpectralFixtures SignedFourCycleValueFixtures

def collisionOther
    (fallback : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (S : {S : Finset (Fin 4) // S.Nonempty}) : Payoff (Fin 4) :=
  if S.1 = {0, 1} then Function.update (fallback S) 0 3 else fallback S

abbrev reward fallback := daggerReward oneOwn (collisionOther fallback)
abbrev data fallback := daggerData oneOwn (collisionOther fallback)
abbrev tests fallback := daggerStrictTests oneOwn (collisionOther fallback)

def cycle (phase : Fin 4) : Fin 4 → PMF Bool :=
  quittingSoloStationaryRoot phase
    (quittingHazardCoin (1 / 2) (by norm_num) (by norm_num))

def profile fallback := quittingCyclicBehaviorProfile
  (reward fallback) cycle 0

theorem collision_reward_zero_one (fallback) :
    reward fallback ⟨{0, 1}, by simp⟩ 0 = 3 := by
  norm_num [reward, daggerReward, rewardWithSingletonMatrix, collisionOther]

theorem phaseHazard_eq_half (fallback) (phase : Fin 4) :
    (data fallback).phaseHazard (tests fallback) phase = 1 / 2 := by
  have h := dagger_normalized_hazards oneOwn (collisionOther fallback)
  rcases h with ⟨h0, h1, h2, h3⟩
  fin_cases phase <;>
    simp only [SignedFourCycleSingletonData.phaseHazard] <;> assumption

theorem coarse_policy (fallback) (phase : Fin 4) :
    (data fallback).coarseValue (tests fallback) phase =
      quittingRootSuccessorPayoff (reward fallback)
        ((data fallback).coarseValue (tests fallback) (finRotate 4 phase))
        (cycle phase) := by
  unfold cycle
  rw [quittingRootSuccessorPayoff_solo]
  have h := (data fallback).coarse_bellman (tests fallback) phase
  rw [phaseHazard_eq_half] at h
  rw [h]
  funext who
  simp [quittingSingletonArcPayoff]

theorem cycle_contracts (who : Fin 4) :
    (∏ phase : Fin 4,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1 := by
  fin_cases who <;>
    simp [cycle, Fin.prod_univ_succ,
      quittingStationaryFixedOpponentsContinueMass_solo_owner,
      quittingStationaryFixedOpponentsContinueMass_solo_other] <;> norm_num

theorem profile_payoff_zero (fallback) :
    quittingTerminalPayoff (reward fallback) (profile fallback) 0 = 1 := by
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
    (reward fallback) cycle ((data fallback).coarseValue (tests fallback))
    (coarse_policy fallback) cycle_contracts
  have hcoarse := dagger_coarse_values (collisionOther fallback)
  change quittingCyclicTerminalValue (reward fallback) cycle 0 0 = 1
  rw [← congrFun (congrFun hvalue 0) 0, hcoarse]
  rfl

theorem delayed_deviation_payoff (fallback) :
    quittingTerminalPayoff (reward fallback)
        (Function.update (profile fallback) 0
          (quittingPureTimeBehaviorStrategy (reward fallback) 0 (some 1))) 0 = 2 := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  rw [quittingRootSequencePureTimeTerminalValue_some_add
    (reward fallback) (quittingProfileLiveRoot (reward fallback) (profile fallback))
      0 0 1]
  simp only [profile, quittingProfileLiveRoot_cyclicBehaviorProfile, zero_add,
    quittingLiveLedgerAccum, Finset.sum_range_one,
    quittingOpponentSurvivalWeight, Finset.prod_range_one]
  simp only [Finset.prod_range_zero, one_mul]
  simp [quittingCyclicOrbit]
  change quittingStationaryFixedOpponentsContinueReward (reward fallback)
      (cycle 0) 0 +
      quittingStationaryFixedOpponentsContinueMass (cycle 0) 0 *
      quittingStationaryFixedOpponentsQuitValue (reward fallback) (cycle 1) 0 = 2
  unfold cycle
  rw [quittingStationaryFixedOpponentsContinueReward_solo_owner]
  rw [quittingStationaryFixedOpponentsContinueMass_solo_owner]
  rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
    (reward fallback) (by decide : (0 : Fin 4) ≠ 1)]
  have hpair : ({1, 0} : Finset (Fin 4)) = {0, 1} := by decide
  norm_num [cycle, quittingSoloReward, quittingSingletonCollisionReward,
    reward, daggerReward, rewardWithSingletonMatrix, collisionOther, oneOwn,
    QuittingLCPClassification.SignedFourCycleMatrixFixtures.gammaDagger, hpair]

theorem coarse_profile_not_exactNash (fallback) :
    ¬(quittingGame (reward fallback)).IsεAsymptoticNash
      (quittingTerminalPayoff (reward fallback)) 0 (profile fallback) := by
  intro hnash
  have hcap := hnash 0
    (quittingPureTimeBehaviorStrategy (reward fallback) 0 (some 1))
  rw [delayed_deviation_payoff, profile_payoff_zero] at hcap
  norm_num at hcap

end GameTheory.SignedFourCycleCoarseNonNash
