/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Regression.FinFivePhaseSeamAtomFloor
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Punishment.CoalitionLock
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.TargetTail.FiniteChainTerminalCompiler

/-!
# Full five-face source provenance does not remove a phase--seam crossing

This is the stronger exact rational regression.  Its five phase roots have
mass-`1 / 2` nonempty atoms and literal quiet-face provenance.  Each face is
backed by a two-date exact terminal Nash profile of the corresponding
deleted-player game, and the quietly lifted omitted player has a strictly
positive immediate-Quit gap.  Nevertheless the player-zero scalar rows are
incompatible with a closing seam below `31 / 32`.

The ambient all-Quit profile is an exact terminal Nash equilibrium, so the
table has zero minimum terminal semantic debt.  Thus the regression separates
the local face-source interface only; it does not realize a global
positive-minimum counterexample.
-/

noncomputable section

namespace GameTheory
namespace FinFiveFullFaceSourcePhaseSeam

open Math.Probability Set QuittingSureSetOwnerRepair

abbrev Player := FinFivePhaseSeamAtomFloor.Player
abbrev phaseQuitter := FinFivePhaseSeamAtomFloor.phaseQuitter
abbrev halfCoin := FinFivePhaseSeamAtomFloor.halfCoin
abbrev phaseRoot := FinFivePhaseSeamAtomFloor.phaseRoot

/-- The strengthened literal reward table, extended to the empty coalition. -/
def weight (coalition : Finset Player) (who : Player) : ℝ :=
  if who = 0 then
    if coalition = {0, 1} then 1
    else if coalition = {0, 2} then 1 / 16
    else if coalition = {0, 3} ∨ coalition = {0, 4} then -1
    else if coalition = Finset.univ.erase 3 then 1 / 16
    else if coalition = Finset.univ.erase 4 then 1
    else 0
  else if coalition = {who} ∨
      (coalition.card = 4 ∧ who ∈ coalition) then 1
  else 0

/-- The reward table on nonempty quitting coalitions. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  rewardOfWeight weight

@[simp] theorem weightOfReward_eq (coalition : Finset Player)
    (hcoalition : coalition.Nonempty) (who : Player) :
    weightOfReward reward coalition who = weight coalition who := by
  exact weightOfReward_rewardOfWeight weight coalition hcoalition who

theorem phaseRoot_owner_quiet (phase : Player) :
    phaseRoot phase phase = PMF.pure false :=
  FinFivePhaseSeamAtomFloor.phaseRoot_owner_quiet phase

theorem phaseRoot_singletonAtomMass (phase : Player) :
    quittingRootCoalitionMass (phaseRoot phase) {phaseQuitter phase} =
      (1 / 2 : ℝ) :=
  FinFivePhaseSeamAtomFloor.phaseRoot_singletonAtomMass phase

theorem phaseRoot_singletonAtom_excludes_owner (phase : Player) :
    phase ∉ ({phaseQuitter phase} : Finset Player) :=
  FinFivePhaseSeamAtomFloor.phaseRoot_singletonAtom_excludes_owner phase

@[simp] theorem singletonWeight_phaseQuitter_zero (phase : Player) :
    weight {phaseQuitter phase} 0 = 0 := by
  fin_cases phase <;> simp +decide [weight]

/-- Player zero again sees the exact scalar Bellman map `z |-> z / 2`. -/
theorem playerZero_successorPayoff (phase : Player) (tail : Payoff Player) :
    quittingRootSuccessorPayoff reward tail (phaseRoot phase) 0 =
      tail 0 / 2 := by
  change quittingRootSuccessorPayoff reward tail
      (quittingSoloStationaryRoot (phaseQuitter phase) halfCoin) 0 =
    tail 0 / 2
  rw [congrFun
    (quittingRootSuccessorPayoff_solo reward (phaseQuitter phase) halfCoin tail) 0]
  simp only [FinFivePhaseSeamAtomFloor.halfCoin,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  change (1 / 2 : ℝ) * weight {phaseQuitter phase} 0 +
      (1 - 1 / 2 : ℝ) * tail 0 = tail 0 / 2
  rw [singletonWeight_phaseQuitter_zero]
  ring

/-- Propagated player-zero values `v_0,...,v_4`. -/
def phaseValue (x : ℝ) : Player → ℝ :=
  ![x, x / 16, x / 8, x / 4, x / 2]

/-- Successor values read by phase roots zero through four. -/
def phaseTail (x : ℝ) : Player → ℝ :=
  ![x / 16, x / 8, x / 4, x / 2, x]

/-- Exact nonseam Bellman propagation survives the strengthened table. -/
theorem playerZero_exact_nonseam_propagation (x : ℝ) (phase : Player)
    (hphase : phase ≠ 0) :
    phaseValue x phase =
      quittingRootSuccessorPayoff reward (fun _ => phaseTail x phase)
        (phaseRoot phase) 0 := by
  rw [playerZero_successorPayoff]
  fin_cases phase <;> simp_all [phaseValue, phaseTail] <;> ring

/-- The strengthened word has the same closing map `x / 32`. -/
theorem playerZero_closingMap (x : ℝ) :
    quittingRootSuccessorPayoff reward (fun _ => phaseTail x 0)
        (phaseRoot 0) 0 = x / 32 := by
  rw [playerZero_successorPayoff]
  simp [phaseTail]
  ring

/-- Player zero's collision reward at each phase. -/
def phaseCollisionValue : Player → ℝ := ![1 / 16, -1, -1, 1 / 16, 1]

@[simp] theorem playerZero_pairWeight (phase : Player) :
    weight {0, phaseQuitter phase} 0 = phaseCollisionValue phase := by
  fin_cases phase <;> simp +decide [phaseCollisionValue, weight]

/-- The five supported Continue rows reduce to the advertised rational
one-variable affine rows. -/
theorem playerZero_endpointDifference (x : ℝ) (phase : Player) :
    quittingRootEndpointDifference reward (fun _ => phaseTail x phase)
        (phaseRoot phase) 0 =
      (phaseCollisionValue phase - phaseTail x phase) / 2 := by
  have hne : (0 : Player) ≠ phaseQuitter phase := by
    exact Ne.symm (FinFivePhaseSeamAtomFloor.phaseQuitter_ne_zero phase)
  change quittingRootEndpointDifference reward (fun _ => phaseTail x phase)
      (quittingSoloStationaryRoot (phaseQuitter phase) halfCoin) 0 = _
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne]
  have hsoloZero : quittingSoloReward reward 0 0 = 0 := by
    change weight ({0} : Finset Player) 0 = 0
    simp +decide [weight]
  have hsoloQuitter : quittingSoloReward reward (phaseQuitter phase) 0 = 0 := by
    change weight ({phaseQuitter phase} : Finset Player) 0 = 0
    exact singletonWeight_phaseQuitter_zero phase
  have hpair : quittingSingletonCollisionReward reward
      (phaseQuitter phase) 0 = phaseCollisionValue phase := by
    change weight ({phaseQuitter phase, 0} : Finset Player) 0 =
      phaseCollisionValue phase
    rw [show ({phaseQuitter phase, 0} : Finset Player) =
      {0, phaseQuitter phase} by ext who; simp [or_comm]]
    exact playerZero_pairWeight phase
  rw [hsoloZero, hsoloQuitter, hpair]
  simp only [FinFivePhaseSeamAtomFloor.halfCoin,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  ring

/-- Conjunction of the canonical scalar box, all five supported Continue
rows, and the upper closing-seam row. -/
def PhaseSeamSystem (delta x : ℝ) : Prop :=
  x ∈ Set.Icc (-1) 1 ∧
    (∀ phase,
      quittingRootEndpointDifference reward (fun _ => phaseTail x phase)
        (phaseRoot phase) 0 ≤ 0) ∧
    (31 / 32 : ℝ) * x ≤ delta

/-- Below `31 / 32`, either binding phase row conflicts with the upper seam. -/
theorem not_exists_phaseSeamSystem_of_lt
    {delta : ℝ} (hdelta : delta < 31 / 32) :
    ¬ ∃ x : ℝ, PhaseSeamSystem delta x := by
  rintro ⟨x, _hbox, hphase, hseam⟩
  have hfour := hphase 4
  rw [playerZero_endpointDifference] at hfour
  have hcollision : phaseCollisionValue 4 = 1 := rfl
  have htail : phaseTail x 4 = x := rfl
  rw [hcollision, htail] at hfour
  norm_num at hseam hdelta
  linarith

/-- The threshold is sharp: `x = 1` satisfies the box, every phase row, and
the seam exactly at `delta = 31 / 32`. -/
theorem phaseSeamSystem_sharp :
    PhaseSeamSystem (31 / 32) 1 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  intro phase
  rw [playerZero_endpointDifference]
  fin_cases phase <;> simp +decide [phaseCollisionValue, phaseTail] <;>
    norm_num

/-! ## Actual two-date deleted-game sources -/

/-- The four retained players on face `phase`. -/
abbrev Survivor (phase : Player) := QuittingDeletedPlayer phase

/-- The phase quitter, regarded as a retained player. -/
def sourceQuitter (phase : Player) : Survivor phase :=
  ⟨phaseQuitter phase,
    FinFivePhaseSeamAtomFloor.phaseQuitter_ne_phase phase⟩

/-- Date-zero root of the deleted-player source. -/
def sourceFirstRoot (phase : Player) : Survivor phase → PMF Bool :=
  quittingSoloStationaryRoot (sourceQuitter phase) halfCoin

/-- At date one all four retained players Quit surely. -/
def sourceExitRoot (phase : Player) : Survivor phase → PMF Bool :=
  quittingPureSetRoot (Finset.univ : Finset (Survivor phase))

/-- The source has two active dates and then an irrelevant all-Continue tail. -/
def sourceRoots (phase : Player) (time : ℕ) : Survivor phase → PMF Bool :=
  if time = 0 then sourceFirstRoot phase
  else if time = 1 then sourceExitRoot phase
  else quittingAllContinueRoot

/-- Exit payoff of all four retained players. -/
def sourceExitValue (phase : Player) : Payoff (Survivor phase) :=
  quittingRootSuccessorPayoff (quittingDeletePlayerReward reward phase) 0
    (sourceExitRoot phase)

/-- Backward-evaluated two-date source values with zero boundary at date two. -/
def sourceValue (phase : Player) (time : ℕ) : Payoff (Survivor phase) :=
  if time = 0 then
    quittingRootSuccessorPayoff (quittingDeletePlayerReward reward phase)
      (sourceExitValue phase) (sourceFirstRoot phase)
  else if time = 1 then sourceExitValue phase
  else 0

/-- The executable deleted-game source profile. -/
def sourceProfile (phase : Player) :
    (quittingGame (quittingDeletePlayerReward reward phase)).BehaviorProfile :=
  quittingInfinitePathProfile (quittingDeletePlayerReward reward phase)
    (sourceRoots phase)

@[simp] theorem deleteReward_singleton (phase : Player)
    (quitter who : Survivor phase) :
    quittingDeletePlayerReward reward phase
        (quittingSingletonTerminal quitter) who =
      reward (quittingSingletonTerminal quitter.1) who.1 := by
  rfl

@[simp] theorem deleteReward_pair (phase : Player)
    (first second who : Survivor phase) :
    quittingDeletePlayerReward reward phase
        ⟨{first, second}, Finset.insert_nonempty first {second}⟩ who =
      reward
        ⟨{first.1, second.1}, Finset.insert_nonempty first.1 {second.1}⟩
        who.1 := by
  change reward (quittingExtendDeletedCoalition (fun player => player = phase)
      ⟨{first, second}, Finset.insert_nonempty first {second}⟩) who.1 = _
  congr 2
  apply Subtype.ext
  simp [quittingExtendDeletedCoalition]

/-- The grand coalition of the deleted game is the four-player face. -/
@[simp] theorem deleteReward_univ (phase : Player) (who : Survivor phase) :
    quittingDeletePlayerReward reward phase
        ⟨Finset.univ,
          ⟨sourceQuitter phase, Finset.mem_univ (sourceQuitter phase)⟩⟩ who =
      reward
        ⟨Finset.univ.erase phase,
          ⟨phaseQuitter phase, by
            simp [FinFivePhaseSeamAtomFloor.phaseQuitter_ne_phase phase]⟩⟩
        who.1 := by
  change reward (quittingExtendDeletedCoalition (fun player => player = phase)
      ⟨Finset.univ,
        ⟨sourceQuitter phase, Finset.mem_univ (sourceQuitter phase)⟩⟩) who.1 = _
  congr 2
  apply Subtype.ext
  ext player
  constructor
  · intro hmem
    obtain ⟨survivor, _, heq⟩ := Finset.mem_map.mp hmem
    subst player
    simp [survivor.2]
  · intro hmem
    have hne : player ≠ phase := (Finset.mem_erase.mp hmem).1
    exact Finset.mem_map.mpr
      ⟨⟨player, hne⟩, Finset.mem_univ _, rfl⟩

theorem sourceRoots_tail (phase : Player) (time : ℕ) (htime : 2 ≤ time) :
    sourceRoots phase time =
      (quittingAllContinueRoot : Survivor phase → PMF Bool) := by
  have hzero : time ≠ 0 := by omega
  have hone : time ≠ 1 := by omega
  simp [sourceRoots, hzero, hone]

theorem sourceValue_terminal (phase : Player) :
    sourceValue phase 2 = 0 := by
  simp [sourceValue]

theorem sourceValue_policy (phase : Player) (time : ℕ) (htime : time < 2) :
    sourceValue phase time =
      quittingRootSuccessorPayoff (quittingDeletePlayerReward reward phase)
        (sourceValue phase (time + 1)) (sourceRoots phase time) := by
  interval_cases time <;> simp [sourceValue, sourceRoots, sourceExitValue]

/-- The date-one all-retained-player exit is stable in every deleted game. -/
theorem sourceExitSet_isQuittingSureExitSet (phase : Player) :
    IsQuittingSureExitSet (quittingDeletePlayerReward reward phase)
      (Finset.univ : Finset (Survivor phase)) := by
  rw [isQuittingSureExitSet_univ_iff]
  rintro ⟨who, hwho⟩
  fin_cases phase <;> fin_cases who <;>
    simp_all +decide [quittingSetReward, quittingDeletePlayerReward,
      quittingDeleteReward, quittingExtendDeletedCoalition, reward,
      rewardOfWeight, weight]

/-- Date one is an exact root Nash row against the zero boundary. -/
theorem sourceExitRoot_isZeroNash (phase : Player) :
    IsεQuittingRootNash (quittingDeletePlayerReward reward phase) 0 0
      (sourceExitRoot phase) := by
  have hnash := isZeroQuittingRootNash_pureSetRoot_setReward
    (reward := quittingDeletePlayerReward reward phase)
    (Finset.univ : Finset (Survivor phase))
    (sourceExitSet_isQuittingSureExitSet phase)
  have hsure : QuittingRootHasSureQuitter (sourceExitRoot phase) := by
    refine ⟨sourceQuitter phase, ?_⟩
    simp only [sourceExitRoot, quittingPureSetRoot]
    congr 1
    simp [quittingSetAction]
  intro who deviation
  have hleft := quittingRootExpectedPayoff_eq_of_hasSureQuitter
    (quittingDeletePlayerReward reward phase)
    (Function.update (sourceExitRoot phase) who deviation)
    (by
      have hcard : 1 < Fintype.card (Survivor phase) := by
        simp [Survivor]
      obtain ⟨other, hother⟩ :=
        Fintype.exists_ne_of_one_lt_card hcard who
      refine ⟨other, ?_⟩
      rw [Function.update_of_ne hother]
      simp only [sourceExitRoot, quittingPureSetRoot]
      congr 1
      simp [quittingSetAction])
    (0 : Payoff (Survivor phase))
      (quittingSetReward (quittingDeletePlayerReward reward phase)
        Finset.univ) who
  have hright := quittingRootExpectedPayoff_eq_of_hasSureQuitter
    (quittingDeletePlayerReward reward phase) (sourceExitRoot phase) hsure
    (0 : Payoff (Survivor phase))
      (quittingSetReward (quittingDeletePlayerReward reward phase)
        Finset.univ) who
  rw [hleft, hright]
  exact hnash who deviation

/-- The date-one continuation vector is literally the all-retained-player
exit reward. -/
theorem sourceExitValue_eq_setReward (phase : Player) :
    sourceExitValue phase =
      quittingSetReward (quittingDeletePlayerReward reward phase)
        Finset.univ := by
  have hsure : QuittingRootHasSureQuitter (sourceExitRoot phase) := by
    refine ⟨sourceQuitter phase, ?_⟩
    simp only [sourceExitRoot, quittingPureSetRoot]
    congr 1
    simp [quittingSetAction]
  funext who
  unfold sourceExitValue quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_of_hasSureQuitter
    (quittingDeletePlayerReward reward phase) (sourceExitRoot phase) hsure
    (0 : Payoff (Survivor phase))
    (quittingSetReward (quittingDeletePlayerReward reward phase)
      Finset.univ) who]
  exact congrFun (quittingPureSetRoot_setReward_fixedPoint
    (reward := quittingDeletePlayerReward reward phase)
    (Finset.univ : Finset (Survivor phase))) who |>.symm

/-- Player zero's payoff when all retained players on a face Quit. -/
def sourceZeroExitValue : Player → ℝ := ![0, 0, 0, 1 / 16, 1]

theorem source_setReward_univ_nonzero (phase : Player) (who : Survivor phase)
    (hzero : who.1 ≠ 0) :
    quittingSetReward (quittingDeletePlayerReward reward phase)
      Finset.univ who = 1 := by
  rw [quittingSetReward_of_nonempty _
      ⟨sourceQuitter phase, Finset.mem_univ (sourceQuitter phase)⟩,
    deleteReward_univ]
  change weight (Finset.univ.erase phase) who.1 = 1
  simp [weight, hzero, who.2]

theorem source_setReward_univ_zero (phase : Player) (hphase : (0 : Player) ≠ phase) :
    quittingSetReward (quittingDeletePlayerReward reward phase)
      Finset.univ (⟨0, hphase⟩ : Survivor phase) =
        sourceZeroExitValue phase := by
  rw [quittingSetReward_of_nonempty _
      ⟨sourceQuitter phase, Finset.mem_univ (sourceQuitter phase)⟩,
    deleteReward_univ]
  change weight (Finset.univ.erase phase) 0 = sourceZeroExitValue phase
  fin_cases phase <;>
    simp_all +decide [sourceZeroExitValue, weight]

theorem source_quitter_soloReward_self (phase : Player) :
    quittingSoloReward (quittingDeletePlayerReward reward phase)
      (sourceQuitter phase) (sourceQuitter phase) = 1 := by
  change quittingDeletePlayerReward reward phase
      (quittingSingletonTerminal (sourceQuitter phase))
        (sourceQuitter phase) = 1
  rw [deleteReward_singleton]
  change weight ({(sourceQuitter phase).1} : Finset Player)
    (sourceQuitter phase).1 = 1
  fin_cases phase <;>
    simp +decide [weight]

theorem source_quitter_exitReward (phase : Player) :
    quittingSetReward (quittingDeletePlayerReward reward phase)
      Finset.univ (sourceQuitter phase) = 1 := by
  apply source_setReward_univ_nonzero
  exact FinFivePhaseSeamAtomFloor.phaseQuitter_ne_zero phase

theorem source_inactive_quitterSoloReward_zero (phase : Player)
    (who : Survivor phase) (hwho : who ≠ sourceQuitter phase) :
    quittingSoloReward (quittingDeletePlayerReward reward phase)
      (sourceQuitter phase) who = 0 := by
  change quittingDeletePlayerReward reward phase
      (quittingSingletonTerminal (sourceQuitter phase)) who = 0
  rw [deleteReward_singleton]
  change weight ({(sourceQuitter phase).1} : Finset Player) who.1 = 0
  rcases who with ⟨who, hwhoPhase⟩
  fin_cases phase <;> fin_cases who <;>
    simp_all +decide [sourceQuitter, weight]

theorem source_inactive_nonzero_ownSoloReward (phase : Player)
    (who : Survivor phase) (hzero : who.1 ≠ 0) :
    quittingSoloReward (quittingDeletePlayerReward reward phase) who who = 1 := by
  change quittingDeletePlayerReward reward phase
      (quittingSingletonTerminal who) who = 1
  rw [deleteReward_singleton]
  change weight ({who.1} : Finset Player) who.1 = 1
  rcases who with ⟨who, hwhoPhase⟩
  fin_cases phase <;> fin_cases who <;>
    simp_all +decide [weight]

theorem source_inactive_nonzero_collisionReward (phase : Player)
    (who : Survivor phase) (hwho : who ≠ sourceQuitter phase)
    (hzero : who.1 ≠ 0) :
    quittingSingletonCollisionReward (quittingDeletePlayerReward reward phase)
      (sourceQuitter phase) who = 0 := by
  change quittingDeletePlayerReward reward phase
      ⟨{sourceQuitter phase, who},
        Finset.insert_nonempty (sourceQuitter phase) {who}⟩ who = 0
  rw [deleteReward_pair]
  change weight ({(sourceQuitter phase).1, who.1} : Finset Player) who.1 = 0
  rcases who with ⟨who, hwhoPhase⟩
  fin_cases phase <;> fin_cases who <;>
    simp_all +decide [sourceQuitter, weight]

theorem source_zero_ownSoloReward (phase : Player)
    (hphase : (0 : Player) ≠ phase) :
    quittingSoloReward (quittingDeletePlayerReward reward phase)
      (⟨0, hphase⟩ : Survivor phase) (⟨0, hphase⟩ : Survivor phase) = 0 := by
  change quittingDeletePlayerReward reward phase
      (quittingSingletonTerminal (⟨0, hphase⟩ : Survivor phase))
        (⟨0, hphase⟩ : Survivor phase) = 0
  rw [deleteReward_singleton]
  change weight ({0} : Finset Player) 0 = 0
  fin_cases phase <;>
    simp_all +decide [weight]

theorem source_zero_collisionReward (phase : Player)
    (hphase : (0 : Player) ≠ phase) :
    quittingSingletonCollisionReward
      (quittingDeletePlayerReward reward phase) (sourceQuitter phase)
        (⟨0, hphase⟩ : Survivor phase) = phaseCollisionValue phase := by
  change quittingDeletePlayerReward reward phase
      ⟨{sourceQuitter phase, (⟨0, hphase⟩ : Survivor phase)},
        Finset.insert_nonempty (sourceQuitter phase) {⟨0, hphase⟩}⟩
      (⟨0, hphase⟩ : Survivor phase) = phaseCollisionValue phase
  rw [deleteReward_pair]
  change weight ({(sourceQuitter phase).1, 0} : Finset Player) 0 =
    phaseCollisionValue phase
  fin_cases phase <;>
    simp_all +decide [phaseCollisionValue, weight]

theorem phaseCollisionValue_le_sourceZeroExitValue (phase : Player)
    (hphase : (0 : Player) ≠ phase) :
    phaseCollisionValue phase ≤ sourceZeroExitValue phase := by
  fin_cases phase <;> simp_all [phaseCollisionValue, sourceZeroExitValue]

theorem sourceFirstRoot_quitter_endpointDifference (phase : Player) :
    quittingRootEndpointDifference (quittingDeletePlayerReward reward phase)
      (sourceExitValue phase) (sourceFirstRoot phase)
      (sourceQuitter phase) = 0 := by
  rw [quittingRootEndpointDifference, sourceFirstRoot,
    quittingRootQuitPayoff_soloStationaryRoot_owner,
    quittingRootContinuePayoff_soloStationaryRoot_owner,
    sourceExitValue_eq_setReward]
  rw [source_quitter_soloReward_self, source_quitter_exitReward]
  norm_num

theorem sourceFirstRoot_other_endpointDifference_nonpos (phase : Player)
    (who : Survivor phase) (hwho : who ≠ sourceQuitter phase) :
    quittingRootEndpointDifference (quittingDeletePlayerReward reward phase)
      (sourceExitValue phase) (sourceFirstRoot phase) who ≤ 0 := by
  rw [quittingRootEndpointDifference, sourceFirstRoot,
    quittingRootQuitPayoff_soloStationaryRoot_other
      (quittingDeletePlayerReward reward phase) hwho,
    quittingRootContinuePayoff_soloStationaryRoot_other
      (quittingDeletePlayerReward reward phase) hwho,
    sourceExitValue_eq_setReward]
  rw [source_inactive_quitterSoloReward_zero phase who hwho]
  simp only [FinFivePhaseSeamAtomFloor.halfCoin,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  by_cases hzero : who.1 = 0
  · have hphase : (0 : Player) ≠ phase := by
      simpa [hzero] using who.2
    have hwhoZero : who = (⟨0, hphase⟩ : Survivor phase) := by
      exact Subtype.ext hzero
    subst who
    rw [source_zero_ownSoloReward, source_zero_collisionReward,
      source_setReward_univ_zero]
    linarith [phaseCollisionValue_le_sourceZeroExitValue phase hphase]
  · rw [source_inactive_nonzero_ownSoloReward phase who hzero,
      source_inactive_nonzero_collisionReward phase who hwho hzero,
      source_setReward_univ_nonzero phase who hzero]
    norm_num

/-- The mixed date-zero root is exact Nash against the date-one exit value. -/
theorem sourceFirstRoot_isZeroNash (phase : Player) :
    IsεQuittingRootNash (quittingDeletePlayerReward reward phase)
      (sourceExitValue phase) 0 (sourceFirstRoot phase) := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    (quittingDeletePlayerReward reward phase) (sourceExitValue phase)
      (sourceFirstRoot phase)).mp
  intro who
  by_cases hwho : who = sourceQuitter phase
  · subst who
    rw [sourceFirstRoot_quitter_endpointDifference]
    simp
  · have hdiff := sourceFirstRoot_other_endpointDifference_nonpos phase who hwho
    have hcontinue :
        (sourceFirstRoot phase who false).toReal = 1 := by
      rw [sourceFirstRoot,
        quittingSoloStationaryRoot_apply_other hwho halfCoin]
      simp
    have hquit : (sourceFirstRoot phase who true).toReal = 0 := by
      rw [sourceFirstRoot,
        quittingSoloStationaryRoot_apply_other hwho halfCoin]
      simp
    constructor
    · rw [hcontinue, one_mul]
      exact hdiff
    · rw [hquit, zero_mul]
      norm_num

/-- Each of the two displayed source dates is an exact deleted-game root
Nash row against its backward continuation value. -/
theorem sourceRoot_isZeroNash (phase : Player) (time : ℕ) (htime : time < 2) :
    IsεQuittingRootNash (quittingDeletePlayerReward reward phase)
      (sourceValue phase (time + 1)) 0 (sourceRoots phase time) := by
  interval_cases time
  · simpa [sourceRoots, sourceValue] using sourceFirstRoot_isZeroNash phase
  · simpa [sourceRoots, sourceValue] using sourceExitRoot_isZeroNash phase

theorem sourceFixedOpponentsContinueMass_one_eq_zero (phase : Player)
    (who : Survivor phase) :
    quittingFixedOpponentsContinueMass (sourceRoots phase) who 1 = 0 := by
  unfold quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  have hcard : 1 < Fintype.card (Survivor phase) := by
    simp [Survivor]
  obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card hcard who
  apply Finset.prod_eq_zero (Finset.mem_univ other)
  rw [Function.update_of_ne hother]
  simp [sourceRoots, sourceExitRoot, quittingPureSetRoot, quittingSetAction]

theorem sourceOpponentSurvivalWeight_two_eq_zero (phase : Player)
    (who : Survivor phase) :
    quittingOpponentSurvivalWeight (sourceRoots phase) who 0 2 = 0 := by
  rw [show 2 = 1 + 1 by omega,
    quittingOpponentSurvivalWeight_zero_succ,
    sourceFixedOpponentsContinueMass_one_eq_zero, mul_zero]

/-- The displayed two-date profile is an exact terminal Nash equilibrium of
the corresponding four-player deleted game, against unrestricted behavioral
deviations. -/
theorem sourceProfile_isExactTerminalNash (phase : Player) :
    (quittingGame (quittingDeletePlayerReward reward phase)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeletePlayerReward reward phase)) 0
        (sourceProfile phase) := by
  apply finiteExactChainProfile_isεAsymptoticNash
    (quittingDeletePlayerReward reward phase) (sourceRoots phase)
      (sourceValue phase) 2 0
  · exact sourceRoots_tail phase
  · exact sourceValue_terminal phase
  · exact sourceValue_policy phase
  · exact sourceRoot_isZeroNash phase
  · intro who
    rw [sourceOpponentSurvivalWeight_two_eq_zero]
    norm_num

/-- The terminal payoff of the exact source is its explicit backward value. -/
theorem sourceProfile_terminalPayoff_eq_value (phase : Player) :
    quittingTerminalPayoff (quittingDeletePlayerReward reward phase)
        (sourceProfile phase) = sourceValue phase 0 := by
  exact quittingTerminalPayoff_finiteExactChainProfile
    (quittingDeletePlayerReward reward phase) (sourceRoots phase)
      (sourceValue phase) 2 (sourceRoots_tail phase)
      (sourceValue_terminal phase) (sourceValue_policy phase)

/-! ## Literal quiet-face provenance -/

/-- The root sequence obtained by extending a deleted source with Never. -/
def liftedSourceRoots (phase : Player) : ℕ → Player → PMF Bool :=
  quittingExtendDeletedRoots (fun player => player = phase) (sourceRoots phase)

/-- The ambient profile obtained by prescribing Never to the omitted player. -/
def liftedSourceProfile (phase : Player) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiftDeletedProfile reward (fun player => player = phase)
    (sourceProfile phase)

/-- The live chronology of the lift is the literal rootwise Never extension
of the deleted source chronology. -/
theorem liftedSourceProfile_liveRoot (phase : Player) (time : ℕ) :
    quittingProfileLiveRoot reward (liftedSourceProfile phase) time =
      liftedSourceRoots phase time := by
  rw [liftedSourceProfile, quittingProfileLiveRoot_liftDeletedProfile]
  simp [sourceProfile, liftedSourceRoots]

/-- Its date-zero root is exactly the advertised mass-`1 / 2` face root. -/
theorem liftedSourceProfile_liveRoot_zero (phase : Player) :
    quittingProfileLiveRoot reward (liftedSourceProfile phase) 0 =
      phaseRoot phase := by
  rw [liftedSourceProfile_liveRoot]
  funext player
  by_cases hplayer : player = phase
  · subst player
    rw [liftedSourceRoots]
    simp [phaseRoot_owner_quiet]
  · let survivor : Survivor phase := ⟨player, hplayer⟩
    rw [show player = survivor.1 by rfl,
      liftedSourceRoots, quittingExtendDeletedRoots_apply]
    simp only [sourceRoots, if_pos, sourceFirstRoot, phaseRoot,
      FinFivePhaseSeamAtomFloor.phaseRoot]
    by_cases hquitter : player = phaseQuitter phase
    · have hsurvivor : survivor = sourceQuitter phase := by
        exact Subtype.ext hquitter
      rw [hsurvivor, quittingSoloStationaryRoot_apply_owner]
      subst player
      change halfCoin = quittingSoloStationaryRoot
        (phaseQuitter phase) halfCoin (sourceQuitter phase).1
      rw [show (sourceQuitter phase).1 = phaseQuitter phase by rfl]
      rw [quittingSoloStationaryRoot_apply_owner]
    · have hsurvivor : survivor ≠ sourceQuitter phase := by
        intro heq
        exact hquitter (congrArg Subtype.val heq)
      rw [quittingSoloStationaryRoot_apply_other hsurvivor,
        quittingSoloStationaryRoot_apply_other hquitter]

/-- The omitted player is literally quiet at every date of the lifted source. -/
theorem liftedSourceProfile_owner_quiet (phase : Player) (time : ℕ) :
    quittingProfileLiveRoot reward (liftedSourceProfile phase) time phase =
      PMF.pure false := by
  rw [liftedSourceProfile_liveRoot]
  exact quittingExtendDeletedRoots_of_deleted
    (fun player => player = phase) (sourceRoots phase) time rfl

/-- Date one of the lift is the pure exit of all four face players. -/
theorem liftedSourceRoots_one (phase : Player) :
    liftedSourceRoots phase 1 =
      quittingPureSetRoot (Finset.univ.erase phase) := by
  funext player
  by_cases hplayer : player = phase
  · subst player
    simp [liftedSourceRoots, quittingPureSetRoot, quittingSetAction]
  · let survivor : Survivor phase := ⟨player, hplayer⟩
    rw [show player = survivor.1 by rfl]
    rw [liftedSourceRoots, quittingExtendDeletedRoots_apply]
    simp [sourceRoots, sourceExitRoot, quittingPureSetRoot,
      quittingSetAction, survivor, hplayer]

/-- Beyond the two active dates the lifted chronology is all-Continue. -/
theorem liftedSourceRoots_tail (phase : Player) (time : ℕ) (htime : 2 ≤ time) :
    liftedSourceRoots phase time = quittingAllContinueRoot := by
  unfold liftedSourceRoots quittingExtendDeletedRoots
  rw [sourceRoots_tail phase time htime]
  funext player
  by_cases hplayer : player = phase
  · subst player
    simp only [quittingExtendDeletedRoot]
    rfl
  · let survivor : Survivor phase := ⟨player, hplayer⟩
    rw [show player = survivor.1 by rfl,
      quittingExtendDeletedRoot_apply]
    rfl

/-- Backward value of the lifted two-date chronology. -/
def liftedSourceValue (phase : Player) (time : ℕ) : Payoff Player :=
  if time = 0 then
    quittingRootSuccessorPayoff reward
      (quittingRootSuccessorPayoff reward 0 (liftedSourceRoots phase 1))
        (liftedSourceRoots phase 0)
  else if time = 1 then
    quittingRootSuccessorPayoff reward 0 (liftedSourceRoots phase 1)
  else 0

theorem liftedSourceValue_terminal (phase : Player) :
    liftedSourceValue phase 2 = 0 := by
  simp [liftedSourceValue]

theorem liftedSourceValue_policy (phase : Player) (time : ℕ)
    (htime : time < 2) :
    liftedSourceValue phase time =
      quittingRootSuccessorPayoff reward (liftedSourceValue phase (time + 1))
        (liftedSourceRoots phase time) := by
  interval_cases time <;> simp [liftedSourceValue]

/-- The lifted source's ambient terminal payoff is its explicit backward
value; no equilibrium claim is made for the lift. -/
theorem liftedSourceProfile_terminalPayoff_eq_value (phase : Player) :
    quittingTerminalPayoff reward (liftedSourceProfile phase) =
      liftedSourceValue phase 0 := by
  unfold liftedSourceProfile quittingLiftDeletedProfile
  rw [sourceProfile, quittingProfileLiveRoot_infinitePathProfile]
  change quittingTerminalPayoff reward
    (quittingInfinitePathProfile reward (liftedSourceRoots phase)) = _
  exact quittingTerminalPayoff_finiteExactChainProfile reward
    (liftedSourceRoots phase) (liftedSourceValue phase) 2
      (liftedSourceRoots_tail phase) (liftedSourceValue_terminal phase)
      (liftedSourceValue_policy phase)

theorem liftedSourceRoots_zero (phase : Player) :
    liftedSourceRoots phase 0 = phaseRoot phase := by
  rw [← liftedSourceProfile_liveRoot phase 0]
  exact liftedSourceProfile_liveRoot_zero phase

/-- The four-player face reward pays the omitted player zero. -/
theorem liftedSource_faceReward_owner_eq_zero (phase : Player) :
    quittingSetReward reward (Finset.univ.erase phase) phase = 0 := by
  have hnonempty : (Finset.univ.erase phase : Finset Player).Nonempty := by
    exact ⟨phaseQuitter phase, by
      simp [FinFivePhaseSeamAtomFloor.phaseQuitter_ne_phase phase]⟩
  rw [quittingSetReward_of_nonempty reward hnonempty]
  change weight (Finset.univ.erase phase) phase = 0
  fin_cases phase <;> simp +decide [weight]

/-- The omitted coordinate of the date-one exit value is zero. -/
theorem liftedSource_exitValue_owner_eq_zero (phase : Player) :
    quittingRootSuccessorPayoff reward 0 (liftedSourceRoots phase 1) phase = 0 := by
  rw [liftedSourceRoots_one]
  have hsure : QuittingRootHasSureQuitter
      (quittingPureSetRoot (Finset.univ.erase phase) : Player → PMF Bool) := by
    refine ⟨phaseQuitter phase, ?_⟩
    simp only [quittingPureSetRoot]
    congr 1
    simp [quittingSetAction,
      FinFivePhaseSeamAtomFloor.phaseQuitter_ne_phase phase]
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_of_hasSureQuitter reward
    (quittingPureSetRoot (Finset.univ.erase phase)) hsure
    (0 : Payoff Player)
    (quittingSetReward reward (Finset.univ.erase phase)) phase]
  have hfixed := congrFun (quittingPureSetRoot_setReward_fixedPoint
    (reward := reward) (Finset.univ.erase phase)) phase
  unfold quittingRootSuccessorPayoff at hfixed
  rw [← hfixed]
  exact liftedSource_faceReward_owner_eq_zero phase

theorem liftedSource_singletonQuitterReward_owner_eq_zero (phase : Player) :
    quittingSoloReward reward (phaseQuitter phase) phase = 0 := by
  change weight ({phaseQuitter phase} : Finset Player) phase = 0
  fin_cases phase <;> simp +decide [weight]

/-- The omitted player receives zero on the lifted source path. -/
theorem liftedSourceValue_owner_eq_zero (phase : Player) :
    liftedSourceValue phase 0 phase = 0 := by
  simp only [liftedSourceValue, if_pos]
  rw [liftedSourceRoots_zero]
  change quittingRootSuccessorPayoff reward
      (quittingRootSuccessorPayoff reward 0 (liftedSourceRoots phase 1))
      (quittingSoloStationaryRoot (phaseQuitter phase) halfCoin) phase = 0
  rw [congrFun (quittingRootSuccessorPayoff_solo reward
    (phaseQuitter phase) halfCoin
      (quittingRootSuccessorPayoff reward 0 (liftedSourceRoots phase 1))) phase]
  rw [liftedSource_singletonQuitterReward_owner_eq_zero,
    liftedSource_exitValue_owner_eq_zero]
  ring

theorem liftedSourceProfile_ownerPayoff_eq_zero (phase : Player) :
    quittingTerminalPayoff reward (liftedSourceProfile phase) phase = 0 := by
  rw [congrFun (liftedSourceProfile_terminalPayoff_eq_value phase) phase]
  exact liftedSourceValue_owner_eq_zero phase

/-- Exact omitted-player immediate-Quit gap on each face. -/
def omittedGap : Player → ℝ := ![1 / 32, 1 / 2, 1 / 2, 1 / 2, 1 / 2]

theorem liftedSource_fixedOpponentsQuitValue_owner (phase : Player) :
    quittingFixedOpponentsQuitValue reward (liftedSourceRoots phase) phase 0 =
      omittedGap phase := by
  rw [← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (liftedSourceRoots phase) phase (0 : Payoff Player) 0,
    liftedSourceRoots_zero]
  change quittingRootQuitPayoff reward 0
    (quittingSoloStationaryRoot (phaseQuitter phase) halfCoin) phase = _
  rw [quittingRootQuitPayoff_soloStationaryRoot_other reward
    (Ne.symm (FinFivePhaseSeamAtomFloor.phaseQuitter_ne_phase phase))]
  simp only [FinFivePhaseSeamAtomFloor.halfCoin,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  have hsolo : quittingSoloReward reward phase phase =
      weight {phase} phase := by
    rfl
  have hcollision : quittingSingletonCollisionReward reward
      (phaseQuitter phase) phase = weight {phaseQuitter phase, phase} phase := by
    rfl
  rw [hsolo, hcollision]
  change (1 - 1 / 2 : ℝ) * weight {phase} phase +
      (1 / 2 : ℝ) * weight {phaseQuitter phase, phase} phase =
        omittedGap phase
  fin_cases phase <;> simp +decide [weight, omittedGap] <;> norm_num

/-- Quitting immediately realizes the positive omitted-player face gap. -/
theorem liftedSourceProfile_ownerImmediateQuitPayoff (phase : Player) :
    quittingTerminalPayoff reward
      (Function.update (liftedSourceProfile phase) phase
        (quittingPureTimeBehaviorStrategy reward phase (some 0))) phase =
      omittedGap phase := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  have hlive : quittingProfileLiveRoot reward (liftedSourceProfile phase) =
      liftedSourceRoots phase := by
    funext time
    exact liftedSourceProfile_liveRoot phase time
  rw [hlive]
  exact liftedSource_fixedOpponentsQuitValue_owner phase

theorem omittedGap_pos (phase : Player) : 0 < omittedGap phase := by
  fin_cases phase <;> norm_num [omittedGap]

/-- The lifted face source therefore has the advertised strictly positive,
source-matched omitted-player gap on every one of the five faces. -/
theorem liftedSourceProfile_ownerImmediateQuitGap (phase : Player) :
    quittingTerminalPayoff reward
        (Function.update (liftedSourceProfile phase) phase
          (quittingPureTimeBehaviorStrategy reward phase (some 0))) phase -
      quittingTerminalPayoff reward (liftedSourceProfile phase) phase =
        omittedGap phase ∧ 0 < omittedGap phase := by
  rw [liftedSourceProfile_ownerImmediateQuitPayoff,
    liftedSourceProfile_ownerPayoff_eq_zero, sub_zero]
  exact ⟨rfl, omittedGap_pos phase⟩



/-! ## The ambient zero-debt boundary -/

/-- The ambient pure profile in which all five players Quit immediately. -/
def ambientAllQuitProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingPureSetRoot (Finset.univ : Finset Player))

/-- All-Quit is an exact ambient terminal Nash equilibrium. -/
theorem ambientAllQuitProfile_isExactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 ambientAllQuitProfile := by
  rw [ambientAllQuitProfile,
    isεAsymptoticNash_pureSetRoot_univ_iff]
  intro who
  fin_cases who <;> simp +decide [quittingSetReward, reward,
    rewardOfWeight, weight]

/-- The ambient exact equilibrium has exactly zero total semantic debt. -/
theorem ambientAllQuitProfile_debtSum_eq_zero :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward ambientAllQuitProfile) = 0 := by
  have hupper := terminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash
    reward ambientAllQuitProfile 0 ambientAllQuitProfile_isExactTerminalNash
  have hnonneg : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward ambientAllQuitProfile) := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalDeviationDebt_nonneg reward ambientAllQuitProfile who
  norm_num at hupper
  linarith

/-- Consequently the table lies on the `D_* = 0` boundary. -/
theorem hasZeroMinimumTerminalSemanticDebt :
    HasZeroMinimumTerminalSemanticDebt reward := by
  let pair := quittingTerminalSemanticPair reward ambientAllQuitProfile
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨ambientAllQuitProfile, rfl⟩
  refine ⟨pair, hpair, ?_, ambientAllQuitProfile_debtSum_eq_zero⟩
  intro candidate hcandidate
  rw [ambientAllQuitProfile_debtSum_eq_zero]
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_nonneg fun who _ =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hcandidate who

end FinFiveFullFaceSourcePhaseSeam
end GameTheory
