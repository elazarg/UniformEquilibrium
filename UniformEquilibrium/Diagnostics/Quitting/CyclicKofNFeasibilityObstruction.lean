/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanQuitEndpointLimit
import UniformEquilibrium.Quitting.Cycles.PhaseSwitchDeviationCap
import UniformEquilibrium.Quitting.Cycles.CyclicKofNFiniteNashCertificate
import UniformEquilibrium.Quitting.Cycles.CyclicKofNPhaseHazards
import UniformEquilibrium.Quitting.Cycles.CyclicKofNPlayerPhaseHazards
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# A feasibility obstruction for prescribed proper cyclic supports

The finite cyclic Nash certificate is a compiler, not a universal producer.
This file gives a general counterexample to the missing producer statement.

Pay each player one exactly when they belong to the terminal quitting
coalition, and zero otherwise.  Whenever a prescribed proper block omits a
player, forcing that player to Continue exposes them to positive absorption
by an opponent and yields strictly less than one.  Quitting immediately
guarantees one. Therefore no positive-hazard word on a proper translated
block is exact Nash for this reward, including at the sure-Quit boundary.
-/

namespace GameTheory

namespace CyclicKofNFeasibilityObstruction

open StochasticGame Math.Probability Math.PMFProduct
open Math.CyclicKofNArithmetic CyclicKofNQuittingSchedule
open CyclicKofNBellmanBridge CyclicKofNFiniteNashCertificate
open CyclicKofNPhaseHazards CyclicKofNPlayerPhaseHazards
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-- Every player receives one exactly when they belong to the terminal
quitting coalition. -/
def selfMembershipReward : {S : Finset G // S.Nonempty} → Payoff G :=
  fun terminal observer => if observer ∈ terminal.1 then 1 else 0

omit [AddGroup G] [Fintype G] in
theorem abs_selfMembershipReward_le_one
    (terminal : {S : Finset G // S.Nonempty}) (observer : G) :
    |selfMembershipReward terminal observer| ≤ 1 := by
  simp only [selfMembershipReward]
  split <;> norm_num

omit [AddGroup G] in
/-- If the owner quits purely, their membership payoff is one regardless of
the opponents and continuation. -/
theorem quittingRootQuitPayoff_selfMembershipReward
    (who : G) (tail : Payoff G) (root : G → PMF Bool) :
    quittingRootQuitPayoff selfMembershipReward tail root who = 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  calc
    expect (pmfPi (Function.update root who (PMF.pure true)))
        (fun action => quittingRootPayoff
          selfMembershipReward tail action who) =
      expect (pmfPi (Function.update root who (PMF.pure true)))
        (fun _action => (1 : ℝ)) := by
          apply Math.ProbabilityMassFunction.expect_congr_on_support
          intro action haction
          have howner :=
            action_eq_true_of_mem_support_pmfPi_update_pure_true
              root who action haction
          have hsome : ∃ player, action player = true := ⟨who, howner⟩
          simp [quittingRootPayoff, selfMembershipReward,
            quittingQuitters, howner, hsome]
    _ = 1 := expect_const _ _

omit [AddGroup G] in
/-- If the owner continues purely, no current absorbing coalition contains
them, so only all-opponents-Continue survival multiplies the tail value. -/
theorem quittingRootContinuePayoff_selfMembershipReward
    (who : G) (tail : Payoff G) (root : G → PMF Bool) :
    quittingRootContinuePayoff selfMembershipReward tail root who =
      quittingStationaryFixedOpponentsContinueMass root who * tail who := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  have habsorb : quittingRootAbsorbingContribution
      selfMembershipReward
      (Function.update root who (PMF.pure false)) who = 0 := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    calc
      expect (pmfPi (Function.update root who (PMF.pure false)))
          (fun action => quittingRootPayoff
            selfMembershipReward (0 : Payoff G) action who) =
        expect (pmfPi (Function.update root who (PMF.pure false)))
          (fun _action => (0 : ℝ)) := by
            apply Math.ProbabilityMassFunction.expect_congr_on_support
            intro action haction
            have howner :=
              action_eq_false_of_mem_support_pmfPi_update_pure_false
                root who action haction
            by_cases hnonempty : (quittingQuitters action).Nonempty
            · have hnotmem : who ∉ quittingQuitters action := by
                simp [quittingQuitters, howner]
              simp [quittingRootPayoff, selfMembershipReward,
                hnonempty, hnotmem]
            · simp [quittingRootPayoff, hnonempty]
      _ = 0 := expect_const _ _
  rw [habsorb, zero_add]
  rfl

omit [AddGroup G] in
/-- A pure-Continue owner cannot be exact Nash when some opponent absorbs
with positive probability and the continuation membership value is at most
one. -/
theorem not_isZeroNash_selfMembershipReward_of_pureContinue
    (owner : G) (tail : Payoff G) (root : G → PMF Bool)
    (htail : tail owner ≤ 1)
    (hpure : root owner = PMF.pure false)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass root owner < 1) :
    ¬ IsεQuittingRootNash selfMembershipReward tail 0 root := by
  intro hnash
  have hendpoint : IsεQuittingRootEndpointNash
      selfMembershipReward tail 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      selfMembershipReward tail root).mpr hnash
  have hquitZero : (root owner true).toReal = 0 := by
    rw [hpure]
    simp
  have hnonpos :=
    quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
      selfMembershipReward tail root owner hendpoint hquitZero
  have hmass0 : 0 ≤
      quittingStationaryFixedOpponentsContinueMass root owner :=
    quittingStationaryFixedOpponentsContinueMass_nonneg root owner
  have hcontinueLe :
      quittingStationaryFixedOpponentsContinueMass root owner * tail owner ≤
        quittingStationaryFixedOpponentsContinueMass root owner := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left htail hmass0
  have hpositive : 0 < quittingRootEndpointDifference
      selfMembershipReward tail root owner := by
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_selfMembershipReward,
      quittingRootContinuePayoff_selfMembershipReward]
    linarith
  exact (not_lt_of_ge hnonpos) hpositive

omit [AddGroup G] in
/-- Canonical terminal evaluation cannot repair the local obstruction: one
pure-Continue phase with strict opponent contraction destroys exact Nash for
the whole finite word. -/
theorem not_forall_canonicalWord_isZeroNash_selfMembershipReward
    {K : ℕ} (owner : G) (roots : Fin K → G → PMF Bool) (phase : Fin K)
    (hpure : roots phase owner = PMF.pure false)
    (hcontracts :
      quittingStationaryFixedOpponentsContinueMass
        (roots phase) owner < 1) :
    ¬ ∀ cyclePhase,
      IsεQuittingRootNash selfMembershipReward
        (quittingCyclicTerminalValue selfMembershipReward roots
          (finRotate K cyclePhase)) 0 (roots cyclePhase) := by
  intro hnash
  let tail : Payoff G :=
    quittingCyclicTerminalValue selfMembershipReward roots
      (finRotate K phase)
  have htailAbs : |tail owner| ≤ 1 := by
    dsimp only [tail, quittingCyclicTerminalValue]
    exact abs_quittingRootSequenceTerminalValue_le
      selfMembershipReward
      (quittingCyclicRootSequence roots (finRotate K phase))
      owner 0 (by norm_num) abs_selfMembershipReward_le_one
  have htail : tail owner ≤ 1 :=
    (le_abs_self (tail owner)).trans htailAbs
  exact not_isZeroNash_selfMembershipReward_of_pureContinue
    owner tail (roots phase) htail hpure hcontracts (hnash phase)

/-- **No universal prescribed-word producer.** For every nonempty proper
translated block and every positive common hazard, including sure Quit, the
owner-membership game fails the residual finite cyclic Nash certificate. -/
theorem not_finiteCyclicNashCertificate_selfMembershipReward
    (A : Finset G) (hA : A.Nonempty)
    (hproper : A ≠ Finset.univ)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β ≤ 1) :
    ¬ IsFiniteCyclicNashCertificate
      selfMembershipReward A β hβpos.le hβ1 := by
  let owner : G := 0
  intro hnash
  obtain ⟨phase, hownerInactive⟩ :=
    exists_not_mem_cyclicSchedule_active A hproper owner
  have hactiveNonempty :
      ((cyclicSchedule A).active phase.val).Nonempty := by
    rw [← Finset.card_pos, card_cyclicSchedule_active]
    exact hA.card_pos
  obtain ⟨opponent, hopponentActive⟩ := hactiveNonempty
  have hopponentNe : opponent ≠ owner := by
    intro hopponent
    subst opponent
    exact hownerInactive hopponentActive
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseRoots A β hβpos.le hβ1 phase) owner < 1 :=
    quittingStationaryFixedOpponentsContinueMass_cyclicPhaseRoots_lt_one
      A β hβpos hβ1 owner phase
        ⟨opponent, hopponentNe, hopponentActive⟩
  have hpure : cyclicPhaseRoots A β hβpos.le hβ1 phase owner =
      PMF.pure false := by
    have hownerInactive' :
        owner ∉ orbitSchedule A (translationClock A phase.val) :=
      hownerInactive
    change quittingActiveRoot ((cyclicSchedule A).active phase.val)
      (fun _ => quittingHazardCoin β hβpos.le hβ1) owner =
        PMF.pure false
    simp [quittingActiveRoot, hownerInactive']
  let tail : Payoff G :=
    cyclicTerminalValues selfMembershipReward
      A β hβpos.le hβ1
        (finRotate (Fintype.card (TranslationPhase A)) phase)
  have htailAbs : |tail owner| ≤ 1 := by
    dsimp only [tail, cyclicTerminalValues, quittingCyclicTerminalValue]
    exact abs_quittingRootSequenceTerminalValue_le
      selfMembershipReward
      (quittingCyclicRootSequence
        (cyclicPhaseRoots A β hβpos.le hβ1)
        (finRotate (Fintype.card (TranslationPhase A)) phase))
      owner 0 (by norm_num) abs_selfMembershipReward_le_one
  have htail : tail owner ≤ 1 :=
    (le_abs_self (tail owner)).trans htailAbs
  exact not_isZeroNash_selfMembershipReward_of_pureContinue
    owner tail (cyclicPhaseRoots A β hβpos.le hβ1 phase)
      htail hpure hcontracts (hnash phase)

/-- Cardinal form: the obstruction applies whenever `0 < K < N`. -/
theorem not_finiteCyclicNashCertificate_selfMembershipReward_of_card_lt
    (A : Finset G) (hA : A.Nonempty)
    (hcard : A.card < Fintype.card G)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β ≤ 1) :
    ¬ IsFiniteCyclicNashCertificate
      selfMembershipReward A β hβpos.le hβ1 := by
  have hproper : A ≠ Finset.univ := by
    intro hfull
    rw [hfull, Finset.card_univ] at hcard
    exact (Nat.lt_irrefl _ hcard)
  exact not_finiteCyclicNashCertificate_selfMembershipReward
    A hA hproper β hβpos hβ1

/-- Phase-varying common hazards do not remove the obstruction. -/
theorem not_finitePhaseHazardNashCertificate_selfMembershipReward
    (A : Finset G) (hA : A.Nonempty)
    (hproper : A ≠ Finset.univ)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) :
    ¬ IsFinitePhaseHazardNashCertificate selfMembershipReward A β
      (fun phase => (hβpos phase).le)
      hβ1 := by
  let owner : G := 0
  obtain ⟨phase, hownerInactive⟩ :=
    exists_not_mem_cyclicSchedule_active A hproper owner
  have hactiveNonempty :
      ((cyclicSchedule A).active phase.val).Nonempty := by
    rw [← Finset.card_pos, card_cyclicSchedule_active]
    exact hA.card_pos
  obtain ⟨opponent, hopponentActive⟩ := hactiveNonempty
  have hopponentNe : opponent ≠ owner := by
    intro hopponent
    subst opponent
    exact hownerInactive hopponentActive
  have hopponent : opponent ∈
      ((cyclicSchedule A).active phase.val).erase owner :=
    Finset.mem_erase.mpr ⟨hopponentNe, hopponentActive⟩
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPhaseHazardRoots A β
          (fun p => (hβpos p).le)
          hβ1 phase) owner < 1 := by
    rw [quittingStationaryFixedOpponentsContinueMass_phaseHazard]
    exact Math.Finset.prod_lt_one_of_mem
      (((cyclicSchedule A).active phase.val).erase owner)
      (fun _player => 1 - β phase)
      opponent hopponent
      (fun _ _ _ => sub_nonneg.mpr (hβ1 phase))
      (fun _ _ _ => by linarith [hβpos phase])
      (by linarith [hβpos phase])
  have hpure :
      cyclicPhaseHazardRoots A β
          (fun p => (hβpos p).le)
          hβ1 phase owner = PMF.pure false := by
    have hownerInactive' :
        owner ∉ orbitSchedule A (translationClock A phase.val) :=
      hownerInactive
    change quittingActiveRoot ((cyclicSchedule A).active phase.val)
      (fun _ => quittingHazardCoin (β phase)
        (hβpos phase).le (hβ1 phase)) owner = PMF.pure false
    simp [quittingActiveRoot, hownerInactive']
  exact not_forall_canonicalWord_isZeroNash_selfMembershipReward
    owner
    (cyclicPhaseHazardRoots A β
      (fun p => (hβpos p).le)
      hβ1)
    phase hpure hcontracts

/-- Fully heterogeneous positive hazards on a prescribed proper cyclic support
word do not remove the obstruction. -/
theorem not_finitePlayerPhaseNashCertificate_selfMembershipReward
    (A : Finset G) (hA : A.Nonempty) (hproper : A ≠ Finset.univ)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1)
    (hβpos : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 < β phase player) :
    ¬ IsFinitePlayerPhaseNashCertificate selfMembershipReward A β
      (fun phase player hplayer => (hβpos phase player hplayer).le)
      hβ1 := by
  let owner : G := 0
  obtain ⟨phase, hownerInactive⟩ :=
    exists_not_mem_cyclicSchedule_active A hproper owner
  have hactiveNonempty :
      ((cyclicSchedule A).active phase.val).Nonempty := by
    rw [← Finset.card_pos, card_cyclicSchedule_active]
    exact hA.card_pos
  obtain ⟨opponent, hopponentActive⟩ := hactiveNonempty
  have hopponentNe : opponent ≠ owner := by
    intro hopponent
    subst opponent
    exact hownerInactive hopponentActive
  have hopponent : opponent ∈
      ((cyclicSchedule A).active phase.val).erase owner :=
    Finset.mem_erase.mpr ⟨hopponentNe, hopponentActive⟩
  have hcontracts :
      quittingStationaryFixedOpponentsContinueMass
        (cyclicPlayerPhaseRoots A β
          (fun p player hplayer => (hβpos p player hplayer).le)
          hβ1 phase) owner < 1 := by
    rw [quittingStationaryFixedOpponentsContinueMass_playerPhase]
    exact Math.Finset.prod_lt_one_of_mem
      (((cyclicSchedule A).active phase.val).erase owner)
      (fun player => 1 - β phase player)
      opponent hopponent
      (fun player hplayer _ => sub_nonneg.mpr
        (hβ1 phase player (Finset.mem_of_mem_erase hplayer)))
      (fun player hplayer _ => by
        linarith [hβpos phase player (Finset.mem_of_mem_erase hplayer)])
      (sub_lt_self 1 (hβpos phase opponent hopponentActive))
  have hpure :
      cyclicPlayerPhaseRoots A β
          (fun p player hplayer => (hβpos p player hplayer).le)
          hβ1 phase owner = PMF.pure false := by
    have hownerInactive' :
        owner ∉ orbitSchedule A (translationClock A phase.val) :=
      hownerInactive
    simp [cyclicPlayerPhaseRoots, hownerInactive']
  exact not_forall_canonicalWord_isZeroNash_selfMembershipReward
    owner
    (cyclicPlayerPhaseRoots A β
      (fun p player hplayer => (hβpos p player hplayer).le)
      hβ1)
    phase hpure hcontracts

/-- The proposed universal common-hazard producer is false for every
nonempty proper block. -/
theorem not_forall_reward_finiteCyclicNashCertificate
    (A : Finset G) (hA : A.Nonempty)
    (hproper : A ≠ Finset.univ)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β ≤ 1) :
    ¬ ∀ reward : {S : Finset G // S.Nonempty} → Payoff G,
      IsFiniteCyclicNashCertificate reward A β hβpos.le hβ1 := by
  intro hproducer
  exact not_finiteCyclicNashCertificate_selfMembershipReward
    A hA hproper β hβpos hβ1 (hproducer selfMembershipReward)

/-- The proposed universal phase-varying producer is false as well. -/
theorem not_forall_reward_finitePhaseHazardNashCertificate
    (A : Finset G) (hA : A.Nonempty)
    (hproper : A ≠ Finset.univ)
    (β : Fin (Fintype.card (TranslationPhase A)) → ℝ)
    (hβpos : ∀ phase, 0 < β phase)
    (hβ1 : ∀ phase, β phase ≤ 1) :
    ¬ ∀ reward : {S : Finset G // S.Nonempty} → Payoff G,
      IsFinitePhaseHazardNashCertificate reward A β
        (fun phase => (hβpos phase).le)
        hβ1 := by
  intro hproducer
  exact not_finitePhaseHazardNashCertificate_selfMembershipReward
    A hA hproper β hβpos hβ1 (hproducer selfMembershipReward)

/-- The proposed universal player-and-phase-hazard producer is false as well. -/
theorem not_forall_reward_finitePlayerPhaseNashCertificate
    (A : Finset G) (hA : A.Nonempty) (hproper : A ≠ Finset.univ)
    (β : Fin (Fintype.card (TranslationPhase A)) → G → ℝ)
    (hβ1 : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → β phase player ≤ 1)
    (hβpos : ∀ phase player,
      player ∈ (cyclicSchedule A).active phase.val → 0 < β phase player) :
    ¬ ∀ reward : {S : Finset G // S.Nonempty} → Payoff G,
      IsFinitePlayerPhaseNashCertificate reward A β
        (fun phase player hplayer => (hβpos phase player hplayer).le)
        hβ1 := by
  intro hproducer
  exact not_finitePlayerPhaseNashCertificate_selfMembershipReward
    A hA hproper β hβ1 hβpos (hproducer selfMembershipReward)

/-- In particular, no prescribed proper common-hazard `4/5` word is a
universal exact-Nash carrier. -/
theorem fourOfFive_not_finiteCyclicNashCertificate_selfMembershipReward
    (A : Finset G) (hA : A.card = 4)
    (hG : Fintype.card G = 5)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β ≤ 1) :
    ¬ IsFiniteCyclicNashCertificate
      selfMembershipReward A β hβpos.le hβ1 := by
  have hnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : A.card < Fintype.card G := by omega
  exact not_finiteCyclicNashCertificate_selfMembershipReward_of_card_lt
    A hnonempty hcard β hβpos hβ1

/-! ## The obstruction game is nevertheless trivially solved -/

/-- Every player quits surely. -/
def allSureQuitRoot : G → PMF Bool := fun _ => PMF.pure true

omit [AddGroup G] in
/-- Against the all-sure-Quit root, every player has a surely quitting
opponent as soon as the population has at least two members. -/
theorem fixedOpponentsContinueMass_allSureQuitRoot_eq_zero
    (hG : 1 < Fintype.card G) (who : G) :
    quittingStationaryFixedOpponentsContinueMass
      (allSureQuitRoot : G → PMF Bool) who = 0 := by
  obtain ⟨opponent, hne⟩ := Fintype.exists_ne_of_one_lt_card hG who
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ opponent)
  simp [allSureQuitRoot, Function.update_of_ne hne]

omit [AddGroup G] [DecidableEq G] in
/-- The all-sure-Quit root absorbs immediately. -/
theorem stationaryContinueMass_allSureQuitRoot_eq_zero (owner : G) :
    quittingStationaryContinueMass
      (allSureQuitRoot : G → PMF Bool) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ owner)
  simp [allSureQuitRoot]

omit [AddGroup G] in
/-- Constant one is the exact Bellman value of all-sure-Quit play. -/
theorem one_eq_rootSuccessorPayoff_allSureQuit
    : (fun _ : G => (1 : ℝ)) =
      quittingRootSuccessorPayoff selfMembershipReward
        (fun _ : G => (1 : ℝ)) allSureQuitRoot := by
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_selfMembershipReward]
  simp [allSureQuitRoot]

omit [AddGroup G] in
/-- All-sure-Quit is exact endpoint Nash against every continuation value. -/
theorem allSureQuitRoot_isZeroEndpointNash_selfMembershipReward_anyTail
    (tail : Payoff G) (hG : 1 < Fintype.card G) :
    IsεQuittingRootEndpointNash selfMembershipReward
      tail 0 allSureQuitRoot := by
  intro who
  have hmass := fixedOpponentsContinueMass_allSureQuitRoot_eq_zero hG who
  have hdiff : quittingRootEndpointDifference
      selfMembershipReward tail allSureQuitRoot who = 1 := by
    rw [quittingRootEndpointDifference,
      quittingRootQuitPayoff_selfMembershipReward,
      quittingRootContinuePayoff_selfMembershipReward, hmass]
    norm_num
  rw [hdiff]
  simp [allSureQuitRoot]

omit [AddGroup G] in
/-- All-sure-Quit is exact endpoint Nash for the membership reward. -/
theorem allSureQuitRoot_isZeroEndpointNash_selfMembershipReward
    (hG : 1 < Fintype.card G) :
    IsεQuittingRootEndpointNash selfMembershipReward
      (fun _ : G => (1 : ℝ)) 0 allSureQuitRoot :=
  allSureQuitRoot_isZeroEndpointNash_selfMembershipReward_anyTail
    (fun _ : G => (1 : ℝ)) hG

/-! ## Adaptive saturation repairs this example at `K = N` -/

/-- Sure Quit at every phase. -/
def allSurePhaseHazard (A : Finset G) :
    Fin (Fintype.card (TranslationPhase A)) → ℝ := fun _ => 1

@[simp] theorem allSurePhaseHazard_pos (A : Finset G) :
    ∀ phase, 0 < allSurePhaseHazard A phase := by
  simp [allSurePhaseHazard]

@[simp] theorem allSurePhaseHazard_le_one (A : Finset G) :
    ∀ phase, allSurePhaseHazard A phase ≤ 1 := by
  simp [allSurePhaseHazard]

omit [AddGroup G] [Fintype G] [DecidableEq G] in
/-- The unit quitting coin is pure Quit. -/
theorem quittingHazardCoin_one_eq_pure_true :
    quittingHazardCoin 1 (by norm_num) (by norm_num) = PMF.pure true := by
  apply PMF.ext
  intro action
  cases action <;>
    simp [quittingHazardCoin, PMF.ofFintype_apply]

/-- On the full block, the sure phase-hazard word is exactly all-sure-Quit. -/
theorem cyclicPhaseHazardRoots_univ_allSure_eq
    (phase : Fin (Fintype.card
      (TranslationPhase (Finset.univ : Finset G)))) :
    cyclicPhaseHazardRoots (Finset.univ : Finset G)
        (allSurePhaseHazard Finset.univ)
        (fun p => (allSurePhaseHazard_pos Finset.univ p).le)
        (allSurePhaseHazard_le_one Finset.univ) phase =
      allSureQuitRoot := by
  have hactive :
      (cyclicSchedule (Finset.univ : Finset G)).active phase.val =
        Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [card_cyclicSchedule_active, Finset.card_univ]
  funext who
  change quittingActiveRoot
      ((cyclicSchedule (Finset.univ : Finset G)).active phase.val)
      (fun _ => quittingHazardCoin 1 (by norm_num) (by norm_num)) who =
        PMF.pure true
  rw [hactive]
  simp [quittingActiveRoot, quittingHazardCoin_one_eq_pure_true]

/-- The self-membership game does have a finite exact cyclic Nash
certificate after adaptive support saturation to the full `N/N` block and
admission of the sure-Quit boundary. -/
theorem fullSupport_allSure_isFinitePhaseHazardNashCertificate
    (hG : 1 < Fintype.card G) :
    IsFinitePhaseHazardNashCertificate selfMembershipReward
      (Finset.univ : Finset G)
      (allSurePhaseHazard Finset.univ)
      (fun _p => (allSurePhaseHazard_pos Finset.univ _p).le)
      (allSurePhaseHazard_le_one Finset.univ) := by
  intro phase
  rw [cyclicPhaseHazardRoots_univ_allSure_eq]
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    selfMembershipReward _ allSureQuitRoot).mp
  exact allSureQuitRoot_isZeroEndpointNash_selfMembershipReward_anyTail _ hG

/-- The phase-hazard compiler consumes the saturated boundary certificate. -/
theorem selfMembershipReward_fullSupportCyclicUniformPayoff
    (hG : 1 < Fintype.card G)
    (initial : Fin (Fintype.card
      (TranslationPhase (Finset.univ : Finset G)))) :
    (quittingGame selfMembershipReward).IsUniformEquilibriumPayoff none
      (cyclicPhaseHazardTerminalValues selfMembershipReward
        (Finset.univ : Finset G)
        (allSurePhaseHazard Finset.univ)
        (fun p => (allSurePhaseHazard_pos Finset.univ p).le)
        (allSurePhaseHazard_le_one Finset.univ) initial) := by
  exact isUniformEquilibriumPayoff_of_finitePhaseHazardNashCertificate
    selfMembershipReward (Finset.univ : Finset G)
      ⟨0, Finset.mem_univ _⟩ hG
      (allSurePhaseHazard Finset.univ)
      (allSurePhaseHazard_pos Finset.univ)
      (allSurePhaseHazard_le_one Finset.univ)
      (fullSupport_allSure_isFinitePhaseHazardNashCertificate hG) initial

omit [AddGroup G] in
/-- The counterexample to prescribed cyclic feasibility has the uniform
equilibrium payoff `1`: every player quitting surely is a contracting exact
stationary certificate. -/
theorem selfMembershipReward_hasUniformEquilibriumPayoff
    (hG : 1 < Fintype.card G) :
    (quittingGame selfMembershipReward).IsUniformEquilibriumPayoff
      none (fun _ : G => (1 : ℝ)) := by
  let witness : G := Classical.choice
    (Fintype.card_pos_iff.mp (Nat.zero_lt_one.trans hG))
  apply isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    selfMembershipReward allSureQuitRoot (fun _ : G => (1 : ℝ))
  · rw [stationaryContinueMass_allSureQuitRoot_eq_zero witness]
    norm_num
  · exact one_eq_rootSuccessorPayoff_allSureQuit
  · exact allSureQuitRoot_isZeroEndpointNash_selfMembershipReward hG
  · intro who
    rw [fixedOpponentsContinueMass_allSureQuitRoot_eq_zero hG who]
    norm_num

end


end CyclicKofNFeasibilityObstruction

end GameTheory
