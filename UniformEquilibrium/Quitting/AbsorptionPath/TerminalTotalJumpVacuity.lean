/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.DiscreteRootSequencePath

/-!
# Vacuity of sequential perfection at a terminal total jump

The printed absorption-path perfection predicate tests a jump only when its
post-jump total is strictly below one.  Consequently every nonempty quitting
game admits a sequentially zero-perfect absorption path that places all mass
on one sure singleton jump.  The construction is independent of the reward.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The constant root sequence in which one owner quits surely and every
other player continues surely. -/
def sureSoloTerminalJumpRoots (owner : ι) : ℕ → ι → PMF Bool :=
  fun _ ↦ Function.update quittingAllContinueRoot owner (PMF.pure true)

/-- The sure-solo sequence has zero survival immediately after its first
row. -/
def sureSoloTerminalJumpCertificate (owner : ι) :
    QuittingFiniteRootSequenceAbsorption (sureSoloTerminalJumpRoots owner) where
  cutoff := 0
  survival_zero := by
    rw [quittingRootSequenceSurvival_succ]
    rw [quittingRootSequenceSurvival_zero, one_mul,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    exact Finset.prod_eq_zero (Finset.mem_univ owner) (by
      simp [sureSoloTerminalJumpRoots])

/-- The absorption path consisting of the sure singleton jump at clock zero. -/
def sureSoloTerminalJumpAbsorptionPath (owner : ι) :
    AbsorptionPath (ι := ι) :=
  (sureSoloTerminalJumpCertificate owner).absorptionPath

private theorem sureSoloTerminalJumpClock_one (owner : ι) :
    quittingRootSequenceClock (sureSoloTerminalJumpRoots owner) 1 = 1 := by
  have hzero := (sureSoloTerminalJumpCertificate owner).survival_zero
  change quittingRootSequenceSurvival (sureSoloTerminalJumpRoots owner) 1 = 0
    at hzero
  rw [quittingRootSequenceClock, hzero]
  ring

private theorem sureSoloTerminalJumpClock_zero_lt_one (owner : ι) :
    quittingRootSequenceClock (sureSoloTerminalJumpRoots owner) 0 <
      quittingRootSequenceClock (sureSoloTerminalJumpRoots owner) 1 := by
  rw [quittingRootSequenceClock_zero, sureSoloTerminalJumpClock_one]
  norm_num

/-- Every jump of the sure-solo path is terminal in total mass. -/
theorem pathTotal_sureSoloTerminalJumpAbsorptionPath_eq_one_of_mem_jumps
    (owner : ι) {time : ℝ}
    (htime : time ∈ pathJumps (sureSoloTerminalJumpAbsorptionPath owner).1) :
    pathTotal (sureSoloTerminalJumpAbsorptionPath owner).1 time = 1 := by
  let certificate := sureSoloTerminalJumpCertificate owner
  obtain ⟨stage, hstage, htimeEq, hpositive, _⟩ :=
    certificate.exists_positive_source_stage htime
  have hstageZero : stage = 0 := Nat.eq_zero_of_le_zero hstage
  subst stage
  rw [htimeEq]
  exact (certificate.pathTotal_cadlagPath_at_positive_stage le_rfl hpositive).trans
    (sureSoloTerminalJumpClock_one owner)

/-- Clock zero is a terminal total jump of the sure-solo path. -/
theorem zero_mem_jumps_sureSoloTerminalJumpAbsorptionPath (owner : ι) :
    0 ∈ pathJumps (sureSoloTerminalJumpAbsorptionPath owner).1 := by
  let certificate := sureSoloTerminalJumpCertificate owner
  have hsum : (∑ coalition,
      quittingRootSequenceStageCoalitionMass
        (sureSoloTerminalJumpRoots owner) 0 coalition) = 1 := by
    rw [
      QuittingFiniteRootSequenceAbsorption.sum_quittingRootSequenceStageCoalitionMass_eq_clock_sub,
      sureSoloTerminalJumpClock_one, quittingRootSequenceClock_zero]
    ring
  have hsumNe : (∑ coalition ∈ Finset.univ,
      quittingRootSequenceStageCoalitionMass
        (sureSoloTerminalJumpRoots owner) 0 coalition) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨coalition, _, hmass⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    hsumNe
  refine ⟨by norm_num, coalition, ?_⟩
  have hjump := certificate.pathJump_cadlagPath_at_positive_stage (stage := 0)
    (by simp [certificate, sureSoloTerminalJumpCertificate])
    (sureSoloTerminalJumpClock_zero_lt_one owner) coalition
  rw [quittingRootSequenceClock_zero] at hjump
  exact hjump.symm ▸ hmass

/-- Under the printed Definition 4.13 jump guard, the sure-solo terminal jump
is sequentially zero-perfect for every reward table: jump perfection is not
tested after total mass reaches one, and the only path time is one. -/
theorem isSequentiallyPerfect_sureSoloTerminalJumpAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    IsSequentiallyPerfectAbsorptionPath reward
      (sureSoloTerminalJumpAbsorptionPath owner) 0 := by
  intro who
  constructor
  · intro time htime hnonterminal
    rw [pathTotal_sureSoloTerminalJumpAbsorptionPath_eq_one_of_mem_jumps
      owner htime] at hnonterminal
    exact (lt_irrefl 1 hnonterminal).elim
  · intro time htime hneOne
    change time ∈ pathTimes
      (sureSoloTerminalJumpCertificate owner).cadlagPath at htime
    rw [(sureSoloTerminalJumpCertificate owner).pathTimes_cadlagPath] at htime
    exact (hneOne htime).elim

/-- Every finite nonempty quitting game has a sequentially zero-perfect path
whose clock-zero jump raises total absorption mass to one, regardless of its
rewards.  This is the literal vacuity in the printed absorption-path endpoint
condition. -/
theorem exists_sequentiallyZeroPerfectAbsorptionPath_with_terminalTotalJumpAtZero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ path : AbsorptionPath (ι := ι),
      IsSequentiallyPerfectAbsorptionPath reward path 0 ∧
        0 ∈ pathJumps path.1 ∧ pathTotal path.1 0 = 1 := by
  let owner : ι := Classical.choice inferInstance
  exact ⟨sureSoloTerminalJumpAbsorptionPath owner,
    isSequentiallyPerfect_sureSoloTerminalJumpAbsorptionPath reward owner,
    zero_mem_jumps_sureSoloTerminalJumpAbsorptionPath owner,
    pathTotal_sureSoloTerminalJumpAbsorptionPath_eq_one_of_mem_jumps owner
      (zero_mem_jumps_sureSoloTerminalJumpAbsorptionPath owner)⟩

end GameTheory.QuittingAbsorptionPath
