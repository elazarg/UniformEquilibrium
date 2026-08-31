/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticCapSwitchFullChord
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawResetCube
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization

/-!
# Source transfer for pair-deleted cap-switch clocks

A face of a frozen stopping-law reset cube changes a pair-deleted survival
event by at most the sum of its reset scales.  This is the literal finite
source-transfer estimate used before compactifying an escaping disagreement
mark.

The theorem is a finite-event comparison.  It does not assert source
chronology, tightness at `Never`, or convergence of any supplied sequence.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem abs_hazardSurvival_mixture_sub_le_scale
    (source target : ℕ → PMF Bool) (scale : ℝ)
    (hscale0 : 0 ≤ scale) (hscale1 : scale ≤ 1) (cutoff : ℕ) :
    |quittingHazardSurvival
          (BooleanHazard.convexMix source target scale hscale0 hscale1) cutoff -
        quittingHazardSurvival source cutoff| ≤ scale := by
  rw [quittingHazardSurvival_convexMix]
  have hsource0 := quittingHazardSurvival_nonneg source cutoff
  have hsource1 := quittingHazardSurvival_le_one source cutoff
  have htarget0 := quittingHazardSurvival_nonneg target cutoff
  have htarget1 := quittingHazardSurvival_le_one target cutoff
  rw [show (1 - scale) * quittingHazardSurvival source cutoff +
      scale * quittingHazardSurvival target cutoff -
        quittingHazardSurvival source cutoff =
      scale * (quittingHazardSurvival target cutoff -
        quittingHazardSurvival source cutoff) by ring,
    abs_mul, abs_of_nonneg hscale0]
  have habs : |quittingHazardSurvival target cutoff -
      quittingHazardSurvival source cutoff| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

/-- A reset-cube face changes a pair-deleted survival event by at most the
sum of all face scales.  Coordinates deleted from the event may occur in the
sum, making the stated bound deliberately uniform. -/
theorem abs_quittingPairDeletedSurvivalWeight_resetCube_profile_sub_source_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (face : Finset ι) (mover observer : ι) (cutoff : ℕ) :
    |quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward (data.profile face))
          mover observer 0 cutoff -
        quittingPairDeletedSurvivalWeight
          (quittingProfileLiveRoot reward data.source)
          mover observer 0 cutoff| ≤
      ∑ player ∈ face, data.scale player := by
  let players := Finset.univ.erase mover
  let faceTail := fun player ↦ quittingHazardSurvival
    (fun stage ↦ quittingRootSequenceUpdate
      (quittingProfileLiveRoot reward (data.profile face)) observer
        quittingAlwaysContinueHazard stage player) cutoff
  let sourceTail := fun player ↦ quittingHazardSurvival
    (fun stage ↦ quittingRootSequenceUpdate
      (quittingProfileLiveRoot reward data.source) observer
        quittingAlwaysContinueHazard stage player) cutoff
  have hface0 : ∀ player ∈ players, 0 ≤ faceTail player := by
    intro player _
    exact quittingHazardSurvival_nonneg _ _
  have hface1 : ∀ player ∈ players, faceTail player ≤ 1 := by
    intro player _
    exact quittingHazardSurvival_le_one _ _
  have hsource0 : ∀ player ∈ players, 0 ≤ sourceTail player := by
    intro player _
    exact quittingHazardSurvival_nonneg _ _
  have hsource1 : ∀ player ∈ players, sourceTail player ≤ 1 := by
    intro player _
    exact quittingHazardSurvival_le_one _ _
  have hproduct := Math.abs_prod_sub_prod_le_sum_abs players faceTail sourceTail
    hface0 hface1 hsource0 hsource1
  have hcoordinate (player : ι) (hplayer : player ∈ players) :
      |faceTail player - sourceTail player| ≤
        if player ∈ face then data.scale player else 0 := by
    by_cases hobserver : player = observer
    · subst player
      have hzero : |faceTail observer - sourceTail observer| = 0 := by
        simp [faceTail, sourceTail, quittingRootSequenceUpdate,
          quittingAlwaysContinueHazard, quittingHazardSurvival_eq_prod]
      rw [hzero]
      split <;> simp_all [data.scale_nonneg]
    · by_cases hface : player ∈ face
      · rw [if_pos hface]
        simp only [faceTail, sourceTail, quittingRootSequenceUpdate]
        simp only [Function.update_of_ne hobserver]
        change |quittingHazardSurvival
              (quittingBehaviorLiveHazard reward (data.profile face player)) cutoff -
            quittingHazardSurvival
              (quittingBehaviorLiveHazard reward (data.source player)) cutoff| ≤
          data.scale player
        rw [data.profile_apply_of_mem face player hface,
          quittingBehaviorLiveHazard_stoppingLawMixture]
        exact abs_hazardSurvival_mixture_sub_le_scale
          (quittingBehaviorLiveHazard reward (data.source player))
          (quittingBehaviorLiveHazard reward (data.target player))
          (data.scale player) (data.scale_nonneg player)
            (data.scale_le_one player) cutoff
      · rw [if_neg hface]
        simp [faceTail, sourceTail, quittingRootSequenceUpdate, hobserver,
          quittingProfileLiveRoot, QuittingStoppingLawResetCubeData.profile,
          hface]
  have hsum : (∑ player ∈ players, |faceTail player - sourceTail player|) ≤
      ∑ player ∈ face, data.scale player := by
    calc
      (∑ player ∈ players, |faceTail player - sourceTail player|) ≤
          ∑ player ∈ players,
            if player ∈ face then data.scale player else 0 := by
        exact Finset.sum_le_sum fun player hplayer ↦ hcoordinate player hplayer
      _ = ∑ player ∈ players.filter (· ∈ face), data.scale player := by
        rw [Finset.sum_filter]
      _ ≤ ∑ player ∈ face, data.scale player := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro player hplayer
          exact (Finset.mem_filter.mp hplayer).2
        · intro player _ _
          exact data.scale_nonneg player
  unfold quittingPairDeletedSurvivalWeight
  rw [quittingOpponentSurvivalWeight_eq_prod_hazardSurvival,
    quittingOpponentSurvivalWeight_eq_prod_hazardSurvival]
  change |(∏ player ∈ players, faceTail player) -
      (∏ player ∈ players, sourceTail player)| ≤ _
  exact hproduct.trans hsum

end GameTheory
