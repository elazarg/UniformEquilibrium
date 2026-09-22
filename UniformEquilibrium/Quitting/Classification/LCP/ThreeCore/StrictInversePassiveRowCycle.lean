/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.PositiveInverseCyclicLabelAdapter
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Classification.ThreePlayer.CyclicCompiler
import UniformEquilibrium.Quitting.Cycles.BalancedSingletonPassiveRows
import UniformEquilibrium.Quitting.Root.PlayerReindex

/-!
# Strict inverse three-cycle producer for passive-row inheritance

The strictly positive inverse of the literal child singleton-difference
matrix supplies the three-owner balanced cycle. Nonnegative factorization
of the remaining singleton rows then gives a uniform payoff for the parent.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open Math.LinearProgramming

private theorem solo_reindex
    {κ : Type} (e : κ ≃ Fin 3)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ)
    (owner who : Fin 3) :
    quittingSoloReward (quittingRewardReindex e reward) owner who =
      quittingSoloReward reward (e.symm owner) (e.symm who) := by
  simp [quittingSoloReward, quittingRewardReindex, quittingCoalitionEquiv]

/-- The existing right-cycle data packaged as a balanced certificate. -/
def RightSingletonCycle.toBalancedCertificate
    {reward : QuittingReward3} (cycle : RightSingletonCycle reward) :
    BalancedSingletonCycleCertificate (L := 3) reward := by
  let hazard : Fin 3 → ℝ :=
    ![rightAlpha reward, rightBeta reward, rightGamma reward]
  refine {
    owner := rightOwner
    hazard := hazard
    coarse := rightCoarse reward
    initial := 0
    hazard_nonneg := ?_
    hazard_lt_one := ?_
    arc := ?_
    active := right_coarse_active cycle
    soloFloor := right_coarse_floor cycle
    opponentDivergence := ?_ }
  · intro phase
    have hpos := right_rates_pos cycle
    fin_cases phase <;> simp [hazard] <;> linarith
  · intro phase
    have hlt := right_rates_lt_one cycle
    fin_cases phase <;> simp [hazard] <;> linarith
  · simpa [hazard] using right_coarse_arc cycle
  · intro who
    have hpos := right_rates_pos cycle
    fin_cases who
    · exact ⟨1, by simp [rightOwner], by simpa [hazard] using hpos.2.1⟩
    · exact ⟨2, by simp [rightOwner], by simpa [hazard] using hpos.2.2⟩
    · exact ⟨0, by simp [rightOwner], by simpa [hazard] using hpos.1⟩

/-- A directed-cycle singleton-difference matrix has the concrete
`RightSingletonCycle` inequalities consumed by the existing compiler. -/
theorem rightSingletonCycle_of_directedSoloMatrix
    (reward : QuittingReward3) (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : normalizedSoloMatrix reward =
      directedCycleMatrix a b c d e f) :
    RightSingletonCycle reward := by
  have hentry (who owner : Fin 3) :
      quittingSoloReward reward owner who - quittingSoloReward reward who who =
        directedCycleMatrix a b c d e f who owner := by
    rw [← normalizedSoloMatrix_eq_soloReward_sub]
    exact congrFun (congrFun hmatrix who) owner
  have hp : rightP reward = a := by
    have h := hentry 0 1
    simp [directedCycleMatrix] at h
    dsimp [rightP]
    linarith
  have hq : rightQ reward = b := by
    have h := hentry 0 2
    simp [directedCycleMatrix] at h
    dsimp [rightQ]
    linarith
  have hr : rightR reward = d := by
    have h := hentry 1 2
    simp [directedCycleMatrix] at h
    dsimp [rightR]
    linarith
  have hs : rightS reward = c := by
    have h := hentry 1 0
    simp [directedCycleMatrix] at h
    dsimp [rightS]
    linarith
  have ht : rightT reward = e := by
    have h := hentry 2 0
    simp [directedCycleMatrix] at h
    dsimp [rightT]
    linarith
  have hu : rightU reward = f := by
    have h := hentry 2 1
    simp [directedCycleMatrix] at h
    dsimp [rightU]
    linarith
  refine {
    h01 := ?_
    h02 := ?_
    h21 := ?_
    h10 := ?_
    h02' := ?_
    h12 := ?_
    hdet := ?_ }
  · dsimp [rightP] at hp; linarith
  · dsimp [rightQ] at hq; linarith
  · dsimp [rightR] at hr; linarith
  · dsimp [rightS] at hs; linarith
  · dsimp [rightT] at ht; linarith
  · dsimp [rightU] at hu; linarith
  · change rightQ reward * rightS reward * rightU reward >
      rightP reward * rightR reward * rightT reward
    rw [hp, hq, hr, hs, ht, hu]
    simpa [cycleGap] using hgap

/-- Transport the right-oriented balanced cycle back from labeled coordinates. -/
def RightSingletonCycle.toBalancedCertificate_reindex
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ)
    (label : κ ≃ Fin 3)
    (cycle : RightSingletonCycle (quittingRewardReindex label reward)) :
    BalancedSingletonCycleCertificate (L := 3) reward := by
  let source := cycle.toBalancedCertificate
  refine {
    owner := fun phase => label.symm (source.owner phase)
    hazard := source.hazard
    coarse := fun phase who => source.coarse phase (label who)
    initial := source.initial
    hazard_nonneg := source.hazard_nonneg
    hazard_lt_one := source.hazard_lt_one
    arc := ?_
    active := ?_
    soloFloor := ?_
    opponentDivergence := ?_ }
  · intro phase
    funext who
    have h := congrFun (source.arc phase) (label who)
    simpa [quittingSingletonArcPayoff, solo_reindex] using h
  · intro phase
    have h := source.active phase
    simpa [solo_reindex] using h
  · intro phase who
    have h := source.soloFloor phase (label who)
    simpa [solo_reindex] using h
  · intro who
    obtain ⟨phase, hne, hpos⟩ := source.opponentDivergence (label who)
    exact ⟨phase, by
      intro heq
      apply hne
      simpa using congrArg label heq, hpos⟩

/-- Strictly positive inverse of the literal induced three-player matrix
constructs the child balanced certificate, with no cycle premise. -/
theorem exists_balancedCertificate_of_strictlyPositiveInverse_child
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hpositive : HasStrictlyPositiveInverse
      (normalizedSoloMatrix (quittingDeleteReward reward deleted))) :
    Nonempty (BalancedSingletonCycleCertificate (L := 3)
      (quittingDeleteReward reward deleted)) := by
  let childReward := quittingDeleteReward reward deleted
  let matrix := normalizedSoloMatrix childReward
  obtain ⟨label, a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hgap, hmatrix⟩ :=
    ThreeCoreCyclicLabelAdapter.exists_directedCycle_labeling_of_strictlyPositiveInverse
      matrix hcard (normalizedSoloMatrix_diagonal childReward) hpositive
  let reward3 := quittingRewardReindex label childReward
  have hsolo : normalizedSoloMatrix reward3 = reindexMatrix label matrix := by
    funext who owner
    rw [normalizedSoloMatrix_eq_soloReward_sub]
    simp only [reward3, reindexMatrix, solo_reindex, matrix]
    rw [normalizedSoloMatrix_eq_soloReward_sub]
  have hmatrix3 : normalizedSoloMatrix reward3 =
      directedCycleMatrix a b c d e f := hsolo.trans hmatrix
  let cycle := rightSingletonCycle_of_directedSoloMatrix reward3 a b c d e f
    ha hb hc hd he hf hgap hmatrix3
  exact ⟨RightSingletonCycle.toBalancedCertificate_reindex childReward label cycle⟩

/-- Raw strict inverse and passive singleton rows yield a fixed parent
uniform-equilibrium payoff. The rows are literal reward-table equalities. -/
theorem exists_uniformEquilibriumPayoff_of_strictInverse_passiveRows
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (hcard : Fintype.card {who : ι // ¬ deleted who} = 3)
    (hpositive : HasStrictlyPositiveInverse
      (normalizedSoloMatrix (quittingDeleteReward reward deleted)))
    (rows : PassiveSingletonRowFactorization reward deleted) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨child⟩ := exists_balancedCertificate_of_strictlyPositiveInverse_child
    reward deleted hcard hpositive
  exact ⟨rows.coarse child child.initial, rows.isUniformEquilibriumPayoff child⟩

end GameTheory
