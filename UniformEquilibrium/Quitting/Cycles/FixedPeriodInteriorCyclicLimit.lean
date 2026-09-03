/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.InteriorCyclicDebtEscape
import UniformEquilibrium.Quitting.Root.NashDefectContinuity

/-!
# Exact fixed-period limits of interior cyclic blocks

At one fixed period, reward-bounded cyclic Bellman points form a compact
finite product.  If the local Nash errors vanish, every cluster point is an
exact cyclic Nash--Bellman word.  If one fixed player's opponent absorption
also vanishes, every other player surely Continues at every phase of the
limit word.  The limit need not absorb and is not asserted to be terminal
Nash.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- The Nash--Bellman point displayed by an interior cyclic block at one
phase, with its product root written in the compact simplex coordinates. -/
def InteriorApproximateNashCyclicBlock.point
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (phase : Fin (m + 1)) : QuittingNashBellmanPoint ι :=
  (block.value phase, quittingSimplexOfRoot (block.cycle phase))

@[simp] theorem InteriorApproximateNashCyclicBlock.point_value
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (phase : Fin (m + 1)) :
    (block.point phase).1 = block.value phase := rfl

@[simp] theorem InteriorApproximateNashCyclicBlock.point_root
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (phase : Fin (m + 1)) :
    quittingRootOfSimplex (block.point phase).2 = block.cycle phase := by
  exact quittingRootOfSimplex_simplexOfRoot _

/-- A strict subsequential exact limit of fixed-period interior cyclic
blocks.  `opponents_continue_sure` states the complete exceptional-face
conclusion: only `owner` may retain Quit mass at any limit phase. -/
structure FixedPeriodExactNashCyclicLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock reward m (error n))
    (owner : ι) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  point : Fin (m + 1) → QuittingNashBellmanPoint ι
  sourcePoint_tendsto : Tendsto (fun n phase ↦ (block (select n)).point phase)
    atTop (nhds point)
  value_bound : ∀ phase who,
    |(point phase).1 who| ≤ quittingRewardBound reward
  bellman : ∀ phase,
    (point phase).1 = quittingRootSuccessorPayoff reward
      (point (finRotate (m + 1) phase)).1
      (quittingRootOfSimplex (point phase).2)
  rootNash : ∀ phase,
    IsεQuittingRootNash reward
      (point (finRotate (m + 1) phase)).1 0
      (quittingRootOfSimplex (point phase).2)
  opponents_continue_sure : ∀ phase other, other ≠ owner →
    quittingRootOfSimplex (point phase).2 other = PMF.pure false

/-- The fixed-period cyclic source points remain in the canonical compact
reward box. -/
theorem InteriorApproximateNashCyclicBlock.point_mem_nashBellmanBox
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (phase : Fin (m + 1)) :
    block.point phase ∈ quittingNashBellmanBox (quittingRewardBound reward) := by
  constructor
  · intro who
    exact (abs_le.mp (block.value_bound phase who)).1
  · intro who
    exact (abs_le.mp (block.value_bound phase who)).2

/-- Fixed-period interior cyclic blocks whose local errors and one fixed
player's opponent absorption vanish have an exact cyclic Nash--Bellman
cluster point supported only on that player. -/
theorem nonempty_fixedPeriodExactNashCyclicLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock reward m (error n))
    (owner : ι)
    (herror : Tendsto error atTop (nhds 0))
    (hopponent : Tendsto (fun n ↦
      quittingCyclicOpponentAbsorptionMass (block n).cycle owner)
      atTop (nhds 0)) :
    Nonempty (FixedPeriodExactNashCyclicLimit reward error block owner) := by
  let sourcePoint : ℕ → Fin (m + 1) → QuittingNashBellmanPoint ι :=
    fun n phase ↦ (block n).point phase
  let carrier : Set (Fin (m + 1) → QuittingNashBellmanPoint ι) :=
    {path | ∀ phase,
      path phase ∈ quittingNashBellmanBox (quittingRewardBound reward)}
  have hcarrierCompact : IsCompact carrier := by
    apply isCompact_pi_infinite
    intro phase
    exact quittingNashBellmanBox_isCompact (ι := ι)
      (quittingRewardBound reward)
  have hsourceMem : ∀ n, sourcePoint n ∈ carrier := by
    intro n phase
    exact (block n).point_mem_nashBellmanBox phase
  obtain ⟨point, hpointMem, select, hselect, hpoint⟩ :=
    hcarrierCompact.tendsto_subseq hsourceMem
  have hpointPhase : ∀ phase, Tendsto (fun n ↦
      sourcePoint (select n) phase) atTop (nhds (point phase)) := by
    intro phase
    exact ((continuous_apply phase).tendsto point).comp hpoint
  have hbellman : ∀ phase,
      (point phase).1 = quittingRootSuccessorPayoff reward
        (point (finRotate (m + 1) phase)).1
        (quittingRootOfSimplex (point phase).2) := by
    intro phase
    let currentValue : (Fin (m + 1) → QuittingNashBellmanPoint ι) → Payoff ι :=
      fun path ↦ (path phase).1
    let edgeData : (Fin (m + 1) → QuittingNashBellmanPoint ι) →
        Payoff ι × QuittingRootSimplex ι := fun path ↦
      ((path (finRotate (m + 1) phase)).1, (path phase).2)
    have hcurrentContinuous : Continuous currentValue := by
      dsimp only [currentValue]
      fun_prop
    have hedgeContinuous : Continuous edgeData := by
      dsimp only [edgeData]
      fun_prop
    have hleft : Tendsto (fun n ↦ currentValue (sourcePoint (select n)))
        atTop (nhds (currentValue point)) :=
      (hcurrentContinuous.tendsto point).comp hpoint
    have hright : Tendsto (fun n ↦
        quittingRootSuccessorPayoff reward
          (edgeData (sourcePoint (select n))).1
          (quittingRootOfSimplex
            (edgeData (sourcePoint (select n))).2)) atTop
        (nhds (quittingRootSuccessorPayoff reward
          (edgeData point).1 (quittingRootOfSimplex (edgeData point).2))) :=
      ((continuous_quittingRootSuccessorPayoff_simplex reward).comp
        hedgeContinuous).tendsto point |>.comp hpoint
    have heq : ∀ n,
        currentValue (sourcePoint (select n)) =
          quittingRootSuccessorPayoff reward
            (edgeData (sourcePoint (select n))).1
            (quittingRootOfSimplex
              (edgeData (sourcePoint (select n))).2) := by
      intro n
      simpa [currentValue, edgeData, sourcePoint,
        InteriorApproximateNashCyclicBlock.point] using
        (block (select n)).bellman phase
    exact tendsto_nhds_unique hleft (hright.congr' <|
      Filter.Eventually.of_forall fun n ↦ (heq n).symm)
  have hrootNash : ∀ phase,
      IsεQuittingRootNash reward
        (point (finRotate (m + 1) phase)).1 0
        (quittingRootOfSimplex (point phase).2) := by
    intro phase
    apply (isεQuittingRootNash_iff_coordinateNashDefect_le
      reward _ 0 _).2
    intro who
    let edgeData : (Fin (m + 1) → QuittingNashBellmanPoint ι) →
        Payoff ι × QuittingRootSimplex ι := fun path ↦
      ((path (finRotate (m + 1) phase)).1, (path phase).2)
    have hedgeContinuous : Continuous edgeData := by
      dsimp only [edgeData]
      fun_prop
    have hdefect : Tendsto (fun n ↦
        quittingRootCoordinateNashDefect reward
          (edgeData (sourcePoint (select n))).1
          (quittingRootOfSimplex
            (edgeData (sourcePoint (select n))).2) who) atTop
        (nhds (quittingRootCoordinateNashDefect reward
          (edgeData point).1
          (quittingRootOfSimplex (edgeData point).2) who)) :=
      ((continuous_quittingRootCoordinateNashDefect_simplex reward who).comp
        hedgeContinuous).tendsto point |>.comp hpoint
    have herrorSelected : Tendsto (fun n ↦ error (select n)) atTop (nhds 0) :=
      herror.comp hselect.tendsto_atTop
    apply le_of_tendsto_of_tendsto hdefect herrorSelected
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa [edgeData, sourcePoint,
        InteriorApproximateNashCyclicBlock.point] using
          (isεQuittingRootNash_iff_coordinateNashDefect_le
            reward _ (error (select n)) _).1
            ((block (select n)).rootNash phase) who
  have hopponentSelected : Tendsto (fun n ↦
      quittingCyclicOpponentAbsorptionMass
        (block (select n)).cycle owner) atTop (nhds 0) :=
    hopponent.comp hselect.tendsto_atTop
  have hopponentsContinue : ∀ phase other, other ≠ owner →
      quittingRootOfSimplex (point phase).2 other = PMF.pure false := by
    intro phase other hne
    have hquitNonneg : ∀ n, 0 ≤
        ((block (select n)).cycle phase other true).toReal :=
      fun n ↦ ENNReal.toReal_nonneg
    have hquitLe : ∀ n,
        ((block (select n)).cycle phase other true).toReal ≤
          quittingCyclicOpponentAbsorptionMass
            (block (select n)).cycle owner := by
      intro n
      let continueProbability : Fin (m + 1) → ℝ := fun stage ↦
        ((block (select n)).cycle stage other false).toReal
      have hsplit := Finset.mul_prod_erase Finset.univ continueProbability
        (Finset.mem_univ phase)
      have hrestLe : (∏ stage ∈ Finset.univ.erase phase,
          continueProbability stage) ≤ 1 :=
        Finset.prod_le_one
          (fun stage _ ↦ ENNReal.toReal_nonneg)
          (fun stage _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top
            (((block (select n)).cycle stage other).coe_le_one false))
      have hphaseNonneg : 0 ≤ continueProbability phase := ENNReal.toReal_nonneg
      have hproductLe : (∏ stage, continueProbability stage) ≤
          continueProbability phase := by
        calc
          (∏ stage, continueProbability stage) = continueProbability phase *
              (∏ stage ∈ Finset.univ.erase phase, continueProbability stage) :=
            hsplit.symm
          _ ≤ continueProbability phase * 1 :=
            mul_le_mul_of_nonneg_left hrestLe hphaseNonneg
          _ = continueProbability phase := mul_one _
      have hsum := quittingRoot_continueProbability_add_quitProbability
        ((block (select n)).cycle phase) other
      have hplayerLe : quittingCyclicPlayerAbsorptionMass
          (block (select n)).cycle other ≤
          quittingCyclicOpponentAbsorptionMass
            (block (select n)).cycle owner :=
        quittingCyclicPlayerAbsorptionMass_le_opponentAbsorptionMass_of_ne
          (block (select n)).cycle hne
      unfold quittingCyclicPlayerAbsorptionMass at hplayerLe
      dsimp only [continueProbability] at hproductLe
      linarith
    have hquitZero : Tendsto (fun n ↦
        ((block (select n)).cycle phase other true).toReal)
        atTop (nhds 0) :=
      squeeze_zero hquitNonneg hquitLe hopponentSelected
    have hlimitQuit : Tendsto (fun n ↦
        ((block (select n)).cycle phase other true).toReal) atTop
        (nhds ((quittingRootOfSimplex (point phase).2 other true).toReal)) := by
      let quitCoordinate :
          (Fin (m + 1) → QuittingNashBellmanPoint ι) → ℝ :=
        fun path ↦ (path phase).2 other true
      have hquitContinuous : Continuous quitCoordinate := by
        dsimp only [quitCoordinate]
        exact (continuous_apply true).comp
          (continuous_subtype_val.comp
            ((continuous_apply other).comp
              (continuous_snd.comp (continuous_apply phase))))
      have hquitCoordinate := (hquitContinuous.tendsto point).comp hpoint
      change Tendsto (fun n ↦
        (sourcePoint (select n) phase).2 other true) atTop
          (nhds ((point phase).2 other true)) at hquitCoordinate
      rw [quittingRootOfSimplex_apply_toReal]
      simpa only [sourcePoint, InteriorApproximateNashCyclicBlock.point,
        quittingSimplexOfRoot,
        Math.ProbabilityMassFunction.coe_stdSimplexEquiv_apply,
        Math.ProbabilityMassFunction.toVector] using hquitCoordinate
    have hzero :
        (quittingRootOfSimplex (point phase).2 other true).toReal = 0 :=
      tendsto_nhds_unique hlimitQuit hquitZero
    exact eq_pure_false_of_apply_true_toReal_eq_zero _ hzero
  exact ⟨{
    select := select
    select_strictMono := hselect
    point := point
    sourcePoint_tendsto := hpoint
    value_bound := fun phase who ↦ abs_le.mpr
      ⟨(hpointMem phase).1 who, (hpointMem phase).2 who⟩
    bellman := hbellman
    rootNash := hrootNash
    opponents_continue_sure := hopponentsContinue
  }⟩

end GameTheory
