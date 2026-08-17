/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Conditioned.Diffuse.Closure
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Classification.PreemptionGateDictionary
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification
import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance

/-!
# Solo structure of exact diffuse quitting tails

An *exact diffuse tail* is the data already carried by the canonical
counterexample seam of
`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/Seam.lean`,
read through the conditioning of
`UniformEquilibrium/Quitting/Cycles/PhantomBoundaryConditioning.lean`: a root
sequence `roots` with the exact policy recursion (`seam.tail_edge`, first
component), exact endpoint Nash at accuracy zero (`seam.tail_edge`, second
component), positive remaining eventual absorption at every date, vanishing
conditioned mesh, and a boundary equal to the annotation's limit
(`seam.value_tendsto` with `seam.limit.value`).  Active tightness — the
boundary coordinate of a recurrently active player is that player's singleton
reward — is `eventually_active_implies_limitValue_eq_singleton` at seam grade
and is recorded here as `limitValue_eq_soloReward_of_persistentlyActive`.

The file formalizes a coexistence obstruction for persistently active
players in exact diffuse tails.

* **Window transport** (`quittingTailConditionedValue_sub_soloReward_of_window`):
  across a window on which only `owner` may quit, the conditioned value's
  displacement from `owner`'s singleton reward is multiplied by the window's
  survival product.  Exact, no asymptotics.
* **T2, quantitative**
  (`survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow`): for one
  solo-`owner` window fenced on both sides by dates at which `spectator` is
  active, the window's absorbed conditioned charge times the absolute
  normalized solo matrix entry `M spectator owner` is at most a fixed multiple
  of the two fence meshes.
* **T2, asymptotic** (`normalizedSoloMatrix_eq_zero_of_fencedSoloWindows`):
  recurrent such windows with uniformly positive charge and vanishing mesh
  force `M spectator owner = 0`.
* **Margin form of the table condition**
  (`quittingZeroFreeSoloMatrix_iff_exists_soloMatrixMargin`): on a finite
  player set, having no vanishing off-diagonal entry is equivalent to a
  uniform positive lower bound `QuittingSoloMatrixMargin` on their absolute
  values, so a quantitative budget asks no more of the table than T3 does.
* **T3** (`quittingTailPersistentlySolo_of_zeroFree`): on a table whose
  normalized solo matrix has no vanishing off-diagonal entry, at most one
  player is persistently active — *conditional* on the window-extraction
  hypothesis `QuittingSoloWindowExtraction`, which isolates the step of
  turning two persistently active players into fenced solo windows carrying
  non-vanishing conditioned charge.
* **T4(b)** (`isEmpty_fencedSoloWindows_of_quittingSoloPreempts`): fenced solo
  windows are impossible along a strict solo-preemption edge, so the
  face-enlargement reading of an obstruction is unavailable there.
* **T4(a)** (`QuittingSoloWindowPhaseStopBranch`): a proposition definition,
  not a theorem.

Nothing in this file asserts that solo windows exist; every solo statement is
conditional on being handed one.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Roots at which a single player may quit -/

/-- A root whose only coordinate with positive Quit mass is `owner`. -/
def IsQuittingSoloRoot (root : ι → PMF Bool) (owner : ι) : Prop :=
  ∀ player, player ≠ owner → root player = PMF.pure false

namespace IsQuittingSoloRoot

omit [Fintype ι] in
/-- A solo root is the canonical solo stationary root of its own hazard. -/
theorem eq_soloStationaryRoot {root : ι → PMF Bool} {owner : ι}
    (hsolo : IsQuittingSoloRoot root owner) :
    root = quittingSoloStationaryRoot owner (root owner) := by
  funext player
  by_cases hplayer : player = owner
  · subst player
    simp [quittingSoloStationaryRoot]
  · rw [hsolo player hplayer]
    simp [quittingSoloStationaryRoot, Function.update_of_ne hplayer]

/-- At a solo root the absorption mass is the owner's Quit probability. -/
theorem absorptionMass {root : ι → PMF Bool} {owner : ι}
    (hsolo : IsQuittingSoloRoot root owner) :
    quittingRootAbsorptionMass root = (root owner true).toReal := by
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingRootAbsorptionMass_soloStationaryRoot owner (root owner)

/-- At an active solo root the conditional absorbing delivery is exactly the
owner's singleton reward row. -/
theorem conditionalAbsorbingDelivery
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι}
    (hsolo : IsQuittingSoloRoot root owner)
    (hactive : 0 < (root owner true).toReal) :
    quittingRootConditionalAbsorbingDelivery reward root =
      quittingSoloReward reward owner := by
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingRootConditionalAbsorbingDelivery_solo reward owner
    (root owner) hactive

end IsQuittingSoloRoot

omit [DecidableEq ι] in
/-- A positive Quit probability forces a positive one-stage absorption mass. -/
theorem quittingRootAbsorptionMass_pos_of_quitProbability_pos
    {root : ι → PMF Bool} {who : ι} (hquit : 0 < (root who true).toReal) :
    0 < quittingRootAbsorptionMass root := by
  have hmass := quittingStationaryContinueMass_le_ownContinueProbability
    root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

/-! ## Survival product of a window of conditioned steps -/

/-- Product of the conditioned survival coefficients `1 - aₜ` across the
window of `length` dates beginning at `start`. -/
def quittingTailConditionedSurvivalProduct
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range length,
    (1 - quittingTailConditionedAbsorptionWeight roots (start + offset))

omit [DecidableEq ι] in
@[simp] theorem quittingTailConditionedSurvivalProduct_zero
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingTailConditionedSurvivalProduct roots start 0 = 1 := by
  simp [quittingTailConditionedSurvivalProduct]

omit [DecidableEq ι] in
/-- The survival product peels its first factor. -/
theorem quittingTailConditionedSurvivalProduct_succ
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) :
    quittingTailConditionedSurvivalProduct roots start (length + 1) =
      (1 - quittingTailConditionedAbsorptionWeight roots start) *
        quittingTailConditionedSurvivalProduct roots (start + 1) length := by
  unfold quittingTailConditionedSurvivalProduct
  rw [Finset.prod_range_succ', mul_comm]
  simp only [Nat.add_zero]
  refine congrArg _ (Finset.prod_congr rfl fun offset _ => ?_)
  rw [show start + (offset + 1) = start + 1 + offset from by omega]

omit [DecidableEq ι] in
/-- Every survival factor lies in the unit interval. -/
theorem quittingTailConditionedSurvivalProduct_mem_unitInterval
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (start length : ℕ) :
    0 ≤ quittingTailConditionedSurvivalProduct roots start length ∧
      quittingTailConditionedSurvivalProduct roots start length ≤ 1 := by
  constructor
  · refine Finset.prod_nonneg fun offset _ => ?_
    have hweight := (quittingTailConditionedWeights_mem_unitInterval roots
      (start + offset) (hpositive (start + offset + 1)).le
      (hpositive (start + offset))).1
    linarith [hweight.2]
  · refine Finset.prod_le_one (fun offset _ => ?_) fun offset _ => ?_
    · have hweight := (quittingTailConditionedWeights_mem_unitInterval roots
        (start + offset) (hpositive (start + offset + 1)).le
        (hpositive (start + offset))).1
      linarith [hweight.2]
    · have hweight := (quittingTailConditionedWeights_mem_unitInterval roots
        (start + offset) (hpositive (start + offset + 1)).le
        (hpositive (start + offset))).1
      linarith [hweight.1]

/-! ## Exact transport across a solo window -/

/-- **Window transport.**  On a window whose every root is an active solo
root of `owner`, the conditional absorbing delivery is constant, so the
conditioned value's displacement from `owner`'s singleton reward row is
multiplied by the window's survival product.  This is exact: no asymptotics
and no endpoint-Nash input. -/
theorem quittingTailConditionedValue_sub_soloReward_of_window
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (owner : ι) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) owner)
    (hactive : ∀ offset, offset < length →
      0 < (roots (start + offset) owner true).toReal)
    (who : ι) :
    quittingTailConditionedValue roots value boundary start who -
        quittingSoloReward reward owner who =
      quittingTailConditionedSurvivalProduct roots start length *
        (quittingTailConditionedValue roots value boundary
            (start + length) who -
          quittingSoloReward reward owner who) := by
  revert start
  induction length with
  | zero => intro start _ _; simp
  | succ length ih =>
      intro start hsolo hactive
      have hsolo0 : IsQuittingSoloRoot (roots start) owner := by
        simpa using hsolo 0 (Nat.succ_pos length)
      have hactive0 : 0 < (roots start owner true).toReal := by
        simpa using hactive 0 (Nat.succ_pos length)
      have habsorption : 0 < quittingRootAbsorptionMass (roots start) := by
        rw [hsolo0.absorptionMass]; exact hactive0
      have hstep :
          quittingTailConditionedValue roots value boundary start who =
            quittingTailConditionedAbsorptionWeight roots start *
                quittingRootConditionalAbsorbingDelivery reward
                  (roots start) who +
              quittingTailConditionedContinuationWeight roots start *
                quittingTailConditionedValue roots value boundary
                  (start + 1) who :=
        congrFun (quittingTailConditionedValue_step roots value boundary
          hpolicy start habsorption (hpositive start)
          (hpositive (start + 1))) who
      have hdelivery :
          quittingRootConditionalAbsorbingDelivery reward (roots start) who =
            quittingSoloReward reward owner who :=
        congrFun (hsolo0.conditionalAbsorbingDelivery reward hactive0) who
      have hweights :=
        quittingTailConditionedWeights_add roots start (hpositive start)
      have hsoloTail : ∀ offset, offset < length →
          IsQuittingSoloRoot (roots (start + 1 + offset)) owner := by
        intro offset hoffset
        have hshift := hsolo (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hactiveTail : ∀ offset, offset < length →
          0 < (roots (start + 1 + offset) owner true).toReal := by
        intro offset hoffset
        have hshift := hactive (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hIH := ih (start + 1) hsoloTail hactiveTail
      rw [show start + (length + 1) = start + 1 + length from by omega,
        quittingTailConditionedSurvivalProduct_succ, hstep, hdelivery,
        show quittingTailConditionedContinuationWeight roots start =
          1 - quittingTailConditionedAbsorptionWeight roots start from
            by linarith]
      linear_combination
        (1 - quittingTailConditionedAbsorptionWeight roots start) * hIH

/-! ## Coexistence forces solo indifference -/

omit [DecidableEq ι] in
/-- The conditional absorbing delivery is bounded by the reward bound. -/
theorem abs_quittingRootConditionalAbsorbingDelivery_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    |quittingRootConditionalAbsorbingDelivery reward root who| ≤ M := by
  unfold quittingRootConditionalAbsorbingDelivery
  rw [abs_div, abs_of_pos habsorption, div_le_iff₀ habsorption]
  exact abs_quittingRootAbsorbingContribution_le reward root who M hreward

/-- **T2, quantitative form.**  Let `spectator` be active at the fence date
and again immediately after a window on which only `owner` may quit, and let
`spectator`'s boundary coordinate be its own singleton reward.  Then the
window's absorbed charge times the normalized solo matrix entry
`M spectator owner` is controlled by the two fence meshes.  Letting the
meshes vanish along windows of non-vanishing charge kills the entry. -/
theorem survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (spectator owner : ι)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (fence length : ℕ)
    (hfence : 0 < (roots fence spectator true).toReal)
    (hreturn : 0 < (roots (fence + 1 + length) spectator true).toReal)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (fence + 1 + offset)) owner)
    (hactive : ∀ offset, offset < length →
      0 < (roots (fence + 1 + offset) owner true).toReal) :
    (1 - quittingTailConditionedAbsorptionWeight roots fence) *
        ((1 - quittingTailConditionedSurvivalProduct roots (fence + 1) length) *
          |normalizedSoloMatrix reward spectator owner|) ≤
      4 * M * quittingTailConditionedAbsorptionWeight roots fence +
        2 * M *
          quittingTailConditionedAbsorptionWeight roots (fence + 1 + length) := by
  set weight := quittingTailConditionedAbsorptionWeight roots fence with hweight
  set returnWeight :=
    quittingTailConditionedAbsorptionWeight roots (fence + 1 + length)
    with hreturnWeight
  set survival :=
    quittingTailConditionedSurvivalProduct roots (fence + 1) length
    with hsurvival
  have hpin : boundary spectator =
      reward (quittingSingletonTerminal spectator) spectator := htight
  have hpinLeft :=
    abs_quittingTailConditionedValue_sub_singleton_le_weight roots value
      boundary hpolicy hnash hreward fence spectator (hpositive fence) hfence
      hpin
  have hpinRight :=
    abs_quittingTailConditionedValue_sub_singleton_le_weight roots value
      boundary hpolicy hnash hreward (fence + 1 + length) spectator
      (hpositive (fence + 1 + length)) hreturn hpin
  have hfenceAbsorption : 0 < quittingRootAbsorptionMass (roots fence) :=
    quittingRootAbsorptionMass_pos_of_quitProbability_pos hfence
  have hstep :
      quittingTailConditionedValue roots value boundary fence spectator =
        weight *
            quittingRootConditionalAbsorbingDelivery reward (roots fence)
              spectator +
          quittingTailConditionedContinuationWeight roots fence *
            quittingTailConditionedValue roots value boundary (fence + 1)
              spectator :=
    congrFun (quittingTailConditionedValue_step roots value boundary hpolicy
      fence hfenceAbsorption (hpositive fence) (hpositive (fence + 1)))
      spectator
  have hweights :=
    quittingTailConditionedWeights_add roots fence (hpositive fence)
  have hcontinuation :
      quittingTailConditionedContinuationWeight roots fence = 1 - weight := by
    linarith
  have hunit := quittingTailConditionedWeights_mem_unitInterval roots fence
    (hpositive (fence + 1)).le (hpositive fence)
  have hweight0 : 0 ≤ weight := hunit.1.1
  have hweight1 : weight ≤ 1 := hunit.1.2
  have hsurvival0 : 0 ≤ survival :=
    (quittingTailConditionedSurvivalProduct_mem_unitInterval roots hpositive
      (fence + 1) length).1
  have hsurvival1 : survival ≤ 1 :=
    (quittingTailConditionedSurvivalProduct_mem_unitInterval roots hpositive
      (fence + 1) length).2
  have hdeliveryBound : |quittingRootConditionalAbsorbingDelivery reward
      (roots fence) spectator| ≤ M :=
    abs_quittingRootConditionalAbsorbingDelivery_le reward (roots fence)
      spectator hreward hfenceAbsorption
  have hsoloBound : |quittingSoloReward reward spectator spectator| ≤ M :=
    hreward (quittingSingletonTerminal spectator) spectator
  set singleton := quittingSoloReward reward spectator spectator
    with hsingleton
  set gap := normalizedSoloMatrix reward spectator owner with hgap
  have hgapEq : gap = quittingSoloReward reward owner spectator - singleton :=
    normalizedSoloMatrix_eq_soloReward_sub reward spectator owner
  set left := quittingTailConditionedValue roots value boundary fence
    spectator - singleton with hleft
  set middle := quittingTailConditionedValue roots value boundary (fence + 1)
    spectator - singleton with hmiddle
  set right := quittingTailConditionedValue roots value boundary
    (fence + 1 + length) spectator - singleton with hright
  set delivery := quittingRootConditionalAbsorbingDelivery reward
    (roots fence) spectator - singleton with hdelivery
  have htransport :
      quittingTailConditionedValue roots value boundary (fence + 1)
            spectator - quittingSoloReward reward owner spectator =
        survival * (quittingTailConditionedValue roots value boundary
            (fence + 1 + length) spectator -
          quittingSoloReward reward owner spectator) :=
    quittingTailConditionedValue_sub_soloReward_of_window roots value boundary
      hpolicy hpositive owner (fence + 1) length hsolo hactive spectator
  have hleftBound : |left| ≤ 2 * M * weight := hpinLeft
  have hrightBound : |right| ≤ 2 * M * returnWeight := hpinRight
  have hdeliveryGap : |delivery| ≤ 2 * M := by
    have hone := abs_le.1 hdeliveryBound
    have htwo := abs_le.1 hsoloBound
    rw [hdelivery, abs_le]
    constructor <;> linarith [hone.1, hone.2, htwo.1, htwo.2]
  have hchronology : left = weight * delivery + (1 - weight) * middle := by
    rw [hleft, hmiddle, hdelivery, hstep, hcontinuation]; ring
  have htransportGap : middle - gap = survival * (right - gap) := by
    rw [hmiddle, hright, hgapEq]
    linear_combination htransport
  have hkey : (1 - weight) * ((1 - survival) * gap) =
      left - weight * delivery - (1 - weight) * survival * right := by
    linear_combination -hchronology - (1 - weight) * htransportGap
  have hproductWeight : |weight * delivery| ≤ 2 * M * weight := by
    calc |weight * delivery| = |weight| * |delivery| := abs_mul _ _
      _ = weight * |delivery| := by rw [abs_of_nonneg hweight0]
      _ ≤ weight * (2 * M) := mul_le_mul_of_nonneg_left hdeliveryGap hweight0
      _ = 2 * M * weight := by ring
  have hproductRight : |(1 - weight) * survival * right| ≤
      2 * M * returnWeight := by
    have hcoefficient : |(1 - weight) * survival| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg (by linarith) hsurvival0)]
      exact mul_le_one₀ (by linarith) hsurvival0 hsurvival1
    calc |(1 - weight) * survival * right| =
          |(1 - weight) * survival| * |right| := abs_mul _ _
      _ ≤ 1 * |right| :=
        mul_le_mul_of_nonneg_right hcoefficient (abs_nonneg right)
      _ = |right| := one_mul _
      _ ≤ 2 * M * returnWeight := hrightBound
  have habs : |(1 - weight) * ((1 - survival) * gap)| ≤
      4 * M * weight + 2 * M * returnWeight := by
    rw [hkey, abs_le]
    have hleftAbs := abs_le.1 hleftBound
    have hmiddleAbs := abs_le.1 hproductWeight
    have hrightAbs := abs_le.1 hproductRight
    constructor <;> linarith [hleftAbs.1, hleftAbs.2, hmiddleAbs.1,
      hmiddleAbs.2, hrightAbs.1, hrightAbs.2]
  have hsplit : |(1 - weight) * ((1 - survival) * gap)| =
      (1 - weight) * ((1 - survival) * |gap|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 - weight by linarith),
      abs_of_nonneg (show (0 : ℝ) ≤ 1 - survival by linarith)]
  rw [hsplit] at habs
  exact habs

/-! ## Recurrent fenced solo windows -/

/-- Recurrent windows on which only `owner` may quit, each fenced on both
sides by a date at which `spectator` is active, and each absorbing at least a
fixed positive share `charge` of the remaining eventual absorption. -/
structure QuittingFencedSoloWindows
    (roots : ℕ → ι → PMF Bool) (spectator owner : ι) where
  /-- Left fence date of window `index`. -/
  fence : ℕ → ℕ
  /-- Number of solo dates in window `index`. -/
  length : ℕ → ℕ
  /-- Uniform lower bound on the conditioned charge absorbed per window. -/
  charge : ℝ
  /-- The fence dates escape to infinity. -/
  fence_tendsto : Tendsto fence atTop atTop
  /-- The uniform charge is positive. -/
  charge_pos : 0 < charge
  /-- `spectator` is active at every left fence. -/
  fence_active : ∀ index, 0 < (roots (fence index) spectator true).toReal
  /-- `spectator` is active again at the date closing each window. -/
  return_active : ∀ index,
    0 < (roots (fence index + 1 + length index) spectator true).toReal
  /-- Only `owner` may quit inside each window. -/
  window_solo : ∀ index offset, offset < length index →
    IsQuittingSoloRoot (roots (fence index + 1 + offset)) owner
  /-- `owner` really is active inside each window. -/
  window_active : ∀ index offset, offset < length index →
    0 < (roots (fence index + 1 + offset) owner true).toReal
  /-- Each window absorbs at least `charge` of the conditioned scale. -/
  charge_le : ∀ index, charge ≤
    1 - quittingTailConditionedSurvivalProduct roots
      (fence index + 1) (length index)

/-- **T2.**  Recurrent solo-`owner` windows fenced by `spectator` activity, in
an exact tail with vanishing conditioned mesh and `spectator`-tight boundary,
force the normalized solo matrix entry `M spectator owner` to vanish. -/
theorem normalizedSoloMatrix_eq_zero_of_fencedSoloWindows
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    {spectator owner : ι}
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (windows : QuittingFencedSoloWindows roots spectator owner) :
    normalizedSoloMatrix reward spectator owner = 0 := by
  set gap := normalizedSoloMatrix reward spectator owner with hgap
  have hfenceMesh : Tendsto
      (fun index => quittingTailConditionedAbsorptionWeight roots
        (windows.fence index)) atTop (nhds 0) :=
    hmesh.comp windows.fence_tendsto
  have hreturnTendsto : Tendsto
      (fun index => windows.fence index + 1 + windows.length index) atTop
      atTop :=
    tendsto_atTop_mono (fun index => by omega) windows.fence_tendsto
  have hreturnMesh : Tendsto
      (fun index => quittingTailConditionedAbsorptionWeight roots
        (windows.fence index + 1 + windows.length index)) atTop (nhds 0) :=
    hmesh.comp hreturnTendsto
  have hbound : ∀ index,
      (1 - quittingTailConditionedAbsorptionWeight roots
          (windows.fence index)) * (windows.charge * |gap|) ≤
        4 * M * quittingTailConditionedAbsorptionWeight roots
            (windows.fence index) +
          2 * M * quittingTailConditionedAbsorptionWeight roots
            (windows.fence index + 1 + windows.length index) := by
    intro index
    have hmain := survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow
      roots value boundary hpolicy hnash hreward hpositive spectator owner
      htight (windows.fence index) (windows.length index)
      (windows.fence_active index) (windows.return_active index)
      (windows.window_solo index) (windows.window_active index)
    have hunit := quittingTailConditionedWeights_mem_unitInterval roots
      (windows.fence index) (hpositive (windows.fence index + 1)).le
      (hpositive (windows.fence index))
    have hchargeLe : windows.charge * |gap| ≤
        (1 - quittingTailConditionedSurvivalProduct roots
          (windows.fence index + 1) (windows.length index)) * |gap| :=
      mul_le_mul_of_nonneg_right (windows.charge_le index) (abs_nonneg gap)
    have hscale := mul_le_mul_of_nonneg_left hchargeLe
      (by linarith [hunit.1.2] :
        (0 : ℝ) ≤ 1 - quittingTailConditionedAbsorptionWeight roots
          (windows.fence index))
    exact hscale.trans hmain
  have hleftTendsto : Tendsto
      (fun index => (1 - quittingTailConditionedAbsorptionWeight roots
        (windows.fence index)) * (windows.charge * |gap|)) atTop
      (nhds (windows.charge * |gap|)) := by
    have hone : Tendsto
        (fun index => 1 - quittingTailConditionedAbsorptionWeight roots
          (windows.fence index)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
        hfenceMesh
    simpa using hone.mul (tendsto_const_nhds
      (x := windows.charge * |gap|) (f := atTop (α := ℕ)))
  have hrightTendsto : Tendsto
      (fun index => 4 * M * quittingTailConditionedAbsorptionWeight roots
          (windows.fence index) +
        2 * M * quittingTailConditionedAbsorptionWeight roots
          (windows.fence index + 1 + windows.length index)) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds (x := 4 * M)
      (f := atTop (α := ℕ))).mul hfenceMesh).add
        ((tendsto_const_nhds (x := 2 * M) (f := atTop (α := ℕ))).mul
          hreturnMesh)
  have hnonpos : windows.charge * |gap| ≤ 0 :=
    le_of_tendsto_of_tendsto' hleftTendsto hrightTendsto hbound
  have hzero : |gap| ≤ 0 :=
    nonpos_of_mul_nonpos_right (by linarith) windows.charge_pos
  exact abs_eq_zero.1 (le_antisymm hzero (abs_nonneg gap))

/-! ## Zero-free tables and eventual solo degeneracy -/

/-- Every off-diagonal entry of the normalized solo matrix has absolute value
at least `margin`.  This is the quantitative currency consumed by budget
arguments, which divide by the entry and so need a uniform bound rather than
mere nonvanishing. -/
def QuittingSoloMatrixMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (margin : ℝ) : Prop :=
  ∀ who owner : ι, who ≠ owner →
    margin ≤ |normalizedSoloMatrix reward who owner|

/-- No off-diagonal entry of the normalized solo matrix vanishes.  The
Solan--Vieille boundary table and the regular five-player tournament seed are
both of this kind. -/
def QuittingZeroFreeSoloMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ who owner : ι, who ≠ owner → normalizedSoloMatrix reward who owner ≠ 0

/-- A positive margin is a zero-free table. -/
theorem quittingZeroFreeSoloMatrix_of_soloMatrixMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {margin : ℝ}
    (hmargin : 0 < margin) (hentries : QuittingSoloMatrixMargin reward margin) :
    QuittingZeroFreeSoloMatrix reward := by
  intro who owner hne hzero
  have hentry := hentries who owner hne
  rw [hzero, abs_zero] at hentry
  linarith

/-- A zero-free table has a positive margin: the finitely many off-diagonal
entries are nonzero, so the least of their absolute values is positive.  With
no off-diagonal pair at all the margin condition is vacuous. -/
theorem exists_soloMatrixMargin_of_quittingZeroFreeSoloMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzeroFree : QuittingZeroFreeSoloMatrix reward) :
    ∃ margin, 0 < margin ∧ QuittingSoloMatrixMargin reward margin := by
  let entry : ι × ι → ℝ :=
    fun pair => |normalizedSoloMatrix reward pair.1 pair.2|
  set pairs : Finset (ι × ι) :=
    Finset.univ.filter (fun pair => pair.1 ≠ pair.2) with hpairs
  have hmem : ∀ pair : ι × ι, pair ∈ pairs ↔ pair.1 ≠ pair.2 := by
    intro pair
    rw [hpairs, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  by_cases hnonempty : pairs.Nonempty
  · refine ⟨pairs.inf' hnonempty entry, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro pair hpair
      exact abs_pos.2 (hzeroFree pair.1 pair.2 ((hmem pair).1 hpair))
    · intro who owner hne
      exact Finset.inf'_le entry ((hmem (who, owner)).2 hne)
  · exact ⟨1, one_pos, fun who owner hne =>
      absurd ⟨(who, owner), (hmem (who, owner)).2 hne⟩ hnonempty⟩

/-- **Zero-freeness is a uniform margin.**  On a finite player set the
qualitative and the quantitative form of the table condition coincide, so a
budget argument's margin hypothesis asks no more of the table than the
coexistence obstruction already does. -/
theorem quittingZeroFreeSoloMatrix_iff_exists_soloMatrixMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingZeroFreeSoloMatrix reward ↔
      ∃ margin, 0 < margin ∧ QuittingSoloMatrixMargin reward margin :=
  ⟨exists_soloMatrixMargin_of_quittingZeroFreeSoloMatrix reward,
    fun ⟨_, hmargin, hentries⟩ =>
      quittingZeroFreeSoloMatrix_of_soloMatrixMargin reward hmargin hentries⟩

/-- `who` quits with positive probability at arbitrarily late dates. -/
def QuittingTailPersistentlyActive
    (roots : ℕ → ι → PMF Bool) (who : ι) : Prop :=
  ∀ start, ∃ time, start ≤ time ∧ 0 < (roots time who true).toReal

/-- At most one player is persistently active. -/
def QuittingTailPersistentlySolo (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ first second : ι, QuittingTailPersistentlyActive roots first →
    QuittingTailPersistentlyActive roots second → first = second

/-- **The window-extraction hypothesis.**  Two distinct
persistently active players are assumed to produce, in one of the two orders,
recurrent solo windows fenced by the other player's activity and carrying a
uniformly positive conditioned charge.  This is a hypothesis, not a theorem:
turning persistence into windows requires controlling collisions and the
share of a single active player, which is not formalized here. -/
def QuittingSoloWindowExtraction (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ first second : ι, first ≠ second →
    QuittingTailPersistentlyActive roots first →
      QuittingTailPersistentlyActive roots second →
        Nonempty (QuittingFencedSoloWindows roots first second) ∨
          Nonempty (QuittingFencedSoloWindows roots second first)

/-- **T3, conditional.**  On a zero-free table, an exact diffuse tail whose
persistently active players are boundary-tight has at most one persistently
active player — given the window-extraction hypothesis. -/
theorem quittingTailPersistentlySolo_of_zeroFree
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    (htight : ∀ who, QuittingTailPersistentlyActive roots who →
      boundary who = quittingSoloReward reward who who)
    (hzeroFree : QuittingZeroFreeSoloMatrix reward)
    (hextraction : QuittingSoloWindowExtraction roots) :
    QuittingTailPersistentlySolo roots := by
  intro first second hfirst hsecond
  by_contra hne
  rcases hextraction first second hne hfirst hsecond with hforward | hbackward
  · obtain ⟨windows⟩ := hforward
    exact hzeroFree first second hne
      (normalizedSoloMatrix_eq_zero_of_fencedSoloWindows roots value boundary
        hpolicy hnash hreward hpositive hmesh (htight first hfirst) windows)
  · obtain ⟨windows⟩ := hbackward
    exact hzeroFree second first (Ne.symm hne)
      (normalizedSoloMatrix_eq_zero_of_fencedSoloWindows roots value boundary
        hpolicy hnash hreward hpositive hmesh (htight second hsecond) windows)

/-- Contrapositive reading of T2 on a zero-free table: no fenced solo window
family exists for a distinct pair. -/
theorem isEmpty_fencedSoloWindows_of_zeroFree
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    {spectator owner : ι} (hne : spectator ≠ owner)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hzeroFree : QuittingZeroFreeSoloMatrix reward) :
    IsEmpty (QuittingFencedSoloWindows roots spectator owner) :=
  ⟨fun windows => hzeroFree spectator owner hne
    (normalizedSoloMatrix_eq_zero_of_fencedSoloWindows roots value boundary
      hpolicy hnash hreward hpositive hmesh htight windows)⟩

/-- **T4(b).**  Along a strict solo-preemption edge `owner ⟶ spectator` with
positive margin, fenced solo windows are impossible in an exact diffuse tail:
coexistence would force the gate entry to vanish, but the edge keeps it at
most `-gap`.  So the face-enlargement reading of an obstruction is
unavailable exactly where a counterexample regime supplies edges. -/
theorem isEmpty_fencedSoloWindows_of_quittingSoloPreempts
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    {spectator owner : ι} {margin : ℝ} (hmargin : 0 < margin)
    (hpreempt : QuittingSoloPreempts reward margin owner spectator)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator) :
    IsEmpty (QuittingFencedSoloWindows roots spectator owner) := by
  obtain ⟨hne, hentry⟩ :=
    (quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg reward margin owner
      spectator).1 hpreempt
  refine ⟨fun windows => ?_⟩
  have hzero := normalizedSoloMatrix_eq_zero_of_fencedSoloWindows roots value
    boundary hpolicy hnash hreward hpositive hmesh htight windows
  rw [hzero] at hentry
  linarith

/-! ## The seam supplies active tightness -/

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}

/-- A persistently active player's seam boundary coordinate is its own
singleton reward.  This is the seam-grade active-tightness input used by T2
and T3, read off `eventually_active_implies_limitValue_eq_singleton`. -/
theorem limitValue_eq_soloReward_of_persistentlyActive
    (seam : QuittingCounterexampleSeamWitness regime) (who : ι)
    (hactive : QuittingTailPersistentlyActive
      (quittingDynamicDebtTailRoots seam.tail) who) :
    seam.limit.value who = quittingSoloReward reward who who := by
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.1
    seam.eventually_active_implies_limitValue_eq_singleton
  obtain ⟨time, hle, hquit⟩ := hactive start
  have hnotPure :
      quittingDynamicDebtTailRoots seam.tail time who ≠ PMF.pure false := by
    intro hpure
    rw [hpure] at hquit
    simp at hquit
  simpa using hstart time hle who hnotPure

/-- The phase-stop-branch proposition (T4(a)): on the canonical periodic
windows of a seam whose late roots are solo at `owner`, the stabilized
obstruction of `exists_infinite_fixedPlayer_fixedBranch` is the phase-stop
branch, and the obstructing player is a strict solo-preemption out-neighbour
of `owner`. -/
def QuittingSoloWindowPhaseStopBranch
    (seam : QuittingCounterexampleSeamWitness regime) (owner : ι)
    (margin : ℝ) : Prop :=
  ∃ other, QuittingSoloPreempts reward margin owner other ∧
    Set.Infinite {window : ℕ |
      ∃ phase : Fin (window + 1),
        regime.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) other phase -
            seam.canonicalPeriodicTailWindowFamily.delivery window other}

end QuittingCounterexampleSeamWitness

end GameTheory
