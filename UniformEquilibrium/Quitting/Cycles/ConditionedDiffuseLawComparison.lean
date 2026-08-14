/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import UniformEquilibrium.Quitting.Projective.AnalyticPacket
import MathUE.PMFProduct.CollisionMass
import MathUE.Probability.FiniteWeightVariation

/-!
# Finite-law comparisons for the tight diffuse conditioned branch

This module closes the finite-law seam in diffuse product rescaling.  The
basic estimate partitions a finite law into its empty atom, singleton atoms,
and collision atoms.  If the source singleton masses dominate the target
singleton masses, their total-variation distance is paid entirely by the
empty mismatch and the target collision mass.  Applied to hazards `a * x`
conditioned at scale `a` and the product hazards `x`, this gives the sharp
quadratic law error, including the forced-Continue opponent law.

The declarations preserve the original `GameTheory` namespace and are
consumed by the strategic compiler.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Empty/singleton/collision partition -/

/-- Coalitions containing at least two players. -/
def quittingDiffuseCollisionCoalitions : Finset (Finset ι) :=
  Finset.univ.filter fun coalition : Finset ι => 2 ≤ coalition.card

omit [DecidableEq ι] in
/-- Abstract three-stratum comparison.  No probability representation is
needed: total mass, singleton domination, and a target collision bound suffice. -/
theorem abs_sum_mul_sub_sum_mul_le_of_singleton_domination
    (source target payoff : Finset ι → ℝ)
    {bound emptyError targetCollision : ℝ}
    (hbound : 0 ≤ bound)
    (hpayoff : ∀ coalition, |payoff coalition| ≤ bound)
    (hsourceNonneg : ∀ coalition, 0 ≤ source coalition)
    (htargetNonneg : ∀ coalition, 0 ≤ target coalition)
    (hsourceTotal : ∑ coalition, source coalition = 1)
    (htargetTotal : ∑ coalition, target coalition = 1)
    (hsingleton : ∀ who, target {who} ≤ source {who})
    (hempty : |source ∅ - target ∅| ≤ emptyError)
    (htargetCollision :
      ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        target coalition ≤ targetCollision) :
    |(∑ coalition, source coalition * payoff coalition) -
        ∑ coalition, target coalition * payoff coalition| ≤
      bound *
        (2 * emptyError + 2 * targetCollision) := by
  classical
  have hcomparison := abs_weightedSum_sub_le_of_domination_off
    (totalError := 0) (controlledError := emptyError)
    (exceptionalMass := targetCollision)
    (Finset.univ : Finset (Finset ι)) {∅}
    (quittingDiffuseCollisionCoalitions (ι := ι))
    source target payoff hbound (fun coalition _ => hpayoff coalition)
    (fun coalition _ => hsourceNonneg coalition)
    (fun coalition _ => htargetNonneg coalition)
    (fun coalition _ hnonempty hnotCollision => by
      have hne : coalition ≠ ∅ := by simpa using hnonempty
      have hpos : 0 < coalition.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      have hcard : coalition.card = 1 := by
        simp only [quittingDiffuseCollisionCoalitions, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnotCollision
        omega
      obtain ⟨who, rfl⟩ := Finset.card_eq_one.mp hcard
      exact hsingleton who)
    (by simp [hsourceTotal, htargetTotal])
    (by simpa using hempty)
    (by simpa using htargetCollision)
  convert hcomparison using 1
  all_goals ring

/-- Comparison of the nonempty parts of two subprobability laws.  The total
mass mismatch replaces the empty-atom mismatch in the probability-law
version. -/
theorem abs_sum_nonempty_mul_sub_sum_nonempty_mul_le_of_singleton_domination
    (source target payoff : Finset ι → ℝ)
    {bound totalError targetCollision : ℝ}
    (hbound : 0 ≤ bound)
    (hpayoff : ∀ coalition, |payoff coalition| ≤ bound)
    (hsourceNonneg : ∀ coalition, 0 ≤ source coalition)
    (htargetNonneg : ∀ coalition, 0 ≤ target coalition)
    (hsingleton : ∀ who, target {who} ≤ source {who})
    (htotal :
      |(∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), source coalition) -
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι), target coalition| ≤
          totalError)
    (htargetCollision :
      ∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        target coalition ≤ targetCollision) :
    |(∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          source coalition * payoff coalition) -
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          target coalition * payoff coalition| ≤
      bound * (totalError + 2 * targetCollision) := by
  classical
  let support := Finset.univ.erase (∅ : Finset ι)
  have hcomparison := abs_weightedSum_sub_le_of_domination_off
    (totalError := totalError) (controlledError := 0)
    (exceptionalMass := targetCollision)
    support (∅ : Finset (Finset ι))
    (quittingDiffuseCollisionCoalitions (ι := ι))
    source target payoff hbound (fun coalition _ => hpayoff coalition)
    (fun coalition _ => hsourceNonneg coalition)
    (fun coalition _ => htargetNonneg coalition)
    (fun coalition hcoalition _ hnotCollision => by
      have hne : coalition ≠ ∅ := Finset.ne_of_mem_erase hcoalition
      have hpos : 0 < coalition.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      have hcard : coalition.card = 1 := by
        simp only [quittingDiffuseCollisionCoalitions, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnotCollision
        omega
      obtain ⟨who, rfl⟩ := Finset.card_eq_one.mp hcard
      exact hsingleton who)
    (by simpa only [support] using htotal)
    (by simp [support])
    (by
      have hsubset : quittingDiffuseCollisionCoalitions (ι := ι) ⊆ support := by
        intro coalition hcoalition
        simp only [quittingDiffuseCollisionCoalitions, Finset.mem_filter,
          Finset.mem_univ, true_and] at hcoalition
        exact Finset.mem_erase.mpr ⟨fun hempty => by
          subst coalition
          simp at hcoalition, Finset.mem_univ _⟩
      simpa [Finset.inter_eq_right.mpr hsubset] using htargetCollision)
  convert hcomparison using 1
  all_goals ring

/-! ## Scaled product laws -/

/-- A singleton atom of the rescaled product law is no larger than the same
singleton atom of the source law divided by the scale. -/
theorem coalitionMass_singleton_le_scaled_div
    (x : ι → ℝ) (scale : ℝ) (who : ι)
    (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hx0 : ∀ player, 0 ≤ x player)
    (hx1 : ∀ player, x player ≤ 1) :
    coalitionMass x {who} ≤
      coalitionMass (fun player => scale * x player) {who} / scale := by
  classical
  have hfactor : ∀ player ∈ ({who} : Finset ι)ᶜ,
      1 - x player ≤ 1 - scale * x player := by
    intro player _
    nlinarith [hx0 player]
  have hnonneg : ∀ player ∈ ({who} : Finset ι)ᶜ,
      0 ≤ 1 - x player := fun player _ => sub_nonneg.mpr (hx1 player)
  have hproduct :
      (∏ player ∈ ({who} : Finset ι)ᶜ, (1 - x player)) ≤
        ∏ player ∈ ({who} : Finset ι)ᶜ,
          (1 - scale * x player) := by
    apply Finset.prod_le_prod hnonneg
    intro player hplayer
    exact hfactor player hplayer
  unfold coalitionMass
  simp only [Finset.prod_singleton]
  have hscaled :
      (scale * x who *
          ∏ player ∈ ({who} : Finset ι)ᶜ,
            (1 - scale * x player)) / scale =
        x who *
          ∏ player ∈ ({who} : Finset ι)ᶜ,
            (1 - scale * x player) := by
    field_simp [hscale.ne']
  rw [hscaled]
  exact mul_le_mul_of_nonneg_left hproduct (hx0 who)

/-- Collision mass of a scaled product law, divided by the scale, is at
most half the square of the unscaled marginal total. -/
theorem collisionMass_scaled_div_le_sum_sq_div_two
    (x : ι → ℝ) (scale : ℝ)
    (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hx0 : ∀ player, 0 ≤ x player)
    (hx1 : ∀ player, x player ≤ 1) :
    collisionMass (fun player => scale * x player) / scale ≤
      (∑ player, x player) ^ 2 / 2 := by
  let scaled : ι → ℝ := fun player => scale * x player
  have hscaled0 : ∀ player, 0 ≤ scaled player := fun player =>
    mul_nonneg hscale.le (hx0 player)
  have hscaled1 : ∀ player, scaled player ≤ 1 := fun player => by
    dsimp only [scaled]
    nlinarith [hx0 player, hx1 player]
  have hcollision := collisionMass_le_pairMulSum scaled hscaled0 hscaled1
  have hpair := Math.pairMulSum_le_sq_sum_div_two scaled Finset.univ
  have hsum : (∑ player, scaled player) =
      scale * ∑ player, x player := by
    unfold scaled
    rw [Finset.mul_sum]
  have hbound : collisionMass scaled ≤
      (scale * ∑ player, x player) ^ 2 / 2 := by
    rw [← hsum]
    exact hcollision.trans hpair
  apply (div_le_iff₀ hscale).2
  nlinarith [sq_nonneg (∑ player, x player)]

/-- Unscaled collision mass is at most half the squared marginal total. -/
theorem collisionMass_le_sum_sq_div_two
    (x : ι → ℝ)
    (hx0 : ∀ player, 0 ≤ x player)
    (hx1 : ∀ player, x player ≤ 1) :
    collisionMass x ≤ (∑ player, x player) ^ 2 / 2 := by
  exact (collisionMass_le_pairMulSum x hx0 hx1).trans
    (Math.pairMulSum_le_sq_sum_div_two x Finset.univ)

/-! ## The conditioned source law -/

/-- The source one-stage coalition law after conditioning the whole tail on
eventual absorption.  Nonempty atoms are divided by remaining eventual
absorption; the empty atom transports the next remaining mass. -/
def quittingTailConditionedCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (coalition : Finset ι) : ℝ :=
  if coalition = ∅ then
    quittingStationaryContinueMass (roots time) *
        quittingTailEventualAbsorption roots (time + 1) /
      quittingTailEventualAbsorption roots time
  else
    quittingRootCoalitionMass (roots time) coalition /
      quittingTailEventualAbsorption roots time

/-- The conditioned source coalition weights have total mass one. -/
theorem sum_quittingTailConditionedCoalitionMass_eq_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    ∑ coalition, quittingTailConditionedCoalitionMass roots time coalition = 1 := by
  have hnonempty := quittingRootCoalitionMass_sum_nonempty (roots time)
  have heventual :=
    quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
      roots time
  rw [← Finset.add_sum_erase Finset.univ
    (quittingTailConditionedCoalitionMass roots time)
    (Finset.mem_univ ∅)]
  have herase :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedCoalitionMass roots time coalition) =
        quittingRootAbsorptionMass (roots time) /
          quittingTailEventualAbsorption roots time := by
    calc
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedCoalitionMass roots time coalition) =
          ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
            quittingRootCoalitionMass (roots time) coalition /
              quittingTailEventualAbsorption roots time := by
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        simp [quittingTailConditionedCoalitionMass,
          (Finset.ne_of_mem_erase hcoalition)]
      _ = _ := by
        rw [← Finset.sum_div, hnonempty]
        unfold quittingRootAbsorptionMass
        rfl
  rw [herase]
  simp only [quittingTailConditionedCoalitionMass, if_pos]
  rw [← add_div]
  have hnumerator :
      quittingStationaryContinueMass (roots time) *
          quittingTailEventualAbsorption roots (time + 1) +
        quittingRootAbsorptionMass (roots time) =
      quittingTailEventualAbsorption roots time := by
    linarith [heventual]
  rw [hnumerator]
  exact div_self hpositive.ne'

/-- Every conditioned source coalition weight is nonnegative. -/
theorem quittingTailConditionedCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (coalition : Finset ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedCoalitionMass roots time coalition := by
  unfold quittingTailConditionedCoalitionMass
  split_ifs
  · exact div_nonneg
      (mul_nonneg (quittingStationaryContinueMass_nonneg _)
        (quittingTailEventualAbsorption_mem_unitInterval roots (time + 1)).1)
      hpositive.le
  · unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
    exact div_nonneg
      (mul_nonneg
        (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
        (Finset.prod_nonneg fun player _ =>
          sub_nonneg.mpr (hazardOfRoot_le_one (roots time) player)))
      hpositive.le

/-- Every ordinary product coalition weight is nonnegative. -/
theorem quittingRootCoalitionMass_nonneg'
    (root : ι → PMF Bool) (coalition : Finset ι) :
    0 ≤ quittingRootCoalitionMass root coalition := by
  unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.prod_nonneg fun player _ =>
      sub_nonneg.mpr (hazardOfRoot_le_one root player))

/-- All ordinary product coalition weights, including the empty atom, sum
to one. -/
theorem sum_quittingRootCoalitionMass_eq_one
    (root : ι → PMF Bool) :
    ∑ coalition, quittingRootCoalitionMass root coalition = 1 := by
  rw [← Finset.add_sum_erase Finset.univ
    (quittingRootCoalitionMass root) (Finset.mem_univ ∅),
    quittingRootCoalitionMass_sum_nonempty]
  have hempty : quittingRootCoalitionMass root ∅ =
      quittingStationaryContinueMass root := by
    unfold quittingRootCoalitionMass
    rw [coalitionMass_empty, continueMass_quittingRootQuitRates]
  rw [hempty]
  ring

/-- The conditioned source singleton atom dominates the rescaled target
singleton atom. -/
theorem quittingRootCoalitionMass_rescaled_le_conditioned_singleton
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingRootCoalitionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) {who} ≤
      quittingTailConditionedCoalitionMass roots time {who} := by
  let scale := quittingTailEventualAbsorption roots time
  let x := quittingTailDiffuseRescaledHazard roots time
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := fun player =>
    quittingTailDiffuseRescaledHazard_nonneg roots time player hpositive
  have hx1 : ∀ player, x player ≤ 1 := fun player =>
    quittingTailDiffuseRescaledHazard_le_one roots time player hpositive
  have htargetRates :
      quittingRootQuitRates
          (quittingTailDiffuseRescaledRoot roots time hpositive) = x := by
    funext player
    change hazardOfRoot
      (quittingTailDiffuseRescaledRoot roots time hpositive) player = x player
    rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hsourceRates : quittingRootQuitRates (roots time) =
      fun player => scale * x player := by
    funext player
    unfold quittingRootQuitRates x quittingTailDiffuseRescaledHazard scale
    field_simp [hpositive.ne']
  have hscaled := coalitionMass_singleton_le_scaled_div
    x scale who hpositive hscaleOne hx0 hx1
  unfold quittingRootCoalitionMass
  rw [htargetRates]
  have hsource :
      quittingTailConditionedCoalitionMass roots time {who} =
        coalitionMass (fun player => scale * x player) {who} / scale := by
    simp only [quittingTailConditionedCoalitionMass,
      show ({who} : Finset ι) ≠ ∅ by simp, if_false]
    unfold quittingRootCoalitionMass
    rw [hsourceRates]
  rw [hsource]
  exact hscaled

/-- Conditioned source collision mass is at most half the squared rescaled
marginal total. -/
theorem conditionedCoalitionCollisionMass_le_rescaledTotal_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingTailConditionedCoalitionMass roots time coalition) ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  let scale := quittingTailEventualAbsorption roots time
  let x := quittingTailDiffuseRescaledHazard roots time
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := fun player =>
    quittingTailDiffuseRescaledHazard_nonneg roots time player hpositive
  have hx1 : ∀ player, x player ≤ 1 := fun player =>
    quittingTailDiffuseRescaledHazard_le_one roots time player hpositive
  have hsourceRates : quittingRootQuitRates (roots time) =
      fun player => scale * x player := by
    funext player
    unfold quittingRootQuitRates x quittingTailDiffuseRescaledHazard scale
    field_simp [hpositive.ne']
  have hsum : (∑ player, x player) =
      quittingTailDiffuseRescaledTotal roots time := rfl
  have hcollision := collisionMass_scaled_div_le_sum_sq_div_two
    x scale hpositive hscaleOne hx0 hx1
  have hleft :
      (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          quittingTailConditionedCoalitionMass roots time coalition) =
        collisionMass (fun player => scale * x player) / scale := by
    calc
      _ = (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
          quittingRootCoalitionMass (roots time) coalition) / scale := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        have hcard : 2 ≤ coalition.card :=
          (Finset.mem_filter.mp hcoalition).2
        have hne : coalition ≠ ∅ := by
          intro hempty
          simp [hempty] at hcard
        simp only [quittingTailConditionedCoalitionMass, hne, if_false]
        rfl
      _ = collisionMass (fun player => scale * x player) / scale := by
        change collisionMass (quittingRootQuitRates (roots time)) / scale =
          collisionMass (fun player => scale * x player) / scale
        rw [hsourceRates]
  rw [hleft, ← hsum]
  exact hcollision

/-- Target rescaled collision mass obeys the same quadratic bound. -/
theorem rescaledCoalitionCollisionMass_le_rescaledTotal_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingRootCoalitionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) coalition) ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  let x := quittingTailDiffuseRescaledHazard roots time
  have hx0 : ∀ player, 0 ≤ x player := fun player =>
    quittingTailDiffuseRescaledHazard_nonneg roots time player hpositive
  have hx1 : ∀ player, x player ≤ 1 := fun player =>
    quittingTailDiffuseRescaledHazard_le_one roots time player hpositive
  have htargetRates :
      quittingRootQuitRates
          (quittingTailDiffuseRescaledRoot roots time hpositive) = x := by
    funext player
    change hazardOfRoot
      (quittingTailDiffuseRescaledRoot roots time hpositive) player = x player
    rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hcollision := collisionMass_le_sum_sq_div_two x hx0 hx1
  change collisionMass (quittingRootQuitRates
      (quittingTailDiffuseRescaledRoot roots time hpositive)) ≤
    quittingTailDiffuseRescaledTotal roots time ^ 2 / 2
  rw [htargetRates]
  exact hcollision

/-- The empty atoms of the conditioned source and target product laws differ
at most quadratically. -/
theorem abs_conditionedCoalitionMass_empty_sub_rescaled_empty_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingTailConditionedCoalitionMass roots time ∅ -
        quittingRootCoalitionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive) ∅| ≤
      quittingTailDiffuseRescaledTotal roots time ^ 2 / 2 := by
  have hsource : quittingTailConditionedCoalitionMass roots time ∅ =
      1 - quittingTailConditionedAbsorptionWeight roots time := by
    simp only [quittingTailConditionedCoalitionMass, if_pos]
    rw [← quittingTailConditionedContinuationWeight]
    exact quittingTailConditionedContinuationWeight_eq_one_sub
      roots time hpositive
  have htarget : quittingRootCoalitionMass
      (quittingTailDiffuseRescaledRoot roots time hpositive) ∅ =
      1 - quittingRootAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) := by
    unfold quittingRootCoalitionMass
    rw [coalitionMass_empty, continueMass_quittingRootQuitRates]
    unfold quittingRootAbsorptionMass
    ring
  rw [hsource, htarget]
  have hcomparison :=
    abs_conditionedWeight_sub_rescaledRoot_absorptionMass_le
      roots time hpositive
  have habs :
      |1 - quittingTailConditionedAbsorptionWeight roots time -
          (1 - quittingRootAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive))| =
        |quittingTailConditionedAbsorptionWeight roots time -
          quittingRootAbsorptionMass
            (quittingTailDiffuseRescaledRoot roots time hpositive)| := by
    rw [show 1 - quittingTailConditionedAbsorptionWeight roots time -
        (1 - quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive)) =
      -(quittingTailConditionedAbsorptionWeight roots time -
        quittingRootAbsorptionMass
          (quittingTailDiffuseRescaledRoot roots time hpositive)) by ring,
      abs_neg]
  rw [habs]
  exact hcomparison

/-- **Quadratic conditioned-law comparison.**  Every bounded observable of
the whole quitter coalition changes by at most `2 M s²` under product
rescaling. -/
theorem abs_conditionedCoalitionExpectation_sub_rescaled_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ)
    (observable : Finset ι → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hobservable : ∀ coalition, |observable coalition| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |(∑ coalition,
          quittingTailConditionedCoalitionMass roots time coalition *
            observable coalition) -
        ∑ coalition,
          quittingRootCoalitionMass
              (quittingTailDiffuseRescaledRoot roots time hpositive) coalition *
            observable coalition| ≤
      2 * M * quittingTailDiffuseRescaledTotal roots time ^ 2 := by
  have habstract :=
    abs_sum_mul_sub_sum_mul_le_of_singleton_domination
      (quittingTailConditionedCoalitionMass roots time)
      (quittingRootCoalitionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive))
      observable hM hobservable
      (fun coalition =>
        quittingTailConditionedCoalitionMass_nonneg
          roots time coalition hpositive)
      (quittingRootCoalitionMass_nonneg'
        (quittingTailDiffuseRescaledRoot roots time hpositive))
      (sum_quittingTailConditionedCoalitionMass_eq_one
        roots time hpositive)
      (sum_quittingRootCoalitionMass_eq_one
        (quittingTailDiffuseRescaledRoot roots time hpositive))
      (fun who =>
        quittingRootCoalitionMass_rescaled_le_conditioned_singleton
          roots time who hpositive)
      (abs_conditionedCoalitionMass_empty_sub_rescaled_empty_le
        roots time hpositive)
      (rescaledCoalitionCollisionMass_le_rescaledTotal_sq_div_two
        roots time hpositive)
  calc
    |_ - _| ≤ M *
        (2 * (quittingTailDiffuseRescaledTotal roots time ^ 2 / 2) +
          2 * (quittingTailDiffuseRescaledTotal roots time ^ 2 / 2)) := habstract
    _ = 2 * M * quittingTailDiffuseRescaledTotal roots time ^ 2 := by ring

/-! ## Deleted-player absorbing laws -/

/-- Nonempty opponent-coalition mass in the source row, normalized by the
full tail absorption scale. -/
def quittingTailConditionedOpponentCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (coalition : Finset ι) : ℝ :=
  quittingRootCoalitionMass
      (Function.update (roots time) who (PMF.pure false)) coalition /
    quittingTailEventualAbsorption roots time

/-- The rescaled target law with the selected player forced to Continue. -/
def quittingTailRescaledOpponentCoalitionMass
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (coalition : Finset ι) : ℝ :=
  quittingRootCoalitionMass
    (Function.update (quittingTailDiffuseRescaledRoot roots time hpositive)
      who (PMF.pure false)) coalition

theorem quittingTailConditionedOpponentCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (coalition : Finset ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    0 ≤ quittingTailConditionedOpponentCoalitionMass
      roots time who coalition :=
  div_nonneg (quittingRootCoalitionMass_nonneg' _ _) hpositive.le

theorem quittingTailRescaledOpponentCoalitionMass_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (coalition : Finset ι) :
    0 ≤ quittingTailRescaledOpponentCoalitionMass
      roots time who hpositive coalition :=
  quittingRootCoalitionMass_nonneg' _ _

/-- The nonempty normalized source opponent law has total mass equal to the
conditioned deleted-clock charge. -/
theorem sum_quittingTailConditionedOpponentCoalitionMass_nonempty
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        quittingTailConditionedOpponentCoalitionMass
          roots time who coalition) =
      quittingTailConditionedOpponentWeight roots time who := by
  unfold quittingTailConditionedOpponentCoalitionMass
  rw [← Finset.sum_div, quittingRootCoalitionMass_sum_nonempty]
  rfl

/-- The nonempty rescaled opponent law has total mass equal to target
opponent absorption. -/
theorem sum_quittingTailRescaledOpponentCoalitionMass_nonempty
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        quittingTailRescaledOpponentCoalitionMass
          roots time who hpositive coalition) =
      quittingRootOpponentAbsorptionMass
        (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
  unfold quittingTailRescaledOpponentCoalitionMass
  rw [quittingRootCoalitionMass_sum_nonempty]
  rfl

/-- Target singleton opponent atoms are dominated by their normalized source
counterparts. -/
theorem quittingTailRescaledOpponentCoalitionMass_singleton_le_conditioned
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who other : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    quittingTailRescaledOpponentCoalitionMass
        roots time who hpositive {other} ≤
      quittingTailConditionedOpponentCoalitionMass
        roots time who {other} := by
  let scale := quittingTailEventualAbsorption roots time
  let x : ι → ℝ := Function.update
    (quittingTailDiffuseRescaledHazard roots time) who 0
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_nonneg
          roots time player hpositive)
  have hx1 : ∀ player, x player ≤ 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_le_one
          roots time player hpositive)
  have htargetRates : quittingRootQuitRates
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hpositive)
        who (PMF.pure false)) = x := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      change hazardOfRoot
        (quittingTailDiffuseRescaledRoot roots time hpositive) player = _
      rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hsourceRates : quittingRootQuitRates
      (Function.update (roots time) who (PMF.pure false)) =
        fun player => scale * x player := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      unfold quittingTailDiffuseRescaledHazard scale
      field_simp [hpositive.ne']
  have hscaled := coalitionMass_singleton_le_scaled_div
    x scale other hpositive hscaleOne hx0 hx1
  unfold quittingTailRescaledOpponentCoalitionMass
    quittingTailConditionedOpponentCoalitionMass quittingRootCoalitionMass
  rw [htargetRates, hsourceRates]
  exact hscaled

/-- Source collision mass in the forced-Continue opponent law. -/
theorem conditionedOpponentCoalitionCollisionMass_le_total_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingTailConditionedOpponentCoalitionMass
          roots time who coalition) ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 := by
  let scale := quittingTailEventualAbsorption roots time
  let x : ι → ℝ := Function.update
    (quittingTailDiffuseRescaledHazard roots time) who 0
  have hscaleOne : scale ≤ 1 :=
    (quittingTailEventualAbsorption_mem_unitInterval roots time).2
  have hx0 : ∀ player, 0 ≤ x player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_nonneg
          roots time player hpositive)
  have hx1 : ∀ player, x player ≤ 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_le_one
          roots time player hpositive)
  have hsourceRates : quittingRootQuitRates
      (Function.update (roots time) who (PMF.pure false)) =
        fun player => scale * x player := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      unfold quittingTailDiffuseRescaledHazard scale
      field_simp [hpositive.ne']
  have hsum : (∑ player, x player) =
      quittingTailDiffuseRescaledOpponentTotal roots time who := by
    unfold x quittingTailDiffuseRescaledOpponentTotal
    rw [Finset.sum_update_of_mem (Finset.mem_univ who)]
    simp [Finset.erase_eq]
  have hcollision := collisionMass_scaled_div_le_sum_sq_div_two
    x scale hpositive hscaleOne hx0 hx1
  unfold quittingTailConditionedOpponentCoalitionMass
  rw [← Finset.sum_div]
  change collisionMass (quittingRootQuitRates
      (Function.update (roots time) who (PMF.pure false))) / scale ≤ _
  rw [hsourceRates]
  rw [hsum] at hcollision
  exact hcollision

/-- Target collision mass in the forced-Continue opponent law. -/
theorem rescaledOpponentCoalitionCollisionMass_le_total_sq_div_two
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    (∑ coalition ∈ quittingDiffuseCollisionCoalitions (ι := ι),
        quittingTailRescaledOpponentCoalitionMass
          roots time who hpositive coalition) ≤
      quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 := by
  let x : ι → ℝ := Function.update
    (quittingTailDiffuseRescaledHazard roots time) who 0
  have hx0 : ∀ player, 0 ≤ x player := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_nonneg
          roots time player hpositive)
  have hx1 : ∀ player, x player ≤ 1 := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp [x]
    · simpa [x, Function.update_of_ne hplayer] using
        (quittingTailDiffuseRescaledHazard_le_one
          roots time player hpositive)
  have htargetRates : quittingRootQuitRates
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hpositive)
        who (PMF.pure false)) = x := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootQuitRates, x]
    · simp only [quittingRootQuitRates, x,
        Function.update_of_ne hplayer]
      change hazardOfRoot
        (quittingTailDiffuseRescaledRoot roots time hpositive) player = _
      rw [hazardOfRoot_quittingTailDiffuseRescaledRoot]
  have hsum : (∑ player, x player) =
      quittingTailDiffuseRescaledOpponentTotal roots time who := by
    unfold x quittingTailDiffuseRescaledOpponentTotal
    rw [Finset.sum_update_of_mem (Finset.mem_univ who)]
    simp [Finset.erase_eq]
  have hcollision := collisionMass_le_sum_sq_div_two x hx0 hx1
  unfold quittingTailRescaledOpponentCoalitionMass
  change collisionMass (quittingRootQuitRates
      (Function.update
        (quittingTailDiffuseRescaledRoot roots time hpositive)
        who (PMF.pure false))) ≤ _
  rw [htargetRates]
  rw [hsum] at hcollision
  exact hcollision

/-- **Quadratic forced-Continue absorbing-law comparison.** -/
theorem abs_conditionedOpponentAbsorbingReward_sub_rescaled_le
    (roots : ℕ → ι → PMF Bool) (time : ℕ) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpositive : 0 < quittingTailEventualAbsorption roots time) :
    |quittingStationaryFixedOpponentsContinueReward reward (roots time) who /
          quittingTailEventualAbsorption roots time -
        quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who| ≤
      3 / 2 * M *
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 := by
  let payoff : Finset ι → ℝ := fun coalition =>
    if h : coalition.Nonempty then reward ⟨coalition, h⟩ who else 0
  have hpayoff : ∀ coalition, |payoff coalition| ≤ M := by
    intro coalition
    by_cases hcoalition : coalition.Nonempty
    · simpa [payoff, hcoalition] using hreward ⟨coalition, hcoalition⟩ who
    · simp [payoff, hcoalition, hM]
  have habstract :=
    abs_sum_nonempty_mul_sub_sum_nonempty_mul_le_of_singleton_domination
      (totalError :=
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)
      (targetCollision :=
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)
      (quittingTailConditionedOpponentCoalitionMass roots time who)
      (quittingTailRescaledOpponentCoalitionMass
        roots time who hpositive)
      payoff hM hpayoff
      (fun coalition => quittingTailConditionedOpponentCoalitionMass_nonneg
        roots time who coalition hpositive)
      (quittingTailRescaledOpponentCoalitionMass_nonneg
        roots time who hpositive)
      (fun other =>
        quittingTailRescaledOpponentCoalitionMass_singleton_le_conditioned
          roots time who other hpositive)
      (by
        rw [sum_quittingTailConditionedOpponentCoalitionMass_nonempty,
          sum_quittingTailRescaledOpponentCoalitionMass_nonempty]
        simpa using
          (abs_conditionedOpponentWeight_sub_rescaledRoot_opponentAbsorption_le
            roots time who hpositive))
      (rescaledOpponentCoalitionCollisionMass_le_total_sq_div_two
        roots time who hpositive)
  have hsource :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailConditionedOpponentCoalitionMass roots time who coalition *
            payoff coalition) =
        quittingStationaryFixedOpponentsContinueReward reward (roots time) who /
          quittingTailEventualAbsorption roots time := by
    unfold quittingTailConditionedOpponentCoalitionMass
    calc
      _ = (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingRootCoalitionMass
              (Function.update (roots time) who (PMF.pure false)) coalition *
            payoff coalition) /
          quittingTailEventualAbsorption roots time := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro coalition _
        ring
      _ = _ := by
        apply congrArg (fun z : ℝ =>
          z / quittingTailEventualAbsorption roots time)
        calc
          _ = ∑ coalition,
              quittingRootCoalitionMass
                  (Function.update (roots time) who (PMF.pure false)) coalition *
                quittingProjectiveCoalitionReward reward coalition who := by
            rw [← Finset.add_sum_erase Finset.univ
              (fun coalition => quittingRootCoalitionMass
                (Function.update (roots time) who (PMF.pure false)) coalition *
                  quittingProjectiveCoalitionReward reward coalition who)
              (Finset.mem_univ ∅)]
            simp only [quittingProjectiveCoalitionReward_empty, mul_zero,
              zero_add]
            apply Finset.sum_congr rfl
            intro coalition hcoalition
            have hnonempty : coalition.Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr
                (Finset.ne_of_mem_erase hcoalition)
            simp [payoff, quittingProjectiveCoalitionReward, hnonempty]
          _ = quittingRootAbsorbingContribution reward
              (Function.update (roots time) who (PMF.pure false)) who :=
            (quittingRootAbsorbingContribution_eq_sum_coalitionMass
              reward _ who).symm
  have htarget :
      (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
          quittingTailRescaledOpponentCoalitionMass
              roots time who hpositive coalition * payoff coalition) =
        quittingStationaryFixedOpponentsContinueReward reward
          (quittingTailDiffuseRescaledRoot roots time hpositive) who := by
    unfold quittingTailRescaledOpponentCoalitionMass
    calc
      _ = ∑ coalition,
          quittingRootCoalitionMass
            (Function.update
              (quittingTailDiffuseRescaledRoot roots time hpositive)
              who (PMF.pure false)) coalition *
            quittingProjectiveCoalitionReward reward coalition who := by
        rw [← Finset.add_sum_erase Finset.univ
          (fun coalition => quittingRootCoalitionMass
            (Function.update
              (quittingTailDiffuseRescaledRoot roots time hpositive)
              who (PMF.pure false)) coalition *
              quittingProjectiveCoalitionReward reward coalition who)
          (Finset.mem_univ ∅)]
        simp only [quittingProjectiveCoalitionReward_empty, mul_zero, zero_add]
        apply Finset.sum_congr rfl
        intro coalition hcoalition
        have hnonempty : coalition.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr
            (Finset.ne_of_mem_erase hcoalition)
        simp [payoff, quittingProjectiveCoalitionReward, hnonempty]
      _ = quittingRootAbsorbingContribution reward
          (Function.update
            (quittingTailDiffuseRescaledRoot roots time hpositive)
            who (PMF.pure false)) who :=
        (quittingRootAbsorbingContribution_eq_sum_coalitionMass
          reward _ who).symm
      _ = _ := rfl
  rw [← hsource, ← htarget]
  calc
    |_ - _| ≤ M *
        (quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2 +
          2 * (quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 / 2)) :=
      habstract
    _ = 3 / 2 * M *
        quittingTailDiffuseRescaledOpponentTotal roots time who ^ 2 := by ring

end GameTheory
