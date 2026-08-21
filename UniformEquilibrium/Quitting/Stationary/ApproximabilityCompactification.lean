/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.R0Margin
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Circulation.DirectionBarycenter
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling

/-!
# Compactifying stationary approximate equilibria

A vanishing family of stationary approximate equilibria has three possible
compactification regimes.  Positive limiting absorption gives an exact
stationary fixed point.  At vanishing absorption, a tangential family whose
equilibrium error is little-o of total hazard gives a homogeneous singleton
LCP solution.  The remaining radial family stays quantitatively close to the
all-Continue apex.

This file supplies the quantitative tangent estimate and the compactness
interface.  It makes no claim that stationary approximate equilibria exist.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open Math.LinearProgramming Math.ProbabilityMassFunction Math.Topology
open QuittingLCPClassification

variable {iota : Type} [Fintype iota] [DecidableEq iota] [Nonempty iota]

omit [Nonempty iota] in
/-- Opponent absorption is bounded by the total stationary hazard. -/
theorem quittingRootOpponentAbsorptionMass_le_stationaryTotalHazard
    (root : iota → PMF Bool) (who : iota) :
    quittingRootOpponentAbsorptionMass root who ≤
      quittingStationaryTotalHazard root := by
  let deleted := Function.update root who (PMF.pure false)
  have hmass : quittingRootOpponentAbsorptionMass root who =
      quittingRootAbsorptionMass deleted := rfl
  rw [hmass]
  refine (quittingRootAbsorptionMass_le_stationaryTotalHazard deleted).trans ?_
  unfold quittingStationaryTotalHazard
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ who)]
  have hdeleted :
      ∑ owner ∈ Finset.univ.erase who, (deleted owner true).toReal =
        ∑ owner ∈ Finset.univ.erase who, (root owner true).toReal := by
    apply Finset.sum_congr rfl
    intro owner howner
    simp [deleted, Function.update_of_ne (Finset.mem_erase.mp howner).1]
  rw [hdeleted]
  simp only [deleted, Function.update_self, PMF.pure_apply,
    Bool.true_eq_false, reduceIte, ENNReal.toReal_zero, add_zero]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun _ _ _ ↦ ENNReal.toReal_nonneg)

omit [Nonempty iota] in
/-- On the normalized hazard simplex, the singleton LCP residual is the
singleton-reward barycenter minus the player's own singleton payoff. -/
theorem singletonLCPResidual_normalizedSoloMatrix_hazardDirection
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (root : iota → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root) (who : iota) :
    singletonLCPResidual (normalizedSoloMatrix reward)
        (quittingStationaryHazardDirection root hpositive) who =
      quittingStationarySingletonDirectionBarycenter reward root who -
        quittingSoloReward reward who who := by
  classical
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold singletonLCPResidual wsum dotProduct quittingProjectiveLCPMatrix
    quittingStationarySingletonDirectionBarycenter
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hmass :
      ∑ owner, quittingStationaryHazardDirection root hpositive owner = 1 :=
    (quittingStationaryHazardDirection root hpositive).property.2
  rw [← Finset.sum_mul, hmass, one_mul]
  congr 1

/-- At small total hazard, the stationary endpoint difference is within
`10 M H` of the negative normalized singleton-LCP residual. -/
theorem abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {M : ℝ} (hreward : ∀ S who, |reward S who| ≤ M)
    (root : iota → PMF Bool) (who : iota)
    (hpositive : 0 < quittingStationaryTotalHazard root)
    (hhalf : quittingStationaryTotalHazard root ≤ 1 / 2) :
    |quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who +
        singletonLCPResidual (normalizedSoloMatrix reward)
          (quittingStationaryHazardDirection root hpositive) who| ≤
      10 * M * quittingStationaryTotalHazard root := by
  let H := quittingStationaryTotalHazard root
  let value := quittingTerminalPayoff reward
    (quittingStationaryProfile reward root) who
  let solo := quittingSoloReward reward who who
  let mixture := quittingStationarySingletonDirectionBarycenter reward root who
  let opponentMass := quittingRootOpponentAbsorptionMass root who
  let quitValue := quittingStationaryFixedOpponentsQuitValue reward root who
  let continueReward := quittingStationaryFixedOpponentsContinueReward reward root who
  let continueMass := quittingStationaryFixedOpponentsContinueMass root who
  have hM : 0 ≤ M := by
    let player : iota := Classical.arbitrary iota
    exact (abs_nonneg (reward ⟨{player}, Finset.singleton_nonempty player⟩ player)).trans
      (hreward ⟨{player}, Finset.singleton_nonempty player⟩ player)
  have hopponent0 : 0 ≤ opponentMass := quittingRootAbsorptionMass_nonneg _
  have hopponent : opponentMass ≤ H :=
    quittingRootOpponentAbsorptionMass_le_stationaryTotalHazard root who
  have hvalue : |value| ≤ M :=
    abs_quittingTerminalPayoff_le reward _ who (fun S player ↦ hreward S player)
  have hquit : |quitValue - solo| ≤ 2 * M * opponentMass := by
    change |quittingStationaryFixedOpponentsQuitValue reward root who -
        reward (quittingSingletonTerminal who) who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root who
    simpa using
      (abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
        (reward := reward) root who hreward)
  have hcontinue : |continueReward| ≤ M * opponentMass := by
    change |quittingFixedOpponentsContinueReward reward (fun _ ↦ root) who 0| ≤
      M * (1 - quittingFixedOpponentsContinueMass (fun _ ↦ root) who 0)
    simpa using
      (abs_quittingFixedOpponentsContinueReward_le_hazard
        reward (fun _ ↦ root) who 0 M hM (fun S ↦ hreward S who))
  have hcontinueMass : 1 - continueMass = opponentMass := rfl
  have hcontinueValue :
      |continueReward + continueMass * value - value| ≤
        2 * M * opponentMass := by
    have hsplit : continueReward + continueMass * value - value =
        continueReward - (1 - continueMass) * value := by ring
    rw [hsplit, hcontinueMass]
    calc
      |continueReward - opponentMass * value| ≤
          |continueReward| + |opponentMass * value| := abs_sub _ _
      _ ≤ M * opponentMass + opponentMass * M := by
        apply add_le_add hcontinue
        rw [abs_mul, abs_of_nonneg hopponent0]
        exact mul_le_mul_of_nonneg_left hvalue hopponent0
      _ = 2 * M * opponentMass := by ring
  have hendpoint : quittingRootEndpointDifference reward
        (fun player ↦ quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) player)
        root who = quitValue - (continueReward + continueMass * value) := by
    simpa [quitValue, continueReward, continueMass, value] using
      quittingRootEndpointDifference_stationary_eq reward root who
  have hlocal :
      |quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who - (solo - value)| ≤ 4 * M * H := by
    rw [hendpoint]
    have hsplit :
        quitValue - (continueReward + continueMass * value) - (solo - value) =
          (quitValue - solo) - (continueReward + continueMass * value - value) := by
      ring
    rw [hsplit]
    calc
      |(quitValue - solo) -
          (continueReward + continueMass * value - value)| ≤
          |quitValue - solo| +
            |continueReward + continueMass * value - value| := abs_sub _ _
      _ ≤ 2 * M * opponentMass + 2 * M * opponentMass :=
        add_le_add hquit hcontinueValue
      _ ≤ 4 * M * H := by nlinarith
  have hbary : |value - mixture| ≤ 6 * M * H := by
    simpa [value, mixture, H] using
      (abs_stationaryPayoff_sub_singletonDirectionBarycenter_le
        reward hreward root who hpositive hhalf)
  rw [singletonLCPResidual_normalizedSoloMatrix_hazardDirection
    reward root hpositive who]
  have hsum :
      quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who + (mixture - solo) =
        (quittingRootEndpointDifference reward
          (fun player ↦ quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) player)
          root who - (solo - value)) + (mixture - value) := by ring
  rw [hsum]
  calc
    |_ + (mixture - value)| ≤ |_| + |mixture - value| := abs_add_le _ _
    _ ≤ 4 * M * H + 6 * M * H := by
      exact add_le_add hlocal (by simpa [abs_sub_comm] using hbary)
    _ = 10 * M * quittingStationaryTotalHazard root := by
      dsimp only [H]
      ring

/-- Approximate endpoint complementarity controls every negative singleton
LCP residual at the normalized hazard direction. -/
theorem neg_singletonLCPResidual_hazardDirection_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {M epsilon : ℝ} (hreward : ∀ S who, |reward S who| ≤ M)
    (hepsilon : 0 ≤ epsilon) (root : iota → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root)
    (hhalf : quittingStationaryTotalHazard root ≤ 1 / 2)
    (hendpoint : IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player)
      epsilon root) (who : iota) :
    -singletonLCPResidual (normalizedSoloMatrix reward)
        (quittingStationaryHazardDirection root hpositive) who ≤
      10 * M * quittingStationaryTotalHazard root + 2 * epsilon := by
  let difference := quittingRootEndpointDifference reward
    (fun player ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player) root who
  let residual := singletonLCPResidual (normalizedSoloMatrix reward)
    (quittingStationaryHazardDirection root hpositive) who
  let hazard := (root who true).toReal
  have hhazard0 : 0 ≤ hazard := ENNReal.toReal_nonneg
  have hhazard : hazard ≤ quittingStationaryTotalHazard root := by
    unfold quittingStationaryTotalHazard
    change (root who true).toReal ≤ ∑ player, (root player true).toReal
    exact Finset.single_le_sum
      (fun player _ ↦ ENNReal.toReal_nonneg (a := root player true))
      (Finset.mem_univ who)
  have hcontinue : (root who false).toReal = 1 - hazard := by
    dsimp only [hazard]
    linarith [quittingRoot_continueProbability_add_quitProbability root who]
  have hcontinueHalf : 1 / 2 ≤ (root who false).toReal := by
    rw [hcontinue]
    linarith
  have hdifference : difference ≤ 2 * epsilon := by
    by_cases hnonpos : difference ≤ 0
    · linarith
    · have hsign : 0 < difference := lt_of_not_ge hnonpos
      have hproduct := (hendpoint who).1
      change (root who false).toReal * difference ≤ epsilon at hproduct
      have hcontinuePos : 0 < (root who false).toReal :=
        lt_of_lt_of_le (by norm_num) hcontinueHalf
      nlinarith [mul_pos hcontinuePos hsign]
  have hclose := abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
    reward hreward root who hpositive hhalf
  change |difference + residual| ≤
    10 * M * quittingStationaryTotalHazard root at hclose
  have hlower := (abs_le.mp hclose).1
  linarith

/-- The hazard-weighted quadratic singleton residual is controlled by the
endpoint error divided by total hazard, plus the direction-chart error. -/
theorem sum_hazardDirection_mul_singletonLCPResidual_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {M epsilon : ℝ} (hreward : ∀ S who, |reward S who| ≤ M)
    (root : iota → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root)
    (hhalf : quittingStationaryTotalHazard root ≤ 1 / 2)
    (hendpoint : IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player)
      epsilon root) :
    (∑ who, (quittingStationaryHazardDirection root hpositive).val who *
        singletonLCPResidual (normalizedSoloMatrix reward)
          (quittingStationaryHazardDirection root hpositive) who) ≤
      10 * M * quittingStationaryTotalHazard root +
        Fintype.card iota * epsilon / quittingStationaryTotalHazard root := by
  let H := quittingStationaryTotalHazard root
  let direction := quittingStationaryHazardDirection root hpositive
  let difference := fun who ↦ quittingRootEndpointDifference reward
    (fun player ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) player) root who
  let residual := fun who ↦ singletonLCPResidual (normalizedSoloMatrix reward)
    direction who
  have hterm : ∀ who,
      direction.val who * residual who ≤
        direction.val who * (10 * M * H) + epsilon / H := by
    intro who
    have hclose := abs_quittingRootEndpointDifference_add_singletonLCPResidual_le
      reward hreward root who hpositive hhalf
    change |difference who + residual who| ≤ 10 * M * H at hclose
    have hupper := (abs_le.mp hclose).2
    have hdirection0 : 0 ≤ direction.val who := direction.property.1 who
    have hweighted := mul_le_mul_of_nonneg_left hupper hdirection0
    have hnash := (hendpoint who).2
    change -epsilon ≤ (root who true).toReal * difference who at hnash
    have hcoordinate : direction.val who = (root who true).toReal / H := rfl
    rw [hcoordinate] at hweighted
    have hraw : (root who true).toReal *
          (difference who + residual who) ≤
        (root who true).toReal * (10 * M * H) := by
      apply (div_le_div_iff_of_pos_right hpositive).mp
      simpa [div_mul_eq_mul_div] using hweighted
    have hscaled : (root who true).toReal * residual who ≤
        (root who true).toReal * (10 * M * H) + epsilon := by
      nlinarith
    have hdiv := (div_le_div_iff_of_pos_right hpositive).2 hscaled
    rw [hcoordinate]
    calc
      (root who true).toReal / H * residual who =
          ((root who true).toReal * residual who) / H := by ring
      _ ≤ ((root who true).toReal * (10 * M * H) + epsilon) / H := hdiv
      _ = (root who true).toReal / H * (10 * M * H) + epsilon / H := by ring
  calc
    (∑ who, direction.val who * residual who) ≤
        ∑ who, (direction.val who * (10 * M * H) + epsilon / H) :=
      Finset.sum_le_sum (fun who _ ↦ hterm who)
    _ = 10 * M * H + Fintype.card iota * epsilon / H := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, direction.property.2,
        one_mul, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-- Quantitative tangent estimate: endpoint `epsilon`-Nash at total hazard
`H` gives homogeneous violation `O(H + epsilon + epsilon/H)`. -/
theorem homogeneousViolation_hazardDirection_le
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {M epsilon : ℝ} (hreward : ∀ S who, |reward S who| ≤ M)
    (hepsilon : 0 ≤ epsilon) (root : iota → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root)
    (hhalf : quittingStationaryTotalHazard root ≤ 1 / 2)
    (hendpoint : IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player)
      epsilon root) :
    homogeneousViolation (normalizedSoloMatrix reward)
        (quittingStationaryHazardDirection root hpositive).val ≤
      (Fintype.card iota + 1) *
          (10 * M * quittingStationaryTotalHazard root) +
        2 * Fintype.card iota * epsilon +
        Fintype.card iota * epsilon / quittingStationaryTotalHazard root := by
  let H := quittingStationaryTotalHazard root
  let direction := quittingStationaryHazardDirection root hpositive
  let residual := fun who ↦ singletonLCPResidual (normalizedSoloMatrix reward)
    direction who
  have hquadratic :
      max 0 (∑ who, direction.val who * residual who) ≤
        10 * M * H + Fintype.card iota * epsilon / H := by
    apply max_le
    · have hM : 0 ≤ M := by
        let player : iota := Classical.arbitrary iota
        exact (abs_nonneg
          (reward ⟨{player}, Finset.singleton_nonempty player⟩ player)).trans
          (hreward ⟨{player}, Finset.singleton_nonempty player⟩ player)
      positivity
    · simpa [H, direction, residual] using
        (sum_hazardDirection_mul_singletonLCPResidual_le
          reward hreward root hpositive hhalf hendpoint)
  have hnegative : ∀ who, max 0 (-residual who) ≤ 10 * M * H + 2 * epsilon := by
    intro who
    apply max_le
    · have hM : 0 ≤ M := by
        let player : iota := Classical.arbitrary iota
        exact (abs_nonneg
          (reward ⟨{player}, Finset.singleton_nonempty player⟩ player)).trans
          (hreward ⟨{player}, Finset.singleton_nonempty player⟩ player)
      positivity
    · simpa [H, direction, residual] using
        (neg_singletonLCPResidual_hazardDirection_le
          reward hreward hepsilon root hpositive hhalf hendpoint who)
  unfold homogeneousViolation
  change max 0 (∑ who, direction.val who * residual who) +
      ∑ who, max 0 (-residual who) ≤ _
  calc
    max 0 (∑ who, direction.val who * residual who) +
        ∑ who, max 0 (-residual who) ≤
      (10 * M * H + Fintype.card iota * epsilon / H) +
        ∑ who, (10 * M * H + 2 * epsilon) :=
      add_le_add hquadratic (Finset.sum_le_sum (fun who _ ↦ hnegative who))
    _ = (Fintype.card iota + 1) * (10 * M * H) +
        2 * Fintype.card iota * epsilon +
        Fintype.card iota * epsilon / H := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

/-- The `R₀` margin inherits the same tangent bound. -/
theorem r0Margin_normalizedSoloMatrix_le_of_stationaryEndpointNash
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {M epsilon : ℝ} (hreward : ∀ S who, |reward S who| ≤ M)
    (hepsilon : 0 ≤ epsilon) (root : iota → PMF Bool)
    (hpositive : 0 < quittingStationaryTotalHazard root)
    (hhalf : quittingStationaryTotalHazard root ≤ 1 / 2)
    (hendpoint : IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) player)
      epsilon root) :
    r0Margin (normalizedSoloMatrix reward) ≤
      (Fintype.card iota + 1) *
          (10 * M * quittingStationaryTotalHazard root) +
        2 * Fintype.card iota * epsilon +
        Fintype.card iota * epsilon / quittingStationaryTotalHazard root := by
  exact (r0Margin_le (normalizedSoloMatrix reward)
    (quittingStationaryHazardDirection root hpositive).property).trans
      (homogeneousViolation_hazardDirection_le
        reward hreward hepsilon root hpositive hhalf hendpoint)

/-- A tangential vanishing-hazard family of stationary endpoint equilibria
produces a homogeneous singleton-LCP solution.  Tangential means that both
the total hazard and `epsilon / hazard` tend to zero. -/
theorem singletonLCPFeasible_of_stationaryEndpointNash_tangent
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (epsilon : ℕ → ℝ) (roots : ℕ → iota → PMF Bool)
    (hepsilon : ∀ n, 0 ≤ epsilon n)
    (hpositive : ∀ n, 0 < quittingStationaryTotalHazard (roots n))
    (hhalf : ∀ n, quittingStationaryTotalHazard (roots n) ≤ 1 / 2)
    (hendpoint : ∀ n, IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward (roots n)) player)
      (epsilon n) (roots n))
    (hhazard : Tendsto
      (fun n ↦ quittingStationaryTotalHazard (roots n)) atTop (nhds 0))
    (htangent : Tendsto
      (fun n ↦ epsilon n / quittingStationaryTotalHazard (roots n))
      atTop (nhds 0)) :
    SingletonLCPFeasible (normalizedSoloMatrix reward) := by
  let M := quittingRewardBound reward
  let error : ℕ → ℝ := fun n ↦
    (Fintype.card iota + 1) *
        (10 * M * quittingStationaryTotalHazard (roots n)) +
      2 * Fintype.card iota * epsilon n +
      Fintype.card iota *
        (epsilon n / quittingStationaryTotalHazard (roots n))
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    have hfactor : ∀ n, epsilon n =
        (epsilon n / quittingStationaryTotalHazard (roots n)) *
          quittingStationaryTotalHazard (roots n) := by
      intro n
      field_simp [(hpositive n).ne']
    have hproduct := htangent.mul hhazard
    convert hproduct using 1
    · funext n
      exact hfactor n
    · norm_num
  have herror : Tendsto error atTop (nhds 0) := by
    dsimp only [error]
    have hfirst := (hhazard.const_mul (10 * M)).const_mul
      ((Fintype.card iota : ℝ) + 1)
    have hsecond := hepsilonZero.const_mul
      (2 * (Fintype.card iota : ℝ))
    have hthird := htangent.const_mul (Fintype.card iota : ℝ)
    convert (hfirst.add hsecond).add hthird using 1
    all_goals norm_num
  have hmargin : r0Margin (normalizedSoloMatrix reward) ≤ 0 := by
    apply ge_of_tendsto' herror
    intro n
    dsimp only [error]
    have hbound :=
      r0Margin_normalizedSoloMatrix_le_of_stationaryEndpointNash
        reward (abs_reward_le_quittingRewardBound reward) (hepsilon n)
        (roots n) (hpositive n) (hhalf n) (hendpoint n)
    dsimp only [M]
    simpa only [mul_div_assoc] using hbound
  have hmarginZero : r0Margin (normalizedSoloMatrix reward) = 0 :=
    le_antisymm hmargin (r0Margin_nonneg (normalizedSoloMatrix reward))
  obtain ⟨p, hp, hvalue⟩ :=
    exists_mem_stdSimplex_homogeneousViolation_eq_r0Margin
      (normalizedSoloMatrix reward)
  apply singletonLCPFeasible_of_violation_nonpos
    (normalizedSoloMatrix reward) hp
  rw [hvalue, hmarginZero]

omit [Nonempty iota] in
/-- A vanishing-error stationary family whose total hazards stay uniformly
away from zero has a compact limit which is an exact absorbing stationary
fixed point and exact endpoint equilibrium. -/
theorem exists_exactStationaryEndpoint_of_hazard_floor
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (epsilon : ℕ → ℝ) (roots : ℕ → iota → PMF Bool)
    {floor : ℝ} (hfloor : 0 < floor)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hhazard : ∀ n, floor ≤ quittingStationaryTotalHazard (roots n))
    (hendpoint : ∀ n, IsεQuittingRootEndpointNash reward
      (fun player ↦ quittingTerminalPayoff reward
        (quittingStationaryProfile reward (roots n)) player)
      (epsilon n) (roots n)) :
    ∃ value : Payoff iota, ∃ root : QuittingRootSimplex iota,
      0 < quittingStationaryTotalHazard (quittingRootOfSimplex root) ∧
      value = quittingRootSuccessorPayoff reward value
        (quittingRootOfSimplex root) ∧
      IsεQuittingRootEndpointNash reward value 0
        (quittingRootOfSimplex root) := by
  let simplexRoots : ℕ → QuittingRootSimplex iota := fun n who ↦
    stdSimplexEquiv (roots n who)
  let values : ℕ → Payoff iota := fun n ↦
    quittingTerminalPayoff reward
      (quittingStationaryProfile reward (roots n))
  let points : ℕ → QuittingNashBellmanPoint iota := fun n ↦
    (values n, simplexRoots n)
  have hrootEq : ∀ n, quittingRootOfSimplex (simplexRoots n) = roots n := by
    intro n
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (roots n who)
  have hmem : ∀ n, points n ∈
      quittingNashBellmanBox (ι := iota) (quittingRewardBound reward) := by
    intro n
    change values n ∈ Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)
    exact quittingTerminalPayoff_mem_rewardCube reward _
  obtain ⟨point, hpoint, subsequence, hsubsequence, hlimit⟩ :=
    (quittingNashBellmanBox_isCompact
      (ι := iota) (quittingRewardBound reward)).tendsto_subseq hmem
  have hvalueLimit : Tendsto (values ∘ subsequence) atTop (nhds point.1) :=
    (continuous_fst.tendsto point).comp hlimit
  have hrootLimit : Tendsto (simplexRoots ∘ subsequence) atTop
      (nhds point.2) := (continuous_snd.tendsto point).comp hlimit
  have hepsilonLimit : Tendsto (epsilon ∘ subsequence) atTop (nhds 0) :=
    hepsilon.comp hsubsequence.tendsto_atTop
  have hexactEndpoint : IsεQuittingRootEndpointNash reward point.1 0
      (quittingRootOfSimplex point.2) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward
      (epsilon ∘ subsequence) (values ∘ subsequence)
      (simplexRoots ∘ subsequence)
      hepsilonLimit hvalueLimit hrootLimit
    exact Filter.Eventually.of_forall fun n ↦ by
      change IsεQuittingRootEndpointNash reward (values (subsequence n))
        (epsilon (subsequence n))
        (quittingRootOfSimplex (simplexRoots (subsequence n)))
      rw [hrootEq]
      exact hendpoint (subsequence n)
  have hfixedSeq : ∀ n, values n =
      quittingRootSuccessorPayoff reward (values n) (roots n) := by
    intro n
    funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff
      reward (roots n) who
  have hsuccessorLimit : Tendsto
      (fun n ↦ quittingRootSuccessorPayoff reward
        (values (subsequence n)) (roots (subsequence n)))
      atTop (nhds (quittingRootSuccessorPayoff reward point.1
        (quittingRootOfSimplex point.2))) := by
    have hpair : Tendsto
        (fun n ↦ (values (subsequence n), simplexRoots (subsequence n)))
        atTop (nhds (point.1, point.2)) :=
      hvalueLimit.prodMk_nhds hrootLimit
    have hcontinuous : ContinuousAt
        (fun point : Payoff iota × QuittingRootSimplex iota ↦
          quittingRootSuccessorPayoff reward point.1
            (quittingRootOfSimplex point.2))
        (point.1, point.2) :=
      (continuous_quittingRootSuccessorPayoff_simplex reward).continuousAt
    have ht := hcontinuous.tendsto.comp hpair
    apply ht.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      change quittingRootSuccessorPayoff reward (values (subsequence n))
          (quittingRootOfSimplex (simplexRoots (subsequence n))) =
        quittingRootSuccessorPayoff reward (values (subsequence n))
          (roots (subsequence n))
      rw [hrootEq]
  have hfixed : point.1 = quittingRootSuccessorPayoff reward point.1
      (quittingRootOfSimplex point.2) := by
    apply tendsto_nhds_unique hvalueLimit
    apply hsuccessorLimit.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      change quittingRootSuccessorPayoff reward (values (subsequence n))
        (roots (subsequence n)) = values (subsequence n)
      exact (hfixedSeq (subsequence n)).symm
  have hhazardLimit : Tendsto
      (fun n ↦ quittingStationaryTotalHazard
        (roots (subsequence n))) atTop
      (nhds (quittingStationaryTotalHazard
        (quittingRootOfSimplex point.2))) := by
    have hcontinuous : Continuous (fun root : QuittingRootSimplex iota ↦
        ∑ who, root who true) := by
      apply continuous_finsetSum
      intro who _
      exact (continuous_apply true).comp
        (continuous_subtype_val.comp (continuous_apply who))
    have ht := hcontinuous.continuousAt.tendsto.comp hrootLimit
    convert ht using 1
    · funext n
      unfold quittingStationaryTotalHazard
      apply Finset.sum_congr rfl
      intro who _
      simp [simplexRoots, Function.comp_apply,
        Math.ProbabilityMassFunction.toVector]
    · unfold quittingStationaryTotalHazard
      apply congrArg nhds
      apply Finset.sum_congr rfl
      intro who _
      exact quittingRootOfSimplex_apply_toReal point.2 who true
  have hhazardLimitFloor : floor ≤ quittingStationaryTotalHazard
      (quittingRootOfSimplex point.2) :=
    ge_of_tendsto' hhazardLimit fun n ↦ hhazard (subsequence n)
  exact ⟨point.1, point.2, hfloor.trans_le hhazardLimitFloor,
    hfixed, hexactEndpoint⟩

omit [Nonempty iota] in
/-- **Stationary compactification converse.**  If stationary terminal
approximate equilibria exist at every accuracy, then either an absorbing
exact stationary endpoint fixed point exists, or approximate equilibria can
be chosen arbitrarily close to the all-Continue apex.  The tangent theorem
above refines vanishing-hazard families with `epsilon / H → 0` to the
homogeneous LCP boundary. -/
theorem exactStationaryEndpoint_or_nearAllContinue_of_stationaryApproximable
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ root : iota → PMF Bool,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) epsilon
          (quittingStationaryProfile reward root)) :
    (∃ value : Payoff iota, ∃ root : QuittingRootSimplex iota,
      0 < quittingStationaryTotalHazard (quittingRootOfSimplex root) ∧
      value = quittingRootSuccessorPayoff reward value
        (quittingRootOfSimplex root) ∧
      IsεQuittingRootEndpointNash reward value 0
        (quittingRootOfSimplex root)) ∨
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ root : iota → PMF Bool,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) epsilon
          (quittingStationaryProfile reward root) ∧
        ∀ who, (root who true).toReal < epsilon) := by
  classical
  by_cases hnear : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ root : iota → PMF Bool,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) epsilon
          (quittingStationaryProfile reward root) ∧
        ∀ who, (root who true).toReal < epsilon
  · exact Or.inr hnear
  · left
    push Not at hnear
    obtain ⟨floor, hfloor, hfar⟩ := hnear
    let epsilon : ℕ → ℝ := fun n ↦ floor / (n + 2)
    have hepsilonPositive : ∀ n, 0 < epsilon n := by
      intro n
      dsimp only [epsilon]
      positivity
    choose roots hnash using fun n ↦ happrox (epsilon n) (hepsilonPositive n)
    have hepsilonLimit : Tendsto epsilon atTop (nhds 0) := by
      dsimp only [epsilon]
      have ht := (tendsto_const_div_atTop_nhds_zero_nat floor).comp
        (tendsto_add_atTop_nat 2)
      convert ht using 1
      funext n
      norm_num [Function.comp_apply, Nat.cast_add]
    have hepsilonFloor : ∀ n, epsilon n ≤ floor := by
      intro n
      dsimp only [epsilon]
      have hdenom : (1 : ℝ) ≤ (n : ℝ) + 2 := by
        have hnat : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by
        have hnat : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      apply (div_le_iff₀ hpos).2
      nlinarith
    have hhazard : ∀ n,
        floor ≤ quittingStationaryTotalHazard (roots n) := by
      intro n
      have hfloorNash := StochasticGame.IsεAsymptoticNash.mono
        (hnash n) (hepsilonFloor n)
      obtain ⟨who, hwho⟩ := hfar (roots n) hfloorNash
      unfold quittingStationaryTotalHazard
      exact hwho.trans
        (Finset.single_le_sum
          (fun player _ ↦ ENNReal.toReal_nonneg (a := roots n player true))
          (Finset.mem_univ who))
    have hendpoint : ∀ n, IsεQuittingRootEndpointNash reward
        (fun player ↦ quittingTerminalPayoff reward
          (quittingStationaryProfile reward (roots n)) player)
        (epsilon n) (roots n) := by
      intro n
      apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward _ _ _).2
      exact isεQuittingRootNash_of_isεAsymptoticNash_stationary
        reward (roots n) (epsilon n) (hnash n)
    exact exists_exactStationaryEndpoint_of_hazard_floor
      reward epsilon roots hfloor hepsilonLimit hhazard hendpoint

end GameTheory
