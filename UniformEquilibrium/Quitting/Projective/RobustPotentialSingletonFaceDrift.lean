import MathUE.Analysis.CollisionAdjustedDrift
import MathUE.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction
import UniformEquilibrium.Quitting.Root.CollisionAdjustedSingletonProbe

/-! # Robust singleton-face drift with the actual derivative coefficient sum

The collision-adjusted source and exact Nash solo root are canonical. Every
unit-cube direction perturbs that same successor inside the original robust
box for sufficiently small rates. The resulting actual edges force the
derivative inequality, and an internally produced sign direction supplies
its absolute coordinate sum. No matrix or singleton-sign premise is used.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every unit-cube direction is realized by perturbed actual robust targets.
Differentiability is needed only at the queried singleton-face point. -/
theorem quittingRobustPotential_singletonFace_directional_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htolerance : 0 ≤ tolerance) (potential : Payoff ι → ℝ)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (M + 2)).IsPotential
        (fun state => potential state.1))
    (point : Payoff ι) (owner : ι)
    (hpoint : ∀ who,
      quittingSoloReward reward who who ≤ point who ∧ point who ≤ M + 1)
    (howner : point owner = quittingSoloReward reward owner owner)
    (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point)
    (direction : Payoff ι) (hdirection : ∀ who, |direction who| ≤ 1) :
    1 + tolerance * derivative direction ≤
      derivative (point - quittingSoloReward reward owner) := by
  let correction := quittingSingletonProbeCorrection reward (M + 2) point owner
  let target : ℝ → Payoff ι := fun rate => point + rate •
    (correction + quittingSoloReward reward owner - point + tolerance • direction)
  have hpointAbs : ∀ who, |point who| ≤ M + 1 := by
    intro who
    apply abs_le.mpr
    have hsolo := neg_le_of_abs_le (hreward (quittingSingletonTerminal who) who)
    change -M ≤ quittingSoloReward reward who who at hsolo
    exact ⟨by linarith [(hpoint who).1], (hpoint who).2⟩
  have htargetSmall : ∀ᶠ rate : ℝ in 𝓝 0,
      ∀ who, |target rate who| ≤ M + 2 := by
    apply Filter.eventually_all.mpr
    intro who
    have hcontinuous : ContinuousAt (fun rate : ℝ => |target rate who|) 0 := by
      unfold target
      fun_prop
    have hstrict : |target 0 who| < M + 2 := by
      simpa only [target, zero_smul, add_zero] using
        (hpointAbs who).trans_lt (show M + 1 < M + 2 by linarith)
    exact (hcontinuous.eventually (gt_mem_nhds hstrict)).mono fun _ hrate => hrate.le
  obtain ⟨ε, hε1, hε0, hprobe⟩ := exists_small_rates_quittingSingletonProbe
    reward hreward (show M < M + 2 by linarith) point owner
    (fun who => ⟨(hpoint who).1, (hpoint who).2.trans (by linarith)⟩) howner
  have hlimit := Math.tendsto_collisionAdjusted_potential_differenceQuotient
    potential derivative point correction
    (quittingSoloReward reward owner + tolerance • direction) hdiff
  have hquotient : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      1 ≤ (potential (point + (rate / (1 - rate)) • correction) -
        potential (point + rate •
          (correction + (quittingSoloReward reward owner + tolerance • direction) - point))) /
        rate := by
    have hsmall : ∀ᶠ rate : ℝ in 𝓝[>] 0, rate < ε :=
      nhdsWithin_le_nhds (gt_mem_nhds hε0)
    filter_upwards [self_mem_nhdsWithin, hsmall,
      (nhdsWithin_le_nhds htargetSmall)] with rate hrate hsmall htargetBox
    change 0 < rate at hrate
    have hrate1 : rate ≤ 1 := (lt_trans hsmall hε1).le
    obtain ⟨hsourceBox, hnash, _, habsorption⟩ := hprobe rate hrate hsmall
    let source : QuittingRobustChargedState ι (M + 2) :=
      ⟨quittingSingletonProbeSource reward (M + 2) point owner rate, hsourceBox⟩
    let successor : QuittingRobustChargedState ι (M + 2) :=
      ⟨target rate, htargetBox⟩
    let root := quittingSingletonProbeRoot owner rate hrate.le hrate1
    have htargetEq : target rate =
        quittingRootSuccessorPayoff reward source.1 root +
          (tolerance * rate) • direction := by
      ext who
      have hactual := quittingSingletonProbeSuccessor_eq_affine reward (M + 2)
        point owner rate hrate.le hrate1 (ne_of_lt (lt_trans hsmall hε1)) who
      change quittingRootSuccessorPayoff reward source.1 root who = _ at hactual
      change point who + rate *
          (correction who + quittingSoloReward reward owner who - point who +
            tolerance * direction who) =
        quittingRootSuccessorPayoff reward source.1 root who +
          (tolerance * rate) * direction who
      rw [hactual]
      dsimp only [correction]
      ring
    have hcharge : quittingRootAbsorptionMass root = rate := habsorption
    have hdefect := (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward source.1 root).mp hnash
    have hedge : IsQuittingFloorFreeRobustEdge reward tolerance (M + 2) source
        (quittingSimplexOfRoot root) successor := by
      intro who
      simp only [quittingRobustChargedEdgeResidual, quittingRobustChargedEdgeRegret,
        quittingRobustChargedEdgeAbsorption, quittingRootOfSimplex_simplexOfRoot]
      change |target rate who - quittingRootSuccessorPayoff reward source.1 root who| ≤
          tolerance * quittingRootAbsorptionMass root ∧
        quittingRootCoordinateNashDefect reward source.1 root who ≤
          tolerance * quittingRootAbsorptionMass root
      rw [hdefect who, hcharge]
      constructor
      · rw [htargetEq]
        change |(quittingRootSuccessorPayoff reward source.1 root who +
            tolerance * rate * direction who) -
          quittingRootSuccessorPayoff reward source.1 root who| ≤ tolerance * rate
        rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (mul_nonneg htolerance hrate.le)]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (hdirection who) (mul_nonneg htolerance hrate.le)
      · exact mul_nonneg htolerance hrate.le
    let edge : QuittingRobustChargedEdge reward tolerance (M + 2) :=
      ⟨((source, quittingSimplexOfRoot root), successor), hedge⟩
    have hdrift := hpotential edge
    change potential (target rate) + quittingRootAbsorptionMass
      (quittingRootOfSimplex (quittingSimplexOfRoot root)) ≤ potential source.1 at hdrift
    rw [quittingRootOfSimplex_simplexOfRoot, hcharge] at hdrift
    have hsourceEq : source.1 = point + (rate / (1 - rate)) • correction := by
      ext who
      rfl
    have htargetAffine : target rate = point + rate •
        (correction + (quittingSoloReward reward owner + tolerance • direction) - point) := by
      unfold target
      rw [show correction + quittingSoloReward reward owner - point + tolerance • direction =
        correction + (quittingSoloReward reward owner + tolerance • direction) - point by abel]
    rw [hsourceEq, htargetAffine] at hdrift
    apply (le_div_iff₀ hrate).mpr
    linarith
  have hdrift := ge_of_tendsto hlimit hquotient
  rw [map_sub, map_add, map_smul] at hdrift
  change 1 ≤ derivative point -
    (derivative (quittingSoloReward reward owner) + tolerance * derivative direction) at hdrift
  rw [map_sub]
  linarith

/-- The sign direction is produced from the actual derivative. This also
includes tolerance zero, where the absolute-sum term vanishes. -/
theorem quittingRobustPotential_singletonFace_l1_drift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htolerance : 0 ≤ tolerance) (potential : Payoff ι → ℝ)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (M + 2)).IsPotential
        (fun state => potential state.1))
    (point : Payoff ι) (owner : ι)
    (hpoint : ∀ who,
      quittingSoloReward reward who who ≤ point who ∧ point who ≤ M + 1)
    (howner : point owner = quittingSoloReward reward owner owner)
    (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point) :
    1 + tolerance * ∑ who, |derivative (Pi.single who 1)| ≤
      derivative (point - quittingSoloReward reward owner) := by
  obtain ⟨direction, hdirection, hsign⟩ :=
    Math.LinearAlgebra.exists_unitCube_direction_apply_eq_sum_abs_single derivative.toLinearMap
  have hdrift := quittingRobustPotential_singletonFace_directional_drift
    reward hreward htolerance potential hpotential point owner hpoint howner
    derivative hdiff direction hdirection
  change derivative direction = ∑ who, |derivative (Pi.single who 1)| at hsign
  rwa [hsign] at hdrift

/-- The original positive tolerance range gives the packet's explicit
absolute-gradient and drift lower bounds at every singleton lower face. -/
theorem quittingRobustPotential_singletonFace_quantitative_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htolerance0 : 0 < tolerance) (htolerance1 : tolerance ≤ 1 / 4)
    (potential : Payoff ι → ℝ)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (M + 2)).IsPotential
        (fun state => potential state.1))
    (point : Payoff ι) (owner : ι)
    (hpoint : ∀ who,
      quittingSoloReward reward who who ≤ point who ∧ point who ≤ M + 1)
    (howner : point owner = quittingSoloReward reward owner owner)
    (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point) :
    (1 + tolerance * ∑ who, |derivative (Pi.single who 1)| ≤
      derivative (point - quittingSoloReward reward owner)) ∧
    (1 / (2 * M + 1 - tolerance) ≤ ∑ who, |derivative (Pi.single who 1)|) ∧
    (2 * M + 1) / (2 * M + 1 - tolerance) ≤
      derivative (point - quittingSoloReward reward owner) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal owner) owner)
  have hdenom : 0 < 2 * M + 1 - tolerance := by linarith
  have hdrift := quittingRobustPotential_singletonFace_l1_drift
    reward hreward htolerance0.le potential hpotential point owner hpoint howner derivative hdiff
  have hcoordinate : ∀ who,
      |(point - quittingSoloReward reward owner) who| ≤ 2 * M + 1 := by
    intro who
    have hfloor := neg_le_of_abs_le (hreward (quittingSingletonTerminal who) who)
    have hsolo := abs_le.mp (hreward (quittingSingletonTerminal owner) who)
    change -M ≤ quittingSoloReward reward who who at hfloor
    change -M ≤ quittingSoloReward reward owner who ∧
      quittingSoloReward reward owner who ≤ M at hsolo
    change |point who - quittingSoloReward reward owner who| ≤ 2 * M + 1
    apply abs_le.mpr
    constructor <;> linarith [(hpoint who).1, (hpoint who).2, hsolo.1, hsolo.2]
  have hupper := Math.LinearAlgebra.abs_apply_le_mul_sum_abs_single
    derivative.toLinearMap (point - quittingSoloReward reward owner) (2 * M + 1) hcoordinate
  have hlinear : derivative (point - quittingSoloReward reward owner) ≤
      (2 * M + 1) * ∑ who, |derivative (Pi.single who 1)| :=
    (le_abs_self _).trans hupper
  have hnorm : 1 / (2 * M + 1 - tolerance) ≤
      ∑ who, |derivative (Pi.single who 1)| := by
    apply (div_le_iff₀ hdenom).mpr
    nlinarith [hdrift, hlinear]
  refine ⟨hdrift, hnorm, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hnorm htolerance0.le
  have hconstant : 1 + tolerance * (1 / (2 * M + 1 - tolerance)) =
      (2 * M + 1) / (2 * M + 1 - tolerance) := by
    field_simp [ne_of_gt hdenom]; ring
  rw [← hconstant]
  linarith

/-- The displayed coefficients are those of the actual Frechet derivative,
with only the packet's local differentiability assumption at the queried point. -/
theorem quittingRobustPotential_singletonFace_fderiv_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htolerance0 : 0 < tolerance) (htolerance1 : tolerance ≤ 1 / 4)
    (potential : Payoff ι → ℝ)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (M + 2)).IsPotential
        (fun state => potential state.1))
    (point : Payoff ι) (owner : ι)
    (hpoint : ∀ who,
      quittingSoloReward reward who who ≤ point who ∧ point who ≤ M + 1)
    (howner : point owner = quittingSoloReward reward owner owner)
    (hdiff : DifferentiableAt ℝ potential point) :
    (1 + tolerance * ∑ who, |(fderiv ℝ potential point) (Pi.single who 1)| ≤
      (fderiv ℝ potential point) (point - quittingSoloReward reward owner)) ∧
    (1 / (2 * M + 1 - tolerance) ≤
      ∑ who, |(fderiv ℝ potential point) (Pi.single who 1)|) ∧
    (2 * M + 1) / (2 * M + 1 - tolerance) ≤
      (fderiv ℝ potential point) (point - quittingSoloReward reward owner) :=
  quittingRobustPotential_singletonFace_quantitative_bounds
    reward hreward htolerance0 htolerance1 potential hpotential point owner hpoint howner
    (fderiv ℝ potential point) hdiff.hasFDerivAt

end GameTheory
