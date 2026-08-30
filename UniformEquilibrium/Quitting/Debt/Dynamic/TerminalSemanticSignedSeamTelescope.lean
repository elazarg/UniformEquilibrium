/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction

/-!
# Signed terminal-debt algebra for a supplied semantic seam chain

This module treats a finite chain of supplied semantic prefix equations. The
expected child used by one prefix step may differ from the next decoded
candidate in both its prescribed-payoff and unrestricted-cap coordinates.

This is a conditional semantic compiler. It does not assert that any point is
executable, attach the chain to behavioral play or a source chronology, make a
renewable child, construct a terminal equilibrium, or prove a uniform-equilibrium
payoff. A payoff-only seam is insufficient: both semantic coordinates occur in
the debt-error bounds.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite semantic prefix chain with a possibly mismatched expected child
at every seam. Values beyond `length` are intentionally irrelevant. -/
structure QuittingTerminalSemanticSeamChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  length : ℕ
  point : ℕ → QuittingTerminalSemanticPair ι
  expectedChild : ℕ → QuittingTerminalSemanticPair ι
  root : ℕ → ι → PMF Bool
  prefix_eq : ∀ stage < length,
    point stage =
      quittingTerminalSemanticPrefix reward (root stage) (expectedChild stage)

namespace QuittingTerminalSemanticSeamChain

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (chain : QuittingTerminalSemanticSeamChain reward)

/-- Difference between the expected and decoded prescribed payoff at one
seam. -/
def prescribedPayoffSeamError (stage : ℕ) (who : ι) : ℝ :=
  (chain.expectedChild stage).1 who - (chain.point (stage + 1)).1 who

/-- Difference between the expected and decoded unrestricted cap at one
seam. -/
def unrestrictedCapSeamError (stage : ℕ) (who : ι) : ℝ :=
  (chain.expectedChild stage).2 who - (chain.point (stage + 1)).2 who

/-- Signed total-debt mismatch at one seam. -/
def signedDebtSeamError (stage : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum (chain.expectedChild stage) -
    quittingTerminalSemanticDebtSum (chain.point (stage + 1))

/-- The one-row total Nash charge, evaluated against the expected child's
unrestricted cap. -/
def stageCharge (stage : ℕ) : ℝ :=
  quittingRootTotalNashDefect reward (chain.expectedChild stage).2
    (chain.root stage)

/-- Survival from stage zero through `stage` supplied roots. -/
def survivalWeight (stage : ℕ) : ℝ :=
  quittingJointSurvivalWeight chain.root 0 stage

/-- Survival-weighted Nash charge on the finite chain. -/
def totalCharge : ℝ :=
  ∑ stage ∈ Finset.range chain.length,
    chain.survivalWeight stage * chain.stageCharge stage

/-- Survival-weighted signed seam error. -/
def weightedSignedSeamError : ℝ :=
  ∑ stage ∈ Finset.range chain.length,
    chain.survivalWeight (stage + 1) * chain.signedDebtSeamError stage

/-- Survival-weighted absolute total-debt seam error. -/
def weightedAbsoluteDebtSeamError : ℝ :=
  ∑ stage ∈ Finset.range chain.length,
    chain.survivalWeight (stage + 1) * |chain.signedDebtSeamError stage|

/-- The signed debt mismatch is exactly cap error minus prescribed-payoff
error, summed over players. -/
theorem signedDebtSeamError_eq_sum_coordinateErrors (stage : ℕ) :
    chain.signedDebtSeamError stage =
      ∑ who, (chain.unrestrictedCapSeamError stage who -
        chain.prescribedPayoffSeamError stage who) := by
  unfold signedDebtSeamError unrestrictedCapSeamError
    prescribedPayoffSeamError quittingTerminalSemanticDebtSum
    quittingTerminalSemanticDebt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro who _
  ring

/-- Both semantic coordinates are needed: the absolute debt seam is bounded
by the sum of prescribed-payoff and unrestricted-cap coordinate errors. -/
theorem abs_signedDebtSeamError_le_sum_coordinateErrors (stage : ℕ) :
    |chain.signedDebtSeamError stage| ≤
      ∑ who, (|chain.prescribedPayoffSeamError stage who| +
        |chain.unrestrictedCapSeamError stage who|) := by
  rw [chain.signedDebtSeamError_eq_sum_coordinateErrors stage]
  calc
    |∑ who, (chain.unrestrictedCapSeamError stage who -
        chain.prescribedPayoffSeamError stage who)| ≤
        ∑ who, |chain.unrestrictedCapSeamError stage who -
          chain.prescribedPayoffSeamError stage who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ who, (|chain.prescribedPayoffSeamError stage who| +
          |chain.unrestrictedCapSeamError stage who|) := by
      apply Finset.sum_le_sum
      intro who _
      simpa [sub_eq_add_neg, add_comm] using abs_add_le
        (chain.unrestrictedCapSeamError stage who)
        (-chain.prescribedPayoffSeamError stage who)

/-- One semantic prefix step, with its signed expected-child/decoded-child
debt mismatch exposed literally. -/
theorem debtSum_step_eq (stage : ℕ) (hstage : stage < chain.length) :
    quittingTerminalSemanticDebtSum (chain.point stage) =
      chain.stageCharge stage +
        quittingStationaryContinueMass (chain.root stage) *
          quittingTerminalSemanticDebtSum (chain.point (stage + 1)) +
        quittingStationaryContinueMass (chain.root stage) *
          chain.signedDebtSeamError stage := by
  have hprefix :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
      reward (chain.expectedChild stage) (chain.root stage)
  rw [← chain.prefix_eq stage hstage] at hprefix
  unfold stageCharge signedDebtSeamError
  linarith

/-- Partial weighted telescope through any supplied initial segment. -/
theorem debtSum_eq_weighted_telescope (fuel : ℕ)
    (hfuel : fuel ≤ chain.length) :
    quittingTerminalSemanticDebtSum (chain.point 0) =
      (∑ stage ∈ Finset.range fuel,
        chain.survivalWeight stage * chain.stageCharge stage) +
      chain.survivalWeight fuel *
        quittingTerminalSemanticDebtSum (chain.point fuel) +
      (∑ stage ∈ Finset.range fuel,
        chain.survivalWeight (stage + 1) * chain.signedDebtSeamError stage) := by
  induction fuel with
  | zero =>
      simp [survivalWeight, quittingJointSurvivalWeight,
        quittingFiniteContinueWeight]
  | succ fuel ih =>
      have hfuelLe : fuel ≤ chain.length :=
        Nat.le_trans (Nat.le_succ fuel) hfuel
      have hfuelLt : fuel < chain.length := Nat.lt_of_succ_le hfuel
      have hstep := chain.debtSum_step_eq fuel hfuelLt
      unfold survivalWeight at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        quittingJointSurvivalWeight_succ, Nat.zero_add, ih hfuelLe,
        hstep]
      ring

/-- Full packet-literal signed-error telescope. -/
theorem debtSum_eq_totalCharge_add_endpoint_add_weightedSignedSeamError :
    quittingTerminalSemanticDebtSum (chain.point 0) =
      chain.totalCharge +
        chain.survivalWeight chain.length *
          quittingTerminalSemanticDebtSum (chain.point chain.length) +
        chain.weightedSignedSeamError := by
  simpa [totalCharge, weightedSignedSeamError] using
    chain.debtSum_eq_weighted_telescope chain.length le_rfl

/-- The signed weighted seam is controlled by the weighted absolute debt
seam. -/
theorem abs_weightedSignedSeamError_le :
    |chain.weightedSignedSeamError| ≤ chain.weightedAbsoluteDebtSeamError := by
  unfold weightedSignedSeamError weightedAbsoluteDebtSeamError
  calc
    |∑ stage ∈ Finset.range chain.length,
        chain.survivalWeight (stage + 1) * chain.signedDebtSeamError stage| ≤
        ∑ stage ∈ Finset.range chain.length,
          |chain.survivalWeight (stage + 1) *
            chain.signedDebtSeamError stage| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ stage ∈ Finset.range chain.length,
          chain.survivalWeight (stage + 1) *
            |chain.signedDebtSeamError stage| := by
      apply Finset.sum_congr rfl
      intro stage _
      rw [abs_mul, abs_of_nonneg]
      exact quittingJointSurvivalWeight_nonneg chain.root 0 (stage + 1)

/-- Explicit paired coordinate bounds control the weighted absolute debt
seam. -/
theorem weightedAbsoluteDebtSeamError_le_of_coordinateBounds
    (prescribedBound capBound : ℕ → ι → ℝ)
    (hprescribed : ∀ stage < chain.length, ∀ who,
      |chain.prescribedPayoffSeamError stage who| ≤ prescribedBound stage who)
    (hcap : ∀ stage < chain.length, ∀ who,
      |chain.unrestrictedCapSeamError stage who| ≤ capBound stage who) :
    chain.weightedAbsoluteDebtSeamError ≤
      ∑ stage ∈ Finset.range chain.length,
        chain.survivalWeight (stage + 1) *
          ∑ who, (prescribedBound stage who + capBound stage who) := by
  unfold weightedAbsoluteDebtSeamError
  apply Finset.sum_le_sum
  intro stage hstage
  apply mul_le_mul_of_nonneg_left
  · exact (chain.abs_signedDebtSeamError_le_sum_coordinateErrors stage).trans
      (Finset.sum_le_sum fun who _ =>
        add_le_add (hprescribed stage (Finset.mem_range.mp hstage) who)
          (hcap stage (Finset.mem_range.mp hstage) who))
  · exact quittingJointSurvivalWeight_nonneg chain.root 0 (stage + 1)

/-- A common sup bound on each of the two semantic coordinates costs at most
`2 * card ι` times that bound at every seam. -/
theorem weightedAbsoluteDebtSeamError_le_of_commonCoordinateBound
    (seamBound : ℕ → ℝ)
    (hprescribed : ∀ stage < chain.length, ∀ who,
      |chain.prescribedPayoffSeamError stage who| ≤ seamBound stage)
    (hcap : ∀ stage < chain.length, ∀ who,
      |chain.unrestrictedCapSeamError stage who| ≤ seamBound stage) :
    chain.weightedAbsoluteDebtSeamError ≤
      ∑ stage ∈ Finset.range chain.length,
        chain.survivalWeight (stage + 1) *
          (2 * (Fintype.card ι : ℝ) * seamBound stage) := by
  have hbound := chain.weightedAbsoluteDebtSeamError_le_of_coordinateBounds
    (fun stage _who => seamBound stage) (fun stage _who => seamBound stage)
    hprescribed hcap
  calc
    chain.weightedAbsoluteDebtSeamError ≤
        ∑ stage ∈ Finset.range chain.length,
          chain.survivalWeight (stage + 1) *
            ∑ _who : ι, (seamBound stage + seamBound stage) := hbound
    _ = _ := by
      apply Finset.sum_congr rfl
      intro stage _
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- In Fin4 the common two-coordinate seam cost is the packet's literal
factor `8`. -/
theorem finFour_weightedAbsoluteDebtSeamError_le_of_commonCoordinateBound
    {reward4 : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (chain : QuittingTerminalSemanticSeamChain reward4)
    (seamBound : ℕ → ℝ)
    (hprescribed : ∀ stage < chain.length, ∀ who,
      |chain.prescribedPayoffSeamError stage who| ≤ seamBound stage)
    (hcap : ∀ stage < chain.length, ∀ who,
      |chain.unrestrictedCapSeamError stage who| ≤ seamBound stage) :
    chain.weightedAbsoluteDebtSeamError ≤
      ∑ stage ∈ Finset.range chain.length,
        chain.survivalWeight (stage + 1) * (8 * seamBound stage) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat, mul_assoc,
    show (2 : ℝ) * 4 = 8 by norm_num] using
    chain.weightedAbsoluteDebtSeamError_le_of_commonCoordinateBound
      seamBound hprescribed hcap

/-- Seam-stable positive-minimum coercivity at an arbitrary survival ceiling.
Only endpoint debt lower bounds are assumed; no executable semantics is
inferred. -/
theorem totalCharge_add_absoluteSeam_add_theta_endpointExcess_ge
    (minimumDebt theta : ℝ) (hminimum0 : 0 ≤ minimumDebt)
    (hstart : minimumDebt ≤
      quittingTerminalSemanticDebtSum (chain.point 0))
    (hend : minimumDebt ≤
      quittingTerminalSemanticDebtSum (chain.point chain.length))
    (hsurvival : chain.survivalWeight chain.length ≤ theta) :
    chain.totalCharge + chain.weightedAbsoluteDebtSeamError +
        theta *
          (quittingTerminalSemanticDebtSum (chain.point chain.length) -
            minimumDebt) ≥
      (1 - theta) * minimumDebt := by
  have htelescope :=
    chain.debtSum_eq_totalCharge_add_endpoint_add_weightedSignedSeamError
  have habs := chain.abs_weightedSignedSeamError_le
  have hsignedLe : chain.weightedSignedSeamError ≤
      chain.weightedAbsoluteDebtSeamError :=
    le_trans (le_abs_self _) habs
  have hendExcess : 0 ≤
      quittingTerminalSemanticDebtSum (chain.point chain.length) - minimumDebt :=
    sub_nonneg.mpr hend
  have hscaled := mul_le_mul_of_nonneg_right hsurvival hendExcess
  have hsurvival0 :=
    quittingJointSurvivalWeight_nonneg chain.root 0 chain.length
  nlinarith

/-- Coordinatewise prescribed-payoff and unrestricted-cap seam bounds give
the packet's explicit seam-stable coercivity estimate. -/
theorem totalCharge_add_coordinateSeamBound_add_theta_endpointExcess_ge
    (minimumDebt theta : ℝ) (hminimum0 : 0 ≤ minimumDebt)
    (hstart : minimumDebt ≤
      quittingTerminalSemanticDebtSum (chain.point 0))
    (hend : minimumDebt ≤
      quittingTerminalSemanticDebtSum (chain.point chain.length))
    (hsurvival : chain.survivalWeight chain.length ≤ theta)
    (prescribedBound capBound : ℕ → ι → ℝ)
    (hprescribed : ∀ stage < chain.length, ∀ who,
      |chain.prescribedPayoffSeamError stage who| ≤ prescribedBound stage who)
    (hcap : ∀ stage < chain.length, ∀ who,
      |chain.unrestrictedCapSeamError stage who| ≤ capBound stage who) :
    chain.totalCharge +
        (∑ stage ∈ Finset.range chain.length,
          chain.survivalWeight (stage + 1) *
            ∑ who, (prescribedBound stage who + capBound stage who)) +
        theta *
          (quittingTerminalSemanticDebtSum (chain.point chain.length) -
            minimumDebt) ≥
      (1 - theta) * minimumDebt := by
  have habsolute :=
    chain.totalCharge_add_absoluteSeam_add_theta_endpointExcess_ge
      minimumDebt theta hminimum0 hstart hend hsurvival
  have hcoordinate :=
    chain.weightedAbsoluteDebtSeamError_le_of_coordinateBounds
      prescribedBound capBound hprescribed hcap
  linarith

end QuittingTerminalSemanticSeamChain

end GameTheory
