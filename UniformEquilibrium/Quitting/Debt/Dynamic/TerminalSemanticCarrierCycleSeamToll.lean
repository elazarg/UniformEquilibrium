/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction

/-!
# Semantic seam tolls for supplied finite carrier cycles

This module compiles a supplied finite family of terminal-semantic carrier
points and product roots. The successor is an arbitrary permutation of the
finite phase type, so deterministic reorderings are included literally.

The results are horizontal finite-family identities. They do not produce the
family, attach it to chronological play, renew it, or prove an equilibrium.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι Phase : Type} [Fintype ι] [DecidableEq ι]
  [Fintype Phase]

/-- Coordinatewise `L¹` distance on prescribed-payoff/unrestricted-cap
semantic pairs. -/
def quittingTerminalSemanticL1Distance
    (first second : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, (|first.1 who - second.1 who| +
    |first.2 who - second.2 who|)

omit [DecidableEq ι] [Fintype Phase] in
/-- The semantic-pair `L¹` distance costs at most `2 * card ι` times its
product sup norm. -/
theorem quittingTerminalSemanticL1Distance_le_two_card_mul_norm
    (first second : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticL1Distance first second ≤
      2 * Fintype.card ι * ‖first - second‖ := by
  let difference := first - second
  have hpayoff := Pi.sum_norm_apply_le_norm difference.1
  have hcap := Pi.sum_norm_apply_le_norm difference.2
  have hfirst : ‖difference.1‖ ≤ ‖difference‖ := norm_fst_le difference
  have hsecond : ‖difference.2‖ ≤ ‖difference‖ := norm_snd_le difference
  have hpayoff' :
      (∑ who, ‖difference.1 who‖) ≤ Fintype.card ι * ‖difference‖ := by
    calc
      _ ≤ Fintype.card ι • ‖difference.1‖ := hpayoff
      _ ≤ Fintype.card ι • ‖difference‖ :=
        nsmul_le_nsmul_right hfirst _
      _ = _ := by simp [nsmul_eq_mul]
  have hcap' :
      (∑ who, ‖difference.2 who‖) ≤ Fintype.card ι * ‖difference‖ := by
    calc
      _ ≤ Fintype.card ι • ‖difference.2‖ := hcap
      _ ≤ Fintype.card ι • ‖difference‖ :=
        nsmul_le_nsmul_right hsecond _
      _ = _ := by simp [nsmul_eq_mul]
  unfold quittingTerminalSemanticL1Distance
  change (∑ who, (‖difference.1 who‖ + ‖difference.2 who‖)) ≤ _
  rw [Finset.sum_add_distrib]
  linarith

/-- Supplied carrier points, roots at their literal cap coordinates, and a
permutation describing the next displayed phase. -/
structure QuittingTerminalSemanticCarrierCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  point : Phase → QuittingTerminalSemanticPair ι
  point_mem : ∀ phase, point phase ∈ quittingTerminalSemanticCarrier reward
  root : Phase → ι → PMF Bool
  successor : Equiv.Perm Phase

namespace QuittingTerminalSemanticCarrierCycle

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (cycle : QuittingTerminalSemanticCarrierCycle (Phase := Phase) reward)

/-- The literal semantic pair obtained by applying the displayed root to its
own carrier source. -/
def prefixedPoint (phase : Phase) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefix reward (cycle.root phase) (cycle.point phase)

/-- Probability that every player continues at the displayed root. -/
def continueMass (phase : Phase) : ℝ :=
  quittingStationaryContinueMass (cycle.root phase)

/-- Probability that the displayed root absorbs immediately. -/
def absorptionMass (phase : Phase) : ℝ := 1 - cycle.continueMass phase

/-- Total ordinary one-row Nash defect against the source point's literal
unrestricted cap. -/
def nashDefect (phase : Phase) : ℝ :=
  quittingRootTotalNashDefect reward (cycle.point phase).2 (cycle.root phase)

/-- Signed total-debt seam from the literal prefixed source to the next
displayed carrier point. -/
def signedDebtRebase (phase : Phase) : ℝ :=
  quittingTerminalSemanticDebtSum (cycle.point (cycle.successor phase)) -
    quittingTerminalSemanticDebtSum (cycle.prefixedPoint phase)

/-- Full prescribed-payoff and unrestricted-cap coordinate error at one
displayed seam. -/
def semanticL1Rebase (phase : Phase) : ℝ :=
  quittingTerminalSemanticL1Distance
    (cycle.point (cycle.successor phase)) (cycle.prefixedPoint phase)

/-- Sup norm of the full prescribed-payoff/cap seam. On `Fin 4` this is the
maximum of the eight scalar coordinate errors. -/
def semanticSupRebase (phase : Phase) : ℝ :=
  ‖cycle.point (cycle.successor phase) - cycle.prefixedPoint phase‖

/-- The source debt consumed by absorption, less the one-row Nash defect. -/
def netAbsorptionCharge (phase : Phase) : ℝ :=
  cycle.absorptionMass phase *
      quittingTerminalSemanticDebtSum (cycle.point phase) -
    cycle.nashDefect phase

omit [Fintype Phase] in
theorem absorptionMass_nonneg (phase : Phase) :
    0 ≤ cycle.absorptionMass phase := by
  unfold absorptionMass continueMass
  linarith [quittingStationaryContinueMass_le_one (cycle.root phase)]

omit [Fintype Phase] in
/-- One displayed seam is exactly the next debt minus the survived source
debt and local Nash defect. -/
theorem signedDebtRebase_eq (phase : Phase) :
    cycle.signedDebtRebase phase =
      quittingTerminalSemanticDebtSum
          (cycle.point (cycle.successor phase)) -
        (cycle.continueMass phase *
            quittingTerminalSemanticDebtSum (cycle.point phase) +
          cycle.nashDefect phase) := by
  unfold signedDebtRebase prefixedPoint continueMass nashDefect
  rw [quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect]

/-- Exact cyclic debt ledger. The source debt terms close because the phase
successor is a permutation. -/
theorem sum_signedDebtRebase_eq_sum_netAbsorptionCharge :
    (∑ phase, cycle.signedDebtRebase phase) =
      ∑ phase, cycle.netAbsorptionCharge phase := by
  simp_rw [cycle.signedDebtRebase_eq]
  unfold netAbsorptionCharge absorptionMass
  have hreindex :
      (∑ phase, quittingTerminalSemanticDebtSum
          (cycle.point (cycle.successor phase))) =
        ∑ phase, quittingTerminalSemanticDebtSum (cycle.point phase) :=
    Equiv.sum_comp cycle.successor
      (fun phase => quittingTerminalSemanticDebtSum (cycle.point phase))
  rw [Finset.sum_sub_distrib, hreindex, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro phase _
  ring

omit [Fintype Phase] in
/-- Exact roots have zero local Nash charge. -/
theorem nashDefect_eq_zero_of_exactRoot
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase))
    (phase : Phase) :
    cycle.nashDefect phase = 0 := by
  exact (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
    reward (cycle.point phase).2 (cycle.root phase)).mp (exactRoot phase)

/-- Exact roots turn the cyclic ledger into the literal absorbed source-debt
sum. -/
theorem sum_signedDebtRebase_eq_sum_absorptionMass_mul_debtSum_of_exactRoot
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase)) :
    (∑ phase, cycle.signedDebtRebase phase) =
      ∑ phase, cycle.absorptionMass phase *
        quittingTerminalSemanticDebtSum (cycle.point phase) := by
  rw [cycle.sum_signedDebtRebase_eq_sum_netAbsorptionCharge]
  apply Finset.sum_congr rfl
  intro phase _
  simp [netAbsorptionCharge, cycle.nashDefect_eq_zero_of_exactRoot exactRoot]

/-- A positive common carrier-debt floor charges every unit of exact-root
absorption around the finite cycle. -/
theorem debtFloor_mul_sum_absorptionMass_le_sum_signedDebtRebase_of_exactRoot
    (debtFloor : ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase)) :
    debtFloor * (∑ phase, cycle.absorptionMass phase) ≤
      ∑ phase, cycle.signedDebtRebase phase := by
  rw [cycle.sum_signedDebtRebase_eq_sum_absorptionMass_mul_debtSum_of_exactRoot
    exactRoot, Finset.mul_sum]
  exact Finset.sum_le_sum fun phase _ =>
    by simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (floor_le phase)
        (cycle.absorptionMass_nonneg phase)

omit [Fintype Phase] in
/-- The absolute total-debt seam is controlled by the full two-coordinate
semantic error. -/
theorem abs_signedDebtRebase_le_semanticL1Rebase (phase : Phase) :
    |cycle.signedDebtRebase phase| ≤ cycle.semanticL1Rebase phase := by
  exact abs_quittingTerminalSemanticDebtSum_sub_le
    (cycle.point (cycle.successor phase)) (cycle.prefixedPoint phase)

omit [Fintype Phase] in
/-- The full semantic `L¹` seam is bounded by `2 * card ι` times the
semantic-pair sup norm. -/
theorem semanticL1Rebase_le_two_card_mul_semanticSupRebase (phase : Phase) :
    cycle.semanticL1Rebase phase ≤
      2 * Fintype.card ι * cycle.semanticSupRebase phase := by
  exact quittingTerminalSemanticL1Distance_le_two_card_mul_norm
    (cycle.point (cycle.successor phase)) (cycle.prefixedPoint phase)

/-- The full payoff/cap seam pays the positive-debt exact-root absorption
toll. -/
theorem debtFloor_mul_sum_absorptionMass_le_sum_semanticL1Rebase_of_exactRoot
    (debtFloor : ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase)) :
    debtFloor * (∑ phase, cycle.absorptionMass phase) ≤
      ∑ phase, cycle.semanticL1Rebase phase := by
  calc
    debtFloor * (∑ phase, cycle.absorptionMass phase) ≤
        ∑ phase, cycle.signedDebtRebase phase :=
      cycle.debtFloor_mul_sum_absorptionMass_le_sum_signedDebtRebase_of_exactRoot
        debtFloor floor_le exactRoot
    _ ≤ ∑ phase, |cycle.signedDebtRebase phase| :=
      Finset.sum_le_sum fun phase _ => le_abs_self _
    _ ≤ ∑ phase, cycle.semanticL1Rebase phase :=
      Finset.sum_le_sum fun phase _ =>
        cycle.abs_signedDebtRebase_le_semanticL1Rebase phase

/-- With a positive carrier-debt floor and one genuinely absorbing phase,
the full semantic seam cannot cancel. -/
theorem sum_semanticL1Rebase_pos_of_exists_absorbing_exactRoot
    (debtFloor : ℝ) (debtFloor_pos : 0 < debtFloor)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase))
    (absorbing : ∃ phase, 0 < cycle.absorptionMass phase) :
    0 < ∑ phase, cycle.semanticL1Rebase phase := by
  have hsum : 0 < ∑ phase, cycle.absorptionMass phase := by
    apply Finset.sum_pos'
    · intro phase _
      exact cycle.absorptionMass_nonneg phase
    · obtain ⟨phase, hphase⟩ := absorbing
      exact ⟨phase, Finset.mem_univ phase, hphase⟩
  have htoll :=
    cycle.debtFloor_mul_sum_absorptionMass_le_sum_semanticL1Rebase_of_exactRoot
      debtFloor floor_le exactRoot
  nlinarith

/-- Approximate roots leave at most `card ι * error` uncharged at each
phase. -/
theorem debtFloor_mul_sum_absorptionMass_sub_error_le_sum_semanticL1Rebase
    (debtFloor : ℝ) (error : Phase → ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (approximateRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 (error phase)
        (cycle.root phase)) :
    debtFloor * (∑ phase, cycle.absorptionMass phase) -
        Fintype.card ι * (∑ phase, error phase) ≤
      ∑ phase, cycle.semanticL1Rebase phase := by
  have hnet :
      debtFloor * (∑ phase, cycle.absorptionMass phase) -
          Fintype.card ι * (∑ phase, error phase) ≤
        ∑ phase, cycle.netAbsorptionCharge phase := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun phase _ => by
      unfold netAbsorptionCharge
      have hfloor := mul_le_mul_of_nonneg_left (floor_le phase)
        (cycle.absorptionMass_nonneg phase)
      have hdefect :=
        quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
          reward (cycle.point phase).2 (cycle.root phase) (error phase)
          (approximateRoot phase)
      change cycle.nashDefect phase ≤ Fintype.card ι * error phase at hdefect
      linarith
  calc
    _ ≤ ∑ phase, cycle.netAbsorptionCharge phase := hnet
    _ = ∑ phase, cycle.signedDebtRebase phase :=
      cycle.sum_signedDebtRebase_eq_sum_netAbsorptionCharge.symm
    _ ≤ ∑ phase, |cycle.signedDebtRebase phase| :=
      Finset.sum_le_sum fun phase _ => le_abs_self _
    _ ≤ ∑ phase, cycle.semanticL1Rebase phase :=
      Finset.sum_le_sum fun phase _ =>
        cycle.abs_signedDebtRebase_le_semanticL1Rebase phase

/-- In a four-player game, the maximum eight-coordinate semantic seam pays
one eighth of the exact-root absorption toll. -/
theorem finFour_debtFloor_div_eight_mul_sum_absorptionMass_le_sum_semanticSupRebase
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (cycle : QuittingTerminalSemanticCarrierCycle
      (Phase := Phase) reward)
    (debtFloor : ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase)) :
    debtFloor / 8 * (∑ phase, cycle.absorptionMass phase) ≤
      ∑ phase, cycle.semanticSupRebase phase := by
  have htoll :=
    cycle.debtFloor_mul_sum_absorptionMass_le_sum_semanticL1Rebase_of_exactRoot
      debtFloor floor_le exactRoot
  have hl1 :
      (∑ phase, cycle.semanticL1Rebase phase) ≤
        8 * (∑ phase, cycle.semanticSupRebase phase) := by
    calc
      _ ≤ ∑ phase, 2 * Fintype.card (Fin 4) * cycle.semanticSupRebase phase :=
        Finset.sum_le_sum fun phase _ =>
          cycle.semanticL1Rebase_le_two_card_mul_semanticSupRebase phase
      _ = _ := by norm_num [Finset.mul_sum]
  linarith

/-- A stationary rematching of the supplied phase sources. Equal row and
column marginals say that roots retain their source distribution while targets
may be coupled arbitrarily with it. -/
structure StationaryCoupling where
  weight : Phase → ℝ
  coupling : Phase → Phase → ℝ
  weight_nonneg : ∀ phase, 0 ≤ weight phase
  coupling_nonneg : ∀ source target, 0 ≤ coupling source target
  weight_sum_eq_one : ∑ phase, weight phase = 1
  row_marginal : ∀ source,
    ∑ target, coupling source target = weight source
  column_marginal : ∀ target,
    ∑ source, coupling source target = weight target

namespace StationaryCoupling

variable (matching : StationaryCoupling (Phase := Phase))

/-- Signed debt seam when a source root is rematched to a possible target
phase. -/
def signedDebtRebase (source target : Phase) : ℝ :=
  quittingTerminalSemanticDebtSum (cycle.point target) -
    quittingTerminalSemanticDebtSum (cycle.prefixedPoint source)

/-- Full payoff/cap coordinate error for a rematched source-target pair. -/
def semanticL1Rebase (source target : Phase) : ℝ :=
  quittingTerminalSemanticL1Distance
    (cycle.point target) (cycle.prefixedPoint source)

/-- Sup norm of the full rematched semantic-pair error. -/
def semanticSupRebase (source target : Phase) : ℝ :=
  ‖cycle.point target - cycle.prefixedPoint source‖

/-- Equal column marginals preserve the weighted target debt. -/
theorem sum_coupling_mul_targetDebt :
    (∑ source, ∑ target,
      matching.coupling source target *
        quittingTerminalSemanticDebtSum (cycle.point target)) =
      ∑ target, matching.weight target *
        quittingTerminalSemanticDebtSum (cycle.point target) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.sum_mul, matching.column_marginal]

/-- Equal row marginals preserve the weighted literal prefixed-source debt. -/
theorem sum_coupling_mul_prefixedDebt :
    (∑ source, ∑ target,
      matching.coupling source target *
        quittingTerminalSemanticDebtSum (cycle.prefixedPoint source)) =
      ∑ source, matching.weight source *
        quittingTerminalSemanticDebtSum (cycle.prefixedPoint source) := by
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.sum_mul, matching.row_marginal]

/-- Exact equal-marginal rematching identity. -/
theorem sum_coupledSignedDebtRebase_eq_sum_weight_mul_netAbsorptionCharge :
    (∑ source, ∑ target,
      matching.coupling source target *
        signedDebtRebase cycle source target) =
      ∑ source, matching.weight source *
        cycle.netAbsorptionCharge source := by
  unfold signedDebtRebase
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [matching.sum_coupling_mul_targetDebt cycle,
    matching.sum_coupling_mul_prefixedDebt cycle,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro source _
  unfold netAbsorptionCharge absorptionMass prefixedPoint continueMass nashDefect
  rw [quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect]
  ring

omit [Fintype Phase] in
/-- The absolute rematched debt seam is controlled by its full semantic
coordinate error. -/
theorem abs_signedDebtRebase_le_semanticL1Rebase (source target : Phase) :
    |signedDebtRebase cycle source target| ≤
      semanticL1Rebase cycle source target := by
  exact abs_quittingTerminalSemanticDebtSum_sub_le
    (cycle.point target) (cycle.prefixedPoint source)

/-- Equal-marginal rematching cannot remove the positive-debt exact-root
semantic seam toll. -/
theorem debtFloor_mul_weightedAbsorptionMass_le_weightedSemanticL1Rebase_of_exactRoot
    (debtFloor : ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase)) :
    debtFloor * (∑ phase,
        matching.weight phase * cycle.absorptionMass phase) ≤
      ∑ source, ∑ target,
        matching.coupling source target *
          semanticL1Rebase cycle source target := by
  have hcharge :
      debtFloor * (∑ phase,
          matching.weight phase * cycle.absorptionMass phase) ≤
        ∑ phase, matching.weight phase *
          cycle.netAbsorptionCharge phase := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun phase _ => by
      rw [netAbsorptionCharge,
        cycle.nashDefect_eq_zero_of_exactRoot exactRoot phase, sub_zero]
      have hinside := mul_le_mul_of_nonneg_left (floor_le phase)
        (cycle.absorptionMass_nonneg phase)
      calc
        debtFloor * (matching.weight phase * cycle.absorptionMass phase) =
            matching.weight phase *
              (cycle.absorptionMass phase * debtFloor) := by ring
        _ ≤ matching.weight phase *
              (cycle.absorptionMass phase *
                quittingTerminalSemanticDebtSum (cycle.point phase)) :=
          mul_le_mul_of_nonneg_left hinside (matching.weight_nonneg phase)
  calc
    _ ≤ ∑ phase, matching.weight phase *
          cycle.netAbsorptionCharge phase := hcharge
    _ = ∑ source, ∑ target,
          matching.coupling source target *
            signedDebtRebase cycle source target :=
      (matching.sum_coupledSignedDebtRebase_eq_sum_weight_mul_netAbsorptionCharge
        cycle).symm
    _ ≤ ∑ source, ∑ target,
          matching.coupling source target *
            semanticL1Rebase cycle source target := by
      exact Finset.sum_le_sum fun source _ =>
        Finset.sum_le_sum fun target _ =>
          mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans
              (abs_signedDebtRebase_le_semanticL1Rebase
                cycle source target))
            (matching.coupling_nonneg source target)

/-- Approximate roots subtract at most the stationary average of
`card ι * error` from the rematched seam toll. -/
theorem debtFloor_mul_weightedAbsorptionMass_sub_error_le_weightedSemanticL1Rebase
    (debtFloor : ℝ) (error : Phase → ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (approximateRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 (error phase)
        (cycle.root phase)) :
    debtFloor * (∑ phase,
        matching.weight phase * cycle.absorptionMass phase) -
        Fintype.card ι *
          (∑ phase, matching.weight phase * error phase) ≤
      ∑ source, ∑ target,
        matching.coupling source target *
          semanticL1Rebase cycle source target := by
  have hcharge :
      debtFloor * (∑ phase,
          matching.weight phase * cycle.absorptionMass phase) -
          Fintype.card ι *
            (∑ phase, matching.weight phase * error phase) ≤
        ∑ phase, matching.weight phase *
          cycle.netAbsorptionCharge phase := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun phase _ => by
      have hfloor := mul_le_mul_of_nonneg_left (floor_le phase)
        (cycle.absorptionMass_nonneg phase)
      have hdefect :=
        quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
          reward (cycle.point phase).2 (cycle.root phase) (error phase)
          (approximateRoot phase)
      change cycle.nashDefect phase ≤ Fintype.card ι * error phase at hdefect
      unfold netAbsorptionCharge
      have hinside :
          debtFloor * cycle.absorptionMass phase -
              Fintype.card ι * error phase ≤
            cycle.absorptionMass phase *
                quittingTerminalSemanticDebtSum (cycle.point phase) -
              cycle.nashDefect phase := by
        linarith
      calc
        debtFloor * (matching.weight phase * cycle.absorptionMass phase) -
            Fintype.card ι * (matching.weight phase * error phase) =
          matching.weight phase *
            (debtFloor * cycle.absorptionMass phase -
              Fintype.card ι * error phase) := by ring
        _ ≤ matching.weight phase *
            (cycle.absorptionMass phase *
                quittingTerminalSemanticDebtSum (cycle.point phase) -
              cycle.nashDefect phase) :=
          mul_le_mul_of_nonneg_left hinside (matching.weight_nonneg phase)
  calc
    _ ≤ ∑ phase, matching.weight phase *
          cycle.netAbsorptionCharge phase := hcharge
    _ = ∑ source, ∑ target,
          matching.coupling source target *
            signedDebtRebase cycle source target :=
      (matching.sum_coupledSignedDebtRebase_eq_sum_weight_mul_netAbsorptionCharge
        cycle).symm
    _ ≤ ∑ source, ∑ target,
          matching.coupling source target *
            semanticL1Rebase cycle source target := by
      exact Finset.sum_le_sum fun source _ =>
        Finset.sum_le_sum fun target _ =>
          mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans
              (abs_signedDebtRebase_le_semanticL1Rebase
                cycle source target))
            (matching.coupling_nonneg source target)

/-- The four-player equal-marginal seam pays one eighth of the weighted
exact-root absorption toll in semantic-pair sup norm. -/
theorem finFour_debtFloor_div_eight_mul_weightedAbsorptionMass_le_weightedSemanticSupRebase
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (cycle : QuittingTerminalSemanticCarrierCycle
      (Phase := Phase) reward)
    (matching : StationaryCoupling (Phase := Phase))
    (debtFloor : ℝ)
    (floor_le : ∀ phase,
      debtFloor ≤ quittingTerminalSemanticDebtSum (cycle.point phase))
    (exactRoot : ∀ phase,
      IsεQuittingRootNash reward (cycle.point phase).2 0 (cycle.root phase)) :
    debtFloor / 8 * (∑ phase,
        matching.weight phase * cycle.absorptionMass phase) ≤
      ∑ source, ∑ target,
        matching.coupling source target *
          semanticSupRebase cycle source target := by
  have htoll :=
    matching.debtFloor_mul_weightedAbsorptionMass_le_weightedSemanticL1Rebase_of_exactRoot
      cycle debtFloor floor_le exactRoot
  have hl1 :
      (∑ source, ∑ target,
          matching.coupling source target *
            semanticL1Rebase cycle source target) ≤
        8 * (∑ source, ∑ target,
          matching.coupling source target *
            semanticSupRebase cycle source target) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun source _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun target _ => by
        have hdistance :=
          quittingTerminalSemanticL1Distance_le_two_card_mul_norm
            (cycle.point target) (cycle.prefixedPoint source)
        change semanticL1Rebase cycle source target ≤
          2 * Fintype.card (Fin 4) *
            semanticSupRebase cycle source target at hdistance
        have hscaled := mul_le_mul_of_nonneg_left hdistance
          (matching.coupling_nonneg source target)
        norm_num at hscaled
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  linarith

end StationaryCoupling

end QuittingTerminalSemanticCarrierCycle

/-- A supplied finite open chain of carrier points and literal product-root
prefixes. Only indices at most `length` are semantically constrained. -/
structure QuittingTerminalSemanticCarrierOpenChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  length : ℕ
  point : ℕ → QuittingTerminalSemanticPair ι
  point_mem : ∀ time ≤ length,
    point time ∈ quittingTerminalSemanticCarrier reward
  root : ℕ → ι → PMF Bool

namespace QuittingTerminalSemanticCarrierOpenChain

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  variable (chain : QuittingTerminalSemanticCarrierOpenChain reward)

/-- Literal prefixed point at one nonterminal chain index. -/
def prefixedPoint (time : ℕ) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefix reward (chain.root time) (chain.point time)

/-- Immediate absorption probability at one chain index. -/
def absorptionMass (time : ℕ) : ℝ :=
  1 - quittingStationaryContinueMass (chain.root time)

/-- One-row ordinary Nash defect against the source point's actual cap. -/
def nashDefect (time : ℕ) : ℝ :=
  quittingRootTotalNashDefect reward (chain.point time).2 (chain.root time)

/-- Signed debt seam from a literal prefix to the next displayed point. -/
def signedDebtRebase (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum (chain.point (time + 1)) -
    quittingTerminalSemanticDebtSum (chain.prefixedPoint time)

/-- The source debt consumed by absorption, less the one-row Nash defect. -/
def netAbsorptionCharge (time : ℕ) : ℝ :=
  chain.absorptionMass time *
      quittingTerminalSemanticDebtSum (chain.point time) -
    chain.nashDefect time

omit [Fintype Phase] in
theorem absorptionMass_nonneg (time : ℕ) :
    0 ≤ chain.absorptionMass time := by
  unfold absorptionMass
  linarith [quittingStationaryContinueMass_le_one (chain.root time)]

omit [Fintype Phase] in
/-- One open-chain seam splits into a debt increment and its absorbed-source
charge. -/
theorem signedDebtRebase_eq_increment_add_netAbsorptionCharge (time : ℕ) :
    chain.signedDebtRebase time =
      (quittingTerminalSemanticDebtSum (chain.point (time + 1)) -
        quittingTerminalSemanticDebtSum (chain.point time)) +
      chain.netAbsorptionCharge time := by
  unfold signedDebtRebase prefixedPoint netAbsorptionCharge absorptionMass
    nashDefect
  rw [quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect]
  ring

/-- Exact open-chain identity: unlike a cycle, the endpoint debt increment
does not cancel. -/
theorem sum_signedDebtRebase_eq_endpointDebt_sub_initialDebt_add_charge :
    (∑ time ∈ Finset.range chain.length, chain.signedDebtRebase time) =
      quittingTerminalSemanticDebtSum (chain.point chain.length) -
          quittingTerminalSemanticDebtSum (chain.point 0) +
        ∑ time ∈ Finset.range chain.length,
          chain.netAbsorptionCharge time := by
  calc
    _ = ∑ time ∈ Finset.range chain.length,
          ((quittingTerminalSemanticDebtSum (chain.point (time + 1)) -
              quittingTerminalSemanticDebtSum (chain.point time)) +
            chain.netAbsorptionCharge time) := by
      apply Finset.sum_congr rfl
      intro time _
      exact chain.signedDebtRebase_eq_increment_add_netAbsorptionCharge time
    _ = (∑ time ∈ Finset.range chain.length,
          (quittingTerminalSemanticDebtSum (chain.point (time + 1)) -
            quittingTerminalSemanticDebtSum (chain.point time))) +
        ∑ time ∈ Finset.range chain.length,
          chain.netAbsorptionCharge time := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      have htelescope :
          (∑ time ∈ Finset.range chain.length,
            (quittingTerminalSemanticDebtSum (chain.point (time + 1)) -
              quittingTerminalSemanticDebtSum (chain.point time))) =
            quittingTerminalSemanticDebtSum (chain.point chain.length) -
              quittingTerminalSemanticDebtSum (chain.point 0) :=
        Finset.sum_range_sub
          (fun time => quittingTerminalSemanticDebtSum (chain.point time))
          chain.length
      rw [htelescope]

omit [Fintype Phase] in
theorem nashDefect_eq_zero_of_exactRoot
    (exactRoot : ∀ time < chain.length,
      IsεQuittingRootNash reward (chain.point time).2 0 (chain.root time))
    (time : ℕ) (time_lt : time < chain.length) :
    chain.nashDefect time = 0 := by
  exact (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
    reward (chain.point time).2 (chain.root time)).mp
      (exactRoot time time_lt)

/-- An exact-root open chain can spend its initial debt excess once. Further
absorption requires a positive signed rebase seam. -/
theorem debtFloor_mul_sum_absorptionMass_sub_initialExcess_le_sum_signedDebtRebase
    (debtFloor initialExcess : ℝ)
    (floor_le : ∀ time ≤ chain.length,
      debtFloor ≤ quittingTerminalSemanticDebtSum (chain.point time))
    (initialDebt :
      quittingTerminalSemanticDebtSum (chain.point 0) =
        debtFloor + initialExcess)
    (exactRoot : ∀ time < chain.length,
      IsεQuittingRootNash reward (chain.point time).2 0 (chain.root time)) :
    debtFloor *
          (∑ time ∈ Finset.range chain.length,
            chain.absorptionMass time) -
        initialExcess ≤
      ∑ time ∈ Finset.range chain.length,
        chain.signedDebtRebase time := by
  rw [chain.sum_signedDebtRebase_eq_endpointDebt_sub_initialDebt_add_charge]
  have hend := floor_le chain.length le_rfl
  have hcharge :
      debtFloor *
          (∑ time ∈ Finset.range chain.length,
            chain.absorptionMass time) ≤
        ∑ time ∈ Finset.range chain.length,
          chain.netAbsorptionCharge time := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun time time_mem => by
      have time_lt := Finset.mem_range.mp time_mem
      rw [netAbsorptionCharge,
        chain.nashDefect_eq_zero_of_exactRoot exactRoot time time_lt, sub_zero]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (floor_le time time_lt.le)
          (chain.absorptionMass_nonneg time)
  linarith

end QuittingTerminalSemanticCarrierOpenChain

end GameTheory
