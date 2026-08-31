/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.OutcomeLawStageDecomposition
import UniformEquilibrium.Quitting.Root.ProductRootProbabilityBridge
import MathUE.PMFProduct.SingletonRatioPairConcentration

/-
Closed-law product base for zero-Never, zero-singleton behavioral limits.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-! ## The coalition box polynomial -/

section CoalitionBox

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def zeroSingletonProductBaseBoxAbsorption (rates : ι → ℝ) : ℝ :=
  1 - Math.PMFProduct.continueMass rates

/-- The exact-coalition mass of a product root read as a polynomial in the
quit-rate vector. -/
def zeroSingletonProductBaseBoxCoalition (w : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, w i) * ∏ i ∈ Sᶜ, (1 - w i)

/-- The coalition polynomial is continuous. -/
theorem zeroSingletonProductBase_continuous_boxCoalition (S : Finset ι) :
    Continuous fun w : ι → ℝ => zeroSingletonProductBaseBoxCoalition w S :=
  (continuous_finsetProd _ fun i _ => continuous_apply i).mul
    (continuous_finsetProd _ fun i _ => continuous_const.sub (continuous_apply i))

/-- **Bridge 3: the exact coalition mass.**  The mass of exactly `S` quitting
at a product root is the coalition polynomial at its quit rates. -/
theorem zeroSingletonProductBase_coalitionMass_eq_boxCoalition
    (root : ι → PMF Bool) (S : Finset ι) :
    quittingRootCoalitionMass root S =
      zeroSingletonProductBaseBoxCoalition (fun who => (root who true).toReal) S := rfl

/-- The coalition polynomial is nonnegative on the unit box. -/
theorem zeroSingletonProductBase_boxCoalition_nonneg {w : ι → ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h1 : ∀ k, w k ≤ 1) (S : Finset ι) : 0 ≤ zeroSingletonProductBaseBoxCoalition w S :=
  mul_nonneg (Finset.prod_nonneg fun i _ => h0 i)
    (Finset.prod_nonneg fun i _ => by linarith [h1 i])

/-- On the unit box a nonempty exact coalition is bounded by absorption. -/
theorem zeroSingletonProductBase_boxCoalition_le_boxAbsorption {w : ι → ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h1 : ∀ k, w k ≤ 1) {S : Finset ι} (hS : S.Nonempty) :
    zeroSingletonProductBaseBoxCoalition w S ≤ zeroSingletonProductBaseBoxAbsorption w := by
  obtain ⟨p, hp⟩ := hS
  have hinside : (∏ i ∈ S, w i) ≤ w p := by
    rw [← Finset.prod_erase_mul S w hp]
    have hrest : (∏ i ∈ S.erase p, w i) ≤ 1 :=
      Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i)
    nlinarith [Finset.prod_nonneg (fun i (_ : i ∈ S.erase p) => h0 i), h0 p]
  have houtside : (∏ i ∈ Sᶜ, (1 - w i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => by linarith [h1 i]) (fun i _ => by linarith [h0 i])
  have houtsideNonneg : 0 ≤ ∏ i ∈ Sᶜ, (1 - w i) :=
    Finset.prod_nonneg fun i _ => by linarith [h1 i]
  have hinsideNonneg : 0 ≤ ∏ i ∈ S, w i := Finset.prod_nonneg fun i _ => h0 i
  have hsplit : (∏ i, (1 - w i)) = (1 - w p) * ∏ i ∈ (Finset.univ.erase p), (1 - w i) :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)).symm
  have herase : (∏ i ∈ (Finset.univ.erase p), (1 - w i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => by linarith [h1 i]) (fun i _ => by linarith [h0 i])
  have heraseNonneg : 0 ≤ ∏ i ∈ (Finset.univ.erase p), (1 - w i) :=
    Finset.prod_nonneg fun i _ => by linarith [h1 i]
  have habs : w p ≤ zeroSingletonProductBaseBoxAbsorption w := by
    rw [zeroSingletonProductBaseBoxAbsorption]
    unfold Math.PMFProduct.continueMass
    rw [hsplit]
    nlinarith [h0 p, h1 p]
  calc zeroSingletonProductBaseBoxCoalition w S = (∏ i ∈ S, w i) * ∏ i ∈ Sᶜ, (1 - w i) := rfl
    _ ≤ w p * 1 := by nlinarith
    _ = w p := mul_one _
    _ ≤ zeroSingletonProductBaseBoxAbsorption w := habs

/-- On the unit box the quit product of any two distinct coordinates is
bounded by absorption. -/
theorem zeroSingletonProductBase_pairProduct_le_boxAbsorption {w : ι → ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h1 : ∀ k, w k ≤ 1) {i j : ι} (hij : i ≠ j) :
    w i * w j ≤ zeroSingletonProductBaseBoxAbsorption w := by
  have hsplit : (∏ k, (1 - w k)) =
      (∏ k ∈ ({i, j} : Finset ι), (1 - w k)) *
        ∏ k ∈ ({i, j} : Finset ι)ᶜ, (1 - w k) :=
    (Finset.prod_mul_prod_compl _ _).symm
  have hpair : (∏ k ∈ ({i, j} : Finset ι), (1 - w k)) = (1 - w i) * (1 - w j) :=
    Finset.prod_pair hij
  have hrest : (∏ k ∈ ({i, j} : Finset ι)ᶜ, (1 - w k)) ≤ 1 :=
    Finset.prod_le_one (fun k _ => by linarith [h1 k]) (fun k _ => by linarith [h0 k])
  have hrestNonneg : 0 ≤ ∏ k ∈ ({i, j} : Finset ι)ᶜ, (1 - w k) :=
    Finset.prod_nonneg fun k _ => by linarith [h1 k]
  have hpairNonneg : 0 ≤ (1 - w i) * (1 - w j) := by
    have := h1 i; have := h1 j; nlinarith
  have hpairBound : (1 - w i) * (1 - w j) ≤ 1 - w i * w j := by
    nlinarith [h0 i, h0 j, h1 i, h1 j]
  rw [zeroSingletonProductBaseBoxAbsorption]
  unfold Math.PMFProduct.continueMass
  rw [hsplit, hpair]
  nlinarith

end CoalitionBox

/-! ## Root and survival consequences -/

section Survival

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonempty exact coalition atom of a product root is bounded by that
root's absorption mass. -/
theorem zeroSingletonProductBase_coalitionMass_le_absorptionMass (root : ι → PMF Bool)
    {S : Finset ι} (hS : S.Nonempty) :
    quittingRootCoalitionMass root S ≤ quittingRootAbsorptionMass root := by
  have hbox := quittingRootQuitRates_mem_unitBox root
  rw [zeroSingletonProductBase_coalitionMass_eq_boxCoalition,
    quittingRootAbsorptionMass_eq_one_sub_continueMass]
  exact zeroSingletonProductBase_boxCoalition_le_boxAbsorption
    (fun k => (hbox k (Set.mem_univ k)).1)
    (fun k => (hbox k (Set.mem_univ k)).2) hS

omit [DecidableEq ι] in
/-- The per-date telescope step: the survival-weighted absorption mass of a
date is exactly the survival drop across that date. -/
private theorem zeroSingletonProductBase_liveMass_mul_absorption_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time *
        quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time) =
      quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
  have hjoint : quittingJointContinueMass reward profile time =
      quittingStationaryContinueMass (quittingProfileLiveRoot reward profile time) := by
    rw [quittingJointContinueMass_eq_product,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    rfl
  have hsucc : quittingLiveMass reward profile (time + 1) =
      quittingLiveMass reward profile time *
        quittingStationaryContinueMass
          (quittingProfileLiveRoot reward profile time) := by
    rw [quittingLiveMass_succ, hjoint]
  rw [hsucc]
  unfold quittingRootAbsorptionMass
  ring

omit [DecidableEq ι] in
/-- Every prefix sum of the survival-weighted absorption series is the
complement of the survival probability at the cutoff. -/
private theorem zeroSingletonProductBase_sum_range_liveMass_mul_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
        quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time) =
      1 - quittingLiveMass reward profile cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih, zeroSingletonProductBase_liveMass_mul_absorption_eq_sub]
      ring

/-- The total exact-singleton mass of the terminal law is the survival-weighted
series of the live roots' total singleton coalition masses. -/
private theorem zeroSingletonProductBase_hasSum_liveMass_mul_singletonTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    HasSum (fun time => quittingLiveMass reward profile time *
        ∑ who, quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) {who})
      (∑ who, quittingTerminalOutcomeMass reward profile
        (some (quittingSingletonTerminal who))) := by
  have hterm : ∀ who ∈ (Finset.univ : Finset ι),
      HasSum (fun time => quittingLiveMass reward profile time *
        quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) {who})
        (quittingTerminalOutcomeMass reward profile
          (some (quittingSingletonTerminal who))) :=
    fun who _ =>
      terminalOutcomeChronology_hasSum_liveMass_mul_singletonCoalition_singletonLawMass
        reward profile who
  have hsum := hasSum_sum hterm
  refine hsum.congr_fun ?_
  intro time
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
/-- Survival past a date is bounded by the complement of that date's
absorption. -/
private theorem zeroSingletonProductBase_liveMass_succ_le_one_sub_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile (time + 1) ≤
      1 - quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time) := by
  have hstep := zeroSingletonProductBase_liveMass_mul_absorption_eq_sub reward profile time
  have hle := quittingLiveMass_le_one reward profile time
  have habs := quittingRootAbsorptionMass_le_one (quittingProfileLiveRoot reward profile time)
  nlinarith

/-! ## The one-date approximation of a coalition coordinate -/

/-- Every coalition coordinate of a terminal law is approximated by the exact
coalition mass of the live root at any date, with error the absorption before
that date plus the survival past it. -/
private theorem zeroSingletonProductBase_law_sub_coalitionMass_abs_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (S : {S : Finset ι // S.Nonempty}) :
    |quittingTerminalOutcomeMass reward profile (some S) -
        quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile cutoff) S.val| ≤
      (1 - quittingLiveMass reward profile cutoff) +
        quittingLiveMass reward profile (cutoff + 1) := by
  have hf : HasSum (fun time => quittingStageCoalitionMass reward profile time S)
      (quittingTerminalOutcomeMass reward profile (some S)) :=
    terminalOutcomeChronology_hasSum_stageCoalitionMass_absorbedMassLimit reward profile S
  have hstage : ∀ time, quittingStageCoalitionMass reward profile time S =
      quittingLiveMass reward profile time *
        quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) S.val :=
    fun time =>
      quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass reward profile time S
  have hfnonneg : ∀ time, 0 ≤ quittingStageCoalitionMass reward profile time S :=
    fun time => quittingStageCoalitionMass_nonneg reward profile time S
  have hfg : ∀ time, quittingStageCoalitionMass reward profile time S ≤
      quittingLiveMass reward profile time *
        quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time) := by
    intro time
    rw [hstage time]
    exact mul_le_mul_of_nonneg_left (zeroSingletonProductBase_coalitionMass_le_absorptionMass _ S.2)
      (quittingLiveMass_nonneg reward profile time)
  have hlow : quittingStageCoalitionMass reward profile cutoff S ≤
      quittingTerminalOutcomeMass reward profile (some S) :=
    le_hasSum hf cutoff fun time _ => hfnonneg time
  have hpre : ∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile time S ≤
      1 - quittingLiveMass reward profile cutoff := by
    calc ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time S
        ≤ ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
            quittingRootAbsorptionMass
              (quittingProfileLiveRoot reward profile time) :=
          Finset.sum_le_sum fun time _ => hfg time
      _ = 1 - quittingLiveMass reward profile cutoff :=
          zeroSingletonProductBase_sum_range_liveMass_mul_absorption reward profile cutoff
  have hupper : quittingTerminalOutcomeMass reward profile (some S) ≤
      (1 - quittingLiveMass reward profile cutoff) +
        quittingStageCoalitionMass reward profile cutoff S +
        quittingLiveMass reward profile (cutoff + 1) := by
    refine le_of_tendsto hf.tendsto_sum_nat ?_
    filter_upwards [eventually_ge_atTop (cutoff + 1)] with horizon hhorizon
    have hIco : ∑ time ∈ Finset.Ico (cutoff + 1) horizon,
        quittingStageCoalitionMass reward profile time S ≤
        ∑ time ∈ Finset.Ico (cutoff + 1) horizon,
          quittingLiveMass reward profile time *
            quittingRootAbsorptionMass
              (quittingProfileLiveRoot reward profile time) :=
      Finset.sum_le_sum fun time _ => hfg time
    rw [Finset.sum_Ico_eq_sub _ hhorizon, Finset.sum_Ico_eq_sub _ hhorizon,
      zeroSingletonProductBase_sum_range_liveMass_mul_absorption reward profile horizon,
      zeroSingletonProductBase_sum_range_liveMass_mul_absorption
        reward profile (cutoff + 1)] at hIco
    have hsucc : ∑ time ∈ Finset.range (cutoff + 1),
        quittingStageCoalitionMass reward profile time S =
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time S) +
          quittingStageCoalitionMass reward profile cutoff S :=
      Finset.sum_range_succ _ _
    have hhorizonNonneg := quittingLiveMass_nonneg reward profile horizon
    linarith
  have hL1 := quittingLiveMass_le_one reward profile cutoff
  have hL0 := quittingLiveMass_nonneg reward profile cutoff
  have hLs0 := quittingLiveMass_nonneg reward profile (cutoff + 1)
  have hcoalNonneg := quittingRootCoalitionMass_nonneg
    (quittingProfileLiveRoot reward profile cutoff) S.val
  have hcoalLe : quittingRootCoalitionMass
      (quittingProfileLiveRoot reward profile cutoff) S.val ≤ 1 :=
    le_trans (zeroSingletonProductBase_coalitionMass_le_absorptionMass _ S.2)
      (quittingRootAbsorptionMass_le_one _)
  have hcut := hstage cutoff
  rw [abs_le]
  constructor <;>
    nlinarith [hlow, hupper, hcut, hcoalNonneg, hcoalLe, hL0, hL1, hLs0,
      mul_nonneg (sub_nonneg.mpr hL1) hcoalNonneg]

/-! ## The efficient-date selection -/

/-- A date failing the efficiency test contributes at least its scaled
survival-weighted absorption to the survival-weighted singleton series. -/
private theorem zeroSingletonProductBase_scaled_absorptionStage_le_singletonStage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (scale : ℝ) (time : ℕ)
    (hfail : ¬(0 < quittingRootAbsorptionMass
        (quittingProfileLiveRoot reward profile time) ∧
      (∑ who, quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) {who}) ≤
        scale * quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time))) :
    scale * (quittingLiveMass reward profile time *
        quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time)) ≤
      quittingLiveMass reward profile time *
        ∑ who, quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) {who} := by
  have hlive := quittingLiveMass_nonneg reward profile time
  have habs := quittingRootAbsorptionMass_nonneg
    (quittingProfileLiveRoot reward profile time)
  rcases eq_or_lt_of_le habs with hzero | hpos
  · have hall : ∀ who : ι, quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) {who} = 0 := by
      intro who
      have hle := zeroSingletonProductBase_coalitionMass_le_absorptionMass
        (quittingProfileLiveRoot reward profile time) (Finset.singleton_nonempty who)
      have hge := quittingRootCoalitionMass_nonneg
        (quittingProfileLiveRoot reward profile time) {who}
      linarith
    have hsum : (∑ who, quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) {who}) = 0 :=
      Finset.sum_eq_zero fun who _ => hall who
    rw [hsum, ← hzero]
    simp
  · have hgap : scale * quittingRootAbsorptionMass
        (quittingProfileLiveRoot reward profile time) <
        ∑ who, quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) {who} := by
      rcases not_and_or.mp hfail with hcontra | hcontra
      · exact absurd hpos hcontra
      · exact not_le.mp hcontra
    nlinarith

/-- If no date passes the efficiency test, the scaled absorbed mass of the
whole play is bounded by the total singleton mass. -/
private theorem zeroSingletonProductBase_scaled_one_sub_never_le_singletonTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (scale : ℝ)
    (hfail : ∀ time, ¬(0 < quittingRootAbsorptionMass
        (quittingProfileLiveRoot reward profile time) ∧
      (∑ who, quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) {who}) ≤
        scale * quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time))) :
    scale * (1 - quittingTerminalOutcomeMass reward profile none) ≤
      ∑ who, quittingTerminalOutcomeMass reward profile
        (some (quittingSingletonTerminal who)) :=
  hasSum_le
    (fun time =>
      zeroSingletonProductBase_scaled_absorptionStage_le_singletonStage
        reward profile scale time (hfail time))
    ((terminalOutcomeChronology_hasSum_liveMass_mul_absorption_one_sub_neverMass
      reward profile).mul_left scale)
    (zeroSingletonProductBase_hasSum_liveMass_mul_singletonTotal reward profile)

/-- If no date before a cutoff passes the efficiency test, the scaled mass
absorbed before that cutoff is bounded by the total singleton mass. -/
private theorem zeroSingletonProductBase_scaled_absorbedBefore_le_singletonTotal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (scale : ℝ) (cutoff : ℕ)
    (hfail : ∀ time, time < cutoff → ¬(0 < quittingRootAbsorptionMass
        (quittingProfileLiveRoot reward profile time) ∧
      (∑ who, quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) {who}) ≤
        scale * quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time))) :
    scale * (1 - quittingLiveMass reward profile cutoff) ≤
      ∑ who, quittingTerminalOutcomeMass reward profile
        (some (quittingSingletonTerminal who)) := by
  have hprefix : scale * (1 - quittingLiveMass reward profile cutoff) =
      ∑ time ∈ Finset.range cutoff, scale * (quittingLiveMass reward profile time *
        quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time)) := by
    rw [← Finset.mul_sum, zeroSingletonProductBase_sum_range_liveMass_mul_absorption]
  rw [hprefix]
  calc ∑ time ∈ Finset.range cutoff, scale * (quittingLiveMass reward profile time *
        quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time))
      ≤ ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
          ∑ who, quittingRootCoalitionMass
            (quittingProfileLiveRoot reward profile time) {who} :=
        Finset.sum_le_sum fun time htime =>
          zeroSingletonProductBase_scaled_absorptionStage_le_singletonStage
            reward profile scale time
            (hfail time (Finset.mem_range.mp htime))
    _ ≤ ∑ who, quittingTerminalOutcomeMass reward profile
          (some (quittingSingletonTerminal who)) :=
        sum_le_hasSum _
          (fun time _ => mul_nonneg (quittingLiveMass_nonneg reward profile time)
            (Finset.sum_nonneg fun who _ => quittingRootCoalitionMass_nonneg _ _))
          (zeroSingletonProductBase_hasSum_liveMass_mul_singletonTotal reward profile)

/-! ## The closed-law product base -/

/-- **Closed-law product-base selection data.**  The product-base hypotheses
select a limiting quit-rate vector with a sure pair, a strictly monotone index
map into the approximating sequence, and a total efficient-date selector, along
which the live roots converge coordinatewise to the limiting quit rates, the
survival mass at the selected dates tends to one, and the limit law is exactly
the product-root law of those quit rates. -/
theorem zeroSingletonProductBase_zeroNever_zeroSingleton_exists_selectionData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hlaw : ∀ outcome, Filter.Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      Filter.atTop (nhds (mu outcome)))
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι) :
    ∃ (w : ι → ℝ) (i j : ι) (phi : ℕ → ℕ) (date : ℕ → ℕ),
      i ≠ j ∧ StrictMono phi ∧
      (∀ k, 0 ≤ w k) ∧ (∀ k, w k ≤ 1) ∧ w i = 1 ∧ w j = 1 ∧
      (∀ S : {S : Finset ι // S.Nonempty},
        mu (some S) = zeroSingletonProductBaseBoxCoalition w S.val) ∧
      (∀ who, Filter.Tendsto (fun m =>
          (quittingProfileLiveRoot reward (profiles (phi m)) (date (phi m))
            who true).toReal)
        Filter.atTop (nhds (w who))) ∧
      Filter.Tendsto (fun m =>
          1 - quittingLiveMass reward (profiles (phi m)) (date (phi m)))
        Filter.atTop (nhds 0) := by
  classical
  obtain ⟨sig, hsig⟩ : ∃ f : ℕ → ℝ, ∀ n, f n =
      ∑ who, quittingTerminalOutcomeMass reward (profiles n)
        (some (quittingSingletonTerminal who)) := ⟨_, fun _ => rfl⟩
  obtain ⟨zet, hzet⟩ : ∃ f : ℕ → ℝ, ∀ n, f n =
      quittingTerminalOutcomeMass reward (profiles n) none := ⟨_, fun _ => rfl⟩
  -- Step 1: the singleton total and the Never coordinate vanish.
  have hsigNonneg : ∀ n, 0 ≤ sig n := by
    intro n
    rw [hsig]
    exact Finset.sum_nonneg fun who _ =>
      (quittingTerminalOutcomeMass_mem_stdSimplex reward (profiles n)).1 _
  have hzetNonneg : ∀ n, 0 ≤ zet n := by
    intro n
    rw [hzet]
    exact (quittingTerminalOutcomeMass_mem_stdSimplex reward (profiles n)).1 _
  have hsigLim : Tendsto sig atTop (nhds 0) := by
    have hterms : Tendsto (fun n => ∑ who : ι,
        quittingTerminalOutcomeMass reward (profiles n)
          (some (quittingSingletonTerminal who))) atTop (nhds (∑ _who : ι, (0 : ℝ))) :=
      tendsto_finsetSum _ fun who _ => by
        simpa [hsingleton who] using hlaw (some (quittingSingletonTerminal who))
    rw [Finset.sum_const_zero] at hterms
    exact (tendsto_congr hsig).mpr hterms
  have hzetLim : Tendsto zet atTop (nhds 0) := by
    have hnone := hlaw none
    rw [hNever] at hnone
    exact (tendsto_congr hzet).mpr hnone
  -- Step 2: a positive vanishing scale dominating the singleton total.
  obtain ⟨del, hdel⟩ : ∃ f : ℕ → ℝ, ∀ n : ℕ, f n =
      Real.sqrt (sig n) + 1 / ((n : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have hdelPos : ∀ n, 0 < del n := by
    intro n
    rw [hdel]
    have hshift : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hroot : (0 : ℝ) ≤ Real.sqrt (sig n) := Real.sqrt_nonneg _
    linarith
  have hsqrtLim : Tendsto (fun n => Real.sqrt (sig n)) atTop (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hsigLim
  have hdelLim : Tendsto del atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hadd := hsqrtLim.add hshift
    rw [add_zero] at hadd
    exact (tendsto_congr hdel).mpr hadd
  have hratioLe : ∀ n, sig n / del n ≤ Real.sqrt (sig n) := by
    intro n
    rw [div_le_iff₀ (hdelPos n)]
    have hsq : Real.sqrt (sig n) * Real.sqrt (sig n) = sig n :=
      Real.mul_self_sqrt (hsigNonneg n)
    have hle : Real.sqrt (sig n) ≤ del n := by
      rw [hdel]
      have hshift : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    nlinarith [Real.sqrt_nonneg (sig n)]
  have hratioLim : Tendsto (fun n => sig n / del n) atTop (nhds 0) :=
    squeeze_zero (fun n => div_nonneg (hsigNonneg n) (hdelPos n).le) hratioLe hsqrtLim
  -- Step 3: eventually some date passes the efficiency test.
  have heventual : ∀ᶠ n in atTop, sig n / del n < 1 / 2 ∧ zet n < 1 / 2 := by
    filter_upwards [hratioLim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
      hzetLim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hone htwo
    exact ⟨hone, htwo⟩
  obtain ⟨start, hstart⟩ := eventually_atTop.mp heventual
  have hexists : ∀ n, start ≤ n → ∃ time,
      0 < quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward (profiles n) time) ∧
        (∑ who, quittingRootCoalitionMass
          (quittingProfileLiveRoot reward (profiles n) time) {who}) ≤
          del n * quittingRootAbsorptionMass
            (quittingProfileLiveRoot reward (profiles n) time) := by
    intro n hn
    by_contra hno
    have hbound :=
      zeroSingletonProductBase_scaled_one_sub_never_le_singletonTotal
        reward (profiles n) (del n) (not_exists.mp hno)
    rw [← hsig n, ← hzet n] at hbound
    have hratio : 1 - zet n ≤ sig n / del n := by
      rw [le_div_iff₀ (hdelPos n), mul_comm]
      exact hbound
    obtain ⟨hone, htwo⟩ := hstart n hn
    linarith
  -- The first efficient date, chosen only past the eventual threshold.
  have hchoice : ∀ n : ℕ, ∃ time : ℕ, start ≤ n →
      (0 < quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward (profiles n) time) ∧
        (∑ who, quittingRootCoalitionMass
          (quittingProfileLiveRoot reward (profiles n) time) {who}) ≤
          del n * quittingRootAbsorptionMass
            (quittingProfileLiveRoot reward (profiles n) time)) ∧
      ∀ earlier, earlier < time → ¬(0 < quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward (profiles n) earlier) ∧
        (∑ who, quittingRootCoalitionMass
          (quittingProfileLiveRoot reward (profiles n) earlier) {who}) ≤
          del n * quittingRootAbsorptionMass
            (quittingProfileLiveRoot reward (profiles n) earlier)) := by
    intro n
    by_cases hn : start ≤ n
    · have hex := hexists n hn
      exact ⟨Nat.find hex, fun _ =>
        ⟨Nat.find_spec hex, fun earlier hearlier => Nat.find_min hex hearlier⟩⟩
    · exact ⟨0, fun hcontra => absurd hcontra hn⟩
  choose date hdate using hchoice
  -- Step 4: absorption strictly before the selected date vanishes.
  have hbefore : ∀ n, start ≤ n →
      1 - quittingLiveMass reward (profiles n) (date n) ≤ sig n / del n := by
    intro n hn
    have hbound :=
      zeroSingletonProductBase_scaled_absorbedBefore_le_singletonTotal
        reward (profiles n) (del n) (date n) (hdate n hn).2
    rw [← hsig n] at hbound
    rw [le_div_iff₀ (hdelPos n), mul_comm]
    exact hbound
  -- Step 5: the selected roots concentrate on a fixed pair.
  let rates : ℕ → ι → ℝ := fun k who =>
    (quittingProfileLiveRoot reward (profiles (k + start))
      (date (k + start)) who true).toReal
  have hrates0 : ∀ k who, 0 ≤ rates k who := by
    intro k who
    exact ((quittingRootQuitRates_mem_unitBox
      (quittingProfileLiveRoot reward (profiles (k + start))
        (date (k + start)))) who (Set.mem_univ who)).1
  have hrates1 : ∀ k who, rates k who ≤ 1 := by
    intro k who
    exact ((quittingRootQuitRates_mem_unitBox
      (quittingProfileLiveRoot reward (profiles (k + start))
        (date (k + start)))) who (Set.mem_univ who)).2
  have hsingletonRates : ∀ k,
      Math.PMFProduct.singletonMass (rates k) ≤
        del (k + start) *
          (1 - Math.PMFProduct.continueMass (rates k)) := by
    intro k
    have hselected := ((hdate (k + start) (by omega)).1).2
    rw [sum_quittingRootSingletonMass_eq_pmfProductSingletonMass,
      quittingRootAbsorptionMass_eq_one_sub_continueMass] at hselected
    exact hselected
  have habsorptionRates : ∀ k,
      0 < 1 - Math.PMFProduct.continueMass (rates k) := by
    intro k
    have hselected := ((hdate (k + start) (by omega)).1).1
    rw [quittingRootAbsorptionMass_eq_one_sub_continueMass] at hselected
    exact hselected
  obtain ⟨i, j, pick, hij, hpick, hpair⟩ :=
    Math.PMFProduct.exists_pair_subsequence_mul_tendsto_one_of_singletonMass_ratio_tendsto_zero
      rates (fun k => del (k + start)) hrates0 hrates1
      (hdelLim.comp (tendsto_add_atTop_nat start))
      hsingletonRates habsorptionRates hcard
  -- Step 6: the selected quit-rate vectors converge in the unit box.
  obtain ⟨quit, hquit⟩ : ∃ f : ℕ → ι → ℝ, ∀ k who, f k who =
      (quittingProfileLiveRoot reward (profiles (pick k + start))
        (date (pick k + start)) who true).toReal := ⟨_, fun _ _ => rfl⟩
  have hquitfun : ∀ k, quit k = fun who =>
      (quittingProfileLiveRoot reward (profiles (pick k + start))
        (date (pick k + start)) who true).toReal := fun k => funext (hquit k)
  have hcompact : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ k, quit k ∈ Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
    intro k
    rw [hquitfun k]
    exact quittingRootQuitRates_mem_unitBox _
  obtain ⟨w, hwmem, trim, htrim, hlim⟩ := hcompact.tendsto_subseq hmem
  have hw0 : ∀ k, 0 ≤ w k := fun k => (hwmem k (Set.mem_univ k)).1
  have hw1 : ∀ k, w k ≤ 1 := fun k => (hwmem k (Set.mem_univ k)).2
  have hcoord : ∀ k : ι, Tendsto (fun m => quit (trim m) k) atTop (nhds (w k)) :=
    fun k => (tendsto_pi_nhds.mp hlim) k
  have hpairLim : Tendsto (fun m => quit (trim m) i * quit (trim m) j) atTop (nhds 1) := by
    simpa only [Function.comp_def, hquit] using hpair.comp htrim.tendsto_atTop
  have hwij : w i * w j = 1 :=
    tendsto_nhds_unique ((hcoord i).mul (hcoord j)) hpairLim
  have hwi : w i = 1 := by
    by_contra hne
    have hlt : w i < 1 := lt_of_le_of_ne (hw1 i) hne
    nlinarith [hw0 i, hw0 j, hw1 j]
  have hwj : w j = 1 := by
    by_contra hne
    have hlt : w j < 1 := lt_of_le_of_ne (hw1 j) hne
    nlinarith [hw0 i, hw0 j, hw1 i]
  have hstrict : StrictMono fun m => pick (trim m) + start := by
    intro a b hab
    exact Nat.add_lt_add_right (hpick (htrim hab)) start
  have hshiftRatio : Tendsto (fun m => sig (pick (trim m) + start) /
      del (pick (trim m) + start)) atTop (nhds 0) :=
    hratioLim.comp hstrict.tendsto_atTop
  -- Step 7: the selected root reproduces every coalition coordinate.
  have hlaweq : ∀ S : {S : Finset ι // S.Nonempty},
      mu (some S) = zeroSingletonProductBaseBoxCoalition w S.val := by
    intro S
    have hlawLim : Tendsto (fun m => quittingTerminalOutcomeMass reward
        (profiles (pick (trim m) + start)) (some S)) atTop (nhds (mu (some S))) :=
      (hlaw (some S)).comp hstrict.tendsto_atTop
    have hboxLim : Tendsto
        (fun m => zeroSingletonProductBaseBoxCoalition (quit (trim m)) S.val) atTop
        (nhds (zeroSingletonProductBaseBoxCoalition w S.val)) :=
      ((zeroSingletonProductBase_continuous_boxCoalition S.val).tendsto w).comp hlim
    have herr : ∀ m, |quittingTerminalOutcomeMass reward
        (profiles (pick (trim m) + start)) (some S) -
          zeroSingletonProductBaseBoxCoalition (quit (trim m)) S.val| ≤
        sig (pick (trim m) + start) / del (pick (trim m) + start) +
          (1 - quit (trim m) i * quit (trim m) j) := by
      intro m
      have hbase := zeroSingletonProductBase_law_sub_coalitionMass_abs_le reward
        (profiles (pick (trim m) + start)) (date (pick (trim m) + start)) S
      have hcoal : quittingRootCoalitionMass
          (quittingProfileLiveRoot reward (profiles (pick (trim m) + start))
            (date (pick (trim m) + start))) S.val =
          zeroSingletonProductBaseBoxCoalition (quit (trim m)) S.val := by
        rw [hquitfun (trim m)]
        exact zeroSingletonProductBase_coalitionMass_eq_boxCoalition _ S.val
      have hsucc := zeroSingletonProductBase_liveMass_succ_le_one_sub_absorption reward
        (profiles (pick (trim m) + start)) (date (pick (trim m) + start))
      have habsorb : quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward (profiles (pick (trim m) + start))
            (date (pick (trim m) + start))) =
          zeroSingletonProductBaseBoxAbsorption (quit (trim m)) := by
        rw [hquitfun (trim m)]
        exact quittingRootAbsorptionMass_eq_one_sub_continueMass _
      have hboxmem := hmem (trim m)
      have hpairLe : quit (trim m) i * quit (trim m) j ≤
          zeroSingletonProductBaseBoxAbsorption (quit (trim m)) :=
        zeroSingletonProductBase_pairProduct_le_boxAbsorption
          (fun k => (hboxmem k (Set.mem_univ k)).1)
          (fun k => (hboxmem k (Set.mem_univ k)).2) hij
      have hpre := hbefore (pick (trim m) + start) (by omega)
      rw [hcoal] at hbase
      rw [habsorb] at hsucc
      rw [abs_le] at hbase ⊢
      exact ⟨by linarith [hbase.1], by linarith [hbase.2]⟩
    have herrLim : Tendsto (fun m =>
        sig (pick (trim m) + start) / del (pick (trim m) + start) +
          (1 - quit (trim m) i * quit (trim m) j)) atTop (nhds 0) := by
      have htwo : Tendsto (fun m => 1 - quit (trim m) i * quit (trim m) j) atTop
          (nhds 0) := by
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hpairLim
      simpa using hshiftRatio.add htwo
    have habsLim := (hlawLim.sub hboxLim).abs
    have hnonpos : |mu (some S) - zeroSingletonProductBaseBoxCoalition w S.val| ≤ 0 :=
      le_of_tendsto_of_tendsto habsLim herrLim (Eventually.of_forall herr)
    have hzero : mu (some S) - zeroSingletonProductBaseBoxCoalition w S.val = 0 :=
      abs_eq_zero.mp (le_antisymm hnonpos (abs_nonneg _))
    linarith
  -- Step 8: the survival mass at the selected dates tends to one.
  have hsurvive : Tendsto (fun m =>
      1 - quittingLiveMass reward (profiles (pick (trim m) + start))
        (date (pick (trim m) + start))) atTop (nhds 0) :=
    squeeze_zero
      (fun m => by
        linarith [quittingLiveMass_le_one reward (profiles (pick (trim m) + start))
          (date (pick (trim m) + start))])
      (fun m => hbefore (pick (trim m) + start) (by omega)) hshiftRatio
  refine ⟨w, i, j, fun m => pick (trim m) + start, date, hij, hstrict, hw0, hw1,
    hwi, hwj, hlaweq, fun who => ?_, hsurvive⟩
  simpa only [hquit] using hcoord who

/-- **Closed-law product-base theorem.**  A coordinatewise limit of ordinary
behavioral quitting laws whose Never coordinate and whose every singleton
coordinate vanish is exactly one product-root law, and the limiting quit-rate
vector has at least two sure quitters. -/
theorem zeroSingletonProductBase_zeroNever_zeroSingleton_law_productBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hlaw : ∀ outcome, Filter.Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      Filter.atTop (nhds (mu outcome)))
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι) :
    ∃ (w : ι → ℝ) (i j : ι), i ≠ j ∧ w i = 1 ∧ w j = 1 ∧
      (∀ k, 0 ≤ w k) ∧ (∀ k, w k ≤ 1) ∧
      ∀ S : {S : Finset ι // S.Nonempty},
        mu (some S) = zeroSingletonProductBaseBoxCoalition w S.val := by
  obtain ⟨w, i, j, _, _, hij, _, hw0, hw1, hwi, hwj, hlaweq, _, _⟩ :=
    zeroSingletonProductBase_zeroNever_zeroSingleton_exists_selectionData
      reward profiles mu hlaw hNever hsingleton hcard
  exact ⟨w, i, j, hij, hwi, hwj, hw0, hw1, hlaweq⟩

end Survival

end GameTheory
