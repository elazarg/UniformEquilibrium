/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SublinearCostSchedule
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalSeamReduction

/-!
# Budget-stable iteration of compatible quitting packets

This module turns a local reached-port packet system into one compatible
infinite block chain.  A sublinear combined seam/availability cost selects a
vanishing scale schedule with divergent total scale and summable total cost.
The availability-loss account then keeps every recursive packet call legal.
Two fixed literal marginal hazards supply the survival fields of the existing
summable-seam compiler.

The certificate capstones below are conditional on an explicit seed whose
canonical debt is already at most the requested error.  Actual
positive-minimum-debt annotations cannot supply such seeds at arbitrarily
small errors.  If the annotations are artificial, a separate adapter from the
actual reached source to the canonical anchor is still required.  Thus these
results are an iteration interface, not a producer for the positive-minimum
route and not a reformulation of the universal quitting-game conjecture.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One packet selected at a reached port and a legal scale.  Its roots are
literal roots and both hazard estimates concern those exact roots. -/
structure QuittingBudgetStablePacketData
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {Port : Type}
    (annotation : Port → QuittingTerminalSemanticPair ι)
    (radius : Port → ℝ) (omega chi : ℝ → ℝ)
    (kappa : ℝ) (first second : ι) (bound : ℝ)
    (source : Port) (scale : ℝ) where
  length : ℕ
  length_pos : 0 < length
  roots : ℕ → ι → PMF Bool
  candidate : ℕ → QuittingTerminalSemanticPair ι
  successor : Port
  exact_step : ∀ offset, offset < length →
    candidate offset =
      quittingTerminalSemanticPrefix reward (roots offset) (candidate (offset + 1))
  entrance_anchor : candidate 0 = annotation source
  prescribed_endpoint : ∀ who,
    |(candidate length).1 who - (annotation successor).1 who| ≤ omega scale
  total_endpoint : ∀ who,
    |(candidate length).1 who - (annotation successor).1 who| +
        |(candidate length).2 who - (annotation successor).2 who| ≤ omega scale
  first_hazard : kappa * scale ≤
    ∑ offset ∈ Finset.range length,
      quittingMarginalQuitHazard roots first offset
  second_hazard : kappa * scale ≤
    ∑ offset ∈ Finset.range length,
      quittingMarginalQuitHazard roots second offset
  radius_successor : radius source - chi scale ≤ radius successor
  debt_nonneg : ∀ offset, offset ≤ length → ∀ who,
    0 ≤ quittingTerminalSemanticDebt (candidate offset) who
  prescribed_bounded : ∀ offset, offset ≤ length → ∀ who,
    |(candidate offset).1 who| ≤ bound
  debt_bounded : ∀ offset, offset ≤ length → ∀ who,
    |quittingTerminalSemanticDebt (candidate offset) who| ≤ bound

/-- Local port packet system with a single uniform candidate-annotation bound.
The port may carry actual-source provenance externally, but this structure does
not identify that source with `annotation`. The availability field asks only
for one good candidate packet at each legal pair. -/
structure QuittingBudgetStablePacketSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  Port : Type
  annotation : Port → QuittingTerminalSemanticPair ι
  radius : Port → ℝ
  radius_pos : ∀ source, 0 < radius source
  omega : ℝ → ℝ
  chi : ℝ → ℝ
  omega_nonneg : ∀ scale, 0 ≤ omega scale
  chi_nonneg : ∀ scale, 0 ≤ chi scale
  kappa : ℝ
  kappa_pos : 0 < kappa
  first : ι
  second : ι
  labels_ne : first ≠ second
  bound : ℝ
  packetAvailable : ∀ (source : Port) (scale : ℝ),
    0 < scale → scale < radius source →
      Nonempty (QuittingBudgetStablePacketData (reward := reward)
        annotation radius omega chi kappa first second bound source scale)
  cost_sublinear : IsOperationallySublinearCost (fun scale => omega scale + chi scale)

/-- Packet data specialized to all fields of one packet system. -/
abbrev QuittingBudgetStablePacket
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (system : QuittingBudgetStablePacketSystem reward)
    (source : system.Port) (scale : ℝ) :=
  QuittingBudgetStablePacketData system.annotation system.radius
    system.omega system.chi system.kappa system.first system.second
    system.bound source scale (reward := reward)

namespace QuittingBudgetStablePacketSystem

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (system : QuittingBudgetStablePacketSystem reward)

/-- The nonnegative combined seam and availability cost. -/
def cost (scale : ℝ) : ℝ := system.omega scale + system.chi scale

theorem cost_nonneg (scale : ℝ) : 0 ≤ system.cost scale :=
  add_nonneg (system.omega_nonneg scale) (system.chi_nonneg scale)

theorem omega_le_cost (scale : ℝ) : system.omega scale ≤ system.cost scale := by
  unfold cost
  linarith [system.chi_nonneg scale]

theorem chi_le_cost (scale : ℝ) : system.chi scale ≤ system.cost scale := by
  unfold cost
  linarith [system.omega_nonneg scale]

/-- A chosen packet at a legal state-scale pair. -/
private noncomputable def choosePacket
    (source : system.Port) (scale : ℝ)
    (hscale : 0 < scale) (hlegal : scale < system.radius source) :
    QuittingBudgetStablePacket system source scale :=
  Classical.choice (system.packetAvailable source scale hscale hlegal)

/-! ## Recursive compatible selection -/

section Selection

variable {budget cap : ℝ}
  (schedule : BudgetedDivergentCostSchedule system.cost budget cap)
  (seed : system.Port)

private theorem chi_prefix_le (block : ℕ) :
    (∑ prior ∈ Finset.range block, system.chi (schedule.scale prior)) ≤ budget := by
  calc
    (∑ prior ∈ Finset.range block, system.chi (schedule.scale prior)) ≤
        ∑ prior ∈ Finset.range block, system.cost (schedule.scale prior) :=
      Finset.sum_le_sum fun prior _ => system.chi_le_cost _
    _ ≤ ∑' prior, system.cost (schedule.scale prior) :=
      schedule.cost_summable.sum_le_tsum _ fun prior _ => system.cost_nonneg _
    _ ≤ budget := schedule.cost_tsum_le

/-- A reached port together with the radius lower bound paid for by all
earlier availability losses. -/
private def SelectionState (block : ℕ) :=
  {source : system.Port //
    system.radius seed -
        (∑ prior ∈ Finset.range block, system.chi (schedule.scale prior)) ≤
      system.radius source}

private theorem scale_legal
    (hroom : cap + budget < system.radius seed)
    (block : ℕ) (state : system.SelectionState schedule seed block) :
    schedule.scale block < system.radius state.1 := by
  have hprefix := system.chi_prefix_le schedule block
  have hscale := schedule.scale_lt_cap block
  have hinvariant := state.2
  linarith

/-- Dependent recursion selects the successor of the chosen legal packet and
carries the remaining-radius invariant to the next state. -/
private noncomputable def selectionState
    (hroom : cap + budget < system.radius seed) :
    (block : ℕ) → system.SelectionState schedule seed block
  | 0 => ⟨seed, by simp⟩
  | block + 1 => by
      let current := selectionState hroom block
      let packet := system.choosePacket current.1 (schedule.scale block)
        (schedule.scale_pos block) (system.scale_legal schedule seed hroom block current)
      refine ⟨packet.successor, ?_⟩
      rw [Finset.sum_range_succ]
      calc
        system.radius seed -
              ((∑ prior ∈ Finset.range block, system.chi (schedule.scale prior)) +
                system.chi (schedule.scale block)) =
            (system.radius seed -
                ∑ prior ∈ Finset.range block, system.chi (schedule.scale prior)) -
              system.chi (schedule.scale block) := by ring
        _ ≤ system.radius current.1 - system.chi (schedule.scale block) :=
          sub_le_sub_right current.2 _
        _ ≤ system.radius packet.successor := packet.radius_successor

/-- Port reached at the entrance of the selected block. -/
def selectedPort
    (hroom : cap + budget < system.radius seed) (block : ℕ) : system.Port :=
  (system.selectionState schedule seed hroom block).1

/-- Packet selected at a recursively reached port. -/
def selectedPacket
    (hroom : cap + budget < system.radius seed) (block : ℕ) :
    QuittingBudgetStablePacket system
      (system.selectedPort schedule seed hroom block) (schedule.scale block) :=
  system.choosePacket _ _ (schedule.scale_pos block)
    (system.scale_legal schedule seed hroom block
      (system.selectionState schedule seed hroom block))

@[simp] theorem selectedPort_zero
    (hroom : cap + budget < system.radius seed) :
    system.selectedPort schedule seed hroom 0 = seed := rfl

theorem selectedPacket_successor
    (hroom : cap + budget < system.radius seed) (block : ℕ) :
    (system.selectedPacket schedule seed hroom block).successor =
      system.selectedPort schedule seed hroom (block + 1) := by
  simp [selectedPacket, selectedPort, selectionState]

/-- Literal blocks and annotations produced by recursive compatible packet
selection. -/
def selectedBlocks
    (hroom : cap + budget < system.radius seed) :
    QuittingVariableLengthSeamBlocksNat reward where
  length := fun block => (system.selectedPacket schedule seed hroom block).length
  length_pos := fun block =>
    (system.selectedPacket schedule seed hroom block).length_pos
  roots := fun block => (system.selectedPacket schedule seed hroom block).roots
  candidate := fun block =>
    (system.selectedPacket schedule seed hroom block).candidate
  exact_step := fun block =>
    (system.selectedPacket schedule seed hroom block).exact_step
  debt_nonneg := fun block =>
    (system.selectedPacket schedule seed hroom block).debt_nonneg
  prescribed_bounded := ⟨system.bound, fun block =>
    (system.selectedPacket schedule seed hroom block).prescribed_bounded⟩
  debt_bounded := ⟨system.bound, fun block =>
    (system.selectedPacket schedule seed hroom block).debt_bounded⟩

theorem selectedBlocks_prescribedSeam_le
    (hroom : cap + budget < system.radius seed) (who : ι) (block : ℕ) :
    (system.selectedBlocks schedule seed hroom).prescribedBlockSeamNat who block ≤
      system.omega (schedule.scale block) := by
  change |((system.selectedPacket schedule seed hroom block).candidate
      (system.selectedPacket schedule seed hroom block).length).1 who -
    ((system.selectedPacket schedule seed hroom (block + 1)).candidate 0).1 who| ≤ _
  rw [(system.selectedPacket schedule seed hroom (block + 1)).entrance_anchor,
    ← system.selectedPacket_successor schedule seed (hroom := hroom) block]
  exact (system.selectedPacket schedule seed hroom block).prescribed_endpoint who

theorem selectedBlocks_totalSeam_le
    (hroom : cap + budget < system.radius seed) (who : ι) (block : ℕ) :
    (system.selectedBlocks schedule seed hroom).totalBlockSeamNat who block ≤
      system.omega (schedule.scale block) := by
  change |((system.selectedPacket schedule seed hroom block).candidate
        (system.selectedPacket schedule seed hroom block).length).1 who -
      ((system.selectedPacket schedule seed hroom (block + 1)).candidate 0).1 who| +
    |((system.selectedPacket schedule seed hroom block).candidate
        (system.selectedPacket schedule seed hroom block).length).2 who -
      ((system.selectedPacket schedule seed hroom (block + 1)).candidate 0).2 who| ≤ _
  rw [(system.selectedPacket schedule seed hroom (block + 1)).entrance_anchor,
    ← system.selectedPacket_successor schedule seed (hroom := hroom) block]
  exact (system.selectedPacket schedule seed hroom block).total_endpoint who

private theorem not_summable_flatHazard
    (hroom : cap + budget < system.radius seed) (owner : ι)
    (hpacket : ∀ block, system.kappa * schedule.scale block ≤
      ∑ offset ∈ Finset.range
          (system.selectedPacket schedule seed hroom block).length,
        quittingMarginalQuitHazard
          (system.selectedPacket schedule seed hroom block).roots owner offset) :
    ¬Summable (quittingMarginalQuitHazard
      (system.selectedBlocks schedule seed hroom).flatRootNat owner) := by
  intro hsummable
  have hscaleTop : Tendsto (fun blocks =>
      ∑ block ∈ Finset.range blocks, schedule.scale block) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      fun block => (schedule.scale_pos block).le).mp schedule.scale_not_summable
  have heventually : ∀ᶠ blocks : ℕ in atTop,
      (∑' time, quittingMarginalQuitHazard
        (system.selectedBlocks schedule seed hroom).flatRootNat owner time) /
          system.kappa <
        ∑ block ∈ Finset.range blocks, schedule.scale block :=
    hscaleTop.eventually (eventually_gt_atTop _)
  obtain ⟨blocks, hlarge⟩ := heventually.exists
  have hcompare : system.kappa *
      (∑ block ∈ Finset.range blocks, schedule.scale block) ≤
      ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum (system.selectedBlocks schedule seed hroom).length
          (quittingMarginalQuitHazard
            (system.selectedBlocks schedule seed hroom).flatRootNat owner) block := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro block _
    rw [consecutiveBlockSum]
    calc
      system.kappa * schedule.scale block ≤
          ∑ offset ∈ Finset.range
              (system.selectedPacket schedule seed hroom block).length,
            quittingMarginalQuitHazard
              (system.selectedPacket schedule seed hroom block).roots owner offset :=
        hpacket block
      _ = ∑ offset ∈ Finset.range
            ((system.selectedBlocks schedule seed hroom).length block),
          quittingMarginalQuitHazard
            (system.selectedBlocks schedule seed hroom).flatRootNat owner
            (consecutiveBlockStart
              (system.selectedBlocks schedule seed hroom).length block + offset) := by
        apply Finset.sum_congr rfl
        intro offset hoffset
        unfold quittingMarginalQuitHazard
          QuittingVariableLengthSeamBlocksNat.flatRootNat
        rw [consecutiveBlockIndex_start_add
            (system.selectedBlocks schedule seed hroom).length
            (system.selectedBlocks schedule seed hroom).length_pos block offset
            (Finset.mem_range.mp hoffset),
          consecutiveBlockOffset_start_add
            (system.selectedBlocks schedule seed hroom).length
            (system.selectedBlocks schedule seed hroom).length_pos block offset
            (Finset.mem_range.mp hoffset)]
        rfl
  rw [sum_consecutiveBlockSum_eq_sum_range] at hcompare
  have hprefix :
      (∑ time ∈ Finset.range
          (consecutiveBlockStart
            (system.selectedBlocks schedule seed hroom).length blocks),
          quittingMarginalQuitHazard
            (system.selectedBlocks schedule seed hroom).flatRootNat owner time) ≤
        ∑' time, quittingMarginalQuitHazard
          (system.selectedBlocks schedule seed hroom).flatRootNat owner time :=
    hsummable.sum_le_tsum _ fun time _ =>
      quittingMarginalQuitHazard_nonneg _ owner time
  have hscaled :
      (∑' time, quittingMarginalQuitHazard
        (system.selectedBlocks schedule seed hroom).flatRootNat owner time) <
        system.kappa *
          ∑ block ∈ Finset.range blocks, schedule.scale block := by
    simpa only [mul_comm] using (div_lt_iff₀ system.kappa_pos).mp hlarge
  linarith

/-- The two selected literal hazard streams both diverge. -/
theorem selectedBlocks_twoPersistent
    (hroom : cap + budget < system.radius seed) :
    HasTwoPersistentQuittingMarginals
      (system.selectedBlocks schedule seed hroom).flatRootNat := by
  refine ⟨system.first, system.second, system.labels_ne, ?_, ?_⟩
  · apply system.not_summable_flatHazard schedule seed hroom system.first
    intro block
    exact (system.selectedPacket schedule seed hroom block).first_hazard
  · apply system.not_summable_flatHazard schedule seed hroom system.second
    intro block
    exact (system.selectedPacket schedule seed hroom block).second_hazard

end Selection

/-! ## Summable-seam source and certificate -/

/-- A budgeted schedule and an explicit small-debt seed construct the full
summable-seam source. -/
theorem exists_summableSeamSource_of_seed
    (eta : ℝ) (heta : 0 < eta)
    (seed : system.Port)
    (hseed : ∀ who,
      quittingTerminalSemanticDebt (system.annotation seed) who ≤ eta) :
    Nonempty (QuittingSummableSeamSource reward eta) := by
  let budget := min eta (system.radius seed / 4)
  let cap := system.radius seed / 2
  have hbudget : 0 < budget := by
    change 0 < min eta (system.radius seed / 4)
    exact lt_min heta (div_pos (system.radius_pos seed) (by norm_num))
  have hcap : 0 < cap := by
    change 0 < system.radius seed / 2
    exact div_pos (system.radius_pos seed) (by norm_num)
  obtain ⟨schedule⟩ := exists_budgetedDivergentCostSchedule
    system.cost system.cost_nonneg system.cost_sublinear hbudget hcap
  have hroom : cap + budget < system.radius seed := by
    have hbudgetLe : budget ≤ system.radius seed / 4 := min_le_right _ _
    dsimp [cap]
    linarith [system.radius_pos seed]
  let blocks := system.selectedBlocks schedule seed hroom
  have hpersistent := system.selectedBlocks_twoPersistent
    schedule seed (hroom := hroom)
  have hcard : 2 ≤ Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨system.first, system.second, system.labels_ne⟩
  obtain ⟨hopponent, hjoint⟩ := hpersistent.survival hcard
  have hseamSummable : ∀ who,
      Summable (blocks.prescribedBlockSeamNat who) := by
    intro who
    exact Summable.of_nonneg_of_le (fun block => abs_nonneg _)
      (fun block => (system.selectedBlocks_prescribedSeam_le
        schedule seed who block (hroom := hroom)).trans (system.omega_le_cost _))
      schedule.cost_summable
  have htotalSummable : ∀ who,
      Summable (blocks.totalBlockSeamNat who) := by
    intro who
    exact Summable.of_nonneg_of_le
      (fun block => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (fun block => (system.selectedBlocks_totalSeam_le
        schedule seed who block (hroom := hroom)).trans (system.omega_le_cost _))
      schedule.cost_summable
  have hbudgetEta : budget ≤ eta := min_le_left _ _
  have hseamTsum : ∀ who,
      ∑' block, blocks.prescribedBlockSeamNat who block ≤ eta := by
    intro who
    calc
      (∑' block, blocks.prescribedBlockSeamNat who block) ≤
          ∑' block, system.cost (schedule.scale block) :=
        Summable.tsum_le_tsum
          (fun block => (system.selectedBlocks_prescribedSeam_le
            schedule seed who block (hroom := hroom)).trans (system.omega_le_cost _))
          (hseamSummable who) schedule.cost_summable
      _ ≤ budget := schedule.cost_tsum_le
      _ ≤ eta := hbudgetEta
  have htotalTsum : ∀ who,
      ∑' block, blocks.totalBlockSeamNat who block ≤ eta := by
    intro who
    calc
      (∑' block, blocks.totalBlockSeamNat who block) ≤
          ∑' block, system.cost (schedule.scale block) :=
        Summable.tsum_le_tsum
          (fun block => (system.selectedBlocks_totalSeam_le
            schedule seed who block (hroom := hroom)).trans (system.omega_le_cost _))
          (htotalSummable who) schedule.cost_summable
      _ ≤ budget := schedule.cost_tsum_le
      _ ≤ eta := hbudgetEta
  refine ⟨blocks.toSummableSeamSourceNat eta hseamSummable htotalSummable
    hseamTsum htotalTsum ?_ hjoint ?_⟩
  · intro who
    change quittingTerminalSemanticDebt
      ((system.selectedPacket schedule seed hroom 0).candidate 0) who ≤ eta
    rw [(system.selectedPacket schedule seed hroom 0).entrance_anchor,
      system.selectedPort_zero schedule seed (hroom := hroom)]
    exact hseed who
  · intro who start
    change Tendsto
      (quittingOpponentSurvivalWeight blocks.flatRootNat who start)
      atTop (nhds 0)
    exact hopponent who start

/-- The checked chronological certificate, still conditional on the explicit
small-debt seed. -/
theorem exists_chronologicalDebtShadowingCertificate_of_seed
    (eta : ℝ) (heta : 0 < eta)
    (seed : system.Port)
    (hseed : ∀ who,
      quittingTerminalSemanticDebt (system.annotation seed) who ≤ eta) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  obtain ⟨source⟩ := system.exists_summableSeamSource_of_seed eta heta seed hseed
  exact source.toChronologicalDebtShadowingCertificate heta

end QuittingBudgetStablePacketSystem

end GameTheory
