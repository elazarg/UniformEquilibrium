/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.MaximalCapSemanticPrefixReturn
import UniformEquilibrium.Quitting.Chronology.StrictCovectorRootStep

/-!
# Tail-normalized flow of a forward exact-cap ray

This module separates two layers which are easy to conflate.

* `QuittingForwardExactCapTail` is actual game data: a forward semantic orbit,
  exact cap--Nash roots, a summable positive hazard clock, and a limiting cap.
* `QuittingTailNormalizedCapFlow` is the selector-independent analytic layer.
  Its two first-order approximation hypotheses are stated literally.  From
  them it derives the renewal and limiting complementarity identities.

The module does not construct a terminal profile or a uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A forward exact-cap ray with a strictly positive summable marginal-hazard
clock.  The root selector is deliberately not part of this interface. -/
structure QuittingForwardExactCapTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  pair : ℕ → QuittingTerminalSemanticPair ι
  root : ℕ → ι → PMF Bool
  pair_mem : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward
  exactNash : ∀ time, IsεQuittingRootNash reward (pair time).2 0 (root time)
  forward : ∀ time,
    pair (time + 1) = quittingTerminalSemanticPrefix reward (root time) (pair time)
  absorption_summable : Summable (fun time ↦ quittingRootAbsorptionMass (root time))
  totalHazard_pos : ∀ time, 0 < ∑ who, quittingRootQuitRates (root time) who
  capLimit : Payoff ι
  cap_tendsto : ∀ who,
    Tendsto (fun time ↦ (pair time).2 who) atTop (nhds (capLimit who))
  singleton_le_capLimit : ∀ who,
    reward (quittingSingletonTerminal who) who ≤ capLimit who

namespace QuittingForwardExactCapTail

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Total marginal Quit hazard at one ray date. -/
def totalHazard (tail : QuittingForwardExactCapTail reward) (time : ℕ) : ℝ :=
  ∑ who, quittingRootQuitRates (tail.root time) who

/-- Current marginal-hazard direction. -/
def currentHazard (tail : QuittingForwardExactCapTail reward) (time : ℕ) : ι → ℝ :=
  quittingNormalizedQuitRates (tail.root time) (tail.totalHazard_pos time)

theorem totalHazard_nonneg (tail : QuittingForwardExactCapTail reward) (time : ℕ) :
    0 ≤ tail.totalHazard time :=
  (tail.totalHazard_pos time).le

theorem currentHazard_nonneg
    (tail : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    0 ≤ tail.currentHazard time who :=
  quittingNormalizedQuitRates_nonneg _ _ who

theorem sum_currentHazard
    (tail : QuittingForwardExactCapTail reward) (time : ℕ) :
    ∑ who, tail.currentHazard time who = 1 :=
  sum_quittingNormalizedQuitRates _ _

theorem quitRate_eq_totalHazard_mul_currentHazard
    (tail : QuittingForwardExactCapTail reward) (time : ℕ) (who : ι) :
    quittingRootQuitRates (tail.root time) who =
      tail.totalHazard time * tail.currentHazard time who :=
  quitRate_eq_sum_mul_normalizedQuitRate _ _ who

theorem totalHazard_summable (tail : QuittingForwardExactCapTail reward) :
    Summable tail.totalHazard := by
  unfold totalHazard
  apply summable_sum
  intro who _
  exact tail.absorption_summable.of_nonneg_of_le
    (fun time ↦ ENNReal.toReal_nonneg)
    (fun time ↦ quitProbability_le_quittingRootAbsorptionMass
      (tail.root time) who)

/-- Remaining marginal-hazard clock after a displayed ray date. -/
def tailMass (tail : QuittingForwardExactCapTail reward) (start : ℕ) : ℝ :=
  ∑' offset, tail.totalHazard (start + offset)

theorem tailMass_pos (tail : QuittingForwardExactCapTail reward) (start : ℕ) :
    0 < tail.tailMass start := by
  unfold tailMass
  have hshift : Summable (fun offset ↦ tail.totalHazard (start + offset)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff start).2 tail.totalHazard_summable
  have hle := hshift.le_tsum 0
    (fun offset _ ↦ tail.totalHazard_nonneg (start + offset))
  simpa using (lt_of_lt_of_le (tail.totalHazard_pos start) hle)

/-- Tail barycenter numerator of the marginal-hazard directions. -/
def tailFlow (tail : QuittingForwardExactCapTail reward)
    (start : ℕ) (who : ι) : ℝ :=
  ∑' offset, tail.totalHazard (start + offset) *
    tail.currentHazard (start + offset) who

theorem weightedCurrentHazard_summable
    (tail : QuittingForwardExactCapTail reward) (start : ℕ) (who : ι) :
    Summable (fun offset ↦ tail.totalHazard (start + offset) *
      tail.currentHazard (start + offset) who) := by
  have hshift : Summable (fun offset ↦ tail.totalHazard (start + offset)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff start).2 tail.totalHazard_summable
  apply hshift.of_nonneg_of_le
  · intro offset
    exact mul_nonneg (tail.totalHazard_nonneg _) (tail.currentHazard_nonneg _ who)
  · intro offset
    have hcoordinate : tail.currentHazard (start + offset) who ≤ 1 := by
      have hsingle := Finset.single_le_sum
        (fun player _ ↦ tail.currentHazard_nonneg (start + offset) player)
        (Finset.mem_univ who)
      simpa only [tail.sum_currentHazard] using hsingle
    exact (mul_le_mul_of_nonneg_left hcoordinate
      (tail.totalHazard_nonneg _)).trans_eq (mul_one _)

/-- Barycenter of all remaining marginal-hazard directions. -/
def tailAverage (tail : QuittingForwardExactCapTail reward)
    (start : ℕ) (who : ι) : ℝ :=
  tail.tailFlow start who / tail.tailMass start

/-- Present hazard as a fraction of the remaining marginal-hazard clock. -/
def renewalRatio (tail : QuittingForwardExactCapTail reward) (start : ℕ) : ℝ :=
  tail.totalHazard start / tail.tailMass start

theorem tailMass_eq_add_succ
    (tail : QuittingForwardExactCapTail reward) (start : ℕ) :
    tail.tailMass start = tail.totalHazard start + tail.tailMass (start + 1) := by
  unfold tailMass
  have hsum : Summable (fun offset ↦ tail.totalHazard (start + offset)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff start).2 tail.totalHazard_summable
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

theorem tailFlow_eq_add_succ
    (tail : QuittingForwardExactCapTail reward) (start : ℕ) (who : ι) :
    tail.tailFlow start who =
      tail.totalHazard start * tail.currentHazard start who +
        tail.tailFlow (start + 1) who := by
  unfold tailFlow
  have hsum := tail.weightedCurrentHazard_summable start who
  have hsplit := hsum.sum_add_tsum_nat_add 1
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

/-- Exact finite-level renewal identity for the remaining hazard barycenter. -/
theorem tailAverage_renewal
    (tail : QuittingForwardExactCapTail reward) (start : ℕ) (who : ι) :
    tail.tailAverage start who =
      tail.renewalRatio start * tail.currentHazard start who +
        (1 - tail.renewalRatio start) * tail.tailAverage (start + 1) who := by
  have hmass := tail.tailMass_eq_add_succ start
  have hflow := tail.tailFlow_eq_add_succ start who
  have hmassPos := tail.tailMass_pos start
  have hnextPos := tail.tailMass_pos (start + 1)
  have haddNe : tail.totalHazard start + tail.tailMass (start + 1) ≠ 0 := by
    rw [← hmass]
    exact hmassPos.ne'
  have hratio : 1 - tail.totalHazard start / tail.tailMass start =
      tail.tailMass (start + 1) / tail.tailMass start := by
    rw [hmass]
    field_simp [haddNe]
    ring
  unfold tailAverage renewalRatio
  rw [hratio, hflow]
  field_simp [hmassPos.ne', hnextPos.ne']

/-- Binding singleton face of the limiting cap. -/
def bindingFinset (tail : QuittingForwardExactCapTail reward) : Finset ι :=
  Finset.univ.filter fun who ↦
    tail.capLimit who = reward (quittingSingletonTerminal who) who

/-- Every sufficiently late positive current hazard is supported on the
binding singleton face of the limiting cap. -/
theorem eventually_currentHazard_supported_binding
    (tail : QuittingForwardExactCapTail reward) :
    ∀ᶠ time in atTop, ∀ who,
      0 < tail.currentHazard time who → who ∈ tail.bindingFinset := by
  have habsorption := tail.absorption_summable.tendsto_atTop_zero
  have hcoordinate : ∀ who, ∀ᶠ time in atTop,
      0 < tail.currentHazard time who →
        tail.capLimit who = reward (quittingSingletonTerminal who) who := by
    intro who
    by_cases hbinding : tail.capLimit who =
        reward (quittingSingletonTerminal who) who
    · exact Eventually.of_forall fun _ _ ↦ hbinding
    · have hstrict : reward (quittingSingletonTerminal who) who <
          tail.capLimit who :=
        lt_of_le_of_ne (tail.singleton_le_capLimit who) (Ne.symm hbinding)
      let gap := tail.capLimit who -
        reward (quittingSingletonTerminal who) who
      have hgap : 0 < gap := sub_pos.mpr hstrict
      have hcap : ∀ᶠ time in atTop,
          |(tail.pair (time + 1)).2 who - tail.capLimit who| < gap / 3 := by
        have hshift := (tail.cap_tendsto who).comp (tendsto_add_atTop_nat 1)
        have hsub := hshift.sub_const (tail.capLimit who)
        have habs : Tendsto (fun time ↦
            |(tail.pair (time + 1)).2 who - tail.capLimit who|) atTop
            (nhds 0) := by
          simpa only [Function.comp_apply, sub_self, abs_zero] using hsub.abs
        exact (tendsto_order.1 habs).2 (gap / 3) (by linarith)
      have habs : ∀ᶠ time in atTop,
          2 * quittingRewardBound reward *
              quittingRootAbsorptionMass (tail.root time) < gap / 3 := by
        have hscaled := habsorption.const_mul (2 * quittingRewardBound reward)
        exact (tendsto_order.1 hscaled).2 (gap / 3) (by linarith)
      filter_upwards [hcap, habs] with time hcapTime habsTime hactive
      have hquit : 0 < quittingRootQuitRates (tail.root time) who := by
        rw [tail.quitRate_eq_totalHazard_mul_currentHazard]
        exact mul_pos (tail.totalHazard_pos time) hactive
      have hnext : (tail.pair (time + 1)).2 =
          quittingRootSuccessorPayoff reward (tail.pair time).2
            (tail.root time) := by
        rw [tail.forward]
        exact quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
          (tail.pair time) (tail.root time) (tail.exactNash time)
      have hactiveEndpoint : (tail.pair (time + 1)).2 who =
          quittingRootQuitPayoff reward (tail.pair time).2
            (tail.root time) who := by
        rw [hnext]
        exact (quittingRootQuitPayoff_eq_successor_of_quitProbability_pos
          reward (tail.pair time).2 (tail.root time) who
            (tail.exactNash time) hquit).symm
      have hendpoint :=
        abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
          reward (tail.pair time).2 (tail.root time) who
            (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)
      have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass
        (tail.root time) who
      have hfactor : 0 ≤ 2 * quittingRewardBound reward :=
        mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
      have hendpoint' : |(tail.pair (time + 1)).2 who -
          reward (quittingSingletonTerminal who) who| < gap / 3 := by
        rw [hactiveEndpoint]
        exact (hendpoint.trans
          (mul_le_mul_of_nonneg_left hopponent hfactor)).trans_lt habsTime
      have htriangle := abs_sub_le (tail.capLimit who)
        ((tail.pair (time + 1)).2 who)
        (reward (quittingSingletonTerminal who) who)
      rw [abs_sub_comm (tail.capLimit who) ((tail.pair (time + 1)).2 who)]
        at htriangle
      dsimp only [gap] at hgap hcapTime hendpoint' htriangle
      rw [abs_of_pos hgap] at htriangle
      exfalso
      linarith
  filter_upwards [(eventually_all_finite Set.finite_univ).2
    (fun who _ ↦ hcoordinate who)] with time htime who hpositive
  simpa [bindingFinset] using htime who (Set.mem_univ who) hpositive

end QuittingForwardExactCapTail

/-- Selector-independent analytic hypotheses for tail-normalized cap flow.

`capFlowError` is the normalized first-order error in the forward cap
increment.  `collisionError` is the normalized first-order error in the
Quit-minus-Continue endpoint difference.  Both must tend to zero on the
binding face; no rate stronger than convergence is assumed. -/
structure QuittingTailNormalizedCapFlow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ray : QuittingForwardExactCapTail reward) where
  soloMatrix : ι → ι → ℝ
  collisionMatrix : ι → ι → ℝ
  endpointSlack : ℕ → ι → ℝ
  capFlowError : ℕ → ι → ℝ
  collisionError : ℕ → ι → ℝ
  cap_increment : ∀ time who,
    (ray.pair (time + 1)).2 who - (ray.pair time).2 who =
      ray.totalHazard time *
        ((∑ owner, soloMatrix who owner * ray.currentHazard time owner) +
          capFlowError time who)
  endpoint_decomposition : ∀ time who,
    ray.renewalRatio time * endpointSlack time who =
      -((ray.capLimit who - (ray.pair time).2 who) / ray.tailMass time) -
        ray.renewalRatio time *
          (∑ owner, collisionMatrix who owner * ray.currentHazard time owner) +
        collisionError time who
  endpointSlack_nonneg : ∀ time who, 0 ≤ endpointSlack time who
  current_complementarity : ∀ time who,
    ray.currentHazard time who * endpointSlack time who = 0
  capFlowError_tendsto_zero : ∀ who ∈ ray.bindingFinset,
    Tendsto (fun time ↦ capFlowError time who) atTop (nhds 0)
  collisionError_tendsto_zero : ∀ who ∈ ray.bindingFinset,
    Tendsto (fun time ↦ collisionError time who) atTop (nhds 0)
  tailNormalized_capFlow : ∀ who ∈ ray.bindingFinset,
    Tendsto (fun time ↦
      (ray.capLimit who - (ray.pair time).2 who) / ray.tailMass time -
        ∑ owner, soloMatrix who owner * ray.tailAverage time owner)
      atTop (nhds 0)

namespace QuittingTailNormalizedCapFlow

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {ray : QuittingForwardExactCapTail reward}

/-- Limiting collision inequality along any jointly convergent subsequence.
The current and tail hazard limits remain distinct. -/
theorem subseq_collision_nonpos
    (flow : QuittingTailNormalizedCapFlow reward ray)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (currentLimit tailLimit : ι → ℝ) (ratioLimit : ℝ)
    (hcurrent : ∀ who, Tendsto (fun rank ↦
      ray.currentHazard (subseq rank) who) atTop (nhds (currentLimit who)))
    (htail : ∀ who, Tendsto (fun rank ↦
      ray.tailAverage (subseq rank) who) atTop (nhds (tailLimit who)))
    (hratio : Tendsto (fun rank ↦ ray.renewalRatio (subseq rank))
      atTop (nhds ratioLimit))
    (who : ι) (hbinding : who ∈ ray.bindingFinset) :
    0 ≤ -(∑ owner, flow.soloMatrix who owner * tailLimit owner) -
      ratioLimit *
        ∑ owner, flow.collisionMatrix who owner * currentLimit owner := by
  have hcap : Tendsto (fun rank ↦
      (ray.capLimit who - (ray.pair (subseq rank)).2 who) /
          ray.tailMass (subseq rank) -
        ∑ owner, flow.soloMatrix who owner *
          ray.tailAverage (subseq rank) owner) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (flow.tailNormalized_capFlow who hbinding).comp hsubseq.tendsto_atTop
  have hmatrix : Tendsto (fun rank ↦
      ∑ owner, flow.soloMatrix who owner *
        ray.tailAverage (subseq rank) owner) atTop
      (nhds (∑ owner, flow.soloMatrix who owner * tailLimit owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact (tendsto_const_nhds : Tendsto
      (fun _rank : ℕ ↦ flow.soloMatrix who owner) atTop
        (nhds (flow.soloMatrix who owner))).mul (htail owner)
  have hcapLimit : Tendsto (fun rank ↦
      (ray.capLimit who - (ray.pair (subseq rank)).2 who) /
        ray.tailMass (subseq rank)) atTop
      (nhds (∑ owner, flow.soloMatrix who owner * tailLimit owner)) := by
    have hadd := hcap.add hmatrix
    convert hadd using 1 <;> simp
  have hcollision : Tendsto (fun rank ↦
      ∑ owner, flow.collisionMatrix who owner *
        ray.currentHazard (subseq rank) owner) atTop
      (nhds (∑ owner, flow.collisionMatrix who owner * currentLimit owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact (tendsto_const_nhds : Tendsto
      (fun _rank : ℕ ↦ flow.collisionMatrix who owner) atTop
        (nhds (flow.collisionMatrix who owner))).mul (hcurrent owner)
  have herror := (flow.collisionError_tendsto_zero who hbinding).comp
    hsubseq.tendsto_atTop
  have hdecomposition : Tendsto (fun rank ↦
      ray.renewalRatio (subseq rank) * flow.endpointSlack (subseq rank) who)
      atTop (nhds (-(∑ owner, flow.soloMatrix who owner * tailLimit owner) -
        ratioLimit *
          ∑ owner, flow.collisionMatrix who owner * currentLimit owner)) := by
    have hright := hcapLimit.neg.sub (hratio.mul hcollision) |>.add herror
    simpa only [Function.comp_apply, add_zero] using hright.congr'
      (Eventually.of_forall fun rank ↦
        (flow.endpoint_decomposition (subseq rank) who).symm)
  exact ge_of_tendsto hdecomposition
    (Eventually.of_forall fun rank ↦ mul_nonneg
      (div_nonneg (ray.totalHazard_nonneg _) (ray.tailMass_pos _).le)
      (flow.endpointSlack_nonneg _ _))

/-- Limiting complementary product. -/
theorem subseq_collision_complementarity
    (flow : QuittingTailNormalizedCapFlow reward ray)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (currentLimit tailLimit : ι → ℝ) (ratioLimit : ℝ)
    (hcurrent : ∀ who, Tendsto (fun rank ↦
      ray.currentHazard (subseq rank) who) atTop (nhds (currentLimit who)))
    (htail : ∀ who, Tendsto (fun rank ↦
      ray.tailAverage (subseq rank) who) atTop (nhds (tailLimit who)))
    (hratio : Tendsto (fun rank ↦ ray.renewalRatio (subseq rank))
      atTop (nhds ratioLimit))
    (who : ι) (hbinding : who ∈ ray.bindingFinset) :
    currentLimit who *
      ((∑ owner, flow.soloMatrix who owner * tailLimit owner) +
        ratioLimit *
          ∑ owner, flow.collisionMatrix who owner * currentLimit owner) = 0 := by
  have hcap : Tendsto (fun rank ↦
      (ray.capLimit who - (ray.pair (subseq rank)).2 who) /
          ray.tailMass (subseq rank) -
        ∑ owner, flow.soloMatrix who owner *
          ray.tailAverage (subseq rank) owner) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (flow.tailNormalized_capFlow who hbinding).comp hsubseq.tendsto_atTop
  have hmatrix : Tendsto (fun rank ↦
      ∑ owner, flow.soloMatrix who owner *
        ray.tailAverage (subseq rank) owner) atTop
      (nhds (∑ owner, flow.soloMatrix who owner * tailLimit owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact (tendsto_const_nhds : Tendsto
      (fun _rank : ℕ ↦ flow.soloMatrix who owner) atTop
        (nhds (flow.soloMatrix who owner))).mul (htail owner)
  have hcapLimit : Tendsto (fun rank ↦
      (ray.capLimit who - (ray.pair (subseq rank)).2 who) /
        ray.tailMass (subseq rank)) atTop
      (nhds (∑ owner, flow.soloMatrix who owner * tailLimit owner)) := by
    convert hcap.add hmatrix using 1 <;> simp
  have hcollision : Tendsto (fun rank ↦
      ∑ owner, flow.collisionMatrix who owner *
        ray.currentHazard (subseq rank) owner) atTop
      (nhds (∑ owner, flow.collisionMatrix who owner * currentLimit owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact (tendsto_const_nhds : Tendsto
      (fun _rank : ℕ ↦ flow.collisionMatrix who owner) atTop
        (nhds (flow.collisionMatrix who owner))).mul (hcurrent owner)
  have herror := (flow.collisionError_tendsto_zero who hbinding).comp
    hsubseq.tendsto_atTop
  have hslack : Tendsto (fun rank ↦
      ray.renewalRatio (subseq rank) * flow.endpointSlack (subseq rank) who)
      atTop (nhds (-(∑ owner, flow.soloMatrix who owner * tailLimit owner) -
        ratioLimit *
          ∑ owner, flow.collisionMatrix who owner * currentLimit owner)) := by
    have hright := hcapLimit.neg.sub (hratio.mul hcollision) |>.add herror
    simpa only [Function.comp_apply, add_zero] using hright.congr'
      (Eventually.of_forall fun rank ↦
        (flow.endpoint_decomposition (subseq rank) who).symm)
  have hzero : Tendsto (fun rank ↦
      ray.currentHazard (subseq rank) who *
        (ray.renewalRatio (subseq rank) *
          flow.endpointSlack (subseq rank) who)) atTop (nhds 0) := by
    have heq : (fun rank ↦ ray.currentHazard (subseq rank) who *
        (ray.renewalRatio (subseq rank) *
          flow.endpointSlack (subseq rank) who)) = fun _ ↦ 0 := by
      funext rank
      calc
        ray.currentHazard (subseq rank) who *
              (ray.renewalRatio (subseq rank) *
                flow.endpointSlack (subseq rank) who) =
            ray.renewalRatio (subseq rank) *
              (ray.currentHazard (subseq rank) who *
                flow.endpointSlack (subseq rank) who) := by ring
        _ = 0 := by rw [flow.current_complementarity, mul_zero]
    rw [heq]
    exact tendsto_const_nhds
  have hproduct := (hcurrent who).mul hslack
  have hunique := tendsto_nhds_unique hproduct hzero
  nlinarith

/-- In the diffuse case, positivity of the current limiting hazard on a
binding coordinate forces the homogeneous solo-flow equation there. -/
theorem subseq_diffuse_positiveCurrent_solo_eq_zero
    (flow : QuittingTailNormalizedCapFlow reward ray)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (currentLimit tailLimit : ι → ℝ) (ratioLimit : ℝ)
    (hcurrent : ∀ who, Tendsto (fun rank ↦
      ray.currentHazard (subseq rank) who) atTop (nhds (currentLimit who)))
    (htail : ∀ who, Tendsto (fun rank ↦
      ray.tailAverage (subseq rank) who) atTop (nhds (tailLimit who)))
    (hratio : Tendsto (fun rank ↦ ray.renewalRatio (subseq rank))
      atTop (nhds ratioLimit))
    (hratioZero : ratioLimit = 0)
    (who : ι) (hbinding : who ∈ ray.bindingFinset)
    (hcurrentPos : 0 < currentLimit who) :
    ∑ owner, flow.soloMatrix who owner * tailLimit owner = 0 := by
  have hcomplementarity := flow.subseq_collision_complementarity subseq
    hsubseq currentLimit tailLimit ratioLimit hcurrent htail hratio who hbinding
  rw [hratioZero, zero_mul, add_zero] at hcomplementarity
  exact (mul_eq_zero.mp hcomplementarity).resolve_left hcurrentPos.ne'

end QuittingTailNormalizedCapFlow

end GameTheory
