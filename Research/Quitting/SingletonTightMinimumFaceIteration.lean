/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumPlateauPacket
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Fixed solo-prefix iteration at a singleton-tight minimum

This file checks the proposed fixed-row iteration on the singleton-tight,
unique-debtor face of the compact terminal-semantic carrier.  The finite
prefix iteration is valid.  Its limiting prescribed vector is the owner's
singleton reward vector, but the limiting finite-prefix envelope at the owner
retains the old tail cap.  The actual stationary solo profile instead has
owner cap `max (solo reward) 0`.  Thus the two semantic limits agree exactly
when the retained owner cap is zero.

The stationary cap statements use the exact best-response theorem against
constant opponents, and therefore quantify over arbitrary behavioral
deviations rather than stationary deviations only.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The hypotheses defining the singleton-tight unique-debtor minimum face. -/
structure QuittingSingletonTightMinimumFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) (debt : ℝ) : Prop where
  mem_carrier : pair ∈ quittingTerminalSemanticCarrier reward
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebtSum candidate
  debt_pos : 0 < debt
  debt_sum : quittingTerminalSemanticDebtSum pair = debt
  owner_tight : pair.1 owner = quittingSoloReward reward owner owner
  owner_debt : quittingTerminalSemanticDebt pair owner = debt
  outsider_debt : ∀ other, other ≠ owner →
    quittingTerminalSemanticDebt pair other = 0

/-- The quantitative rate premise used in the fixed-row construction. -/
def QuittingSoloRateControlled
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (debt rate bound : ℝ) : Prop :=
  0 < rate ∧ rate ≤ 1 ∧ 0 ≤ bound ∧
    (∀ other, other ≠ owner →
      quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other ≤ bound) ∧
    rate * bound ≤ (1 - rate) * debt

/-- The solo row is Nash against the prescribed coordinate, but its owner
has a strictly positive defect against the retained behavioral cap.  That
cap defect is exactly the prescribed Quit mass times the minimum debt. -/
theorem quittingRootCoordinateNashDefect_solo_owner_cap_eq_rate_mul_debt
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    quittingRootCoordinateNashDefect reward pair.2
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)) owner =
      rate * debt := by
  let hazard := quittingHazardCoin rate hrate.1.le hrate.2.1
  let root := quittingSoloStationaryRoot owner hazard
  have hcap : pair.2 owner =
      quittingSoloReward reward owner owner + debt := by
    have hownerDebt := hface.owner_debt
    unfold quittingTerminalSemanticDebt at hownerDebt
    rw [hface.owner_tight] at hownerDebt
    linarith
  have hcapGe : quittingSoloReward reward owner owner ≤ pair.2 owner := by
    rw [hcap]
    exact le_add_of_nonneg_right hface.debt_pos.le
  change quittingRootCoordinateNashDefect reward pair.2 root owner = _
  rw [quittingRootCoordinateNashDefect,
    quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_soloStationaryRoot_owner,
    quittingRootContinuePayoff_soloStationaryRoot_owner,
    max_eq_right hcapGe]
  simp only [root, hazard, quittingSoloStationaryRoot_apply_owner,
    quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  rw [hcap]
  ring

/-- Exact Q188--Q191 account for one singleton-tight prefix.  The owner debt
is split between cap-Nash error at the root and survival-weighted debt in the
old tail; it is not contracted by an exact Nash--Bellman edge. -/
theorem singletonTight_owner_debt_eq_capDefect_add_liveTail
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    debt =
      quittingRootCoordinateNashDefect reward pair.2
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)) owner +
      quittingStationaryContinueMass
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)) * debt := by
  rw [quittingRootCoordinateNashDefect_solo_owner_cap_eq_rate_mul_debt
    pair owner hface hrate, quittingStationaryContinueMass_solo,
    quittingHazardCoin_false_toReal]
  ring

/-- After any finite number of repeated singleton prefixes, the accumulated
cap defects plus the surviving old-tail debt exhaust the original owner debt.
The last term is the finite-horizon phantom cap. -/
theorem singletonTight_owner_debt_eq_sum_capDefects_add_phantomTail
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    ∀ n : ℕ,
      debt =
        (∑ time ∈ Finset.range n,
          (1 - rate) ^ time *
            quittingRootCoordinateNashDefect reward pair.2
              (quittingSoloStationaryRoot owner
                (quittingHazardCoin rate hrate.1.le hrate.2.1)) owner) +
        (1 - rate) ^ n * debt := by
  intro n
  rw [quittingRootCoordinateNashDefect_solo_owner_cap_eq_rate_mul_debt
    pair owner hface hrate]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        debt =
            (∑ time ∈ Finset.range n,
              (1 - rate) ^ time * (rate * debt)) +
              (1 - rate) ^ n * debt := ih
        _ = (∑ time ∈ Finset.range n,
              (1 - rate) ^ time * (rate * debt)) +
            (1 - rate) ^ n * (rate * debt) +
            ((1 - rate) ^ n * (1 - rate)) * debt := by ring

/-- At a singleton-tight unique-debtor minimum, the controlled positive solo
rate is exact Nash against the displayed prescribed coordinate. -/
theorem isZeroQuittingRootNash_solo_of_singletonTightMinimumFace
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner
        (quittingHazardCoin rate hrate.1.le hrate.2.1)) := by
  let hazard := quittingHazardCoin rate hrate.1.le hrate.2.1
  let root := quittingSoloStationaryRoot owner hazard
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward pair.1 root).mp
  intro who
  by_cases hwho : who = owner
  · subst who
    have hdiff : quittingRootEndpointDifference reward pair.1 root owner = 0 := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner,
        hface.owner_tight]
      ring
    rw [hdiff]
    exact ⟨by simp, by simp⟩
  · have hmargin := minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hM hreward hface.mem_carrier hface.minimum
        (hface.debt_sum.symm ▸ hface.debt_pos) who
    have hzero := hface.outsider_debt who hwho
    have hcapEq : pair.2 who = pair.1 who := by
      unfold quittingTerminalSemanticDebt at hzero
      linarith
    have hclearance : debt ≤ pair.1 who -
        quittingSoloReward reward who who := by
      rw [hface.debt_sum] at hmargin
      simpa [hcapEq, quittingSoloReward, quittingSingletonTerminal] using hmargin
    have hcollision := hrate.2.2.2.1 who hwho
    have hdiff : quittingRootEndpointDifference reward pair.1 root who ≤ 0 := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloStationaryRoot_other reward hwho,
        quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        show (hazard true).toReal = rate by
          simp [hazard],
        show (hazard false).toReal = 1 - rate by
          simp [hazard]]
      have hbudget := hrate.2.2.2.2
      have hclearMul := mul_le_mul_of_nonneg_left hclearance
        (sub_nonneg.mpr hrate.2.1)
      have hcollisionMul := mul_le_mul_of_nonneg_left hcollision hrate.1.le
      linarith
    have hcontinue : (root who false).toReal = 1 := by
      simp [root, quittingSoloStationaryRoot, hwho]
    have hquit : (root who true).toReal = 0 := by
      simp [root, quittingSoloStationaryRoot, hwho]
    exact ⟨by rw [hcontinue, one_mul]; exact hdiff,
      by rw [hquit, zero_mul]; norm_num⟩

/-- Prefixing once by the controlled solo row preserves the entire
singleton-tight minimum face and every debt coordinate. -/
theorem quittingSingletonTightMinimumFace_prefix
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    let root := quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate.1.le hrate.2.1)
    QuittingSingletonTightMinimumFace reward
      (quittingTerminalSemanticPrefix reward root pair) owner debt := by
  let hazard := quittingHazardCoin rate hrate.1.le hrate.2.1
  let root := quittingSoloStationaryRoot owner hazard
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hnash : IsεQuittingRootNash reward pair.1 0 root := by
    exact isZeroQuittingRootNash_solo_of_singletonTightMinimumFace
      pair owner hM hreward hface hrate
  have hmem : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier reward root pair hM hreward
      hface.mem_carrier
  have hdebtEq : ∀ who,
      quittingTerminalSemanticDebt prefixed who =
        quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_prefix_eq_of_minimum
      reward pair root hM hreward hface.mem_carrier hface.minimum hnash
  have hsumEq : quittingTerminalSemanticDebtSum prefixed =
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_congr rfl fun who _ => hdebtEq who
  have hownerPrescribed : prefixed.1 owner =
      quittingSoloReward reward owner owner := by
    have hvalue := congrFun
      (quittingRootSuccessorPayoff_solo reward owner hazard pair.1) owner
    have hmass := quittingSoloHazardMass_add hazard
    change quittingRootSuccessorPayoff reward pair.1 root owner = _
    rw [hvalue, hface.owner_tight, ← add_mul, add_comm, hmass, one_mul]
  refine {
    mem_carrier := hmem
    minimum := ?_
    debt_pos := hface.debt_pos
    debt_sum := hsumEq.trans hface.debt_sum
    owner_tight := hownerPrescribed
    owner_debt := (hdebtEq owner).trans hface.owner_debt
    outsider_debt := fun other hother =>
      (hdebtEq other).trans (hface.outsider_debt other hother) }
  intro candidate hcandidate
  rw [hsumEq]
  exact hface.minimum candidate hcandidate

/-- Every finite iterate of the fixed solo prefix stays on the same
singleton-tight minimum face. -/
theorem quittingSingletonTightMinimumFace_iterate
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    ∀ n,
      QuittingSingletonTightMinimumFace reward
        ((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1)))^[n] pair)
        owner debt := by
  intro n
  induction n with
  | zero => simpa using hface
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact quittingSingletonTightMinimumFace_prefix
        _ owner hM hreward ih hrate

/-- The prescribed coordinate of the fixed-row iterates has the exact
geometric formula. -/
theorem quittingSoloPrefix_iterate_prescribed_apply
    (pair : QuittingTerminalSemanticPair ι) (owner who : ι)
    {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ∀ n,
      (((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0 hrate1)))^[n] pair).1 who) =
        quittingSoloReward reward owner who +
          (1 - rate) ^ n *
            (pair.1 who - quittingSoloReward reward owner who) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change quittingRootSuccessorPayoff reward
        (((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0 hrate1)))^[n] pair).1)
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate0 hrate1)) who = _
      rw [congrFun (quittingRootSuccessorPayoff_solo reward owner
        (quittingHazardCoin rate hrate0 hrate1) _) who,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal, ih]
      ring

/-- The prescribed coordinates of the fixed-row finite prefixes converge to
the owner's singleton reward vector. -/
theorem tendsto_quittingSoloPrefix_iterate_prescribed
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ} (hrate0 : 0 < rate) (hrate1 : rate ≤ 1) :
    Tendsto (fun n =>
      ((quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate0.le hrate1)))^[n] pair).1)
      atTop (𝓝 (quittingSoloReward reward owner)) := by
  apply tendsto_pi_nhds.2
  intro who
  have hbaseAbs : |1 - rate| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hrate1)]
    linarith
  have hpow : Tendsto (fun n : ℕ => (1 - rate) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbaseAbs
  have hscaled := hpow.mul_const
    (pair.1 who - quittingSoloReward reward owner who)
  convert (tendsto_const_nhds.add hscaled) using 1
  · funext n
    exact quittingSoloPrefix_iterate_prescribed_apply
      (reward := reward) pair owner who hrate0.le hrate1 n
  · simp

/-- The finite-prefix limit keeps the old owner cap and clears every outsider
cap together with its prescribed coordinate. -/
def quittingSingletonTightIterationLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (debt : ℝ) : QuittingTerminalSemanticPair ι :=
  (quittingSoloReward reward owner,
    Function.update (quittingSoloReward reward owner) owner
      (quittingSoloReward reward owner owner + debt))

/-- The whole semantic pair of the fixed finite-prefix iterates converges to
the retained-tail limit, not automatically to the stationary solo pair. -/
theorem tendsto_quittingSingletonTightMinimumFace_iterate
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    Tendsto (fun n =>
      (quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)))^[n] pair)
      atTop (𝓝 (quittingSingletonTightIterationLimit reward owner debt)) := by
  let step := quittingTerminalSemanticPrefix reward
    (quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate.1.le hrate.2.1))
  have hfaces : ∀ n,
      QuittingSingletonTightMinimumFace reward ((step^[n]) pair) owner debt :=
    quittingSingletonTightMinimumFace_iterate
      pair owner hM hreward hface hrate
  have hprescribed : Tendsto (fun n => ((step^[n]) pair).1)
      atTop (𝓝 (quittingSoloReward reward owner)) :=
    tendsto_quittingSoloPrefix_iterate_prescribed
      (reward := reward) pair owner hrate.1 hrate.2.1
  have henvelope : Tendsto (fun n => ((step^[n]) pair).2)
      atTop (𝓝 (Function.update (quittingSoloReward reward owner) owner
        (quittingSoloReward reward owner owner + debt))) := by
    apply tendsto_pi_nhds.2
    intro who
    by_cases hwho : who = owner
    · subst who
      have heq : ∀ n, ((step^[n]) pair).2 owner =
          quittingSoloReward reward owner owner + debt := by
        intro n
        have htight := (hfaces n).owner_tight
        have hdebt := (hfaces n).owner_debt
        unfold quittingTerminalSemanticDebt at hdebt
        linarith
      simpa only [Function.update_self, heq] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
          quittingSoloReward reward owner owner + debt) atTop
          (𝓝 (quittingSoloReward reward owner owner + debt)))
    · have heq : ∀ n, ((step^[n]) pair).2 who = ((step^[n]) pair).1 who := by
        intro n
        have hzero := (hfaces n).outsider_debt who hwho
        unfold quittingTerminalSemanticDebt at hzero
        linarith
      have hcoordinate := (tendsto_pi_nhds.1 hprescribed) who
      simpa only [Function.update_of_ne hwho, heq] using hcoordinate
  change Tendsto (fun n => (((step^[n]) pair).1, ((step^[n]) pair).2))
    atTop (𝓝 (quittingSingletonTightIterationLimit reward owner debt))
  rw [quittingSingletonTightIterationLimit, nhds_prod_eq]
  exact hprescribed.prodMk henvelope

/-- Under iteration of the singleton-tight minimum face, every outsider's
limiting owner-solo payoff clears its own singleton reward by the full minimum
debt. -/
theorem quittingSoloReward_sub_ownSolo_ge_debt_of_singletonTightIteration
    (pair : QuittingTerminalSemanticPair ι) (owner other : ι)
    {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound)
    (hother : other ≠ owner) :
    debt ≤ quittingSoloReward reward owner other -
      quittingSoloReward reward other other := by
  let step := quittingTerminalSemanticPrefix reward
    (quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate.1.le hrate.2.1))
  have hfaces : ∀ n,
      QuittingSingletonTightMinimumFace reward ((step^[n]) pair) owner debt := by
    exact quittingSingletonTightMinimumFace_iterate
      pair owner hM hreward hface hrate
  have hclearance : ∀ n,
      debt ≤ ((step^[n]) pair).1 other -
        quittingSoloReward reward other other := by
    intro n
    have hmargin := minimumTerminalSemantic_singletonMargin
      (reward := reward) ((step^[n]) pair) hM hreward
        (hfaces n).mem_carrier (hfaces n).minimum
        ((hfaces n).debt_sum.symm ▸ (hfaces n).debt_pos) other
    have hzero := (hfaces n).outsider_debt other hother
    have hcapEq : ((step^[n]) pair).2 other =
        ((step^[n]) pair).1 other := by
      unfold quittingTerminalSemanticDebt at hzero
      linarith
    rw [(hfaces n).debt_sum, hcapEq] at hmargin
    exact hmargin
  have htendsto : Tendsto (fun n =>
      ((step^[n]) pair).1 other - quittingSoloReward reward other other)
      atTop (𝓝 (quittingSoloReward reward owner other -
        quittingSoloReward reward other other)) := by
    have hprescribed := tendsto_quittingSoloPrefix_iterate_prescribed
      (reward := reward) pair owner hrate.1 hrate.2.1
    exact ((tendsto_pi_nhds.1 hprescribed) other).sub tendsto_const_nhds
  exact ge_of_tendsto htendsto (Filter.Eventually.of_forall hclearance)

/-- The actual stationary solo profile has the owner's singleton reward as
prescribed payoff and the exact arbitrary-behavior best-response caps stated
below.  Under the limiting outsider clearance, all outsider caps equal their
prescribed payoffs; the owner cap is `max solo 0`. -/
theorem quittingTerminalSemanticPair_stationarySolo_of_limitingClearance
    (owner : ι) {rate debt : ℝ}
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hclearance : ∀ other, other ≠ owner →
      debt ≤ quittingSoloReward reward owner other -
        quittingSoloReward reward other other)
    (hcollision : ∀ other, other ≠ owner →
      quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other ≤
        ((1 - rate) / rate) * debt) :
    quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0.le hrate1))) =
      (quittingSoloReward reward owner,
        Function.update (quittingSoloReward reward owner) owner
          (max (quittingSoloReward reward owner owner) 0)) := by
  let hazard := quittingHazardCoin rate hrate0.le hrate1
  let root := quittingSoloStationaryRoot owner hazard
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_soloStationary reward owner who hazard
      (by simp [hazard, hrate0])
  · funext who
    change quittingContinuationBestResponseValue reward
      (quittingStationaryProfile reward root) who = _
    rw [show quittingContinuationBestResponseValue reward
          (quittingStationaryProfile reward root) who =
        quittingBestReplyValue reward
          (quittingStationaryProfile reward root) who by rfl,
      quittingBestReplyValue_stationary]
    by_cases hwho : who = owner
    · subst who
      simp [root, hazard]
    · rw [quittingStationaryUnilateralCap_solo_other reward hwho hazard
        (by simp [hazard, hrate0]),
        quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
          reward hwho hazard]
      simp only [hazard, quittingHazardCoin_false_toReal,
        quittingHazardCoin_true_toReal]
      rw [Function.update_of_ne hwho]
      apply max_eq_right
      have hc := hcollision who hwho
      have hs := hclearance who hwho
      have hrateNonzero : rate ≠ 0 := ne_of_gt hrate0
      have hrateNonneg : 0 ≤ rate := hrate0.le
      have hcMul : rate *
          (quittingSingletonCollisionReward reward owner who -
            quittingSoloReward reward owner who) ≤
          (1 - rate) * debt := by
        calc
          _ ≤ rate * (((1 - rate) / rate) * debt) :=
            mul_le_mul_of_nonneg_left hc hrateNonneg
          _ = _ := by field_simp [hrateNonzero]
      have hsMul := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hrate1)
      linarith

/-- Specialization of the stationary semantic formula to the iterated
singleton-tight minimum face. -/
theorem quittingTerminalSemanticPair_stationarySolo_of_singletonTightIteration
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1))) =
      (quittingSoloReward reward owner,
        Function.update (quittingSoloReward reward owner) owner
          (max (quittingSoloReward reward owner owner) 0)) := by
  have hclearance : ∀ other, other ≠ owner →
      debt ≤ quittingSoloReward reward owner other -
        quittingSoloReward reward other other := by
    intro other hother
    exact quittingSoloReward_sub_ownSolo_ge_debt_of_singletonTightIteration
      pair owner other hM hreward hface hrate hother
  have hcollision : ∀ other, other ≠ owner →
      quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other ≤
        ((1 - rate) / rate) * debt := by
    intro other hother
    have hc := hrate.2.2.2.1 other hother
    have hb := hrate.2.2.2.2
    apply hc.trans
    calc
      bound ≤ ((1 - rate) * debt) / rate :=
        (le_div_iff₀ hrate.1).2 (by nlinarith)
      _ = ((1 - rate) / rate) * debt := by
        field_simp [ne_of_gt hrate.1]
  exact quittingTerminalSemanticPair_stationarySolo_of_limitingClearance
    owner hrate.1 hrate.2.1 hclearance hcollision

/-- The finite-prefix semantic limit agrees with the actual stationary solo
semantic pair exactly when the retained owner cap equals the stationary
Quit-versus-Never cap. -/
theorem stationarySolo_eq_singletonTightIterationLimit_iff
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound) :
    quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1))) =
        quittingSingletonTightIterationLimit reward owner debt ↔
      max (quittingSoloReward reward owner owner) 0 =
        quittingSoloReward reward owner owner + debt := by
  rw [quittingTerminalSemanticPair_stationarySolo_of_singletonTightIteration
    pair owner hM hreward hface hrate]
  constructor
  · intro heq
    have hcoord := congrFun (congrArg Prod.snd heq) owner
    simpa [quittingSingletonTightIterationLimit] using hcoord
  · intro heq
    apply Prod.ext
    · rfl
    · funext who
      by_cases hwho : who = owner
      · subst who
        simpa [quittingSingletonTightIterationLimit] using heq
      · simp [quittingSingletonTightIterationLimit, hwho]

/-- If the owner's singleton reward is nonnegative, the limiting clearance
makes the stationary solo profile an exact uniform-equilibrium producer. -/
theorem isUniformEquilibriumPayoff_solo_of_singletonTightIteration
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {debt rate bound M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hface : QuittingSingletonTightMinimumFace reward pair owner debt)
    (hrate : QuittingSoloRateControlled reward owner debt rate bound)
    (hownerNonneg : 0 ≤ quittingSoloReward reward owner owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hclearance : ∀ other, other ≠ owner →
      debt ≤ quittingSoloReward reward owner other -
        quittingSoloReward reward other other := by
    intro other hother
    exact quittingSoloReward_sub_ownSolo_ge_debt_of_singletonTightIteration
      pair owner other hM hreward hface hrate hother
  apply isUniformEquilibriumPayoff_soloReward_of_inactive reward owner
    (quittingHazardCoin rate hrate.1.le hrate.2.1)
  · simp [hrate.1]
  · exact hownerNonneg
  · intro other hother
    have hs := hclearance other hother
    have hc := hrate.2.2.2.1 other hother
    have hb := hrate.2.2.2.2
    simp only [quittingHazardCoin_false_toReal,
      quittingHazardCoin_true_toReal]
    have hsMul := mul_le_mul_of_nonneg_left hs
      (sub_nonneg.mpr hrate.2.1)
    have hcMul := mul_le_mul_of_nonneg_left hc hrate.1.le
    linarith

end GameTheory
