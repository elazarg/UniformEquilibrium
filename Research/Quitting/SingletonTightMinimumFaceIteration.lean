/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumPlateauPacket
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Fixed solo-prefix iteration at a singleton-tight minimum

This file checks fixed-row iteration on the singleton-tight,
unique-debtor face of the compact terminal-semantic carrier.  The finite
prefix iteration is valid.  Its limiting prescribed vector is the owner's
singleton reward vector, but the limiting finite-prefix envelope at the owner
retains the old tail cap.  Carrier-wide washout of arbitrary tails and global
minimality identify that cap exactly with the owner's behavioral punishment
value.  The actual stationary solo profile instead has owner cap
`max (solo reward) 0`; positive debt forces `solo < punishment ≤ 0`, so the two
semantic limits agree exactly when the punishment value is zero.  In a
counterexample regime, the whole singleton-tight positive-debt face enters
the established atomic-handoff or exact player-deletion alternatives.

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
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) : Prop where
  mem_carrier : pair ∈ quittingTerminalSemanticCarrier reward
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebtSum candidate
  debt_pos : 0 < quittingTerminalSemanticDebtSum pair
  owner_tight : pair.1 owner = quittingSoloReward reward owner owner
  outsider_debt : ∀ other, other ≠ owner →
    quittingTerminalSemanticDebt pair other = 0

theorem quittingSingletonTight_ownerDebt_eq_debtSum
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (hface : QuittingSingletonTightMinimumFace reward pair owner) :
    quittingTerminalSemanticDebt pair owner =
      quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  rw [Finset.sum_eq_single owner]
  · intro other _ hother
    exact hface.outsider_debt other hother
  · exact (by simp)

/-- The quantitative rate premise used in the fixed-row construction. -/
def QuittingSoloRateControlled
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (pair : QuittingTerminalSemanticPair ι) (rate : ℝ) : Prop :=
  0 < rate ∧ rate ≤ 1 ∧
    (∀ other, other ≠ owner →
      rate * (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other) ≤
        (1 - rate) * quittingTerminalSemanticDebtSum pair)

/-- Maximum positive collision-over-solo gain over the finite player set. -/
def quittingSingletonCollisionGainMax
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : ℝ :=
  letI : Nonempty ι := ⟨owner⟩
  QuittingBoundaryHolonomy.finitePlayerMax (fun other ↦
    if other = owner then 0 else
      max 0 (quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other))

/-- The finite maximum bound from the question implies the pointwise
controlled-rate premise used by the prefix construction. -/
theorem quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ} (hdebt : 0 < quittingTerminalSemanticDebtSum pair)
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hbound : rate ≤ quittingTerminalSemanticDebtSum pair /
      (quittingTerminalSemanticDebtSum pair +
        quittingSingletonCollisionGainMax reward owner)) :
    QuittingSoloRateControlled reward owner pair rate := by
  letI : Nonempty ι := ⟨owner⟩
  refine ⟨hrate0, hrate1, ?_⟩
  intro other hother
  have hgain : max 0 (quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other) ≤
      quittingSingletonCollisionGainMax reward owner := by
    dsimp [quittingSingletonCollisionGainMax]
    have hmax := QuittingBoundaryHolonomy.le_finitePlayerMax
      (fun player => if player = owner then 0 else
        max 0 (quittingSingletonCollisionReward reward owner player -
          quittingSoloReward reward owner player)) other
    simpa [hother] using hmax
  have hgain' : quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other ≤
      quittingSingletonCollisionGainMax reward owner :=
    (le_max_right _ _).trans hgain
  have hdenom : 0 < quittingTerminalSemanticDebtSum pair +
      quittingSingletonCollisionGainMax reward owner := by
    have hmaxnonneg : 0 ≤ quittingSingletonCollisionGainMax reward owner := by
      dsimp [quittingSingletonCollisionGainMax]
      exact le_trans (by simp) (QuittingBoundaryHolonomy.le_finitePlayerMax _ owner)
    linarith
  have hcross := (le_div_iff₀ hdenom).mp hbound
  have hgainMul := mul_le_mul_of_nonneg_left hgain' hrate0.le
  nlinarith

/-- The solo row is Nash against the prescribed coordinate, but its owner
has a strictly positive defect against the behavioral cap inherited from the tail.  That
cap defect is exactly the prescribed Quit mass times the minimum debt. -/
theorem quittingRootCoordinateNashDefect_solo_owner_cap_eq_rate_mul_debt
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    quittingRootCoordinateNashDefect reward pair.2
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)) owner =
      rate * quittingTerminalSemanticDebtSum pair := by
  let hazard := quittingHazardCoin rate hrate.1.le hrate.2.1
  let root := quittingSoloStationaryRoot owner hazard
  have hcap : pair.2 owner =
      quittingSoloReward reward owner owner +
        quittingTerminalSemanticDebtSum pair := by
    have hownerDebt := quittingSingletonTight_ownerDebt_eq_debtSum
      pair owner hface
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

/-- Exact account for one singleton-tight prefix.  The owner debt
is split between cap-Nash error at the root and survival-weighted debt in the
old tail; it is not contracted by an exact Nash--Bellman edge. -/
theorem singletonTight_owner_debt_eq_capDefect_add_liveTail
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    quittingTerminalSemanticDebtSum pair =
      quittingRootCoordinateNashDefect reward pair.2
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)) owner +
      quittingStationaryContinueMass
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)) *
          quittingTerminalSemanticDebtSum pair := by
  rw [quittingRootCoordinateNashDefect_solo_owner_cap_eq_rate_mul_debt
    pair owner hface hrate, quittingStationaryContinueMass_solo,
    quittingHazardCoin_false_toReal]
  ring

/-- After any finite number of repeated singleton prefixes, the accumulated
cap defects plus the surviving old-tail debt exhaust the original owner debt.
The last term is the finite-horizon phantom cap. -/
theorem singletonTight_owner_debt_eq_sum_capDefects_add_phantomTail
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    ∀ n : ℕ,
      quittingTerminalSemanticDebtSum pair =
        (∑ time ∈ Finset.range n,
          (1 - rate) ^ time *
            quittingRootCoordinateNashDefect reward pair.2
              (quittingSoloStationaryRoot owner
                (quittingHazardCoin rate hrate.1.le hrate.2.1)) owner) +
        (1 - rate) ^ n * quittingTerminalSemanticDebtSum pair := by
  intro n
  rw [quittingRootCoordinateNashDefect_solo_owner_cap_eq_rate_mul_debt
    pair owner hface hrate]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        quittingTerminalSemanticDebtSum pair =
            (∑ time ∈ Finset.range n,
              (1 - rate) ^ time *
                (rate * quittingTerminalSemanticDebtSum pair)) +
              (1 - rate) ^ n * quittingTerminalSemanticDebtSum pair := ih
        _ = (∑ time ∈ Finset.range n,
              (1 - rate) ^ time *
                (rate * quittingTerminalSemanticDebtSum pair)) +
            (1 - rate) ^ n * (rate * quittingTerminalSemanticDebtSum pair) +
            ((1 - rate) ^ n * (1 - rate)) *
              quittingTerminalSemanticDebtSum pair := by ring

/-- At a singleton-tight unique-debtor minimum, the controlled positive solo
rate is exact Nash against the displayed prescribed coordinate. -/
theorem isZeroQuittingRootNash_solo_of_singletonTightMinimumFace
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
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
      (reward := reward) pair hface.mem_carrier hface.minimum
        hface.debt_pos who
    have hzero := hface.outsider_debt who hwho
    have hcapEq : pair.2 who = pair.1 who := by
      unfold quittingTerminalSemanticDebt at hzero
      linarith
    have hclearance : quittingTerminalSemanticDebtSum pair ≤ pair.1 who -
        quittingSoloReward reward who who := by
      simpa [hcapEq, quittingSoloReward, quittingSingletonTerminal] using hmargin
    have hcollision := hrate.2.2 who hwho
    have hdiff : quittingRootEndpointDifference reward pair.1 root who ≤ 0 := by
      rw [quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloStationaryRoot_other reward hwho,
        quittingRootContinuePayoff_soloStationaryRoot_other reward hwho,
        show (hazard true).toReal = rate by
          simp [hazard],
        show (hazard false).toReal = 1 - rate by
          simp [hazard]]
      have hclearMul := mul_le_mul_of_nonneg_left hclearance
        (sub_nonneg.mpr hrate.2.1)
      linarith
    have hcontinue : (root who false).toReal = 1 := by
      simp [root, quittingSoloStationaryRoot, hwho]
    have hquit : (root who true).toReal = 0 := by
      simp [root, quittingSoloStationaryRoot, hwho]
    exact ⟨by rw [hcontinue, one_mul]; exact hdiff,
      by rw [hquit, zero_mul]; norm_num⟩

/-- The prefix preserves the total debt on the minimum face. -/
theorem quittingSingletonTightMinimumFace_prefix_debtSum_eq
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1)) pair) =
      quittingTerminalSemanticDebtSum pair := by
  let hazard := quittingHazardCoin rate hrate.1.le hrate.2.1
  let root := quittingSoloStationaryRoot owner hazard
  have hnash : IsεQuittingRootNash reward pair.1 0 root := by
    exact isZeroQuittingRootNash_solo_of_singletonTightMinimumFace
      pair owner hface hrate
  have hdebtEq : ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who =
        quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_prefix_eq_of_minimum
      reward pair root hface.mem_carrier hface.minimum hnash
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_congr rfl fun who _ => hdebtEq who

/-- Prefixing once by the controlled solo row preserves the entire
singleton-tight minimum face and every debt coordinate. -/
theorem quittingSingletonTightMinimumFace_prefix
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    let root := quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate.1.le hrate.2.1)
    QuittingSingletonTightMinimumFace reward
      (quittingTerminalSemanticPrefix reward root pair) owner := by
  let hazard := quittingHazardCoin rate hrate.1.le hrate.2.1
  let root := quittingSoloStationaryRoot owner hazard
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hnash : IsεQuittingRootNash reward pair.1 0 root := by
    exact isZeroQuittingRootNash_solo_of_singletonTightMinimumFace
      pair owner hface hrate
  have hmem : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier reward root pair
      hface.mem_carrier
  have hdebtEq : ∀ who,
      quittingTerminalSemanticDebt prefixed who =
        quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_prefix_eq_of_minimum
      reward pair root hface.mem_carrier hface.minimum hnash
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
    debt_pos := by
      calc
        0 < quittingTerminalSemanticDebtSum pair := hface.debt_pos
        _ = quittingTerminalSemanticDebtSum prefixed := hsumEq.symm
    owner_tight := hownerPrescribed
    outsider_debt := fun other hother =>
      (hdebtEq other).trans (hface.outsider_debt other hother) }
  intro candidate hcandidate
  rw [hsumEq]
  exact hface.minimum candidate hcandidate

/-- Every finite iterate of the fixed solo prefix stays on the same
singleton-tight minimum face. -/
theorem quittingSingletonTightMinimumFace_iterate
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    ∀ n,
      QuittingSingletonTightMinimumFace reward
        ((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1)))^[n] pair)
        owner := by
  let step := quittingTerminalSemanticPrefix reward
    (quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate.1.le hrate.2.1))
  have hresult : ∀ n, QuittingSingletonTightMinimumFace reward
      ((step^[n]) pair) owner ∧
      quittingTerminalSemanticDebtSum ((step^[n]) pair) =
        quittingTerminalSemanticDebtSum pair := by
    intro n
    induction n with
    | zero => exact ⟨hface, rfl⟩
    | succ n ih =>
        have hrate' : QuittingSoloRateControlled reward owner
            ((step^[n]) pair) rate := by
          refine ⟨hrate.1, hrate.2.1, ?_⟩
          intro other hother
          have hbase := hrate.2.2 other hother
          simpa only [ih.2] using hbase
        rw [Function.iterate_succ_apply']
        have hsumStep := quittingSingletonTightMinimumFace_prefix_debtSum_eq
          _ owner ih.1 hrate'
        exact ⟨quittingSingletonTightMinimumFace_prefix
            _ owner ih.1 hrate', hsumStep.trans ih.2⟩
  intro n
  exact (hresult n).1

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

/-- Limit of repeatedly prefixing an arbitrary semantic tail by one positive
solo row when every outsider's pure-Quit endpoint lies below the owner's
singleton payoff at that coordinate. -/
def quittingSingletonOwnerWashoutLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (quittingSoloReward reward owner,
    Function.update (quittingSoloReward reward owner) owner
      (max (quittingSoloReward reward owner owner) (pair.2 owner)))

/-- Repeated positive solo prefixing washes out every arbitrary tail whenever
each outsider's immediate Quit endpoint is no larger than the corresponding
owner-singleton payoff. -/
theorem tendsto_quittingSoloPrefix_iterate_of_outsiderEndpoint_le
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ} (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    Tendsto (fun n ↦
      (quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate0.le hrate1)))^[n] pair)
      atTop (nhds (quittingSingletonOwnerWashoutLimit reward owner pair)) := by
  let hazard := quittingHazardCoin rate hrate0.le hrate1
  let root := quittingSoloStationaryRoot owner hazard
  let step := quittingTerminalSemanticPrefix reward root
  have hprescribed : Tendsto (fun n ↦ ((step^[n]) pair).1)
      atTop (nhds (quittingSoloReward reward owner)) := by
    exact tendsto_quittingSoloPrefix_iterate_prescribed
      (reward := reward) pair owner hrate0 hrate1
  have hownerStep (candidate : QuittingTerminalSemanticPair ι) :
      (step candidate).2 owner =
        max (quittingSoloReward reward owner owner) (candidate.2 owner) := by
    change max
        (quittingRootQuitPayoff reward candidate.1 root owner)
        (quittingRootContinuePayoff reward
          (Function.update candidate.1 owner (candidate.2 owner)) root owner) = _
    rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
      quittingRootContinuePayoff_soloStationaryRoot_owner]
    simp
  have henvelope : Tendsto (fun n ↦ ((step^[n]) pair).2)
      atTop (nhds (Function.update (quittingSoloReward reward owner) owner
        (max (quittingSoloReward reward owner owner) (pair.2 owner)))) := by
    apply tendsto_pi_nhds.2
    intro who
    by_cases hwho : who = owner
    · subst who
      have howner : ∀ n,
          ((step^[Nat.succ n]) pair).2 owner =
            max (quittingSoloReward reward owner owner) (pair.2 owner) := by
        intro n
        induction n with
        | zero =>
            rw [Function.iterate_succ_apply']
            simpa using hownerStep pair
        | succ n ih =>
            rw [Function.iterate_succ_apply', hownerStep, ih]
            simp
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hn
      simpa [Nat.add_comm] using (howner offset).symm
    · let a := quittingSoloReward reward owner who
      let endpoint :=
        (1 - rate) * quittingSoloReward reward who who +
          rate * quittingSingletonCollisionReward reward owner who
      let ρ := 1 - rate
      have hρ0 : 0 ≤ ρ := by
        dsimp [ρ]
        linarith
      have hρ1 : ρ < 1 := by
        dsimp [ρ]
        linarith
      have hgamma : endpoint - a ≤ 0 := by
        exact sub_nonpos.mpr (hendpoint who hwho)
      have hstep (candidate : QuittingTerminalSemanticPair ι) :
          (step candidate).2 who - a =
            max (endpoint - a) (ρ * (candidate.2 who - a)) := by
        change max
            (quittingRootQuitPayoff reward candidate.1 root who)
            (quittingRootContinuePayoff reward
              (Function.update candidate.1 who (candidate.2 who)) root who) -
              a = _
        rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hwho,
          quittingRootContinuePayoff_soloStationaryRoot_other reward hwho]
        simp only [hazard, quittingHazardCoin_false_toReal,
          quittingHazardCoin_true_toReal, Function.update_self]
        rw [← max_sub_sub_right]
        congr 1
        dsimp [endpoint, a, ρ]
        ring
      have hgamma_le : ∀ n,
          endpoint - a ≤ ((step^[Nat.succ n]) pair).2 who - a := by
        intro n
        rw [Function.iterate_succ_apply', hstep]
        exact le_max_left _ _
      have hcontract : ∀ n,
          ((step^[Nat.succ (Nat.succ n)]) pair).2 who - a =
            ρ * (((step^[Nat.succ n]) pair).2 who - a) := by
        intro n
        rw [Function.iterate_succ_apply', hstep, max_eq_right]
        by_cases hy : 0 ≤ ((step^[Nat.succ n]) pair).2 who - a
        · exact hgamma.trans
            (mul_nonneg hρ0 hy)
        · have hyNonpos : ((step^[Nat.succ n]) pair).2 who - a ≤ 0 :=
            le_of_not_ge hy
          exact (hgamma_le n).trans <| calc
            ((step^[Nat.succ n]) pair).2 who - a =
                ρ * (((step^[Nat.succ n]) pair).2 who - a) +
                  rate * (((step^[Nat.succ n]) pair).2 who - a) := by
                    dsimp [ρ]
                    ring
            _ ≤ ρ * (((step^[Nat.succ n]) pair).2 who - a) :=
              add_le_of_nonpos_right
                (mul_nonpos_of_nonneg_of_nonpos hrate0.le hyNonpos)
      have hformula : ∀ n,
          ((step^[Nat.succ n]) pair).2 who - a =
            ρ ^ n * (((step^[1]) pair).2 who - a) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [hcontract n, ih, pow_succ]
            ring
      have hpow : Tendsto (fun n : ℕ ↦ ρ ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
      have hshifted : Tendsto (fun n ↦
          ((step^[Nat.succ n]) pair).2 who - a) atTop (nhds 0) := by
        convert hpow.mul_const (((step^[1]) pair).2 who - a) using 1
        · funext n
          exact hformula n
        · simp
      have hunshifted : Tendsto (fun n ↦
          ((step^[n]) pair).2 who - a) atTop (nhds 0) := by
        apply (tendsto_add_atTop_iff_nat 1).1
        simpa [Nat.add_comm] using hshifted
      have hcoordinate : Tendsto (fun n : ℕ ↦
          a + (((step^[n]) pair).2 who - a)) atTop (nhds (a + 0)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ a) atTop (nhds a)).add
          hunshifted
      simpa [a, Function.update_of_ne hwho] using hcoordinate
  change Tendsto (fun n ↦ (((step^[n]) pair).1, ((step^[n]) pair).2))
    atTop (nhds (quittingSingletonOwnerWashoutLimit reward owner pair))
  rw [quittingSingletonOwnerWashoutLimit, nhds_prod_eq]
  exact hprescribed.prodMk henvelope

/-- Under iteration of the singleton-tight minimum face, every outsider's
limiting owner-solo payoff clears its own singleton reward by the full minimum
debt. -/
theorem quittingSoloReward_sub_ownSolo_ge_debt_of_singletonTightIteration
    (pair : QuittingTerminalSemanticPair ι) (owner other : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate)
    (hother : other ≠ owner) :
    quittingTerminalSemanticDebtSum pair ≤
      quittingSoloReward reward owner other -
      quittingSoloReward reward other other := by
  let step := quittingTerminalSemanticPrefix reward
    (quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate.1.le hrate.2.1))
  have hfaces : ∀ n,
      QuittingSingletonTightMinimumFace reward ((step^[n]) pair) owner := by
    exact quittingSingletonTightMinimumFace_iterate
      pair owner hface hrate
  have hsums : ∀ n, quittingTerminalSemanticDebtSum ((step^[n]) pair) =
      quittingTerminalSemanticDebtSum pair := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hrate' : QuittingSoloRateControlled reward owner ((step^[n]) pair) rate := by
          refine ⟨hrate.1, hrate.2.1, ?_⟩
          intro who hwho
          rw [ih]
          exact hrate.2.2 who hwho
        rw [Function.iterate_succ_apply']
        exact (quittingSingletonTightMinimumFace_prefix_debtSum_eq
          _ owner (hfaces n) hrate').trans ih
  have hclearance : ∀ n,
      quittingTerminalSemanticDebtSum pair ≤ ((step^[n]) pair).1 other -
        quittingSoloReward reward other other := by
    intro n
    have hmargin := minimumTerminalSemantic_singletonMargin
      (reward := reward) ((step^[n]) pair)
        (hfaces n).mem_carrier (hfaces n).minimum
        (hfaces n).debt_pos other
    have hzero := (hfaces n).outsider_debt other hother
    have hcapEq : ((step^[n]) pair).2 other =
        ((step^[n]) pair).1 other := by
      unfold quittingTerminalSemanticDebt at hzero
      linarith
    rw [hcapEq] at hmargin
    rw [hsums n] at hmargin
    exact hmargin
  have htendsto : Tendsto (fun n =>
      ((step^[n]) pair).1 other - quittingSoloReward reward other other)
      atTop (𝓝 (quittingSoloReward reward owner other -
        quittingSoloReward reward other other)) := by
    have hprescribed := tendsto_quittingSoloPrefix_iterate_prescribed
      (reward := reward) pair owner hrate.1 hrate.2.1
    exact ((tendsto_pi_nhds.1 hprescribed) other).sub tendsto_const_nhds
  exact ge_of_tendsto htendsto (Filter.Eventually.of_forall hclearance)

/-- The controlled solo row clears every outsider's immediate Quit
endpoint after passing the minimum-face clearance to the limit. -/
theorem quittingControlledSolo_outsiderEndpoint_le_solo
    (pair : QuittingTerminalSemanticPair ι) (owner other : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate)
    (hother : other ≠ owner) :
    (1 - rate) * quittingSoloReward reward other other +
        rate * quittingSingletonCollisionReward reward owner other ≤
      quittingSoloReward reward owner other := by
  have hclearance :=
    quittingSoloReward_sub_ownSolo_ge_debt_of_singletonTightIteration
      pair owner other hface hrate hother
  have hcollision := hrate.2.2 other hother
  have hclearanceMul := mul_le_mul_of_nonneg_left hclearance
    (sub_nonneg.mpr hrate.2.1)
  linarith

/-- The face iteration converges directly to the carrier washout limit. -/
theorem tendsto_quittingSingletonTightMinimumFace_iterate
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    Tendsto (fun n =>
      (quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate.1.le hrate.2.1)))^[n] pair)
      atTop (𝓝 (quittingSingletonOwnerWashoutLimit reward owner pair)) := by
  apply tendsto_quittingSoloPrefix_iterate_of_outsiderEndpoint_le
    (reward := reward) pair owner hrate.1 hrate.2.1
  intro other hother
  exact quittingControlledSolo_outsiderEndpoint_le_solo
    pair owner other hface hrate hother

/-- Carrier invariance and closure turn arbitrary-tail solo washout into a
new point of the terminal-semantic carrier. -/
theorem quittingSingletonOwnerWashoutLimit_mem_carrier
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ} (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingSingletonOwnerWashoutLimit reward owner pair ∈
      quittingTerminalSemanticCarrier reward := by
  let root := quittingSoloStationaryRoot owner
    (quittingHazardCoin rate hrate0.le hrate1)
  let step := quittingTerminalSemanticPrefix reward root
  have htendsto :=
    tendsto_quittingSoloPrefix_iterate_of_outsiderEndpoint_le
      (reward := reward) pair owner hrate0 hrate1 hendpoint
  change Tendsto (fun n ↦ (step^[n]) pair) atTop
    (nhds (quittingSingletonOwnerWashoutLimit reward owner pair)) at htendsto
  have hiterates : ∀ n, (step^[n]) pair ∈
      quittingTerminalSemanticCarrier reward := by
    intro n
    induction n with
    | zero => simpa using hpair
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact quittingTerminalSemanticPrefix_mem_carrier reward root _ ih
  exact (quittingTerminalSemanticCarrier_isCompact reward).isClosed.mem_of_tendsto
    htendsto (Filter.Eventually.of_forall hiterates)

/-- A singleton-tight positive-debt minimum has the least owner envelope
coordinate on the entire terminal-semantic carrier.  The only rate premise
needed is outsider endpoint clearance for one positive solo row. -/
theorem singletonTight_ownerEnvelope_le_of_mem_carrier
    (minimum candidate : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward minimum owner)
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other)
    (hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward) :
    minimum.2 owner ≤ candidate.2 owner := by
  let washout := quittingSingletonOwnerWashoutLimit reward owner candidate
  have hwashout : washout ∈ quittingTerminalSemanticCarrier reward :=
    quittingSingletonOwnerWashoutLimit_mem_carrier
      (reward := reward) candidate owner hrate0 hrate1 hendpoint hcandidate
  have hsum : quittingTerminalSemanticDebtSum washout =
      max (quittingSoloReward reward owner owner) (candidate.2 owner) -
        quittingSoloReward reward owner owner := by
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.sum_eq_single owner]
    · simp [washout, quittingSingletonOwnerWashoutLimit,
        quittingTerminalSemanticDebt]
    · intro other _ hother
      simp [washout, quittingSingletonOwnerWashoutLimit,
        quittingTerminalSemanticDebt, hother]
    · intro howner
      exact (howner (Finset.mem_univ owner)).elim
  have hminimum := hface.minimum washout hwashout
  rw [hsum] at hminimum
  have hcandidateStrict : quittingSoloReward reward owner owner <
      candidate.2 owner := by
    by_contra hnot
    have hle : candidate.2 owner ≤
        quittingSoloReward reward owner owner := le_of_not_gt hnot
    rw [max_eq_left hle] at hminimum
    linarith [hface.debt_pos]
  have hownerCap : minimum.2 owner =
      quittingSoloReward reward owner owner +
        quittingTerminalSemanticDebtSum minimum := by
    have hdebt := quittingSingletonTight_ownerDebt_eq_debtSum
      minimum owner hface
    unfold quittingTerminalSemanticDebt at hdebt
    rw [hface.owner_tight] at hdebt
    linarith
  rw [max_eq_right hcandidateStrict.le] at hminimum
  rw [hownerCap]
  linarith

/-- The finite-prefix owner cap on a singleton-tight positive-debt face is exactly its
behavioral punishment value. -/
theorem singletonTight_ownerEnvelope_eq_punishmentValue
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    pair.2 owner = quittingPunishmentValue reward owner := by
  apply le_antisymm
  · unfold quittingPunishmentValue
    apply le_ciInf
    intro profile
    have hliteral : quittingTerminalSemanticPair reward profile ∈
        quittingTerminalSemanticCarrier reward :=
      subset_closure ⟨profile, rfl⟩
    have hle := singletonTight_ownerEnvelope_le_of_mem_carrier
      (reward := reward) pair (quittingTerminalSemanticPair reward profile)
        owner hface hrate0 hrate1 hendpoint hliteral
    simpa [quittingTerminalSemanticPair,
      quittingContinuationBestResponseValue, quittingBestReplyValue, iSup]
      using hle
  · exact quittingPunishmentValue_le_terminalSemanticEnvelope
      pair hface.mem_carrier owner

/-- The positive minimum debt is exactly the owner's punishment-value moat
above its singleton payoff. -/
theorem singletonTight_debt_eq_punishmentGap
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    quittingTerminalSemanticDebtSum pair = quittingPunishmentValue reward owner -
      quittingSoloReward reward owner owner := by
  have hcap := singletonTight_ownerEnvelope_eq_punishmentValue
    (reward := reward) pair owner hface hrate0 hrate1 hendpoint
  have howner := quittingSingletonTight_ownerDebt_eq_debtSum pair owner hface
  unfold quittingTerminalSemanticDebt at howner
  rw [hface.owner_tight, hcap] at howner
  linarith

/-- The punishment value on the singleton-tight positive-debt branch is
nonpositive; the owner's singleton payoff lies strictly below it. -/
theorem singletonTight_soloReward_lt_punishmentValue_and_nonpos
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner ∧
      quittingPunishmentValue reward owner ≤ 0 := by
  have hgap := singletonTight_debt_eq_punishmentGap
    (reward := reward) pair owner hface hrate0 hrate1 hendpoint
  have hstrict : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner := by
    linarith [hface.debt_pos]
  refine ⟨hstrict, ?_⟩
  have hceiling := quittingPunishmentValue_le_max_solo reward owner
  rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty reward
    (Finset.singleton_nonempty owner) owner] at hceiling
  change quittingPunishmentValue reward owner ≤
    max (quittingSoloReward reward owner owner) 0 at hceiling
  by_cases hsolo : quittingSoloReward reward owner owner ≤ 0
  · simpa [max_eq_right hsolo] using hceiling
  · have hsoloPos : 0 < quittingSoloReward reward owner owner :=
      lt_of_not_ge hsolo
    rw [max_eq_left hsoloPos.le] at hceiling
    linarith

/-- The actual stationary solo profile has the owner's singleton reward as
prescribed payoff and the exact arbitrary-behavior best-response caps stated
below.  Outsider endpoint clearance is the only game-specific premise; the
owner cap is `max solo 0`. -/
theorem quittingTerminalSemanticPair_stationarySolo_of_outsiderEndpoint_le
    (owner : ι) {rate : ℝ}
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
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
      exact hendpoint who hwho

/-- Specialization of the stationary semantic formula to the iterated
singleton-tight minimum face. -/
theorem quittingTerminalSemanticPair_stationarySolo_of_singletonTightIteration
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1))) =
      (quittingSoloReward reward owner,
        Function.update (quittingSoloReward reward owner) owner
          (max (quittingSoloReward reward owner owner) 0)) := by
  apply quittingTerminalSemanticPair_stationarySolo_of_outsiderEndpoint_le
    owner hrate.1 hrate.2.1
  intro other hother
  exact quittingControlledSolo_outsiderEndpoint_le_solo
    pair owner other hface hrate hother

/-- The stationary pair equals the washout limit exactly when the punishment
value vanishes. -/
theorem stationarySolo_eq_singletonOwnerWashoutLimit_iff_punishmentValue_eq_zero
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate.1.le hrate.2.1))) =
        quittingSingletonOwnerWashoutLimit reward owner pair ↔
      quittingPunishmentValue reward owner = 0 := by
  have hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other := by
    intro other hother
    exact quittingControlledSolo_outsiderEndpoint_le_solo
      pair owner other hface hrate hother
  rw [quittingTerminalSemanticPair_stationarySolo_of_outsiderEndpoint_le
    owner hrate.1 hrate.2.1 hendpoint]
  unfold quittingSingletonOwnerWashoutLimit
  have howner := quittingSingletonTight_ownerDebt_eq_debtSum pair owner hface
  unfold quittingTerminalSemanticDebt at howner
  rw [hface.owner_tight] at howner
  have hcap : pair.2 owner = quittingSoloReward reward owner owner +
      quittingTerminalSemanticDebtSum pair := by linarith
  have hsign := singletonTight_soloReward_lt_punishmentValue_and_nonpos
    (reward := reward) pair owner hface hrate.1 hrate.2.1 hendpoint
  have hsoloNonpos : quittingSoloReward reward owner owner ≤ 0 :=
    hsign.1.le.trans hsign.2
  rw [max_eq_right hsoloNonpos]
  have hgap := singletonTight_debt_eq_punishmentGap
    (reward := reward) pair owner hface hrate.1 hrate.2.1 hendpoint
  rw [hcap, max_eq_right (by linarith [hface.debt_pos]), hgap]
  constructor
  · intro heq
    have hcoord := congrFun (congrArg Prod.snd heq) owner
    simp at hcoord
    linarith
  · intro hpunish
    apply Prod.ext
    · rfl
    · funext who
      by_cases hwho : who = owner
      · subst who
        simp [hpunish]
      · simp [hwho]

/-- In a counterexample regime, a singleton-tight positive-debt minimum is
not a residual branch: it exposes either a strict atomic owner toggle with an
outsider deviation, or the same exploitability gap on a nonempty strictly
smaller player type. -/
theorem QuittingCounterexampleRegime.singletonTight_atomicHandoff_or_playerDeletion
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate0 : 0 < rate) (hrate1 : rate ≤ 1)
    (hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    (∃ (quitters : Finset ι) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward ⟨insert owner quitters,
              Finset.insert_nonempty owner quitters⟩ owner ∧
          ∃ who, who ≠ owner ∧ ∃ deviation : PMF Bool,
            quittingRootExpectedPayoff reward 0
                (Function.update
                  (QuittingSureSetOwnerRepair.quittingPureSetRoot
                    (insert owner quitters)) who deviation) who >
              quittingRootExpectedPayoff reward 0
                (QuittingSureSetOwnerRepair.quittingPureSetRoot
                  (insert owner quitters)) who) ∨
      (Nonempty (QuittingDeletedPlayer owner) ∧
        HasTerminalExploitabilityGap
          (quittingDeletePlayerReward reward owner) regime.terminalGap ∧
        Fintype.card (QuittingDeletedPlayer owner) < Fintype.card ι) := by
  have hsign := singletonTight_soloReward_lt_punishmentValue_and_nonpos
    (reward := reward) pair owner hface hrate0 hrate1 hendpoint
  have hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner := by
    simpa [quittingSoloReward, quittingSingletonTerminal] using hsign.1
  have hdispatch := exists_strict_owner_toggle_or_exact_playerDeletion
    reward owner regime.terminalGap_pos regime.terminalExploitability
      hsolo hsign.2
  exact strictToggle_or_playerDeletion_to_atomicHandoff
    reward regime.terminalGap_pos regime.terminalExploitability owner hdispatch

/-- Positive debt forces the owner's singleton reward below zero. -/
theorem singletonTight_soloReward_neg
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) {rate : ℝ}
    (hface : QuittingSingletonTightMinimumFace reward pair owner)
    (hrate : QuittingSoloRateControlled reward owner pair rate) :
    quittingSoloReward reward owner owner < 0 := by
  have hendpoint : ∀ other, other ≠ owner →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other := by
    intro other hother
    exact quittingControlledSolo_outsiderEndpoint_le_solo
      pair owner other hface hrate hother
  have hsign := singletonTight_soloReward_lt_punishmentValue_and_nonpos
    (reward := reward) pair owner hface hrate.1 hrate.2.1 hendpoint
  linarith

end GameTheory
