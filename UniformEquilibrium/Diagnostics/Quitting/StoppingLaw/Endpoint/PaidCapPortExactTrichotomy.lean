/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapLiftedSummablePort
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixAdmissiblePath
import UniformEquilibrium.Quitting.Projective.CumulativeChargeNearReturn

/-!
# Exact paid cap-port trichotomy

A paid cap-lifted source has finite total absorption.  If the limiting cap
returns to the initial cap with positive total absorption, finite literal
prefixes give cumulative-charge admissible payoff near-returns.  A nonzero
cap displacement instead pays a quantitative drop in total semantic debt.
The only remaining case is zero total absorption: every selected root is
literally all Continue and the original paid row shifts through every prefix
without loss.

The inert branch is only a boundary for this actual paid cap lift.  It is not
asserted to arise from every positive-minimum frontier or from a terminal
exploitability witness.  The quantitative branch is a real-valued decrease,
not a well-founded recursive rank.  The cap annotations are behavioral
best-response envelopes, not prescribed payoffs, and the shifted paid row is
not promoted here to a prescribed-payoff Nash--Bellman edge.  No infinite
behavior profile or multiplication of outer absorption by suffix paid gain is
constructed.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open QuittingPunishmentFloorInfiniteOrbit

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingPaidCapLiftedSource

variable (source : QuittingPaidCapLiftedSource reward)

/-- Total absorption charge of the literal cap-lifted prefix chronology. -/
def totalAbsorption : ℝ :=
  ∑' time, quittingRootAbsorptionMass
    (quittingCapLiftedPrefixRoot reward
      (quittingCapLiftedPrefixProfile reward source.profile time))

theorem totalAbsorption_nonneg : 0 ≤ source.totalAbsorption := by
  exact tsum_nonneg fun time ↦ quittingRootAbsorptionMass_nonneg _

/-- Sup-norm displacement between the initial cap and the semantic-port cap
limit. -/
def capDisplacement (port : source.SummablePort) : ℝ :=
  dist port.semanticPort.limit.2
    (quittingTerminalSemanticPair reward source.profile).2

theorem capDisplacement_nonneg (port : source.SummablePort) :
    0 ≤ source.capDisplacement port := dist_nonneg

/-- The checked finite debt budget passes to the complete absorption sum. -/
theorem minimum_mul_totalAbsorption_le_debtDrop
    (port : source.SummablePort) :
    quittingTerminalSemanticDebtSum source.minimum * source.totalAbsorption ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum port.semanticPort.limit := by
  let absorption : ℕ → ℝ := fun time ↦
    quittingRootAbsorptionMass
      (quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time))
  have hpartial : ∀ horizon,
      quittingTerminalSemanticDebtSum source.minimum *
            ∑ time ∈ Finset.range horizon, absorption time ≤
        source.initialDebt -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingCapLiftedPrefixProfile reward source.profile horizon)) := by
    intro horizon
    exact source.minimum_mul_partialAbsorption_le_debtDrop horizon
  have hsum : Tendsto (fun horizon ↦
      ∑ time ∈ Finset.range horizon, absorption time) atTop
      (nhds source.totalAbsorption) := by
    simpa [absorption, totalAbsorption] using
      source.absorption_summable.hasSum.tendsto_sum_nat
  have hleft : Tendsto (fun horizon ↦
      quittingTerminalSemanticDebtSum source.minimum *
        ∑ time ∈ Finset.range horizon, absorption time) atTop
      (nhds (quittingTerminalSemanticDebtSum source.minimum *
        source.totalAbsorption)) :=
    hsum.const_mul _
  have hdebt : Tendsto (fun horizon ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)))
      atTop
      (nhds (quittingTerminalSemanticDebtSum port.semanticPort.limit)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      port.semanticPort.semantic_tendsto
  have hright : Tendsto (fun horizon ↦ source.initialDebt -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)))
      atTop
      (nhds (source.initialDebt -
        quittingTerminalSemanticDebtSum port.semanticPort.limit)) :=
    tendsto_const_nhds.sub hdebt
  exact le_of_tendsto_of_tendsto' hleft hright hpartial

private theorem abs_cap_displacement_coordinate_le
    (port : source.SummablePort) (who : iota) :
    |port.semanticPort.limit.2 who -
        (quittingTerminalSemanticPair reward source.profile).2 who| ≤
      2 * quittingRewardBound reward * source.totalAbsorption := by
  let orbit := quittingCapLiftedPunishmentFloorOrbit reward source.profile
  let absorption : ℕ → ℝ := fun time ↦
    quittingRootAbsorptionMass (orbit.roots time)
  have hfinite : ∀ horizon,
      |orbit.value horizon who - orbit.value 0 who| ≤
        2 * quittingRewardBound reward *
          ∑ time ∈ Finset.range horizon, absorption time := by
    intro horizon
    have htelescope : orbit.value horizon who - orbit.value 0 who =
        ∑ time ∈ Finset.range horizon,
          (orbit.value (time + 1) who - orbit.value time who) := by
      induction horizon with
      | zero => simp
      | succ horizon ih =>
          rw [Finset.sum_range_succ, ← ih]
          ring
    rw [htelescope]
    calc
      |∑ time ∈ Finset.range horizon,
          (orbit.value (time + 1) who - orbit.value time who)| ≤
          ∑ time ∈ Finset.range horizon,
            |orbit.value (time + 1) who - orbit.value time who| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ time ∈ Finset.range horizon,
          2 * quittingRewardBound reward * absorption time := by
            apply Finset.sum_le_sum
            intro time _
            exact orbit.abs_value_succ_sub_le_two_mul_absorptionMass
              time who
      _ = 2 * quittingRewardBound reward *
          ∑ time ∈ Finset.range horizon, absorption time := by
            rw [Finset.mul_sum]
  have hvalue : Tendsto (fun horizon ↦
      |orbit.value horizon who - orbit.value 0 who|) atTop
      (nhds |port.semanticPort.limit.2 who -
        (quittingTerminalSemanticPair reward source.profile).2 who|) := by
    have hraw := (port.semanticPort.capPort.value_tendsto who).sub_const
      (orbit.value 0 who)
    have habs := hraw.abs
    simpa [orbit, quittingCapLiftedPunishmentFloorOrbit,
      port.semanticPort.envelope_eq] using habs
  have hsum : Tendsto (fun horizon ↦
      ∑ time ∈ Finset.range horizon, absorption time) atTop
      (nhds source.totalAbsorption) := by
    simpa [orbit, absorption, totalAbsorption,
      quittingCapLiftedPunishmentFloorOrbit] using
      source.absorption_summable.hasSum.tendsto_sum_nat
  have hbound := hsum.const_mul (2 * quittingRewardBound reward)
  exact le_of_tendsto_of_tendsto' hvalue hbound hfinite

/-- Total cap displacement is bounded by twice the reward bound times the
complete absorption charge. -/
theorem capDisplacement_le_two_mul_totalAbsorption
    (port : source.SummablePort) :
    source.capDisplacement port ≤
      2 * quittingRewardBound reward * source.totalAbsorption := by
  have hbound : 0 ≤
      2 * quittingRewardBound reward * source.totalAbsorption :=
    mul_nonneg (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward))
      source.totalAbsorption_nonneg
  rw [capDisplacement, dist_pi_le_iff hbound]
  intro who
  simpa [Real.dist_eq] using source.abs_cap_displacement_coordinate_le port who

/-- A positive cap displacement forces a quantitatively fixed total-debt
drop, with the sharp factor supplied by the two-reward-bound motion estimate. -/
theorem minimum_mul_capDisplacement_div_twoRewardBound_le_debtDrop
    (port : source.SummablePort)
    (hdisplacement : 0 < source.capDisplacement port) :
    quittingTerminalSemanticDebtSum source.minimum *
          (source.capDisplacement port / (2 * quittingRewardBound reward)) ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum port.semanticPort.limit := by
  have hreward : 0 < quittingRewardBound reward := by
    have hbound := source.capDisplacement_le_two_mul_totalAbsorption port
    have habsorption := source.totalAbsorption_nonneg
    have hrewardNonneg := quittingRewardBound_nonneg reward
    nlinarith
  have hratio : source.capDisplacement port /
        (2 * quittingRewardBound reward) ≤ source.totalAbsorption := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hreward)).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      source.capDisplacement_le_two_mul_totalAbsorption port
  exact (mul_le_mul_of_nonneg_left hratio source.minimum_pos.le).trans
    (source.minimum_mul_totalAbsorption_le_debtDrop port)

/-- The quantitative displacement branch, including its strict decrease and
the uniform estimate on every fixed positive displacement slice. -/
structure QuantitativeDebtDescent (port : source.SummablePort) : Prop where
  displacement_pos : 0 < source.capDisplacement port
  rewardBound_pos : 0 < quittingRewardBound reward
  displacement_le_two_mul_totalAbsorption :
    source.capDisplacement port ≤
      2 * quittingRewardBound reward * source.totalAbsorption
  scaledDisplacement_le_scaledAbsorption :
    quittingTerminalSemanticDebtSum source.minimum *
          (source.capDisplacement port / (2 * quittingRewardBound reward)) ≤
      quittingTerminalSemanticDebtSum source.minimum * source.totalAbsorption
  absorption_charge :
    quittingTerminalSemanticDebtSum source.minimum * source.totalAbsorption ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum port.semanticPort.limit
  displacement_charge :
    quittingTerminalSemanticDebtSum source.minimum *
          (source.capDisplacement port / (2 * quittingRewardBound reward)) ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum port.semanticPort.limit
  debtDrop_pos : 0 < source.initialDebt -
    quittingTerminalSemanticDebtSum port.semanticPort.limit
  slice_charge : ∀ eta : ℝ, 0 < eta → eta ≤ source.capDisplacement port →
    quittingTerminalSemanticDebtSum source.minimum *
          (eta / (2 * quittingRewardBound reward)) ≤
      source.initialDebt -
        quittingTerminalSemanticDebtSum port.semanticPort.limit

/-- A positive cap displacement supplies the complete quantitative branch. -/
theorem quantitativeDebtDescent_of_capDisplacement_pos
    (port : source.SummablePort)
    (hdisplacement : 0 < source.capDisplacement port) :
    QuantitativeDebtDescent source port := by
  have hreward : 0 < quittingRewardBound reward := by
    have hbound := source.capDisplacement_le_two_mul_totalAbsorption port
    have habsorption := source.totalAbsorption_nonneg
    have hrewardNonneg := quittingRewardBound_nonneg reward
    nlinarith
  have hdisplacementCharge :=
    source.minimum_mul_capDisplacement_div_twoRewardBound_le_debtDrop
      port hdisplacement
  have hscaledPos : 0 < quittingTerminalSemanticDebtSum source.minimum *
      (source.capDisplacement port / (2 * quittingRewardBound reward)) :=
    mul_pos source.minimum_pos
      (div_pos hdisplacement (mul_pos (by norm_num) hreward))
  have hratio : source.capDisplacement port /
        (2 * quittingRewardBound reward) ≤ source.totalAbsorption := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hreward)).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      source.capDisplacement_le_two_mul_totalAbsorption port
  refine {
    displacement_pos := hdisplacement
    rewardBound_pos := hreward
    displacement_le_two_mul_totalAbsorption :=
      source.capDisplacement_le_two_mul_totalAbsorption port
    scaledDisplacement_le_scaledAbsorption :=
      mul_le_mul_of_nonneg_left hratio source.minimum_pos.le
    absorption_charge := source.minimum_mul_totalAbsorption_le_debtDrop port
    displacement_charge := hdisplacementCharge
    debtDrop_pos := hscaledPos.trans_le hdisplacementCharge
    slice_charge := ?_ }
  intro eta heta hetaLe
  have hratio : eta / (2 * quittingRewardBound reward) ≤
      source.capDisplacement port / (2 * quittingRewardBound reward) :=
    div_le_div_of_nonneg_right hetaLe (mul_nonneg (by norm_num) hreward.le)
  exact (mul_le_mul_of_nonneg_left hratio source.minimum_pos.le).trans
    hdisplacementCharge

/-- If the complete nonnegative absorption sum vanishes, every literal cap
root has zero absorption. -/
theorem root_absorption_eq_zero_of_totalAbsorption_eq_zero
    (hzero : source.totalAbsorption = 0) (time : ℕ) :
    quittingRootAbsorptionMass
        (quittingCapLiftedPrefixRoot reward
          (quittingCapLiftedPrefixProfile reward source.profile time)) = 0 := by
  let absorption : ℕ → ℝ := fun index ↦
    quittingRootAbsorptionMass
      (quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile index))
  have hle : absorption time ≤ ∑' index, absorption index :=
    source.absorption_summable.le_tsum time fun index _ ↦
      quittingRootAbsorptionMass_nonneg _
  have hsum : (∑' index, absorption index) = 0 := by
    simpa [absorption, totalAbsorption] using hzero
  exact le_antisymm (by simpa [hsum] using hle)
    (quittingRootAbsorptionMass_nonneg _)

/-- Zero complete charge makes every selected cap root literally all
Continue, not merely a zero-charge point in a quotient. -/
theorem root_eq_allContinue_of_totalAbsorption_eq_zero
    (hzero : source.totalAbsorption = 0) (time : ℕ) :
    quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time) =
      (quittingAllContinueRoot : iota → PMF Bool) := by
  let root := quittingCapLiftedPrefixRoot reward
    (quittingCapLiftedPrefixProfile reward source.profile time)
  have habsorption : quittingRootAbsorptionMass root = 0 := by
    exact source.root_absorption_eq_zero_of_totalAbsorption_eq_zero hzero time
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  funext who
  simpa only [quittingAllContinueRoot] using
    eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

/-- Literal all-Continue cap prefixing leaves the entire terminal-semantic
pair unchanged at every finite depth. -/
theorem semanticPair_eq_of_totalAbsorption_eq_zero
    (hzero : source.totalAbsorption = 0) (horizon : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile horizon) =
      quittingTerminalSemanticPair reward source.profile := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [quittingCapLiftedPrefixProfile_semanticPair_succ,
        source.root_eq_allContinue_of_totalAbsorption_eq_zero hzero horizon]
      have hnash : IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon)).2 0
          (quittingAllContinueRoot : iota → PMF Bool) := by
        simpa [source.root_eq_allContinue_of_totalAbsorption_eq_zero hzero horizon]
          using quittingCapLiftedPrefixRoot_exactNash reward
            (quittingCapLiftedPrefixProfile reward source.profile horizon)
      exact (quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap
        reward _).2 hnash |>.trans ih

/-- With every outer root all Continue, the paid observer reaches the literal
suffix with probability one. -/
theorem observerReach_eq_one_of_totalAbsorption_eq_zero
    (hzero : source.totalAbsorption = 0) (horizon : ℕ) :
    source.observerReach horizon = 1 := by
  unfold observerReach
  apply Finset.prod_eq_one
  intro time htime
  have hroot := source.root_eq_allContinue_of_totalAbsorption_eq_zero hzero time
  rw [hroot]
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  have hupdate : Function.update
      (quittingAllContinueRoot : iota → PMF Bool) source.observer
        (PMF.pure false) = quittingAllContinueRoot := by
    funext who
    by_cases hwho : who = source.observer
    · subst who
      simp [quittingAllContinueRoot]
    · simp [Function.update_of_ne hwho, quittingAllContinueRoot]
  rw [hupdate]
  have hall := quittingRootAbsorptionMass_allContinueRoot (ι := iota)
  unfold quittingRootAbsorptionMass at hall
  linarith

/-- Both shifted pure-time witnesses retain exactly their original payoff
difference on every inert literal prefix. -/
theorem pureTimePayoff_sub_shift_eq_of_totalAbsorption_eq_zero
    (hzero : source.totalAbsorption = 0) (horizon : ℕ)
    (first second : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer (quittingCapLiftPureTimeShift horizon first) -
        quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer (quittingCapLiftPureTimeShift horizon second) =
      quittingPureTimeDeviationPayoff reward source.profile source.observer first -
        quittingPureTimeDeviationPayoff reward source.profile source.observer second := by
  rw [source.pureTimePayoff_sub_shift horizon,
    source.observerReach_eq_one_of_totalAbsorption_eq_zero hzero horizon, one_mul]

/-- In the inert branch the literal shifted witnesses decode to a paid row
with the full original gain.  Its live mass and temporal data are exactly the
original ones, and its edge identity remains the standard reached-gain
identity. -/
theorem exists_losslessShiftedPaidRow_of_totalAbsorption_eq_zero
    (port : source.SummablePort)
    (hzero : source.totalAbsorption = 0) (horizon : ℕ) :
    ∃ row : QuittingPaidFirstDisagreementRow reward
        (quittingCapLiftedPrefixProfile reward source.profile horizon)
        source.observer source.gain,
      row.sourceWitness =
          quittingCapLiftPureTimeShift horizon source.row.sourceWitness ∧
        row.receivingWitness =
          quittingCapLiftPureTimeShift horizon source.row.receivingWitness ∧
        row.liveMass = source.row.liveMass ∧
        row.reachedGain = source.row.reachedGain ∧
        row.receivingEarlier = source.row.receivingEarlier ∧
        row.start = horizon + source.row.start ∧
        row.later = source.row.later := by
  let shifted := port.shiftedRows horizon
  have hpayoff := source.pureTimePayoff_sub_shift_eq_of_totalAbsorption_eq_zero
    hzero horizon source.row.receivingWitness source.row.sourceWitness
  have horiginal : source.gain ≤
      quittingPureTimeDeviationPayoff reward source.profile source.observer
          source.row.receivingWitness -
        quittingPureTimeDeviationPayoff reward source.profile source.observer
          source.row.sourceWitness :=
    source.row.gain_le_paid.trans_eq source.row.edge_identity.symm
  have hgainPaid : source.gain ≤
      shifted.row.liveMass * shifted.row.reachedGain := by
    have hedge := shifted.row.edge_identity
    rw [shifted.sourceWitness_eq, shifted.receivingWitness_eq] at hedge
    exact (horiginal.trans_eq hpayoff.symm).trans_eq hedge
  have hlive : shifted.row.liveMass = source.row.liveMass := by
    rw [shifted.liveMass_eq,
      source.observerReach_eq_one_of_totalAbsorption_eq_zero hzero horizon,
      one_mul]
  have hgainLive : source.gain ≤
      2 * quittingRewardBound reward * shifted.row.liveMass := by
    calc
      source.gain ≤ 2 * quittingRewardBound reward * source.row.liveMass :=
        source.row.gain_le_liveMass
      _ = 2 * quittingRewardBound reward * shifted.row.liveMass := by rw [hlive]
  have hsourceProductPos : 0 < source.row.liveMass * source.row.reachedGain :=
    source.gain_pos.trans_le source.row.gain_le_paid
  have hsourceLiveNonneg : 0 ≤ source.row.liveMass := by
    rw [source.row.liveMass_eq]
    exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
  have hsourceReachedPos : 0 < source.row.reachedGain :=
    pos_of_mul_pos_right hsourceProductPos hsourceLiveNonneg
  have hsourceLivePos : 0 < source.row.liveMass :=
    pos_of_mul_pos_left hsourceProductPos hsourceReachedPos.le
  have hreached : shifted.row.reachedGain = source.row.reachedGain := by
    have hshiftedEdge := shifted.row.edge_identity
    rw [shifted.sourceWitness_eq, shifted.receivingWitness_eq, hpayoff,
      source.row.edge_identity] at hshiftedEdge
    rw [hlive] at hshiftedEdge
    nlinarith
  let row : QuittingPaidFirstDisagreementRow reward
      (quittingCapLiftedPrefixProfile reward source.profile horizon)
      source.observer source.gain := {
    sourceWitness := shifted.row.sourceWitness
    receivingWitness := shifted.row.receivingWitness
    start := shifted.row.start
    later := shifted.row.later
    later_strict := shifted.row.later_strict
    receivingEarlier := shifted.row.receivingEarlier
    chronology := shifted.row.chronology
    liveMass := shifted.row.liveMass
    liveMass_eq := shifted.row.liveMass_eq
    reachedGain := shifted.row.reachedGain
    reachedGain_eq := shifted.row.reachedGain_eq
    edge_identity := shifted.row.edge_identity
    gain_le_paid := hgainPaid
    gain_le_liveMass := hgainLive }
  refine ⟨row, shifted.sourceWitness_eq, shifted.receivingWitness_eq,
    hlive, hreached, ?_, ?_, ?_⟩
  · exact shifted.receivingEarlier_eq
  · exact shifted.start_eq
  · exact shifted.later_eq

/-- Complete literal inert branch.  All fields concern the actual finite cap
prefix profiles and the checked shifted paid rows; no infinite behavior
profile or prescribed-payoff Bellman edge is asserted. -/
structure InertStall (port : source.SummablePort) : Prop where
  totalAbsorption_eq_zero : source.totalAbsorption = 0
  capDisplacement_eq_zero : source.capDisplacement port = 0
  root_eq_allContinue : ∀ time,
    quittingCapLiftedPrefixRoot reward
        (quittingCapLiftedPrefixProfile reward source.profile time) =
      (quittingAllContinueRoot : iota → PMF Bool)
  semanticPair_eq : ∀ horizon,
    quittingTerminalSemanticPair reward
        (quittingCapLiftedPrefixProfile reward source.profile horizon) =
      quittingTerminalSemanticPair reward source.profile
  debt_eq : ∀ horizon who,
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.profile) who
  debtSum_eq : ∀ horizon,
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)) =
      source.initialDebt
  observerReach_eq_one : ∀ horizon, source.observerReach horizon = 1
  shiftedPayoffDifference_eq : ∀ horizon,
    quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer
          (quittingCapLiftPureTimeShift horizon source.row.receivingWitness) -
        quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward source.profile horizon)
          source.observer
          (quittingCapLiftPureTimeShift horizon source.row.sourceWitness) =
      quittingPureTimeDeviationPayoff reward source.profile source.observer
          source.row.receivingWitness -
        quittingPureTimeDeviationPayoff reward source.profile source.observer
          source.row.sourceWitness
  losslessShiftedPaidRow : ∀ horizon,
    ∃ row : QuittingPaidFirstDisagreementRow reward
        (quittingCapLiftedPrefixProfile reward source.profile horizon)
        source.observer source.gain,
      row.sourceWitness =
          quittingCapLiftPureTimeShift horizon source.row.sourceWitness ∧
        row.receivingWitness =
          quittingCapLiftPureTimeShift horizon source.row.receivingWitness ∧
        row.liveMass = source.row.liveMass ∧
        row.reachedGain = source.row.reachedGain ∧
        row.receivingEarlier = source.row.receivingEarlier ∧
        row.start = horizon + source.row.start ∧
        row.later = source.row.later

/-- Zero complete charge supplies every literal field of the inert stall. -/
theorem inertStall_of_totalAbsorption_eq_zero
    (port : source.SummablePort)
    (hzero : source.totalAbsorption = 0) :
    InertStall source port := by
  have hcap : source.capDisplacement port = 0 := by
    apply le_antisymm
    · have hbound := source.capDisplacement_le_two_mul_totalAbsorption port
      rw [hzero, mul_zero] at hbound
      exact hbound
    · exact source.capDisplacement_nonneg port
  refine {
    totalAbsorption_eq_zero := hzero
    capDisplacement_eq_zero := hcap
    root_eq_allContinue :=
      source.root_eq_allContinue_of_totalAbsorption_eq_zero hzero
    semanticPair_eq :=
      source.semanticPair_eq_of_totalAbsorption_eq_zero hzero
    debt_eq := ?_
    debtSum_eq := ?_
    observerReach_eq_one :=
      source.observerReach_eq_one_of_totalAbsorption_eq_zero hzero
    shiftedPayoffDifference_eq := ?_
    losslessShiftedPaidRow :=
      source.exists_losslessShiftedPaidRow_of_totalAbsorption_eq_zero port hzero }
  · intro horizon who
    rw [source.semanticPair_eq_of_totalAbsorption_eq_zero hzero horizon]
  · intro horizon
    rw [source.semanticPair_eq_of_totalAbsorption_eq_zero hzero horizon]
    rfl
  · intro horizon
    exact source.pureTimePayoff_sub_shift_eq_of_totalAbsorption_eq_zero
      hzero horizon source.row.receivingWitness source.row.sourceWitness

/-- Every positive charge floor strictly below complete absorption, together
with exact return of the limiting cap, produces literal finite-prefix
cumulative-charge payoff near-returns retaining that floor. -/
theorem nonempty_cumulativeNearReturnFamily_of_chargeFloor
    (port : source.SummablePort)
    (chargeFloor : ℝ) (hchargeFloor : 0 < chargeFloor)
    (hchargeBelow : chargeFloor < source.totalAbsorption)
    (hdisplacement : source.capDisplacement port = 0) :
    Nonempty (QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily
      reward) := by
  let orbit := quittingCapLiftedPunishmentFloorOrbit reward source.profile
  have hlimit : port.semanticPort.capPort.limit = orbit.value 0 := by
    have hdist : dist port.semanticPort.limit.2
        (quittingTerminalSemanticPair reward source.profile).2 = 0 := by
      simpa [capDisplacement] using hdisplacement
    have henvelope : port.semanticPort.limit.2 =
        port.semanticPort.capPort.limit := port.semanticPort.envelope_eq
    apply dist_eq_zero.mp
    rw [← henvelope]
    simpa [orbit, quittingCapLiftedPunishmentFloorOrbit] using hdist
  have hvalue : Tendsto orbit.value atTop (nhds (orbit.value 0)) := by
    apply tendsto_pi_nhds.2
    intro who
    have hcoordinate := port.semanticPort.capPort.value_tendsto who
    rw [hlimit] at hcoordinate
    exact hcoordinate
  let absorption : ℕ → ℝ := fun time ↦
    quittingRootAbsorptionMass (orbit.roots time)
  have hsum : Tendsto (fun horizon ↦
      ∑ time ∈ Finset.range horizon, absorption time) atTop
      (nhds source.totalAbsorption) := by
    simpa [orbit, absorption, totalAbsorption,
      quittingCapLiftedPunishmentFloorOrbit] using
      source.absorption_summable.hasSum.tendsto_sum_nat
  refine ⟨{
    chargeFloor := chargeFloor
    chargeFloor_pos := hchargeFloor
    nearReturn := ?_ }⟩
  intro endpointError hendpointError
  have hchargeEventually : ∀ᶠ horizon in atTop,
      chargeFloor <
        ∑ time ∈ Finset.range horizon, absorption time :=
    hsum.eventually (Ioi_mem_nhds hchargeBelow)
  have hcloseEventually : ∀ᶠ horizon in atTop,
      dist (orbit.value horizon) (orbit.value 0) < endpointError :=
    hvalue.eventually (Metric.ball_mem_nhds _ hendpointError)
  obtain ⟨horizon, hcharge, hclose⟩ :=
    (hchargeEventually.and hcloseEventually).exists
  let cert := orbit.toFinitePrefix horizon
  let start := quittingFinitePrefixAdmissibleState cert 0 (by omega)
  let finish := quittingFinitePrefixAdmissibleState cert horizon (by
    change horizon ≤ horizon
    exact le_rfl)
  let path := quittingFinitePrefixAdmissiblePath cert horizon (by
    change horizon ≤ horizon
    exact le_rfl)
  refine ⟨start, finish, path, ?_, ?_⟩
  · dsimp only [path]
    rw [chargeSum_quittingFinitePrefixAdmissiblePath]
    change chargeFloor ≤
      ∑ time ∈ Finset.range horizon, absorption time
    exact hcharge.le
  · intro who
    have hcloseLe : dist (orbit.value horizon) (orbit.value 0) ≤
        endpointError := hclose.le
    rw [dist_pi_le_iff hendpointError.le] at hcloseLe
    change |orbit.value 0 who - orbit.value horizon who| ≤ endpointError
    simpa [Real.dist_eq, abs_sub_comm] using hcloseLe who

/-- The convenient half-charge specialization of the arbitrary retained-floor
near-return theorem. -/
theorem nonempty_cumulativeNearReturnFamily_of_totalAbsorption_pos_of_capDisplacement_zero
    (port : source.SummablePort)
    (habsorption : 0 < source.totalAbsorption)
    (hdisplacement : source.capDisplacement port = 0) :
    Nonempty (QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily
      reward) :=
  source.nonempty_cumulativeNearReturnFamily_of_chargeFloor
    port (source.totalAbsorption / 2) (half_pos habsorption)
      (half_lt_self habsorption) hdisplacement

/-- Charged near-return branch with its checked downstream uniform-payoff
consumer already discharged. -/
structure ChargedNearReturn (port : source.SummablePort) : Prop where
  totalAbsorption_pos : 0 < source.totalAbsorption
  capDisplacement_eq_zero : source.capDisplacement port = 0
  cumulativeNearReturns : Nonempty
    (QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily reward)
  uniformEquilibriumPayoff : ∃ payoff : Payoff iota,
    (quittingGame reward).IsUniformEquilibriumPayoff none payoff

/-- Positive charge with zero limiting cap displacement enters the existing
cumulative near-return uniform-equilibrium consumer. -/
theorem chargedNearReturn_of_totalAbsorption_pos_of_capDisplacement_zero
    (port : source.SummablePort)
    (habsorption : 0 < source.totalAbsorption)
    (hdisplacement : source.capDisplacement port = 0) :
    ChargedNearReturn source port := by
  obtain ⟨family⟩ :=
    source.nonempty_cumulativeNearReturnFamily_of_totalAbsorption_pos_of_capDisplacement_zero
      port habsorption hdisplacement
  exact {
    totalAbsorption_pos := habsorption
    capDisplacement_eq_zero := hdisplacement
    cumulativeNearReturns := ⟨family⟩
    uniformEquilibriumPayoff := family.exists_uniformEquilibriumPayoff }

/-- The literal port lies in one of the three checked cases: charged cap
near-return, quantitative debt descent, or a completely inert marked stall. -/
theorem chargedNearReturn_or_quantitativeDebtDescent_or_inertStall
    (port : source.SummablePort) :
    ChargedNearReturn source port ∨
      QuantitativeDebtDescent source port ∨ InertStall source port := by
  by_cases habsorptionZero : source.totalAbsorption = 0
  · exact Or.inr (Or.inr
      (source.inertStall_of_totalAbsorption_eq_zero port habsorptionZero))
  have habsorption : 0 < source.totalAbsorption :=
    lt_of_le_of_ne source.totalAbsorption_nonneg (Ne.symm habsorptionZero)
  by_cases hdisplacementZero : source.capDisplacement port = 0
  · exact Or.inl
      (source.chargedNearReturn_of_totalAbsorption_pos_of_capDisplacement_zero
        port habsorption hdisplacementZero)
  have hdisplacement : 0 < source.capDisplacement port :=
    lt_of_le_of_ne (source.capDisplacement_nonneg port)
      (Ne.symm hdisplacementZero)
  exact Or.inr (Or.inl
    (source.quantitativeDebtDescent_of_capDisplacement_pos
      port hdisplacement))

/-- The three cases are pairwise disjoint by their exact scalar signs. -/
theorem exactTrichotomy_pairwiseDisjoint (port : source.SummablePort) :
    ¬(ChargedNearReturn source port ∧ QuantitativeDebtDescent source port) ∧
      ¬(ChargedNearReturn source port ∧ InertStall source port) ∧
      ¬(QuantitativeDebtDescent source port ∧ InertStall source port) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hcharged, hdescent⟩
    have hpositive := hdescent.displacement_pos
    rw [hcharged.capDisplacement_eq_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  · rintro ⟨hcharged, hinert⟩
    have hpositive := hcharged.totalAbsorption_pos
    rw [hinert.totalAbsorption_eq_zero] at hpositive
    exact (lt_irrefl 0) hpositive
  · rintro ⟨hdescent, hinert⟩
    have hpositive := hdescent.displacement_pos
    rw [hinert.capDisplacement_eq_zero] at hpositive
    exact (lt_irrefl 0) hpositive

/-- Exhaustive, pairwise-disjoint exact trichotomy for a paid cap-lifted
summable port. -/
theorem exactTrichotomy (port : source.SummablePort) :
    (ChargedNearReturn source port ∨
        QuantitativeDebtDescent source port ∨ InertStall source port) ∧
      ¬(ChargedNearReturn source port ∧ QuantitativeDebtDescent source port) ∧
      ¬(ChargedNearReturn source port ∧ InertStall source port) ∧
      ¬(QuantitativeDebtDescent source port ∧ InertStall source port) := by
  exact ⟨source.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall port,
    source.exactTrichotomy_pairwiseDisjoint port⟩

end QuittingPaidCapLiftedSource

end GameTheory
