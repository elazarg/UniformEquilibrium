/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.RectangleResetFaceMinimizer
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Root.MaximalAbsorptionNash
import UniformEquilibrium.Quitting.RewardBound

/-!
# Maximal-root ledger for a vanishing-response rectangle

At every literal double endpoint of the common rectangle subsequence, this
module selects the canonical maximal-absorption exact root against the actual
unrestricted behavioral cap.  Prefix debt and the signed sibling atom then
obey exact scaling identities.  Global minimum debt and the canonical reward
bound give a uniform retained-atom estimate.

This is branch-local source data.  It does not make the sibling prefix Nash,
make the charged row renewable, or supply a downstream chamber consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
variable {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
variable {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}

/-- Original rectangle rank on the common joint-limit subsequence. -/
def quittingRectangleMaximalRootIndex
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : ℕ :=
  dispatch.subseq (limit.subseq n)

/-- Literal low-debt response endpoint on the common subsequence. -/
def quittingRectangleMaximalRootEndpoint
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawRectangleDoubleEndpointProfile packet
    (quittingRectangleMaximalRootIndex limit n)

/-- Same-response sibling endpoint on the common subsequence. -/
def quittingRectangleMaximalRootSibling
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawRectangleSourceResponseProfile packet
    (quittingRectangleMaximalRootIndex limit n)

/-- Maximal-absorption exact root at the literal response endpoint cap. -/
def quittingRectangleMaximalRoot
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : Fin 4 → PMF Bool :=
  quittingMaximalAbsorptionCapRoot reward
    (quittingTerminalSemanticPair reward
      (quittingRectangleMaximalRootEndpoint limit n)).2

/-- Absorption of the literal maximal root. -/
def quittingRectangleMaximalRootAbsorption
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : ℝ :=
  quittingRootAbsorptionMass (quittingRectangleMaximalRoot limit n)

/-- Total debt of the unprefixed response endpoint. -/
def quittingRectangleEndpointDebt
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingRectangleMaximalRootEndpoint limit n))

/-- Debt charge paid by the maximal root. -/
def quittingRectangleMaximalRootCharge
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : ℝ :=
  quittingRectangleMaximalRootAbsorption limit n *
    quittingRectangleEndpointDebt limit n

/-- Literal maximal-root prefix of the response endpoint. -/
def quittingRectangleMaximalRootPrefixedEndpoint
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingRectangleMaximalRoot limit n)
    (quittingRectangleMaximalRootEndpoint limit n)

/-- The same root prefixed to the same-response sibling. -/
def quittingRectangleMaximalRootPrefixedSibling
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingRectangleMaximalRoot limit n)
    (quittingRectangleMaximalRootSibling limit n)

theorem quittingRectangleMaximalRoot_exactNash
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootEndpoint limit n)).2 0
      (quittingRectangleMaximalRoot limit n) :=
  quittingMaximalAbsorptionCapRoot_exactNash reward _

theorem quittingRectangleMaximalRootAbsorption_nonneg
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    0 ≤ quittingRectangleMaximalRootAbsorption limit n :=
  quittingRootAbsorptionMass_nonneg _

/-- Every player debt is scaled by the literal maximal-root survival factor.
This is the coordinatewise form of the exact cap-Nash prefix ledger. -/
theorem quittingRectangleMaximalRootPrefixedEndpoint_debt_coordinate_eq
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) (who : Fin 4) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n)) who =
      (1 - quittingRectangleMaximalRootAbsorption limit n) *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootEndpoint limit n)) who := by
  rw [show quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)) who =
      quittingStationaryContinueMass (quittingRectangleMaximalRoot limit n) *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootEndpoint limit n)) who by
    simpa only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt,
      quittingRectangleMaximalRootPrefixedEndpoint] using
        (quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
          (reward := reward) (quittingRectangleMaximalRoot limit n)
          (quittingRectangleMaximalRootEndpoint limit n) who
          (quittingRectangleMaximalRoot_exactNash limit n))]
  unfold quittingRectangleMaximalRootAbsorption quittingRootAbsorptionMass
  ring

/-- Every endpoint debt is positive because the frontier base is a positive
global minimum. -/
theorem quittingRectangleEndpointDebt_pos
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    0 < quittingRectangleEndpointDebt limit n := by
  exact frontier.base_positive.trans_le
    (frontier.base_minimum _
      (quittingTerminalSemanticPair_mem_carrier reward _))

/-- Exact total-debt scaling under the literal maximal-root prefix. -/
theorem quittingRectangleMaximalRootPrefixedEndpoint_debt_eq
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n)) =
      (1 - quittingRectangleMaximalRootAbsorption limit n) *
        quittingRectangleEndpointDebt limit n := by
  rw [show quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)) =
      quittingStationaryContinueMass
          (quittingRectangleMaximalRoot limit n) *
        quittingRectangleEndpointDebt limit n by
    exact quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
      (reward := reward) (quittingRectangleMaximalRoot limit n)
        (quittingRectangleMaximalRootEndpoint limit n)
          (quittingRectangleMaximalRoot_exactNash limit n)]
  unfold quittingRectangleMaximalRootAbsorption quittingRootAbsorptionMass
  ring

/-- The literal debt drop is exactly absorption times endpoint debt. -/
theorem quittingRectangleMaximalRootCharge_eq_debt_sub_prefixedDebt
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    quittingRectangleMaximalRootCharge limit n =
      quittingRectangleEndpointDebt limit n -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootPrefixedEndpoint limit n)) := by
  rw [quittingRectangleMaximalRootPrefixedEndpoint_debt_eq]
  unfold quittingRectangleMaximalRootCharge
  ring

/-- Charge is nonnegative and no larger than the endpoint's excess over the
global minimum. -/
theorem quittingRectangleMaximalRootCharge_bounds
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    0 ≤ quittingRectangleMaximalRootCharge limit n ∧
      quittingRectangleMaximalRootCharge limit n ≤
        quittingRectangleEndpointDebt limit n -
          quittingTerminalSemanticDebtSum frontier.base := by
  have hchargeNonneg : 0 ≤ quittingRectangleMaximalRootCharge limit n :=
    mul_nonneg (quittingRectangleMaximalRootAbsorption_nonneg limit n)
      (quittingRectangleEndpointDebt_pos limit n).le
  have hprefixedCarrier := quittingTerminalSemanticPair_mem_carrier reward
    (quittingRectangleMaximalRootPrefixedEndpoint limit n)
  have hminimum := frontier.base_minimum _ hprefixedCarrier
  constructor
  · exact hchargeNonneg
  · rw [quittingRectangleMaximalRootCharge_eq_debt_sub_prefixedDebt]
    exact sub_le_sub_left hminimum _

/-- Every literal endpoint debt is bounded by eight times the canonical
coordinate reward bound. -/
theorem quittingRectangleEndpointDebt_le_eight_mul_rewardBound
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    quittingRectangleEndpointDebt limit n ≤ 8 * quittingRewardBound reward := by
  let pair := quittingTerminalSemanticPair reward
    (quittingRectangleMaximalRootEndpoint limit n)
  have hbox := quittingTerminalSemanticCarrier_mem_box reward pair
    (abs_reward_le_quittingRewardBound reward)
    (quittingTerminalSemanticPair_mem_carrier reward _)
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt pair who ≤
        2 * quittingRewardBound reward := by
    intro who
    unfold quittingTerminalSemanticDebt
    linarith [hbox.1.1 who, hbox.2.2 who]
  unfold quittingRectangleEndpointDebt quittingTerminalSemanticDebtSum
  calc
    ∑ who, quittingTerminalSemanticDebt pair who ≤
        ∑ _ : Fin 4, 2 * quittingRewardBound reward :=
      Finset.sum_le_sum fun who _ => hcoordinate who
    _ = 8 * quittingRewardBound reward := by
      norm_num [Finset.sum_const]
      ring

/-- The positive global debt minimum supplies a standalone survival floor for
every literal maximal root. -/
theorem quittingRectangleMaximalRoot_survival_floor
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    quittingTerminalSemanticDebtSum frontier.base /
          (8 * quittingRewardBound reward) ≤
      1 - quittingRectangleMaximalRootAbsorption limit n := by
  have hD : 0 < quittingRectangleEndpointDebt limit n :=
    quittingRectangleEndpointDebt_pos limit n
  have hscale : quittingTerminalSemanticDebtSum frontier.base /
        quittingRectangleEndpointDebt limit n ≤
      1 - quittingRectangleMaximalRootAbsorption limit n := by
    rw [div_le_iff₀ hD]
    have hminimum := frontier.base_minimum _
      (quittingTerminalSemanticPair_mem_carrier reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n))
    rw [quittingRectangleMaximalRootPrefixedEndpoint_debt_eq] at hminimum
    exact hminimum
  have hdenom : quittingTerminalSemanticDebtSum frontier.base /
        (8 * quittingRewardBound reward) ≤
      quittingTerminalSemanticDebtSum frontier.base /
        quittingRectangleEndpointDebt limit n := by
    exact div_le_div_of_nonneg_left frontier.base_positive.le hD
      (quittingRectangleEndpointDebt_le_eight_mul_rewardBound limit n)
  exact hdenom.trans hscale

/-- Endpoint debt converges to the debt of the common semantic cluster. -/
theorem quittingRectangleEndpointDebt_tendsto
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    Tendsto (quittingRectangleEndpointDebt limit) atTop
      (nhds (quittingTerminalSemanticDebtSum dispatch.cluster.1)) := by
  have hpair : Tendsto (fun n =>
      quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootEndpoint limit n)) atTop
      (nhds dispatch.cluster.1) := by
    exact (continuous_fst.tendsto dispatch.cluster).comp limit.endpoint_tendsto
  change Tendsto (fun n => quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingRectangleMaximalRootEndpoint limit n))) atTop
      (nhds (quittingTerminalSemanticDebtSum dispatch.cluster.1))
  exact continuous_quittingTerminalSemanticDebtSum.tendsto dispatch.cluster.1
    |>.comp hpair

/-- Vanishing maximal-root absorption forces the exact debt charge to
vanish. -/
theorem quittingRectangleMaximalRootCharge_tendsto_zero
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (habsorption : Tendsto (quittingRectangleMaximalRootAbsorption limit)
      atTop (nhds 0)) :
    Tendsto (quittingRectangleMaximalRootCharge limit) atTop (nhds 0) := by
  change Tendsto (fun n => quittingRectangleMaximalRootAbsorption limit n *
    quittingRectangleEndpointDebt limit n) atTop (nhds 0)
  simpa only [zero_mul] using
    habsorption.mul (quittingRectangleEndpointDebt_tendsto limit)

/-- The common prefix scales the signed rectangle atom exactly. -/
theorem quittingRectangleMaximalRootPrefixed_atom_eq
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    quittingTerminalPayoffDifferenceAtom reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)
        (quittingRectangleMaximalRootPrefixedSibling limit n)
        packet.observer (some packet.terminal) =
      (1 - quittingRectangleMaximalRootAbsorption limit n) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingRectangleMaximalRootEndpoint limit n)
          (quittingRectangleMaximalRootSibling limit n)
          packet.observer (some packet.terminal) := by
  simpa [quittingRectangleMaximalRootPrefixedEndpoint,
    quittingRectangleMaximalRootPrefixedSibling,
    quittingLiteralRootStackJointSurvival,
    quittingRectangleMaximalRootAbsorption, quittingRootAbsorptionMass] using
      (quittingTerminalPayoffDifferenceAtom_literalRootStack reward
        [quittingRectangleMaximalRoot limit n]
        (quittingRectangleMaximalRootEndpoint limit n)
        (quittingRectangleMaximalRootSibling limit n)
        packet.observer (some packet.terminal))

/-- The maximal-root prefix retains the packet's signed atom with the uniform
positive-minimum factor. -/
theorem quittingRectangleMaximalRootPrefixed_atom_lower
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (n : ℕ) :
    packet.charge * quittingTerminalSemanticDebtSum frontier.base /
          (32 * quittingRewardBound reward) ≤
      16 * quittingTerminalPayoffDifferenceAtom reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)
        (quittingRectangleMaximalRootPrefixedSibling limit n)
        packet.observer (some packet.terminal) := by
  have hM : 0 < quittingRewardBound reward := packet.rewardBound_pos
  have hsurvival := quittingRectangleMaximalRoot_survival_floor limit n
  have hcard : Fintype.card (QuittingTerminalOutcome (Fin 4)) = 16 := by
    decide
  have hatom : packet.charge / 4 ≤
      16 * quittingTerminalPayoffDifferenceAtom reward
        (quittingRectangleMaximalRootEndpoint limit n)
        (quittingRectangleMaximalRootSibling limit n)
        packet.observer (some packet.terminal) := by
    simpa only [hcard, Nat.cast_ofNat,
      quittingRectangleMaximalRootIndex,
      quittingRectangleMaximalRootEndpoint,
      quittingRectangleMaximalRootSibling] using
        dispatch.atom_bound (limit.subseq n)
  have hcharge : 0 < packet.charge := packet.charge_pos
  have hfactor : 0 ≤ packet.charge / 4 := (div_pos hcharge (by norm_num)).le
  have hsurvivalNonneg :
      0 ≤ 1 - quittingRectangleMaximalRootAbsorption limit n := by
    simpa [quittingRectangleMaximalRootAbsorption,
      quittingRootAbsorptionMass] using
        quittingStationaryContinueMass_nonneg
          (quittingRectangleMaximalRoot limit n)
  calc
    packet.charge * quittingTerminalSemanticDebtSum frontier.base /
          (32 * quittingRewardBound reward) =
        (quittingTerminalSemanticDebtSum frontier.base /
            (8 * quittingRewardBound reward)) * (packet.charge / 4) := by
      field_simp
      ring
    _ ≤ (1 - quittingRectangleMaximalRootAbsorption limit n) *
        (16 * quittingTerminalPayoffDifferenceAtom reward
          (quittingRectangleMaximalRootEndpoint limit n)
          (quittingRectangleMaximalRootSibling limit n)
          packet.observer (some packet.terminal)) :=
      mul_le_mul hsurvival hatom hfactor hsurvivalNonneg
    _ = 16 * quittingTerminalPayoffDifferenceAtom reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)
        (quittingRectangleMaximalRootPrefixedSibling limit n)
        packet.observer (some packet.terminal) := by
      rw [quittingRectangleMaximalRootPrefixed_atom_eq]
      ring

/-- If the literal maximal-root absorption vanishes, then prefixing the
endpoint by those exact roots preserves the common joint semantic/law limit.
The proof uses the exact coordinate debt scaling, so no root-topology or
closed-Nash hypothesis is hidden in this statement. -/
theorem quittingRectangleMaximalRootPrefixedEndpoint_tendsto_cluster
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (habsorption : Tendsto (quittingRectangleMaximalRootAbsorption limit)
      atTop (nhds 0)) :
    Tendsto (fun n =>
      (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n),
        quittingTerminalOutcomeMass reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n)))
      atTop (nhds dispatch.cluster) := by
  have hendpointPair : Tendsto (fun n =>
      quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootEndpoint limit n)) atTop
      (nhds dispatch.cluster.1) :=
    (continuous_fst.tendsto dispatch.cluster).comp limit.endpoint_tendsto
  have hendpointMass : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward
        (quittingRectangleMaximalRootEndpoint limit n)) atTop
      (nhds dispatch.cluster.2) :=
    (continuous_snd.tendsto dispatch.cluster).comp limit.endpoint_tendsto
  have hprescribed : Tendsto (fun n =>
      (quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)).1) atTop
      (nhds dispatch.cluster.1.1) := by
    apply tendsto_pi_nhds.2
    intro who
    have hendpoint := (tendsto_pi_nhds.mp
      ((continuous_fst.tendsto dispatch.cluster.1).comp hendpointPair)) who
    have herror : Tendsto (fun n =>
        (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootPrefixedEndpoint limit n)).1 who -
          (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootEndpoint limit n)).1 who)
        atTop (nhds 0) := by
      apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _
        (fun n => 2 * quittingRewardBound reward *
          quittingRectangleMaximalRootAbsorption limit n)
      · simpa using tendsto_const_nhds.mul habsorption
      · filter_upwards with n
        rw [quittingRectangleMaximalRootPrefixedEndpoint,
          quittingTerminalSemanticPair_rootThenContinuation]
        exact
          abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
            reward
            (quittingTerminalSemanticPair reward
              (quittingRectangleMaximalRootEndpoint limit n)).1
            (quittingRectangleMaximalRoot limit n) who
            (quittingRewardBound reward)
            (abs_reward_le_quittingRewardBound reward)
            (abs_quittingTerminalPayoff_le reward
              (quittingRectangleMaximalRootEndpoint limit n) who
              (abs_reward_le_quittingRewardBound reward))
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
      herror.add hendpoint
  have hdebt : Tendsto (fun n => fun who =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n)) who) atTop
      (nhds (fun who => quittingTerminalSemanticDebt dispatch.cluster.1 who)) := by
    apply tendsto_pi_nhds.2
    intro who
    have hendpoint : Tendsto (fun n =>
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootEndpoint limit n)) who) atTop
        (nhds (quittingTerminalSemanticDebt dispatch.cluster.1 who)) :=
      (continuous_quittingTerminalSemanticDebt who).tendsto dispatch.cluster.1
        |>.comp hendpointPair
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hscale := (hone.sub habsorption).mul hendpoint
    simpa only [sub_zero, one_mul,
      quittingRectangleMaximalRootPrefixedEndpoint_debt_coordinate_eq] using hscale
  have hsemantic : Tendsto (fun n =>
      quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)) atTop
      (nhds dispatch.cluster.1) := by
    have hcap : Tendsto (fun n =>
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n)).2) atTop
        (nhds dispatch.cluster.1.2) := by
      apply tendsto_pi_nhds.2
      intro who
      have hsum := (tendsto_pi_nhds.mp hdebt who).add
        (tendsto_pi_nhds.mp hprescribed who)
      simpa only [quittingTerminalSemanticDebt, sub_add_cancel] using hsum
    rw [nhds_prod_eq]
    exact hprescribed.prodMk hcap
  have hlaw : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)) atTop
      (nhds dispatch.cluster.2) := by
    apply tendsto_pi_nhds.2
    intro outcome
    have hendpoint := tendsto_pi_nhds.mp hendpointMass outcome
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    cases outcome with
    | none =>
        have hproduct := (hone.sub habsorption).mul hendpoint
        simpa only [sub_zero, one_mul,
          quittingRectangleMaximalRootPrefixedEndpoint,
          quittingTerminalOutcomeMass_rootThenContinuation,
          quittingRectangleMaximalRootAbsorption,
          quittingRootAbsorptionMass, sub_sub_cancel] using hproduct
    | some terminal =>
        have hcoalition : Tendsto (fun n =>
            quittingRootCoalitionMass
              (quittingRectangleMaximalRoot limit n) terminal.val)
            atTop (nhds 0) := by
          apply squeeze_zero'
          · exact Filter.Eventually.of_forall fun n =>
              quittingRootCoalitionMass_nonneg _ _
          · obtain ⟨marked, hmarked⟩ := terminal.property
            exact Filter.Eventually.of_forall fun n =>
              (quittingRootCoalitionMass_le_quitProbability_of_mem
                (quittingRectangleMaximalRoot limit n) terminal.val marked
                hmarked).trans
                  (quittingQuitProbability_le_absorptionMass _ marked)
          · exact habsorption
        have hproduct := (hone.sub habsorption).mul hendpoint
        have hadd := hcoalition.add hproduct
        simpa only [zero_add, sub_zero, one_mul,
          quittingRectangleMaximalRootPrefixedEndpoint,
          quittingTerminalOutcomeMass_rootThenContinuation,
          quittingRectangleMaximalRootAbsorption,
          quittingRootAbsorptionMass, sub_sub_cancel] using hadd
  rw [nhds_prod_eq]
  exact hsemantic.prodMk hlaw

/-- The observer debt of the literal maximal-root-prefixed endpoint still
vanishes along the common rectangle subsequence. -/
theorem quittingRectangleMaximalRootPrefixedEndpoint_observerDebt_tendsto_zero
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootPrefixedEndpoint limit n))
        packet.observer) atTop (nhds 0) := by
  have hendpoint : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootEndpoint limit n))
        packet.observer) atTop (nhds 0) := by
    have hraw := packet.observer_debt_tendsto_zero.comp
      ((dispatch.subseq_strictMono.comp limit.subseq_strictMono).tendsto_atTop)
    change Tendsto ((fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStoppingLawRectangleDoubleEndpointProfile packet n))
        packet.observer) ∘ dispatch.subseq ∘ limit.subseq) atTop (nhds 0) at hraw
    change Tendsto ((fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStoppingLawRectangleDoubleEndpointProfile packet n))
        packet.observer) ∘ dispatch.subseq ∘ limit.subseq) atTop (nhds 0)
    exact hraw
  have hprefixEq : ∀ n,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRectangleMaximalRootPrefixedEndpoint limit n))
          packet.observer =
        (1 - quittingRectangleMaximalRootAbsorption limit n) *
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingRectangleMaximalRootEndpoint limit n))
            packet.observer :=
    fun n => quittingRectangleMaximalRootPrefixedEndpoint_debt_coordinate_eq
      limit n packet.observer
  refine squeeze_zero' ?_ ?_ hendpoint
  · filter_upwards with n
    rw [hprefixEq]
    have hdebt0 : 0 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootEndpoint limit n)) packet.observer := by
      simpa only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
        quittingTerminalDeviationDebt] using
          quittingTerminalDeviationDebt_nonneg reward
            (quittingRectangleMaximalRootEndpoint limit n) packet.observer
    exact mul_nonneg (by
      simpa [quittingRectangleMaximalRootAbsorption,
        quittingRootAbsorptionMass] using
          quittingStationaryContinueMass_nonneg
            (quittingRectangleMaximalRoot limit n)) hdebt0
  · filter_upwards with n
    rw [hprefixEq]
    have hdebt0 : 0 ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRectangleMaximalRootEndpoint limit n)) packet.observer := by
      simpa only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
        quittingTerminalDeviationDebt] using
          quittingTerminalDeviationDebt_nonneg reward
            (quittingRectangleMaximalRootEndpoint limit n) packet.observer
    exact mul_le_of_le_one_left hdebt0 (by
      simpa [quittingRectangleMaximalRootAbsorption,
        quittingRootAbsorptionMass] using
          quittingStationaryContinueMass_le_one
            (quittingRectangleMaximalRoot limit n))

end GameTheory
