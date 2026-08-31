/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.RectangleMaximalRootLedger
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumOpponentIncidence

/-!
# Ordered maximal-root reduction for a Fin4 response rectangle

The literal maximal roots on a supplied rectangle have three ordered outcomes.
Either absorption stays uniformly positive on a strict subsequence, or it
vanishes.  In the vanishing branch, equality with the global minimum produces
the existing reset-rigid chamber, while strict separation produces a vanishing
charge at an off-minimum reset cluster.

This is a consumer of the supplied hard-residual rectangle and its common
compact limit.  It does not construct such a rectangle, renew any row, or
turn any of the three outcomes into a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability FinFourQuantitativeFullSupportHardResidual
open scoped Topology

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
variable {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
variable {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}

/-- A strict subsequence on which literal maximal-root absorption and its
debt charge stay uniformly positive. -/
structure QuittingRectangleUniformlyChargedMaximalRoot
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) where
  lower : ℝ
  lower_pos : 0 < lower
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  absorption_lower : ∀ n,
    lower ≤ quittingRectangleMaximalRootAbsorption limit (subseq n)
  charge_lower : ∀ n,
    lower * quittingTerminalSemanticDebtSum frontier.base ≤
      quittingRectangleMaximalRootCharge limit (subseq n)

/-- Vanishing maximal roots at a cluster on the global-minimum debt fibre,
together with the literal reset-rigid chamber forced there. -/
structure QuittingRectangleMinimumResetRigidMaximalRoot
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) where
  absorption_tendsto_zero :
    Tendsto (quittingRectangleMaximalRootAbsorption limit) atTop (nhds 0)
  cluster_debt_eq_base :
    quittingTerminalSemanticDebtSum dispatch.cluster.1 =
      quittingTerminalSemanticDebtSum frontier.base
  totalOpponentIncidence_pos : 0 <
    quittingTerminalTotalOpponentIncidenceMass packet.observer dispatch.cluster.2
  resetRigidChamber : Nonempty
    (QuittingLawTightResetRigidChamber reward dispatch.cluster dispatch.cluster
      dispatch.cluster frontier.base)

/-- Vanishing maximal roots at a cluster whose total debt is strictly above
the global minimum.  The exact maximal-root charge also vanishes. -/
structure QuittingRectangleOffMinimumVanishingMaximalRoot
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) where
  absorption_tendsto_zero :
    Tendsto (quittingRectangleMaximalRootAbsorption limit) atTop (nhds 0)
  charge_tendsto_zero :
    Tendsto (quittingRectangleMaximalRootCharge limit) atTop (nhds 0)
  prefixedEndpoint_tendsto_cluster : Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n),
      quittingTerminalOutcomeMass reward
        (quittingRectangleMaximalRootPrefixedEndpoint limit n)))
    atTop (nhds dispatch.cluster)
  base_debt_lt_cluster :
    quittingTerminalSemanticDebtSum frontier.base <
      quittingTerminalSemanticDebtSum dispatch.cluster.1
  cluster_observer_reset :
    quittingTerminalSemanticDebt dispatch.cluster.1 packet.observer = 0
  minimizer_observer_reset :
    quittingTerminalSemanticDebt dispatch.minimizer packet.observer = 0
  minimizer_unique_allContinue : ∀ root : Fin 4 → PMF Bool,
    IsεQuittingRootNash reward dispatch.minimizer.2 0 root →
      root = (quittingAllContinueRoot : Fin 4 → PMF Bool)

/-- **Ordered maximal-root reduction.**  A supplied common rectangle limit
falls into a uniformly charged subsequence, a minimum-fibre reset-rigid
chamber, or an off-minimum vanishing-root branch. -/
theorem QuittingStoppingLawRectangleJointAtomLimit.maximalRoot_threeWay
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (QuittingRectangleUniformlyChargedMaximalRoot limit) ∨
      Nonempty (QuittingRectangleMinimumResetRigidMaximalRoot limit) ∨
      Nonempty (QuittingRectangleOffMinimumVanishingMaximalRoot limit) := by
  by_cases habsorption : Tendsto
      (quittingRectangleMaximalRootAbsorption limit) atTop (nhds 0)
  · rcases dispatch.cluster_fiber_or_separated with hminimum | hoffMinimum
    · right
      left
      have hclusterGlobal : ∀ candidate ∈
          quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum dispatch.cluster.1 ≤
            quittingTerminalSemanticDebtSum candidate := by
        intro candidate hcandidate
        rw [hminimum]
        exact frontier.base_minimum candidate hcandidate
      let clusterMinimum : IsQuittingLawTightCapNashSaturationMinimum
          reward dispatch.cluster dispatch.cluster := {
        mem := quittingLawTightCapNashSaturationHull_origin_mem
          reward dispatch.cluster
        debt_le := by
          intro point hpoint
          exact hclusterGlobal point.1
            (terminalSemanticLawCarrier_fst_mem_carrier point
              (quittingLawTightCapNashSaturationHull_subset_carrier
                reward dispatch.cluster dispatch.cluster_mem hpoint))
      }
      have hincidence : 0 <
          quittingTerminalTotalOpponentIncidenceMass packet.observer
            dispatch.cluster.2 :=
        totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero
          reward bound residual dispatch.cluster dispatch.cluster_mem
            hclusterGlobal packet.observer dispatch.cluster_observer_reset
      have hchamber := exists_quittingLawTightResetRigidChamber
        residual.witness frontier.base frontier.base_minimum
          frontier.base_positive dispatch.cluster dispatch.cluster dispatch.cluster
            dispatch.cluster_mem clusterMinimum clusterMinimum.minimum_mem_face
              packet.observer dispatch.cluster_observer_reset hincidence
      exact ⟨{
        absorption_tendsto_zero := habsorption
        cluster_debt_eq_base := hminimum
        totalOpponentIncidence_pos := hincidence
        resetRigidChamber := hchamber
      }⟩
    · right
      right
      exact ⟨{
        absorption_tendsto_zero := habsorption
        charge_tendsto_zero :=
          quittingRectangleMaximalRootCharge_tendsto_zero limit habsorption
        prefixedEndpoint_tendsto_cluster :=
          quittingRectangleMaximalRootPrefixedEndpoint_tendsto_cluster
            limit habsorption
        base_debt_lt_cluster := hoffMinimum
        cluster_observer_reset := dispatch.cluster_observer_reset
        minimizer_observer_reset := dispatch.minimizer_observer_reset
        minimizer_unique_allContinue := dispatch.unique_capNash
      }⟩
  · left
    obtain ⟨lower, hlower, hfrequent⟩ :=
      Math.exists_pos_frequently_ge_of_nonneg_of_not_tendsto_zero
        (quittingRectangleMaximalRootAbsorption limit)
        (quittingRectangleMaximalRootAbsorption_nonneg limit) habsorption
    obtain ⟨subseq, hsubseq, habsorptionLower⟩ :=
      extraction_of_frequently_atTop hfrequent
    have hchargeLower : ∀ n,
        lower * quittingTerminalSemanticDebtSum frontier.base ≤
          quittingRectangleMaximalRootCharge limit (subseq n) := by
      intro n
      unfold quittingRectangleMaximalRootCharge
      calc
        lower * quittingTerminalSemanticDebtSum frontier.base ≤
            lower * quittingRectangleEndpointDebt limit (subseq n) :=
          mul_le_mul_of_nonneg_left
            (frontier.base_minimum _
              (quittingTerminalSemanticPair_mem_carrier reward _)) hlower.le
        _ ≤ quittingRectangleMaximalRootAbsorption limit (subseq n) *
            quittingRectangleEndpointDebt limit (subseq n) :=
          mul_le_mul_of_nonneg_right (habsorptionLower n)
            (quittingRectangleEndpointDebt_pos limit (subseq n)).le
    exact ⟨{
      lower := lower
      lower_pos := hlower
      subseq := subseq
      subseq_strictMono := hsubseq
      absorption_lower := habsorptionLower
      charge_lower := hchargeLower
    }⟩

/-- Uniform positive absorption on a strict subsequence excludes vanishing
maximal-root absorption on the original sequence. -/
theorem QuittingRectangleUniformlyChargedMaximalRoot.not_absorption_tendsto_zero
    {limit : QuittingStoppingLawRectangleJointAtomLimit dispatch}
    (charged : QuittingRectangleUniformlyChargedMaximalRoot limit) :
    ¬ Tendsto (quittingRectangleMaximalRootAbsorption limit) atTop (nhds 0) := by
  intro hzero
  have hsubsequence := hzero.comp charged.subseq_strictMono.tendsto_atTop
  have hlower : Tendsto (fun _ : ℕ => charged.lower) atTop
      (nhds charged.lower) := tendsto_const_nhds
  have hle : charged.lower ≤ 0 :=
    le_of_tendsto_of_tendsto hlower hsubsequence
      (Filter.Eventually.of_forall charged.absorption_lower)
  exact (not_le_of_gt charged.lower_pos) hle

/-- The three maximal-root outcomes are jointly exhaustive and pairwise
exclusive. -/
structure QuittingRectangleMaximalRootExactlyOne
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) where
  outcome :
    Nonempty (QuittingRectangleUniformlyChargedMaximalRoot limit) ∨
      Nonempty (QuittingRectangleMinimumResetRigidMaximalRoot limit) ∨
      Nonempty (QuittingRectangleOffMinimumVanishingMaximalRoot limit)
  charged_excludes_minimum : ¬
    (Nonempty (QuittingRectangleUniformlyChargedMaximalRoot limit) ∧
      Nonempty (QuittingRectangleMinimumResetRigidMaximalRoot limit))
  charged_excludes_offMinimum : ¬
    (Nonempty (QuittingRectangleUniformlyChargedMaximalRoot limit) ∧
      Nonempty (QuittingRectangleOffMinimumVanishingMaximalRoot limit))
  minimum_excludes_offMinimum : ¬
    (Nonempty (QuittingRectangleMinimumResetRigidMaximalRoot limit) ∧
      Nonempty (QuittingRectangleOffMinimumVanishingMaximalRoot limit))

/-- **Exclusive ordered maximal-root reduction.**  Exactly one of the charged,
minimum-fibre reset-rigid, and off-minimum vanishing alternatives holds. -/
theorem QuittingStoppingLawRectangleJointAtomLimit.maximalRoot_exactlyOne
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    QuittingRectangleMaximalRootExactlyOne limit where
  outcome := limit.maximalRoot_threeWay residual
  charged_excludes_minimum := by
    rintro ⟨⟨charged⟩, ⟨minimum⟩⟩
    exact charged.not_absorption_tendsto_zero
      minimum.absorption_tendsto_zero
  charged_excludes_offMinimum := by
    rintro ⟨⟨charged⟩, ⟨offMinimum⟩⟩
    exact charged.not_absorption_tendsto_zero
      offMinimum.absorption_tendsto_zero
  minimum_excludes_offMinimum := by
    rintro ⟨⟨minimum⟩, ⟨offMinimum⟩⟩
    have hlt := offMinimum.base_debt_lt_cluster
    rw [minimum.cluster_debt_eq_base] at hlt
    exact (lt_irrefl _ hlt)

end GameTheory
