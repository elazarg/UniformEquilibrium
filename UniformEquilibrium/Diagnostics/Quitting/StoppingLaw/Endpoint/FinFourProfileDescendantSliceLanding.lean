/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFourProfileDescendantSlice
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.RectangleMaximalRootReduction
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PositiveTotalSlopeFullReplacement

/-!
# Fin4 rectangle landing in a four-profile descendant slice

A supplied rectangle joint-law limit determines four literal source profiles.
One common compact subsequence carries the response atom, full-replacement gain,
and vanishing observer debt. Positive normalized densities then give a slice
minimizer that either lands at the global minimum in a reset-rigid chamber or
has strictly larger debt.

This is a branch-local adapter for the supplied rectangle and hard residual. It
does not construct either input, supply ancestry or chronology, consume either
landing arm, or prove a uniform-equilibrium result.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open FinFourQuantitativeFullSupportHardResidual
open QuittingFourProfileResponseFamily
open scoped Topology

/-! ## Literal rectangle source adapter -/

namespace QuittingStoppingLawRectangleJointAtomLimit

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
variable {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
variable {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}

/-- The one common rank in the tangent family selected by the rectangle and
joint-law compactifications. -/
def fourProfileRank
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) (n : ℕ) : ℕ :=
  packet.rank (dispatch.subseq (limit.subseq n))

/-- The literal response, sibling, full-replacement, and source profiles on
the common rectangle ranks. -/
def fourProfileResponseFamily
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    QuittingFourProfileResponseFamily reward where
  responseProfile n :=
    quittingStoppingLawRectangleDoubleEndpointProfile packet
      (dispatch.subseq (limit.subseq n))
  siblingProfile n :=
    quittingStoppingLawRectangleSourceResponseProfile packet
      (dispatch.subseq (limit.subseq n))
  replacementProfile n :=
    frontier.fullReplacementProfile packet.mover (limit.fourProfileRank n)
  sourceProfile n := frontier.source (limit.fourProfileRank n)
  terminal := packet.terminal
  observer := packet.observer
  mover := packet.mover.1

theorem fourProfileRank_strictMono
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    StrictMono limit.fourProfileRank :=
  dispatch.rank_strictMono.comp limit.subseq_strictMono

theorem fourProfile_actualGain_eq_fullReplacementPrescribedGain
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) (n : ℕ) :
    (QuittingFourProfileResponseFamily.baseDecoration
      (family := limit.fourProfileResponseFamily) n).actualGain packet.mover.1 =
      frontier.fullReplacementPrescribedGain packet.mover
        (limit.fourProfileRank n) := by
  rfl

theorem fourProfile_actualGain_tendsto_baseDebt
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    Tendsto (fun n ↦
      (QuittingFourProfileResponseFamily.baseDecoration
        (family := limit.fourProfileResponseFamily) n).actualGain packet.mover.1)
      atTop (nhds (quittingTerminalSemanticDebt frontier.base packet.mover.1)) := by
  rw [show (fun n ↦
      (QuittingFourProfileResponseFamily.baseDecoration
        (family := limit.fourProfileResponseFamily) n).actualGain packet.mover.1) =
      (fun n ↦ frontier.fullReplacementPrescribedGain packet.mover
        (limit.fourProfileRank n)) by
    funext n
    exact limit.fourProfile_actualGain_eq_fullReplacementPrescribedGain n]
  exact (frontier.fullReplacementPrescribedGain_tendsto_baseDebt packet.mover).comp
    limit.fourProfileRank_strictMono.tendsto_atTop

theorem fourProfile_signedAtom_lower
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) (n : ℕ) :
    packet.charge / 4 ≤
      (QuittingFourProfileResponseFamily.baseDecoration
        (family := limit.fourProfileResponseFamily) n).signedAtom reward
          packet.terminal packet.observer := by
  change packet.charge / 4 ≤
    (Fintype.card (QuittingTerminalOutcome (Fin 4)) : ℝ) *
      ((quittingTerminalOutcomeMass reward
            (quittingStoppingLawRectangleDoubleEndpointProfile packet
              (dispatch.subseq (limit.subseq n))) (some packet.terminal) -
          quittingTerminalOutcomeMass reward
            (quittingStoppingLawRectangleSourceResponseProfile packet
              (dispatch.subseq (limit.subseq n))) (some packet.terminal)) *
        reward packet.terminal packet.observer)
  simpa only [quittingTerminalPayoffDifferenceAtom,
    quittingTerminalOutcomeReward] using dispatch.atom_bound (limit.subseq n)

theorem fourProfile_observerDebt_tendsto_zero
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    Tendsto (fun n ↦
      (QuittingFourProfileResponseFamily.baseDecoration
        (family := limit.fourProfileResponseFamily) n).observerDebt packet.observer)
      atTop (nhds 0) := by
  change Tendsto (fun n ↦ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (quittingStoppingLawRectangleDoubleEndpointProfile packet
        (dispatch.subseq (limit.subseq n)))) packet.observer) atTop (nhds 0)
  have hzero := packet.observer_debt_tendsto_zero.comp
    (dispatch.subseq_strictMono.comp
      limit.subseq_strictMono).tendsto_atTop
  change Tendsto (fun n ↦ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward
      (Function.update
        (Function.update
          (frontier.source (packet.rank (dispatch.subseq (limit.subseq n))))
          packet.mover.1
          (frontier.replacement packet.mover
            (packet.rank (dispatch.subseq (limit.subseq n)))))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime (dispatch.subseq (limit.subseq n))))))
    packet.observer) atTop (nhds 0) at hzero
  exact hzero

/-- A further common compact subsequence of the four literal profiles carries
the response atom, actual replacement gain, and vanishing observer debt at one
joint limit. -/
theorem exists_convergentFourProfilePassport
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch) :
    ∃ subseq : ℕ → ℕ, ∃ _hsubseq : StrictMono subseq,
      Nonempty (QuittingFourProfileResponseFamily.ConvergentFourProfilePassport
        (limit.fourProfileResponseFamily.reindex subseq)) := by
  let family := limit.fourProfileResponseFamily
  have hmem : ∀ n,
      QuittingFourProfileResponseFamily.baseDecoration (family := family) n ∈
        QuittingFourProfileResponseFamily.prefixOrbitAmbient (reward := reward) :=
    fun n ↦ QuittingFourProfileResponseFamily.rawDecoration_mem_ambient family n []
  obtain ⟨cluster, hcluster, subseq, hsubseq, htendsto⟩ :=
    (QuittingFourProfileResponseFamily.prefixOrbitAmbient_isCompact
      (reward := reward)).tendsto_subseq hmem
  have hresponse : cluster.response = dispatch.cluster := by
    have hleft :=
      (continuous_fst.comp continuous_fst).tendsto cluster |>.comp htendsto
    have hright := limit.endpoint_tendsto.comp hsubseq.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  have hsibling : cluster.sibling = limit.comparison := by
    have hleft :=
      (continuous_snd.comp continuous_fst).tendsto cluster |>.comp htendsto
    have hright := limit.comparison_tendsto.comp hsubseq.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  have hobserver : cluster.observerDebt packet.observer = 0 := by
    have hleft :=
      (QuittingFourProfileResponseDecoration.continuous_observerDebt
        packet.observer).tendsto cluster |>.comp htendsto
    have hright := limit.fourProfile_observerDebt_tendsto_zero.comp
      hsubseq.tendsto_atTop
    exact tendsto_nhds_unique hleft hright
  have hresponseDebt : 0 < cluster.responseDebt := by
    rw [QuittingFourProfileResponseDecoration.responseDebt, hresponse]
    exact frontier.base_positive.trans_le
      (frontier.base_minimum dispatch.cluster.1
        (terminalSemanticLawCarrier_fst_mem_carrier dispatch.cluster
          dispatch.cluster_mem))
  have hsignedAtom : 0 <
      cluster.signedAtom reward packet.terminal packet.observer := by
    have hlimitAtom :=
      (QuittingFourProfileResponseDecoration.continuous_signedAtom
        (reward := reward) packet.terminal packet.observer).tendsto cluster
        |>.comp htendsto
    have hbound : Filter.Eventually (fun n ↦
        packet.charge / 4 ≤
          (QuittingFourProfileResponseFamily.baseDecoration
            (family := family) (subseq n)).signedAtom reward
              packet.terminal packet.observer) atTop :=
      Eventually.of_forall fun n ↦ limit.fourProfile_signedAtom_lower (subseq n)
    have hle : packet.charge / 4 ≤
        cluster.signedAtom reward packet.terminal packet.observer :=
      ge_of_tendsto hlimitAtom hbound
    exact (div_pos packet.charge_pos (by norm_num)).trans_le hle
  have hactualGain : 0 < cluster.actualGain packet.mover.1 := by
    have hleft :=
      (QuittingFourProfileResponseDecoration.continuous_actualGain
        packet.mover.1).tendsto cluster |>.comp htendsto
    have hright := limit.fourProfile_actualGain_tendsto_baseDebt.comp
      hsubseq.tendsto_atTop
    have heq := tendsto_nhds_unique hleft hright
    rw [heq]
    exact (frontier.positiveDebtSupport_iff packet.mover.1).1
      packet.mover.property
  refine ⟨subseq, hsubseq, ⟨{
    limit := cluster
    tendsto_base := by
      change Tendsto (family.baseDecoration ∘ subseq) atTop (nhds cluster)
      exact htendsto
    observerDebt_eq_zero := hobserver
    responseDebt_pos := hresponseDebt
    signedAtom_pos := hsignedAtom
    actualGain_pos := hactualGain
  }⟩⟩

/-- Complete four-profile descendant-slice landing from one literal rectangle
joint limit in the Fin4 hard residual. -/
structure QuittingFourProfileDescendantSliceLanding
    {bound : ℝ}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (_residual : FinFourQuantitativeFullSupportHardResidual reward bound) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  passport : QuittingFourProfileResponseFamily.ConvergentFourProfilePassport
    (limit.fourProfileResponseFamily.reindex subseq)
  atomDensity : ℝ
  gainDensity : ℝ
  atomDensity_pos : 0 < atomDensity
  gainDensity_pos : 0 < gainDensity
  point : QuittingFourProfileResponseDecoration (Fin 4)
  point_mem : point ∈
    QuittingFourProfileResponseFamily.normalizedDescendantSlice
      (limit.fourProfileResponseFamily.reindex subseq) atomDensity gainDensity
  point_minimizes : ∀ candidate ∈
      QuittingFourProfileResponseFamily.normalizedDescendantSlice
        (limit.fourProfileResponseFamily.reindex subseq) atomDensity gainDensity,
    point.responseDebt ≤ candidate.responseDebt
  baseDebt_le_pointDebt :
    quittingTerminalSemanticDebtSum frontier.base ≤ point.responseDebt
  pointDebt_le_clusterDebt : point.responseDebt ≤
    quittingTerminalSemanticDebtSum dispatch.cluster.1
  observerDebt_eq_zero : point.observerDebt packet.observer = 0
  signedAtom_lower : atomDensity * point.responseDebt ≤
    point.signedAtom reward packet.terminal packet.observer
  actualGain_lower : gainDensity * point.responseDebt ≤
    point.actualGain packet.mover.1
  exactRoot_iff_allContinue : ∀ root : Fin 4 → PMF Bool,
    IsεQuittingRootNash reward point.response.1.2 0 root ↔
      root = (quittingAllContinueRoot : Fin 4 → PMF Bool)
  minimumLanding_or_strictPort :
    (point.responseDebt = quittingTerminalSemanticDebtSum frontier.base ∧
      0 < quittingTerminalTotalOpponentIncidenceMass packet.observer
        point.response.2 ∧
      Nonempty (QuittingLawTightResetRigidChamber reward point.response
        point.response point.response frontier.base)) ∨
    quittingTerminalSemanticDebtSum frontier.base < point.responseDebt

/-- The literal rectangle profiles, a further common compact subsequence, and
the hard-residual minimum classification produce the exhaustive minimum
reset-rigid versus strictly off-minimum descendant-neutral landing. -/
theorem exists_fourProfileDescendantSliceLanding
    {bound : ℝ}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (QuittingFourProfileDescendantSliceLanding limit residual) := by
  obtain ⟨subseq, hsubseq, ⟨passport⟩⟩ :=
    limit.exists_convergentFourProfilePassport
  let family := limit.fourProfileResponseFamily.reindex subseq
  let atomDensity :=
    passport.limit.signedAtom reward packet.terminal packet.observer /
      (2 * passport.limit.responseDebt)
  let gainDensity := passport.limit.actualGain packet.mover.1 /
    (2 * passport.limit.responseDebt)
  have hdebtNe : passport.limit.responseDebt ≠ 0 :=
    ne_of_gt passport.responseDebt_pos
  have hatomDensityPos : 0 < atomDensity := by
    exact div_pos passport.signedAtom_pos
      (mul_pos (by norm_num) passport.responseDebt_pos)
  have hgainDensityPos : 0 < gainDensity := by
    exact div_pos passport.actualGain_pos
      (mul_pos (by norm_num) passport.responseDebt_pos)
  have hatomStrict : atomDensity * passport.limit.responseDebt <
      passport.limit.signedAtom reward packet.terminal packet.observer := by
    have heq : atomDensity * passport.limit.responseDebt =
        passport.limit.signedAtom reward packet.terminal packet.observer / 2 := by
      dsimp only [atomDensity]
      field_simp [hdebtNe]
    rw [heq]
    exact half_lt_self passport.signedAtom_pos
  have hgainStrict : gainDensity * passport.limit.responseDebt <
      passport.limit.actualGain packet.mover.1 := by
    have heq : gainDensity * passport.limit.responseDebt =
        passport.limit.actualGain packet.mover.1 / 2 := by
      dsimp only [gainDensity]
      field_simp [hdebtNe]
    rw [heq]
    exact half_lt_self passport.actualGain_pos
  have hpassportMem :=
    ConvergentFourProfilePassport.limit_mem_normalizedDescendantSlice family
      passport atomDensity gainDensity hatomStrict hgainStrict
  obtain ⟨point, hpoint, hmin⟩ :=
    QuittingFourProfileResponseFamily.exists_minimum_normalizedDescendantSlice
      family atomDensity gainDensity ⟨passport.limit, hpassportMem⟩
  have hpointCarrier :=
    QuittingFourProfileResponseFamily.response_semantic_mem_carrier family
      hpoint.1
  have hbaseLe : quittingTerminalSemanticDebtSum frontier.base ≤
      point.responseDebt := frontier.base_minimum point.response.1 hpointCarrier
  have hpointLe : point.responseDebt ≤
      passport.limit.responseDebt := hmin passport.limit hpassportMem
  have hpassportResponse : passport.limit.response = dispatch.cluster := by
    have hleft :=
      (continuous_fst.comp continuous_fst).tendsto passport.limit |>.comp
        passport.tendsto_base
    have hright := limit.endpoint_tendsto.comp
      (hsubseq.tendsto_atTop)
    exact tendsto_nhds_unique hleft hright
  have hpointLeCluster : point.responseDebt ≤
      quittingTerminalSemanticDebtSum dispatch.cluster.1 := by
    change quittingTerminalSemanticDebtSum point.response.1 ≤
      quittingTerminalSemanticDebtSum passport.limit.response.1 at hpointLe
    rw [hpassportResponse] at hpointLe
    exact hpointLe
  have hroot : ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward point.response.1.2 0 root ↔
        root = (quittingAllContinueRoot : Fin 4 → PMF Bool) :=
    QuittingFourProfileResponseFamily.minimum_normalizedDescendantSlice_isZeroNash_iff_allContinue
      family frontier.base frontier.base_minimum frontier.base_positive
        atomDensity gainDensity point hpoint hmin
  have hlanding :
      (point.responseDebt = quittingTerminalSemanticDebtSum frontier.base ∧
        0 < quittingTerminalTotalOpponentIncidenceMass packet.observer
          point.response.2 ∧
        Nonempty (QuittingLawTightResetRigidChamber reward point.response
          point.response point.response frontier.base)) ∨
      quittingTerminalSemanticDebtSum frontier.base < point.responseDebt := by
    rcases hbaseLe.eq_or_lt with heq | hlt
    · left
      have hpointLaw : point.response ∈
          quittingTerminalSemanticLawCarrier reward := by
        have hambient :=
          QuittingFourProfileResponseFamily.prefixOrbitCarrier_subset_ambient
            family hpoint.1
        exact hambient.1.1
      have hpointMinimum : ∀ candidate ∈
          quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum point.response.1 ≤
            quittingTerminalSemanticDebtSum candidate := by
        intro candidate hcandidate
        calc
          quittingTerminalSemanticDebtSum point.response.1 =
              point.responseDebt := rfl
          _ = quittingTerminalSemanticDebtSum frontier.base := heq.symm
          _ ≤ quittingTerminalSemanticDebtSum candidate :=
            frontier.base_minimum candidate hcandidate
      have hincidence :=
        totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero
          reward bound residual point.response hpointLaw hpointMinimum
            packet.observer hpoint.2.1
      let minimum : IsQuittingLawTightCapNashSaturationMinimum reward
          point.response point.response := {
        mem := quittingLawTightCapNashSaturationHull_origin_mem reward
          point.response
        debt_le := by
          intro candidate hcandidate
          exact hpointMinimum candidate.1
            (terminalSemanticLawCarrier_fst_mem_carrier candidate
              (quittingLawTightCapNashSaturationHull_subset_carrier reward
                point.response hpointLaw hcandidate))
      }
      have hchamber := exists_quittingLawTightResetRigidChamber
        residual.witness frontier.base frontier.base_minimum
          frontier.base_positive point.response point.response point.response
            hpointLaw minimum minimum.minimum_mem_face packet.observer
              hpoint.2.1 hincidence
      exact ⟨heq.symm, hincidence, hchamber⟩
    · exact Or.inr hlt
  exact ⟨{
    subseq := subseq
    subseq_strictMono := hsubseq
    passport := passport
    atomDensity := atomDensity
    gainDensity := gainDensity
    atomDensity_pos := hatomDensityPos
    gainDensity_pos := hgainDensityPos
    point := point
    point_mem := hpoint
    point_minimizes := hmin
    baseDebt_le_pointDebt := hbaseLe
    pointDebt_le_clusterDebt := hpointLeCluster
    observerDebt_eq_zero := hpoint.2.1
    signedAtom_lower := hpoint.2.2.1
    actualGain_lower := hpoint.2.2.2
    exactRoot_iff_allContinue := hroot
    minimumLanding_or_strictPort := hlanding
  }⟩

end QuittingStoppingLawRectangleJointAtomLimit

end GameTheory
