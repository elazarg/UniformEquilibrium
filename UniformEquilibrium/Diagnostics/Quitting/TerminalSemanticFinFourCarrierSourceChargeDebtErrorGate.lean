/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.MinimumFiberSupportDrop
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation
import UniformEquilibrium.Quitting.Paths.StrictAllContinueBasinSuccessorPath

/-!
# Carrier-source charge versus debt or aggregate root error

For a hypothetical four-player counterexample, fix a positive absorption
threshold.  A successor path beginning at the prescribed payoff of an actual
terminal-semantic carrier pair cannot contain a root above that threshold
unless either its source debt is uniformly above the global minimum or its
aggregate declared root-Nash error is uniformly positive.

The proof combines the compact linear basin around the whole minimum carrier
fiber with a compactness moat which turns proximity in debt into proximity to
that fiber.  The path is oriented outward from its carrier source, exactly as
in `successorPath_mem_and_absorptionSum_le_of_linearDefect`.

The final theorem decodes paths in the full punishment-floor admissible
charged relation.  It still requires the path source payoff to be identified
with an actual semantic carrier pair; no such identification is inferred from
floor admissibility alone.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.ChargedPathBudget Math.Probability
open Math.ProbabilityMassFunction Math.PMFProduct

/-- Carrier compactness prices failure to lie within half of a prescribed
metric collar around the complete minimum-debt fiber. -/
theorem exists_pos_carrierDebtMoat_of_infDist_minimumFiber
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (K : Set (Payoff ι)) {rho : ℝ}
    (_hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hK : K = Prod.fst ''
      quittingTerminalSemanticMinimumFiber reward base)
    (hrho : 0 < rho) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair <
            quittingTerminalSemanticDebtSum base + eta →
          Metric.infDist pair.1 K < rho / 2 := by
  let far : Set (QuittingTerminalSemanticPair ι) :=
    quittingTerminalSemanticCarrier reward ∩
      {pair | rho / 2 ≤ Metric.infDist pair.1 K}
  have hfarCompact : IsCompact far := by
    apply (quittingTerminalSemanticCarrier_isCompact reward).inter_right
    exact isClosed_le continuous_const
      ((Metric.continuous_infDist_pt K).comp continuous_fst)
  by_cases hfarNonempty : far.Nonempty
  · obtain ⟨selected, hselected, hselectedMin⟩ :=
      hfarCompact.exists_isMinOn hfarNonempty
        continuous_quittingTerminalSemanticDebtSum.continuousOn
    have hbaseLe : quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum selected :=
      hminimum selected hselected.1
    have hdebtNe : quittingTerminalSemanticDebtSum base ≠
        quittingTerminalSemanticDebtSum selected := by
      intro heq
      have hselectedFiber : selected ∈
          quittingTerminalSemanticMinimumFiber reward base :=
        ⟨hselected.1, heq.symm⟩
      have hselectedK : selected.1 ∈ K := by
        rw [hK]
        exact ⟨selected, hselectedFiber, rfl⟩
      have hzero := Metric.infDist_zero_of_mem hselectedK
      have hselectedFar := hselected.2
      change rho / 2 ≤ Metric.infDist selected.1 K at hselectedFar
      linarith
    have hdebtLt : quittingTerminalSemanticDebtSum base <
        quittingTerminalSemanticDebtSum selected :=
      lt_of_le_of_ne hbaseLe hdebtNe
    let eta := (quittingTerminalSemanticDebtSum selected -
      quittingTerminalSemanticDebtSum base) / 2
    have heta : 0 < eta := by
      dsimp only [eta]
      linarith
    refine ⟨eta, heta, ?_⟩
    intro pair hpair hnear
    by_contra hnotClose
    have hpairFar : pair ∈ far := by
      refine ⟨hpair, ?_⟩
      exact le_of_not_gt hnotClose
    have hselectedLe := hselectedMin hpairFar
    change quittingTerminalSemanticDebtSum selected ≤
      quittingTerminalSemanticDebtSum pair at hselectedLe
    dsimp only [eta] at hnear
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro pair hpair _hnear
    apply lt_of_not_ge
    intro hfar
    exact hfarNonempty ⟨pair, hpair, hfar⟩

/-- The reusable quantitative data for the carrier-source gate. -/
structure FinFourCarrierSourceChargeDebtErrorGate
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (chargeThreshold : ℝ) where
  base : QuittingTerminalSemanticPair (Fin 4)
  K : Set (Payoff (Fin 4))
  N : Set (Payoff (Fin 4))
  c : ℝ
  C : ℝ
  rho : ℝ
  eta : ℝ
  errorFloor : ℝ
  base_mem : base ∈ quittingTerminalSemanticCarrier reward
  base_minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum base ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_projection : K = Prod.fst ''
    quittingTerminalSemanticMinimumFiber reward base
  c_pos : 0 < c
  C_pos : 0 < C
  rho_pos : 0 < rho
  eta_pos : 0 < eta
  errorFloor_pos : 0 < errorFloor
  chargeThreshold_pos : 0 < chargeThreshold
  reward_bound : ∀ S player, |reward S player| ≤ C
  tail_bound : ∀ tail ∈ N, ∀ player, |tail player| ≤ C
  thickening_subset : Metric.thickening rho K ⊆ N
  linear_defect : ∀ tail ∈ N, ∀ root : Fin 4 → PMF Bool,
    c * quittingRootAbsorptionMass root ≤
      quittingRootTotalNashDefect reward tail root
  source_close : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum pair <
        quittingTerminalSemanticDebtSum base + eta →
      Metric.infDist pair.1 K < rho / 2
  errorFloor_le_tube : errorFloor ≤ c * rho / (16 * C)
  errorFloor_le_charge : errorFloor ≤ c * chargeThreshold / 4

/-- No-uniform-payoff data produces the fixed constants in the source gate
for every positive charge threshold. -/
theorem exists_finFour_carrierSourceChargeDebtErrorGate_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {chargeThreshold : ℝ} (hchargeThreshold : 0 < chargeThreshold) :
    Nonempty (FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold) := by
  obtain ⟨base, K, N, c, C, rho, hbase, hminimum, _hpositive, hK,
      _hKcompact, _hKnonempty, _hNopen, _hKN, _hNbounded, hc, hC, hrho,
      hreward, htail, hthick, hlinear, _hvanishing⟩ :=
    exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff
      reward hno
  obtain ⟨eta, heta, hclose⟩ :=
    exists_pos_carrierDebtMoat_of_infDist_minimumFiber
      reward base K hbase hminimum hK hrho
  let errorFloor := min (c * rho / (16 * C))
    (c * chargeThreshold / 4)
  have htubePos : 0 < c * rho / (16 * C) := by positivity
  have hchargePos : 0 < c * chargeThreshold / 4 := by positivity
  have herrorFloor : 0 < errorFloor :=
    lt_min htubePos hchargePos
  exact ⟨{
    base := base
    K := K
    N := N
    c := c
    C := C
    rho := rho
    eta := eta
    errorFloor := errorFloor
    base_mem := hbase
    base_minimum := hminimum
    minimum_projection := hK
    c_pos := hc
    C_pos := hC
    rho_pos := hrho
    eta_pos := heta
    errorFloor_pos := herrorFloor
    chargeThreshold_pos := hchargeThreshold
    reward_bound := hreward
    tail_bound := htail
    thickening_subset := hthick
    linear_defect := hlinear
    source_close := hclose
    errorFloor_le_tube := min_le_left _ _
    errorFloor_le_charge := min_le_right _ _ }⟩

namespace QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

/-- A full-replacement sequence converging to a strictly off-minimum cluster
eventually stays at least half of that cluster's excess debt above the global
minimum.  These are literal semantic pairs of the actual reset profiles. -/
theorem eventually_base_add_half_clusterDebtExcess_le_fullReplacementDebt
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (endpoint :
      QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster
        frontier mover)
    (hseparated : quittingTerminalSemanticDebtSum frontier.base <
      quittingTerminalSemanticDebtSum endpoint.cluster) :
    ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebtSum frontier.base +
          (quittingTerminalSemanticDebtSum endpoint.cluster -
            quittingTerminalSemanticDebtSum frontier.base) / 2 ≤
        quittingTerminalSemanticDebtSum
          (frontier.fullReplacementPair mover (endpoint.subseq rank)) := by
  have htendsto : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (frontier.fullReplacementPair mover (endpoint.subseq rank)))
      atTop (nhds (quittingTerminalSemanticDebtSum endpoint.cluster)) :=
    continuous_quittingTerminalSemanticDebtSum.tendsto endpoint.cluster |>.comp
      endpoint.fullReplacement_tendsto
  have hlower : quittingTerminalSemanticDebtSum frontier.base +
      (quittingTerminalSemanticDebtSum endpoint.cluster -
        quittingTerminalSemanticDebtSum frontier.base) / 2 <
      quittingTerminalSemanticDebtSum endpoint.cluster := by
    linarith
  filter_upwards [htendsto.eventually (Ioi_mem_nhds hlower)] with rank hrank
  exact hrank.le

end QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster

namespace FinFourCarrierSourceChargeDebtErrorGate

/-- A fixed-charge successor path pays either the carrier-source debt moat or
the aggregate declared root-error floor. -/
theorem debt_or_error
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {chargeThreshold : ℝ}
    (gate : FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold)
    (source : QuittingTerminalSemanticPair (Fin 4))
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (value : ℕ → Payoff (Fin 4))
    (root : ℕ → Fin 4 → PMF Bool) (error : ℕ → ℝ)
    (length : ℕ)
    (hstart : value 0 = source.1)
    (herrorNonneg : ∀ time < length, 0 ≤ error time)
    (hnash : ∀ time < length,
      IsεQuittingRootNash reward (value time) (error time) (root time))
    (hsuccessor : ∀ time < length,
      value (time + 1) =
        quittingRootSuccessorPayoff reward (value time) (root time))
    (hcharged : ∃ time < length,
      chargeThreshold ≤ quittingRootAbsorptionMass (root time)) :
    quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
        quittingTerminalSemanticDebtSum source ∨
      gate.errorFloor ≤
        ∑ time ∈ Finset.range length, error time := by
  by_cases hdebt : quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
      quittingTerminalSemanticDebtSum source
  · exact Or.inl hdebt
  · right
    apply le_of_not_gt
    intro herrorSmall
    have hsourceClose := gate.source_close source hsource (by
      exact lt_of_not_ge hdebt)
    have hbudget : (2 * gate.C * Fintype.card (Fin 4) / gate.c) *
        (∑ time ∈ Finset.range length, error time) < gate.rho / 2 := by
      have herrorTube : (∑ time ∈ Finset.range length, error time) <
          gate.c * gate.rho / (16 * gate.C) :=
        herrorSmall.trans_le gate.errorFloor_le_tube
      norm_num [Fintype.card_fin] at ⊢
      have hcNe : gate.c ≠ 0 := ne_of_gt gate.c_pos
      have hCNe : gate.C ≠ 0 := ne_of_gt gate.C_pos
      have hcoefficientPos : 0 < 2 * gate.C * 4 / gate.c := by
        have hnumerator : 0 < 2 * gate.C * 4 := by
          nlinarith [gate.C_pos]
        exact div_pos hnumerator gate.c_pos
      calc
        (2 * gate.C * 4 / gate.c) *
            (∑ time ∈ Finset.range length, error time) <
          (2 * gate.C * 4 / gate.c) *
            (gate.c * gate.rho / (16 * gate.C)) :=
          mul_lt_mul_of_pos_left herrorTube hcoefficientPos
        _ = gate.rho / 2 := by field_simp; ring
    have hpath :=
      successorPath_mem_and_absorptionSum_le_of_linearDefect
        reward gate.K gate.N value root error length gate.C_pos gate.c_pos
          gate.rho_pos gate.reward_bound gate.tail_bound gate.linear_defect
          (by
            rw [gate.minimum_projection]
            exact (quittingTerminalSemanticMinimumFiber_nonempty
              reward gate.base gate.base_mem).image Prod.fst)
          gate.thickening_subset (by simpa [hstart] using hsourceClose)
          herrorNonneg hnash hsuccessor hbudget
    obtain ⟨stage, hstage, hstageCharge⟩ := hcharged
    have hchargeSum : chargeThreshold ≤
        ∑ time ∈ Finset.range length,
          quittingRootAbsorptionMass (root time) := by
      exact hstageCharge.trans (Finset.single_le_sum
        (fun time _ ↦ quittingRootAbsorptionMass_nonneg (root time))
        (Finset.mem_range.mpr hstage))
    have habsorptionError := hchargeSum.trans hpath.2.1
    have herrorCharge :
        (∑ time ∈ Finset.range length, error time) <
          gate.c * chargeThreshold / 4 :=
      herrorSmall.trans_le gate.errorFloor_le_charge
    have hcNe : gate.c ≠ 0 := ne_of_gt gate.c_pos
    norm_num [Fintype.card_fin] at habsorptionError
    have hcoefficientPos : 0 < 4 / gate.c := by
      exact div_pos (by norm_num) gate.c_pos
    have hstrict : 4 / gate.c *
        (∑ time ∈ Finset.range length, error time) <
          chargeThreshold := by
      calc
        4 / gate.c * (∑ time ∈ Finset.range length, error time) <
            4 / gate.c * (gate.c * chargeThreshold / 4) :=
          mul_lt_mul_of_pos_left herrorCharge hcoefficientPos
        _ = chargeThreshold := by field_simp
    exact (not_lt_of_ge habsorptionError) hstrict

/-- Exact successor paths have zero aggregate declared error, so a charged
path from an actual carrier source must start above the debt moat. -/
theorem debt_of_exactPath
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {chargeThreshold : ℝ}
    (gate : FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold)
    (source : QuittingTerminalSemanticPair (Fin 4))
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (value : ℕ → Payoff (Fin 4))
    (root : ℕ → Fin 4 → PMF Bool) (length : ℕ)
    (hstart : value 0 = source.1)
    (hnash : ∀ time < length,
      IsεQuittingRootNash reward (value time) 0 (root time))
    (hsuccessor : ∀ time < length,
      value (time + 1) =
        quittingRootSuccessorPayoff reward (value time) (root time))
    (hcharged : ∃ time < length,
      chargeThreshold ≤ quittingRootAbsorptionMass (root time)) :
    quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
      quittingTerminalSemanticDebtSum source := by
  have hgate := gate.debt_or_error source hsource value root
    (fun _ ↦ 0) length hstart (by simp) hnash hsuccessor hcharged
  rcases hgate with hdebt | herror
  · exact hdebt
  · simp only [Finset.sum_const_zero] at herror
    exact False.elim ((not_lt_of_ge herror) gate.errorFloor_pos)

/-- Actual-source adapter for a path in the full punishment-floor admissible
charged relation.  A positive total path charge is enough; a single edge of
that charge is a special case. -/
theorem debt_of_punishmentFloorAdmissiblePath
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {chargeThreshold : ℝ}
    (gate : FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold)
    (sourcePair : QuittingTerminalSemanticPair (Fin 4))
    (hsourcePair : sourcePair ∈ quittingTerminalSemanticCarrier reward)
    (source target : QuittingPunishmentFloorAdmissibleState reward)
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target)
    (hsource : source.1.1.1 = sourcePair.1)
    (hcharge : chargeThreshold ≤ path.chargeSum) :
    quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
      quittingTerminalSemanticDebtSum sourcePair := by
  let cert :=
    QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix path
  have hstart : cert.value 0 = sourcePair.1 := by
    change QuittingPunishmentFloorBoxPath.value
        (QuittingPunishmentFloorAdmissibleChargedRelation.pathToBoxPath path)
        0 = sourcePair.1
    rw [QuittingPunishmentFloorBoxPath.value_zero]
    exact hsource
  have hchargedSum : chargeThreshold ≤
      ∑ time ∈ Finset.range cert.horizon,
        quittingRootAbsorptionMass (cert.roots time) := by
    change chargeThreshold ≤ cert.charge
    rw [QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge]
    exact hcharge
  by_contra hnotDebt
  have hsourceClose := gate.source_close sourcePair hsourcePair
    (lt_of_not_ge hnotDebt)
  have hbudget : (2 * gate.C * Fintype.card (Fin 4) / gate.c) *
      (∑ _time ∈ Finset.range cert.horizon, (0 : ℝ)) <
        gate.rho / 2 := by
    simp only [Finset.sum_const_zero, mul_zero]
    linarith [gate.rho_pos]
  have hpath :=
    successorPath_mem_and_absorptionSum_le_of_linearDefect
      reward gate.K gate.N cert.value cert.roots (fun _ ↦ 0)
        cert.horizon gate.C_pos gate.c_pos gate.rho_pos gate.reward_bound
        gate.tail_bound gate.linear_defect
        (by
          rw [gate.minimum_projection]
          exact (quittingTerminalSemanticMinimumFiber_nonempty
            reward gate.base gate.base_mem).image Prod.fst)
        gate.thickening_subset (by simpa [hstart] using hsourceClose)
        (by simp) cert.exactNash cert.policy hbudget
  have hzero := hchargedSum.trans hpath.2.1
  simp only [Finset.sum_const_zero, mul_zero] at hzero
  exact (not_lt_of_ge hzero) gate.chargeThreshold_pos

/-- Relation-level high-charge adapter in the exact shape used by the checked
payoff-near-return consumer.  The semantic source identification remains an
explicit hypothesis. -/
theorem debt_of_punishmentFloorAdmissiblePath_highCharge
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {chargeThreshold : ℝ}
    (gate : FinFourCarrierSourceChargeDebtErrorGate
      reward chargeThreshold)
    (sourcePair : QuittingTerminalSemanticPair (Fin 4))
    (hsourcePair : sourcePair ∈ quittingTerminalSemanticCarrier reward)
    (source target : QuittingPunishmentFloorAdmissibleState reward)
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target)
    (hsource : source.1.1.1 = sourcePair.1)
    (hhigh : 0 < path.highChargeCount chargeThreshold) :
    quittingTerminalSemanticDebtSum gate.base + gate.eta ≤
      quittingTerminalSemanticDebtSum sourcePair := by
  have hcountOne : (1 : ℝ) ≤ path.highChargeCount chargeThreshold := by
    exact_mod_cast (show 1 ≤ path.highChargeCount chargeThreshold by omega)
  have hthresholdCount : chargeThreshold ≤
      (path.highChargeCount chargeThreshold : ℝ) * chargeThreshold := by
    nlinarith [gate.chargeThreshold_pos]
  have hcharge : chargeThreshold ≤ path.chargeSum :=
    hthresholdCount.trans
      (ChargedRelation.Path.highChargeCount_mul_le_chargeSum
        chargeThreshold path)
  exact gate.debt_of_punishmentFloorAdmissiblePath sourcePair hsourcePair
    source target path hsource hcharge

end FinFourCarrierSourceChargeDebtErrorGate

end GameTheory
