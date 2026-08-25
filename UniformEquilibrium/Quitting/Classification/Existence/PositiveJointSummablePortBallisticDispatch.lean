/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorSummablePortLabel
import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointSummablePortPhantomReduction

/-!
# Ballistic dispatch of a positive-joint summable port

Failure of the well-supported absorbing branch gives one uniform scale at
which every positively charged finite segment of an exact punishment-floor
orbit must move.  A positive-charge summable port which returns to its
initial annotation therefore gives the well-supported branch.  More
generally, a summable port either has literal zero charge and is the constant
all-Continue orbit, or its limiting displacement carries a fixed signed
terminal label.

The source specialization retains the reached endpoint and its no-sure-exit
proof.  The formal port limit is used only as a Bellman annotation; it is not
identified with the payoff of an executable all-Never profile.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingPunishmentFloorInfiniteOrbit

/-- Maximum coordinate movement over one finite segment. -/
def segmentDisplacement [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (start horizon : ℕ) : ℝ :=
  QuittingBoundaryHolonomy.finitePlayerMax fun who ↦
    |orbit.value (start + horizon) who - orbit.value start who|

/-- One positive ballistic scale, uniform over all finite segments of an
exact punishment-floor orbit. -/
structure BallisticCertificate [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) where
  scale : ℝ
  scale_pos : 0 < scale
  segment_strict : ∀ start horizon,
    0 < (orbit.toFiniteSegment start horizon).charge →
      scale * ((orbit.toFiniteSegment start horizon).charge /
          (1 + (orbit.toFiniteSegment start horizon).charge)) <
        orbit.segmentDisplacement start horizon

/-- One single-seam lasso supplies a completely absorbing support-local
sequence at twice its lasso error. -/
theorem nonempty_wellSupportedAbsorbingSequenceAt_of_singleSeamProjectiveLasso
    [Nonempty iota] {error : ℝ}
    (hlasso : ∃ K : ℕ,
      Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error)) :
    ∃ roots : ℕ → iota → PMF Bool,
      IsCompletelyAbsorbing roots ∧
        IsQuittingRootSequenceSupportApproxNash reward roots (2 * error) := by
  obtain ⟨_K, ⟨lasso⟩⟩ := hlasso
  obtain ⟨plan, hsupport, hdiverges, _hrational⟩ :=
    lasso.exists_supportRationalDivergentPath
  have hcomplete : IsCompletelyAbsorbing plan := by
    have hdiverges' : ¬Summable (fun time ↦
        quittingRootAbsorptionMass (plan time)) := by
      change ¬Summable (fun time ↦
        quittingRootAbsorptionMass (plan time)) at hdiverges
      exact hdiverges
    have hzero :=
      tendsto_zero_quittingJointSurvivalWeight_of_not_summable_absorption
        plan 0 (by simpa only [zero_add] using hdiverges')
    have heq : quittingJointSurvivalWeight plan 0 =
        quittingSurvivalPrefix plan := by
      funext fuel
      simpa using
        (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix plan 0 fuel)
    unfold IsCompletelyAbsorbing
    rw [← heq]
    exact hzero
  exact ⟨plan, hcomplete, hsupport⟩

/-- Failure of branch `S.3` forces one uniform ballistic displacement scale
on every positively charged finite segment of every supplied exact floor
orbit. -/
theorem nonempty_ballisticCertificate_of_not_wellSupported
    [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (hfailure : ¬QuittingWellSupportedAbsorbingSequenceExistence reward) :
    Nonempty orbit.BallisticCertificate := by
  rw [QuittingWellSupportedAbsorbingSequenceExistence] at hfailure
  push Not at hfailure
  obtain ⟨delta, hdelta, hbad⟩ := hfailure
  let scale := delta / 2
  have hscale : 0 < scale := by
    dsimp only [scale]
    linarith
  refine ⟨{
    scale := scale
    scale_pos := hscale
    segment_strict := ?_ }⟩
  intro start horizon hcharge
  let segment := orbit.toFiniteSegment start horizon
  let ratio := segment.charge / (1 + segment.charge)
  have hratio : 0 < ratio := by
    dsimp only [ratio]
    apply div_pos hcharge
    linarith
  by_contra hnot
  have hdisplacement : orbit.segmentDisplacement start horizon ≤
      scale * ratio := le_of_not_gt hnot
  have hclose : ∀ who,
      |segment.value 0 who - segment.value segment.horizon who| ≤
        scale * ratio := by
    intro who
    have hcoordinate :
        |orbit.value (start + horizon) who - orbit.value start who| ≤
          orbit.segmentDisplacement start horizon :=
      by simpa only [segmentDisplacement] using
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun player ↦
            |orbit.value (start + horizon) player - orbit.value start player|)
          who)
    have hvalueZero : segment.value 0 = orbit.value start := by
      simp [segment]
    have hvalueEnd : segment.value segment.horizon =
        orbit.value (start + horizon) := by
      rfl
    rw [hvalueZero, hvalueEnd, abs_sub_comm]
    exact hcoordinate.trans hdisplacement
  obtain ⟨_K, hlasso⟩ :=
    exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn
      segment segment.charge (scale * ratio) scale hcharge le_rfl
        (mul_nonneg hscale.le hratio.le) le_rfl hclose
  obtain ⟨roots, hcomplete, hsupport⟩ :=
    nonempty_wellSupportedAbsorbingSequenceAt_of_singleSeamProjectiveLasso
      ⟨_, hlasso⟩
  have htwice : 2 * scale = delta := by
    dsimp only [scale]
    ring
  exact hbad roots hcomplete (by rwa [htwice] at hsupport)

/-- A positive-charge summable port which returns to its initial annotation
produces single-seam lassos at every accuracy and hence literal branch
`S.3`. -/
theorem SummableChargeAllContinuePort.wellSupported_of_totalAbsorption_pos_of_return
    [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (port : orbit.SummableChargeAllContinuePort)
    (hpositive : 0 < ∑' time,
      quittingRootAbsorptionMass (orbit.roots time))
    (hreturn : port.limit = orbit.value 0) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  apply
    quittingWellSupportedAbsorbingSequenceExistence_of_singleSeamProjectiveLassos
      reward
  intro error herror
  let total := ∑' time, quittingRootAbsorptionMass (orbit.roots time)
  let chargeFloor := total / 2
  have hchargeFloor : 0 < chargeFloor := by
    dsimp only [chargeFloor, total]
    linarith
  have hchargeTendsto : Tendsto orbit.partialAbsorption atTop (nhds total) := by
    change Tendsto (fun horizon ↦ ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (orbit.roots time)) atTop (nhds total)
    exact port.absorption_summable.hasSum.tendsto_sum_nat
  have hvalueTendsto : Tendsto orbit.value atTop (nhds port.limit) :=
    tendsto_pi_nhds.2 port.value_tendsto
  have htarget : 0 < error * (chargeFloor / (1 + chargeFloor)) := by
    positivity
  obtain ⟨chargeStart, hchargeStart⟩ :=
    Metric.tendsto_atTop.1 hchargeTendsto chargeFloor hchargeFloor
  obtain ⟨valueStart, hvalueStart⟩ :=
    Metric.tendsto_atTop.1 hvalueTendsto _ htarget
  let horizon := max chargeStart valueStart
  have hcharge : chargeFloor ≤ orbit.partialAbsorption horizon := by
    have hcloseTotal := hchargeStart horizon (le_max_left _ _)
    rw [Real.dist_eq] at hcloseTotal
    rw [abs_lt] at hcloseTotal
    have hhalf : chargeFloor + chargeFloor = total := by
      dsimp only [chargeFloor]
      ring
    linarith
  have hclose : ∀ who,
      |(orbit.toFinitePrefix horizon).value 0 who -
          (orbit.toFinitePrefix horizon).value
            (orbit.toFinitePrefix horizon).horizon who| ≤
        error * (chargeFloor / (1 + chargeFloor)) := by
    intro who
    have hdist := hvalueStart horizon (le_max_right _ _)
    have hcoordinate := (dist_le_pi_dist (orbit.value horizon) port.limit who).trans_lt
      hdist
    rw [hreturn] at hcoordinate
    simpa [QuittingPunishmentFloorInfiniteOrbit.toFinitePrefix,
      Real.dist_eq, abs_sub_comm] using hcoordinate.le
  exact
    exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn
      (orbit.toFinitePrefix horizon) chargeFloor
        (error * (chargeFloor / (1 + chargeFloor))) error
        hchargeFloor (by simpa using hcharge) (mul_nonneg herror.le (by positivity))
        le_rfl hclose

/-- The limiting displacement of a summable port obeys the same ballistic
lower bound as every finite initial segment. -/
theorem BallisticCertificate.limitDisplacement_lower
    [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (certificate : orbit.BallisticCertificate)
    (port : orbit.SummableChargeAllContinuePort) :
    certificate.scale *
        ((∑' time, quittingRootAbsorptionMass (orbit.roots time)) /
          (1 + ∑' time, quittingRootAbsorptionMass (orbit.roots time))) ≤
      QuittingBoundaryHolonomy.finitePlayerMax fun who ↦
        |port.limit who - orbit.value 0 who| := by
  let total := ∑' time, quittingRootAbsorptionMass (orbit.roots time)
  have htotalNonneg : 0 ≤ total :=
    tsum_nonneg orbit.absorptionMass_nonneg
  have hchargeTendsto : Tendsto orbit.partialAbsorption atTop (nhds total) := by
    change Tendsto (fun horizon ↦ ∑ time ∈ Finset.range horizon,
      quittingRootAbsorptionMass (orbit.roots time)) atTop (nhds total)
    exact port.absorption_summable.hasSum.tendsto_sum_nat
  have hratioTendsto : Tendsto
      (fun horizon ↦ certificate.scale *
        (orbit.partialAbsorption horizon /
          (1 + orbit.partialAbsorption horizon))) atTop
      (nhds (certificate.scale * (total / (1 + total)))) := by
    apply Filter.Tendsto.const_mul certificate.scale
    exact hchargeTendsto.div (tendsto_const_nhds.add hchargeTendsto)
      (by linarith)
  have hvalueTendsto : Tendsto orbit.value atTop (nhds port.limit) :=
    tendsto_pi_nhds.2 port.value_tendsto
  have hcontinuous : Continuous (fun value : Payoff iota ↦
      QuittingBoundaryHolonomy.finitePlayerMax fun who ↦
        |value who - orbit.value 0 who|) := by
    unfold QuittingBoundaryHolonomy.finitePlayerMax
    convert Continuous.finset_sup' (s := Finset.univ)
      Finset.univ_nonempty (fun (who : iota) _hwho ↦
        ((continuous_apply who).sub
          (continuous_const : Continuous
            (fun _value : Payoff iota ↦ orbit.value 0 who))).abs) using 1
    funext value
    rw [Finset.sup'_apply]
    simp only [Pi.sub_apply]
  have hdisplacementTendsto : Tendsto
      (fun horizon ↦ orbit.segmentDisplacement 0 horizon) atTop
      (nhds (QuittingBoundaryHolonomy.finitePlayerMax fun who ↦
        |port.limit who - orbit.value 0 who|)) := by
    have hfunction : (fun horizon ↦ orbit.segmentDisplacement 0 horizon) =
        (fun value : Payoff iota ↦
          QuittingBoundaryHolonomy.finitePlayerMax fun who ↦
            |value who - orbit.value 0 who|) ∘ orbit.value := by
      funext horizon
      simp only [segmentDisplacement, zero_add, Function.comp_apply]
    rw [hfunction]
    exact hcontinuous.continuousAt.tendsto.comp hvalueTendsto
  apply le_of_tendsto_of_tendsto' hratioTendsto hdisplacementTendsto
  intro horizon
  by_cases hcharge : 0 < orbit.partialAbsorption horizon
  · have hstrict := certificate.segment_strict 0 horizon (by
      simpa [QuittingPunishmentFloorInfiniteOrbit.toFiniteSegment,
        QuittingPunishmentFloorFinitePrefix.charge, partialAbsorption] using hcharge)
    simpa [QuittingPunishmentFloorInfiniteOrbit.toFiniteSegment,
      QuittingPunishmentFloorFinitePrefix.charge, partialAbsorption] using hstrict.le
  · have hzero : orbit.partialAbsorption horizon = 0 := by
      exact le_antisymm (le_of_not_gt hcharge)
        (Finset.sum_nonneg fun time _ ↦ orbit.absorptionMass_nonneg time)
    rw [hzero]
    simp only [zero_div, mul_zero]
    have hnonneg : 0 ≤ |orbit.value horizon (Classical.choice inferInstance) -
        orbit.value 0 (Classical.choice inferInstance)| := abs_nonneg _
    exact hnonneg.trans
      (by simpa only [segmentDisplacement, zero_add] using
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun player ↦ |orbit.value horizon player - orbit.value 0 player|)
          (Classical.choice inferInstance)))

/-- Literal rigidity of the zero-total-charge arm. -/
structure SummableChargeZeroRigidity
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (port : orbit.SummableChargeAllContinuePort) where
  totalAbsorption_eq_zero :
    (∑' time, quittingRootAbsorptionMass (orbit.roots time)) = 0
  absorptionMass_eq_zero : ∀ time,
    quittingRootAbsorptionMass (orbit.roots time) = 0
  roots_eq_allContinue : ∀ time,
    orbit.roots time = quittingAllContinueRoot
  value_eq_initial : ∀ time, orbit.value time = orbit.value 0
  limit_eq_initial : port.limit = orbit.value 0

/-- Positive ballistic arm of a summable port, with the canonical reward
bound used by both the signed contribution and coalition-mass inequalities. -/
structure SummableChargePositiveSignedBoundary [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (port : orbit.SummableChargeAllContinuePort)
    (certificate : orbit.BallisticCertificate) where
  totalAbsorption : ℝ
  totalAbsorption_eq : totalAbsorption =
    ∑' time, quittingRootAbsorptionMass (orbit.roots time)
  totalAbsorption_pos : 0 < totalAbsorption
  rho : ℝ
  rho_eq : rho = certificate.scale *
    (totalAbsorption / (1 + totalAbsorption))
  rho_pos : 0 < rho
  displacement : ∃ who,
    rho ≤ |port.limit who - orbit.value 0 who|
  rewardBound_pos : 0 < quittingRewardBound reward
  signedPort : Nonempty (SummableChargeSignedTerminalPort orbit rho
    (quittingRewardBound reward))

/-- Under one ballistic certificate, a summable port has exactly the
zero-charge rigid form or the positive-charge displaced signed-label form. -/
theorem BallisticCertificate.zeroRigidity_or_positiveSignedBoundary
    [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (certificate : orbit.BallisticCertificate)
    (port : orbit.SummableChargeAllContinuePort) :
    Nonempty (SummableChargeZeroRigidity orbit port) ∨
      Nonempty (SummableChargePositiveSignedBoundary orbit port certificate) := by
  let total := ∑' time, quittingRootAbsorptionMass (orbit.roots time)
  have htotalNonneg : 0 ≤ total :=
    tsum_nonneg orbit.absorptionMass_nonneg
  rcases htotalNonneg.eq_or_lt with hzero | hpositive
  · left
    have hzero' : total = 0 := hzero.symm
    have habsorption : ∀ time,
        quittingRootAbsorptionMass (orbit.roots time) = 0 := by
      intro time
      apply le_antisymm
      · have hle := port.absorption_summable.sum_le_tsum
          ({time} : Finset ℕ) (fun other _ ↦ orbit.absorptionMass_nonneg other)
        simpa [total, hzero'] using hle
      · exact orbit.absorptionMass_nonneg time
    have hroots : ∀ time, orbit.roots time = quittingAllContinueRoot := by
      intro time
      apply eq_quittingAllContinueRoot_of_continueMass_eq_one
      unfold quittingRootAbsorptionMass at habsorption
      linarith [habsorption time]
    have hvalue : ∀ time, orbit.value time = orbit.value 0 := by
      intro time
      induction time with
      | zero => rfl
      | succ time ih =>
          rw [orbit.policy time, hroots time,
            quittingRootSuccessorPayoff_allContinueRoot_eq, ih]
    have hlimit : port.limit = orbit.value 0 := by
      funext who
      apply tendsto_nhds_unique (port.value_tendsto who)
      convert tendsto_const_nhds (x := orbit.value 0 who) using 1
      funext time
      exact congrFun (hvalue time) who
    exact ⟨{
      totalAbsorption_eq_zero := hzero'
      absorptionMass_eq_zero := habsorption
      roots_eq_allContinue := hroots
      value_eq_initial := hvalue
      limit_eq_initial := hlimit }⟩
  · right
    let rho := certificate.scale * (total / (1 + total))
    have hrho : 0 < rho := by
      dsimp only [rho]
      exact mul_pos certificate.scale_pos (div_pos hpositive (by linarith))
    have hlimitLower := certificate.limitDisplacement_lower orbit port
    have hdisplacement : ∃ who,
        rho ≤ |port.limit who - orbit.value 0 who| := by
      unfold QuittingBoundaryHolonomy.finitePlayerMax at hlimitLower
      obtain ⟨who, _hwho, hwho⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun player ↦ |port.limit player - orbit.value 0 player|)
      exact ⟨who, by simpa [rho, total, hwho] using hlimitLower⟩
    have hrewardBound : 0 < quittingRewardBound reward := by
      by_contra hnot
      have hboundZero : quittingRewardBound reward = 0 :=
        le_antisymm (le_of_not_gt hnot) (quittingRewardBound_nonneg reward)
      obtain ⟨who, hwho⟩ := hdisplacement
      have hlimitBound : |port.limit who| ≤ quittingRewardBound reward :=
        abs_le.2 ⟨port.limit_mem.1 who, port.limit_mem.2 who⟩
      have hvalueBound : |orbit.value 0 who| ≤ quittingRewardBound reward :=
        abs_le.2 ⟨(orbit.value_mem 0).1 who, (orbit.value_mem 0).2 who⟩
      rw [hboundZero] at hlimitBound hvalueBound
      have hzeroLimit : port.limit who = 0 :=
        abs_eq_zero.mp (le_antisymm hlimitBound (abs_nonneg _))
      have hzeroValue : orbit.value 0 who = 0 :=
        abs_eq_zero.mp (le_antisymm hvalueBound (abs_nonneg _))
      rw [hzeroLimit, hzeroValue] at hwho
      exact (not_le_of_gt hrho) (by simpa using hwho)
    have hsigned := nonempty_summableChargeSignedTerminalPort_of_displacement
      orbit port hrho hrewardBound (abs_reward_le_quittingRewardBound reward)
      (fun time player ↦ abs_le.2 ⟨(orbit.value_mem time).1 player,
        (orbit.value_mem time).2 player⟩) hdisplacement
    exact ⟨{
      totalAbsorption := total
      totalAbsorption_eq := rfl
      totalAbsorption_pos := hpositive
      rho := rho
      rho_eq := rfl
      rho_pos := hrho
      displacement := hdisplacement
      rewardBound_pos := hrewardBound
      signedPort := hsigned }⟩

end QuittingPunishmentFloorInfiniteOrbit

namespace QuittingPositiveJointPrefixReachNoSureExitResidual

/-- Source-matched ballistic dispatch.  The surviving endpoint retains its
no-sure-exit provenance and is accompanied by its literal summable port and
either zero-charge rigidity or a positive signed terminal label. -/
theorem wellSupported_or_endpointBallisticBoundary
    [Nonempty iota]
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      ∃ endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward,
        ¬endpoint.HasSureExitNashPrefix ∧
          ∃ port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
              endpoint.exactPrefixOrbit,
            Nonempty
                (QuittingPunishmentFloorInfiniteOrbit.SummableChargeZeroRigidity
                  endpoint.exactPrefixOrbit port) ∨
              ∃ certificate : endpoint.exactPrefixOrbit.BallisticCertificate,
                Nonempty
                  (QuittingPunishmentFloorInfiniteOrbit.SummableChargePositiveSignedBoundary
                      endpoint.exactPrefixOrbit port certificate) := by
  rcases residual.wellSupported_or_summableExactPrefixPort with
    hwellSupported | ⟨endpoint, hnoSureExit, ⟨port⟩⟩
  · exact Or.inl hwellSupported
  · by_cases hwellSupported : QuittingWellSupportedAbsorbingSequenceExistence reward
    · exact Or.inl hwellSupported
    · obtain ⟨certificate⟩ :=
        endpoint.exactPrefixOrbit.nonempty_ballisticCertificate_of_not_wellSupported
          hwellSupported
      refine Or.inr ⟨endpoint, hnoSureExit, port, ?_⟩
      rcases certificate.zeroRigidity_or_positiveSignedBoundary
          endpoint.exactPrefixOrbit port with hzero | hpositive
      · exact Or.inl hzero
      · exact Or.inr ⟨certificate, hpositive⟩

end QuittingPositiveJointPrefixReachNoSureExitResidual

end GameTheory
