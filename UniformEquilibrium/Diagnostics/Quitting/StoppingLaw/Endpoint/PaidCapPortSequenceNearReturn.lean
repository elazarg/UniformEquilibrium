/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapPortExactTrichotomy

/-!
# Varying-source paid cap ports produce payoff near-returns

The fixed-source paid cap trichotomy requires the limiting cap displacement to
vanish exactly.  For applications coming from literal rectangle sequences the
source is naturally allowed to vary with the requested endpoint accuracy.
Exact equality is then unnecessary: a uniform positive lower bound on total
absorption, together with cap displacement tending to zero, already supplies
the cumulative-charge admissible payoff near-return family.

For each endpoint tolerance this theorem selects one index and then one finite
literal prefix of that index's actual cap-lifted orbit.  Thus every returned
path is source-matched to one supplied behavioral profile.  No endpoint,
terminal law, paid row, or continuation is recombined across different
indices.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingPaidCapLiftedSource

/-- A sequence of actual paid cap sources yields cumulative admissible payoff
near-returns when its complete absorption is eventually bounded below and its
limiting cap displacement tends to zero.  The source and finite path may vary
with the endpoint tolerance, exactly as allowed by the consumer interface. -/
theorem nonempty_cumulativeNearReturnFamily_of_eventually_totalAbsorption_ge_of_capDisplacement_tendsto_zero
    (source : ℕ → QuittingPaidCapLiftedSource reward)
    (port : ∀ index, (source index).SummablePort)
    (chargeFloor : ℝ) (hchargeFloor : 0 < chargeFloor)
    (habsorption : ∀ᶠ index in atTop,
      chargeFloor ≤ (source index).totalAbsorption)
    (hdisplacement : Tendsto
      (fun index => (source index).capDisplacement (port index))
      atTop (nhds 0)) :
    Nonempty
      (QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily reward) := by
  refine ⟨{
    chargeFloor := chargeFloor / 2
    chargeFloor_pos := half_pos hchargeFloor
    nearReturn := ?_ }⟩
  intro endpointError hendpointError
  have hsmallDisplacement : ∀ᶠ index in atTop,
      (source index).capDisplacement (port index) < endpointError / 2 :=
    hdisplacement.eventually (Iio_mem_nhds (half_pos hendpointError))
  obtain ⟨index, habsorptionIndex, hdisplacementIndex⟩ :=
    (habsorption.and hsmallDisplacement).exists
  let orbit :=
    quittingCapLiftedPunishmentFloorOrbit reward (source index).profile
  let absorption : ℕ → ℝ := fun time =>
    quittingRootAbsorptionMass (orbit.roots time)
  have hhalfBelowTotal :
      chargeFloor / 2 < (source index).totalAbsorption :=
    (half_lt_self hchargeFloor).trans_le habsorptionIndex
  have hsum : Tendsto (fun horizon =>
      ∑ time ∈ Finset.range horizon, absorption time) atTop
      (nhds (source index).totalAbsorption) := by
    simpa [orbit, absorption, totalAbsorption,
      quittingCapLiftedPunishmentFloorOrbit] using
      (source index).absorption_summable.hasSum.tendsto_sum_nat
  have hchargeEventually : ∀ᶠ horizon in atTop,
      chargeFloor / 2 <
        ∑ time ∈ Finset.range horizon, absorption time :=
    hsum.eventually (Ioi_mem_nhds hhalfBelowTotal)
  have hvalue : Tendsto orbit.value atTop
      (nhds (port index).semanticPort.capPort.limit) := by
    apply tendsto_pi_nhds.2
    intro who
    simpa [orbit] using
      (port index).semanticPort.capPort.value_tendsto who
  have hlimitInitial :
      dist (port index).semanticPort.capPort.limit (orbit.value 0) <
        endpointError / 2 := by
    have hbound := hdisplacementIndex
    rw [capDisplacement, (port index).semanticPort.envelope_eq] at hbound
    simpa [orbit, quittingCapLiftedPunishmentFloorOrbit] using hbound
  have hcloseEventually : ∀ᶠ horizon in atTop,
      dist (orbit.value horizon)
          (port index).semanticPort.capPort.limit < endpointError / 2 :=
    hvalue.eventually
      (Metric.ball_mem_nhds _ (half_pos hendpointError))
  obtain ⟨horizon, hcharge, hclose⟩ :=
    (hchargeEventually.and hcloseEventually).exists
  have hreturn :
      dist (orbit.value horizon) (orbit.value 0) < endpointError := by
    calc
      dist (orbit.value horizon) (orbit.value 0) ≤
          dist (orbit.value horizon)
              (port index).semanticPort.capPort.limit +
            dist (port index).semanticPort.capPort.limit
              (orbit.value 0) :=
        dist_triangle _ _ _
      _ < endpointError / 2 + endpointError / 2 :=
        add_lt_add hclose hlimitInitial
      _ = endpointError := by ring
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
    change chargeFloor / 2 ≤
      ∑ time ∈ Finset.range horizon, absorption time
    exact hcharge.le
  · intro who
    have hreturnLe : dist (orbit.value horizon) (orbit.value 0) ≤
        endpointError := hreturn.le
    rw [dist_pi_le_iff hendpointError.le] at hreturnLe
    change |orbit.value 0 who - orbit.value horizon who| ≤ endpointError
    simpa [Real.dist_eq, abs_sub_comm] using hreturnLe who

/-- Direct downstream form of the varying-source consumer. -/
theorem exists_uniformEquilibriumPayoff_of_eventually_totalAbsorption_ge_of_capDisplacement_tendsto_zero
    (source : ℕ → QuittingPaidCapLiftedSource reward)
    (port : ∀ index, (source index).SummablePort)
    (chargeFloor : ℝ) (hchargeFloor : 0 < chargeFloor)
    (habsorption : ∀ᶠ index in atTop,
      chargeFloor ≤ (source index).totalAbsorption)
    (hdisplacement : Tendsto
      (fun index => (source index).capDisplacement (port index))
      atTop (nhds 0)) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨family⟩ :=
    nonempty_cumulativeNearReturnFamily_of_eventually_totalAbsorption_ge_of_capDisplacement_tendsto_zero
      source port chargeFloor hchargeFloor habsorption hdisplacement
  exact family.exists_uniformEquilibriumPayoff

end QuittingPaidCapLiftedSource

end GameTheory
