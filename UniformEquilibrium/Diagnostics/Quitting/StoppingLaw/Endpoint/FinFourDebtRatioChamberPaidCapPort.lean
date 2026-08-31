/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualProfileTerminalGapPaidCap
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticDebtRatioCarrierResponse

/-!
# Four-player debt-ratio chamber paid-cap attachment

The incoming edge is the fixed-payer approximate full response constructed by
the carrier-response theorem.  The paid-cap port is selected separately at its
literal target.  Its observer and paid row are not identified with that payer
or response.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- One retained incoming full-response edge and the separately selected paid
cap port based at its literal target. -/
structure FinFourDebtRatioResponsePaidCapPort
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (source : QuittingDebtRatioApproximateResponseSource reward minimum)
    (gamma : ℝ) (index : ℕ) where
  target_eq : source.target index =
    Function.update (source.carrier.profile index) source.carrier.payer
      (source.response index)
  incoming_gain_floor : gamma ≤
    quittingTerminalPayoff reward (source.target index) source.carrier.payer -
      quittingTerminalPayoff reward (source.carrier.profile index)
        source.carrier.payer
  target_excess_floor :
    (quittingTerminalSemanticDebtSum minimum *
        (2 * quittingTerminalExploitabilityInf reward -
          quittingTerminalSemanticDebtSum minimum) /
        (quittingTerminalSemanticDebtSum minimum -
          quittingTerminalExploitabilityInf reward)) / 2 ≤
      quittingTerminalDebtSum reward (source.target index) -
        quittingTerminalSemanticDebtSum minimum
  paidPort : QuittingActualProfileTerminalGapPaidCapPort
    reward minimum (source.target index) gamma

/-- In the strict four-player ratio chamber, one actual fixed-payer response
source has an eventual tail whose every target carries the concrete half-
excess floor and a separately selected paid-cap port. -/
theorem exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward)
    (hlower : quittingTerminalExploitabilityInf reward <
      quittingTerminalSemanticDebtSum minimum)
    (hupper : quittingTerminalSemanticDebtSum minimum <
      2 * quittingTerminalExploitabilityInf reward)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgammaLt : gamma < quittingTerminalExploitabilityInf reward) :
    ∃ source : QuittingDebtRatioApproximateResponseSource reward minimum,
      ∃ firstIndex : ℕ, ∀ index, firstIndex ≤ index →
        Nonempty
          (FinFourDebtRatioResponsePaidCapPort
            reward minimum source gamma index) := by
  obtain ⟨source⟩ := nonempty_quittingDebtRatioApproximateResponseSource
    reward minimum hminimum
  have hpayerStrict :=
    source.exploitabilityInf_lt_point_payer_debt_of_debtSum_lt_two_mul
      hminimum hpositive hupper bound hreward
  have hgain : ∀ᶠ n in atTop, gamma <
      quittingTerminalPayoff reward (source.target n) source.carrier.payer -
        quittingTerminalPayoff reward (source.carrier.profile n)
          source.carrier.payer :=
    source.tendsto_response_gain.eventually_const_lt
      (hgammaLt.trans hpayerStrict)
  have hexcess :=
    source.eventually_half_ratioCrossing_le_target_debtExcess
      hminimum hpositive hlower hupper bound hreward
  obtain ⟨firstIndex, htail⟩ := eventually_atTop.mp (hgain.and hexcess)
  refine ⟨source, firstIndex, ?_⟩
  intro index hindex
  have hdata := htail index hindex
  have hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum :=
    hpositive.trans hlower
  let gap := hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf
    reward hgammaLt
  obtain ⟨paidPort⟩ := gap.nonempty_actualProfilePaidCapPort
    hgamma minimum hminimum_le hminimumPos (source.target index)
  exact ⟨{
    target_eq := rfl
    incoming_gain_floor := hdata.1.le
    target_excess_floor := hdata.2
    paidPort := paidPort }⟩

/-- Failure of a four-player uniform-equilibrium payoff and the strict upper
ratio bound construct the minimum carrier point, actual fixed-payer response
source, and eventual separately selected paid-cap ports.  The strict lower
ratio bound is derived from the quantitative debt separation theorem. -/
theorem
    exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort_of_no_uniformEquilibriumPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬∃ payoff,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (bound : ℝ) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hupper : quittingTerminalDebtSumInf reward <
      2 * quittingTerminalExploitabilityInf reward)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgammaLt : gamma < quittingTerminalExploitabilityInf reward) :
    ∃ minimum ∈ quittingTerminalSemanticCarrier reward,
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      ∃ source : QuittingDebtRatioApproximateResponseSource reward minimum,
        ∃ firstIndex : ℕ, ∀ index, firstIndex ≤ index →
          Nonempty
            (FinFourDebtRatioResponsePaidCapPort
              reward minimum source gamma index) := by
  have hpositive :=
    quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff reward hno
  obtain ⟨minimum, hminimum, hminimum_le⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  have hminimumEq : quittingTerminalDebtSumInf reward =
      quittingTerminalSemanticDebtSum minimum :=
    quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      minimum hminimum hminimum_le
  have hseparation :=
    quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub
      reward bound hbound hreward hpositive
  have hlower : quittingTerminalExploitabilityInf reward <
      quittingTerminalSemanticDebtSum minimum := by
    have hstrict : 0 < quittingTerminalExploitabilityInf reward ^ 2 /
        (2 * bound) := by positivity
    rw [hminimumEq] at hseparation
    linarith
  have hminimumUpper : quittingTerminalSemanticDebtSum minimum <
      2 * quittingTerminalExploitabilityInf reward := by
    rw [← hminimumEq]
    exact hupper
  obtain ⟨source, firstIndex, hports⟩ :=
    exists_eventually_nonempty_finFourDebtRatioResponsePaidCapPort
      reward minimum hminimum hminimum_le hpositive hlower hminimumUpper
        bound hreward gamma hgamma hgammaLt
  exact ⟨minimum, hminimum, hminimum_le, source, firstIndex, hports⟩

end GameTheory
