/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.FlatCirculationSupportRankElimination
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapMinimumFiberContraction

/-!
# Dispatching a paid first-disagreement row through its cap-lifted port

An attained `QuittingPaidFirstDisagreementRow` on a literal profile, together
with a positive global minimum of total terminal-semantic debt, is exactly the
field data of a `QuittingPaidCapLiftedSource`.  Such a source has a summable
port, and every summable port falls into the charged near-return, quantitative
debt descent, inert stall alternative.  A paid row is therefore an entry into
that alternative rather than a terminal uniform-payoff conclusion: of the three
arms only `QuittingPaidCapLiftedSource.ChargedNearReturn` carries a
uniform-equilibrium payoff.

A paid payoff premium is not an absorption charge.  The cap-lift debt budget
bounds total absorption by the source's excess total debt over the global
minimum, so along a sequence of sources whose initial debts converge to a fixed
minimum debt the total absorption converges to zero.  No fixed positive
absorption-charge floor survives such a sequence, however large the row gain
remains after normalization.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A paid first-disagreement row on a literal profile, at a positive global
minimum of total terminal-semantic debt, produces a cap-lifted source whose
minimum, profile, observer and gain are the supplied ones, together with a
summable port lying in the checked charged near-return, quantitative debt
descent, inert stall alternative. -/
theorem paidFirstDisagreement_capPortTrichotomy
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (gain : ℝ) (hgain : 0 < gain)
    (row : QuittingPaidFirstDisagreementRow reward profile observer gain) :
    ∃ (source : QuittingPaidCapLiftedSource reward)
      (port : source.SummablePort),
      source.minimum = minimum ∧ source.profile = profile ∧
        source.observer = observer ∧ source.gain = gain ∧
        (source.ChargedNearReturn port ∨
          source.QuantitativeDebtDescent port ∨ source.InertStall port) := by
  let source : QuittingPaidCapLiftedSource reward :=
    { minimum := minimum
      minimum_le := hminimum
      minimum_pos := hminimumPos
      profile := profile
      observer := observer
      gain := gain
      gain_pos := hgain
      row := row }
  obtain ⟨port⟩ := source.nonempty_summablePort
  exact ⟨source, port, rfl, rfl, rfl, rfl,
    source.chargedNearReturn_or_quantitativeDebtDescent_or_inertStall port⟩

namespace QuittingPositiveMinimumDebtTangentFamily

namespace FullReplacementCluster

variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
  {mover : {who // who ∈ frontier.positiveDebtSupport}}

/-- Cap-lifted dispatch data for a full-replacement cluster: one selected
rank, a nonmover observer with positive gain carrying a paid row on the literal
full-replacement profile at that rank, and a cap-lifted source and summable
port whose minimum is the frontier base, whose profile is that literal
full-replacement profile, and whose port satisfies `arm`. -/
def PaidCapPortDispatch
    (endpoint : FullReplacementCluster frontier mover)
    (arm : ∀ source : QuittingPaidCapLiftedSource reward,
      source.SummablePort → Prop) : Prop :=
  ∃ (rank : ℕ) (observer : ι) (gain : ℝ)
    (_row : QuittingPaidFirstDisagreementRow reward
      (frontier.fullReplacementProfile mover (endpoint.subseq rank))
      observer gain)
    (source : QuittingPaidCapLiftedSource reward)
    (port : source.SummablePort),
    observer ≠ mover.1 ∧ 0 < gain ∧
      source.minimum = frontier.base ∧
      source.profile =
        frontier.fullReplacementProfile mover (endpoint.subseq rank) ∧
      source.observer = observer ∧ source.gain = gain ∧ arm source port

/-- An off-minimum paid first disagreement retains its strict endpoint
separation and dispatches one of its actual paid rows into the cap-port
alternative at the frontier base. -/
theorem separated_and_paidCapPortDispatch_of_offMinimumPaidFirstDisagreement
    (endpoint : FullReplacementCluster frontier mover)
    (paid : endpoint.HasOffMinimumPaidFirstDisagreement) :
    quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum endpoint.cluster ∧
      endpoint.PaidCapPortDispatch (fun source port ↦
        source.ChargedNearReturn port ∨ source.QuantitativeDebtDescent port ∨
          source.InertStall port) := by
  obtain ⟨hseparated, observer, gain, hobserver, hgain, hrows⟩ := paid
  obtain ⟨rank, ⟨row⟩⟩ := hrows.exists
  obtain ⟨source, port, hminimum, hprofile, hobserverEq, hgainEq,
      halternative⟩ :=
    paidFirstDisagreement_capPortTrichotomy frontier.base frontier.base_minimum
      frontier.base_positive
      (frontier.fullReplacementProfile mover (endpoint.subseq rank)) observer
      gain hgain row
  exact ⟨hseparated, rank, observer, gain, row, source, port, hobserver,
    hgain, hminimum, hprofile, hobserverEq, hgainEq, halternative⟩

end FullReplacementCluster

end QuittingPositiveMinimumDebtTangentFamily

namespace QuittingPaidCapLiftedSource

/-- **Charge collapse at the minimum fibre.**  The cap-lift debt budget pays
every selected root's absorption out of the source's excess total debt above
the global minimum, so initial debts converging to a fixed minimum debt force
the complete absorption charge to vanish. -/
theorem totalAbsorption_tendsto_zero_of_initialDebt_tendsto_minimum
    (source : ℕ → QuittingPaidCapLiftedSource reward)
    (port : ∀ index, (source index).SummablePort)
    (minimumDebt : ℝ)
    (hminimumDebt : ∀ index,
      quittingTerminalSemanticDebtSum (source index).minimum = minimumDebt)
    (hinitial : Tendsto (fun index ↦ (source index).initialDebt) atTop
      (nhds minimumDebt)) :
    Tendsto (fun index ↦ (source index).totalAbsorption) atTop (nhds 0) := by
  have hexcess : Tendsto
      (fun index ↦ ((source index).initialDebt - minimumDebt) / minimumDebt)
      atTop (nhds 0) := by
    simpa using (hinitial.sub_const minimumDebt).div_const minimumDebt
  refine squeeze_zero (fun index ↦ (source index).totalAbsorption_nonneg)
    (fun index ↦ ?_) hexcess
  simpa [hminimumDebt index] using
    (source index).totalAbsorption_le_excess_div_minimum (port index)

/-- No fixed positive absorption-charge floor survives a sequence of paid
cap-lifted sources whose initial debts converge to their common minimum debt.
The paid rows may keep an arbitrary fixed positive gain while the admissible
path charge of their cap lifts vanishes. -/
theorem not_eventually_chargeFloor_le_totalAbsorption_of_initialDebt_tendsto_minimum
    (source : ℕ → QuittingPaidCapLiftedSource reward)
    (port : ∀ index, (source index).SummablePort)
    (minimumDebt : ℝ)
    (hminimumDebt : ∀ index,
      quittingTerminalSemanticDebtSum (source index).minimum = minimumDebt)
    (hinitial : Tendsto (fun index ↦ (source index).initialDebt) atTop
      (nhds minimumDebt))
    (chargeFloor : ℝ) (hchargeFloor : 0 < chargeFloor) :
    ¬ ∀ᶠ index in atTop, chargeFloor ≤ (source index).totalAbsorption := by
  intro hfloor
  have hcollapse := totalAbsorption_tendsto_zero_of_initialDebt_tendsto_minimum
    source port minimumDebt hminimumDebt hinitial
  exact absurd (ge_of_tendsto hcollapse hfloor) (not_le.2 hchargeFloor)

end QuittingPaidCapLiftedSource

end GameTheory
