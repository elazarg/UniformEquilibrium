/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Actual tails near a singleton-separated carrier point

A point of the finite-dimensional terminal-semantic carrier need not be
realized by one behavior profile.  It is nevertheless a sequential limit of
actual profile pairs.  If its prescribed coordinate is uniformly separated
from all own singleton rewards, one sufficiently late actual profile retains
half that separation while its whole semantic pair is arbitrarily close and
its total debt is correspondingly close above the carrier value.

This is only an actual-tail selector.  It does not identify the chosen
profile with the carrier point or place its semantic pair on a minimum fibre.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An actual behavioral tail selected near a singleton-separated carrier
point.  The conclusion is stronger than a minimum-fibre specialization: the
input carrier point may be arbitrary. -/
theorem exists_actualNearCarrierTail_of_uniformSingletonGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticPair ι)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward)
    {delta epsilon : ℝ} (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hsingleton : ∀ who,
      delta ≤ point.1 who - reward (quittingSingletonTerminal who) who) :
    ∃ tail : (quittingGame reward).BehaviorProfile,
      dist (quittingTerminalSemanticPair reward tail) point < epsilon ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward tail) <
          quittingTerminalSemanticDebtSum point + epsilon ∧
        ∀ who, delta / 2 ≤
          quittingTerminalPayoff reward tail who -
            reward (quittingSingletonTerminal who) who := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward point hpoint
  have hmetric : ∀ᶠ index in atTop,
      dist (quittingTerminalSemanticPair reward (profiles index)) point <
        epsilon := by
    have hball : Metric.ball point epsilon ∈ nhds point :=
      Metric.ball_mem_nhds point hepsilon
    simpa only [Metric.mem_ball] using hprofiles.eventually hball
  have hdebtTendsto : Tendsto
      (fun index => quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles index))) atTop
      (nhds (quittingTerminalSemanticDebtSum point)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp hprofiles
  have hdebt : ∀ᶠ index in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles index)) <
        quittingTerminalSemanticDebtSum point + epsilon :=
    hdebtTendsto.eventually (Iio_mem_nhds (by linarith))
  have hpayoff : ∀ᶠ index in atTop, ∀ who,
      delta / 2 ≤ quittingTerminalPayoff reward (profiles index) who -
        reward (quittingSingletonTerminal who) who := by
    rw [eventually_all]
    intro who
    have hcoordinate : Tendsto
        (fun index => quittingTerminalPayoff reward (profiles index) who)
        atTop (nhds (point.1 who)) :=
      ((continuous_apply who).comp continuous_fst).continuousAt.tendsto.comp
        hprofiles
    have hlower : point.1 who - delta / 2 < point.1 who := by linarith
    filter_upwards [hcoordinate.eventually (Ioi_mem_nhds hlower)] with index hindex
    linarith [hsingleton who]
  obtain ⟨index, hindex⟩ := (hmetric.and (hdebt.and hpayoff)).exists
  exact ⟨profiles index, hindex.1, hindex.2.1, hindex.2.2⟩

end GameTheory
