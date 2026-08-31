/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawExploitabilityFloor
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

/-!
# Separation of total debt from terminal exploitability

The coordinatewise stopping-law chord bound is stronger than separate payoff
and cap Lipschitz estimates. Since every endpoint debt is at most twice the
reward bound, it forces a quantitative gap between the infimum of total debt
and the infimum of maximum debt.

This module is source mathematics only. It constructs no paid port and makes
no uniform-equilibrium claim.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Maximum terminal debt is no larger than the total-debt infimum. -/
theorem quittingTerminalExploitabilityInf_le_debtSumInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalExploitabilityInf reward ≤
      quittingTerminalDebtSumInf reward := by
  unfold quittingTerminalDebtSumInf
  apply le_csInf (Set.range_nonempty _)
  rintro total ⟨profile, rfl⟩
  exact (quittingTerminalExploitabilityInf_le reward profile).trans
    (quittingTerminalExploitability_le_terminalSemanticDebtSum reward profile)

/-- **Strong debt-ratio separation.** If terminal exploitability has a
positive global infimum, total debt stays above it by at least
`eta^2 / (2 * bound)`. -/
theorem quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 < bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward) :
    quittingTerminalExploitabilityInf reward ^ 2 / (2 * bound) ≤
      quittingTerminalDebtSumInf reward -
        quittingTerminalExploitabilityInf reward := by
  let eta := quittingTerminalExploitabilityInf reward
  let totalInf := quittingTerminalDebtSumInf reward
  let gap := totalInf - eta
  have heta : 0 < eta := hpositive
  have htwoBound : 0 < 2 * bound := by positivity
  have hetaBound : eta ≤ 2 * bound := by
    exact quittingTerminalExploitabilityInf_le_two_mul_bound
      reward bound hreward
  have hgap : 0 ≤ gap := by
    dsimp only [gap, totalInf, eta]
    linarith [quittingTerminalExploitabilityInf_le_debtSumInf reward]
  change eta ^ 2 / (2 * bound) ≤ gap
  by_contra hnot
  have hcontra : gap < eta ^ 2 / (2 * bound) := lt_of_not_ge hnot
  have hsqLe : eta ^ 2 / (2 * bound) ≤ eta := by
    rw [div_le_iff₀ htwoBound]
    nlinarith
  have hgapEta : gap < eta := hcontra.trans_le hsqLe
  have hleftDen : 0 < eta + gap := by linarith
  have hrightDen : 0 < 2 * bound - gap := by linarith
  have hratio : gap / (eta + gap) <
      (eta - gap) / (2 * bound - gap) := by
    have hcross : gap * (2 * bound) < eta ^ 2 := by
      rw [lt_div_iff₀ htwoBound] at hcontra
      nlinarith
    rw [div_lt_div_iff₀ hleftDen hrightDen]
    nlinarith
  obtain ⟨lambda, hlambdaLower, hlambdaUpper⟩ :=
    exists_between hratio
  have hlambda0 : 0 < lambda := by
    have hratioNonneg : 0 ≤ gap / (eta + gap) :=
      div_nonneg hgap hleftDen.le
    exact hratioNonneg.trans_lt hlambdaLower
  have hlambda1 : lambda < 1 := by
    have hratioLeOne : (eta - gap) / (2 * bound - gap) ≤ 1 := by
      rw [div_le_one hrightDen]
      linarith
    exact hlambdaUpper.trans_le hratioLeOne
  have hmoverBase : (1 - lambda) * (eta + gap) < eta := by
    rw [div_lt_iff₀ hleftDen] at hlambdaLower
    nlinarith
  have hotherBase :
      (1 - lambda) * gap + lambda * (2 * bound) < eta := by
    rw [lt_div_iff₀ hrightDen] at hlambdaUpper
    nlinarith
  let slack := min
    (eta - (1 - lambda) * (eta + gap))
    (eta - ((1 - lambda) * gap + lambda * (2 * bound)))
  have hslack : 0 < slack := by
    dsimp only [slack]
    exact lt_min (sub_pos.mpr hmoverBase) (sub_pos.mpr hotherBase)
  let error := slack / 4
  have herrorEq : error = slack / 4 := rfl
  have herror : 0 < error := div_pos hslack (by norm_num)
  have htotalNear : totalInf < totalInf + error := lt_add_of_pos_right _ herror
  unfold totalInf quittingTerminalDebtSumInf at htotalNear
  obtain ⟨total, ⟨profile, hprofileTotal⟩, htotal⟩ :=
    exists_lt_of_csInf_lt (Set.range_nonempty _) htotalNear
  subst total
  obtain ⟨mover, -, hmoverMax⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty fun who : ι =>
      quittingTerminalDeviationDebt reward profile who
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalDeviationDebt reward profile who :=
    fun who => quittingTerminalDeviationDebt_nonneg reward profile who
  have hexploitEq : quittingTerminalExploitability reward profile =
      quittingTerminalDeviationDebt reward profile mover := by
    unfold quittingTerminalExploitability finitePlayerMax
    change Finset.univ.sup' Finset.univ_nonempty
      (fun who => max 0 (quittingTerminalDeviationDebt reward profile who)) =
        quittingTerminalDeviationDebt reward profile mover
    simp_rw [max_eq_right (hdebtNonneg _)]
    exact hmoverMax
  let moverDebt := quittingTerminalDeviationDebt reward profile mover
  have hetaMover : eta ≤ moverDebt := by
    dsimp only [eta, moverDebt]
    rw [← hexploitEq]
    exact quittingTerminalExploitabilityInf_le reward profile
  obtain ⟨bestResponse, hbestResponse⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile mover herror
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward mover (profile mover) bestResponse lambda hlambda0.le hlambda1.le
  let mixedProfile := Function.update profile mover mixedStrategy
  let endpointProfile := Function.update profile mover bestResponse
  have hendpointMover :
      quittingTerminalDeviationDebt reward endpointProfile mover ≤ error := by
    have hcapInvariant := quittingContinuationBestResponseValue_update_self
      reward profile mover bestResponse
    dsimp only [endpointProfile]
    unfold quittingTerminalDeviationDebt
    linarith
  have hmixedMoverChord :=
    quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward profile mover (profile mover) bestResponse lambda
        hlambda0.le hlambda1.le
  rw [Function.update_eq_self] at hmixedMoverChord
  change quittingTerminalDeviationDebt reward
      (Function.update profile mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover
          (profile mover) bestResponse lambda hlambda0.le hlambda1.le)) mover =
    (1 - lambda) * quittingTerminalDeviationDebt reward profile mover +
      lambda * quittingTerminalDeviationDebt reward endpointProfile mover at hmixedMoverChord
  have hmixedMover :
      quittingTerminalDeviationDebt reward mixedProfile mover < eta := by
    dsimp only [mixedProfile, mixedStrategy]
    rw [hmixedMoverChord]
    have hmoverDebtLe : moverDebt ≤ eta + gap + error := by
      dsimp only [moverDebt, gap, eta]
      change quittingTerminalDebtSum reward profile <
        quittingTerminalDebtSumInf reward + error at htotal
      have hmoverLeSum : moverDebt ≤ quittingTerminalDebtSum reward profile := by
        unfold quittingTerminalDebtSum
        exact Finset.single_le_sum
          (fun who _ => hdebtNonneg who) (Finset.mem_univ mover)
      linarith
    have hendpoint : quittingTerminalDeviationDebt reward endpointProfile mover ≤
        error := hendpointMover
    dsimp only [endpointProfile] at hendpoint
    have hslackLe : slack ≤
        eta - (1 - lambda) * (eta + gap) := min_le_left _ _
    nlinarith [herrorEq]
  have hmixedOther : ∀ other, other ≠ mover →
      quittingTerminalDeviationDebt reward mixedProfile other < eta := by
    intro other hother
    have hsourceOther : quittingTerminalDeviationDebt reward profile other <
        gap + error := by
      have hsourceLe : quittingTerminalDeviationDebt reward profile other ≤
          quittingTerminalDebtSum reward profile - moverDebt := by
        unfold quittingTerminalDebtSum
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ mover)]
        have hmember : other ∈ Finset.univ.erase mover := by simp [hother]
        have hsingle := Finset.single_le_sum
          (fun who _ => hdebtNonneg who) hmember
        linarith
      dsimp only [gap]
      change quittingTerminalDebtSum reward profile <
        quittingTerminalDebtSumInf reward + error at htotal
      linarith
    have hchord :=
      quittingTerminalSemanticDebt_stoppingLawMixture_le_boundChord
        reward profile mover other (profile mover) bestResponse lambda bound
          hlambda0.le hlambda1.le hreward
    rw [Function.update_eq_self] at hchord
    change quittingTerminalDeviationDebt reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (profile mover) bestResponse lambda hlambda0.le hlambda1.le)) other ≤
      (1 - lambda) * quittingTerminalDeviationDebt reward profile other +
        lambda * (2 * bound) at hchord
    have hslackLe : slack ≤
        eta - ((1 - lambda) * gap + lambda * (2 * bound)) :=
      min_le_right _ _
    dsimp only [mixedProfile, mixedStrategy]
    nlinarith [herrorEq]
  have hmixedExploit : quittingTerminalExploitability reward mixedProfile < eta := by
    unfold quittingTerminalExploitability finitePlayerMax
    rw [Finset.sup'_lt_iff]
    intro who _
    have hdebt := if hwho : who = mover then by
        simpa [hwho] using hmixedMover
      else hmixedOther who hwho
    have hdebtNonnegMixed :=
      quittingTerminalDeviationDebt_nonneg reward mixedProfile who
    change max 0 (quittingTerminalDeviationDebt reward mixedProfile who) < eta
    rw [max_eq_right hdebtNonnegMixed]
    exact hdebt
  exact (not_lt_of_ge
    (quittingTerminalExploitabilityInf_le reward mixedProfile)) hmixedExploit

/-- Square-root debt separation, as a direct corollary of the stronger
quadratic-over-linear estimate above. -/
theorem quittingTerminalExploitabilityInf_sqrt_separation_le_debtSumInf_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 < bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward) :
    Real.sqrt
        (4 * bound ^ 2 + quittingTerminalExploitabilityInf reward ^ 2) -
        2 * bound ≤
      quittingTerminalDebtSumInf reward -
        quittingTerminalExploitabilityInf reward := by
  let eta := quittingTerminalExploitabilityInf reward
  have htwoBound : 0 < 2 * bound := by positivity
  have hsqrt : Real.sqrt (4 * bound ^ 2 + eta ^ 2) ≤
      2 * bound + eta ^ 2 / (2 * bound) := by
    rw [Real.sqrt_le_iff]
    constructor
    · have hetaSq : 0 ≤ eta ^ 2 := sq_nonneg eta
      have hquot : 0 ≤ eta ^ 2 / (2 * bound) := div_nonneg hetaSq htwoBound.le
      linarith
    · have hetaSq : 0 ≤ eta ^ 2 := sq_nonneg eta
      have hquotSq : 0 ≤ (eta ^ 2 / (2 * bound)) ^ 2 := sq_nonneg _
      have hcancel : (2 * bound) * (eta ^ 2 / (2 * bound)) = eta ^ 2 := by
        field_simp
      nlinarith
  have hstrong :=
    quittingTerminalExploitabilityInf_sq_div_two_bound_le_debtSumInf_sub
      reward bound hbound hreward hpositive
  dsimp only [eta] at hsqrt
  linarith

end GameTheory
