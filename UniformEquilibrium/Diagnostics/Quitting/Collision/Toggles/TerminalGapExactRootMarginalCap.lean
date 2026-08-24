/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapConstrainedStationary
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedSemanticCarrier
import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Root.NearSureRoot

/-!
# A terminal exploitability gap keeps exact floor roots away from sure Quit

Forcing one marginal of an exact bounded root to pure Quit costs at most four
times the reward bound times that marginal's Continue probability.  A
punishment continuation for the forced player turns the resulting sure-first
row into a behavioral terminal approximate equilibrium.  A positive terminal
exploitability gap therefore gives a quantitative lower bound on every
Continue probability.

The continuation target is required to lie above the actual behavioral
punishment floor.  No stationary or restricted-deviation substitute is used.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every coordinate of an exact bounded root above the behavioral punishment
floor has Continue probability at least `gap / (4 * M)`. -/
theorem terminalGap_div_four_mul_le_exactFloorRoot_continueProbability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {gap M : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M)
    (hfloor : ∀ player, quittingPunishmentValue reward player ≤ tail player)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    gap / (4 * M) ≤ (root who false).toReal := by
  have hgapBound : gap ≤ 2 * M :=
    terminalExploitabilityGap_le_two_mul_bound reward hreward hexploit
  have hM : 0 < M := by linarith
  let continueMass := (root who false).toReal
  have hcontinueNonneg : 0 ≤ continueMass := ENNReal.toReal_nonneg
  have hscaledNonneg : 0 ≤ 4 * M * continueMass := by positivity
  have hscaled : gap ≤ 4 * M * continueMass := by
    by_contra hnot
    have hstrict : 4 * M * continueMass < gap := lt_of_not_ge hnot
    let epsilon := (gap - 4 * M * continueMass) / 2
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      linarith
    obtain ⟨punishRow, hpunish⟩ :=
      exists_punishRow_stationaryUnilateralCap_le reward who hepsilon
    let continuation := quittingStationaryProfile reward punishRow
    let best := quittingContinuationBestResponse reward continuation
    let forced := Function.update root who (PMF.pure true)
    have hforcedSure : QuittingRootHasSureQuitter forced :=
      quittingRootHasSureQuitter_update_pure_true root who
    have hbestWho : best who ≤ tail who + epsilon := by
      change quittingContinuationBestResponseValue reward continuation who ≤ _
      rw [quittingContinuationBestResponseValue_eq_bestReplyValue,
        quittingBestReplyValue_stationary]
      linarith [hfloor who]
    have hforcedTail : IsεQuittingRootNash reward tail
        (4 * M * continueMass) forced := by
      have h := isεQuittingRootNash_update_pure_true
        reward tail root who hreward htail hnash
      simpa [continueMass, forced] using h
    have hforcedBest : IsεQuittingRootNash reward best
        (4 * M * continueMass + epsilon) forced := by
      intro player deviation
      have htailNash := hforcedTail player deviation
      by_cases hplayer : player = who
      · subst player
        have hdeviation := quittingRootExpectedPayoff_continuation_le_add
          reward best tail (Function.update forced who deviation) who
          hepsilon.le hbestWho
        have hprescribed := quittingRootExpectedPayoff_eq_of_hasSureQuitter
          reward forced hforcedSure best tail who
        linarith
      · have hdeviatedSure : QuittingRootHasSureQuitter
            (Function.update forced player deviation) := by
          refine ⟨who, ?_⟩
          rw [Function.update_of_ne (Ne.symm hplayer)]
          simp [forced]
        have hdeviation := quittingRootExpectedPayoff_eq_of_hasSureQuitter
          reward (Function.update forced player deviation) hdeviatedSure
            best tail player
        have hprescribed := quittingRootExpectedPayoff_eq_of_hasSureQuitter
          reward forced hforcedSure best tail player
        linarith
    have hterminal :=
      isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
        reward forced continuation hforcedSure hforcedBest
    obtain ⟨player, deviation, himprove⟩ := hexploit
      (quittingRootThenContinuationProfile reward forced continuation)
    have hnashDeviation := hterminal player deviation
    dsimp only [epsilon] at hnashDeviation
    linarith
  exact (div_le_iff₀ (by positivity : 0 < 4 * M)).2 (by
    nlinarith [hscaled])

/-- Equivalent upper-bound form for the Quit marginal. -/
theorem exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {gap M : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M)
    (hfloor : ∀ player, quittingPunishmentValue reward player ≤ tail player)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    (root who true).toReal ≤ 1 - gap / (4 * M) := by
  have hcontinue :=
    terminalGap_div_four_mul_le_exactFloorRoot_continueProbability
      reward tail root who hgap hreward htail hfloor hexploit hnash
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  linarith

end GameTheory
