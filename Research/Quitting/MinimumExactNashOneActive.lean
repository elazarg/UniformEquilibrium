/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.KActiveCompactPath
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex

/-!
# Exact minimum dynamics is one-active

At a positive minimum semantic pair, every exact Nash root is all-Continue or
a solo root through the unique debt gate.  Therefore its literal positive
Quit support has cardinality at most one, regardless of ambient player
cardinality.

This identifies the exact minimum stratum with the `K = 1` level of the
compact-path hierarchy.  It does not produce a compatible chronological
sequence of such roots; that remains the renewal/state-matching producer.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem minimumTerminalSemantic_exactNash_hasSupportCardAtMost_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    HasQuittingSupportCardAtMost 1 root := by
  rcases minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo
      (reward := reward) pair root hM hreward hpair hminimum hpositive hnash with
    hcontinue | ⟨owner, _hgate, _hownerPositive, hothers⟩
  · subst root
    unfold HasQuittingSupportCardAtMost quittingPositiveHazardSupport
    simp [quittingAllContinueRoot, hazardOfRoot]
  · unfold HasQuittingSupportCardAtMost
    have hsubset : quittingPositiveHazardSupport root ⊆ {owner} := by
      intro who hwho
      by_contra hnot
      have hne : who ≠ owner := by simpa using hnot
      have hpure := hothers who hne
      have hpositiveWho : 0 < hazardOfRoot root who :=
        (Finset.mem_filter.mp hwho).2
      unfold hazardOfRoot at hpositiveWho
      rw [hpure] at hpositiveWho
      simp at hpositiveWho
    exact (Finset.card_le_card hsubset).trans_eq (Finset.card_singleton owner)

end GameTheory
