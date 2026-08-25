/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetPayoffAlignment
import
  UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import
  UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawMixture

/-!
# Pair-base fixed-law rigidity

This research module studies the extra counterfactual information carried by
one complete terminal law.  For a two-player sure-Quit base, deleting either
base player has no singleton boundary term: the other base player still Quits
at the first live row.  Consequently the retained terminal law determines the
base player's Always-Continue payoff.  The intended application is to upgrade
the exact payoff alignment of a pair-base fixed-law reset to equality of the
full terminal-semantic pairs.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Once the retained law has already exposed every target cap as a lower
bound on the returned cap, fixed-law total-debt minimality upgrades exact
payoff alignment to equality of the full semantic pairs. -/
theorem QuittingFixedLawResetDispatch.eq_target_of_target_cap_le
    {source target : QuittingTerminalSemanticPair ι}
    {mass : QuittingTerminalOutcome ι → ℝ}
    {owner other : ι} {returned : QuittingTerminalSemanticPair ι}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward)
    (hcap : ∀ who, target.2 who ≤ returned.2 who) :
    returned = target := by
  have hpayoff : returned.1 = target.1 :=
    dispatch.prescribed_eq_target htarget
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt target who ≤
        quittingTerminalSemanticDebt returned who := by
    intro who
    unfold quittingTerminalSemanticDebt
    rw [hpayoff]
    exact sub_le_sub_right (hcap who) _
  have hsumLower : quittingTerminalSemanticDebtSum target ≤
      quittingTerminalSemanticDebtSum returned := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_le_sum fun who _ ↦ hcoordinate who
  have hsumEq :
      (∑ who, quittingTerminalSemanticDebt target who) =
        ∑ who, quittingTerminalSemanticDebt returned who := by
    change quittingTerminalSemanticDebtSum target =
      quittingTerminalSemanticDebtSum returned
    exact le_antisymm hsumLower dispatch.target_ge
  have hdebtEq : ∀ who,
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt returned who := by
    intro who
    exact (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset ι))
      (fun player _ ↦ hcoordinate player)).mp hsumEq who
        (Finset.mem_univ who)
  apply Prod.ext
  · exact hpayoff
  · funext who
    have hwho := hdebtEq who
    unfold quittingTerminalSemanticDebt at hwho
    rw [hpayoff] at hwho
    linarith

end GameTheory
