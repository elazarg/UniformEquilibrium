/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.FirstStageAdapter
import UniformEquilibrium.Quitting.Root.FaceGeometry
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Advancing a same-date marked transfer

A marked first-opponent selection may transfer the player flag without
advancing calendar time.  This file isolates the elementary Bellman estimate
which controls that obstruction.

For a one-stage Nash--Bellman edge `current → successor` with absorption
mass `p`, bounded terminal rewards and bounded successor values give

`|current i - successor i| ≤ 2 M p`.

Consequently, if a newly marked player has current value at most `-θ`, then
either the root has the quantitatively positive jump `p ≥ θ/(4M)`, or the
same player remains at most `-θ/2` at the survived successor.  In the latter
case the flag can be moved forward by one actual stage.

The positive-jump alternative is an actual compatible Bellman edge, but this
file does not claim that its successor is again negatively marked or that one
such edge is already a terminal discharge.  Those are separate SCC/path
questions.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Parameterized same-date transfer dichotomy.  Advancing the marked flag
one actual stage spends at most the supplied negativity budget `η`; otherwise
the root has absorption mass at least `η / (2M)`.  This additive form can be
iterated without repeatedly halving the negative threshold. -/
theorem markedNegative_advance_or_absorptionMass_ge_of_budget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η : ℝ)
    (hM : 0 < M) (_hη : 0 ≤ η)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnegative : current marked ≤ -θ) :
    η / (2 * M) ≤ quittingRootAbsorptionMass root ∨
      successor marked ≤ -θ + η := by
  by_cases hjump : η / (2 * M) ≤ quittingRootAbsorptionMass root
  · exact Or.inl hjump
  · right
    have hpSmall :
        quittingRootAbsorptionMass root < η / (2 * M) :=
      lt_of_not_ge hjump
    have hden : 0 < 2 * M := mul_pos (by norm_num) hM
    have hscaled :
        2 * M * quittingRootAbsorptionMass root < η := by
      simpa [mul_comm] using (lt_div_iff₀ hden).1 hpSmall
    have hjumpBound :=
      abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
        reward successor root marked M hreward hsuccessorBound
    have hcoordinate :
        current marked =
          quittingRootSuccessorPayoff reward successor root marked := by
      exact congrFun hbellman marked
    rw [← hcoordinate] at hjumpBound
    have hforward : successor marked - current marked ≤
        |current marked - successor marked| := by
      simpa [abs_sub_comm] using le_abs_self (successor marked - current marked)
    nlinarith

omit [DecidableEq ι] in
/-- Half-margin form of the additive budget theorem.  A player which is
`θ`-negative at the current endpoint either lies on a root with absorption
mass at least `θ/(4M)`, or remains `θ/2`-negative after advancing one actual
stage. -/
theorem markedNegative_advance_or_absorptionMass_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ : ℝ)
    (hM : 0 < M) (hθ : 0 ≤ θ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnegative : current marked ≤ -θ) :
    θ / (4 * M) ≤ quittingRootAbsorptionMass root ∨
      successor marked ≤ -(θ / 2) := by
  have hbudget := markedNegative_advance_or_absorptionMass_ge_of_budget
    reward current successor root marked M θ (θ / 2) hM
      (div_nonneg hθ (by norm_num)) hreward hsuccessorBound
      hbellman hnegative
  rcases hbudget with hjump | hadvance
  · left
    have hratio : (θ / 2) / (2 * M) = θ / (4 * M) := by
      field_simp
      ring
    rw [hratio] at hjump
    exact hjump
  · right
    linarith

/-! ## A successor escape makes the product jump playerwise charged -/

/-- If an exact-Nash root starts with a `θ`-negative marked value but its
survived successor rises by `η`, the marked player's *opponents* must absorb
with mass at least `η/(2M)`.  Otherwise pure Continue would beat the current
value. -/
theorem successorEscape_le_two_mul_opponentAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked) :
    η ≤ 2 * M * quittingRootOpponentAbsorptionMass root marked := by
  have hcontinueNash := hnash marked (PMF.pure false)
  have hcontinue :
      quittingRootContinuePayoff reward successor root marked ≤
        current marked := by
    rw [congrFun hbellman marked]
    simpa [quittingRootContinuePayoff,
      quittingRootSuccessorPayoff] using hcontinueNash
  have hjumpBound :=
    abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward successor
        (Function.update root marked (PMF.pure false)) marked M
        hreward hsuccessorBound
  change
    |quittingRootContinuePayoff reward successor root marked -
        successor marked| ≤
      2 * M * quittingRootOpponentAbsorptionMass root marked at hjumpBound
  have hforward :
      successor marked -
          quittingRootContinuePayoff reward successor root marked ≤
        |quittingRootContinuePayoff reward successor root marked -
          successor marked| := by
    simpa [abs_sub_comm] using le_abs_self
      (successor marked -
        quittingRootContinuePayoff reward successor root marked)
  linarith

/-- Ratio form of `successorEscape_le_two_mul_opponentAbsorptionMass`. -/
theorem ratio_le_opponentAbsorptionMass_of_successorEscape
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η : ℝ) (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked) :
    η / (2 * M) ≤ quittingRootOpponentAbsorptionMass root marked := by
  have hcharge := successorEscape_le_two_mul_opponentAbsorptionMass
    reward current successor root marked M θ η hreward hsuccessorBound
      hbellman hnash hnegative hescape
  exact (div_le_iff₀ (mul_pos (by norm_num) hM)).2
    (by simpa [mul_comm] using hcharge)

/-- A same-date marked root with marked Quit mass `β` and a successor escape
of size `η` is charged for every player.  Other players see the marked Quit
hazard; the marked player sees the opponent hazard forced by exact Nash. -/
theorem min_le_opponentAbsorptionMass_of_markedHazard_of_successorEscape
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η β : ℝ) (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked)
    (hmarkedHazard : β ≤ (root marked true).toReal) :
    ∀ who, min β (η / (2 * M)) ≤
      quittingRootOpponentAbsorptionMass root who := by
  intro who
  by_cases hwho : who = marked
  · subst who
    exact (min_le_right β (η / (2 * M))).trans
      (ratio_le_opponentAbsorptionMass_of_successorEscape
        reward current successor root marked M θ η hM hreward
          hsuccessorBound hbellman hnash hnegative hescape)
  · exact (min_le_left β (η / (2 * M))).trans
      (hmarkedHazard.trans
        (quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne root
          (Ne.symm hwho)))

/-- **Actual-suffix restart or playerwise-charged jump.**  The carrier is the
genuine Bellman edge `current → successor`, not a re-rooted copy.  If the
marked coordinate stays inside its negative band at `successor`, the marked
construction can restart one calendar stage later.  Otherwise the current
root has a quantitative opponent-absorption charge for every player: other
players see the marked Quit hazard `β`, while the marked player sees the
Nash-forced opponent charge `η/(2M)`.

This is the local jump-or-strict-time rule.  The charged edge still has to be
retained in a compatible recurrent segment or consumed by a separately
proved local discharge; it is not itself asserted to be an equilibrium. -/
theorem markedNegative_advance_or_playerwiseChargedJump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η β : ℝ) (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hmarkedHazard : β ≤ (root marked true).toReal) :
    successor marked ≤ -θ + η ∨
      ∀ who, min β (η / (2 * M)) ≤
        quittingRootOpponentAbsorptionMass root who := by
  by_cases hadvance : successor marked ≤ -θ + η
  · exact Or.inl hadvance
  · right
    exact min_le_opponentAbsorptionMass_of_markedHazard_of_successorEscape
      reward current successor root marked M θ η β hM hreward
        hsuccessorBound hbellman hnash hnegative (le_of_not_ge hadvance)
        hmarkedHazard

/-- With positive marked mass and a positive escape budget, the charged-jump
branch contracts every player's one-stage opponent clock. -/
theorem opponentAbsorptionMass_pos_of_chargedJump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : Payoff ι) (root : ι → PMF Bool)
    (marked : ι) (M θ η β : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hβ : 0 < β)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hsuccessorBound : |successor marked| ≤ M)
    (hbellman : current =
      quittingRootSuccessorPayoff reward successor root)
    (hnash : IsεQuittingRootNash reward successor 0 root)
    (hnegative : current marked ≤ -θ)
    (hescape : -θ + η ≤ successor marked)
    (hmarkedHazard : β ≤ (root marked true).toReal) :
    ∀ who, 0 < quittingRootOpponentAbsorptionMass root who := by
  have hcharge :=
    min_le_opponentAbsorptionMass_of_markedHazard_of_successorEscape
      reward current successor root marked M θ η β hM hreward
        hsuccessorBound hbellman hnash hnegative hescape hmarkedHazard
  have hratio : 0 < η / (2 * M) :=
    div_pos hη (mul_pos (by norm_num) hM)
  intro who
  exact (lt_min hβ hratio).trans_le (hcharge who)

end GameTheory
