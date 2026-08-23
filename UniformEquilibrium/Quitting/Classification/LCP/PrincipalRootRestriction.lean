/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.PrincipalRestriction
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalReward
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Principal restriction of quitting root actions

A Boolean action on a principal player subtype extends to the ambient player
type by assigning Continue to every omitted player.  Its quitter coalition and
one-stage payoff are exactly the corresponding principal restrictions.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Extend a principal-subtype action by pure Continue outside the selected
players. -/
def quittingPrincipalAction (players : Finset ι)
    (action : players → Bool) : ι → Bool :=
  principalExtend players (fun _ => false) action

omit [Fintype ι] in
@[simp] theorem quittingPrincipalAction_apply_subtype
    (players : Finset ι) (action : players → Bool) (who : players) :
    quittingPrincipalAction players action who.1 = action who := by
  simp [quittingPrincipalAction]

omit [Fintype ι] in
@[simp] theorem quittingPrincipalAction_apply_of_not_mem
    (players : Finset ι) (action : players → Bool) {who : ι}
    (hwho : who ∉ players) :
    quittingPrincipalAction players action who = false := by
  exact principalExtend_apply_not_mem players (fun _ => false) action hwho

/-- The ambient quitter set of the extended action is the mapped principal
quitter set. -/
theorem quittingQuitters_principalAction
    (players : Finset ι) (action : players → Bool) :
    quittingQuitters (quittingPrincipalAction players action) =
      (quittingQuitters action).map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
  ext who
  by_cases hwho : who ∈ players
  · have happ : quittingPrincipalAction players action who =
        action ⟨who, hwho⟩ := by
      simpa only [quittingPrincipalAction] using
        principalExtend_apply_mem players (fun _ => false) action
          ⟨who, hwho⟩
    simp [quittingQuitters, happ, hwho]
  · simp [quittingQuitters, hwho]

/-- One-stage payoff commutes exactly with principal action and reward
restriction. -/
theorem quittingRootPayoff_principalAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (players : Finset ι)
    (action : players → Bool) (who : players) :
    quittingRootPayoff reward continuation
        (quittingPrincipalAction players action) who.1 =
      quittingRootPayoff (quittingPrincipalReward reward players)
        (fun principalWho => continuation principalWho.1) action who := by
  unfold quittingRootPayoff
  rw [quittingQuitters_principalAction]
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp only [Finset.map_nonempty, hquit, dite_true]
    rfl
  · have hmapped : ¬((quittingQuitters action).map
        ⟨Subtype.val, Subtype.val_injective⟩).Nonempty := by
      simpa only [Finset.map_nonempty] using hquit
    simp only [hquit, hmapped, dite_false]

/-- Expected one-stage payoff is unchanged when pure-Continue coordinates are
deleted and rewards, continuation values, and the receiver are restricted to
the retained subtype. -/
theorem quittingRootExpectedPayoff_principal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (players : Finset ι)
    (hpure : ∀ who, who ∉ players → root who = PMF.pure false)
    (who : players) :
    quittingRootExpectedPayoff reward continuation root who.1 =
      quittingRootExpectedPayoff (quittingPrincipalReward reward players)
        (fun principalWho => continuation principalWho.1)
        (principalMarginals root players) who := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_eq_principal root players (fun _ => false) hpure]
  apply congrArg (expect (pmfPi (principalMarginals root players)))
  funext action
  exact quittingRootPayoff_principalAction
    reward continuation players action who

omit [Fintype ι] in
/-- Restriction commutes with updating one retained marginal. -/
theorem principalMarginals_update
    (root : ι → PMF Bool) (players : Finset ι)
    (who : players) (marginal : PMF Bool) :
    principalMarginals (Function.update root who.1 marginal) players =
      Function.update (principalMarginals root players) who marginal := by
  funext other
  by_cases heq : other = who
  · subst heq
    simp [principalMarginals]
  · have hval : other.1 ≠ who.1 := fun h =>
      heq (Subtype.ext h)
    simp [principalMarginals, Function.update_of_ne, heq, hval]

omit [Fintype ι] in
/-- Updating a retained marginal preserves the pure-Continue condition on
every omitted coordinate. -/
theorem update_eq_pureContinue_off_principal
    (root : ι → PMF Bool) (players : Finset ι)
    (hpure : ∀ outside, outside ∉ players →
      root outside = PMF.pure false)
    (who : players) (marginal : PMF Bool) :
    ∀ outside, outside ∉ players →
      Function.update root who.1 marginal outside = PMF.pure false := by
  intro outside houtside
  have hne : outside ≠ who.1 := by
    intro heq
    subst heq
    exact houtside who.2
  rw [Function.update_of_ne hne]
  exact hpure outside houtside

/-- A retained player's updated expected payoff commutes with principal
restriction. -/
theorem quittingRootExpectedPayoff_update_principal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (players : Finset ι)
    (hpure : ∀ outside, outside ∉ players →
      root outside = PMF.pure false)
    (who : players) (marginal : PMF Bool) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root who.1 marginal) who.1 =
      quittingRootExpectedPayoff (quittingPrincipalReward reward players)
        (fun principalWho => continuation principalWho.1)
        (Function.update (principalMarginals root players) who marginal) who := by
  rw [← principalMarginals_update]
  exact quittingRootExpectedPayoff_principal reward continuation
    (Function.update root who.1 marginal) players
    (update_eq_pureContinue_off_principal root players hpure who marginal) who

/-- The prescribed successor payoff of a retained player commutes with
principal restriction. -/
theorem quittingRootSuccessorPayoff_principal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (players : Finset ι)
    (hpure : ∀ outside, outside ∉ players →
      root outside = PMF.pure false)
    (who : players) :
    quittingRootSuccessorPayoff reward continuation root who.1 =
      quittingRootSuccessorPayoff (quittingPrincipalReward reward players)
        (fun principalWho => continuation principalWho.1)
        (principalMarginals root players) who :=
  quittingRootExpectedPayoff_principal reward continuation root players hpure who

/-- Pure-Quit minus pure-Continue payoff of a retained player commutes with
principal restriction. -/
theorem quittingRootEndpointDifference_principal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (players : Finset ι)
    (hpure : ∀ outside, outside ∉ players →
      root outside = PMF.pure false)
    (who : players) :
    quittingRootEndpointDifference reward continuation root who.1 =
      quittingRootEndpointDifference (quittingPrincipalReward reward players)
        (fun principalWho => continuation principalWho.1)
        (principalMarginals root players) who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_update_principal reward continuation root
      players hpure who (PMF.pure true),
    quittingRootExpectedPayoff_update_principal reward continuation root
      players hpure who (PMF.pure false)]

end QuittingLCPClassification
end GameTheory
