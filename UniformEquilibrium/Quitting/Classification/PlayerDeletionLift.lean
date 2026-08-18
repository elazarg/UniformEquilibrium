/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PlayerDeletion
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Stationary.CoalitionToggleDeletion
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Exact deletion of universally Never players

Fix a decidable predicate `deleted` on the players and restrict the quitting
table to the subtype `{who : ι // ¬ deleted who}` of survivors.  This module
supplies the naturality which is absent from the equivalence-only player
reindexing API of
`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`: a behavioral
profile of the reduced game lifts to the original game by making every deleted
player Continue surely, and every surviving player's on-path payoff, arbitrary
behavioral deviation payoff, and best-response value are exactly preserved.

Deleting one player `owner` is the predicate `fun who => who = owner`, whose
survivor type is `QuittingDeletedPlayer owner` and whose reduced table is
`quittingDeletePlayerReward`.  Deleting a whole block `B` is the predicate
`fun who => who ∈ B`, treated in
`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`.  Both are
instances of the same constructions and of the same proofs; nothing below
depends on the shape of the deleted set.

The construction is kept at the live-root level.  This loses no behavioral
generality in a quitting game: terminal payoffs and arbitrary unilateral
behavioral deviations depend only on the unique all-Continue public history.

Under `QuittingOwnerJoinAntitone` a deleted single owner has exactly zero
best-response debt on every lifted profile, so a witnessed terminal
exploitability gap descends to the reduced table without loss.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The reduced table -/

/-- Embed a nonempty coalition of surviving players in the original player
type. -/
def quittingExtendDeletedCoalition (deleted : ι → Prop)
    (terminal : {S : Finset {who : ι // ¬ deleted who} // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} :=
  ⟨terminal.1.map
      (Function.Embedding.subtype (p := fun who : ι => ¬ deleted who)),
    Finset.map_nonempty.mpr terminal.2⟩

/-- Restriction of a quitting reward table to the surviving players. -/
def quittingDeleteReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop) :
    {S : Finset {who : ι // ¬ deleted who} // S.Nonempty} →
      Payoff {who : ι // ¬ deleted who} :=
  fun terminal who =>
    reward (quittingExtendDeletedCoalition deleted terminal) who.1

/-- Restriction of a quitting reward table to the players other than
`owner`. -/
abbrev quittingDeletePlayerReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    {S : Finset (QuittingDeletedPlayer owner) // S.Nonempty} →
      Payoff (QuittingDeletedPlayer owner) :=
  quittingDeleteReward reward (fun who => who = owner)

/-! ## Extending actions, roots and payoff vectors -/

/-- Extend an action of the reduced game by making every deleted player
Continue. -/
def quittingExtendDeletedAction (deleted : ι → Prop) [DecidablePred deleted]
    (action : {who : ι // ¬ deleted who} → Bool) : ι → Bool :=
  fun who => if h : deleted who then false else action ⟨who, h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedAction_of_deleted (deleted : ι → Prop)
    [DecidablePred deleted] (action : {who : ι // ¬ deleted who} → Bool)
    {who : ι} (hwho : deleted who) :
    quittingExtendDeletedAction deleted action who = false := by
  simp [quittingExtendDeletedAction, hwho]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedAction_apply (deleted : ι → Prop)
    [DecidablePred deleted] (action : {who : ι // ¬ deleted who} → Bool)
    (who : {who : ι // ¬ deleted who}) :
    quittingExtendDeletedAction deleted action who.1 = action who := by
  simp [quittingExtendDeletedAction, who.2]

omit [Fintype ι] [DecidableEq ι] in
theorem quittingExtendDeletedAction_injective (deleted : ι → Prop)
    [DecidablePred deleted] :
    Function.Injective (quittingExtendDeletedAction deleted) := by
  intro first second heq
  funext who
  have h := congrFun heq who.1
  simpa using h

/-- Extend a reduced product root by making every deleted player Continue
surely. -/
def quittingExtendDeletedRoot (deleted : ι → Prop) [DecidablePred deleted]
    (root : {who : ι // ¬ deleted who} → PMF Bool) : ι → PMF Bool :=
  fun who => if h : deleted who then PMF.pure false else root ⟨who, h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedRoot_of_deleted (deleted : ι → Prop)
    [DecidablePred deleted] (root : {who : ι // ¬ deleted who} → PMF Bool)
    {who : ι} (hwho : deleted who) :
    quittingExtendDeletedRoot deleted root who = PMF.pure false := by
  simp [quittingExtendDeletedRoot, hwho]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedRoot_apply (deleted : ι → Prop)
    [DecidablePred deleted] (root : {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who}) :
    quittingExtendDeletedRoot deleted root who.1 = root who := by
  simp [quittingExtendDeletedRoot, who.2]

/-- The full product law with sure-Continue deleted coordinates is the push
forward of the reduced product law under action extension. -/
theorem pmfPi_quittingExtendDeletedRoot (deleted : ι → Prop)
    [DecidablePred deleted] (root : {who : ι // ¬ deleted who} → PMF Bool) :
    pmfPi (quittingExtendDeletedRoot deleted root) =
      PMF.map (quittingExtendDeletedAction deleted) (pmfPi root) := by
  classical
  ext action
  rw [pmfPi_apply, PMF.map_apply, tsum_fintype]
  by_cases hquiet : ∀ who, deleted who → action who = false
  · let reduced : {who : ι // ¬ deleted who} → Bool := fun who => action who.1
    have hext : quittingExtendDeletedAction deleted reduced = action := by
      funext who
      by_cases h : deleted who
      · simp [quittingExtendDeletedAction, h, hquiet who h]
      · simp [quittingExtendDeletedAction, reduced, h]
    have hprod :
        (∏ who : ι, quittingExtendDeletedRoot deleted root who (action who)) =
          ∏ who : {who : ι // ¬ deleted who}, root who (reduced who) := by
      rw [← Fintype.prod_subtype_mul_prod_subtype deleted
        (fun who => quittingExtendDeletedRoot deleted root who (action who))]
      rw [Finset.prod_eq_one (fun who _ => by
        simp [quittingExtendDeletedRoot, who.2, hquiet who.1 who.2]), one_mul]
      exact Finset.prod_congr rfl fun who _ => by simp [reduced]
    rw [hprod]
    change (pmfPi root) reduced = _
    symm
    have hsum :
        (∑ b ∈ Finset.univ,
          if action = quittingExtendDeletedAction deleted b then
            (pmfPi root) b else 0) =
          (if action = quittingExtendDeletedAction deleted reduced then
            (pmfPi root) reduced else 0) := by
      apply Finset.sum_eq_single reduced
      · intro other _ hne
        have hneq : action ≠ quittingExtendDeletedAction deleted other := by
          intro heq
          apply hne
          apply quittingExtendDeletedAction_injective deleted
          exact heq.symm.trans hext.symm
        simp [hneq]
      · simp
    rw [if_pos hext.symm] at hsum
    convert hsum using 1
    congr 1
    funext other
    by_cases h : action = quittingExtendDeletedAction deleted other <;> simp [h]
  · push Not at hquiet
    obtain ⟨bad, hbad, hbadTrue⟩ := hquiet
    have hbadEq : action bad = true := by
      cases h : action bad <;> simp_all
    have hprod :
        (∏ who : ι, quittingExtendDeletedRoot deleted root who (action who)) =
          0 := by
      rw [← Fintype.prod_subtype_mul_prod_subtype deleted
        (fun who => quittingExtendDeletedRoot deleted root who (action who))]
      rw [Finset.prod_eq_zero (Finset.mem_univ (⟨bad, hbad⟩ :
        {who : ι // deleted who})) (by
          simp [quittingExtendDeletedRoot, hbad, hbadEq]), zero_mul]
    rw [hprod]
    symm
    have hsum :
        (∑ reduced ∈ Finset.univ,
          if action = quittingExtendDeletedAction deleted reduced then
            (pmfPi root) reduced else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro reduced _
      simp [show action ≠ quittingExtendDeletedAction deleted reduced by
        intro heq
        have := congrFun heq bad
        simp [hbadEq, hbad] at this]
    convert hsum using 1
    congr 1
    funext reduced
    by_cases h : action = quittingExtendDeletedAction deleted reduced <;>
      simp [h]

/-- Extend a reduced payoff vector by irrelevant zero coordinates on the
deleted players. -/
def quittingExtendDeletedPayoff (deleted : ι → Prop) [DecidablePred deleted]
    (payoff : Payoff {who : ι // ¬ deleted who}) : Payoff ι :=
  fun who => if h : deleted who then 0 else payoff ⟨who, h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedPayoff_apply (deleted : ι → Prop)
    [DecidablePred deleted] (payoff : Payoff {who : ι // ¬ deleted who})
    (who : {who : ι // ¬ deleted who}) :
    quittingExtendDeletedPayoff deleted payoff who.1 = payoff who := by
  simp [quittingExtendDeletedPayoff, who.2]

omit [DecidableEq ι] in
/-- Extending a reduced action maps its quitter set to the corresponding
coalition in the original player type. -/
theorem quittingQuitters_extendDeletedAction (deleted : ι → Prop)
    [DecidablePred deleted] (action : {who : ι // ¬ deleted who} → Bool) :
    quittingQuitters (quittingExtendDeletedAction deleted action) =
      (quittingQuitters action).map
        (Function.Embedding.subtype (p := fun who : ι => ¬ deleted who)) := by
  classical
  ext who
  by_cases h : deleted who
  · simp [quittingQuitters, quittingExtendDeletedAction, h]
  · simp [quittingQuitters, quittingExtendDeletedAction, h]

/-! ## One-stage naturality -/

omit [DecidableEq ι] in
/-- One-stage root payoffs commute with deletion for every surviving
coordinate. -/
theorem quittingRootPayoff_extendDeletedAction_of_apply_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (fullContinuation : Payoff ι)
    (continuation : Payoff {who : ι // ¬ deleted who})
    (action : {who : ι // ¬ deleted who} → Bool)
    (who : {who : ι // ¬ deleted who})
    (hcontinuation : fullContinuation who.1 = continuation who) :
    quittingRootPayoff reward fullContinuation
        (quittingExtendDeletedAction deleted action) who.1 =
      quittingRootPayoff (quittingDeleteReward reward deleted)
        continuation action who := by
  classical
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hextQuit :
        (quittingQuitters
          (quittingExtendDeletedAction deleted action)).Nonempty := by
      rw [quittingQuitters_extendDeletedAction]
      exact Finset.map_nonempty.mpr hquit
    rw [quittingRootPayoff, dif_pos hextQuit,
      quittingRootPayoff, dif_pos hquit]
    unfold quittingDeleteReward quittingExtendDeletedCoalition
    congr 2
    exact quittingQuitters_extendDeletedAction deleted action
  · have hextQuit :
        ¬(quittingQuitters
          (quittingExtendDeletedAction deleted action)).Nonempty := by
      rw [quittingQuitters_extendDeletedAction]
      exact fun h => hquit (Finset.map_nonempty.mp h)
    rw [quittingRootPayoff, dif_neg hextQuit,
      quittingRootPayoff, dif_neg hquit]
    exact hcontinuation

omit [DecidableEq ι] in
/-- The extension form of one-stage payoff naturality. -/
theorem quittingRootPayoff_extendDeletedAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted] (continuation : Payoff {who : ι // ¬ deleted who})
    (action : {who : ι // ¬ deleted who} → Bool)
    (who : {who : ι // ¬ deleted who}) :
    quittingRootPayoff reward (quittingExtendDeletedPayoff deleted continuation)
        (quittingExtendDeletedAction deleted action) who.1 =
      quittingRootPayoff (quittingDeleteReward reward deleted)
        continuation action who :=
  quittingRootPayoff_extendDeletedAction_of_apply_eq
    reward deleted (quittingExtendDeletedPayoff deleted continuation)
      continuation action who
      (quittingExtendDeletedPayoff_apply deleted continuation who)

/-- Root-payoff naturality only needs agreement of the two continuation
vectors at the displayed surviving player. -/
theorem quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (fullContinuation : Payoff ι)
    (continuation : Payoff {who : ι // ¬ deleted who})
    (root : {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who})
    (hcontinuation : fullContinuation who.1 = continuation who) :
    quittingRootExpectedPayoff reward fullContinuation
        (quittingExtendDeletedRoot deleted root) who.1 =
      quittingRootExpectedPayoff (quittingDeleteReward reward deleted)
        continuation root who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_quittingExtendDeletedRoot, expect_map]
  apply congrArg (expect (pmfPi root))
  funext action
  exact quittingRootPayoff_extendDeletedAction_of_apply_eq
    reward deleted fullContinuation continuation action who hcontinuation

/-- Expected one-stage payoffs commute with deletion for every surviving
coordinate. -/
theorem quittingRootExpectedPayoff_extendDeletedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted] (continuation : Payoff {who : ι // ¬ deleted who})
    (root : {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who}) :
    quittingRootExpectedPayoff reward
        (quittingExtendDeletedPayoff deleted continuation)
        (quittingExtendDeletedRoot deleted root) who.1 =
      quittingRootExpectedPayoff (quittingDeleteReward reward deleted)
        continuation root who :=
  quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq
    reward deleted (quittingExtendDeletedPayoff deleted continuation)
      continuation root who
      (quittingExtendDeletedPayoff_apply deleted continuation who)

omit [Fintype ι] in
/-- Extending roots commutes with updating a surviving coordinate. -/
theorem Function.update_quittingExtendDeletedRoot (deleted : ι → Prop)
    [DecidablePred deleted] (root : {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who}) (hazard : PMF Bool) :
    Function.update (quittingExtendDeletedRoot deleted root) who.1 hazard =
      quittingExtendDeletedRoot deleted (Function.update root who hazard) := by
  funext player
  by_cases hp : player = who.1
  · subst player
    rw [Function.update_self]
    simp
  · by_cases ho : deleted player
    · rw [Function.update_of_ne hp]
      simp [ho]
    · rw [Function.update_of_ne hp]
      unfold quittingExtendDeletedRoot
      rw [dif_neg ho]
      have hsub : (⟨player, ho⟩ : {w : ι // ¬ deleted w}) ≠ who := by
        intro heq
        exact hp (congrArg Subtype.val heq)
      rw [dif_neg ho]
      simp [Function.update_of_ne hsub]

/-! ## Naturality along a chronology -/

/-- Extend every row of a reduced root chronology by making the deleted
players Continue. -/
def quittingExtendDeletedRoots (deleted : ι → Prop) [DecidablePred deleted]
    (roots : ℕ → {who : ι // ¬ deleted who} → PMF Bool) :
    ℕ → ι → PMF Bool :=
  fun time => quittingExtendDeletedRoot deleted (roots time)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedRoots_of_deleted (deleted : ι → Prop)
    [DecidablePred deleted]
    (roots : ℕ → {who : ι // ¬ deleted who} → PMF Bool) (time : ℕ)
    {who : ι} (hwho : deleted who) :
    quittingExtendDeletedRoots deleted roots time who = PMF.pure false := by
  simp [quittingExtendDeletedRoots, hwho]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingExtendDeletedRoots_apply (deleted : ι → Prop)
    [DecidablePred deleted]
    (roots : ℕ → {who : ι // ¬ deleted who} → PMF Bool) (time : ℕ)
    (who : {who : ι // ¬ deleted who}) :
    quittingExtendDeletedRoots deleted roots time who.1 = roots time who := by
  simp [quittingExtendDeletedRoots]

/-- Every finite zero-boundary unilateral payoff is preserved under the Never
lift, for arbitrary hazards of a surviving player. -/
theorem quittingFiniteRootPayoff_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (roots : ℕ → {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who}) (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingFiniteRootPayoff reward
          (quittingExtendDeletedRoots deleted roots) who.1 hazard start fuel =
        quittingFiniteRootPayoff (quittingDeleteReward reward deleted)
          roots who hazard start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff, quittingFiniteRootPayoff,
        show quittingExtendDeletedRoots deleted roots start =
          quittingExtendDeletedRoot deleted (roots start) by rfl,
        Function.update_quittingExtendDeletedRoot]
      exact quittingRootExpectedPayoff_extendDeletedRoot_of_apply_eq
        reward deleted
          (fun _ => quittingFiniteRootPayoff reward
            (quittingExtendDeletedRoots deleted roots) who.1 hazard
              (start + 1) fuel)
          (fun _ => quittingFiniteRootPayoff
            (quittingDeleteReward reward deleted) roots who hazard
              (start + 1) fuel)
          (Function.update (roots start) who (hazard start)) who (ih (start + 1))

/-- Infinite terminal values of arbitrary surviving-player hazard deviations
are preserved by the Never lift. -/
theorem quittingRootSequenceHazardTerminalValue_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (roots : ℕ → {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who}) (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingExtendDeletedRoots deleted roots) who.1 hazard start =
      quittingRootSequenceHazardTerminalValue
        (quittingDeleteReward reward deleted) roots who hazard start := by
  have hfull := tendsto_quittingFiniteRootPayoff_terminal reward
    (quittingExtendDeletedRoots deleted roots) who.1 hazard start
  have hreduced := tendsto_quittingFiniteRootPayoff_terminal
    (quittingDeleteReward reward deleted) roots who hazard start
  apply tendsto_nhds_unique hfull
  apply hreduced.congr'
  exact Filter.Eventually.of_forall fun fuel =>
    (quittingFiniteRootPayoff_extendDeletedRoots
      reward deleted roots who hazard start fuel).symm

/-- The prescribed terminal value of a reduced chronology is preserved by the
Never lift. -/
theorem quittingRootSequenceTerminalValue_extendDeletedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (roots : ℕ → {who : ι // ¬ deleted who} → PMF Bool)
    (who : {who : ι // ¬ deleted who}) (start : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingExtendDeletedRoots deleted roots) who.1 start =
      quittingRootSequenceTerminalValue
        (quittingDeleteReward reward deleted) roots who start := by
  have hfull := tendsto_quittingFiniteRootPayoff_self_terminalValue reward
    (quittingExtendDeletedRoots deleted roots) who.1 start
  have hreduced := tendsto_quittingFiniteRootPayoff_self_terminalValue
    (quittingDeleteReward reward deleted) roots who start
  apply tendsto_nhds_unique hfull
  apply hreduced.congr'
  exact Filter.Eventually.of_forall fun fuel => by
    simpa using (quittingFiniteRootPayoff_extendDeletedRoots reward deleted roots
      who (fun time => roots time who) start fuel).symm

/-! ## The profile lift -/

/-- Lift an arbitrary reduced behavioral profile through its canonical live
root sequence, making every deleted player Continue surely. -/
def quittingLiftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingInfinitePathProfile reward
    (quittingExtendDeletedRoots deleted
      (quittingProfileLiveRoot (quittingDeleteReward reward deleted) profile))

omit [DecidableEq ι] in
@[simp] theorem quittingProfileLiveRoot_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingLiftDeletedProfile reward deleted profile) =
      quittingExtendDeletedRoots deleted
        (quittingProfileLiveRoot (quittingDeleteReward reward deleted)
          profile) := by
  unfold quittingLiftDeletedProfile
  exact quittingProfileLiveRoot_infinitePathProfile _ _

/-- Every surviving player's on-path terminal payoff is exactly preserved by
the profile lift. -/
theorem quittingTerminalPayoff_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who}) :
    quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward deleted profile) who.1 =
      quittingTerminalPayoff (quittingDeleteReward reward deleted)
        profile who := by
  unfold quittingLiftDeletedProfile
  rw [quittingTerminalPayoff_infinitePathProfile,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  exact quittingRootSequenceTerminalValue_extendDeletedRoots reward deleted
    (quittingProfileLiveRoot (quittingDeleteReward reward deleted) profile)
      who 0

/-- Pure quit-time deviations of surviving players have exactly the same
payoff before and after the lift. -/
theorem quittingTerminalPayoff_update_pureTime_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who}) (quitTime : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update (quittingLiftDeletedProfile reward deleted profile)
          who.1 (quittingPureTimeBehaviorStrategy reward who.1 quitTime)) who.1 =
      quittingTerminalPayoff (quittingDeleteReward reward deleted)
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy
            (quittingDeleteReward reward deleted) who quitTime)) who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  unfold quittingLiftDeletedProfile
  rw [quittingProfileLiveRoot_infinitePathProfile]
  exact quittingRootSequenceHazardTerminalValue_extendDeletedRoots
    reward deleted
      (quittingProfileLiveRoot (quittingDeleteReward reward deleted) profile)
      who (quittingPureTimeHazard quitTime) 0

/-- The full behavioral best-response value of every surviving player is
exactly preserved by the Never lift.  This is stronger than the inequality
needed for approximate equilibria: no accuracy is lost in either
direction. -/
theorem quittingBestReplyValue_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who}) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward deleted profile) who.1 =
      quittingBestReplyValue (quittingDeleteReward reward deleted)
        profile who := by
  apply le_antisymm
  · apply quittingBestReplyValue_le
    intro deviation
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨quitTime, htime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward (quittingLiftDeletedProfile reward deleted profile) who.1
          deviation hε
    calc
      quittingTerminalPayoff reward
          (Function.update (quittingLiftDeletedProfile reward deleted profile)
            who.1 deviation) who.1 ≤
        quittingTerminalPayoff reward
            (Function.update (quittingLiftDeletedProfile reward deleted profile)
              who.1
              (quittingPureTimeBehaviorStrategy reward who.1 quitTime)) who.1 +
          ε := htime
      _ = quittingTerminalPayoff (quittingDeleteReward reward deleted)
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy
                (quittingDeleteReward reward deleted) who quitTime)) who +
          ε := by rw [quittingTerminalPayoff_update_pureTime_liftDeletedProfile]
      _ ≤ quittingBestReplyValue (quittingDeleteReward reward deleted)
            profile who + ε := by
        have hle := le_quittingBestReplyValue
          (quittingDeleteReward reward deleted) profile who
          (quittingPureTimeBehaviorStrategy
            (quittingDeleteReward reward deleted) who quitTime)
        linarith
  · apply quittingBestReplyValue_le
    intro deviation
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨quitTime, htime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        (quittingDeleteReward reward deleted) profile who deviation hε
    calc
      quittingTerminalPayoff (quittingDeleteReward reward deleted)
          (Function.update profile who deviation) who ≤
        quittingTerminalPayoff (quittingDeleteReward reward deleted)
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy
                (quittingDeleteReward reward deleted) who quitTime)) who +
          ε := htime
      _ = quittingTerminalPayoff reward
            (Function.update (quittingLiftDeletedProfile reward deleted profile)
              who.1
              (quittingPureTimeBehaviorStrategy reward who.1 quitTime)) who.1 +
          ε := by rw [quittingTerminalPayoff_update_pureTime_liftDeletedProfile]
      _ ≤ quittingBestReplyValue reward
            (quittingLiftDeletedProfile reward deleted profile) who.1 + ε :=
        by
          have hle := le_quittingBestReplyValue reward
            (quittingLiftDeletedProfile reward deleted profile) who.1
            (quittingPureTimeBehaviorStrategy reward who.1 quitTime)
          linarith

/-- Read the live-path hazard of an original-game deviation as a behavioral
strategy of the reduced game.  Off the unique live history its history
argument is irrelevant. -/
def quittingDeletedDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted] (who : {who : ι // ¬ deleted who})
    (deviation : (quittingGame reward).BehaviorStrategy who.1) :
    (quittingGame (quittingDeleteReward reward deleted)).BehaviorStrategy who :=
  fun time _ => quittingBehaviorLiveHazard reward deviation time

/-- An arbitrary behavioral deviation by a surviving player has exactly the
same payoff after deletion.  This is stronger than equality of suprema and
preserves a witnessed exploitability gap without epsilon loss. -/
theorem quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who})
    (deviation : (quittingGame reward).BehaviorStrategy who.1) :
    quittingTerminalPayoff reward
        (Function.update (quittingLiftDeletedProfile reward deleted profile)
          who.1 deviation) who.1 =
      quittingTerminalPayoff (quittingDeleteReward reward deleted)
        (Function.update profile who
          (quittingDeletedDeviation reward deleted who deviation)) who := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_liftDeletedProfile]
  unfold quittingDeletedDeviation quittingBehaviorLiveHazard
  exact quittingRootSequenceHazardTerminalValue_extendDeletedRoots
    reward deleted
      (quittingProfileLiveRoot (quittingDeleteReward reward deleted) profile)
      who (fun time => deviation time (quittingLiveHist reward time)) 0

/-- The lifted profile already has every deleted player playing literal Never
on every history. -/
theorem Function.update_liftDeletedProfile_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deleted : ι → Prop)
    [DecidablePred deleted]
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    {owner : ι} (howner : deleted owner) :
    Function.update (quittingLiftDeletedProfile reward deleted profile) owner
        (quittingPureTimeBehaviorStrategy reward owner none) =
      quittingLiftDeletedProfile reward deleted profile := by
  funext player time history
  by_cases hp : player = owner
  · subst player
    simp [quittingPureTimeBehaviorStrategy, quittingLiftDeletedProfile,
      quittingInfinitePathProfile,
      quittingRootSequenceProfile, quittingExtendDeletedRoots, howner]
  · simp [Function.update_of_ne hp]

/-! ## Deleting a single universally Never owner -/

/-- In the antitone branch, the deleted owner has exactly zero debt on every
lifted reduced profile. -/
theorem quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (profile : (quittingGame
      (quittingDeletePlayerReward reward owner)).BehaviorProfile)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward (fun who => who = owner) profile)
        owner =
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward (fun who => who = owner) profile)
        owner := by
  rw [quittingBestReplyValue_eq_never_of_ownerJoinAntitone
    reward (quittingLiftDeletedProfile reward (fun who => who = owner) profile)
      owner hjoin hsolo hchi]
  rw [Function.update_liftDeletedProfile_never reward (fun who => who = owner)
    profile rfl]

/-- **Exact exploitability-floor descent.**  If the owner-side coalition
increments are all nonpositive at the negative singleton gate, deleting the
universal-Never owner preserves a witnessed positive terminal
exploitability gap exactly.  The proof also covers an empty complement: in
that case its conclusion is impossible, so the hypotheses themselves rule
out the original positive floor. -/
theorem hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    HasTerminalExploitabilityGap
      (quittingDeletePlayerReward reward owner) gap := by
  intro profile
  obtain ⟨player, deviation, hdeviation⟩ :=
    hexploit (quittingLiftDeletedProfile reward (fun who => who = owner) profile)
  by_cases hp : player = owner
  · subst player
    have hbest := quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff
      reward owner profile hjoin hsolo hchi
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftDeletedProfile reward (fun who => who = owner) profile)
      owner deviation
    linarith
  · let who : QuittingDeletedPlayer owner := ⟨player, hp⟩
    refine ⟨who, quittingDeletedDeviation reward (fun w => w = owner) who
      deviation, ?_⟩
    have hon := quittingTerminalPayoff_liftDeletedProfile
      reward (fun w => w = owner) profile who
    have hdev :=
      quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
        reward (fun w => w = owner) profile who deviation
    dsimp only [who] at hon hdev
    linarith

/-- A positive gap in the deletion branch forces the complement of the owner
to be inhabited.  Thus the one-player edge case is discharged before any
cardinality induction is invoked. -/
theorem nonempty_deletedPlayer_of_ownerJoinAntitone_and_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hjoin : QuittingOwnerJoinAntitone reward owner)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    Nonempty (QuittingDeletedPlayer owner) := by
  have hdeleted :=
    hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone
      reward owner hgap hexploit hjoin hsolo hchi
  obtain ⟨who, _deviation, _⟩ :=
    hdeleted (quittingAlwaysContinueProfile
      (quittingDeletePlayerReward reward owner))
  exact ⟨who⟩

end GameTheory
