/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Exceptional.InfiniteLTG
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Stationary.CoalitionToggleDeletion
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Deleting a whole block of universal Never players

`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean` restricts
a quitting table to the complement of a single player.  This module restricts
the table to the complement of an arbitrary `Finset` of players at once and
supplies the same naturality: a behavioral profile of the survivor game lifts
to the original game by making every deleted player Continue surely, and every
surviving player's on-path payoff and arbitrary behavioral deviation payoff are
exactly preserved.

The construction is kept at the live-root level.  This loses no behavioral
generality in a quitting game: terminal payoffs and arbitrary unilateral
behavioral deviations depend only on the unique all-Continue public history.

`QuittingBlockDispensable` is the deletion gate, a pair of finite table checks:
the block form of `QuittingOwnerJoinAntitone` over the survivors, and a solo
reward at most the survivor continue floor.  When every member of the block
passes it, `hasTerminalExploitabilityGap_deleteBlock_of_dispensable` carries a
witnessed terminal exploitability gap to the survivor table with no loss, and
`exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable` carries a
uniform-equilibrium payoff back, unchanged at every survivor.  Deleting a whole
block at once is a weaker demand than deleting its members one at a time,
because the gate quantifies only over coalitions of survivors.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The players that survive deletion of the block `B`. -/
abbrev QuittingBlockSurvivor {ι : Type} (B : Finset ι) := {who : ι // who ∉ B}

/-- Embed a nonempty coalition of surviving players in the original player
type. -/
def quittingExtendBlockCoalition (B : Finset ι)
    (terminal : {S : Finset (QuittingBlockSurvivor B) // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} :=
  ⟨terminal.1.map
      (Function.Embedding.subtype (p := fun who : ι => who ∉ B)),
    Finset.map_nonempty.mpr terminal.2⟩

/-- Restriction of a quitting reward table to the players outside `B`. -/
def quittingDeleteBlockReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι) :
    {S : Finset (QuittingBlockSurvivor B) // S.Nonempty} →
      Payoff (QuittingBlockSurvivor B) :=
  fun terminal who => reward (quittingExtendBlockCoalition B terminal) who.1

/-- Extend an action of the survivor game by making every deleted player
Continue. -/
def quittingExtendBlockAction (B : Finset ι)
    (action : QuittingBlockSurvivor B → Bool) : ι → Bool :=
  fun who => if h : who ∈ B then false else action ⟨who, h⟩

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockAction_of_mem (B : Finset ι)
    (action : QuittingBlockSurvivor B → Bool) {who : ι} (hwho : who ∈ B) :
    quittingExtendBlockAction B action who = false := by
  simp [quittingExtendBlockAction, hwho]

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockAction_apply (B : Finset ι)
    (action : QuittingBlockSurvivor B → Bool)
    (who : QuittingBlockSurvivor B) :
    quittingExtendBlockAction B action who.1 = action who := by
  simp [quittingExtendBlockAction, who.2]

omit [Fintype ι] in
theorem quittingExtendBlockAction_injective (B : Finset ι) :
    Function.Injective (quittingExtendBlockAction B) := by
  intro first second heq
  funext who
  have h := congrFun heq who.1
  simpa using h

/-- Extend a survivor product root by making every deleted player Continue
surely. -/
def quittingExtendBlockRoot (B : Finset ι)
    (root : QuittingBlockSurvivor B → PMF Bool) : ι → PMF Bool :=
  fun who => if h : who ∈ B then PMF.pure false else root ⟨who, h⟩

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockRoot_of_mem (B : Finset ι)
    (root : QuittingBlockSurvivor B → PMF Bool) {who : ι} (hwho : who ∈ B) :
    quittingExtendBlockRoot B root who = PMF.pure false := by
  simp [quittingExtendBlockRoot, hwho]

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockRoot_apply (B : Finset ι)
    (root : QuittingBlockSurvivor B → PMF Bool)
    (who : QuittingBlockSurvivor B) :
    quittingExtendBlockRoot B root who.1 = root who := by
  simp [quittingExtendBlockRoot, who.2]

/-- Splitting a product over the player type along the deleted block. -/
theorem prod_split_quittingBlock {M : Type*} [CommMonoid M] (B : Finset ι)
    (value : ι → M) :
    (∏ who : ι, value who) =
      (∏ who ∈ B, value who) * ∏ who : QuittingBlockSurvivor B, value who.1 := by
  classical
  rw [← Finset.prod_mul_prod_compl B value]
  congr 1
  exact Finset.prod_subtype Bᶜ (fun x => by simp) value

/-- The full product law with sure-Continue deleted coordinates is the push
forward of the survivor product law under action extension. -/
theorem pmfPi_quittingExtendBlockRoot
    (B : Finset ι) (root : QuittingBlockSurvivor B → PMF Bool) :
    pmfPi (quittingExtendBlockRoot B root) =
      PMF.map (quittingExtendBlockAction B) (pmfPi root) := by
  classical
  ext action
  rw [pmfPi_apply, PMF.map_apply, tsum_fintype]
  by_cases hblock : ∀ who ∈ B, action who = false
  · let reduced : QuittingBlockSurvivor B → Bool := fun who => action who.1
    have hext : quittingExtendBlockAction B reduced = action := by
      funext who
      by_cases h : who ∈ B
      · simp [quittingExtendBlockAction, h, hblock who h]
      · simp [quittingExtendBlockAction, reduced, h]
    have hprod :
        (∏ who : ι, quittingExtendBlockRoot B root who (action who)) =
          ∏ who : QuittingBlockSurvivor B, root who (reduced who) := by
      rw [prod_split_quittingBlock B
        (fun who => quittingExtendBlockRoot B root who (action who))]
      rw [Finset.prod_eq_one (fun who hwho => by
        simp [quittingExtendBlockRoot, hwho, hblock who hwho]), one_mul]
      exact Finset.prod_congr rfl fun who _ => by simp [reduced]
    rw [hprod]
    change (pmfPi root) reduced = _
    symm
    have hsum :
        (∑ b ∈ Finset.univ,
          if action = quittingExtendBlockAction B b then
            (pmfPi root) b else 0) =
          (if action = quittingExtendBlockAction B reduced then
            (pmfPi root) reduced else 0) := by
      apply Finset.sum_eq_single reduced
      · intro other _ hne
        have hneq : action ≠ quittingExtendBlockAction B other := by
          intro heq
          apply hne
          apply quittingExtendBlockAction_injective B
          exact heq.symm.trans hext.symm
        simp [hneq]
      · simp
    rw [if_pos hext.symm] at hsum
    convert hsum using 1
    congr 1
    funext other
    by_cases h : action = quittingExtendBlockAction B other <;> simp [h]
  · push Not at hblock
    obtain ⟨bad, hbad, hbadTrue⟩ := hblock
    have hbadEq : action bad = true := by
      cases h : action bad <;> simp_all
    have hprod :
        (∏ who : ι, quittingExtendBlockRoot B root who (action who)) = 0 := by
      rw [prod_split_quittingBlock B
        (fun who => quittingExtendBlockRoot B root who (action who))]
      rw [Finset.prod_eq_zero hbad (by simp [quittingExtendBlockRoot, hbad,
        hbadEq]), zero_mul]
    rw [hprod]
    symm
    have hsum :
        (∑ reduced ∈ Finset.univ,
          if action = quittingExtendBlockAction B reduced then
            (pmfPi root) reduced else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro reduced _
      simp [show action ≠ quittingExtendBlockAction B reduced by
        intro heq
        have := congrFun heq bad
        simp [hbadEq, hbad] at this]
    convert hsum using 1
    congr 1
    funext reduced
    by_cases h : action = quittingExtendBlockAction B reduced <;> simp [h]

/-- Extend a survivor payoff vector by irrelevant zero coordinates on the
deleted block. -/
def quittingExtendBlockPayoff (B : Finset ι)
    (payoff : Payoff (QuittingBlockSurvivor B)) : Payoff ι :=
  fun who => if h : who ∈ B then 0 else payoff ⟨who, h⟩

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockPayoff_apply (B : Finset ι)
    (payoff : Payoff (QuittingBlockSurvivor B))
    (who : QuittingBlockSurvivor B) :
    quittingExtendBlockPayoff B payoff who.1 = payoff who := by
  simp [quittingExtendBlockPayoff, who.2]

/-- Extending a survivor action maps its quitter set to the corresponding
coalition in the original player type. -/
theorem quittingQuitters_extendBlockAction (B : Finset ι)
    (action : QuittingBlockSurvivor B → Bool) :
    quittingQuitters (quittingExtendBlockAction B action) =
      (quittingQuitters action).map
        (Function.Embedding.subtype (p := fun who : ι => who ∉ B)) := by
  classical
  ext who
  by_cases h : who ∈ B
  · simp [quittingQuitters, quittingExtendBlockAction, h]
  · simp [quittingQuitters, quittingExtendBlockAction, h]

/-- One-stage root payoffs commute with block deletion for every surviving
coordinate. -/
theorem quittingRootPayoff_extendBlockAction_of_apply_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (fullContinuation : Payoff ι)
    (continuation : Payoff (QuittingBlockSurvivor B))
    (action : QuittingBlockSurvivor B → Bool)
    (who : QuittingBlockSurvivor B)
    (hcontinuation : fullContinuation who.1 = continuation who) :
    quittingRootPayoff reward fullContinuation
        (quittingExtendBlockAction B action) who.1 =
      quittingRootPayoff (quittingDeleteBlockReward reward B)
        continuation action who := by
  classical
  by_cases hquit : (quittingQuitters action).Nonempty
  · have hextQuit :
        (quittingQuitters (quittingExtendBlockAction B action)).Nonempty := by
      rw [quittingQuitters_extendBlockAction]
      exact Finset.map_nonempty.mpr hquit
    rw [quittingRootPayoff, dif_pos hextQuit,
      quittingRootPayoff, dif_pos hquit]
    unfold quittingDeleteBlockReward quittingExtendBlockCoalition
    congr 2
    exact quittingQuitters_extendBlockAction B action
  · have hextQuit :
        ¬(quittingQuitters (quittingExtendBlockAction B action)).Nonempty := by
      rw [quittingQuitters_extendBlockAction]
      exact fun h => hquit (Finset.map_nonempty.mp h)
    rw [quittingRootPayoff, dif_neg hextQuit,
      quittingRootPayoff, dif_neg hquit]
    exact hcontinuation

/-- The extension form of one-stage payoff naturality. -/
theorem quittingRootPayoff_extendBlockAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (continuation : Payoff (QuittingBlockSurvivor B))
    (action : QuittingBlockSurvivor B → Bool)
    (who : QuittingBlockSurvivor B) :
    quittingRootPayoff reward (quittingExtendBlockPayoff B continuation)
        (quittingExtendBlockAction B action) who.1 =
      quittingRootPayoff (quittingDeleteBlockReward reward B)
        continuation action who :=
  quittingRootPayoff_extendBlockAction_of_apply_eq
    reward B (quittingExtendBlockPayoff B continuation)
      continuation action who
      (quittingExtendBlockPayoff_apply B continuation who)

/-- Root-payoff naturality only needs agreement of the two continuation
vectors at the displayed surviving player. -/
theorem quittingRootExpectedPayoff_extendBlockRoot_of_apply_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (fullContinuation : Payoff ι)
    (continuation : Payoff (QuittingBlockSurvivor B))
    (root : QuittingBlockSurvivor B → PMF Bool)
    (who : QuittingBlockSurvivor B)
    (hcontinuation : fullContinuation who.1 = continuation who) :
    quittingRootExpectedPayoff reward fullContinuation
        (quittingExtendBlockRoot B root) who.1 =
      quittingRootExpectedPayoff (quittingDeleteBlockReward reward B)
        continuation root who := by
  unfold quittingRootExpectedPayoff
  rw [pmfPi_quittingExtendBlockRoot, expect_map]
  apply congrArg (expect (pmfPi root))
  funext action
  exact quittingRootPayoff_extendBlockAction_of_apply_eq
    reward B fullContinuation continuation action who hcontinuation

omit [Fintype ι] in
/-- Extending roots commutes with updating a surviving coordinate. -/
theorem Function.update_quittingExtendBlockRoot
    (B : Finset ι) (root : QuittingBlockSurvivor B → PMF Bool)
    (who : QuittingBlockSurvivor B) (hazard : PMF Bool) :
    Function.update (quittingExtendBlockRoot B root) who.1 hazard =
      quittingExtendBlockRoot B (Function.update root who hazard) := by
  funext player
  by_cases hp : player = who.1
  · subst player
    rw [Function.update_self]
    simp
  · by_cases ho : player ∈ B
    · rw [Function.update_of_ne hp]
      simp [ho]
    · rw [Function.update_of_ne hp]
      unfold quittingExtendBlockRoot
      rw [dif_neg ho]
      have hsub : (⟨player, ho⟩ : QuittingBlockSurvivor B) ≠ who := by
        intro heq
        exact hp (congrArg Subtype.val heq)
      rw [dif_neg ho]
      simp [Function.update_of_ne hsub]

/-- Extend every row of a survivor root chronology by making the deleted
block Continue. -/
def quittingExtendBlockRoots (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool) :
    ℕ → ι → PMF Bool :=
  fun time => quittingExtendBlockRoot B (roots time)

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockRoots_of_mem (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool) (time : ℕ)
    {who : ι} (hwho : who ∈ B) :
    quittingExtendBlockRoots B roots time who = PMF.pure false := by
  simp [quittingExtendBlockRoots, hwho]

omit [Fintype ι] in
@[simp] theorem quittingExtendBlockRoots_apply (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool) (time : ℕ)
    (who : QuittingBlockSurvivor B) :
    quittingExtendBlockRoots B roots time who.1 = roots time who := by
  simp [quittingExtendBlockRoots]

/-- Every finite zero-boundary unilateral payoff is preserved under the block
Never lift, for arbitrary hazards of a surviving player. -/
theorem quittingFiniteRootPayoff_extendBlockRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool)
    (who : QuittingBlockSurvivor B) (hazard : ℕ → PMF Bool) :
    ∀ start fuel,
      quittingFiniteRootPayoff reward (quittingExtendBlockRoots B roots)
          who.1 hazard start fuel =
        quittingFiniteRootPayoff (quittingDeleteBlockReward reward B)
          roots who hazard start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      rw [quittingFiniteRootPayoff, quittingFiniteRootPayoff,
        show quittingExtendBlockRoots B roots start =
          quittingExtendBlockRoot B (roots start) by rfl,
        Function.update_quittingExtendBlockRoot]
      exact quittingRootExpectedPayoff_extendBlockRoot_of_apply_eq
        reward B
          (fun _ => quittingFiniteRootPayoff reward
            (quittingExtendBlockRoots B roots) who.1 hazard
              (start + 1) fuel)
          (fun _ => quittingFiniteRootPayoff
            (quittingDeleteBlockReward reward B) roots who hazard
              (start + 1) fuel)
          (Function.update (roots start) who (hazard start)) who (ih (start + 1))

/-- Infinite terminal values of arbitrary surviving-player hazard deviations
are preserved by the block Never lift. -/
theorem quittingRootSequenceHazardTerminalValue_extendBlockRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool)
    (who : QuittingBlockSurvivor B) (hazard : ℕ → PMF Bool) (start : ℕ) :
    quittingRootSequenceHazardTerminalValue reward
        (quittingExtendBlockRoots B roots) who.1 hazard start =
      quittingRootSequenceHazardTerminalValue
        (quittingDeleteBlockReward reward B) roots who hazard start := by
  have hfull := tendsto_quittingFiniteRootPayoff_terminal reward
    (quittingExtendBlockRoots B roots) who.1 hazard start
  have hreduced := tendsto_quittingFiniteRootPayoff_terminal
    (quittingDeleteBlockReward reward B) roots who hazard start
  apply tendsto_nhds_unique hfull
  apply hreduced.congr'
  exact Filter.Eventually.of_forall fun fuel =>
    (quittingFiniteRootPayoff_extendBlockRoots
      reward B roots who hazard start fuel).symm

/-- The prescribed terminal value of a survivor chronology is preserved by
the block Never lift. -/
theorem quittingRootSequenceTerminalValue_extendBlockRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool)
    (who : QuittingBlockSurvivor B) (start : ℕ) :
    quittingRootSequenceTerminalValue reward
        (quittingExtendBlockRoots B roots) who.1 start =
      quittingRootSequenceTerminalValue
        (quittingDeleteBlockReward reward B) roots who start := by
  have hfull := tendsto_quittingFiniteRootPayoff_self_terminalValue reward
    (quittingExtendBlockRoots B roots) who.1 start
  have hreduced := tendsto_quittingFiniteRootPayoff_self_terminalValue
    (quittingDeleteBlockReward reward B) roots who start
  apply tendsto_nhds_unique hfull
  apply hreduced.congr'
  exact Filter.Eventually.of_forall fun fuel => by
    simpa using (quittingFiniteRootPayoff_extendBlockRoots reward B roots
      who (fun time => roots time who) start fuel).symm

/-- Lift an arbitrary survivor behavioral profile through its canonical live
root sequence, making every deleted player Continue surely. -/
def quittingLiftBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingInfinitePathProfile reward
    (quittingExtendBlockRoots B
      (quittingProfileLiveRoot (quittingDeleteBlockReward reward B) profile))

@[simp] theorem quittingProfileLiveRoot_liftBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingLiftBlockProfile reward B profile) =
      quittingExtendBlockRoots B
        (quittingProfileLiveRoot (quittingDeleteBlockReward reward B)
          profile) := by
  unfold quittingLiftBlockProfile
  exact quittingProfileLiveRoot_infinitePathProfile _ _

/-- Every surviving player's on-path terminal payoff is exactly preserved by
the block profile lift. -/
theorem quittingTerminalPayoff_liftBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    (who : QuittingBlockSurvivor B) :
    quittingTerminalPayoff reward
        (quittingLiftBlockProfile reward B profile) who.1 =
      quittingTerminalPayoff (quittingDeleteBlockReward reward B)
        profile who := by
  unfold quittingLiftBlockProfile
  rw [quittingTerminalPayoff_infinitePathProfile,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  exact quittingRootSequenceTerminalValue_extendBlockRoots reward B
    (quittingProfileLiveRoot (quittingDeleteBlockReward reward B) profile)
      who 0

/-- Read the live-path hazard of an original-game deviation as a behavioral
strategy of the survivor game. -/
def quittingDeleteBlockDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (who : QuittingBlockSurvivor B)
    (deviation : (quittingGame reward).BehaviorStrategy who.1) :
    (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorStrategy who :=
  fun time _ => quittingBehaviorLiveHazard reward deviation time

/-- An arbitrary behavioral deviation by a surviving player has exactly the
same payoff after block deletion. -/
theorem quittingTerminalPayoff_update_liftBlockProfile_eq_deleteDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    (who : QuittingBlockSurvivor B)
    (deviation : (quittingGame reward).BehaviorStrategy who.1) :
    quittingTerminalPayoff reward
        (Function.update (quittingLiftBlockProfile reward B profile)
          who.1 deviation) who.1 =
      quittingTerminalPayoff (quittingDeleteBlockReward reward B)
        (Function.update profile who
          (quittingDeleteBlockDeviation reward B who deviation)) who := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingProfileLiveRoot_liftBlockProfile]
  unfold quittingDeleteBlockDeviation quittingBehaviorLiveHazard
  exact quittingRootSequenceHazardTerminalValue_extendBlockRoots
    reward B
      (quittingProfileLiveRoot (quittingDeleteBlockReward reward B) profile)
      who (fun time => deviation time (quittingLiveHist reward time)) 0

/-! ## The deletion gate of a single deleted player over the survivors -/

/-- Player `owner` weakly loses by joining every nonempty coalition of
survivors of `B`.  This is the block form of `QuittingOwnerJoinAntitone`: it
quantifies only over coalitions disjoint from `B`, so deleting a whole block
at once is a weaker hypothesis than deleting its members one at a time. -/
def QuittingBlockJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : Prop :=
  ∀ (quitters : Finset ι) (hquitters : quitters.Nonempty),
    Disjoint quitters B →
      reward
          ⟨insert owner quitters, Finset.insert_nonempty owner quitters⟩ owner ≤
        reward ⟨quitters, hquitters⟩ owner

/-- A root chronology in which no member of `B` ever quits. -/
def QuittingRootsQuietOn (B : Finset ι) (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ time, ∀ who ∈ B, roots time who = PMF.pure false

/-- A root chronology in which no member of `B` other than `owner` ever
quits.  Every fixed-opponent quantity below overwrites `owner`'s own
coordinate, so leaving it unconstrained costs nothing and makes the singleton
block `{owner}` an unconditional instance. -/
def QuittingRootsBlockQuiet (B : Finset ι) (owner : ι)
    (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ time, ∀ who ∈ B, who ≠ owner → roots time who = PMF.pure false

omit [Fintype ι] [DecidableEq ι] in
theorem QuittingRootsQuietOn.blockQuiet {B : Finset ι}
    {roots : ℕ → ι → PMF Bool} (hquiet : QuittingRootsQuietOn B roots)
    (owner : ι) : QuittingRootsBlockQuiet B owner roots :=
  fun time who hwho _ => hquiet time who hwho

omit [Fintype ι] [DecidableEq ι] in
/-- The singleton block constrains nothing. -/
theorem quittingRootsBlockQuiet_singleton (owner : ι)
    (roots : ℕ → ι → PMF Bool) :
    QuittingRootsBlockQuiet {owner} owner roots := by
  intro _ who hwho hne
  exact absurd (Finset.mem_singleton.mp hwho) hne

omit [Fintype ι] in
theorem quittingRootsQuietOn_extendBlockRoots (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool) :
    QuittingRootsQuietOn B (quittingExtendBlockRoots B roots) :=
  fun _ _ hwho => quittingExtendBlockRoots_of_mem B roots _ hwho

omit [Fintype ι] in
/-- Forcing a quiet root to Continue at one coordinate keeps it quiet. -/
theorem quittingRootsBlockQuiet.update_pure_false {B : Finset ι}
    {root : ι → PMF Bool} {owner : ι}
    (hquiet : ∀ who ∈ B, who ≠ owner → root who = PMF.pure false) :
    ∀ who ∈ B,
      Function.update root owner (PMF.pure false) who = PMF.pure false := by
  intro who hwho
  by_cases hp : who = owner
  · subst who
    simp
  · rw [Function.update_of_ne hp]
    exact hquiet who hwho hp

omit [DecidableEq ι] in
/-- No member of the block quits on the support of a quiet product row. -/
theorem quittingAction_eq_false_of_mem_block {B : Finset ι}
    {root : ι → PMF Bool} (hquiet : ∀ who ∈ B, root who = PMF.pure false)
    {action : ι → Bool} (hsupport : pmfPi root action ≠ 0)
    {who : ι} (hwho : who ∈ B) : action who = false := by
  classical
  by_contra hne
  have htrue : action who = true := by cases h : action who <;> simp_all
  apply hsupport
  rw [pmfPi_apply]
  refine Finset.prod_eq_zero (Finset.mem_univ who) ?_
  rw [hquiet who hwho, htrue]
  simp

omit [DecidableEq ι] in
/-- An action in which no member of the block quits has a quitter set
disjoint from the block. -/
theorem disjoint_quittingQuitters_of_forall_mem_eq_false
    {B : Finset ι} {action : ι → Bool}
    (hfalse : ∀ who ∈ B, action who = false) :
    Disjoint (quittingQuitters action) B := by
  classical
  refine Finset.disjoint_left.mpr fun a ha hb => ?_
  have htrue : action a = true := by
    simpa [quittingQuitters] using ha
  rw [hfalse a hb] at htrue
  exact Bool.noConfusion htrue

/-- Block form of the one-stage owner-insertion sign estimate: the terminal
opponent advantage is nonnegative on every row in which the owner continues
and no member of the block quits. -/
theorem quittingTerminalOpponentAdvantage_nonneg_of_blockJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) (hjoin : QuittingBlockJoinAntitone reward B owner)
    (action : ι → Bool)
    (hdisjoint : Disjoint (quittingQuitters action) B) :
    0 ≤ quittingTerminalOpponentAdvantage reward owner action := by
  classical
  unfold quittingTerminalOpponentAdvantage quittingRootPayoff
  rw [quittingQuitters_update_true_of_apply_false]
  by_cases hquitters : (quittingQuitters action).Nonempty
  · simp only [dif_pos hquitters,
      dif_pos (Finset.insert_nonempty owner (quittingQuitters action))]
    exact sub_nonneg.mpr (hjoin (quittingQuitters action) hquitters hdisjoint)
  · have hempty : quittingQuitters action = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hquitters
    simp [hempty, quittingSingletonTerminal]

/-- Block form of the one-stage quit comparison. -/
theorem quittingFixedOpponentsQuitValue_le_of_blockJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hquiet : QuittingRootsBlockQuiet B owner roots)
    (hjoin : QuittingBlockJoinAntitone reward B owner) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots owner time ≤
      quittingFixedOpponentsContinueReward reward roots owner time +
        quittingFixedOpponentsContinueMass roots owner time *
          reward (quittingSingletonTerminal owner) owner := by
  classical
  let root := roots time
  have hquietUpdate : ∀ who ∈ B,
      Function.update root owner (PMF.pure false) who = PMF.pure false :=
    quittingRootsBlockQuiet.update_pure_false (hquiet time)
  have hexpect :
      0 ≤ expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner) := by
    unfold expect
    apply tsum_nonneg
    intro action
    by_cases hmass :
        (pmfPi (Function.update root owner (PMF.pure false))) action = 0
    · rw [hmass, ENNReal.toReal_zero, zero_mul]
    · have hfalse := fun who (hwho : who ∈ B) =>
        quittingAction_eq_false_of_mem_block hquietUpdate hmass hwho
      exact mul_nonneg ENNReal.toReal_nonneg
        (quittingTerminalOpponentAdvantage_nonneg_of_blockJoinAntitone
          reward B owner hjoin action
          (disjoint_quittingQuitters_of_forall_mem_eq_false hfalse))
  rw [expect_terminalOpponentAdvantage] at hexpect
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots owner (0 : Payoff ι) time
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward roots owner
      (fun _ => reward (quittingSingletonTerminal owner) owner) time
  dsimp only [root] at hexpect
  rw [hquit, hcontinue] at hexpect
  exact sub_nonneg.mp hexpect

/-- **The continue-floor ride inequality.**  Against a quiet chronology every
realized absorbing coalition is a nonempty set of survivors, so the row's
absorbing contribution finances any lower bound on the survivor rewards. -/
theorem mul_continueFloor_le_quittingFixedOpponentsContinueReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (floor : ℝ)
    (hquiet : QuittingRootsBlockQuiet B owner roots)
    (hfloor : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      floor ≤ reward ⟨S, hS⟩ owner)
    (time : ℕ) :
    (1 - quittingFixedOpponentsContinueMass roots owner time) * floor ≤
      quittingFixedOpponentsContinueReward reward roots owner time := by
  classical
  set root := Function.update (roots time) owner (PMF.pure false) with hroot
  have hquietUpdate : ∀ who ∈ B, root who = PMF.pure false :=
    quittingRootsBlockQuiet.update_pure_false (hquiet time)
  have hsplit := quittingRootExpectedPayoff_eq_absorbingContribution_add
    reward (fun _ => floor) root owner
  have hnonneg : 0 ≤ expect (pmfPi root) (fun action =>
      quittingRootPayoff reward (fun _ => floor) action owner - floor) := by
    unfold expect
    apply tsum_nonneg
    intro action
    by_cases hmass : (pmfPi root) action = 0
    · rw [hmass, ENNReal.toReal_zero, zero_mul]
    · refine mul_nonneg ENNReal.toReal_nonneg ?_
      rw [sub_nonneg]
      have hfalse := fun who (hwho : who ∈ B) =>
        quittingAction_eq_false_of_mem_block hquietUpdate hmass hwho
      by_cases hquitters : (quittingQuitters action).Nonempty
      · rw [quittingRootPayoff, dif_pos hquitters]
        exact hfloor _ hquitters
          (disjoint_quittingQuitters_of_forall_mem_eq_false hfalse)
      · rw [quittingRootPayoff, dif_neg hquitters]
  have hrewrite : expect (pmfPi root) (fun action =>
        quittingRootPayoff reward (fun _ => floor) action owner - floor) =
      quittingRootExpectedPayoff reward (fun _ => floor) root owner - floor := by
    rw [expect_sub, expect_const]
    rfl
  rw [hrewrite] at hnonneg
  have hmassEq : quittingStationaryContinueMass root =
      quittingFixedOpponentsContinueMass roots owner time := rfl
  have habsorbEq : quittingRootAbsorbingContribution reward root owner =
      quittingFixedOpponentsContinueReward reward roots owner time := rfl
  rw [hsplit, hmassEq, habsorbEq] at hnonneg
  have hring : (1 - quittingFixedOpponentsContinueMass roots owner time) * floor =
      floor - quittingFixedOpponentsContinueMass roots owner time * floor := by
    ring
  rw [hring]
  linarith

/-- Under a nonpositive continue floor, every suffix `Never` payoff against a
quiet chronology is at least the floor. -/
theorem continueFloor_le_neverTail_of_quiet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (floor : ℝ)
    (hquiet : QuittingRootsBlockQuiet B owner roots)
    (hfloor : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      floor ≤ reward ⟨S, hS⟩ owner)
    (hnonpos : floor ≤ 0) (start : ℕ) :
    floor ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none start := by
  have hledger : ∀ fuel,
      floor ≤ quittingLiveLedgerAccum reward roots owner start fuel := by
    intro fuel
    have haccount := le_quittingLiveLedgerAccum_add_survival_mul_from
      reward roots owner floor start fuel (fun offset _ =>
        mul_continueFloor_le_quittingFixedOpponentsContinueReward
          reward B roots owner floor hquiet hfloor (start + offset))
    have hsurvival0 :=
      quittingOpponentSurvivalWeight_nonneg roots owner start fuel
    have hsurvival1 :=
      quittingOpponentSurvivalWeight_le_one roots owner start fuel
    nlinarith
  exact ge_of_tendsto'
    (tendsto_quittingLiveLedgerAccum_from reward roots owner start) hledger

/-- Every deterministic finite quit date is weakly dominated by `Never`
against a quiet chronology, at the block gate. -/
theorem quittingRootSequencePureTimeTerminalValue_le_never_of_blockGate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (floor : ℝ)
    (hquiet : QuittingRootsBlockQuiet B owner roots)
    (hjoin : QuittingBlockJoinAntitone reward B owner)
    (hfloor : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      floor ≤ reward ⟨S, hS⟩ owner)
    (hnonpos : floor ≤ 0)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ floor)
    (quitTime : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots owner quitTime 0 ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none 0 := by
  cases quitTime with
  | none => exact le_rfl
  | some time =>
      have htail := continueFloor_le_neverTail_of_quiet reward B roots owner
        floor hquiet hfloor hnonpos (time + 1)
      have hquitLocal := quittingFixedOpponentsQuitValue_le_of_blockJoinAntitone
        reward B roots owner hquiet hjoin time
      have hmass0 :=
        quittingFixedOpponentsContinueMass_nonneg roots owner time
      have hlocal : quittingFixedOpponentsQuitValue reward roots owner time ≤
          quittingRootSequencePureTimeTerminalValue reward roots owner none
            time := by
        rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
        have hsoloLe : reward (quittingSingletonTerminal owner) owner ≤
            quittingRootSequencePureTimeTerminalValue reward roots owner none
              (time + 1) := hsolo.trans htail
        nlinarith
      rw [quittingRootSequencePureTimeTerminalValue_some_eq,
        quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_tail
          reward roots owner 0 time]
      have hscaled := mul_le_mul_of_nonneg_left hlocal
        (quittingOpponentSurvivalWeight_nonneg roots owner 0 time)
      simpa [Nat.zero_add, add_comm] using
        (add_le_add_right hscaled
          (quittingLiveLedgerAccum reward roots owner 0 time))

/-- **Block deletion core.**  At the block gate, literal `Never` attains the
full behavioral best-response value of a deleted player against every profile
whose live chronology is quiet on the block. -/
theorem quittingBestReplyValue_eq_never_of_blockGate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) (floor : ℝ)
    (hquiet : QuittingRootsBlockQuiet B owner
      (quittingProfileLiveRoot reward profile))
    (hjoin : QuittingBlockJoinAntitone reward B owner)
    (hfloor : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      floor ≤ reward ⟨S, hS⟩ owner)
    (hnonpos : floor ≤ 0)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ floor) :
    quittingBestReplyValue reward profile owner =
      quittingTerminalPayoff reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner := by
  let neverPayoff := quittingTerminalPayoff reward
    (Function.update profile owner
      (quittingPureTimeBehaviorStrategy reward owner none)) owner
  have hpure : ∀ quitTime : Option ℕ,
      quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner quitTime)) owner ≤
        neverPayoff := by
    intro quitTime
    dsimp only [neverPayoff]
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    exact quittingRootSequencePureTimeTerminalValue_le_never_of_blockGate
      reward B (quittingProfileLiveRoot reward profile) owner floor
      hquiet hjoin hfloor hnonpos hsolo quitTime
  apply le_antisymm
  · apply quittingBestReplyValue_le
    intro deviation
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨quitTime, htime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward profile owner deviation hε
    have hp := hpure quitTime
    linarith
  · exact le_quittingBestReplyValue reward profile owner
      (quittingPureTimeBehaviorStrategy reward owner none)

/-- The lifted profile already has every deleted player playing literal
`Never` on every history. -/
theorem Function.update_liftBlockProfile_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    {owner : ι} (howner : owner ∈ B) :
    Function.update (quittingLiftBlockProfile reward B profile) owner
        (quittingPureTimeBehaviorStrategy reward owner none) =
      quittingLiftBlockProfile reward B profile := by
  funext player time history
  by_cases hp : player = owner
  · subst player
    simp [quittingPureTimeBehaviorStrategy, quittingLiftBlockProfile,
      quittingInfinitePathProfile, quittingRootSequenceProfile,
      quittingExtendBlockRoots, howner]
  · simp [Function.update_of_ne hp]

/-- At the block gate every deleted player has exactly zero behavioral
best-response debt on every lifted survivor profile. -/
theorem quittingBestReplyValue_liftBlockProfile_eq_terminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    (owner : ι) (howner : owner ∈ B) (floor : ℝ)
    (hjoin : QuittingBlockJoinAntitone reward B owner)
    (hfloor : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      floor ≤ reward ⟨S, hS⟩ owner)
    (hnonpos : floor ≤ 0)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤ floor) :
    quittingBestReplyValue reward
        (quittingLiftBlockProfile reward B profile) owner =
      quittingTerminalPayoff reward
        (quittingLiftBlockProfile reward B profile) owner := by
  have hquiet : QuittingRootsBlockQuiet B owner
      (quittingProfileLiveRoot reward
        (quittingLiftBlockProfile reward B profile)) := by
    rw [quittingProfileLiveRoot_liftBlockProfile]
    exact (quittingRootsQuietOn_extendBlockRoots B _).blockQuiet owner
  rw [quittingBestReplyValue_eq_never_of_blockGate reward B
    (quittingLiftBlockProfile reward B profile) owner floor hquiet
      hjoin hfloor hnonpos hsolo]
  rw [Function.update_liftBlockProfile_never reward B profile howner]

/-! ## The dispensability gate as a finite table check -/

/-- The **continue floor** of `owner` over the survivors of `B`: the least of
`0` and the rewards of `owner` at the nonempty coalitions disjoint from
`B`. -/
def quittingBlockContinueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : ℝ :=
  (insert (0 : ℝ)
      ((Finset.univ.filter
        (fun T : {S : Finset ι // S.Nonempty} => Disjoint T.1 B)).image
          (fun T => reward T owner))).min'
    (Finset.insert_nonempty _ _)

theorem quittingBlockContinueFloor_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : quittingBlockContinueFloor reward B owner ≤ 0 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem quittingBlockContinueFloor_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) (S : Finset ι) (hS : S.Nonempty) (hdisjoint : Disjoint S B) :
    quittingBlockContinueFloor reward B owner ≤ reward ⟨S, hS⟩ owner := by
  refine Finset.min'_le _ _ (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_image.mpr
    ⟨⟨S, hS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdisjoint⟩, rfl⟩

/-- The continue floor is the greatest nonpositive lower bound of the
survivor rewards. -/
theorem le_quittingBlockContinueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) {value : ℝ} (hzero : value ≤ 0)
    (hrow : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      value ≤ reward ⟨S, hS⟩ owner) :
    value ≤ quittingBlockContinueFloor reward B owner := by
  classical
  unfold quittingBlockContinueFloor
  refine Finset.le_min' _ _ _ ?_
  intro entry hentry
  rcases Finset.mem_insert.mp hentry with hzeroEntry | hmem
  · exact hzeroEntry ▸ hzero
  · obtain ⟨terminal, hterminal, rfl⟩ := Finset.mem_image.mp hmem
    exact hrow terminal.1 terminal.2 (Finset.mem_filter.mp hterminal).2

omit [Fintype ι] [DecidableEq ι] in
/-- Set rewards of the survivor game are set rewards of the original table at
the corresponding coalition of survivors. -/
theorem quittingSetReward_deleteBlockReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (E : Finset (QuittingBlockSurvivor B)) (who : QuittingBlockSurvivor B) :
    quittingSetReward (quittingDeleteBlockReward reward B) E who =
      quittingSetReward reward
        (E.map (Function.Embedding.subtype (p := fun w : ι => w ∉ B))) who.1 := by
  by_cases hE : E.Nonempty
  · rw [quittingSetReward_of_nonempty _ hE,
      quittingSetReward_of_nonempty _ (Finset.map_nonempty.mpr hE)]
    rfl
  · rw [Finset.not_nonempty_iff_eq_empty.mp hE]
    simp [quittingSetReward]

omit [Fintype ι] in
/-- **Reading survivor sure exit sets off the original table.**  A set of
survivors exits surely in the survivor game exactly when its image passes the
membership toggles of the original table at the survivors. -/
theorem isQuittingSureExitSet_deleteBlockReward_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (E : Finset (QuittingBlockSurvivor B)) :
    IsQuittingSureExitSet (quittingDeleteBlockReward reward B) E ↔
      (∀ member ∈ E.map (Function.Embedding.subtype (p := fun w : ι => w ∉ B)),
          quittingSetReward reward
              ((E.map (Function.Embedding.subtype
                (p := fun w : ι => w ∉ B))).erase member) member ≤
            quittingSetReward reward
              (E.map (Function.Embedding.subtype
                (p := fun w : ι => w ∉ B))) member) ∧
        ∀ outsider ∉ B,
          outsider ∉ E.map (Function.Embedding.subtype
              (p := fun w : ι => w ∉ B)) →
            quittingSetReward reward
                (insert outsider (E.map (Function.Embedding.subtype
                  (p := fun w : ι => w ∉ B)))) outsider ≤
              quittingSetReward reward
                (E.map (Function.Embedding.subtype
                  (p := fun w : ι => w ∉ B))) outsider := by
  classical
  constructor
  · rintro ⟨hmember, houtsider⟩
    refine ⟨fun member hmem => ?_, fun outsider hout hmem => ?_⟩
    · obtain ⟨survivor, hsurvivor, rfl⟩ := Finset.mem_map.mp hmem
      have hstep := hmember survivor hsurvivor
      rw [quittingSetReward_deleteBlockReward,
        quittingSetReward_deleteBlockReward, Finset.map_erase] at hstep
      exact hstep
    · have hsurvivor : (⟨outsider, hout⟩ : QuittingBlockSurvivor B) ∉ E := by
        intro hcontra
        exact hmem (Finset.mem_map_of_mem _ hcontra)
      have hstep := houtsider ⟨outsider, hout⟩ hsurvivor
      rw [quittingSetReward_deleteBlockReward,
        quittingSetReward_deleteBlockReward, Finset.map_insert] at hstep
      exact hstep
  · rintro ⟨hmember, houtsider⟩
    refine ⟨fun survivor hsurvivor => ?_, fun survivor hsurvivor => ?_⟩
    · rw [quittingSetReward_deleteBlockReward,
        quittingSetReward_deleteBlockReward, Finset.map_erase]
      exact hmember survivor.1 (Finset.mem_map_of_mem _ hsurvivor)
    · rw [quittingSetReward_deleteBlockReward,
        quittingSetReward_deleteBlockReward, Finset.map_insert]
      refine houtsider survivor.1 survivor.2 ?_
      intro hcontra
      obtain ⟨other, hother, heq⟩ := Finset.mem_map.mp hcontra
      have hsame : other = survivor := Subtype.ext heq
      exact hsurvivor (hsame ▸ hother)

/-- **The block dispensability gate.**  Player `owner` weakly loses by joining
every coalition of survivors, and its solo reward is at most its continue
floor over the survivors.  Both clauses are finite table checks. -/
def QuittingBlockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : Prop :=
  QuittingBlockJoinAntitone reward B owner ∧
    reward (quittingSingletonTerminal owner) owner ≤
      quittingBlockContinueFloor reward B owner

/-- A player passing the gate has exactly zero behavioral best-response debt
on every lifted survivor profile. -/
theorem quittingBestReplyValue_liftBlockProfile_eq_terminalPayoff_of_dispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    {owner : ι} (howner : owner ∈ B)
    (hgate : QuittingBlockDispensable reward B owner) :
    quittingBestReplyValue reward
        (quittingLiftBlockProfile reward B profile) owner =
      quittingTerminalPayoff reward
        (quittingLiftBlockProfile reward B profile) owner :=
  quittingBestReplyValue_liftBlockProfile_eq_terminalPayoff reward B profile
    owner howner (quittingBlockContinueFloor reward B owner) hgate.1
    (fun S hS hdisjoint =>
      quittingBlockContinueFloor_le reward B owner S hS hdisjoint)
    (quittingBlockContinueFloor_nonpos reward B owner) hgate.2

/-- **Exact exploitability-floor descent under block deletion.**  If every
member of `B` passes the block gate, deleting the whole block preserves a
witnessed positive terminal exploitability gap exactly. -/
theorem hasTerminalExploitabilityGap_deleteBlock_of_dispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d) :
    HasTerminalExploitabilityGap (quittingDeleteBlockReward reward B) gap := by
  intro profile
  obtain ⟨player, deviation, hdeviation⟩ :=
    hexploit (quittingLiftBlockProfile reward B profile)
  by_cases hp : player ∈ B
  · have hbest :=
      quittingBestReplyValue_liftBlockProfile_eq_terminalPayoff_of_dispensable
        reward B profile hp (hgate player hp)
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftBlockProfile reward B profile) player deviation
    linarith
  · refine ⟨⟨player, hp⟩,
      quittingDeleteBlockDeviation reward B ⟨player, hp⟩ deviation, ?_⟩
    have hon := quittingTerminalPayoff_liftBlockProfile
      reward B profile ⟨player, hp⟩
    have hdev :=
      quittingTerminalPayoff_update_liftBlockProfile_eq_deleteDeviation
        reward B profile ⟨player, hp⟩ deviation
    dsimp only at hon hdev
    linarith

/-- **The block deletion producer.**  If every member of `B` passes the block
gate and the survivor game has a uniform-equilibrium payoff, so does the
original game. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    (hsurvivor : ∃ payoff : Payoff (QuittingBlockSurvivor B),
      (quittingGame
        (quittingDeleteBlockReward reward B)).IsUniformEquilibriumPayoff
          none payoff) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).1 hno
  exact
    ((not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
        (quittingDeleteBlockReward reward B)).2
      ⟨gap, hgap,
        hasTerminalExploitabilityGap_deleteBlock_of_dispensable reward B hgap
          hexploit hgate⟩) hsurvivor

/-! ## The producer with the survivors' payoff preserved -/

/-- The lift of a terminal `ε`-equilibrium of the survivor game is a terminal
`ε`-equilibrium of the original game. -/
theorem isεAsymptoticNash_liftBlockProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    {error : ℝ} (herror : 0 ≤ error)
    {profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile}
    (hnash : (quittingGame (quittingDeleteBlockReward reward B)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteBlockReward reward B)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      error (quittingLiftBlockProfile reward B profile) := by
  intro who deviation
  by_cases hp : who ∈ B
  · have hbest :=
      quittingBestReplyValue_liftBlockProfile_eq_terminalPayoff_of_dispensable
        reward B profile hp (hgate who hp)
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftBlockProfile reward B profile) who deviation
    linarith
  · have hon := quittingTerminalPayoff_liftBlockProfile
      reward B profile ⟨who, hp⟩
    have hdev :=
      quittingTerminalPayoff_update_liftBlockProfile_eq_deleteDeviation
        reward B profile ⟨who, hp⟩ deviation
    have hstep := hnash ⟨who, hp⟩
      (quittingDeleteBlockDeviation reward B ⟨who, hp⟩ deviation)
    dsimp only at hon hdev
    linarith

/-- A uniform-equilibrium payoff supplies terminal approximate equilibria
whose own terminal payoffs are close to it. -/
theorem exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (target : Payoff ι)
    (hpayoff : (quittingGame reward).IsUniformEquilibriumPayoff none target)
    {error : ℝ} (herror : 0 < error) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) error profile ∧
        ∀ who, |quittingTerminalPayoff reward profile who - target who| ≤ error := by
  have hhalf : 0 < error / 2 := by linarith
  obtain ⟨profile, threshold, hprofile⟩ := hpayoff (error / 2) hhalf
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none (error / 2) profile :=
    ⟨threshold, fun horizon hhorizon => (hprofile horizon hhorizon).1⟩
  have hterminal : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (error / 2) profile :=
    (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
      none (quittingTerminalPayoff reward) huniform
      (fun selectedProfile who =>
        tendsto_finiteAveragePayoff_quittingGame reward selectedProfile who)
  refine ⟨profile, hterminal.mono (by linarith), fun who => ?_⟩
  have hlimit := tendsto_finiteAveragePayoff_quittingGame reward profile who
  have habs : Tendsto
      (fun horizon => |(quittingGame reward).finiteAveragePayoff none horizon
        profile who - target who|) atTop
      (nhds |quittingTerminalPayoff reward profile who - target who|) :=
    ((hlimit.sub tendsto_const_nhds).abs)
  have hhalfBound :
      |quittingTerminalPayoff reward profile who - target who| ≤ error / 2 := by
    refine le_of_tendsto habs ?_
    exact Filter.eventually_atTop.mpr
      ⟨threshold, fun horizon hhorizon => (hprofile horizon hhorizon).2 who⟩
  linarith

/-- **The block deletion producer, with the survivors' payoff preserved.**
If every member of `B` passes the block gate and `target` is a
uniform-equilibrium payoff of the survivor game, the original game has a
uniform-equilibrium payoff agreeing with `target` at every survivor.

No closed form is claimed for the deleted players' coordinates: they are the
limit of the never-quit payoffs of the lifted approximate equilibria, which
depends on the selected sequence. -/
theorem exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    (target : Payoff (QuittingBlockSurvivor B))
    (htarget : (quittingGame
      (quittingDeleteBlockReward reward B)).IsUniformEquilibriumPayoff
        none target) :
    ∃ payoff : Payoff ι,
      (∀ who : QuittingBlockSurvivor B, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  let error : ℕ → ℝ := fun step => 1 / ((step : ℝ) + 1)
  have herrorPos : ∀ step, 0 < error step := by
    intro step
    dsimp [error]
    positivity
  have hexists : ∀ step, ∃ profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile,
      (quittingGame (quittingDeleteBlockReward reward B)).IsεAsymptoticNash
          (quittingTerminalPayoff (quittingDeleteBlockReward reward B))
          (error step) profile ∧
        ∀ who, |quittingTerminalPayoff (quittingDeleteBlockReward reward B)
          profile who - target who| ≤ error step :=
    fun step =>
      exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff
        (quittingDeleteBlockReward reward B) target htarget (herrorPos step)
  choose profiles hnash hclose using hexists
  let lifted : ℕ → (quittingGame reward).BehaviorProfile :=
    fun step => quittingLiftBlockProfile reward B (profiles step)
  have hmem : ∀ step, quittingTerminalPayoff reward (lifted step) ∈
      Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward) :=
    fun step => quittingTerminalPayoff_mem_rewardCube reward (lifted step)
  obtain ⟨payoff, -, subsequence, hsubsequence, hlimit⟩ :=
    (isCompact_Icc : IsCompact
      (Set.Icc (fun _ : ι => -quittingRewardBound reward)
        (fun _ : ι => quittingRewardBound reward))).tendsto_subseq hmem
  have herrorLimit : Tendsto error atTop (nhds 0) := by
    simpa [error] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsubLimit : Tendsto (error ∘ subsequence) atTop (nhds 0) :=
    herrorLimit.comp hsubsequence.tendsto_atTop
  refine ⟨payoff, fun who => ?_, ?_⟩
  · have hcoord : Tendsto
        (fun step => quittingTerminalPayoff reward (lifted (subsequence step)) who.1)
        atTop (nhds (payoff who.1)) :=
      (tendsto_pi_nhds.mp hlimit) who.1
    have hbound : ∀ step,
        |quittingTerminalPayoff reward (lifted (subsequence step)) who.1 -
          target who| ≤ (error ∘ subsequence) step := by
      intro step
      rw [quittingTerminalPayoff_liftBlockProfile]
      exact hclose (subsequence step) who
    have hzero : |payoff who.1 - target who| ≤ 0 := by
      refine le_of_tendsto_of_tendsto' ((hcoord.sub tendsto_const_nhds).abs)
        hsubLimit hbound
    have := abs_nonpos_iff.mp hzero
    linarith [sub_eq_zero.mp this]
  · refine quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
      (filter := atTop) reward payoff (error ∘ subsequence)
      (fun step => lifted (subsequence step)) hsubLimit ?_ hlimit
    refine Filter.Frequently.of_forall fun step => ?_
    exact isεAsymptoticNash_liftBlockProfile reward B hgate
      (herrorPos (subsequence step)).le (hnash (subsequence step))


end GameTheory
