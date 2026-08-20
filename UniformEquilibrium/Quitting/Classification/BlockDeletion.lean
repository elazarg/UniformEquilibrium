/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Exceptional.InfiniteLTG
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Classification.SymmetricQuittingGame
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Stationary.CoalitionToggleDeletion
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import MathUE.Finset.InsertExtremum

/-!
# Deleting a whole block of universal Never players

Restricting a quitting table to the complement of a `Finset` `B` of players is
the deletion predicate `fun who => who ∈ B` of
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`, so the
whole lift-and-transport naturality is inherited: a behavioral profile of the
survivor game lifts to the original game by making every deleted player
Continue surely, and every surviving player's on-path payoff, arbitrary
behavioral deviation payoff and best-response value are exactly preserved.
What this module adds is the deletion gate and the producers it powers.

`QuittingBlockDispensable` is the deletion gate, a pair of finite table checks:
the block form of `QuittingOwnerJoinAntitone` over the survivors, and a solo
reward at most the survivor continue floor.  When every member of the block
passes it, `hasTerminalExploitabilityGap_deleteBlock_of_dispensable` carries a
witnessed terminal exploitability gap to the survivor table with no loss, and
`exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable` carries a
uniform-equilibrium payoff back, unchanged at every survivor.  Deleting a whole
block at once is a weaker demand than deleting its members one at a time,
because the gate quantifies only over coalitions of survivors.

Because the survivors' coordinates are preserved exactly, any solver for the
survivor table transports its displayed answer to the original game.  The
instance supplied here is
`exists_uniformEquilibriumPayoff_eq_setReward_of_blockDispensable_cardinalSymmetric`,
which solves cardinally symmetric survivors at any survivor count and reads the
resulting coordinates off the original table as the exit reward of one
coalition of survivors.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The players that survive deletion of the block `B`. -/
abbrev QuittingBlockSurvivor {ι : Type} (B : Finset ι) := {who : ι // who ∉ B}

/-- Deleting a block removes exactly its members from the player count. -/
@[simp] theorem card_quittingBlockSurvivor (B : Finset ι) :
    Fintype.card (QuittingBlockSurvivor B) = Fintype.card ι - B.card := by
  rw [show Fintype.card (QuittingBlockSurvivor B) =
    Fintype.card {who : ι // ¬ who ∈ B} from rfl, Fintype.card_subtype_compl]
  simp

/-- Restriction of a quitting reward table to the players outside `B`. -/
abbrev quittingDeleteBlockReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι) :
    {S : Finset (QuittingBlockSurvivor B) // S.Nonempty} →
      Payoff (QuittingBlockSurvivor B) :=
  quittingDeleteReward reward (· ∈ B)

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
theorem quittingRootsQuietOn_extendDeletedRoots (B : Finset ι)
    (roots : ℕ → QuittingBlockSurvivor B → PMF Bool) :
    QuittingRootsQuietOn B (quittingExtendDeletedRoots (· ∈ B) roots) :=
  fun _ _ hwho => quittingExtendDeletedRoots_of_deleted (· ∈ B) roots _ hwho

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

/-- At the block gate every deleted player has exactly zero behavioral
best-response debt on every lifted survivor profile. -/
theorem quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff_of_blockGate
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
        (quittingLiftDeletedProfile reward (· ∈ B) profile) owner =
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile) owner := by
  have hquiet : QuittingRootsBlockQuiet B owner
      (quittingProfileLiveRoot reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile)) := by
    rw [quittingProfileLiveRoot_liftDeletedProfile]
    exact (quittingRootsQuietOn_extendDeletedRoots B _).blockQuiet owner
  rw [quittingBestReplyValue_eq_never_of_blockGate reward B
    (quittingLiftDeletedProfile reward (· ∈ B) profile) owner floor hquiet
      hjoin hfloor hnonpos hsolo]
  rw [Function.update_liftDeletedProfile_never reward (· ∈ B) profile howner]

/-! ## The dispensability gate as a finite table check -/

/-- The nonempty coalitions of survivors of `B`, as a finite index set of
reward rows. -/
def quittingSurvivorTerminals (B : Finset ι) :
    Finset {S : Finset ι // S.Nonempty} :=
  Finset.univ.filter (fun T : {S : Finset ι // S.Nonempty} => Disjoint T.1 B)

theorem mem_quittingSurvivorTerminals {B : Finset ι}
    {T : {S : Finset ι // S.Nonempty}} :
    T ∈ quittingSurvivorTerminals B ↔ Disjoint T.1 B := by
  simp [quittingSurvivorTerminals]

/-- The **continue floor** of `owner` over the survivors of `B`: the least of
`0` and the rewards of `owner` at the nonempty coalitions disjoint from
`B`. -/
def quittingBlockContinueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : ℝ :=
  Math.Finset.insertMin 0 (quittingSurvivorTerminals B) (fun T => reward T owner)

theorem quittingBlockContinueFloor_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : quittingBlockContinueFloor reward B owner ≤ 0 :=
  Math.Finset.insertMin_le_base _ _ _

theorem quittingBlockContinueFloor_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) (S : Finset ι) (hS : S.Nonempty) (hdisjoint : Disjoint S B) :
    quittingBlockContinueFloor reward B owner ≤ reward ⟨S, hS⟩ owner :=
  Math.Finset.insertMin_le _ _ (mem_quittingSurvivorTerminals.mpr hdisjoint)

/-- The continue floor is the greatest nonpositive lower bound of the
survivor rewards. -/
theorem le_quittingBlockContinueFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) {value : ℝ} (hzero : value ≤ 0)
    (hrow : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      value ≤ reward ⟨S, hS⟩ owner) :
    value ≤ quittingBlockContinueFloor reward B owner :=
  Math.Finset.le_insertMin hzero fun T hT =>
    hrow T.1 T.2 (mem_quittingSurvivorTerminals.mp hT)

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

omit [Fintype ι] [DecidableEq ι] in
/-- The survivor game's solo rows are the original table's solo rows. -/
@[simp] theorem quittingDeleteBlockReward_singletonTerminal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (quitter who : QuittingBlockSurvivor B) :
    quittingDeleteBlockReward reward B (quittingSingletonTerminal quitter) who =
      reward (quittingSingletonTerminal quitter.1) who.1 := by
  refine congrArg (fun T => reward T who.1) (Subtype.ext ?_)
  simp [quittingExtendDeletedCoalition, quittingSingletonTerminal]

omit [Fintype ι] in
/-- The survivor game's two-player collision rows are the original table's
collision rows at the corresponding pair. -/
@[simp] theorem quittingDeleteBlockReward_pair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (first second who : QuittingBlockSurvivor B) :
    quittingDeleteBlockReward reward B
        ⟨{first, second}, Finset.insert_nonempty first {second}⟩ who =
      reward ⟨{first.1, second.1}, Finset.insert_nonempty first.1 {second.1}⟩ who.1 := by
  refine congrArg (fun T => reward T who.1) (Subtype.ext ?_)
  simp [quittingExtendDeletedCoalition]

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
theorem quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff_of_blockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    {owner : ι} (howner : owner ∈ B)
    (hgate : QuittingBlockDispensable reward B owner) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile) owner =
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile) owner :=
  quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff_of_blockGate reward B profile
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
    hexploit (quittingLiftDeletedProfile reward (· ∈ B) profile)
  by_cases hp : player ∈ B
  · have hbest :=
      quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff_of_blockDispensable
        reward B profile hp (hgate player hp)
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftDeletedProfile reward (· ∈ B) profile) player deviation
    linarith
  · refine ⟨⟨player, hp⟩,
      quittingDeletedDeviation reward (· ∈ B) ⟨player, hp⟩ deviation, ?_⟩
    have hon := quittingTerminalPayoff_liftDeletedProfile
      reward (· ∈ B) profile ⟨player, hp⟩
    have hdev :=
      quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
        reward (· ∈ B) profile ⟨player, hp⟩ deviation
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
theorem isεAsymptoticNash_liftDeletedProfile_of_blockDispensable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    {error : ℝ} (herror : 0 ≤ error)
    {profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile}
    (hnash : (quittingGame (quittingDeleteBlockReward reward B)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteBlockReward reward B)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      error (quittingLiftDeletedProfile reward (· ∈ B) profile) := by
  intro who deviation
  by_cases hp : who ∈ B
  · have hbest :=
      quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff_of_blockDispensable
        reward B profile hp (hgate who hp)
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftDeletedProfile reward (· ∈ B) profile) who deviation
    linarith
  · have hon := quittingTerminalPayoff_liftDeletedProfile
      reward (· ∈ B) profile ⟨who, hp⟩
    have hdev :=
      quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
        reward (· ∈ B) profile ⟨who, hp⟩ deviation
    have hstep := hnash ⟨who, hp⟩
      (quittingDeletedDeviation reward (· ∈ B) ⟨who, hp⟩ deviation)
    dsimp only at hon hdev
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
    fun step => quittingLiftDeletedProfile reward (· ∈ B) (profiles step)
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
      rw [quittingTerminalPayoff_liftDeletedProfile]
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
    exact isεAsymptoticNash_liftDeletedProfile_of_blockDispensable reward B hgate
      (herrorPos (subsequence step)).le (hnash (subsequence step))

/-! ## Cardinally symmetric survivors -/

/-- **Deleting a block onto cardinally symmetric survivors.**  If every member
of `B` passes the block gate and the survivor table depends only on the size of
the quitting coalition and on membership in it, then the original game has a
uniform-equilibrium payoff whose value at every survivor is the exit reward of
one fixed coalition of survivors, read off the original table.

No bound on the number of survivors is imposed: the survivor game is solved by
`exists_isQuittingSureExitSet_of_cardinalSymmetric`, whose enlargement argument
runs at any finite player count. -/
theorem exists_uniformEquilibriumPayoff_eq_setReward_of_blockDispensable_cardinalSymmetric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hgate : ∀ d ∈ B, QuittingBlockDispensable reward B d)
    (hsymmetric :
      IsQuittingCardinalSymmetric (quittingDeleteBlockReward reward B)) :
    ∃ (exitSet : Finset ι) (payoff : Payoff ι),
      Disjoint exitSet B ∧
        (∀ who ∉ B, payoff who = quittingSetReward reward exitSet who) ∧
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  classical
  obtain ⟨survivorExit, hexit⟩ := exists_isQuittingSureExitSet_of_cardinalSymmetric
    (quittingDeleteBlockReward reward B) hsymmetric
  obtain ⟨payoff, hvalue, huniform⟩ :=
    exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable reward B
      hgate (quittingSetReward (quittingDeleteBlockReward reward B) survivorExit)
      (isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
        (quittingDeleteBlockReward reward B) hexit)
  refine ⟨survivorExit.map
      (Function.Embedding.subtype (p := fun who : ι => who ∉ B)),
    payoff, Finset.disjoint_left.mpr ?_, fun who hwho => ?_, huniform⟩
  · intro member hmember
    obtain ⟨survivor, -, rfl⟩ := Finset.mem_map.mp hmember
    exact survivor.2
  · rw [hvalue ⟨who, hwho⟩, quittingSetReward_deleteBlockReward]

end GameTheory
