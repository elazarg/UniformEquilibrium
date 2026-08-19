/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.ContinueFloor
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# The quantitative deletion inequality

`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean` deletes a block of players whose
members are exactly untempted by the lift of a survivor profile.  This module
drops the gate and measures the temptation instead.

Two table constants control a deleted player `d`.  Its **join cap** is the
largest gain `r_d(S ∪ {d}) - r_d(S)` over the nonempty coalitions `S` of
survivors, floored at `0`.  Its **solo premium** is the excess of `r_d({d})`
over the continue floor, again floored at `0`.  Against the lift of a survivor
profile whose per-stage absorption never exceeds `A`, the deleted player's
best-response excess is at most `A` times the join cap plus the solo premium.
Consequently a terminal exploitability gap is charged to one of two sides:
either some deleted player's excess bound covers it, or the survivor profile
is exploitable by it inside the survivor game.  A survivor approximate
equilibrium sharper than the gap closes the second side.

For a singleton block the bound holds at the one deleted player with no
disjunction, which yields a solo-escape versus atomic-temptation dichotomy and
a screen: a table admitting survivor equilibria with vanishing per-stage
absorption and a solo reward at most the continue floor has a
uniform-equilibrium payoff (`quittingGame_exists_uniformEquilibriumPayoff_of_vanishingAbsorption`).

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletionExcessBound.lean`
specializes the dichotomy to a singleton block over at most three or four
survivors, where the survivor game's terminal approximate equilibria are
unconditional.

These are necessary conditions on a counterexample, not a characterization.
Failure to find a lift of the displayed shape proves nothing about the
original game, which may be solved by a profile in which every player quits.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The join cap -/

/-- The largest gain `owner` can make by joining a nonempty coalition of
survivors of `B`, floored at `0`. -/
def quittingBlockJoinCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : ℝ :=
  Math.Finset.insertMax 0 (quittingSurvivorTerminals B)
    (fun T => reward ⟨insert owner T.1, Finset.insert_nonempty owner T.1⟩ owner -
      reward T owner)

theorem quittingBlockJoinCap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : 0 ≤ quittingBlockJoinCap reward B owner := by
  unfold quittingBlockJoinCap
  exact Math.Finset.base_le_insertMax _ _ _

theorem sub_le_quittingBlockJoinCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) (S : Finset ι) (hS : S.Nonempty) (hdisjoint : Disjoint S B) :
    reward ⟨insert owner S, Finset.insert_nonempty owner S⟩ owner -
        reward ⟨S, hS⟩ owner ≤
      quittingBlockJoinCap reward B owner := by
  unfold quittingBlockJoinCap
  refine Math.Finset.le_insertMax (0 : ℝ)
    (fun T => reward ⟨insert owner T.1, Finset.insert_nonempty owner T.1⟩ owner -
      reward T owner) (index := ⟨S, hS⟩) ?_
  exact mem_quittingSurvivorTerminals.mpr hdisjoint

/-- The join cap is the least nonnegative upper bound of the survivor join
margins. -/
theorem quittingBlockJoinCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) {value : ℝ} (hzero : 0 ≤ value)
    (hrow : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      reward ⟨insert owner S, Finset.insert_nonempty owner S⟩ owner -
        reward ⟨S, hS⟩ owner ≤ value) :
    quittingBlockJoinCap reward B owner ≤ value := by
  unfold quittingBlockJoinCap
  exact Math.Finset.insertMax_le hzero fun T hT =>
    hrow T.1 T.2 (mem_quittingSurvivorTerminals.mp hT)

/-- A join-antitone player has join cap zero, so the quantitative bound below
specializes to the exact gate of
`quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff_of_blockGate`. -/
theorem quittingBlockJoinCap_eq_zero_of_blockJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {B : Finset ι}
    {owner : ι} (hjoin : QuittingBlockJoinAntitone reward B owner) :
    quittingBlockJoinCap reward B owner = 0 := by
  refine le_antisymm ?_ (quittingBlockJoinCap_nonneg reward B owner)
  refine quittingBlockJoinCap_le reward B owner le_rfl fun S hS hdisjoint => ?_
  have hstep := hjoin S hS hdisjoint
  linarith

/-! ## Reading off the absorption probability -/

/-- The all-ones reward table.  Its absorbing contribution at a product row is
the row's absorption probability. -/
def quittingUnitReward (ι : Type) [Fintype ι] [DecidableEq ι] :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun _ _ => 1

theorem quittingRootAbsorbingContribution_unitReward
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution (quittingUnitReward ι) root who =
      1 - quittingStationaryContinueMass root := by
  have hsplit := quittingRootExpectedPayoff_eq_absorbingContribution_add
    (quittingUnitReward ι) (fun _ => (1 : ℝ)) root who
  have hone : quittingRootExpectedPayoff (quittingUnitReward ι)
      (fun _ => (1 : ℝ)) root who = 1 := by
    unfold quittingRootExpectedPayoff
    have hconst : (fun action =>
        quittingRootPayoff (quittingUnitReward ι) (fun _ => (1 : ℝ)) action who) =
        fun _ => (1 : ℝ) := by
      funext action
      unfold quittingRootPayoff
      by_cases hquitters : (quittingQuitters action).Nonempty <;>
        simp [hquitters, quittingUnitReward]
    rw [hconst, expect_const]
  rw [hone] at hsplit
  have hsplit' : (1 : ℝ) =
      quittingRootAbsorbingContribution (quittingUnitReward ι) root who +
        quittingStationaryContinueMass root * 1 := hsplit
  linarith

/-! ## The one-stage quit comparison with a join cap -/

/-- **The one-stage estimate.**  Against a chronology quiet on the block, the
value of quitting now exceeds the value of continuing now by at most the
per-stage absorption probability times the join cap. -/
theorem quittingFixedOpponentsQuitValue_le_add_mul_joinCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hquiet : QuittingRootsBlockQuiet B owner roots) (time : ℕ) :
    quittingFixedOpponentsQuitValue reward roots owner time ≤
      quittingFixedOpponentsContinueReward reward roots owner time +
        quittingFixedOpponentsContinueMass roots owner time *
          reward (quittingSingletonTerminal owner) owner +
        (1 - quittingFixedOpponentsContinueMass roots owner time) *
          quittingBlockJoinCap reward B owner := by
  classical
  set root := Function.update (roots time) owner (PMF.pure false) with hroot
  set cap := quittingBlockJoinCap reward B owner with hcap
  have hquietUpdate : ∀ who ∈ B, root who = PMF.pure false :=
    quittingRootsBlockQuiet.update_pure_false (hquiet time)
  have hownerRoot : ∀ who ∈ ({owner} : Finset ι), root who = PMF.pure false := by
    intro who hwho
    rw [Finset.mem_singleton.mp hwho, hroot, Function.update_self]
  have hnonneg : 0 ≤ expect (pmfPi root) (fun action =>
      quittingTerminalOpponentAdvantage reward owner action +
        cap * quittingRootPayoff (quittingUnitReward ι) 0 action owner) := by
    unfold expect
    apply tsum_nonneg
    intro action
    by_cases hmass : (pmfPi root) action = 0
    · rw [hmass, ENNReal.toReal_zero, zero_mul]
    · refine mul_nonneg ENNReal.toReal_nonneg ?_
      have hfalse := fun who (hwho : who ∈ B) =>
        quittingAction_eq_false_of_mem_block hquietUpdate hmass hwho
      have howner : action owner = false :=
        quittingAction_eq_false_of_mem_block hownerRoot hmass
          (Finset.mem_singleton_self owner)
      have hdisjoint := disjoint_quittingQuitters_of_forall_mem_eq_false hfalse
      have hswap := quittingQuitters_update_true_of_apply_false action owner
      simp only [quittingTerminalOpponentAdvantage, quittingRootPayoff, hswap,
        Pi.zero_apply]
      by_cases hquitters : (quittingQuitters action).Nonempty
      · rw [dif_pos hquitters,
          dif_pos (Finset.insert_nonempty owner (quittingQuitters action)),
          dif_pos hquitters]
        have hbound := sub_le_quittingBlockJoinCap reward B owner
          (quittingQuitters action) hquitters hdisjoint
        simp only [quittingUnitReward]
        linarith
      · have hempty : quittingQuitters action = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hquitters
        simp [hempty, quittingSingletonTerminal]
  rw [expect_add, expect_const_mul] at hnonneg
  rw [expect_terminalOpponentAdvantage] at hnonneg
  have hindicator : expect (pmfPi root)
      (fun action => quittingRootPayoff (quittingUnitReward ι) 0 action owner) =
      1 - quittingFixedOpponentsContinueMass roots owner time :=
    quittingRootAbsorbingContribution_unitReward root owner
  rw [hindicator] at hnonneg
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots owner (0 : Payoff ι) time
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward roots owner
      (fun _ => reward (quittingSingletonTerminal owner) owner) time
  rw [hquit, hcontinue] at hnonneg
  linarith

/-! ## The shifted domination -/

/-- The excess bound of a deleted player: the per-stage absorption bound times
the join cap, plus the solo premium over the continue floor. -/
def quittingBlockDeletionExcessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) (absorptionBound : ℝ) : ℝ :=
  absorptionBound * quittingBlockJoinCap reward B owner +
    max 0 (reward (quittingSingletonTerminal owner) owner -
      quittingBlockContinueFloor reward B owner)

theorem quittingBlockDeletionExcessBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) {absorptionBound : ℝ} (habsorb : 0 ≤ absorptionBound) :
    0 ≤ quittingBlockDeletionExcessBound reward B owner absorptionBound := by
  unfold quittingBlockDeletionExcessBound
  have hcap := quittingBlockJoinCap_nonneg reward B owner
  have hmax := le_max_left (0 : ℝ)
    (reward (quittingSingletonTerminal owner) owner -
      quittingBlockContinueFloor reward B owner)
  nlinarith

/-- **The shifted domination.**  Every deterministic quit date is dominated by
`Never` up to the excess bound. -/
theorem quittingRootSequencePureTimeTerminalValue_le_never_add_excessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) {absorptionBound : ℝ}
    (hquiet : QuittingRootsBlockQuiet B owner roots)
    (habsorb : ∀ time,
      1 - quittingFixedOpponentsContinueMass roots owner time ≤ absorptionBound)
    (quitTime : Option ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots owner quitTime 0 ≤
      quittingRootSequencePureTimeTerminalValue reward roots owner none 0 +
        quittingBlockDeletionExcessBound reward B owner absorptionBound := by
  have hcap := quittingBlockJoinCap_nonneg reward B owner
  have hboundNonneg :
      0 ≤ quittingBlockDeletionExcessBound reward B owner absorptionBound := by
    refine quittingBlockDeletionExcessBound_nonneg reward B owner ?_
    have := quittingFixedOpponentsContinueMass_le_one roots owner 0
    have := habsorb 0
    linarith
  cases quitTime with
  | none => linarith
  | some time =>
      have hfloorTail := continueFloor_le_neverTail_of_quiet reward B roots owner
        (quittingBlockContinueFloor reward B owner) hquiet
        (fun S hS hdisjoint =>
          quittingBlockContinueFloor_le reward B owner S hS hdisjoint)
        (quittingBlockContinueFloor_nonpos reward B owner) (time + 1)
      have hquitLocal := quittingFixedOpponentsQuitValue_le_add_mul_joinCap
        reward B roots owner hquiet time
      have hmass0 := quittingFixedOpponentsContinueMass_nonneg roots owner time
      have hmass1 := quittingFixedOpponentsContinueMass_le_one roots owner time
      have hstep1 :
          (1 - quittingFixedOpponentsContinueMass roots owner time) *
              quittingBlockJoinCap reward B owner ≤
            absorptionBound * quittingBlockJoinCap reward B owner :=
        mul_le_mul_of_nonneg_right (habsorb time) hcap
      have hmax0 := le_max_left (0 : ℝ)
        (reward (quittingSingletonTerminal owner) owner -
          quittingBlockContinueFloor reward B owner)
      have hmax1 := le_max_right (0 : ℝ)
        (reward (quittingSingletonTerminal owner) owner -
          quittingBlockContinueFloor reward B owner)
      have hstep2 :
          quittingFixedOpponentsContinueMass roots owner time *
              (reward (quittingSingletonTerminal owner) owner -
                quittingRootSequencePureTimeTerminalValue reward roots owner none
                  (time + 1)) ≤
            max 0 (reward (quittingSingletonTerminal owner) owner -
              quittingBlockContinueFloor reward B owner) := by
        rcases le_total (reward (quittingSingletonTerminal owner) owner -
            quittingBlockContinueFloor reward B owner) 0 with hsign | hsign
        · nlinarith
        · nlinarith
      have hlocal : quittingFixedOpponentsQuitValue reward roots owner time ≤
          quittingRootSequencePureTimeTerminalValue reward roots owner none time +
            quittingBlockDeletionExcessBound reward B owner absorptionBound := by
        rw [quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents]
        unfold quittingBlockDeletionExcessBound
        nlinarith
      rw [quittingRootSequencePureTimeTerminalValue_some_eq,
        quittingRootSequencePureTimeTerminalValue_none_eq_ledger_add_tail
          reward roots owner 0 time, Nat.zero_add]
      have hsurv0 := quittingOpponentSurvivalWeight_nonneg roots owner 0 time
      have hsurv1 := quittingOpponentSurvivalWeight_le_one roots owner 0 time
      nlinarith

/-- **The best-response excess bound.**  Against a chronology quiet on the
block whose per-stage absorption never exceeds `absorptionBound`, a deleted
player's full behavioral best-response value exceeds its never-quit payoff by
at most the excess bound. -/
theorem quittingBestReplyValue_le_never_add_excessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι)
    {absorptionBound : ℝ}
    (hquiet : QuittingRootsBlockQuiet B owner
      (quittingProfileLiveRoot reward profile))
    (habsorb : ∀ time, 1 - quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward profile) owner time ≤ absorptionBound) :
    quittingBestReplyValue reward profile owner ≤
      quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner none)) owner +
        quittingBlockDeletionExcessBound reward B owner absorptionBound := by
  apply quittingBestReplyValue_le
  intro deviation
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨quitTime, htime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile owner deviation hε
  have hpure := quittingRootSequencePureTimeTerminalValue_le_never_add_excessBound
    reward B (quittingProfileLiveRoot reward profile) owner hquiet habsorb quitTime
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at htime
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  linarith

/-! ## Transporting the absorption bound through the lift -/

theorem quittingStationaryContinueMass_extendDeletedRoot (B : Finset ι)
    (root : QuittingBlockSurvivor B → PMF Bool) :
    quittingStationaryContinueMass (quittingExtendDeletedRoot (· ∈ B) root) =
      quittingStationaryContinueMass root := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    ← Fintype.prod_subtype_mul_prod_subtype (fun who : ι => who ∈ B)
      (fun who => (quittingExtendDeletedRoot (· ∈ B) root who false).toReal),
    Finset.prod_eq_one (fun who _ => by simp [who.2]), one_mul]
  exact Finset.prod_congr rfl fun who _ => by simp

theorem quittingFixedOpponentsContinueMass_extendDeletedRoots_of_mem
    (B : Finset ι) (roots : ℕ → QuittingBlockSurvivor B → PMF Bool)
    {owner : ι} (howner : owner ∈ B) (time : ℕ) :
    quittingFixedOpponentsContinueMass
        (quittingExtendDeletedRoots (· ∈ B) roots) owner time =
      quittingStationaryContinueMass (roots time) := by
  have hupdate : Function.update (quittingExtendDeletedRoots (· ∈ B) roots time) owner
      (PMF.pure false) = quittingExtendDeletedRoots (· ∈ B) roots time := by
    funext who
    by_cases hp : who = owner
    · subst who
      simp [howner]
    · rw [Function.update_of_ne hp]
  unfold quittingFixedOpponentsContinueMass
  rw [hupdate]
  exact quittingStationaryContinueMass_extendDeletedRoot B (roots time)

/-- The excess bound applies to every deleted player against the lift of a
survivor profile whose per-stage absorption never exceeds
`absorptionBound`. -/
theorem quittingBestReplyValue_liftDeletedProfile_le_add_excessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    {owner : ι} (howner : owner ∈ B) {absorptionBound : ℝ}
    (habsorb : ∀ time, 1 - quittingStationaryContinueMass
      (quittingProfileLiveRoot (quittingDeleteBlockReward reward B)
        profile time) ≤ absorptionBound) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile) owner ≤
      quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward (· ∈ B) profile) owner +
        quittingBlockDeletionExcessBound reward B owner absorptionBound := by
  have hroot := quittingProfileLiveRoot_liftDeletedProfile reward (· ∈ B) profile
  have hquiet : QuittingRootsBlockQuiet B owner
      (quittingProfileLiveRoot reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile)) := by
    rw [hroot]
    exact (quittingRootsQuietOn_extendDeletedRoots B _).blockQuiet owner
  have hmass : ∀ time, 1 - quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward
        (quittingLiftDeletedProfile reward (· ∈ B) profile)) owner time ≤
      absorptionBound := by
    intro time
    rw [hroot, quittingFixedOpponentsContinueMass_extendDeletedRoots_of_mem
      B _ howner time]
    exact habsorb time
  have hstep := quittingBestReplyValue_le_never_add_excessBound reward B
    (quittingLiftDeletedProfile reward (· ∈ B) profile) owner hquiet hmass
  rwa [Function.update_liftDeletedProfile_never reward (· ∈ B) profile howner] at hstep

/-! ## The deletion inequality -/

/-- **The deletion alternative.**  A terminal exploitability gap of the
original game is charged to exactly one of two sides against any survivor
profile whose per-stage absorption never exceeds `absorptionBound`: either
some deleted player's excess bound already covers the gap, or the survivor
profile is itself exploitable by the gap inside the survivor game.  Nothing is
asked of the survivor profile beyond its absorption bound. -/
theorem exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    {gap absorptionBound : ℝ}
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    (habsorb : ∀ time, 1 - quittingStationaryContinueMass
      (quittingProfileLiveRoot (quittingDeleteBlockReward reward B)
        profile time) ≤ absorptionBound) :
    (∃ owner ∈ B,
        gap ≤ quittingBlockDeletionExcessBound reward B owner absorptionBound) ∨
      ∃ (survivor : QuittingBlockSurvivor B)
        (deviation : (quittingGame
          (quittingDeleteBlockReward reward B)).BehaviorStrategy survivor),
        quittingTerminalPayoff (quittingDeleteBlockReward reward B) profile
            survivor + gap ≤
          quittingTerminalPayoff (quittingDeleteBlockReward reward B)
            (Function.update profile survivor deviation) survivor := by
  obtain ⟨player, deviation, hdeviation⟩ :=
    hexploit (quittingLiftDeletedProfile reward (· ∈ B) profile)
  by_cases hp : player ∈ B
  · refine Or.inl ⟨player, hp, ?_⟩
    have hbest := quittingBestReplyValue_liftDeletedProfile_le_add_excessBound
      reward B profile hp habsorb
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftDeletedProfile reward (· ∈ B) profile) player deviation
    linarith
  · refine Or.inr ⟨⟨player, hp⟩,
      quittingDeletedDeviation reward (· ∈ B) ⟨player, hp⟩ deviation, ?_⟩
    have hon := quittingTerminalPayoff_liftDeletedProfile
      reward (· ∈ B) profile ⟨player, hp⟩
    have hdev :=
      quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
        reward (· ∈ B) profile ⟨player, hp⟩ deviation
    dsimp only at hon hdev
    linarith

/-- **The quantitative deletion inequality.**  If the original game has a
terminal exploitability gap and the survivor game has a terminal
`error`-equilibrium with `error < gap` whose per-stage absorption never
exceeds `absorptionBound`, then some deleted player's excess bound is at least
the gap: the survivor disjunct of
`exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap` is killed by the
equilibrium hypothesis. -/
theorem exists_mem_gap_le_blockDeletionExcessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    {gap error absorptionBound : ℝ}
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    (hnash : (quittingGame (quittingDeleteBlockReward reward B)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteBlockReward reward B)) error profile)
    (herror : error < gap)
    (habsorb : ∀ time, 1 - quittingStationaryContinueMass
      (quittingProfileLiveRoot (quittingDeleteBlockReward reward B)
        profile time) ≤ absorptionBound) :
    ∃ owner ∈ B,
      gap ≤ quittingBlockDeletionExcessBound reward B owner absorptionBound := by
  rcases exists_mem_gap_le_blockDeletionExcessBound_or_survivorGap reward B
    hexploit profile habsorb with hmain | ⟨survivor, deviation, hgain⟩
  · exact hmain
  · exact absurd (hnash survivor deviation) (by push Not; linarith)

/-! ## Deleting a single player over at most three survivors -/

theorem card_quittingBlockSurvivor_singleton (owner : ι) :
    Fintype.card (QuittingBlockSurvivor ({owner} : Finset ι)) =
      Fintype.card ι - 1 := by
  rw [show Fintype.card (QuittingBlockSurvivor ({owner} : Finset ι)) =
      Fintype.card {x : ι // ¬ x ∈ ({owner} : Finset ι)} from rfl,
    Fintype.card_subtype_compl]
  simp

/-- Deleting one player from at most `n + 1` players leaves at most `n`
survivors. -/
theorem card_quittingBlockSurvivor_singleton_le {n : ℕ}
    (hcard : Fintype.card ι ≤ n + 1) (owner : ι) :
    Fintype.card (QuittingBlockSurvivor ({owner} : Finset ι)) ≤ n := by
  rw [card_quittingBlockSurvivor_singleton]
  omega

/-- **The single-deleted-player inequality.**  With one deleted player the
deletion inequality carries no disjunction: that player alone must account for
the whole gap against every survivor approximate equilibrium sharper than the
gap. -/
theorem gap_le_singletonDeletionExcessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap error absorptionBound : ℝ}
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile)
    (hnash : (quittingGame
        (quittingDeleteBlockReward reward ({owner} : Finset ι))).IsεAsymptoticNash
      (quittingTerminalPayoff
        (quittingDeleteBlockReward reward ({owner} : Finset ι))) error profile)
    (herror : error < gap)
    (habsorb : ∀ time, 1 - quittingStationaryContinueMass
      (quittingProfileLiveRoot
        (quittingDeleteBlockReward reward ({owner} : Finset ι))
        profile time) ≤ absorptionBound) :
    gap ≤ quittingBlockDeletionExcessBound reward {owner} owner
      absorptionBound := by
  obtain ⟨deleted, hdeleted, hbound⟩ := exists_mem_gap_le_blockDeletionExcessBound
    reward {owner} hexploit profile hnash herror habsorb
  rwa [Finset.mem_singleton.mp hdeleted] at hbound

/-- **The dispensability dichotomy.**  At a positive gap the deleted player
either escapes on its own — its solo reward beats its continue floor by half
the gap — or its temptation is atomic: the survivor equilibrium keeps enough
per-stage absorption mass to finance half the gap through a strictly
profitable join, which in particular forces a positive join cap. -/
theorem singletonDeletion_soloEscape_or_atomicTemptation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap error absorptionBound : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile)
    (hnash : (quittingGame
        (quittingDeleteBlockReward reward ({owner} : Finset ι))).IsεAsymptoticNash
      (quittingTerminalPayoff
        (quittingDeleteBlockReward reward ({owner} : Finset ι))) error profile)
    (herror : error < gap)
    (habsorb : ∀ time, 1 - quittingStationaryContinueMass
      (quittingProfileLiveRoot
        (quittingDeleteBlockReward reward ({owner} : Finset ι))
        profile time) ≤ absorptionBound) :
    gap / 2 ≤ reward (quittingSingletonTerminal owner) owner -
        quittingBlockContinueFloor reward {owner} owner ∨
      (0 < quittingBlockJoinCap reward {owner} owner ∧
        gap / 2 ≤
          absorptionBound * quittingBlockJoinCap reward {owner} owner) := by
  have hmain := gap_le_singletonDeletionExcessBound reward owner hexploit
    profile hnash herror habsorb
  unfold quittingBlockDeletionExcessBound at hmain
  have hcap := quittingBlockJoinCap_nonneg reward {owner} owner
  by_cases hpremium : gap / 2 ≤
      max 0 (reward (quittingSingletonTerminal owner) owner -
        quittingBlockContinueFloor reward {owner} owner)
  · left
    rcases max_choice (0 : ℝ)
      (reward (quittingSingletonTerminal owner) owner -
        quittingBlockContinueFloor reward {owner} owner) with hchoice | hchoice
    · rw [hchoice] at hpremium
      linarith
    · rwa [hchoice] at hpremium
  · right
    push Not at hpremium
    have hproduct : gap / 2 ≤
        absorptionBound * quittingBlockJoinCap reward {owner} owner := by
      linarith
    refine ⟨?_, hproduct⟩
    rcases hcap.lt_or_eq with hpos | hzero
    · exact hpos
    · rw [← hzero, mul_zero] at hproduct
      linarith

/-- The atomic branch in the divided form of the dichotomy. -/
theorem le_absorptionBound_of_atomicTemptation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap absorptionBound : ℝ}
    (hcap : 0 < quittingBlockJoinCap reward {owner} owner)
    (hatomic : gap / 2 ≤
      absorptionBound * quittingBlockJoinCap reward {owner} owner) :
    gap / (2 * quittingBlockJoinCap reward {owner} owner) ≤ absorptionBound := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-! ## The vanishing-absorption screen -/

/-- **The vanishing-absorption rate.**  Every positive absorption level `delta`
below the gap that the survivor game realizes with matching accuracy carries
the whole deletion inequality: the gap is at most `delta` times the join cap
plus the solo premium over the continue floor.  The rate is uniform in `delta`,
and `continueFloor_add_gap_le_solo_of_vanishingAbsorption` is its limit. -/
theorem gap_le_singletonDeletionExcessBound_of_vanishingAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hvanishing : ∀ delta : ℝ, 0 < delta →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile,
        (quittingGame
            (quittingDeleteBlockReward reward
              ({owner} : Finset ι))).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteBlockReward reward ({owner} : Finset ι)))
          delta profile ∧
        ∀ time, 1 - quittingStationaryContinueMass
          (quittingProfileLiveRoot
            (quittingDeleteBlockReward reward ({owner} : Finset ι))
            profile time) ≤ delta)
    {delta : ℝ} (hdelta : 0 < delta) (hlt : delta < gap) :
    gap ≤ quittingBlockDeletionExcessBound reward {owner} owner delta := by
  obtain ⟨profile, hnash, habsorb⟩ := hvanishing delta hdelta
  exact gap_le_singletonDeletionExcessBound reward owner hexploit profile hnash
    hlt habsorb

/-- **The vanishing-absorption necessary condition.**  If the survivor game
has terminal approximate equilibria of arbitrarily small accuracy whose
per-stage absorption is arbitrarily small, the join term of the deletion
inequality drops out and the deleted player must clear its continue floor by
the whole gap.  This is the `delta → 0` limit of
`gap_le_singletonDeletionExcessBound_of_vanishingAbsorption`, which keeps the
rate. -/
theorem continueFloor_add_gap_le_solo_of_vanishingAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap)
    (hvanishing : ∀ delta : ℝ, 0 < delta →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile,
        (quittingGame
            (quittingDeleteBlockReward reward
              ({owner} : Finset ι))).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteBlockReward reward ({owner} : Finset ι)))
          delta profile ∧
        ∀ time, 1 - quittingStationaryContinueMass
          (quittingProfileLiveRoot
            (quittingDeleteBlockReward reward ({owner} : Finset ι))
            profile time) ≤ delta) :
    quittingBlockContinueFloor reward {owner} owner + gap ≤
      reward (quittingSingletonTerminal owner) owner := by
  by_contra hcontra
  push Not at hcontra
  set cap := quittingBlockJoinCap reward {owner} owner with hcapDef
  set premium := max 0 (reward (quittingSingletonTerminal owner) owner -
    quittingBlockContinueFloor reward {owner} owner) with hpremiumDef
  have hcap : 0 ≤ cap := quittingBlockJoinCap_nonneg reward {owner} owner
  have hpremiumLt : premium < gap := max_lt hgap (by linarith)
  have hrate : ∀ delta : ℝ, 0 < delta → delta < gap →
      gap ≤ delta * cap + premium := by
    intro delta hdelta hlt
    have hstep := gap_le_singletonDeletionExcessBound_of_vanishingAbsorption
      reward owner hexploit hvanishing hdelta hlt
    unfold quittingBlockDeletionExcessBound at hstep
    rw [← hcapDef, ← hpremiumDef] at hstep
    exact hstep
  have hlimit : gap ≤ premium := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hposc : (0 : ℝ) < cap + 1 := by linarith
    have hdelta : 0 < min (gap / 2) (η / (cap + 1)) :=
      lt_min (by linarith) (div_pos hη hposc)
    have hlt : min (gap / 2) (η / (cap + 1)) < gap :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hstep := hrate _ hdelta hlt
    have hshrink : min (gap / 2) (η / (cap + 1)) * cap ≤ η / (cap + 1) * cap :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hcap
    have hsplit : η / (cap + 1) * cap + η / (cap + 1) = η := by
      field_simp
    linarith [div_nonneg hη.le hposc.le]
  linarith

/-- **The screen.**  A finite quitting game whose survivor game after deleting
one player admits terminal approximate equilibria with vanishing per-stage
absorption, and whose deleted player's solo reward is at most its continue
floor, has a uniform-equilibrium payoff.  No join hypothesis is used. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_vanishingAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hvanishing : ∀ delta : ℝ, 0 < delta →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile,
        (quittingGame
            (quittingDeleteBlockReward reward
              ({owner} : Finset ι))).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteBlockReward reward ({owner} : Finset ι)))
          delta profile ∧
        ∀ time, 1 - quittingStationaryContinueMass
          (quittingProfileLiveRoot
            (quittingDeleteBlockReward reward ({owner} : Finset ι))
            profile time) ≤ delta)
    (hsolo : reward (quittingSingletonTerminal owner) owner ≤
      quittingBlockContinueFloor reward {owner} owner) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).1 hno
  have hstep := continueFloor_add_gap_le_solo_of_vanishingAbsorption reward owner
    hgap hexploit hvanishing
  linarith

end GameTheory
