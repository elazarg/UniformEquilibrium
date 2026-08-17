/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSmallSurvivorDeletion
import UniformEquilibrium.Quitting.Punishment.ContinueFloor

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
Consequently a terminal exploitability gap is at most that bound at some
deleted player.

For a singleton block over at most three survivors the bound holds at the one
deleted player with no disjunction, which yields a solo-escape versus
atomic-temptation dichotomy and a screen: a table admitting survivor
equilibria with vanishing per-stage absorption and a solo reward at most the
continue floor has a uniform-equilibrium payoff.

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
  (insert (0 : ℝ)
      ((Finset.univ.filter
        (fun T : {S : Finset ι // S.Nonempty} => Disjoint T.1 B)).image
          (fun T =>
            reward ⟨insert owner T.1, Finset.insert_nonempty owner T.1⟩ owner -
              reward T owner))).max'
    (Finset.insert_nonempty _ _)

theorem quittingBlockJoinCap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) : 0 ≤ quittingBlockJoinCap reward B owner :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem sub_le_quittingBlockJoinCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) (S : Finset ι) (hS : S.Nonempty) (hdisjoint : Disjoint S B) :
    reward ⟨insert owner S, Finset.insert_nonempty owner S⟩ owner -
        reward ⟨S, hS⟩ owner ≤
      quittingBlockJoinCap reward B owner := by
  refine Finset.le_max' _ _ (Finset.mem_insert_of_mem ?_)
  exact Finset.mem_image.mpr
    ⟨⟨S, hS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdisjoint⟩, rfl⟩

/-- A join-antitone player has join cap zero, so the quantitative bound below
specializes to the exact gate of
`quittingBestReplyValue_liftBlockProfile_eq_terminalPayoff`. -/
theorem quittingBlockJoinCap_eq_zero_of_blockJoinAntitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {B : Finset ι}
    {owner : ι} (hjoin : QuittingBlockJoinAntitone reward B owner) :
    quittingBlockJoinCap reward B owner = 0 := by
  refine le_antisymm ?_ (quittingBlockJoinCap_nonneg reward B owner)
  refine Finset.max'_le _ _ _ ?_
  intro value hvalue
  rcases Finset.mem_insert.mp hvalue with hzero | hmem
  · exact hzero.le
  · obtain ⟨terminal, hterminal, rfl⟩ := Finset.mem_image.mp hmem
    have hdisjoint : Disjoint terminal.1 B := (Finset.mem_filter.mp hterminal).2
    have hstep := hjoin terminal.1 terminal.2 hdisjoint
    linarith

/-- The join cap is the least nonnegative upper bound of the survivor join
margins. -/
theorem quittingBlockJoinCap_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (owner : ι) {value : ℝ} (hzero : 0 ≤ value)
    (hrow : ∀ (S : Finset ι) (hS : S.Nonempty), Disjoint S B →
      reward ⟨insert owner S, Finset.insert_nonempty owner S⟩ owner -
        reward ⟨S, hS⟩ owner ≤ value) :
    quittingBlockJoinCap reward B owner ≤ value := by
  classical
  unfold quittingBlockJoinCap
  refine Finset.max'_le _ _ _ ?_
  intro entry hentry
  rcases Finset.mem_insert.mp hentry with hzeroEntry | hmem
  · exact hzeroEntry ▸ hzero
  · obtain ⟨terminal, hterminal, rfl⟩ := Finset.mem_image.mp hmem
    exact hrow terminal.1 terminal.2 (Finset.mem_filter.mp hterminal).2

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

theorem quittingStationaryContinueMass_extendBlockRoot (B : Finset ι)
    (root : QuittingBlockSurvivor B → PMF Bool) :
    quittingStationaryContinueMass (quittingExtendBlockRoot B root) =
      quittingStationaryContinueMass root := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    prod_split_quittingBlock B
      (fun who => (quittingExtendBlockRoot B root who false).toReal),
    Finset.prod_eq_one (fun who hwho => by simp [hwho]), one_mul]
  exact Finset.prod_congr rfl fun who _ => by simp

theorem quittingFixedOpponentsContinueMass_extendBlockRoots_of_mem
    (B : Finset ι) (roots : ℕ → QuittingBlockSurvivor B → PMF Bool)
    {owner : ι} (howner : owner ∈ B) (time : ℕ) :
    quittingFixedOpponentsContinueMass
        (quittingExtendBlockRoots B roots) owner time =
      quittingStationaryContinueMass (roots time) := by
  have hupdate : Function.update (quittingExtendBlockRoots B roots time) owner
      (PMF.pure false) = quittingExtendBlockRoots B roots time := by
    funext who
    by_cases hp : who = owner
    · subst who
      simp [howner]
    · rw [Function.update_of_ne hp]
  unfold quittingFixedOpponentsContinueMass
  rw [hupdate]
  exact quittingStationaryContinueMass_extendBlockRoot B (roots time)

/-- The excess bound applies to every deleted player against the lift of a
survivor profile whose per-stage absorption never exceeds
`absorptionBound`. -/
theorem quittingBestReplyValue_liftBlockProfile_le_add_excessBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (profile : (quittingGame
      (quittingDeleteBlockReward reward B)).BehaviorProfile)
    {owner : ι} (howner : owner ∈ B) {absorptionBound : ℝ}
    (habsorb : ∀ time, 1 - quittingStationaryContinueMass
      (quittingProfileLiveRoot (quittingDeleteBlockReward reward B)
        profile time) ≤ absorptionBound) :
    quittingBestReplyValue reward
        (quittingLiftBlockProfile reward B profile) owner ≤
      quittingTerminalPayoff reward
          (quittingLiftBlockProfile reward B profile) owner +
        quittingBlockDeletionExcessBound reward B owner absorptionBound := by
  have hroot := quittingProfileLiveRoot_liftBlockProfile reward B profile
  have hquiet : QuittingRootsBlockQuiet B owner
      (quittingProfileLiveRoot reward
        (quittingLiftBlockProfile reward B profile)) := by
    rw [hroot]
    exact (quittingRootsQuietOn_extendBlockRoots B _).blockQuiet owner
  have hmass : ∀ time, 1 - quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward
        (quittingLiftBlockProfile reward B profile)) owner time ≤
      absorptionBound := by
    intro time
    rw [hroot, quittingFixedOpponentsContinueMass_extendBlockRoots_of_mem
      B _ howner time]
    exact habsorb time
  have hstep := quittingBestReplyValue_le_never_add_excessBound reward B
    (quittingLiftBlockProfile reward B profile) owner hquiet hmass
  rwa [Function.update_liftBlockProfile_never reward B profile howner] at hstep

/-! ## The deletion inequality -/

/-- **The quantitative deletion inequality.**  If the original game has a
terminal exploitability gap and the survivor game has a terminal
`error`-equilibrium with `error < gap` whose per-stage absorption never
exceeds `absorptionBound`, then some deleted player's excess bound is at least
the gap. -/
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
  obtain ⟨player, deviation, hdeviation⟩ :=
    hexploit (quittingLiftBlockProfile reward B profile)
  by_cases hp : player ∈ B
  · refine ⟨player, hp, ?_⟩
    have hbest := quittingBestReplyValue_liftBlockProfile_le_add_excessBound
      reward B profile hp habsorb
    have hupper := le_quittingBestReplyValue reward
      (quittingLiftBlockProfile reward B profile) player deviation
    linarith
  · exfalso
    have hon := quittingTerminalPayoff_liftBlockProfile
      reward B profile ⟨player, hp⟩
    have hdev :=
      quittingTerminalPayoff_update_liftBlockProfile_eq_deleteDeviation
        reward B profile ⟨player, hp⟩ deviation
    have hstep := hnash ⟨player, hp⟩
      (quittingDeleteBlockDeviation reward B ⟨player, hp⟩ deviation)
    dsimp only at hon hdev
    linarith

/-! ## Deleting a single player over at most three survivors -/

theorem card_quittingBlockSurvivor_singleton (owner : ι) :
    Fintype.card (QuittingBlockSurvivor ({owner} : Finset ι)) =
      Fintype.card ι - 1 := by
  rw [show Fintype.card (QuittingBlockSurvivor ({owner} : Finset ι)) =
      Fintype.card {x : ι // ¬ x ∈ ({owner} : Finset ι)} from rfl,
    Fintype.card_subtype_compl]
  simp

theorem card_quittingBlockSurvivor_singleton_eq_three
    (hcard : Fintype.card ι = 4) (owner : ι) :
    Fintype.card (QuittingBlockSurvivor ({owner} : Finset ι)) = 3 := by
  rw [card_quittingBlockSurvivor_singleton, hcard]

/-- A survivor game with at most three players has terminal approximate
equilibria at every positive accuracy, unconditionally. -/
theorem exists_terminalNash_deleteBlock_of_card_le_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hcard : Fintype.card (QuittingBlockSurvivor B) ≤ 3) :
    ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward B)).BehaviorProfile,
        (quittingGame (quittingDeleteBlockReward reward B)).IsεAsymptoticNash
          (quittingTerminalPayoff (quittingDeleteBlockReward reward B))
          error profile := by
  obtain ⟨payoff, hpayoff⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three hcard
      (quittingDeleteBlockReward reward B)
  exact quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
    (quittingDeleteBlockReward reward B) payoff hpayoff

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

/-- **The vanishing-absorption necessary condition.**  If the survivor game
has terminal approximate equilibria of arbitrarily small accuracy whose
per-stage absorption is arbitrarily small, the join term of the deletion
inequality drops out and the deleted player must clear its continue floor by
the whole gap. -/
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
  have hpremiumNonneg : 0 ≤ premium := le_max_left _ _
  have hdenom : (0 : ℝ) < 2 * (cap + 1) := by linarith
  set delta := (gap - premium) / (2 * (cap + 1)) with hdeltaDef
  have hdeltaPos : 0 < delta := div_pos (by linarith) hdenom
  have hdeltaMul : delta * (2 * (cap + 1)) = gap - premium := by
    rw [hdeltaDef]
    field_simp
  have hdeltaCap : 0 ≤ delta * cap := mul_nonneg hdeltaPos.le hcap
  have hdeltaSmall : delta * cap ≤ (gap - premium) / 2 := by nlinarith
  have hdeltaHalf : delta ≤ gap / 2 := by nlinarith
  obtain ⟨profile, hnash, habsorb⟩ := hvanishing delta hdeltaPos
  have hmain := gap_le_singletonDeletionExcessBound reward owner hexploit
    profile hnash (by linarith) habsorb
  unfold quittingBlockDeletionExcessBound at hmain
  rw [← hcapDef, ← hpremiumDef] at hmain
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

/-! ## Four players

At four players the survivor game after deleting one player has exactly three
players, so its terminal approximate equilibria exist unconditionally and the
single-deleted-player inequality applies to every player with no induction
hypothesis. -/

/-- At four players, the three-player subgame omitting one player has terminal
approximate equilibria at every positive accuracy. -/
theorem fourPlayer_exists_terminalNash_deleteSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card ι = 4) (owner : ι) :
    ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward
            ({owner} : Finset ι))).BehaviorProfile,
        (quittingGame
            (quittingDeleteBlockReward reward
              ({owner} : Finset ι))).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteBlockReward reward ({owner} : Finset ι)))
          error profile :=
  exists_terminalNash_deleteBlock_of_card_le_three reward {owner}
    (le_of_eq (card_quittingBlockSurvivor_singleton_eq_three hcard owner))

/-- **The four-player dichotomy.**  At four players with a positive gap, every
player admits a three-player subgame approximate equilibrium sharper than the
gap, and against any per-stage absorption bound for it the omitted player
either escapes on its own or is atomically tempted.

This is a necessary condition on a counterexample.  It does not characterize
solvability: a four-player table can be solved by a profile in which every
player quits, and no lift of a subgame equilibrium sees such a profile. -/
theorem fourPlayer_exists_terminalNash_soloEscape_or_atomicTemptation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card ι = 4) (owner : ι) {gap error : ℝ}
    (hgap : 0 < gap) (hexploit : HasTerminalExploitabilityGap reward gap)
    (herrorPos : 0 < error) (herror : error < gap) :
    ∃ profile : (quittingGame
        (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile,
      (quittingGame
          (quittingDeleteBlockReward reward
            ({owner} : Finset ι))).IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingDeleteBlockReward reward ({owner} : Finset ι)))
        error profile ∧
      ∀ absorptionBound : ℝ,
        (∀ time, 1 - quittingStationaryContinueMass
          (quittingProfileLiveRoot
            (quittingDeleteBlockReward reward ({owner} : Finset ι))
            profile time) ≤ absorptionBound) →
        gap / 2 ≤ reward (quittingSingletonTerminal owner) owner -
            quittingBlockContinueFloor reward {owner} owner ∨
          (0 < quittingBlockJoinCap reward {owner} owner ∧
            gap / 2 ≤
              absorptionBound * quittingBlockJoinCap reward {owner} owner) := by
  obtain ⟨profile, hnash⟩ :=
    fourPlayer_exists_terminalNash_deleteSingleton reward hcard owner error
      herrorPos
  exact ⟨profile, hnash, fun absorptionBound habsorb =>
    singletonDeletion_soloEscape_or_atomicTemptation reward owner hgap hexploit
      profile hnash herror habsorb⟩

end GameTheory
