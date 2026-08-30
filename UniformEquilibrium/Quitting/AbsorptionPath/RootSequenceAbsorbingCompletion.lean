/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.SupportWitnessAbsorptionBridge
import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryRestart
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

/-!
# Late absorbing completion of quitting root sequences

An actual quitting root sequence with a small `Never` atom can be completed
after an arbitrarily requested finite prefix by one sure solo quitter.  The
owner is selected from the finite product of the players' own survival
clocks.  This makes every other player's deleted clock small.  The selected
owner is the exceptional coordinate: its sure-solo deviation envelope is
compared exactly with the Never cap and then with the source by deleted-tail
coupling.

The result is quantitative at the level needed by terminal Nash consumers.
It does not construct, compactify, or take a limit of absorption paths.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The literal sure-solo completion attached after `cutoff`. -/
def quittingLateSureSoloRoots
    (roots : ℕ → ι → PMF Bool) (owner : ι) (cutoff : ℕ) :
    ℕ → ι → PMF Bool :=
  quittingElementaryTailRoots roots cutoff (.sureSolo owner)

omit [Fintype ι] [Nonempty ι] in
@[simp] theorem quittingLateSureSoloRoots_cutoff_owner
    (roots : ℕ → ι → PMF Bool) (owner : ι) (cutoff : ℕ) :
    quittingLateSureSoloRoots roots owner cutoff cutoff owner = PMF.pure true := by
  have hroot := congrFun (quittingElementaryTailRoots_add roots cutoff 0
    (.sureSolo owner)) owner
  simpa [quittingLateSureSoloRoots, quittingElementaryCapRoots,
    quittingSureSoloRoot] using hroot

omit [Nonempty ι] in
theorem quittingJointSurvivalLimit_lateSureSolo_eq_zero
    (roots : ℕ → ι → PMF Bool) (owner : ι) (cutoff : ℕ) :
    quittingJointSurvivalLimit
      (quittingLateSureSoloRoots roots owner cutoff) 0 = 0 := by
  let completed := quittingLateSureSoloRoots roots owner cutoff
  have hzero : quittingJointSurvivalWeight completed 0 (cutoff + 1) = 0 := by
    simp only [Nat.zero_add, quittingJointSurvivalWeight_succ]
    apply mul_eq_zero_of_right
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_eq_zero (Finset.mem_univ owner)
    change (completed cutoff owner false).toReal = 0
    dsimp only [completed]
    rw [quittingLateSureSoloRoots_cutoff_owner]
    norm_num
  have hle := le_quittingJointSurvivalWeight_of_tendsto completed 0
    (tendsto_quittingJointSurvivalLimit completed 0) (cutoff + 1)
  rw [hzero] at hle
  exact le_antisymm hle (quittingJointSurvivalLimit_nonneg completed 0)

/-- Zero-one reward selecting one finite terminal coalition. -/
def quittingTerminalCoalitionIndicatorReward
    (terminal : {S : Finset ι // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun outcome _ => if outcome = terminal then 1 else 0

omit [Fintype ι] [Nonempty ι] in
theorem quittingTerminalCoalitionIndicatorReward_abs_le_one
    (terminal outcome : {S : Finset ι // S.Nonempty}) (who : ι) :
    |quittingTerminalCoalitionIndicatorReward terminal outcome who| ≤ 1 := by
  simp only [quittingTerminalCoalitionIndicatorReward]
  split_ifs <;> norm_num

omit [Nonempty ι] in
/-- A finite coordinate of the actual complete terminal law of root-sequence
profile is the terminal value of its zero-one indicator reward. -/
theorem quittingTerminalOutcomeMass_rootSequence_some_eq_indicatorValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (terminal : {S : Finset ι // S.Nonempty})
    (observer : ι) :
    quittingTerminalOutcomeMass reward
        (quittingRootSequenceProfile reward roots 0) (some terminal) =
      quittingRootSequenceTerminalValue
        (quittingTerminalCoalitionIndicatorReward terminal) roots observer 0 := by
  let indicator := quittingTerminalCoalitionIndicatorReward terminal
  let profile := quittingRootSequenceProfile indicator roots 0
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass indicator profile) observer
  have hmass : quittingAbsorbedMassLimit reward
      (quittingRootSequenceProfile reward roots 0) terminal =
        quittingAbsorbedMassLimit indicator profile terminal := by
    exact quittingAbsorbedMassLimit_reward_irrelevant reward indicator
      (quittingRootSequenceProfile reward roots 0) terminal
  change quittingAbsorbedMassLimit reward
      (quittingRootSequenceProfile reward roots 0) terminal = _
  rw [hmass]
  change quittingAbsorbedMassLimit indicator profile terminal =
    quittingTerminalPayoff indicator profile observer
  rw [← hmoment]
  unfold quittingTerminalRewardMoment quittingTerminalOutcomeReward
    quittingTerminalOutcomeMass indicator profile
  rw [Fintype.sum_option]
  simp only [Pi.zero_apply, mul_zero, zero_add, indicator,
    quittingTerminalCoalitionIndicatorReward]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp

/-- Data and quantitative conclusions of one late sure-solo completion.
The source roots remain an explicit parameter, so the prefix and all error
bounds refer to one literal supplied sequence. -/
structure QuittingRootSequenceLateSureSoloCompletion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (lowerBound : ℕ) (ε d M : ℝ) where
  owner : ι
  cutoff : ℕ
  cutoff_ge : lowerBound ≤ cutoff
  joint_survival_lt :
    quittingJointSurvivalWeight roots 0 cutoff < d ^ Fintype.card ι
  owner_ownSurvival_le :
    quittingHazardSurvival (quittingRootSequenceOwnHazard roots owner) cutoff ≤ d
  owner_deletedTail_lt :
    quittingOpponentSurvivalWeight roots owner 0 cutoff -
      quittingOpponentSurvivalLimit roots owner 0 < d
  terminalLaw_close : ∀ outcome,
    |quittingTerminalOutcomeMass reward
          (quittingRootSequenceProfile reward roots 0) outcome -
        quittingTerminalOutcomeMass reward
          (quittingRootSequenceProfile reward
            (quittingLateSureSoloRoots roots owner cutoff) 0) outcome| ≤
      2 * d ^ Fintype.card ι
  prescribed_close : ∀ who,
    |quittingRootSequenceTerminalValue reward roots who 0 -
        quittingRootSequenceTerminalValue reward
          (quittingLateSureSoloRoots roots owner cutoff) who 0| ≤
      2 * M * d ^ Fintype.card ι
  envelope_close : ∀ who,
    |quittingRootSequenceBestResponseValue reward roots who -
        quittingRootSequenceBestResponseValue reward
          (quittingLateSureSoloRoots roots owner cutoff) who| ≤ 2 * M * d
  nash : IsεQuittingRootSequenceNash reward
    (ε + 2 * M * (d + d ^ Fintype.card ι))
    (quittingLateSureSoloRoots roots owner cutoff)

namespace QuittingRootSequenceLateSureSoloCompletion

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {lowerBound : ℕ} {ε d M : ℝ}

omit [Nonempty ι] in
/-- The completed word is definitionally the source word before its cutoff. -/
theorem prefix_eq
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M)
    {time : ℕ} (htime : time < completion.cutoff) :
    quittingLateSureSoloRoots roots completion.owner completion.cutoff time =
      roots time :=
  quittingElementaryTailRoots_of_lt roots (.sureSolo completion.owner) htime

omit [Nonempty ι] in
/-- The completed word has a literal sure solo quitter at the cutoff. -/
theorem cutoff_owner_eq_pureQuit
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) :
    quittingLateSureSoloRoots roots completion.owner completion.cutoff
        completion.cutoff completion.owner = PMF.pure true := by
  exact quittingLateSureSoloRoots_cutoff_owner roots completion.owner
    completion.cutoff

omit [Nonempty ι] in
/-- Joint survival of the completed sequence is already exactly zero just
after its literal sure-solo row. -/
theorem jointSurvival_cutoff_succ_eq_zero
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) :
    quittingJointSurvivalWeight
        (quittingLateSureSoloRoots roots completion.owner completion.cutoff)
        0 (completion.cutoff + 1) = 0 := by
  simp only [Nat.zero_add, quittingJointSurvivalWeight_succ]
  apply mul_eq_zero_of_right
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ completion.owner)
  have howner := completion.cutoff_owner_eq_pureQuit
  rw [howner]
  norm_num

omit [Nonempty ι] in
/-- A sure solo root makes the completed sequence completely absorbing. -/
theorem completelyAbsorbing
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) :
    IsCompletelyAbsorbing
      (quittingLateSureSoloRoots roots completion.owner completion.cutoff) := by
  let completed := quittingLateSureSoloRoots roots completion.owner completion.cutoff
  have hzero : quittingSurvivalPrefix completed (completion.cutoff + 1) = 0 := by
    calc
      quittingSurvivalPrefix completed (completion.cutoff + 1) =
          quittingJointSurvivalWeight completed 0 (completion.cutoff + 1) := by
        simpa using (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix
          completed 0 (completion.cutoff + 1)).symm
      _ = 0 := completion.jointSurvival_cutoff_succ_eq_zero
  change IsCompletelyAbsorbing completed
  unfold IsCompletelyAbsorbing
  rw [Metric.tendsto_atTop]
  intro tolerance htolerance
  refine ⟨completion.cutoff + 1, fun time htime => ?_⟩
  have hle := quittingSurvivalPrefix_antitone completed htime
  rw [hzero] at hle
  have hnonneg := quittingSurvivalPrefix_nonneg completed time
  have heq : quittingSurvivalPrefix completed time = 0 := le_antisymm hle hnonneg
  simp [heq, htolerance]

/-- The exact Nash widening can be weakened to the simpler `4 M d` bound. -/
theorem nash_add_four_mul_d
    (completion : QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hM : 0 ≤ M) :
    IsεQuittingRootSequenceNash reward (ε + 4 * M * d)
      (quittingLateSureSoloRoots roots completion.owner completion.cutoff) := by
  have hcardPos : 0 < Fintype.card ι := Fintype.card_pos
  have hpow : d ^ Fintype.card ι ≤ d := by
    obtain ⟨card, hcard⟩ := Nat.exists_eq_succ_of_ne_zero hcardPos.ne'
    rw [hcard, pow_succ]
    exact mul_le_of_le_one_left hd0.le (pow_le_one₀ hd0.le hd1)
  intro who hazard
  have hnash := completion.nash who hazard
  nlinarith

end QuittingRootSequenceLateSureSoloCompletion

/-! ## Construction at a supplied cutoff -/

/-- A cutoff with small joint survival, one small own-survival clock, and a
small exceptional deleted-tail loss produces the full sure-solo completion.
These are exactly the three finite-cutoff inequalities used in the proof. -/
theorem nonempty_lateSureSoloCompletion_at_cutoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (lowerBound : ℕ)
    {ε d M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (owner : ι) (cutoff : ℕ) (hcutoff : lowerBound ≤ cutoff)
    (hjoint : quittingJointSurvivalWeight roots 0 cutoff <
      d ^ Fintype.card ι)
    (hown : quittingHazardSurvival
      (quittingRootSequenceOwnHazard roots owner) cutoff ≤ d)
    (htail : quittingOpponentSurvivalWeight roots owner 0 cutoff -
      quittingOpponentSurvivalLimit roots owner 0 < d) :
    Nonempty (QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) := by
  let completed := quittingLateSureSoloRoots roots owner cutoff
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_nonempty reward hreward
  have hlaw : ∀ outcome,
      |quittingTerminalOutcomeMass reward
            (quittingRootSequenceProfile reward roots 0) outcome -
          quittingTerminalOutcomeMass reward
            (quittingRootSequenceProfile reward completed 0) outcome| ≤
        2 * d ^ Fintype.card ι := by
    intro outcome
    cases outcome with
    | none =>
        change |quittingLiveMassLimit reward
              (quittingRootSequenceProfile reward roots 0) -
            quittingLiveMassLimit reward
              (quittingRootSequenceProfile reward completed 0)| ≤ _
        rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit,
          quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit,
          quittingJointSurvivalLimit_lateSureSolo_eq_zero]
        rw [sub_zero, abs_of_nonneg
          (quittingJointSurvivalLimit_nonneg roots 0)]
        have hlimit := le_quittingJointSurvivalWeight_of_tendsto roots 0
          (tendsto_quittingJointSurvivalLimit roots 0) cutoff
        have hpowNonneg : 0 ≤ d ^ Fintype.card ι :=
          (quittingJointSurvivalWeight_nonneg roots 0 cutoff).trans hjoint.le
        linarith
    | some terminal =>
        rw [quittingTerminalOutcomeMass_rootSequence_some_eq_indicatorValue
          reward roots terminal owner,
          quittingTerminalOutcomeMass_rootSequence_some_eq_indicatorValue
            reward completed terminal owner]
        have hbound :=
          abs_quittingRootSequenceTerminalValue_sub_elementarySureSolo_le
            (quittingTerminalCoalitionIndicatorReward terminal) roots owner
              owner cutoff (M := 1)
              (quittingTerminalCoalitionIndicatorReward_abs_le_one terminal)
        dsimp only [completed, quittingLateSureSoloRoots]
        norm_num at hbound ⊢
        exact hbound.trans (mul_le_mul_of_nonneg_left hjoint.le (by norm_num))
  have hprescribed : ∀ who,
      |quittingRootSequenceTerminalValue reward roots who 0 -
          quittingRootSequenceTerminalValue reward completed who 0| ≤
        2 * M * d ^ Fintype.card ι := by
    intro who
    have hbound :=
      abs_quittingRootSequenceTerminalValue_sub_elementarySureSolo_le
        reward roots owner who cutoff hreward
    dsimp only [completed, quittingLateSureSoloRoots]
    exact hbound.trans (mul_le_mul_of_nonneg_left hjoint.le
      (mul_nonneg (by norm_num) hM))
  have henvelope : ∀ who,
      |quittingRootSequenceBestResponseValue reward roots who -
          quittingRootSequenceBestResponseValue reward completed who| ≤
        2 * M * d := by
    intro who
    by_cases hwho : who = owner
    · subst who
      rw [show quittingRootSequenceBestResponseValue reward completed owner =
          quittingRootSequenceBestResponseValue reward
            (quittingElementaryTailRoots roots cutoff (.never)) owner by
        dsimp only [completed, quittingLateSureSoloRoots]
        exact
          quittingRootSequenceBestResponseValue_elementarySureSolo_owner_eq_never
            reward roots cutoff owner]
      by_cases hlimitZero :
          quittingOpponentSurvivalLimit roots owner 0 = 0
      · have hbound :=
          abs_quittingRootSequenceBestResponseValue_sub_elementarySureSolo_le
            reward roots owner owner cutoff hreward
        rw [quittingRootSequenceBestResponseValue_elementarySureSolo_owner_eq_never]
          at hbound
        have hclock : quittingOpponentSurvivalWeight roots owner 0 cutoff < d := by
          rw [← sub_zero
            (quittingOpponentSurvivalWeight roots owner 0 cutoff),
            ← hlimitZero]
          exact htail
        exact hbound.trans (mul_le_mul_of_nonneg_left hclock.le
          (mul_nonneg (by norm_num) hM))
      · have hlimitPos : 0 < quittingOpponentSurvivalLimit roots owner 0 :=
          lt_of_le_of_ne (quittingOpponentSurvivalLimit_nonneg roots owner 0)
            (Ne.symm hlimitZero)
        have hbound :=
          abs_quittingRootSequenceBestResponseValue_sub_elementaryNever_le
            reward roots owner cutoff hreward hlimitPos
        exact hbound.trans (mul_le_mul_of_nonneg_left htail.le
          (mul_nonneg (by norm_num) hM))
    · have hbound :=
        abs_quittingRootSequenceBestResponseValue_sub_elementarySureSolo_le
          reward roots owner who cutoff hreward
      have hclock : quittingOpponentSurvivalWeight roots who 0 cutoff ≤ d :=
        (quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
          roots (Ne.symm hwho) cutoff).trans hown
      dsimp only [completed, quittingLateSureSoloRoots]
      exact hbound.trans (mul_le_mul_of_nonneg_left hclock
        (mul_nonneg (by norm_num) hM))
  have hnashProfile :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward ε roots).mp hnash
  have hsourceBest : ∀ who,
      quittingRootSequenceBestResponseValue reward roots who ≤
        quittingRootSequenceTerminalValue reward roots who 0 + ε := by
    intro who
    unfold quittingRootSequenceBestResponseValue
      quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, ⟨(quittingRootSequenceProfile reward roots 0) who, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact hnashProfile who deviation
  have hcompletedNash : IsεQuittingRootSequenceNash reward
      (ε + 2 * M * (d + d ^ Fintype.card ι)) completed := by
    intro who hazard
    have hhazard : quittingRootSequenceHazardTerminalValue reward completed
        who hazard 0 ≤ quittingRootSequenceBestResponseValue reward completed who := by
      unfold quittingRootSequenceBestResponseValue
      rw [quittingRootSequenceHazardTerminalValue_eq_terminalPayoff_update]
      exact quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (quittingRootSequenceProfile reward completed 0) who
          (fun time _history => hazard time)
    have hbestUpper : quittingRootSequenceBestResponseValue reward completed who ≤
        quittingRootSequenceBestResponseValue reward roots who + 2 * M * d := by
      linarith [neg_le_abs
        (quittingRootSequenceBestResponseValue reward roots who -
          quittingRootSequenceBestResponseValue reward completed who),
        henvelope who]
    have hpayoffUpper : quittingRootSequenceTerminalValue reward roots who 0 ≤
        quittingRootSequenceTerminalValue reward completed who 0 +
          2 * M * d ^ Fintype.card ι := by
      linarith [le_abs_self
        (quittingRootSequenceTerminalValue reward roots who 0 -
          quittingRootSequenceTerminalValue reward completed who 0),
        hprescribed who]
    have hsource := hsourceBest who
    dsimp only [completed] at hhazard hbestUpper hpayoffUpper ⊢
    linarith
  exact ⟨{
    owner := owner
    cutoff := cutoff
    cutoff_ge := hcutoff
    joint_survival_lt := hjoint
    owner_ownSurvival_le := hown
    owner_deletedTail_lt := htail
    terminalLaw_close := hlaw
    prescribed_close := hprescribed
    envelope_close := henvelope
    nash := hcompletedNash
  }⟩

/-! ## Late-cutoff selection from the actual Never atom -/

/-- If the actual root sequence's `Never` mass is below `d ^ card ι`, then
after every requested finite prefix there is a sure-solo completion with the
quantitative payoff, envelope, and Nash bounds above.  The single cutoff is
chosen late enough for all deleted clocks before the owner is selected. -/
theorem exists_lateSureSoloCompletion_of_jointLimit_lt_pow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (lowerBound : ℕ)
    {ε d M : ℝ} (hd : 0 < d)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : IsεQuittingRootSequenceNash reward ε roots)
    (hnever : quittingJointSurvivalLimit roots 0 <
      d ^ Fintype.card ι) :
    Nonempty (QuittingRootSequenceLateSureSoloCompletion
      reward roots lowerBound ε d M) := by
  have hjointEventually : ∀ᶠ cutoff in atTop,
      quittingJointSurvivalWeight roots 0 cutoff <
        d ^ Fintype.card ι :=
    (tendsto_quittingJointSurvivalLimit roots 0).eventually_lt_const hnever
  have htailEventually : ∀ who, ∀ᶠ cutoff in atTop,
      quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0 < d := by
    intro who
    have htendsto : Tendsto (fun cutoff =>
        quittingOpponentSurvivalWeight roots who 0 cutoff -
          quittingOpponentSurvivalLimit roots who 0) atTop (nhds 0) := by
      simpa using (tendsto_quittingOpponentSurvivalLimit roots who 0).sub_const
        (quittingOpponentSurvivalLimit roots who 0)
    exact htendsto.eventually_lt_const hd
  have htailAll : ∀ᶠ cutoff in atTop, ∀ who,
      quittingOpponentSurvivalWeight roots who 0 cutoff -
        quittingOpponentSurvivalLimit roots who 0 < d :=
    Filter.eventually_all.mpr htailEventually
  obtain ⟨cutoff, hcutoff, hjoint, htail⟩ :=
    ((eventually_ge_atTop lowerBound).and
      (hjointEventually.and htailAll)).exists
  have hsurvival : quittingSurvivalPrefix roots cutoff <
      d ^ Fintype.card ι := by
    calc
      quittingSurvivalPrefix roots cutoff =
          quittingJointSurvivalWeight roots 0 cutoff := by
        simpa using (quittingJointSurvivalWeight_eq_quittingSurvivalPrefix
          roots 0 cutoff).symm
      _ < d ^ Fintype.card ι := hjoint
  obtain ⟨owner, howner⟩ :=
    exists_ownSurvival_le_of_survivalPrefix_lt_pow roots cutoff hd hsurvival
  exact nonempty_lateSureSoloCompletion_at_cutoff reward roots lowerBound
    hreward hnash owner cutoff hcutoff hjoint howner (htail owner)

end GameTheory
