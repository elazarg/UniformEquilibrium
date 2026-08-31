/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.FiniteMixedNashSupport
import UniformEquilibrium.Diagnostics.Quitting.AdjacentDeadlineGapSource
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailGraftDecomposition

/-!
# Adjacent-deadline retained-tail reprojection

This module records the literal timing laws and behavioral profiles used to
reproject one adjacent finite-deadline source over a supplied behavioral tail.
It proves exact support, pass-through, zero-`Never`, and reverse-participant
identities.  It does not select the source or tail, put the tail on a minimum
fibre, or produce chronology, return, renewal, terminal approximation, or a
uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem expect_sub_expect_censoredLift_eq_boundary_mul
    {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (value : QuittingFiniteDeadlineTimingAction (deadline + 1) → ℝ) :
    Math.Probability.expect law value -
        Math.Probability.expect
          ((law.map quittingFiniteDeadlineTimingActionCensor).map
            quittingFiniteDeadlineTimingActionInclude) value =
      (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal *
        (value (quittingFiniteDeadlineTimingBoundaryAction deadline) -
          value none) := by
  rw [Math.Probability.expect_map, Math.Probability.expect_map,
    ← Math.Probability.expect_sub, Math.Probability.expect_eq_sum]
  rw [Finset.sum_eq_single
    (quittingFiniteDeadlineTimingBoundaryAction deadline)]
  · simp [quittingFiniteDeadlineTimingActionCensor,
      quittingFiniteDeadlineTimingActionInclude,
      quittingFiniteDeadlineTimingBoundaryAction]
  · intro action _ haction
    cases action with
    | none => simp [quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingActionInclude]
    | some date =>
        have hne : date ≠ ⟨deadline, Nat.lt_succ_self deadline⟩ := by
          intro heq
          apply haction
          simp [quittingFiniteDeadlineTimingBoundaryAction, heq]
        have hlt : date.val < deadline := by
          have hle := Nat.le_of_lt_succ date.isLt
          exact lt_of_le_of_ne hle fun heq => hne (Fin.ext heq)
        simp [quittingFiniteDeadlineTimingActionCensor,
          quittingFiniteDeadlineTimingActionInclude, hlt]
  · simp

private theorem prod_update_none_toReal
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction n))
    (who : ι) (law : PMF (QuittingFiniteDeadlineTimingAction n)) :
    (∏ player, ((Function.update mixed who law) player none).toReal) =
      (law none).toReal *
        ∏ other ∈ Finset.univ.erase who, (mixed other none).toReal := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ who)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]

omit [Fintype ι] [DecidableEq ι] in
/-- Successor-clock inclusion preserves the literal `Never` coefficient. -/
theorem finiteDeadlineTimingProfileInclude_none_toReal
    {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingFiniteDeadlineTimingProfileInclude mixed who none).toReal =
      (mixed who none).toReal := by
  unfold quittingFiniteDeadlineTimingProfileInclude
  rw [PMF.map_apply]
  simp [quittingFiniteDeadlineTimingActionInclude]

/-! ## Literal retained-tail profiles -/

/-- The included old timing law on the successor clock. -/
def quittingAdjacentDeadlineOldIncludedTiming
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :=
  quittingFiniteDeadlineTimingProfileInclude source.old

/-- The old source law executed on the successor clock before a common tail. -/
def quittingAdjacentDeadlineOldGraft
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :=
  quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
    (quittingAdjacentDeadlineOldIncludedTiming source) tail

/-- The old observer forced to Quit at the newly exposed boundary date. -/
def quittingAdjacentDeadlineOldBoundaryProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :=
  quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
    (Function.update (quittingAdjacentDeadlineOldIncludedTiming source)
      source.observer
      (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
    tail

/-- The old observer forced to pass the finite word and resume its tail. -/
def quittingAdjacentDeadlineOldPassProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :=
  quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
    (Function.update (quittingAdjacentDeadlineOldIncludedTiming source)
      source.observer (PMF.pure none)) tail

/-- The successor law after censoring its new boundary and lifting it back to
the successor clock. -/
def quittingAdjacentDeadlineCensoredTiming
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :=
  quittingFiniteDeadlineTimingProfileInclude
    (quittingFiniteDeadlineTimingProfileCensor source.new)

/-- The fully censored successor law before a common tail. -/
def quittingAdjacentDeadlineCensoredGraft
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :=
  quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
    (quittingAdjacentDeadlineCensoredTiming source) tail

/-- Restore one successor marginal above the fully censored source. -/
def quittingAdjacentDeadlineParticipantTiming
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (participant : ι) :=
  Function.update (quittingAdjacentDeadlineCensoredTiming source) participant
    (source.new participant)

/-- Restore one successor marginal and execute the resulting law before the
common tail. -/
def quittingAdjacentDeadlineParticipantGraft
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) :=
  quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
    (quittingAdjacentDeadlineParticipantTiming source participant) tail

/-- Opponent passage through the old hard timing word. -/
def quittingAdjacentDeadlineOldOpponentNeverProduct
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) : ℝ :=
  ∏ other ∈ Finset.univ.erase source.observer,
    (source.old other none).toReal

/-- Opponent passage through the fully censored successor word. -/
def quittingAdjacentDeadlineCensoredOpponentNeverProduct
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (who : ι) : ℝ :=
  ∏ other ∈ Finset.univ.erase who,
    ((quittingFiniteDeadlineTimingProfileCensor source.new) other none).toReal

private theorem finiteDeadline_boundaryEU_sub_neverEU_eq_prod_none_mul_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension.eu
          (Function.update (quittingFiniteDeadlineTimingProfileInclude mixed) who
            (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction deadline)))
          who -
        (quittingFiniteDeadlineTimingGame reward
          (deadline + 1)).mixedExtension.eu
          (Function.update (quittingFiniteDeadlineTimingProfileInclude mixed) who
            (PMF.pure none)) who =
      (∏ other ∈ Finset.univ.erase who, (mixed other none).toReal) *
        reward (quittingSingletonTerminal who) who := by
  let profile := quittingFiniteDeadlineTimingProfile reward deadline mixed
  have hlate := quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
    reward (quittingProfileLiveRoot reward profile) who deadline deadline le_rfl
    (fun stage hstage => by
      dsimp only [profile]
      exact quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
        reward deadline mixed hstage)
  rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at hlate
  change quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who (some deadline))) who -
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who none)) who =
    quittingFiniteDeadlineOpponentSurvival reward profile deadline who *
      reward (quittingSingletonTerminal who) who at hlate
  dsimp only [profile] at hlate
  rw [quittingFiniteDeadlineOpponentSurvival_timingProfile_eq_prod_none]
    at hlate
  have hboundary :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (deadline + 1)
      (quittingFiniteDeadlineTimingProfileInclude mixed) who
      (quittingFiniteDeadlineTimingBoundaryAction deadline)
  have hnever :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (deadline + 1)
      (quittingFiniteDeadlineTimingProfileInclude mixed) who none
  have hprofile := quittingFiniteDeadlineTimingProfile_include_eq
    reward deadline mixed
  rw [hprofile] at hboundary hnever
  have hboundary' :
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who (some deadline))) who =
        (quittingFiniteDeadlineTimingGame reward
          (deadline + 1)).mixedExtension.eu
          (Function.update (quittingFiniteDeadlineTimingProfileInclude mixed) who
            (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction deadline)))
          who := by
    simpa only [show quittingFiniteDeadlineTimingActionTime
        (quittingFiniteDeadlineTimingBoundaryAction deadline) =
          (some deadline : Option ℕ) by rfl] using hboundary
  have hnever' :
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who none)) who =
        (quittingFiniteDeadlineTimingGame reward
          (deadline + 1)).mixedExtension.eu
          (Function.update (quittingFiniteDeadlineTimingProfileInclude mixed) who
            (PMF.pure none)) who := by
    simpa only [show quittingFiniteDeadlineTimingActionTime
        (none : QuittingFiniteDeadlineTimingAction (deadline + 1)) =
          (none : Option ℕ) by rfl] using hnever
  linarith

/-- Positive old `Never` support pins the newly exposed hard boundary gain to
the opponent-`Never` cylinder times the observer's singleton reward. -/
theorem finiteDeadline_supportNever_boundaryGain_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hsupport : source.old source.observer none ≠ 0) :
    (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain
        (quittingFiniteDeadlineTimingProfileInclude source.old)
        source.observer
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline) =
      (∏ other ∈ Finset.univ.erase source.observer,
          (source.old other none).toReal) *
        reward (quittingSingletonTerminal source.observer) source.observer := by
  letI : Finite
      (quittingFiniteDeadlineTimingGame reward source.deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : ι) : Finite
      ((quittingFiniteDeadlineTimingGame reward source.deadline).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  let profile := quittingFiniteDeadlineTimingProfile reward
    source.deadline source.old
  have hsupportGain :
      (quittingFiniteDeadlineTimingGame reward source.deadline).mixedGain
          source.old source.observer none = 0 :=
    KernelGame.mixedGain_eq_zero_of_mem_support
      (quittingFiniteDeadlineTimingGame reward source.deadline)
      source.old source.oldNash source.observer none hsupport
  have hneverPayoff :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward source.deadline source.old source.observer none
  have hprescribedOld :=
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
      reward source.deadline source.old source.observer
  have hneverPayoff' :
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward source.deadline source.old)
            source.observer
            (quittingPureTimeBehaviorStrategy reward source.observer none))
          source.observer =
        (quittingFiniteDeadlineTimingGame reward source.deadline).mixedExtension.eu
          (Function.update source.old source.observer (PMF.pure none))
          source.observer := by
    simpa only [show quittingFiniteDeadlineTimingActionTime
        (none : QuittingFiniteDeadlineTimingAction source.deadline) =
          (none : Option ℕ) by rfl] using hneverPayoff
  have hneverEq :
      quittingTerminalPayoff reward
          (Function.update profile source.observer
            (quittingPureTimeBehaviorStrategy reward source.observer none))
          source.observer =
        quittingTerminalPayoff reward profile source.observer := by
    unfold KernelGame.mixedGain at hsupportGain
    dsimp only [profile]
    linarith [hneverPayoff']
  have hlate :=
    quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
      reward (quittingProfileLiveRoot reward profile) source.observer
      source.deadline source.deadline le_rfl
      (fun stage hstage => by
        dsimp only [profile]
        exact quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
          reward source.deadline source.old hstage)
  rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at hlate
  change quittingTerminalPayoff reward
        (Function.update profile source.observer
          (quittingPureTimeBehaviorStrategy reward source.observer
            (some source.deadline))) source.observer -
      quittingTerminalPayoff reward
        (Function.update profile source.observer
          (quittingPureTimeBehaviorStrategy reward source.observer none))
          source.observer =
    quittingFiniteDeadlineOpponentSurvival reward profile source.deadline
        source.observer *
      reward (quittingSingletonTerminal source.observer) source.observer at hlate
  dsimp only [profile] at hlate
  rw [quittingFiniteDeadlineOpponentSurvival_timingProfile_eq_prod_none]
    at hlate
  have hboundaryPayoff :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (source.deadline + 1)
      (quittingFiniteDeadlineTimingProfileInclude source.old)
      source.observer
      (quittingFiniteDeadlineTimingBoundaryAction source.deadline)
  have hprescribed := quittingFiniteDeadlineTiming_mixedEU_include_eq
    reward source.deadline source.old source.observer
  unfold KernelGame.mixedGain
  rw [hprescribed]
  have hprofile := quittingFiniteDeadlineTimingProfile_include_eq
    reward source.deadline source.old
  rw [hprofile] at hboundaryPayoff
  have hboundaryPayoff' :
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward source.deadline source.old)
            source.observer
            (quittingPureTimeBehaviorStrategy reward source.observer
              (some source.deadline))) source.observer =
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedExtension.eu
          (Function.update (quittingFiniteDeadlineTimingProfileInclude source.old)
            source.observer
            (PMF.pure
              (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
          source.observer := by
    simpa only [show quittingFiniteDeadlineTimingActionTime
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline) =
          (some source.deadline : Option ℕ) by rfl] using hboundaryPayoff
  dsimp only [profile] at hneverEq hlate
  linarith [hboundaryPayoff']

/-! ## Exact graft identities -/

/-- Behind one common tail, the newly exposed boundary response minus passing
the finite word is exactly the opponent-`Never` cylinder times singleton
reward minus tail payoff. -/
theorem finiteDeadlineTailGraft_Q_sub_pass_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldBoundaryProfile source tail)
          source.observer -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldPassProfile source tail)
          source.observer =
      quittingAdjacentDeadlineOldOpponentNeverProduct source *
        (reward (quittingSingletonTerminal source.observer) source.observer -
          quittingTerminalPayoff reward tail source.observer) := by
  let mixed := quittingAdjacentDeadlineOldIncludedTiming source
  let boundaryLaw := Function.update mixed source.observer
    (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction source.deadline))
  let passLaw := Function.update mixed source.observer (PMF.pure none)
  have hboundary :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) boundaryLaw tail source.observer
  have hpass :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) passLaw tail source.observer
  have hincludeProd :
      (∏ other ∈ Finset.univ.erase source.observer,
          (mixed other none).toReal) =
        quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    apply Finset.prod_congr rfl
    intro other _
    exact finiteDeadlineTimingProfileInclude_none_toReal source.old other
  have hboundaryProd :
      (∏ player, (boundaryLaw player none).toReal) = 0 := by
    rw [prod_update_none_toReal]
    simp [quittingFiniteDeadlineTimingBoundaryAction]
  have hpassProd :
      (∏ player, (passLaw player none).toReal) =
        quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    rw [prod_update_none_toReal, hincludeProd]
    simp
  have hhard := finiteDeadline_boundaryEU_sub_neverEU_eq_prod_none_mul_singleton
    reward source.deadline source.old source.observer
  dsimp only [mixed, boundaryLaw, passLaw] at hboundary hpass
  rw [hboundaryProd, zero_mul, add_zero] at hboundary
  rw [hpassProd] at hpass
  let hardBoundary :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (Function.update (quittingFiniteDeadlineTimingProfileInclude source.old)
        source.observer
        (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
      source.observer
  let hardPass :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (Function.update (quittingFiniteDeadlineTimingProfileInclude source.old)
        source.observer (PMF.pure none)) source.observer
  let opponent := ∏ other ∈ Finset.univ.erase source.observer,
    (source.old other none).toReal
  change _ = hardBoundary at hboundary
  change _ = hardPass + opponent *
    quittingTerminalPayoff reward tail source.observer at hpass
  change hardBoundary - hardPass = opponent *
    reward (quittingSingletonTerminal source.observer) source.observer at hhard
  change quittingTerminalPayoff reward
        (quittingAdjacentDeadlineOldBoundaryProfile source tail)
        source.observer -
      quittingTerminalPayoff reward
        (quittingAdjacentDeadlineOldPassProfile source tail)
        source.observer = _
  unfold quittingAdjacentDeadlineOldBoundaryProfile
    quittingAdjacentDeadlineOldPassProfile
  simp only [quittingAdjacentDeadlineOldIncludedTiming,
    quittingAdjacentDeadlineOldOpponentNeverProduct] at hboundary hpass ⊢
  change _ = opponent *
    (reward (quittingSingletonTerminal source.observer) source.observer -
      quittingTerminalPayoff reward tail source.observer)
  rw [hboundary, hpass, mul_sub]
  linarith [hhard]

/-- Forcing the old observer to Quit at the new boundary is a literal
unilateral update of the old retained-tail profile. -/
theorem quittingAdjacentDeadlineOldBoundaryProfile_eq_update
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingAdjacentDeadlineOldBoundaryProfile source tail =
      Function.update (quittingAdjacentDeadlineOldGraft source tail)
        source.observer
        (quittingAdjacentDeadlineOldBoundaryProfile source tail
          source.observer) := by
  exact quittingRetainedTailMixedTimingProfile_update
    reward (source.deadline + 1)
      (quittingAdjacentDeadlineOldIncludedTiming source) tail source.observer
      (PMF.pure
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline))

/-- Passing the old finite word and resuming the common tail is a literal
unilateral update of the old retained-tail profile. -/
theorem quittingAdjacentDeadlineOldPassProfile_eq_update
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingAdjacentDeadlineOldPassProfile source tail =
      Function.update (quittingAdjacentDeadlineOldGraft source tail)
        source.observer
        (quittingAdjacentDeadlineOldPassProfile source tail source.observer) := by
  exact quittingRetainedTailMixedTimingProfile_update
    reward (source.deadline + 1)
      (quittingAdjacentDeadlineOldIncludedTiming source) tail source.observer
      (PMF.pure none)

/-- With positive old `Never` support, passing the old timing word has exact
actual payoff gain `Hᵢ (1-Sᵢ) Uᵢ(tail)`. -/
theorem finiteDeadlineOldPassProfile_sub_oldGraft_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hsupport : source.old source.observer none ≠ 0) :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldPassProfile source tail)
          source.observer -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldGraft source tail) source.observer =
      quittingAdjacentDeadlineOldOpponentNeverProduct source *
        (1 - (source.old source.observer none).toReal) *
        quittingTerminalPayoff reward tail source.observer := by
  let mixed := quittingAdjacentDeadlineOldIncludedTiming source
  let passLaw := Function.update mixed source.observer (PMF.pure none)
  have hbase :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) mixed tail source.observer
  have hpass :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) passLaw tail source.observer
  have hincludeProd :
      (∏ other ∈ Finset.univ.erase source.observer,
          (mixed other none).toReal) =
        quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    apply Finset.prod_congr rfl
    intro other _
    exact finiteDeadlineTimingProfileInclude_none_toReal source.old other
  have hobserver :
      (mixed source.observer none).toReal =
        (source.old source.observer none).toReal :=
    finiteDeadlineTimingProfileInclude_none_toReal source.old source.observer
  have hbaseProd : (∏ player, (mixed player none).toReal) =
      (source.old source.observer none).toReal *
        quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun player => (mixed player none).toReal)
      (Finset.mem_univ source.observer), hobserver, hincludeProd]
  have hpassProd : (∏ player, (passLaw player none).toReal) =
      quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    rw [prod_update_none_toReal, hincludeProd]
    simp
  have hboundaryGain := finiteDeadline_supportNever_boundaryGain_eq
    source hsupport
  have hhard := finiteDeadline_boundaryEU_sub_neverEU_eq_prod_none_mul_singleton
    reward source.deadline source.old source.observer
  unfold KernelGame.mixedGain at hboundaryGain
  dsimp only [mixed, passLaw] at hbase hpass
  rw [hbaseProd] at hbase
  rw [hpassProd] at hpass
  let hardBoundary :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (Function.update (quittingFiniteDeadlineTimingProfileInclude source.old)
        source.observer
        (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
      source.observer
  let hardPass :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (Function.update (quittingFiniteDeadlineTimingProfileInclude source.old)
        source.observer (PMF.pure none)) source.observer
  let hardBase :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (quittingFiniteDeadlineTimingProfileInclude source.old) source.observer
  let opponent := quittingAdjacentDeadlineOldOpponentNeverProduct source
  let ownNever := (source.old source.observer none).toReal
  let tailPayoff := quittingTerminalPayoff reward tail source.observer
  let singleton :=
    reward (quittingSingletonTerminal source.observer) source.observer
  change _ = hardBase + ownNever * opponent * tailPayoff at hbase
  change _ = hardPass + opponent * tailPayoff at hpass
  change hardBoundary - hardBase = opponent * singleton at hboundaryGain
  change hardBoundary - hardPass = opponent * singleton at hhard
  have hpassBase : hardPass = hardBase := by linarith
  unfold quittingAdjacentDeadlineOldPassProfile
    quittingAdjacentDeadlineOldGraft
  change _ - _ = opponent * (1 - ownNever) * tailPayoff
  rw [hpass, hbase, hpassBase]
  ring

/-- Singleton separation makes the literal pass response earn at least its
old support payment times the probability of not already passing. -/
theorem finiteDeadlineOldPassProfile_payoffGain_ge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hdelta : 0 < delta)
    (htail : delta / 2 ≤
      quittingTerminalPayoff reward tail source.observer -
        reward (quittingSingletonTerminal source.observer) source.observer)
    (hsupport : source.old source.observer none ≠ 0) :
    (1 - (source.old source.observer none).toReal) * gamma ≤
      quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldPassProfile source tail)
          source.observer -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineOldGraft source tail) source.observer := by
  rw [finiteDeadlineOldPassProfile_sub_oldGraft_eq source tail hsupport]
  have hgainEq := finiteDeadline_supportNever_boundaryGain_eq source hsupport
  have hgain := source.oldBoundaryGain_ge
  rw [hgainEq] at hgain
  have hopponent :
      0 ≤ quittingAdjacentDeadlineOldOpponentNeverProduct source := by
    unfold quittingAdjacentDeadlineOldOpponentNeverProduct
    exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have htailReward :
      reward (quittingSingletonTerminal source.observer) source.observer ≤
        quittingTerminalPayoff reward tail source.observer := by
    linarith
  have hpayment : gamma ≤
      quittingAdjacentDeadlineOldOpponentNeverProduct source *
        quittingTerminalPayoff reward tail source.observer :=
    hgain.trans <| mul_le_mul_of_nonneg_left htailReward hopponent
  have hone : 0 ≤ 1 - (source.old source.observer none).toReal := by
    have hmassENN : source.old source.observer none ≤ (1 : ENNReal) :=
      (source.old source.observer).coe_le_one none
    have hmass : (source.old source.observer none).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmassENN
    linarith
  calc
    (1 - (source.old source.observer none).toReal) * gamma ≤
        (1 - (source.old source.observer none).toReal) *
          (quittingAdjacentDeadlineOldOpponentNeverProduct source *
            quittingTerminalPayoff reward tail source.observer) :=
      mul_le_mul_of_nonneg_left hpayment hone
    _ = quittingAdjacentDeadlineOldOpponentNeverProduct source *
        (1 - (source.old source.observer none).toReal) *
        quittingTerminalPayoff reward tail source.observer := by ring

/-- If the old observer has zero `Never` mass, its actual grafted boundary
gain equals the hard boundary gain for every opponent column preserving that
observer marginal. -/
theorem finiteDeadline_zeroNever_boundaryGain_graft_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hzero : source.old source.observer none = 0)
    (mixed : ι → PMF
      (QuittingFiniteDeadlineTimingAction (source.deadline + 1)))
    (hobserver : mixed source.observer =
      quittingAdjacentDeadlineOldIncludedTiming source source.observer) :
    quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1)
            (Function.update mixed source.observer
              (PMF.pure
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
            tail) source.observer -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1) mixed tail) source.observer =
      (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain mixed source.observer
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline) := by
  let boundaryLaw := Function.update mixed source.observer
    (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction source.deadline))
  have hboundary :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) boundaryLaw tail source.observer
  have hbase :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) mixed tail source.observer
  have hboundaryProd :
      (∏ player, (boundaryLaw player none).toReal) = 0 := by
    rw [prod_update_none_toReal]
    simp [quittingFiniteDeadlineTimingBoundaryAction]
  have hobserverNone : (mixed source.observer none).toReal = 0 := by
    rw [hobserver]
    unfold quittingAdjacentDeadlineOldIncludedTiming
    rw [finiteDeadlineTimingProfileInclude_none_toReal source.old source.observer,
      hzero]
    rfl
  have hbaseProd : (∏ player, (mixed player none).toReal) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ source.observer) hobserverNone
  dsimp only [boundaryLaw] at hboundary
  rw [hboundaryProd, zero_mul, add_zero] at hboundary
  rw [hbaseProd, zero_mul, add_zero] at hbase
  rw [hboundary, hbase]
  rfl

/-- If the old observer has zero `Never` mass, every two-column common
boundary-response difference that keeps that observer marginal fixed is
literally unchanged by grafting one common tail. -/
theorem finiteDeadline_zeroNever_responseDifference_graft_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hzero : source.old source.observer none = 0)
    (first second : ι → PMF
      (QuittingFiniteDeadlineTimingAction (source.deadline + 1)))
    (hfirst : first source.observer =
      quittingAdjacentDeadlineOldIncludedTiming source source.observer)
    (hsecond : second source.observer =
      quittingAdjacentDeadlineOldIncludedTiming source source.observer) :
    (quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1)
            (Function.update first source.observer
              (PMF.pure
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
            tail) source.observer -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1) first tail) source.observer) -
      (quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1)
            (Function.update second source.observer
              (PMF.pure
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
            tail) source.observer -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1) second tail) source.observer) =
      (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain first source.observer
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline) -
        (quittingFiniteDeadlineTimingGame reward
          (source.deadline + 1)).mixedGain second source.observer
            (quittingFiniteDeadlineTimingBoundaryAction source.deadline) := by
  rw [finiteDeadline_zeroNever_boundaryGain_graft_eq
      source tail hzero first hfirst,
    finiteDeadline_zeroNever_boundaryGain_graft_eq
      source tail hzero second hsecond]

private theorem finiteDeadline_censoredBoundary_sub_pass_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1)
            (Function.update (quittingAdjacentDeadlineCensoredTiming source) who
              (PMF.pure
                (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
            tail) who -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward
            (source.deadline + 1)
            (Function.update (quittingAdjacentDeadlineCensoredTiming source) who
              (PMF.pure none)) tail) who =
      quittingAdjacentDeadlineCensoredOpponentNeverProduct source who *
        (reward (quittingSingletonTerminal who) who -
          quittingTerminalPayoff reward tail who) := by
  let censored := quittingFiniteDeadlineTimingProfileCensor source.new
  let mixed := quittingFiniteDeadlineTimingProfileInclude censored
  let boundaryLaw := Function.update mixed who
    (PMF.pure (quittingFiniteDeadlineTimingBoundaryAction source.deadline))
  let passLaw := Function.update mixed who (PMF.pure none)
  have hboundary :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) boundaryLaw tail who
  have hpass :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward (source.deadline + 1) passLaw tail who
  have hincludeProd :
      (∏ other ∈ Finset.univ.erase who, (mixed other none).toReal) =
        quittingAdjacentDeadlineCensoredOpponentNeverProduct source who := by
    apply Finset.prod_congr rfl
    intro other _
    exact finiteDeadlineTimingProfileInclude_none_toReal censored other
  have hboundaryProd :
      (∏ player, (boundaryLaw player none).toReal) = 0 := by
    rw [prod_update_none_toReal]
    simp [quittingFiniteDeadlineTimingBoundaryAction]
  have hpassProd : (∏ player, (passLaw player none).toReal) =
      quittingAdjacentDeadlineCensoredOpponentNeverProduct source who := by
    rw [prod_update_none_toReal, hincludeProd]
    simp
  have hhard := finiteDeadline_boundaryEU_sub_neverEU_eq_prod_none_mul_singleton
    reward source.deadline censored who
  dsimp only [boundaryLaw, passLaw] at hboundary hpass
  rw [hboundaryProd, zero_mul, add_zero] at hboundary
  rw [hpassProd] at hpass
  dsimp only [censored, mixed] at hboundary hpass
  let hardBoundary : ℝ :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (Function.update
        (quittingFiniteDeadlineTimingProfileInclude
          (quittingFiniteDeadlineTimingProfileCensor source.new)) who
        (PMF.pure
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline))) who
  let hardPass : ℝ :=
    (quittingFiniteDeadlineTimingGame reward
      (source.deadline + 1)).mixedExtension.eu
      (Function.update
        (quittingFiniteDeadlineTimingProfileInclude
          (quittingFiniteDeadlineTimingProfileCensor source.new)) who
        (PMF.pure none)) who
  let opponent : ℝ := ∏ other ∈ Finset.univ.erase who,
    ((quittingFiniteDeadlineTimingProfileCensor source.new) other none).toReal
  let tailPayoff := quittingTerminalPayoff reward tail who
  let singleton := reward (quittingSingletonTerminal who) who
  change _ = hardBoundary at hboundary
  change _ = hardPass + opponent * tailPayoff at hpass
  dsimp only [censored] at hhard
  change hardBoundary - hardPass = opponent * singleton at hhard
  unfold quittingAdjacentDeadlineCensoredTiming
    quittingAdjacentDeadlineCensoredOpponentNeverProduct
  change _ - _ = opponent * (singleton - tailPayoff)
  rw [hboundary, hpass]
  linear_combination hhard

/-- Restoring one player's successor-boundary mass above the fully censored
law changes that player's actual retained payoff by exactly its boundary mass
times the censored opponent cylinder and singleton-minus-tail payoff. -/
private theorem finiteDeadlineParticipantGraft_sub_censoredGraft_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant =
      (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant *
        (reward (quittingSingletonTerminal participant) participant -
          quittingTerminalPayoff reward tail participant) := by
  let game := quittingRetainedTailFiniteTimingGame reward
    (source.deadline + 1) tail
  let base := quittingAdjacentDeadlineCensoredTiming source
  let law := source.new participant
  let value := fun action => game.mixedExtension.eu
    (Function.update base participant (PMF.pure action)) participant
  let censoredLaw :=
    ((law.map quittingFiniteDeadlineTimingActionCensor).map
      quittingFiniteDeadlineTimingActionInclude)
  have hparticipantEU := game.mixedExtension_eu_update base participant law
  have hcensoredEU := game.mixedExtension_eu_update
    base participant censoredLaw
  have hcensoredLaw : base participant = censoredLaw := by
    rfl
  have hcensoredUpdate :
      Function.update base participant censoredLaw = base := by
    rw [← hcensoredLaw]
    exact Function.update_eq_self participant base
  have hcensoredUpdateEU := congrArg
    (fun mixed => game.mixedExtension.eu mixed participant) hcensoredUpdate
  have hcensoredEU' : game.mixedExtension.eu base participant =
      Math.Probability.expect censoredLaw value :=
    hcensoredUpdateEU.symm.trans hcensoredEU
  have hexpect := expect_sub_expect_censoredLift_eq_boundary_mul law value
  have hpure := finiteDeadline_censoredBoundary_sub_pass_eq
    source tail participant
  have hparticipantPayoff :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
      reward tail (source.deadline + 1)
      (quittingAdjacentDeadlineParticipantTiming source participant)
      participant
  have hcensoredPayoff :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
      reward tail (source.deadline + 1)
      (quittingAdjacentDeadlineCensoredTiming source) participant
  have hboundaryPayoff :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
      reward tail (source.deadline + 1)
      (Function.update (quittingAdjacentDeadlineCensoredTiming source)
        participant
        (PMF.pure
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
      participant
  have hpassPayoff :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_mixedEU
      reward tail (source.deadline + 1)
      (Function.update (quittingAdjacentDeadlineCensoredTiming source)
        participant (PMF.pure none)) participant
  dsimp only [game, base, law, value, censoredLaw]
    at hparticipantEU hcensoredEU' hexpect
  change (quittingRetainedTailFiniteTimingGame reward
      (source.deadline + 1) tail).mixedExtension.eu
      (quittingAdjacentDeadlineParticipantTiming source participant)
      participant = _ at hparticipantEU
  change quittingTerminalPayoff reward
      (quittingAdjacentDeadlineParticipantGraft source tail participant)
      participant = _ at hparticipantPayoff
  change quittingTerminalPayoff reward
      (quittingAdjacentDeadlineCensoredGraft source tail) participant = _
      at hcensoredPayoff
  let participantExpectation := Math.Probability.expect
    (source.new participant) fun action =>
      (quittingRetainedTailFiniteTimingGame reward
        (source.deadline + 1) tail).mixedExtension.eu
        (Function.update (quittingAdjacentDeadlineCensoredTiming source)
          participant (PMF.pure action)) participant
  let censoredExpectation := Math.Probability.expect
    (((source.new participant).map
        quittingFiniteDeadlineTimingActionCensor).map
      quittingFiniteDeadlineTimingActionInclude) fun action =>
      (quittingRetainedTailFiniteTimingGame reward
        (source.deadline + 1) tail).mixedExtension.eu
        (Function.update (quittingAdjacentDeadlineCensoredTiming source)
          participant (PMF.pure action)) participant
  let pureBoundary := (quittingRetainedTailFiniteTimingGame reward
    (source.deadline + 1) tail).mixedExtension.eu
    (Function.update (quittingAdjacentDeadlineCensoredTiming source)
      participant
      (PMF.pure
        (quittingFiniteDeadlineTimingBoundaryAction source.deadline)))
    participant
  let purePass := (quittingRetainedTailFiniteTimingGame reward
    (source.deadline + 1) tail).mixedExtension.eu
    (Function.update (quittingAdjacentDeadlineCensoredTiming source)
      participant (PMF.pure none)) participant
  let boundaryMass := (source.new participant
    (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal
  let opponent := quittingAdjacentDeadlineCensoredOpponentNeverProduct
    source participant
  let singleton := reward (quittingSingletonTerminal participant) participant
  let tailPayoff := quittingTerminalPayoff reward tail participant
  change _ = participantExpectation at hparticipantEU
  change _ = censoredExpectation at hcensoredEU'
  change participantExpectation - censoredExpectation =
    boundaryMass * (pureBoundary - purePass) at hexpect
  change _ = pureBoundary at hboundaryPayoff
  change _ = purePass at hpassPayoff
  have hpureEU : pureBoundary - purePass =
      opponent * (singleton - tailPayoff) := by
    rw [← hboundaryPayoff, ← hpassPayoff]
    exact hpure
  rw [hparticipantPayoff, hcensoredPayoff, hparticipantEU, hcensoredEU']
  rw [hexpect, hpureEU]
  ring

/-- Censoring the selected participant's restored successor marginal is a
literal unilateral update of the complete retained-tail behavior profile. -/
theorem quittingAdjacentDeadlineCensoredGraft_eq_update_participant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) :
    quittingAdjacentDeadlineCensoredGraft source tail =
      Function.update
        (quittingAdjacentDeadlineParticipantGraft source tail participant)
        participant
        (quittingAdjacentDeadlineCensoredGraft source tail participant) := by
  have hforward := quittingRetainedTailMixedTimingProfile_update
    reward (source.deadline + 1)
    (quittingAdjacentDeadlineCensoredTiming source) tail participant
    (source.new participant)
  change quittingAdjacentDeadlineParticipantGraft source tail participant =
    Function.update (quittingAdjacentDeadlineCensoredGraft source tail)
      participant
      (quittingAdjacentDeadlineParticipantGraft source tail participant
        participant) at hforward
  funext player
  by_cases hplayer : player = participant
  · subst player
    rw [Function.update_self]
  · rw [Function.update_of_ne hplayer]
    have hcoordinate := congrFun hforward player
    rw [Function.update_of_ne hplayer] at hcoordinate
    exact hcoordinate.symm

/-- The reverse participant update has exact actual payoff gain equal to the
boundary mass times the censored opponent cylinder and tail singleton gap. -/
theorem finiteDeadlineCensoredGraft_sub_participantGraft_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile) (participant : ι) :
    quittingTerminalPayoff reward
          (quittingAdjacentDeadlineCensoredGraft source tail) participant -
        quittingTerminalPayoff reward
          (quittingAdjacentDeadlineParticipantGraft source tail participant)
          participant =
      (source.new participant
          (quittingFiniteDeadlineTimingBoundaryAction source.deadline)).toReal *
        quittingAdjacentDeadlineCensoredOpponentNeverProduct
          source participant *
        (quittingTerminalPayoff reward tail participant -
          reward (quittingSingletonTerminal participant) participant) := by
  have h := finiteDeadlineParticipantGraft_sub_censoredGraft_eq
    source tail participant
  linarith

end GameTheory
