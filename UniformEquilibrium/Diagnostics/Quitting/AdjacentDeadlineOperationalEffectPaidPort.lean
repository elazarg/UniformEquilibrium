/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.AdjacentDeadlineSelectedBoundaryEffectDispatch
import UniformEquilibrium.Diagnostics.Quitting.AllContinuePrefixSemantics
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailGraftDecomposition
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualReachPaidFirstDisagreement
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapLiftedSummablePort

/-!
# Adjacent-deadline operational effects feed the paid-port waist

The selected large-effect arm of the adjacent-deadline spectator dispatch is
converted into a literal same-tail unilateral update.  The already checked
small-effect arm supplies the same interface.  Positive debt then selects an
actual-support paid row and enters the cap-lifted summable port.

Finite timing `none` always means passage to the displayed behavioral tail;
it is not terminal all-Never.  This module constructs its outputs from the
adjacent source and does not assume a paid update.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A passive finite-timing probe: every opponent passes the whole finite
word, while `mover` uses the displayed timing law, and every `none` outcome
continues with the literal tail. -/
def quittingFiniteDeadlinePassiveNoneProbe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) (mover : ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailMixedTimingProfile reward deadline
    (Function.update (fun _ => PMF.pure none) mover law) tail

/-- Replacing the timing law in a passive probe is literally one complete
behavioral-strategy update. -/
theorem quittingFiniteDeadlinePassiveNoneProbe_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) (mover : ι) :
    quittingFiniteDeadlinePassiveNoneProbe reward deadline second tail mover =
      Function.update
        (quittingFiniteDeadlinePassiveNoneProbe reward deadline first tail mover)
        mover
        (quittingFiniteDeadlinePassiveNoneProbe reward deadline second tail mover mover) := by
  unfold quittingFiniteDeadlinePassiveNoneProbe
  rw [quittingRetainedTailMixedTimingProfile_update reward deadline
      (fun _ => PMF.pure none) tail mover second,
    quittingRetainedTailMixedTimingProfile_update reward deadline
      (fun _ => PMF.pure none) tail mover first]
  simp

/-- With every opponent assigned finite-timing `none`, a hard finite timing
action pays the mover its singleton reward exactly when it is finite. -/
private theorem timingPurePayoff_passiveNone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover : ι) :
    ∀ (deadline : ℕ)
      (action : QuittingFiniteDeadlineTimingAction deadline),
      timingPurePayoff reward deadline
          (Function.update (fun _ : ι => none) mover action) mover =
        if action = none then 0
        else reward (quittingSingletonTerminal mover) mover := by
  intro deadline
  induction deadline with
  | zero =>
      intro action
      have hnone : action = none := by
        cases action with
        | none => rfl
        | some time => exact Fin.elim0 time
      subst action
      exact timingPurePayoff_zero reward _ mover
  | succ deadline ih =>
      intro action
      cases action with
      | none =>
          rw [if_pos rfl]
          have hempty : (quittingQuitters fun player =>
              timingActionCurrent
                ((Function.update
                  (fun _ : ι =>
                    (none : QuittingFiniteDeadlineTimingAction (deadline + 1)))
                  mover none) player)) = ∅ := by
            ext player
            simp [quittingQuitters, timingActionCurrent]
          have hcurrent : ¬(quittingQuitters fun player =>
              timingActionCurrent
                ((Function.update
                  (fun _ : ι =>
                    (none : QuittingFiniteDeadlineTimingAction (deadline + 1)))
                  mover none) player)).Nonempty := by
            rw [hempty]
            exact Finset.not_nonempty_empty
          rw [timingPurePayoff_succ_of_current_empty reward deadline _ mover hcurrent]
          have htail : timingChoicesTail
              (Function.update
                (fun _ : ι =>
                  (none : QuittingFiniteDeadlineTimingAction (deadline + 1)))
                mover none) =
                Function.update
                  (fun _ : ι =>
                    (none : QuittingFiniteDeadlineTimingAction deadline))
                  mover none := by
            funext player
            simp [timingChoicesTail, Function.update_apply, timingActionTail]
          rw [htail, ih none, if_pos rfl]
      | some time =>
          rw [if_neg (Option.some_ne_none time)]
          cases time using Fin.cases with
          | zero =>
              have hcurrent : quittingQuitters (fun player =>
                  timingActionCurrent
                    ((Function.update (fun _ : ι => none) mover
                      (some (0 : Fin (deadline + 1)))) player)) = {mover} := by
                ext player
                by_cases hplayer : player = mover
                · subst player
                  simp [quittingQuitters, timingActionCurrent]
                · simp [quittingQuitters, timingActionCurrent, hplayer]
              have hnonempty : (quittingQuitters fun player =>
                  timingActionCurrent
                    ((Function.update (fun _ : ι => none) mover
                      (some (0 : Fin (deadline + 1)))) player)).Nonempty := by
                rw [hcurrent]
                exact Finset.singleton_nonempty mover
              rw [timingPurePayoff_succ_of_current_nonempty reward deadline _ mover
                hnonempty]
              congr 2
          | succ later =>
              have hempty : quittingQuitters (fun player =>
                  timingActionCurrent
                    ((Function.update (fun _ : ι => none) mover
                      (some later.succ)) player)) = ∅ := by
                ext player
                by_cases hplayer : player = mover
                · subst player
                  simp [quittingQuitters, timingActionCurrent]
                · simp [quittingQuitters, hplayer, timingActionCurrent]
              have hcurrent : ¬(quittingQuitters fun player =>
                  timingActionCurrent
                    ((Function.update (fun _ : ι => none) mover
                      (some later.succ)) player)).Nonempty := by
                rw [hempty]
                exact Finset.not_nonempty_empty
              rw [timingPurePayoff_succ_of_current_empty reward deadline _ mover hcurrent]
              have htail : timingChoicesTail
                  (Function.update (fun _ : ι => none) mover (some later.succ)) =
                    Function.update (fun _ : ι => none) mover (some later) := by
                funext player
                by_cases hplayer : player = mover
                · subst player
                  simp [timingChoicesTail, timingActionTail]
                · simp [timingChoicesTail, Function.update_of_ne hplayer,
                    timingActionTail]
              calc
                timingPurePayoff reward deadline
                    (timingChoicesTail
                      (Function.update (fun _ : ι => none) mover
                        (some later.succ))) mover =
                    timingPurePayoff reward deadline
                      (Function.update (fun _ : ι => none) mover (some later)) mover :=
                  congrArg (fun choices =>
                    timingPurePayoff reward deadline choices mover) htail
                _ = _ := by
                  rw [ih (some later), if_neg (Option.some_ne_none later)]

/-- The hard payoff of a passive timing probe depends only on the law's
finite mass: every finite date stops alone, while timing `none` has hard-tail
payoff zero. -/
private theorem quittingFiniteDeadlineTimingGame_passiveNone_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction deadline)) (mover : ι) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        (Function.update (fun _ => PMF.pure none) mover law) mover =
      (1 - (law none).toReal) *
        reward (quittingSingletonTerminal mover) mover := by
  have hpure : ∀ action : QuittingFiniteDeadlineTimingAction deadline,
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
          (Function.update (fun _ => PMF.pure none) mover (PMF.pure action)) mover =
        timingPurePayoff reward deadline
          (Function.update (fun _ : ι => none) mover action) mover := by
    intro action
    let game := quittingFiniteDeadlineTimingGame reward deadline
    have hprofile :
        Function.update (fun _ : ι => PMF.pure none) mover (PMF.pure action) =
        game.pureMixedProfile
          (Function.update (fun _ : ι => none) mover action) := by
      funext player
      unfold game KernelGame.pureMixedProfile
      by_cases hplayer : player = mover
      · subst player
        simp only [Function.update_self]
        rfl
      · simp only [Function.update_of_ne hplayer]
        rfl
    calc
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
          (Function.update (fun _ => PMF.pure none) mover (PMF.pure action)) mover =
          game.mixedExtension.eu
            (game.pureMixedProfile
              (Function.update (fun _ : ι => none) mover action)) mover := by
            exact congrArg
              (fun profile => game.mixedExtension.eu profile mover) hprofile
      _ = game.eu (Function.update (fun _ : ι => none) mover action) mover :=
        game.mixedExtension_eu_pureMixedProfile _ mover
      _ = timingPurePayoff reward deadline
          (Function.update (fun _ : ι => none) mover action) mover := by
        unfold game quittingFiniteDeadlineTimingGame timingPurePayoff
        exact KernelGame.eu_ofPureEU _ _ _ _
  have htotal := Math.Probability.pmf_toReal_sum_one law
  rw [Fintype.sum_option] at htotal
  have hupdate :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu_update
      (fun _ : ι => PMF.pure none) mover law
  rw [hupdate]
  change Math.Probability.expect law (fun action : Option (Fin deadline) =>
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        (Function.update (fun _ => PMF.pure none) mover (PMF.pure action)) mover) = _
  rw [Math.Probability.expect_eq_sum]
  simp_rw [hpure, timingPurePayoff_passiveNone reward mover]
  rw [Fintype.sum_option]
  simp only [Option.some_ne_none, ↓reduceIte, mul_zero, zero_add]
  rw [← Finset.sum_mul]
  have hfinite : (∑ i, (law (some i)).toReal) = 1 - (law none).toReal := by
    linarith
  rw [hfinite]

/-- Exact retained-tail affine identity for a passive finite-timing probe. -/
theorem quittingFiniteDeadlinePassiveNoneProbe_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) (mover : ι) :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlinePassiveNoneProbe reward deadline law tail mover)
        mover =
      (1 - (law none).toReal) *
          reward (quittingSingletonTerminal mover) mover +
        (law none).toReal * quittingTerminalPayoff reward tail mover := by
  unfold quittingFiniteDeadlinePassiveNoneProbe
  rw [quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul]
  have hproduct :
      (∏ player, ((Function.update (fun _ : ι => PMF.pure none) mover law)
        player none).toReal) = (law none).toReal := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ mover)]
    simp only [Function.update_self]
    have hopponents :
        (∏ other ∈ Finset.univ.erase mover,
          ((Function.update (fun _ : ι => PMF.pure none) mover law)
            other none).toReal) = 1 := by
      apply Finset.prod_eq_one
      intro other hother
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
      simp
    rw [hopponents, mul_one]
  have hhard := quittingFiniteDeadlineTimingGame_passiveNone_mixedEU
    reward deadline law mover
  calc
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
          (Function.update (fun _ => PMF.pure none) mover law) mover +
        (∏ player, ((Function.update (fun _ : ι => PMF.pure none) mover law)
          player none).toReal) * quittingTerminalPayoff reward tail mover =
      (1 - (law none).toReal) *
          reward (quittingSingletonTerminal mover) mover +
        (∏ player, ((Function.update (fun _ : ι => PMF.pure none) mover law)
          player none).toReal) * quittingTerminalPayoff reward tail mover := by
            exact congrArg
              (fun value => value +
                (∏ player,
                  ((Function.update (fun _ : ι => PMF.pure none) mover law)
                    player none).toReal) *
                  quittingTerminalPayoff reward tail mover) hhard
    _ = _ := by rw [hproduct]

/-- Exact signed payoff difference between two passive finite-timing probes.
The sign is the sign of the change in timing-`none` mass times the tail's
strict singleton separation. -/
theorem finiteDeadlinePassiveNoneProbe_payoff_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) (mover : ι) :
    quittingTerminalPayoff reward
          (quittingFiniteDeadlinePassiveNoneProbe reward deadline second tail mover)
          mover -
        quittingTerminalPayoff reward
          (quittingFiniteDeadlinePassiveNoneProbe reward deadline first tail mover)
          mover =
      ((second none).toReal - (first none).toReal) *
        (quittingTerminalPayoff reward tail mover -
          reward (quittingSingletonTerminal mover) mover) := by
  rw [quittingFiniteDeadlinePassiveNoneProbe_payoff,
    quittingFiniteDeadlinePassiveNoneProbe_payoff]
  ring

/-! ## Same-tail paid updates -/

/-- A literal finite-timing own-coordinate update behind one common
behavioral tail, together with a positive prescribed-payoff floor. -/
structure QuittingFiniteDeadlineSameTailPaidUpdate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : (quittingGame reward).BehaviorProfile)
    (floor : ℝ) where
  mover : ι
  sourceTiming : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)
  targetTiming : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)
  targetTiming_eq_update : targetTiming =
    Function.update sourceTiming mover (targetTiming mover)
  payoffGain_ge : floor ≤
    quittingTerminalPayoff reward
        (quittingRetainedTailMixedTimingProfile reward deadline targetTiming tail)
        mover -
      quittingTerminalPayoff reward
        (quittingRetainedTailMixedTimingProfile reward deadline sourceTiming tail)
        mover

namespace QuittingFiniteDeadlineSameTailPaidUpdate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {deadline : ℕ} {tail : (quittingGame reward).BehaviorProfile}
    {floor : ℝ}

/-- The literal source behavioral profile. -/
def sourceProfile
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) : (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailMixedTimingProfile reward deadline
    update.sourceTiming tail

/-- The literal target behavioral profile. -/
def targetProfile
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) : (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailMixedTimingProfile reward deadline
    update.targetTiming tail

/-- The target is literally one complete own-strategy replacement of the
source. -/
theorem targetProfile_eq_update
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) :
    update.targetProfile = Function.update update.sourceProfile update.mover
      (update.targetProfile update.mover) := by
  unfold sourceProfile targetProfile
  rw [update.targetTiming_eq_update]
  exact quittingRetainedTailMixedTimingProfile_update reward deadline
    update.sourceTiming tail update.mover (update.targetTiming update.mover)

/-- The stored floor is the literal mover payoff gain. -/
theorem floor_le_payoffGain
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) :
    floor ≤ quittingTerminalPayoff reward update.targetProfile update.mover -
      quittingTerminalPayoff reward update.sourceProfile update.mover :=
  update.payoffGain_ge

/-- A same-tail own update leaves the mover's unrestricted behavioral cap
exactly fixed. -/
theorem bestResponseValue_eq
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) :
    quittingContinuationBestResponseValue reward update.targetProfile update.mover =
      quittingContinuationBestResponseValue reward update.sourceProfile update.mover := by
  rw [update.targetProfile_eq_update,
    quittingContinuationBestResponseValue_update_self]

/-- The mover's terminal debt decreases by exactly the prescribed-payoff
gain; this is derived from the constructed own update, not assumed. -/
theorem semanticDebt_eq_sub_payoffGain
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward update.targetProfile) update.mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward update.sourceProfile) update.mover -
        (quittingTerminalPayoff reward update.targetProfile update.mover -
          quittingTerminalPayoff reward update.sourceProfile update.mover) := by
  rw [update.targetProfile_eq_update]
  exact quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward update.sourceProfile update.mover (update.targetProfile update.mover)

/-- Lowering the certified floor preserves the literal update and all exact
semantic projections. -/
def weaken
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) {smaller : ℝ} (hsmaller : smaller ≤ floor) :
    QuittingFiniteDeadlineSameTailPaidUpdate reward deadline tail smaller where
  mover := update.mover
  sourceTiming := update.sourceTiming
  targetTiming := update.targetTiming
  targetTiming_eq_update := update.targetTiming_eq_update
  payoffGain_ge := hsmaller.trans update.payoffGain_ge

end QuittingFiniteDeadlineSameTailPaidUpdate

/-- An absolute payoff separation between two one-coordinate timing laws can
always be oriented as a paid same-tail update.  Both signs are retained. -/
theorem exists_sameTailPaidUpdate_of_abs_payoff_sub_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) (mover : ι) (floor : ℝ)
    (hsecond : second = Function.update first mover (second mover))
    (hfloor : floor ≤
      |quittingTerminalPayoff reward
            (quittingRetainedTailMixedTimingProfile reward deadline second tail) mover -
        quittingTerminalPayoff reward
            (quittingRetainedTailMixedTimingProfile reward deadline first tail) mover|) :
    ∃ update : QuittingFiniteDeadlineSameTailPaidUpdate
        reward deadline tail floor,
      (update.sourceTiming = first ∧ update.targetTiming = second) ∨
        (update.sourceTiming = second ∧ update.targetTiming = first) := by
  let difference :=
    quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward deadline second tail) mover -
      quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward deadline first tail) mover
  by_cases hnonneg : 0 ≤ difference
  · let update : QuittingFiniteDeadlineSameTailPaidUpdate
        reward deadline tail floor := {
      mover := mover
      sourceTiming := first
      targetTiming := second
      targetTiming_eq_update := hsecond
      payoffGain_ge := by
        change floor ≤ difference
        rw [← abs_of_nonneg hnonneg]
        exact hfloor }
    exact ⟨update, Or.inl ⟨rfl, rfl⟩⟩
  · have hfirst : first = Function.update second mover (first mover) := by
      funext player
      by_cases hplayer : player = mover
      · subst player
        simp
      · rw [Function.update_of_ne hplayer]
        have hcoordinate := congrFun hsecond player
        rw [Function.update_of_ne hplayer] at hcoordinate
        exact hcoordinate.symm
    let update : QuittingFiniteDeadlineSameTailPaidUpdate
        reward deadline tail floor := {
      mover := mover
      sourceTiming := second
      targetTiming := first
      targetTiming_eq_update := hfirst
      payoffGain_ge := by
        have hreverse :
            quittingTerminalPayoff reward
                  (quittingRetainedTailMixedTimingProfile reward deadline first tail) mover -
                quittingTerminalPayoff reward
                  (quittingRetainedTailMixedTimingProfile reward deadline second tail) mover =
              -difference := by
          dsimp only [difference]
          ring
        rw [hreverse, ← abs_of_nonpos (le_of_not_ge hnonneg)]
        exact hfloor }
    exact ⟨update, Or.inr ⟨rfl, rfl⟩⟩

/-- Exact seam identity for forcing one finite timing date behind a retained
tail.  The finite response absorbs before the tail; only the base profile's
joint timing-`none` cylinder receives the tail correction. -/
theorem finiteDeadlineRetainedTailPureDateGain_eq_hardGain_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) (mover : ι)
    (date : Fin deadline) :
    quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward deadline
            (Function.update mixed mover (PMF.pure (some date))) tail) mover -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward deadline mixed tail) mover =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
          mixed mover (some date) -
        (∏ player, (mixed player none).toReal) *
          quittingTerminalPayoff reward tail mover := by
  have htarget :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward deadline (Function.update mixed mover (PMF.pure (some date))) tail mover
  have hsource :=
    quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul
      reward deadline mixed tail mover
  have htargetProduct :
      (∏ player,
        ((Function.update mixed mover (PMF.pure (some date))) player none).toReal) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ mover)
    simp
  rw [htargetProduct, zero_mul, add_zero] at htarget
  unfold KernelGame.mixedGain
  rw [htarget, hsource]
  simp only [sub_eq_add_neg]
  rw [neg_add_rev]
  ac_rfl

/-! ## Consuming a large selected effect in four players -/

/-- A large Fin4 selected-effect gauge yields either a large timing-`none`
coordinate, or uniform smallness of those coordinates together with a large
hard boundary-gain discrepancy. -/
theorem finFourAdjacentLargeSelectedEffect_none_or_boundaryGain
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hgamma : 0 < gamma) (hbound : 0 < bound)
    (hlarge : gamma / bound / 8 ≤
      quittingAdjacentDeadlineSelectedBoundaryEffectGauge source) :
    (∃ mover,
      gamma / (16 * bound) ≤
        |(quittingAdjacentDeadlineOldIncludedTiming source mover none).toReal -
          (quittingAdjacentDeadlineCensoredTiming source mover none).toReal|) ∨
      ((∀ mover,
        |(quittingAdjacentDeadlineOldIncludedTiming source mover none).toReal -
          (quittingAdjacentDeadlineCensoredTiming source mover none).toReal| <
            gamma / (16 * bound)) ∧
        gamma / 2 ≤
          |quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source|) := by
  let coordinate : Fin 4 → ℝ := fun mover =>
    (source.old mover none).toReal -
      ((quittingFiniteDeadlineTimingProfileCensor source.new) mover none).toReal
  by_cases hcoordinate : ∃ mover, gamma / (16 * bound) ≤ |coordinate mover|
  · left
    obtain ⟨mover, hmover⟩ := hcoordinate
    refine ⟨mover, ?_⟩
    unfold coordinate at hmover
    unfold quittingAdjacentDeadlineOldIncludedTiming
      quittingAdjacentDeadlineCensoredTiming
    rw [finiteDeadlineTimingProfileInclude_none_toReal source.old mover,
      finiteDeadlineTimingProfileInclude_none_toReal
        (quittingFiniteDeadlineTimingProfileCensor source.new) mover]
    exact hmover
  · right
    push Not at hcoordinate
    have hcoordinateMax : finiteAbsoluteMaximum coordinate < gamma / bound / 8 := by
      unfold finiteAbsoluteMaximum
      apply (Finset.max'_lt_iff _ _).2
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with ⟨mover, -, rfl⟩
      have hsmall := hcoordinate mover
      have hratioPos : 0 < gamma / bound := div_pos hgamma hbound
      have heq : gamma / (16 * bound) = gamma / bound / 16 := by
        field_simp
      rw [heq] at hsmall
      linarith
    have hnormalized : gamma / bound / 8 ≤
        |quittingAdjacentDeadlineOldBoundaryGain source -
          quittingAdjacentDeadlineCensoredBoundaryGain source| / (4 * bound) := by
      unfold quittingAdjacentDeadlineSelectedBoundaryEffectGauge at hlarge
      rcases (le_max_iff.mp hlarge) with hnever | hgain
      · change gamma / bound / 8 ≤ finiteAbsoluteMaximum coordinate at hnever
        exact False.elim ((not_le_of_gt hcoordinateMax) hnever)
      · exact hgain
    have hdenom : 0 < 4 * bound := mul_pos (by norm_num) hbound
    have hmul := mul_le_mul_of_nonneg_right hnormalized hdenom.le
    have hleft : (gamma / bound / 8) * (4 * bound) = gamma / 2 := by
      field_simp
      ring
    have hright :
        (|quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source| / (4 * bound)) *
            (4 * bound) =
          |quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source| := by
      exact div_mul_cancel₀ _ hdenom.ne'
    refine ⟨?_, ?_⟩
    · intro mover
      unfold coordinate at hcoordinate
      simpa only [quittingAdjacentDeadlineOldIncludedTiming,
        quittingAdjacentDeadlineCensoredTiming,
        finiteDeadlineTimingProfileInclude_none_toReal] using hcoordinate mover
    · rwa [hleft, hright] at hmul

/-- The joint timing-`none` seam is one-Lipschitz in the four coordinate
`none` probabilities. -/
theorem finFourAdjacentJointNone_abs_sub_le_sum
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound) :
    |(∏ player,
          (quittingAdjacentDeadlineOldIncludedTiming source player none).toReal) -
        (∏ player,
          (quittingAdjacentDeadlineCensoredTiming source player none).toReal)| ≤
      ∑ player,
        |(quittingAdjacentDeadlineOldIncludedTiming source player none).toReal -
          (quittingAdjacentDeadlineCensoredTiming source player none).toReal| := by
  let first : Fin 4 → ℝ := fun player =>
    (quittingAdjacentDeadlineOldIncludedTiming source player none).toReal
  let second : Fin 4 → ℝ := fun player =>
    (quittingAdjacentDeadlineCensoredTiming source player none).toReal
  have hboundProduct := Math.abs_prod_sub_prod_le_sum_abs
    (Finset.univ : Finset (Fin 4)) first second
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun player _ => ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (quittingAdjacentDeadlineOldIncludedTiming source player) none))
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun player _ => ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (quittingAdjacentDeadlineCensoredTiming source player) none))
  simpa only [first, second, Finset.mem_univ, Finset.prod_const] using hboundProduct

/-- If all four timing-`none` coordinates move by less than
`gamma/(16*bound)`, then the joint tail cylinders move by less than
`gamma/(4*bound)`. -/
theorem finFourAdjacentJointNone_abs_sub_lt
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (hcoordinate : ∀ player,
      |(quittingAdjacentDeadlineOldIncludedTiming source player none).toReal -
        (quittingAdjacentDeadlineCensoredTiming source player none).toReal| <
          gamma / (16 * bound)) :
    |(∏ player,
          (quittingAdjacentDeadlineOldIncludedTiming source player none).toReal) -
        (∏ player,
          (quittingAdjacentDeadlineCensoredTiming source player none).toReal)| <
      gamma / (4 * bound) := by
  have hseam := finFourAdjacentJointNone_abs_sub_le_sum source
  have hsum : (∑ player : Fin 4,
      |(quittingAdjacentDeadlineOldIncludedTiming source player none).toReal -
        (quittingAdjacentDeadlineCensoredTiming source player none).toReal|) <
      4 * (gamma / (16 * bound)) := by
    rw [Fin.sum_univ_four]
    linarith [hcoordinate 0, hcoordinate 1, hcoordinate 2, hcoordinate 3]
  have heq : 4 * (gamma / (16 * bound)) = gamma / (4 * bound) := by ring
  rw [← heq]
  exact hseam.trans_lt hsum

/-! ## Quantitative large-selected-effect conversion -/

/-- The payment floor obtained from a large selected effect. -/
def finFourAdjacentLargeSelectedEffectPaidFloor
    (gamma bound delta : ℝ) : ℝ :=
  min (delta * gamma / (32 * bound)) (gamma / 8)

/-- The common floor after merging the large-effect and reverse-participant
branches. -/
def finFourAdjacentSpectatorPaidFloor
    (gamma bound delta : ℝ) : ℝ :=
  min (27 * delta * (gamma / bound) ^ 4 / 4096)
    (finFourAdjacentLargeSelectedEffectPaidFloor gamma bound delta)

theorem finFourAdjacentLargeSelectedEffectPaidFloor_pos
    {gamma bound delta : ℝ}
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta) :
    0 < finFourAdjacentLargeSelectedEffectPaidFloor gamma bound delta := by
  unfold finFourAdjacentLargeSelectedEffectPaidFloor
  exact lt_min
    (div_pos (mul_pos hdelta hgamma) (mul_pos (by norm_num) hbound))
    (div_pos hgamma (by norm_num))

theorem finFourAdjacentSpectatorPaidFloor_pos
    {gamma bound delta : ℝ}
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta) :
    0 < finFourAdjacentSpectatorPaidFloor gamma bound delta := by
  unfold finFourAdjacentSpectatorPaidFloor
  apply lt_min
  · positivity
  · exact finFourAdjacentLargeSelectedEffectPaidFloor_pos hgamma hbound hdelta

/-- A macroscopic selected-effect gauge constructs a literal same-tail paid
update.  A large timing-`none` coefficient uses a passive probe; otherwise
the hard boundary response survives the exact retained-tail seam. -/
theorem finFourAdjacentLargeSelectedEffect_exists_sameTailPaidUpdate
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player)
    (hlarge : gamma / bound / 8 ≤
      quittingAdjacentDeadlineSelectedBoundaryEffectGauge source) :
    Nonempty (QuittingFiniteDeadlineSameTailPaidUpdate reward
      (source.deadline + 1) tail
      (finFourAdjacentLargeSelectedEffectPaidFloor gamma bound delta)) := by
  rcases finFourAdjacentLargeSelectedEffect_none_or_boundaryGain
      source hgamma hbound hlarge with
    ⟨mover, hcoefficient⟩ | ⟨hcoordinates, hboundary⟩
  · let firstTiming : Fin 4 →
        PMF (QuittingFiniteDeadlineTimingAction (source.deadline + 1)) :=
      Function.update (fun _ => PMF.pure none) mover
        (quittingAdjacentDeadlineOldIncludedTiming source mover)
    let secondTiming : Fin 4 →
        PMF (QuittingFiniteDeadlineTimingAction (source.deadline + 1)) :=
      Function.update (fun _ => PMF.pure none) mover
        (quittingAdjacentDeadlineCensoredTiming source mover)
    have htimingUpdate : secondTiming =
        Function.update firstTiming mover (secondTiming mover) := by
      simp [firstTiming, secondTiming]
    have hidentity := finiteDeadlinePassiveNoneProbe_payoff_sub reward
      (source.deadline + 1)
      (quittingAdjacentDeadlineOldIncludedTiming source mover)
      (quittingAdjacentDeadlineCensoredTiming source mover) tail mover
    change quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
            secondTiming tail) mover -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
            firstTiming tail) mover = _ at hidentity
    have hgapNonneg : 0 ≤ quittingTerminalPayoff reward tail mover -
        reward (quittingSingletonTerminal mover) mover :=
      (div_pos hdelta (by norm_num)).le.trans (htail mover)
    have hcoefficient' : gamma / (16 * bound) ≤
        |(quittingAdjacentDeadlineCensoredTiming source mover none).toReal -
          (quittingAdjacentDeadlineOldIncludedTiming source mover none).toReal| := by
      simpa [abs_sub_comm] using hcoefficient
    have hproduct : delta * gamma / (32 * bound) ≤
        |((quittingAdjacentDeadlineCensoredTiming source mover none).toReal -
            (quittingAdjacentDeadlineOldIncludedTiming source mover none).toReal) *
          (quittingTerminalPayoff reward tail mover -
            reward (quittingSingletonTerminal mover) mover)| := by
      rw [abs_mul, abs_of_nonneg hgapNonneg]
      calc
        delta * gamma / (32 * bound) =
            (gamma / (16 * bound)) * (delta / 2) := by
              field_simp
              ring
        _ ≤ _ := mul_le_mul hcoefficient' (htail mover)
          (div_nonneg hdelta.le (by norm_num)) (abs_nonneg _)
    have hpayoff : finFourAdjacentLargeSelectedEffectPaidFloor
          gamma bound delta ≤
        |quittingTerminalPayoff reward
              (quittingRetainedTailMixedTimingProfile reward
                (source.deadline + 1) secondTiming tail) mover -
          quittingTerminalPayoff reward
              (quittingRetainedTailMixedTimingProfile reward
                (source.deadline + 1) firstTiming tail) mover| := by
      rw [hidentity]
      exact (min_le_left _ _).trans hproduct
    obtain ⟨update, -⟩ := exists_sameTailPaidUpdate_of_abs_payoff_sub_ge
      reward (source.deadline + 1) firstTiming secondTiming tail mover
        (finFourAdjacentLargeSelectedEffectPaidFloor gamma bound delta)
        htimingUpdate hpayoff
    exact ⟨update⟩
  · let oldTiming := quittingAdjacentDeadlineOldIncludedTiming source
    let censoredTiming := quittingAdjacentDeadlineCensoredTiming source
    let boundaryDate : Fin (source.deadline + 1) :=
      ⟨source.deadline, Nat.lt_succ_self source.deadline⟩
    let boundary : QuittingFiniteDeadlineTimingAction (source.deadline + 1) :=
      some boundaryDate
    let oldJoint := ∏ player, (oldTiming player none).toReal
    let censoredJoint := ∏ player, (censoredTiming player none).toReal
    let tailPayoff := quittingTerminalPayoff reward tail source.observer
    let oldTailGain := quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
            (Function.update oldTiming source.observer (PMF.pure boundary)) tail)
          source.observer -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
            oldTiming tail) source.observer
    let censoredTailGain := quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
            (Function.update censoredTiming source.observer (PMF.pure boundary)) tail)
          source.observer -
        quittingTerminalPayoff reward
          (quittingRetainedTailMixedTimingProfile reward (source.deadline + 1)
            censoredTiming tail) source.observer
    have holdIdentity : oldTailGain =
        quittingAdjacentDeadlineOldBoundaryGain source - oldJoint * tailPayoff := by
      simpa [oldTailGain, oldTiming, oldJoint, tailPayoff, boundary, boundaryDate,
        quittingFiniteDeadlineTimingBoundaryAction,
        quittingAdjacentDeadlineOldBoundaryGain] using
        (finiteDeadlineRetainedTailPureDateGain_eq_hardGain_sub reward
          (source.deadline + 1) oldTiming tail source.observer boundaryDate)
    have hcensoredIdentity : censoredTailGain =
        quittingAdjacentDeadlineCensoredBoundaryGain source -
          censoredJoint * tailPayoff := by
      simpa [censoredTailGain, censoredTiming, censoredJoint, tailPayoff,
        boundary, boundaryDate,
        quittingFiniteDeadlineTimingBoundaryAction,
        quittingAdjacentDeadlineCensoredBoundaryGain] using
        (finiteDeadlineRetainedTailPureDateGain_eq_hardGain_sub reward
          (source.deadline + 1) censoredTiming tail source.observer boundaryDate)
    have hjoint := finFourAdjacentJointNone_abs_sub_lt source hcoordinates
    change |oldJoint - censoredJoint| < gamma / (4 * bound) at hjoint
    have htailBound : |tailPayoff| ≤ bound := by
      exact abs_quittingTerminalPayoff_le reward tail source.observer hreward
    have hcorrection : |(oldJoint - censoredJoint) * tailPayoff| < gamma / 4 := by
      rw [abs_mul]
      calc
        |oldJoint - censoredJoint| * |tailPayoff| ≤
            |oldJoint - censoredJoint| * bound :=
          mul_le_mul_of_nonneg_left htailBound (abs_nonneg _)
        _ < (gamma / (4 * bound)) * bound :=
          mul_lt_mul_of_pos_right hjoint hbound
        _ = gamma / 4 := by field_simp
    have hhardLe :
        |quittingAdjacentDeadlineOldBoundaryGain source -
            quittingAdjacentDeadlineCensoredBoundaryGain source| ≤
          |oldTailGain - censoredTailGain| +
            |(oldJoint - censoredJoint) * tailPayoff| := by
      have hdecomposition :
          quittingAdjacentDeadlineOldBoundaryGain source -
              quittingAdjacentDeadlineCensoredBoundaryGain source =
            (oldTailGain - censoredTailGain) +
              (oldJoint - censoredJoint) * tailPayoff := by
        rw [holdIdentity, hcensoredIdentity]
        ring
      rw [hdecomposition]
      exact abs_add_le _ _
    have htailDifference : gamma / 4 <
        |oldTailGain - censoredTailGain| := by
      linarith
    have hresponse : gamma / 8 < |oldTailGain| ∨
        gamma / 8 < |censoredTailGain| := by
      by_contra hnone
      push Not at hnone
      have htriangle := abs_sub oldTailGain censoredTailGain
      linarith
    rcases hresponse with hold | hcensored
    · obtain ⟨update, -⟩ := exists_sameTailPaidUpdate_of_abs_payoff_sub_ge
        reward (source.deadline + 1) oldTiming
          (Function.update oldTiming source.observer (PMF.pure boundary)) tail
          source.observer
          (finFourAdjacentLargeSelectedEffectPaidFloor gamma bound delta)
          (by simp) ((min_le_right _ _).trans hold.le)
      exact ⟨update⟩
    · obtain ⟨update, -⟩ := exists_sameTailPaidUpdate_of_abs_payoff_sub_ge
        reward (source.deadline + 1) censoredTiming
          (Function.update censoredTiming source.observer (PMF.pure boundary)) tail
          source.observer
          (finFourAdjacentLargeSelectedEffectPaidFloor gamma bound delta)
          (by simp) ((min_le_right _ _).trans hcensored.le)
      exact ⟨update⟩

/-- The full adjacent spectator dispatch now has a single literal same-tail
paid-update output.  The previously unconsumed selected-large arm and the
checked reverse-participant arm are merged at their common explicit floor. -/
theorem finFourAdjacentSpectator_exists_sameTailPaidUpdate
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player) :
    Nonempty (QuittingFiniteDeadlineSameTailPaidUpdate reward
      (source.deadline + 1) tail
      (finFourAdjacentSpectatorPaidFloor gamma bound delta)) := by
  rcases
      quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant_finFour
        source tail hgamma hbound hdelta hscale hreward hpass htail with
    hlarge | ⟨participant, edge, hpaid⟩
  · obtain ⟨update⟩ :=
      finFourAdjacentLargeSelectedEffect_exists_sameTailPaidUpdate
        source tail hgamma hbound hdelta hreward htail hlarge
    exact ⟨update.weaken (min_le_right _ _)⟩
  · let update : QuittingFiniteDeadlineSameTailPaidUpdate reward
        (source.deadline + 1) tail
        (finFourAdjacentSpectatorPaidFloor gamma bound delta) := {
      mover := participant
      sourceTiming := quittingAdjacentDeadlineParticipantTiming source participant
      targetTiming := quittingAdjacentDeadlineCensoredTiming source
      targetTiming_eq_update := by
        funext player
        by_cases hplayer : player = participant
        · subst player
          simp
        · simp [quittingAdjacentDeadlineParticipantTiming,
            Function.update_of_ne hplayer]
      payoffGain_ge := by
        exact (min_le_left _ _).trans hpaid }
    exact ⟨update⟩

/-! ## Literal ancestry and actual-support passport -/

/-- Four explicit unilateral replacements carry any Fin4 behavioral profile
to any other one.  This records the finite ancestry used by the adjacent
construction rather than leaving it implicit in the player cardinality. -/
structure FinFourBehaviorReplacementAncestry
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (base target : (quittingGame reward).BehaviorProfile) where
  afterZero : (quittingGame reward).BehaviorProfile
  afterOne : (quittingGame reward).BehaviorProfile
  afterTwo : (quittingGame reward).BehaviorProfile
  afterZero_eq : afterZero = Function.update base 0 (target 0)
  afterOne_eq : afterOne = Function.update afterZero 1 (target 1)
  afterTwo_eq : afterTwo = Function.update afterOne 2 (target 2)
  target_eq : target = Function.update afterTwo 3 (target 3)

theorem nonempty_finFourBehaviorReplacementAncestry
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (base target : (quittingGame reward).BehaviorProfile) :
    Nonempty (FinFourBehaviorReplacementAncestry base target) := by
  let afterZero := Function.update base (0 : Fin 4) (target 0)
  let afterOne := Function.update afterZero (1 : Fin 4) (target 1)
  let afterTwo := Function.update afterOne (2 : Fin 4) (target 2)
  have htarget : target = Function.update afterTwo (3 : Fin 4) (target 3) := by
    funext player
    fin_cases player <;> simp [afterZero, afterOne, afterTwo]
  exact ⟨{
    afterZero := afterZero
    afterOne := afterOne
    afterTwo := afterTwo
    afterZero_eq := rfl
    afterOne_eq := rfl
    afterTwo_eq := rfl
    target_eq := htarget }⟩

/-- The same-tail source has a literal four-replacement ancestry from the
finite all-Continue prefix of its tail.  Under singleton-cap domination that
prefix realizes exactly the tail's terminal semantic pair. -/
theorem QuittingFiniteDeadlineSameTailPaidUpdate.exists_allContinuePrefixAncestry
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {deadline : ℕ} {tail : (quittingGame reward).BehaviorProfile}
    {floor : ℝ}
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor)
    (hsolo : ∀ player, reward (quittingSingletonTerminal player) player ≤
      quittingContinuationBestResponseValue reward tail player) :
    ∃ base : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward base =
          quittingTerminalSemanticPair reward tail ∧
        Nonempty (FinFourBehaviorReplacementAncestry base update.sourceProfile) := by
  let base := quittingAllContinuePrefixIterate reward tail deadline
  refine ⟨base, ?_, nonempty_finFourBehaviorReplacementAncestry _ _⟩
  exact quittingTerminalSemanticPair_allContinuePrefixIterate_eq
    reward tail hsolo deadline

/-- A paid same-tail update decoded to an actual stopping-law support row,
with the three packet reach floors stated literally. -/
structure QuittingSameTailActualReachPaidUpdatePassport
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {deadline : ℕ} {tail : (quittingGame reward).BehaviorProfile}
    {floor bound : ℝ}
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor) where
  floor_pos : 0 < floor
  bound_pos : 0 < bound
  row : QuittingPaidFirstDisagreementRow reward update.sourceProfile
    update.mover (floor / 4)
  sourceWitness_mem_support : row.sourceWitness ∈
    (quittingBehaviorStoppingLaw reward
      (update.sourceProfile update.mover)).support
  ownReach_ge : floor / (4 * bound) ≤
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward
        (update.sourceProfile update.mover)) row.start
  opponentReach_ge : floor / (8 * bound) ≤ row.liveMass
  jointReach_ge : floor ^ 2 / (32 * bound ^ 2) ≤
    quittingSurvivalPrefix
      (quittingProfileLiveRoot reward update.sourceProfile) row.start

namespace QuittingSameTailActualReachPaidUpdatePassport

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {deadline : ℕ} {tail : (quittingGame reward).BehaviorProfile}
    {floor bound : ℝ}
    {update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor}

/-- The passport and a global positive minimum form the existing cap-lifted
source without any additional paid-update hypothesis. -/
def capLiftedSource
    (passport : QuittingSameTailActualReachPaidUpdatePassport
      (bound := bound) update)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    QuittingPaidCapLiftedSource reward where
  minimum := minimum
  minimum_le := hminimum
  minimum_pos := hminimumPos
  profile := update.sourceProfile
  observer := update.mover
  gain := floor / 4
  gain_pos := div_pos passport.floor_pos (by norm_num)
  row := passport.row

end QuittingSameTailActualReachPaidUpdatePassport

/-- Positive payoff of the constructed unilateral update supplies the debt
needed by the actual-support first-disagreement decoder. -/
theorem QuittingFiniteDeadlineSameTailPaidUpdate.nonempty_actualReachPassport
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {deadline : ℕ} {tail : (quittingGame reward).BehaviorProfile}
    {floor bound : ℝ}
    (update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor)
    (hfloor : 0 < floor) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    Nonempty (QuittingSameTailActualReachPaidUpdatePassport
      (bound := bound) update) := by
  have htargetLe : quittingTerminalPayoff reward update.targetProfile update.mover ≤
      quittingContinuationBestResponseValue reward update.sourceProfile update.mover := by
    rw [update.targetProfile_eq_update]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward update.sourceProfile update.mover (update.targetProfile update.mover)
  have hdebt : floor ≤
      quittingContinuationBestResponseValue reward update.sourceProfile update.mover -
        quittingTerminalPayoff reward update.sourceProfile update.mover := by
    linarith [update.floor_le_payoffGain]
  obtain ⟨row, hsupport, hown, hopponent, hjoint⟩ :=
    positiveDebt_exists_actualJointReach_paidRow_mem_support reward
      update.sourceProfile update.mover bound floor hreward hfloor hdebt
  have hown' : floor / (4 * bound) ≤
      quittingHazardSurvival
        (quittingBehaviorLiveHazard reward
          (update.sourceProfile update.mover)) row.start := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hbound)).2
    simpa [mul_comm] using hown
  have hopponent' : floor / (8 * bound) ≤ row.liveMass := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hbound)).2
    simpa [mul_comm] using hopponent
  have hjoint' : floor ^ 2 / (32 * bound ^ 2) ≤
      quittingSurvivalPrefix
        (quittingProfileLiveRoot reward update.sourceProfile) row.start := by
    have hdenom : 0 < 32 * bound ^ 2 := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith
  exact ⟨{
    floor_pos := hfloor
    bound_pos := hbound
    row := row
    sourceWitness_mem_support := hsupport
    ownReach_ge := hown'
    opponentReach_ge := hopponent'
    jointReach_ge := hjoint' }⟩

/-- Every actual Fin4 terminal-semantic debt sum is at most `8 * bound` for
a reward table bounded by `bound`. -/
theorem finFour_terminalSemanticDebtSum_le_eight_mul_bound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤ 8 * bound := by
  unfold quittingTerminalSemanticDebtSum
  calc
    (∑ player, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) player) ≤
        ∑ _player : Fin 4, 2 * bound := by
      apply Finset.sum_le_sum
      intro player _
      simpa [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
        quittingTerminalDeviationDebt] using
        (quittingTerminalDeviationDebt_le_two_mul_bound
          reward profile player bound hreward)
    _ = 8 * bound := by
      norm_num [Finset.sum_const]
      ring

/-! ## Final cap-lifted summable port -/

namespace QuittingSameTailActualReachPaidUpdatePassport

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {deadline : ℕ} {tail : (quittingGame reward).BehaviorProfile}
    {floor bound : ℝ}
    {update : QuittingFiniteDeadlineSameTailPaidUpdate
      reward deadline tail floor}

/-- The packet's explicit `D_* / (8M)` suffix-reach floor. -/
theorem minimumDebt_div_eightBound_le_capLiftedReachFloor
    (passport : QuittingSameTailActualReachPaidUpdatePassport
      (bound := bound) update)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalSemanticDebtSum minimum / (8 * bound) ≤
      (passport.capLiftedSource minimum hminimum hminimumPos).reachFloor := by
  let capSource := passport.capLiftedSource minimum hminimum hminimumPos
  have hinitial : capSource.initialDebt ≤ 8 * bound :=
    finFour_terminalSemanticDebtSum_le_eight_mul_bound
      reward update.sourceProfile bound hreward
  have hdenom : 0 < 8 * bound := mul_pos (by norm_num) passport.bound_pos
  have hinitialPos : 0 < capSource.initialDebt := capSource.initialDebt_pos
  unfold QuittingPaidCapLiftedSource.reachFloor
  rw [div_le_div_iff₀ hdenom hinitialPos]
  exact mul_le_mul_of_nonneg_left hinitial hminimumPos.le

/-- Every shifted paid row retains the literal gain
`D_* * floor / (32M)`. -/
theorem minimumDebt_mul_floor_div_thirtyTwoBound_le_shiftedGain
    (passport : QuittingSameTailActualReachPaidUpdatePassport
      (bound := bound) update)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (horizon : ℕ) :
    quittingTerminalSemanticDebtSum minimum * floor / (32 * bound) ≤
      quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward update.sourceProfile horizon)
          update.mover
          (quittingCapLiftPureTimeShift horizon passport.row.receivingWitness) -
        quittingPureTimeDeviationPayoff reward
          (quittingCapLiftedPrefixProfile reward update.sourceProfile horizon)
          update.mover
          (quittingCapLiftPureTimeShift horizon passport.row.sourceWitness) := by
  let capSource := passport.capLiftedSource minimum hminimum hminimumPos
  have hreach := passport.minimumDebt_div_eightBound_le_capLiftedReachFloor
    minimum hminimum hminimumPos hreward
  have hscaled : quittingTerminalSemanticDebtSum minimum * floor / (32 * bound) ≤
      capSource.reachFloor * capSource.gain := by
    change _ ≤ capSource.reachFloor * (floor / 4)
    calc
      quittingTerminalSemanticDebtSum minimum * floor / (32 * bound) =
          (quittingTerminalSemanticDebtSum minimum / (8 * bound)) *
            (floor / 4) := by
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hreach
        (div_nonneg passport.floor_pos.le (by norm_num))
  exact hscaled.trans (capSource.shifted_gain_le horizon)

end QuittingSameTailActualReachPaidUpdatePassport

/-- Every adjacent spectator source satisfying the packet hypotheses enters
the existing cap-lifted summable paid port, with no supplied paid update. -/
theorem finFourAdjacentSpectator_nonempty_capLiftedSummablePort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ update : QuittingFiniteDeadlineSameTailPaidUpdate reward
        (source.deadline + 1) tail
        (finFourAdjacentSpectatorPaidFloor gamma bound delta),
      ∃ passport : QuittingSameTailActualReachPaidUpdatePassport
          (bound := bound) update,
        Nonempty (QuittingPaidCapLiftedSource.SummablePort
            (passport.capLiftedSource minimum hminimum hminimumPos)) ∧
          quittingTerminalSemanticDebtSum minimum / (8 * bound) ≤
            (passport.capLiftedSource minimum hminimum hminimumPos).reachFloor ∧
          ∀ horizon,
            quittingTerminalSemanticDebtSum minimum *
                  finFourAdjacentSpectatorPaidFloor gamma bound delta /
                    (32 * bound) ≤
              quittingPureTimeDeviationPayoff reward
                  (quittingCapLiftedPrefixProfile reward
                    update.sourceProfile horizon)
                  update.mover
                  (quittingCapLiftPureTimeShift horizon
                    passport.row.receivingWitness) -
                quittingPureTimeDeviationPayoff reward
                  (quittingCapLiftedPrefixProfile reward
                    update.sourceProfile horizon)
                  update.mover
                  (quittingCapLiftPureTimeShift horizon
                    passport.row.sourceWitness) := by
  obtain ⟨update⟩ := finFourAdjacentSpectator_exists_sameTailPaidUpdate
    source tail hgamma hbound hdelta hscale hreward hpass htail
  obtain ⟨passport⟩ := update.nonempty_actualReachPassport
    (finFourAdjacentSpectatorPaidFloor_pos hgamma hbound hdelta) hbound hreward
  obtain ⟨port⟩ :=
    (passport.capLiftedSource minimum hminimum hminimumPos).nonempty_summablePort
  have hreach := passport.minimumDebt_div_eightBound_le_capLiftedReachFloor
    minimum hminimum hminimumPos hreward
  have hshift := passport.minimumDebt_mul_floor_div_thirtyTwoBound_le_shiftedGain
    minimum hminimum hminimumPos hreward
  exact ⟨update, passport, ⟨port⟩, hreach, hshift⟩

/-- Exact packet specialization: the retained tail itself realizes the
supplied positive global minimum, and the produced source has explicit
finite all-Continue-prefix replacement ancestry from that realizer. -/
theorem finFourAdjacentSpectatorTailMinimum_nonempty_capLiftedSummablePort
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {gamma bound delta : ℝ}
    (source : QuittingAdjacentDeadlineGapSource reward gamma bound)
    (tail : (quittingGame reward).BehaviorProfile)
    (hgamma : 0 < gamma) (hbound : 0 < bound) (hdelta : 0 < delta)
    (hscale : gamma / bound ≤ 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpass : 1 - (source.old source.observer none).toReal <
      gamma / bound / 8)
    (htail : ∀ player, delta / 2 ≤
      quittingTerminalPayoff reward tail player -
        reward (quittingSingletonTerminal player) player)
    (hminimum : ∀ candidate,
      candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward tail) ≤
          quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward tail)) :
    ∃ update : QuittingFiniteDeadlineSameTailPaidUpdate reward
        (source.deadline + 1) tail
        (finFourAdjacentSpectatorPaidFloor gamma bound delta),
      (∃ base : (quittingGame reward).BehaviorProfile,
        quittingTerminalSemanticPair reward base =
            quittingTerminalSemanticPair reward tail ∧
          Nonempty
            (FinFourBehaviorReplacementAncestry base update.sourceProfile)) ∧
      ∃ passport : QuittingSameTailActualReachPaidUpdatePassport
          (bound := bound) update,
        Nonempty (QuittingPaidCapLiftedSource.SummablePort
            (passport.capLiftedSource
              (quittingTerminalSemanticPair reward tail) hminimum hminimumPos)) ∧
          quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward tail) / (8 * bound) ≤
            (passport.capLiftedSource
              (quittingTerminalSemanticPair reward tail)
                hminimum hminimumPos).reachFloor ∧
          ∀ horizon,
            quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward tail) *
                finFourAdjacentSpectatorPaidFloor gamma bound delta /
                  (32 * bound) ≤
              quittingPureTimeDeviationPayoff reward
                  (quittingCapLiftedPrefixProfile reward
                    update.sourceProfile horizon)
                  update.mover
                  (quittingCapLiftPureTimeShift horizon
                    passport.row.receivingWitness) -
                quittingPureTimeDeviationPayoff reward
                  (quittingCapLiftedPrefixProfile reward
                    update.sourceProfile horizon)
                  update.mover
                  (quittingCapLiftPureTimeShift horizon
                    passport.row.sourceWitness) := by
  obtain ⟨update, passport, port, hreach, hshift⟩ :=
    finFourAdjacentSpectator_nonempty_capLiftedSummablePort source tail
      hgamma hbound hdelta hscale hreward hpass htail
      (quittingTerminalSemanticPair reward tail) hminimum hminimumPos
  have hsolo : ∀ player, reward (quittingSingletonTerminal player) player ≤
      quittingContinuationBestResponseValue reward tail player := by
    intro player
    have hself := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward tail player (tail player)
    rw [Function.update_eq_self] at hself
    linarith [htail player]
  obtain ⟨base, hbase, ancestry⟩ :=
    update.exists_allContinuePrefixAncestry hsolo
  exact ⟨update, ⟨base, hbase, ancestry⟩,
    passport, port, hreach, hshift⟩

end GameTheory
