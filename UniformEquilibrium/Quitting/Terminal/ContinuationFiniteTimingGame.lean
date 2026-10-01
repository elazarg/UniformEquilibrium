import UniformEquilibrium.Quitting.Terminal.RetainedTailFiniteTimingWord
import UniformEquilibrium.Quitting.Root.TruncatedStoppingLaw
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge
import UniformEquilibrium.ProofView.Concepts.Existence.ParameterizedFiniteNash

/-! # Finite timing games with an arbitrary terminal continuation

The terminal vector is formal source data, not the payoff of an assumed behavioral tail.
The actual timing law decodes to the canonical chronological root word. All identities
include Never, zero-survival conditional rows, and the empty calendar.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal finite timer game with continuation `tail` on joint Never. -/
abbrev quittingContinuationFiniteTimingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : Payoff ι) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => QuittingFiniteDeadlineTimingAction deadline)
    (fun choices => quittingFiniteRootWordPayoff reward
      (quittingRetainedTailPureTimingRootStack deadline choices) tail)

instance quittingContinuationFiniteTimingGame_finiteOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : Payoff ι) :
    Finite (quittingContinuationFiniteTimingGame reward deadline tail).Outcome := by
  unfold quittingContinuationFiniteTimingGame KernelGame.ofPureEU
  infer_instance

omit [DecidableEq ι] in
private theorem pureWord_zero_eq_timingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) :
    quittingFiniteRootWordPayoff reward
        (quittingRetainedTailPureTimingRootStack deadline choices) 0 who =
      timingPurePayoff reward deadline choices who := by
  have h := quittingRetainedTailTimingPurePayoff_alwaysContinue_eq_timingPurePayoff
    reward deadline choices who
  unfold quittingRetainedTailTimingPurePayoff quittingRetainedTailFiniteTimingGraft at h
  rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff] at h
  have hzero : quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) = 0 := by
    funext player
    exact quittingTerminalPayoff_quittingAlwaysContinue reward player
  rwa [hzero] at h

omit [DecidableEq ι] in
/-- The arbitrary terminal vector enters the pure payoff only on joint Never. -/
theorem quittingContinuationFiniteTimingGame_purePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : Payoff ι)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) (who : ι) :
    (quittingContinuationFiniteTimingGame reward deadline tail).eu choices who =
      timingPurePayoff reward deadline choices who +
        tail who * (if choices = (fun _ => none) then 1 else 0) := by
  classical
  rw [KernelGame.eu_ofPureEU]
  have h := quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul reward
    (quittingRetainedTailPureTimingRootStack deadline choices) tail 0 who
  rw [pureWord_zero_eq_timingPurePayoff, Pi.zero_apply, sub_zero,
    quittingRetainedTailPureTimingRootStack_jointSurvival_eq_indicator] at h
  linarith

omit [DecidableEq ι] in
/-- The unique joint Never declaration receives exactly the specified terminal vector. -/
theorem quittingContinuationFiniteTimingGame_allNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : Payoff ι) (who : ι) :
    (quittingContinuationFiniteTimingGame reward deadline tail).eu (fun _ => none) who =
      tail who := by
  classical
  rw [quittingContinuationFiniteTimingGame_purePayoff]
  have hprofile : quittingPureStoppingTimeProfile reward
      (fun _ : ι => quittingFiniteDeadlineTimingActionTime
        (none : QuittingFiniteDeadlineTimingAction deadline)) =
      quittingAlwaysContinueProfile reward := by
    funext player time history
    rfl
  unfold timingPurePayoff
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]
  simp only [ite_true, mul_one, zero_add]

omit [DecidableEq ι] in
/-- Exact independent-law evaluation with the literal all-Never mass. -/
theorem quittingContinuationFiniteTimingGame_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : Payoff ι)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) :
    (quittingContinuationFiniteTimingGame reward deadline tail).mixedExtension.eu mixed who =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu mixed who +
        tail who * ∏ player, (mixed player none).toReal := by
  classical
  rw [(quittingContinuationFiniteTimingGame reward deadline tail).mixedExtension_eu]
  simp_rw [quittingContinuationFiniteTimingGame_purePayoff]
  rw [expect_add, expect_const_mul, ← apply_toReal_eq_expect_indicator]
  simp only [pmfPi_apply, ENNReal.toReal_prod]
  rw [finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff]
  rfl

/-- The same actual mixed timing laws yield the same chronological-word payoff,
for every formal terminal vector, including at exhausted survival prefixes. -/
theorem quittingContinuationFiniteTimingGame_mixedEU_eq_wordPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (tail : Payoff ι)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) :
    (quittingContinuationFiniteTimingGame reward deadline tail).mixedExtension.eu mixed who =
      quittingFiniteRootWordPayoff reward
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail who := by
  have hhard := congrArg (fun profile => quittingTerminalPayoff reward profile who)
    (quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
      reward deadline mixed)
  unfold quittingRetainedTailFiniteTimingHardGraft quittingRetainedTailFiniteTimingGraft
    at hhard
  rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff,
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU] at hhard
  have hzero : quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) = 0 := by
    funext player
    exact quittingTerminalPayoff_quittingAlwaysContinue reward player
  rw [hzero] at hhard
  have h := quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul reward
    (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail 0 who
  rw [Pi.zero_apply, sub_zero,
    quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none, hhard] at h
  rw [quittingContinuationFiniteTimingGame_mixedEU]
  linarith

/-- Joint continuity of the actual Nash map as the formal terminal vector varies. -/
theorem continuous_quittingContinuationFiniteTimingNashMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) :
    Continuous (fun data :
      Payoff ι × MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline) =>
      (show MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline) from
        (quittingContinuationFiniteTimingGame reward deadline data.1).nashMapOnMixedSimplex
          data.2)) := by
  classical
  have hpayoff (choices : ι → QuittingFiniteDeadlineTimingAction deadline) (who : ι) :
      Continuous (fun tail : Payoff ι =>
        quittingFiniteRootWordPayoff reward
          (quittingRetainedTailPureTimingRootStack deadline choices) tail who) := by
    have hformula : (fun tail : Payoff ι =>
        quittingFiniteRootWordPayoff reward
          (quittingRetainedTailPureTimingRootStack deadline choices) tail who) =
        fun tail => timingPurePayoff reward deadline choices who +
          tail who * (if choices = (fun _ => none) then 1 else 0) := by
      funext tail
      simpa only [quittingContinuationFiniteTimingGame, KernelGame.eu_ofPureEU] using
        quittingContinuationFiniteTimingGame_purePayoff reward deadline tail choices who
    rw [hformula]
    exact continuous_const.add ((continuous_apply who).mul continuous_const)
  exact KernelGame.continuous_ofPureEU_nashMapOnMixedSimplex
    (Action := fun _ : ι => QuittingFiniteDeadlineTimingAction deadline)
    (Parameter := Payoff ι)
    (fun tail choices => quittingFiniteRootWordPayoff reward
      (quittingRetainedTailPureTimingRootStack deadline choices) tail) hpayoff

/-- Exact stopping-law transport for any finite chronological root word.
The law identity is furnished by the canonical finite-menu realization; no payoff
or cap certificate is an input. Formal terminal vectors need not be attainable. -/
theorem quittingContinuationFiniteTimingGame_mixedEU_eq_wordPayoff_of_laws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) (tail : Payoff ι)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hlaws : ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
      quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who))
    (who : ι) :
    (quittingContinuationFiniteTimingGame reward deadline tail).mixedExtension.eu mixed who =
      quittingFiniteRootWordPayoff reward
        (List.ofFn fun time : Fin deadline => roots time.val) tail who := by
  classical
  cases deadline with
  | zero =>
      rw [quittingContinuationFiniteTimingGame_mixedEU_eq_wordPayoff]
      simp [quittingRetainedTailMixedTimingRootStack, quittingFiniteRootWordPayoff]
  | succ deadline =>
      let profile := quittingRootSequenceProfile reward
        (quittingTruncatedRoots roots (deadline + 1)) 0
      have hpay : quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward (deadline + 1) mixed) =
          quittingTerminalPayoff reward profile := by
        funext observer
        rw [quittingTerminalPayoff_eq_compactStoppingLawsOfProfile reward profile observer]
        unfold quittingFiniteDeadlineTimingProfile
        congr 2
        funext player
        unfold quittingCompactStoppingLawsOfProfile
        apply congrArg CompactStoppingLaw.ofPMF
        simpa only [quittingFiniteDeadlineTimingLaw, CompactStoppingLaw.toPMF_ofPMF,
          profile] using hlaws player
      have htail : quittingRootSequenceProfile reward
          (quittingTruncatedRoots roots (deadline + 1)) (deadline + 1) =
          quittingAlwaysContinueProfile reward := by
        funext player time history
        change quittingTruncatedRoots roots (deadline + 1) (deadline + 1 + time) player =
          PMF.pure false
        rw [quittingTruncatedRoots_of_le roots (Nat.le_add_right _ _)]
        rfl
      have hword : (List.ofFn fun time : Fin (deadline + 1) =>
          quittingTruncatedRoots roots (deadline + 1) time.val) =
          List.ofFn fun time : Fin (deadline + 1) => roots time.val := by
        congr 1
        funext time
        exact quittingTruncatedRoots_of_lt roots time.isLt
      have hprofile := quittingRootSequenceProfile_eq_literalRootStack reward
        (quittingTruncatedRoots roots (deadline + 1)) 0 (deadline + 1)
      simp only [Nat.zero_add, htail, hword] at hprofile
      have hzero : quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) = 0 := by
        funext player
        exact quittingTerminalPayoff_quittingAlwaysContinue reward player
      dsimp only [profile] at hpay
      rw [hprofile, quittingTerminalPayoff_literalRootStack_eq_wordPayoff, hzero] at hpay
      have hpayWho := congrFun hpay who
      rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU] at hpayWho
      have hsurvival :
          quittingLiteralRootStackJointSurvival
            (List.ofFn fun time : Fin (deadline + 1) => roots time.val) =
          ∏ player, (mixed player none).toReal := by
        rw [quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
        apply Finset.prod_congr rfl
        intro player _
        have hnone := quittingBehaviorStoppingLaw_truncatedRoots_none_toReal
          reward roots (deadline + 1) (Nat.succ_pos _) player
        have hlawAtNever := congrArg
          (fun law : PMF CompactStoppingTime => (law (⊤ : CompactStoppingTime)).toReal)
          (hlaws player)
        have hfiniteNever := congrArg ENNReal.toReal
          (quittingFiniteDeadlineTimingLaw_none (mixed player))
        have hsurvivalPlayer : (mixed player none).toReal =
            ∏ time ∈ Finset.range (deadline + 1), (roots time player false).toReal :=
          hfiniteNever.symm.trans (hlawAtNever.trans hnone)
        unfold quittingLiteralRootStackOwnSurvival
        rw [List.map_ofFn, List.prod_ofFn]
        change (∏ time : Fin (deadline + 1), (roots time.val player false).toReal) =
          (mixed player none).toReal
        exact (Fin.prod_univ_eq_prod_range
          (fun time => (roots time player false).toReal) (deadline + 1)).trans
            hsurvivalPlayer.symm
      have hsub := quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul reward
        (List.ofFn fun time : Fin (deadline + 1) => roots time.val) tail 0 who
      rw [Pi.zero_apply, sub_zero, hsurvival] at hsub
      rw [quittingContinuationFiniteTimingGame_mixedEU]
      linarith

end GameTheory
