import UniformEquilibrium.Quitting.Root.FiniteDeadlineCapRecursion
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction
import MathUE.ProbabilityMassFunction.FiniteStoppingTimeMenu

/-! # Actual finite-menu realization of finite root words -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The stopping law of a truncated root-word strategy has no finite atom at
or after its truncation deadline. -/
theorem quittingBehaviorStoppingLaw_truncatedRootProfile_some_eq_zero_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) (who : ι)
    {time : ℕ} (htime : deadline ≤ time) :
    quittingBehaviorStoppingLaw reward
      (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who)
      (some time) = 0 := by
  have hz : (quittingBehaviorStoppingLaw reward
      (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0 who)
      (some time)).toReal = 0 := by
    rw [quittingBehaviorStoppingLaw_some_toReal]
    unfold quittingBehaviorLiveHazard quittingHazardStopMass
    simp only [quittingRootSequenceProfile, Nat.zero_add]
    have hroot : quittingTruncatedRoots roots deadline time who = PMF.pure false := by
      rw [quittingTruncatedRoots_of_le roots htime]
      rfl
    have hstop : (Math.Probability.DiscreteHazard.BooleanHazard.toScalar
        (fun time => quittingTruncatedRoots roots deadline time who)).stop time = 0 := by
      change (quittingTruncatedRoots roots deadline time who true).toReal = 0
      rw [hroot]
      simp
    unfold Math.Probability.DiscreteHazard.ScalarHazard.stopMass
    rw [hstop, mul_zero]
  rcases (ENNReal.toReal_eq_zero_iff _).mp hz with hzero | htop
  · exact hzero
  · exact (PMF.apply_ne_top _ _ htop).elim

omit [DecidableEq ι] in
/-- Every finite product-root word followed by all Continue is represented by
actual independent laws on the corresponding date-or-Never menu. -/
theorem exists_finiteDeadlineTimingLaws_of_truncatedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots roots deadline) 0 who) := by
  classical
  have hexists (who : ι) : ∃ law : PMF (Option (Fin deadline)),
      law.map (Math.Probability.finiteStoppingTimeDecode deadline) =
        quittingBehaviorStoppingLaw reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots roots deadline) 0 who) := by
    obtain ⟨law, hlaw, _⟩ := Math.Probability.exists_finiteStoppingTimePMF_map_eq
      (quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward
          (quittingTruncatedRoots roots deadline) 0 who)) deadline
      (fun time htime =>
        quittingBehaviorStoppingLaw_truncatedRootProfile_some_eq_zero_of_le
          reward roots deadline who htime)
    exact ⟨law, hlaw⟩
  choose mixed hmixed using hexists
  refine ⟨mixed, fun who => ?_⟩
  rw [quittingFiniteDeadlineTimingLaw,
    Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  have hmaps : (mixed who).map quittingFiniteDeadlineTimingActionTime =
      (mixed who).map (Math.Probability.finiteStoppingTimeDecode deadline) := by
    congr 1
    funext action
    cases action with
    | none => rfl
    | some time => rfl
  rw [hmaps, hmixed who]

/-- The realized finite-menu product law preserves the prescribed terminal
payoff vector of the truncated root word. -/
theorem exists_finiteDeadlineTimingProfile_payoff_eq_truncatedRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots roots deadline) 0) := by
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_truncatedRoots reward roots deadline
  refine ⟨mixed, ?_⟩
  funext observer
  rw [quittingTerminalPayoff_eq_compactStoppingLawsOfProfile reward
    (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0)]
  unfold quittingFiniteDeadlineTimingProfile
  congr 2
  funext who
  unfold quittingCompactStoppingLawsOfProfile
  apply congrArg Math.Probability.CompactStoppingLaw.ofPMF
  simpa [quittingFiniteDeadlineTimingLaw] using hmixed who

/-- The realization preserves every displayed pure-menu payoff as well as
the prescribed payoff, so it preserves the finite reply cap. -/
theorem exists_finiteDeadlineTimingProfile_menu_payoff_realization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalPayoff reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots roots deadline) 0) ∧
      ∀ who (action : QuittingFiniteDeadlineTimingAction deadline),
        quittingTerminalPayoff reward
            (Function.update
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
              (quittingPureTimeBehaviorStrategy reward who
                (quittingFiniteDeadlineTimingActionTime action))) who =
          quittingTerminalPayoff reward
            (Function.update
              (quittingRootSequenceProfile reward
                (quittingTruncatedRoots roots deadline) 0) who
              (quittingPureTimeBehaviorStrategy reward who
                (quittingFiniteDeadlineTimingActionTime action))) who := by
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_truncatedRoots reward roots deadline
  have hcompact : (fun who => quittingFiniteDeadlineTimingLaw (mixed who)) =
      quittingCompactStoppingLawsOfProfile reward
        (quittingRootSequenceProfile reward
          (quittingTruncatedRoots roots deadline) 0) := by
    funext who
    unfold quittingCompactStoppingLawsOfProfile
    apply congrArg Math.Probability.CompactStoppingLaw.ofPMF
    simpa [quittingFiniteDeadlineTimingLaw] using hmixed who
  refine ⟨mixed, ?_, ?_⟩
  · funext observer
    rw [quittingTerminalPayoff_eq_compactStoppingLawsOfProfile reward
      (quittingRootSequenceProfile reward (quittingTruncatedRoots roots deadline) 0)]
    simp [quittingFiniteDeadlineTimingProfile, hcompact]
  · intro who action
    symm
    rw [quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile]
    simp [quittingFiniteDeadlineTimingProfile, hcompact]

/-- In particular, one actual finite-menu product law realizes the cap of
the supplied finite root word simultaneously for every player. -/
theorem exists_finiteDeadlineReplyCap_eq_finiteRootWordCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (deadline : ℕ) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      ∀ who, quittingFiniteDeadlineReplyCap reward deadline mixed who =
        quittingFiniteRootWordCap reward
          (List.ofFn fun time : Fin deadline => roots time.val) who 0 := by
  obtain ⟨mixed, _, hpure⟩ :=
    exists_finiteDeadlineTimingProfile_menu_payoff_realization
      reward roots deadline
  refine ⟨mixed, fun who => ?_⟩
  rw [quittingFiniteDeadlineReplyCap_eq_sup_pureTimeTerminalValue]
  have hvalues : (fun action : QuittingFiniteDeadlineTimingAction deadline =>
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed)) who
        (quittingFiniteDeadlineTimingActionTime action) 0) =
      fun action => quittingRootSequencePureTimeTerminalValue reward
        (quittingTruncatedRoots roots deadline) who
        (quittingFiniteDeadlineTimingActionTime action) 0 := by
    funext action
    calc
      _ = quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who
              (quittingFiniteDeadlineTimingActionTime action))) who :=
        (quittingTerminalPayoff_update_pureTimeBehaviorStrategy reward _ _ _).symm
      _ = _ := hpure who action
      _ = _ := by
        rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
        simp
  rw [hvalues]
  have hfold := finitePureTimeMenuCap_eq_finiteRootWordCap
    reward (quittingTruncatedRoots roots deadline) who 0 deadline
  have htail' : quittingRootSequencePureTimeTerminalValue reward
      (quittingTruncatedRoots roots deadline) who none deadline = 0 := by
    unfold quittingRootSequencePureTimeTerminalValue
    apply quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    intro time htime
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingRootSequenceUpdate, quittingPureTimeHazard]
      change PMF.pure false = PMF.pure false
      rfl
    · simp [quittingRootSequenceUpdate, hplayer,
        quittingTruncatedRoots_of_le roots htime]
  simp only [Nat.zero_add] at hfold
  rw [htail'] at hfold
  have hlist : (List.ofFn fun time : Fin deadline =>
      quittingTruncatedRoots roots deadline time.val) =
      List.ofFn fun time : Fin deadline => roots time.val := by
    congr 1
    funext time
    rw [quittingTruncatedRoots_of_lt roots time.isLt]
  rw [hlist] at hfold
  convert hfold using 1
  · congr 1
    funext action
    cases action with
    | none =>
        change quittingRootSequencePureTimeTerminalValue reward _ who none = _
        rfl
    | some time =>
        change quittingRootSequencePureTimeTerminalValue reward _ who
          (some time.val) = _
        simp

end GameTheory
