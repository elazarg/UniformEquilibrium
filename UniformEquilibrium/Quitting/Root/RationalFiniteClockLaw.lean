import UniformEquilibrium.Quitting.Root.RationalFiniteWordSemantics
import UniformEquilibrium.Quitting.Root.TruncatedStoppingLaw
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-! # Exact rational masses of actual finite independent clocks

Executable prefix products compute every finite atom and the retained Never
atom. The existing finite root-word realization supplies the actual PMFs and
their full semantic pair. This adds rational mass witnesses to that realization;
it does not introduce a restricted deviation menu.
-/

namespace GameTheory

open scoped BigOperators
open _root_.Math.Probability

variable {players deadline : ℕ}

/-- Exact own survival before a date of the rational word. -/
def rationalFiniteClockPrefix (roots : ℕ → RationalQuittingRoot players)
    (who : Fin players) (time : ℕ) : ℚ :=
  ∏ date ∈ Finset.range time, (1 - (roots date).probability who)

/-- Exact marginal clock masses: finite dates use survival times hazard;
Never retains own survival through the entire finite word. -/
def rationalFiniteClockMass (roots : ℕ → RationalQuittingRoot players)
    (deadline : ℕ) (who : Fin players) : Option (Fin deadline) → ℚ
  | none => rationalFiniteClockPrefix roots who deadline
  | some time => rationalFiniteClockPrefix roots who time.val * (roots time.val).probability who

noncomputable section

private theorem finiteStoppingTimeDecode_injective (deadline : ℕ) :
    Function.Injective (Math.Probability.finiteStoppingTimeDecode deadline) := by
  intro first second heq
  cases first with
  | none => cases second <;> simp_all [Math.Probability.finiteStoppingTimeDecode]
  | some first =>
      cases second with
      | none => simp [Math.Probability.finiteStoppingTimeDecode] at heq
      | some second =>
          simp only [Math.Probability.finiteStoppingTimeDecode, Option.map_some,
            Option.some.injEq] at heq
          exact congrArg some (Fin.ext heq)

private theorem finiteStoppingTimeDecode_eq_timingActionTime (deadline : ℕ) :
    Math.Probability.finiteStoppingTimeDecode deadline =
      quittingFiniteDeadlineTimingActionTime (deadline := deadline) := by
  funext action
  cases action <;> rfl

private theorem finiteStoppingTimeDecode_map_apply
    (law : PMF (Option (Fin deadline))) (choice : Option (Fin deadline)) :
    law.map (Math.Probability.finiteStoppingTimeDecode deadline)
        (Math.Probability.finiteStoppingTimeDecode deadline choice) = law choice := by
  rw [PMF.map_apply, tsum_eq_single choice]
  · simp
  · intro other hother
    have hne : Math.Probability.finiteStoppingTimeDecode deadline choice ≠
        Math.Probability.finiteStoppingTimeDecode deadline other := by
      intro heq
      exact hother ((finiteStoppingTimeDecode_injective deadline heq).symm)
    simp [hne]

theorem rationalFiniteClockPrefix_cast (roots : ℕ → RationalQuittingRoot players)
    (who : Fin players) (time : ℕ) :
    (rationalFiniteClockPrefix roots who time : ℝ) =
      ∏ date ∈ Finset.range time, ((roots date).toPMF who false).toReal := by
  simp [rationalFiniteClockPrefix, Rat.cast_prod]

/-- The concrete root word's actual retained atom is exactly its rational mass. -/
theorem rationalFiniteClockMass_cast_eq_stoppingLaw
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (roots : ℕ → RationalQuittingRoot players) (deadline : ℕ) (hdeadline : 0 < deadline)
    (who : Fin players) (choice : Option (Fin deadline)) :
    (rationalFiniteClockMass roots deadline who choice : ℝ) =
      (quittingBehaviorStoppingLaw reward
        (quittingRootSequenceProfile reward
          (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0 who)
        (Math.Probability.finiteStoppingTimeDecode deadline choice)).toReal := by
  cases choice with
  | none =>
      simp only [Math.Probability.finiteStoppingTimeDecode, Option.map_none]
      rw [quittingBehaviorStoppingLaw_truncatedRoots_none_toReal
        reward _ deadline hdeadline who]
      exact rationalFiniteClockPrefix_cast roots who deadline
  | some time =>
      simp only [Math.Probability.finiteStoppingTimeDecode, Option.map_some]
      rw [quittingBehaviorStoppingLaw_truncatedRoots_some_eq_of_lt
        reward _ deadline time.val time.isLt who,
        quittingBehaviorStoppingLaw_some_toReal,
        quittingHazardStopMass_eq_survival_mul_stop, quittingHazardSurvival_eq_prod]
      simp only [quittingBehaviorLiveHazard, quittingRootSequenceProfile, Nat.zero_add]
      change ((rationalFiniteClockPrefix roots who time.val *
          (roots time.val).probability who : ℚ) : ℝ) = _
      rw [Rat.cast_mul, rationalFiniteClockPrefix_cast,
        RationalQuittingRoot.toPMF_true_toReal]

/-- Actual independent PMFs, exact rational marginal atoms, exact stopping laws,
and the unrestricted behavioral semantic pair are all supplied by the same word. -/
theorem exists_rationalFiniteClockLaws_exact
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (roots : ℕ → RationalQuittingRoot players) (deadline : ℕ) (hdeadline : 0 < deadline) :
    ∃ mixed : Fin players → PMF (Option (Fin deadline)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass roots deadline who choice : ℝ)) ∧
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0 who)) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0) := by
  obtain ⟨mixed, hmixed⟩ := exists_finiteDeadlineTimingLaws_of_truncatedRoots
    reward (fun time => (roots time).toPMF) deadline
  have hcompact : (fun who => quittingFiniteDeadlineTimingLaw (mixed who)) =
      quittingCompactStoppingLawsOfProfile reward
        (quittingRootSequenceProfile reward
          (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0) := by
    funext who
    unfold quittingCompactStoppingLawsOfProfile
    apply congrArg Math.Probability.CompactStoppingLaw.ofPMF
    simpa [quittingFiniteDeadlineTimingLaw] using hmixed who
  refine ⟨mixed, ?_, hmixed, ?_⟩
  · intro who choice
    have hmap : (mixed who).map (Math.Probability.finiteStoppingTimeDecode deadline) =
        quittingBehaviorStoppingLaw reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0 who) := by
      have h := hmixed who
      rw [quittingFiniteDeadlineTimingLaw,
        Math.Probability.CompactStoppingLaw.toPMF_ofPMF] at h
      change ((mixed who).map quittingFiniteDeadlineTimingActionTime : PMF (Option ℕ)) =
        quittingBehaviorStoppingLaw reward
          (quittingRootSequenceProfile reward
            (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0 who) at h
      rw [← finiteStoppingTimeDecode_eq_timingActionTime deadline] at h
      exact h
    rw [← finiteStoppingTimeDecode_map_apply (mixed who) choice, hmap]
    exact (rationalFiniteClockMass_cast_eq_stoppingLaw
      reward roots deadline hdeadline who choice).symm
  · rw [quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile reward
      (quittingRootSequenceProfile reward
        (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0)]
    simp only [quittingFiniteDeadlineTimingProfile, hcompact]

/-- A zero-hazard outsider receives the literal point mass at Never. -/
theorem rationalFiniteClockLaw_eq_pure_none_of_zero
    (roots : ℕ → RationalQuittingRoot players) (deadline : ℕ)
    (who : Fin players) (law : PMF (Option (Fin deadline)))
    (hlaw : ∀ choice, (law choice).toReal =
      (rationalFiniteClockMass roots deadline who choice : ℝ))
    (hzero : ∀ time < deadline, (roots time).probability who = 0) :
    law = PMF.pure none := by
  apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  rw [hlaw]
  cases choice with
  | none =>
      have hprefix : rationalFiniteClockPrefix roots who deadline = 1 := by
        apply Finset.prod_eq_one
        intro time htime
        rw [hzero time (Finset.mem_range.mp htime)]
        simp
      simp [rationalFiniteClockMass, hprefix]
  | some time =>
      simp [rationalFiniteClockMass, hzero time.val time.isLt]

/-- The same finite rational word has the already checked exact rational
payoff/cap fold, whose cap includes all after-support dates and Never. -/
theorem rationalFiniteClock_truncated_semanticPair_eq_cast
    (reward : RationalQuittingReward players) (roots : ℕ → RationalQuittingRoot players)
    (deadline : ℕ) :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingRootSequenceProfile (rationalQuittingRewardToReal reward)
          (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0) =
      (fun who => ((rationalQuittingFiniteWordSemanticPair reward
          (List.ofFn fun time : Fin deadline => roots time.val)).1 who : ℝ),
        fun who => ((rationalQuittingFiniteWordSemanticPair reward
          (List.ofFn fun time : Fin deadline => roots time.val)).2 who : ℝ)) := by
  have hprofile := quittingRootSequenceProfile_eq_literalRootStack
    (rationalQuittingRewardToReal reward)
    (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) 0 deadline
  have htail : quittingRootSequenceProfile (rationalQuittingRewardToReal reward)
      (quittingTruncatedRoots (fun time => (roots time).toPMF) deadline) deadline =
        quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward) := by
    funext who time history
    simp only [quittingRootSequenceProfile]
    rw [quittingTruncatedRoots_of_le _ (Nat.le_add_right deadline time)]
    rfl
  have hword : (List.ofFn fun time : Fin deadline =>
      quittingTruncatedRoots (fun time => (roots time).toPMF) deadline (0 + time.val)) =
        (List.ofFn fun time : Fin deadline => roots time.val).map RationalQuittingRoot.toPMF := by
    rw [List.map_ofFn]
    congr 1
    funext time
    simp only [Nat.zero_add, Function.comp_apply]
    rw [quittingTruncatedRoots_of_lt _ time.isLt]
  simp only [Nat.zero_add] at hprofile
  rw [htail] at hprofile
  have hword' := hword
  simp only [Nat.zero_add] at hword'
  rw [hword'] at hprofile
  rw [hprofile]
  exact quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward
    (List.ofFn fun time : Fin deadline => roots time.val)

end

end GameTheory
