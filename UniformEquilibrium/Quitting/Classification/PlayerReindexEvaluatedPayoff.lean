import MathUE.PMFProduct.Reindex
import MathUE.Reindex
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality
import UniformEquilibrium.Quitting.Paths.StoppingLawEvaluatedPayoff

/-! # Naturality of clock-evaluated quitting payoffs under player relabeling -/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability Math.PMFProduct

section Earliest

variable {ι κ : Type} [Fintype ι] [Fintype κ]

private theorem quittingEarliestStoppingValue_reindex
    (e : ι ≃ κ) (times : ι → Option ℕ) :
    quittingEarliestStoppingValue (fun who : κ => times (e.symm who)) =
      quittingEarliestStoppingValue times := by
  change (Finset.univ.inf (fun who : κ =>
      (quittingStoppingTimeValue (times (e.symm who)) : WithTop ℕ))) =
    Finset.univ.inf (fun who : ι =>
      (quittingStoppingTimeValue (times who) : WithTop ℕ))
  rw [Finset.inf_eq_iInf, Finset.inf_eq_iInf]
  simp only [Finset.mem_univ, iInf_true]
  exact Math.Reindex.iInf_comp_equiv e.symm
    (fun who : ι => quittingStoppingTimeValue (times who))

end Earliest

section Outcome

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  [Nonempty ι] [Nonempty κ]

private theorem quittingFirstStoppingOutcome_reindex
    (e : ι ≃ κ) (times : ι → Option ℕ) :
    quittingFirstStoppingOutcome (fun who : κ => times (e.symm who)) =
      Option.map (quittingCoalitionEquiv e) (quittingFirstStoppingOutcome times) := by
  have htime := quittingEarliestStoppingValue_reindex e times
  unfold quittingFirstStoppingOutcome
  rw [htime]
  split_ifs with htop
  · rfl
  · congr 1
    apply Subtype.ext
    ext who
    simp [quittingEarliestStoppingCoalition, quittingCoalitionEquiv,
      Finset.mem_map_equiv, htime]

end Outcome

section PureClock

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  [Nonempty ι] [Nonempty κ]

private theorem quittingPureClockEvaluatedPayoff_reindex
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (who : ι) :
    quittingPureClockEvaluatedPayoff (quittingRewardReindex e reward)
        evaluation (fun player : κ => times (e.symm player)) (e who) =
      quittingPureClockEvaluatedPayoff reward evaluation times who := by
  unfold quittingPureClockEvaluatedPayoff
  rw [quittingFirstStoppingOutcome_reindex e times,
    quittingEarliestStoppingValue_reindex e times]
  cases quittingFirstStoppingOutcome times <;>
    simp [quittingRewardReindex]

end PureClock

section StoppingLaw

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  [Nonempty ι] [Nonempty κ]

/-- Clock-evaluated expected payoffs are invariant under player relabeling. -/
theorem quittingStoppingLawEvaluatedPayoff_reindex
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (laws : ι → PMF (Option ℕ)) (who : ι) :
    quittingStoppingLawEvaluatedPayoff (quittingRewardReindex e reward)
        evaluation (fun player => laws (e.symm player)) (e who) =
      quittingStoppingLawEvaluatedPayoff reward evaluation laws who := by
  let clockEquiv : (ι → Option ℕ) ≃ (κ → Option ℕ) :=
    e.arrowCongr (Equiv.refl (Option ℕ))
  have hmap : PMF.map clockEquiv (pmfPi laws) =
      pmfPi (fun player => laws (e.symm player)) :=
    pmfPi_map_precompEquiv e clockEquiv (fun _ _ => rfl) laws
  unfold quittingStoppingLawEvaluatedPayoff
  rw [← hmap, expect_map]
  congr 1
  funext times
  exact quittingPureClockEvaluatedPayoff_reindex e reward evaluation times who

end StoppingLaw

section Reindex

variable {ι κ : Type} [Fintype ι] [Fintype κ]
  [Nonempty ι] [Nonempty κ]

/-- Actual behavioral evaluated payoffs commute with relabeling. -/
theorem quittingBehaviorEvaluatedPayoff_profilePushforward
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedPayoff (quittingRewardReindex e reward)
        evaluation (quittingProfilePushforward e reward profile) (e who) =
      quittingBehaviorEvaluatedPayoff reward evaluation profile who := by
  unfold quittingBehaviorEvaluatedPayoff
  have hlaws : quittingBehaviorStoppingLaws
        (quittingRewardReindex e reward)
        (quittingProfilePushforward e reward profile) =
      fun player => quittingBehaviorStoppingLaws reward profile (e.symm player) := by
    funext player
    change quittingBehaviorStoppingLaw (quittingRewardReindex e reward)
        (quittingProfilePushforward e reward profile player) =
      quittingBehaviorStoppingLaw reward (profile (e.symm player))
    have h := quittingBehaviorStoppingLaw_profilePushforward e reward profile
      (e.symm player)
    rw [e.apply_symm_apply] at h
    exact h
  rw [hlaws]
  exact quittingStoppingLawEvaluatedPayoff_reindex e reward evaluation
    (quittingBehaviorStoppingLaws reward profile) who

/-- Evaluated payoffs commute with behavioral profile pullback. -/
theorem quittingBehaviorEvaluatedPayoff_profilePullback
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingRewardReindex e reward)).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedPayoff (quittingRewardReindex e reward)
        evaluation profile (e who) =
      quittingBehaviorEvaluatedPayoff reward evaluation
        (quittingProfilePullback e reward profile) who := by
  conv_lhs => rw [← quittingProfilePushforward_pullback e reward profile]
  exact quittingBehaviorEvaluatedPayoff_profilePushforward e reward evaluation
    (quittingProfilePullback e reward profile) who

/-- Full evaluated behavioral caps commute with relabeling. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_profilePushforward
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedDeviationPayoffCap (quittingRewardReindex e reward)
        evaluation (quittingProfilePushforward e reward profile) (e who) =
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation profile who := by
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply congrArg sSup
  ext value
  simp only [Set.mem_range]
  constructor
  · rintro ⟨deviation, rfl⟩
    let pulled : (quittingGame reward).BehaviorStrategy who :=
      fun time history => deviation time (quittingHistEquiv e reward time history)
    refine ⟨pulled, ?_⟩
    have hupdate := quittingProfilePullback_update e reward
      (quittingProfilePushforward e reward profile) who deviation
    rw [quittingProfilePullback_pushforward] at hupdate
    change quittingBehaviorEvaluatedPayoff reward evaluation
        (Function.update profile who pulled) who = _
    rw [quittingBehaviorEvaluatedPayoff_profilePullback, hupdate]
  · rintro ⟨deviation, rfl⟩
    refine ⟨quittingStrategyPushforward e reward who deviation, ?_⟩
    rw [← quittingProfilePushforward_update]
    exact quittingBehaviorEvaluatedPayoff_profilePushforward e reward
      evaluation (Function.update profile who deviation) who

/-- Full evaluated behavioral caps commute with profile pullback. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_profilePullback
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingRewardReindex e reward)).BehaviorProfile) (who : ι) :
    quittingBehaviorEvaluatedDeviationPayoffCap (quittingRewardReindex e reward)
        evaluation profile (e who) =
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingProfilePullback e reward profile) who := by
  conv_lhs => rw [← quittingProfilePushforward_pullback e reward profile]
  exact quittingBehaviorEvaluatedDeviationPayoffCap_profilePushforward
    e reward evaluation (quittingProfilePullback e reward profile) who

end Reindex

section RewardPayoffEq

variable {ρ : Type} [Fintype ρ] [Nonempty ρ]

/-- Equal reward tables give equal evaluated payoffs after profile transport. -/
@[simp] theorem quittingBehaviorEvaluatedPayoff_profileOfRewardEq
    {first second : {S : Finset ρ // S.Nonempty} → Payoff ρ}
    (hreward : first = second)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame second).BehaviorProfile) (who : ρ) :
    quittingBehaviorEvaluatedPayoff first evaluation
        (quittingProfileOfRewardEq hreward profile) who =
      quittingBehaviorEvaluatedPayoff second evaluation profile who := by
  subst second
  rfl

end RewardPayoffEq

section RewardCapEq

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ] [Nonempty ρ]

/-- Equal reward tables give equal unrestricted evaluated caps. -/
@[simp] theorem quittingBehaviorEvaluatedDeviationPayoffCap_profileOfRewardEq
    {first second : {S : Finset ρ // S.Nonempty} → Payoff ρ}
    (hreward : first = second)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame second).BehaviorProfile) (who : ρ) :
    quittingBehaviorEvaluatedDeviationPayoffCap first evaluation
        (quittingProfileOfRewardEq hreward profile) who =
      quittingBehaviorEvaluatedDeviationPayoffCap second evaluation profile who := by
  subst second
  rfl

end RewardCapEq

end GameTheory
