import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockParentLawPushforward
import UniformEquilibrium.Quitting.Paths.StoppingLawEvaluatedPayoff

/-!
# Evaluated payoff adapter for capped-clock parent laws

The common parent coupling has the evaluated stopping-law payoffs of the
outsider replacement, the quiet baseline, and each reconstructed capped-child
replacement as its three relevant marginals.  The last replacement is an
actual unrestricted behavioral deviation from the reconstructed quiet profile.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- The source coupling's outsider experiment is the evaluated payoff of the
parent stopping laws in which the outsider uses `outsideLaw`. -/
theorem expect_parentSource_outside_eq_stoppingLawEvaluatedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) :
    expect (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => quittingPureClockEvaluatedPayoff reward evaluation
          (outsideDeadlineClocks (fun i => clocks (some i)) (clocks none)) none) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedClockParentSourceLaws childLaws outsideLaw) none := by
  rw [quittingStoppingLawEvaluatedPayoff]
  apply congrArg (expect (pmfPi
    (cappedClockParentSourceLaws childLaws outsideLaw)))
  funext clocks
  congr 2
  funext player
  cases player <;> rfl

omit [DecidableEq ι] in
/-- Discarding the sampled outsider clock gives the evaluated payoff of the
quiet parent stopping laws. -/
theorem expect_parentSource_quiet_eq_stoppingLawEvaluatedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ))
    (who : Option ι) :
    expect (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => quittingPureClockEvaluatedPayoff reward evaluation
          (quietParentClocks fun i => clocks (some i)) who) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (quietParentStoppingLaws childLaws) who := by
  rw [quittingStoppingLawEvaluatedPayoff]
  rw [← map_pmfPi_cappedClockParentSourceLaws_quiet childLaws outsideLaw,
    expect_map]

/-- The capped-child marginal is the evaluated payoff of its actual compiled
complete stopping law. -/
theorem expect_parentSource_cappedChild_eq_stoppingLawEvaluatedPayoff
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    expect (pmfPi (cappedClockParentSourceLaws childLaws outsideLaw))
        (fun clocks => quittingPureClockEvaluatedPayoff reward evaluation
          (cappedChildParentClocks (fun j => clocks (some j))
            (clocks none) i) (some i)) =
      quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedChildParentStoppingLaws childLaws outsideLaw i) (some i) := by
  rw [quittingStoppingLawEvaluatedPayoff]
  rw [← map_pmfPi_cappedClockParentSourceLaws_cappedChild
    childLaws outsideLaw i, expect_map]

/-- Every capped-child marginal is the payoff of an actual unrestricted
behavioral deviation from the reconstructed quiet profile. -/
theorem cappedChild_stoppingLawEvaluatedPayoff_le_behaviorDeviationCap
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childLaws : ι → PMF (Option ℕ)) (outsideLaw : PMF (Option ℕ)) (i : ι) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (cappedChildParentStoppingLaws childLaws outsideLaw i) (some i) ≤
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingStoppingLawProfile reward
          (quietParentStoppingLaws childLaws)) (some i) := by
  rw [← quittingBehaviorEvaluatedPayoff_stoppingLawProfile]
  let quietProfile := quittingStoppingLawProfile reward
    (quietParentStoppingLaws childLaws)
  let deviation := quittingStoppingLawBehaviorStrategy reward (some i)
    (cappedClockStoppingLaw (childLaws i) outsideLaw)
  have hprofile : quittingStoppingLawProfile reward
      (cappedChildParentStoppingLaws childLaws outsideLaw i) =
      Function.update quietProfile (some i) deviation := by
    funext player
    by_cases hp : player = some i
    · subst player
      simp [cappedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile]
    · simp [cappedChildParentStoppingLaws, quietProfile, deviation,
        quittingStoppingLawProfile, hp]
  rw [hprofile]
  unfold quittingBehaviorEvaluatedDeviationPayoffCap
  apply le_csSup
    (bddAbove_range_quittingBehaviorEvaluatedPayoff_update reward evaluation
      evaluation_nonneg evaluation_antitone quietProfile (some i))
  exact ⟨deviation, rfl⟩

end GameTheory
