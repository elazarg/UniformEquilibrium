import UniformEquilibrium.Quitting.Paths.FiniteCalendarOrderedPairGroupExclusion

/-! # Real calendar witnesses for rejection of raw exclusion -/

noncomputable section

namespace GameTheory

variable {players : Type} [Fintype players] [DecidableEq players]

/-- Strict raw exclusion fails exactly when one genuine calendar profile has
nonnegative singleton-relative surplus in every coordinate. -/
theorem not_hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_nonnegative
    (reward : {S : Finset players // S.Nonempty} → Payoff players) :
    ¬HasQuittingFiniteCalendarRawStrictExclusion reward ↔
      ∃ profile : MixedSimplex players
          (fun _ => QuittingFiniteDeadlineTimingAction
            (Fintype.card players * (Fintype.card players + 1))),
        ∀ who,
          reward (quittingSingletonTerminal who) who ≤
            quittingFiniteCalendarRawPayoff reward _ profile who := by
  simp only [HasQuittingFiniteCalendarRawStrictExclusion, not_forall, not_exists,
    not_lt]

/-- Weak-subset rejection records either a failed singleton sign premise or
one genuine calendar profile with strictly positive surplus on every owner. -/
theorem not_hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff
    (reward : {S : Finset players // S.Nonempty} → Payoff players)
    (owners : Finset players) :
    ¬HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners ↔
      (∃ who ∈ owners,
        reward (quittingSingletonTerminal who) who < 0) ∨
      ∃ profile : MixedSimplex players
          (fun _ => QuittingFiniteDeadlineTimingAction
            (Fintype.card players * (Fintype.card players + 1))),
        ∀ who ∈ owners,
          reward (quittingSingletonTerminal who) who <
            quittingFiniteCalendarRawPayoff reward _ profile who := by
  unfold HasQuittingFiniteCalendarRawWeakSubsetExclusion
  classical
  constructor
  · intro hexclusion
    by_cases hsign : ∀ who ∈ owners,
        0 ≤ reward (quittingSingletonTerminal who) who
    · right
      have hprofiles : ¬∀ profile : MixedSimplex players
          (fun _ => QuittingFiniteDeadlineTimingAction
            (Fintype.card players * (Fintype.card players + 1))),
          ∃ who ∈ owners,
          quittingFiniteCalendarRawPayoff reward
              (Fintype.card players * (Fintype.card players + 1)) profile who ≤
            reward (quittingSingletonTerminal who) who := by
        exact fun hprofiles => hexclusion ⟨hsign, hprofiles⟩
      push Not at hprofiles
      exact hprofiles
    · left
      push Not at hsign
      exact hsign
  · rintro (hsign | hprofile) hexclusion
    · obtain ⟨who, hwho, hnegative⟩ := hsign
      exact (not_le_of_gt hnegative) (hexclusion.1 who hwho)
    · obtain ⟨profile, hprofile⟩ := hprofile
      obtain ⟨who, hwho, hpayoff⟩ := hexclusion.2 profile
      exact (not_le_of_gt (hprofile who hwho)) hpayoff

variable [Nonempty players]

/-- Group rejection retains the exact quantifier order: every admissible
uniform pair weight has a calendar profile defeating all distinct pairs. -/
theorem not_exists_quittingFiniteCalendarRawGroupExclusion_iff
    (reward : {S : Finset players // S.Nonempty} → Payoff players) :
    ¬(∃ beta < 1,
        HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) ↔
      ∀ lambda, 0 < lambda → lambda ≤ (1 : ℝ) / 2 →
        ∃ profile : MixedSimplex players
            (fun _ => QuittingFiniteDeadlineTimingAction
              (Fintype.card players * (Fintype.card players + 1))),
          ∀ first second, first ≠ second →
            0 <
              (1 - lambda) *
                  (quittingFiniteCalendarRawPayoff reward _ profile first -
                    reward (quittingSingletonTerminal first) first) +
                lambda *
                  (quittingFiniteCalendarRawPayoff reward _ profile second -
                    reward (quittingSingletonTerminal second) second) := by
  rw [exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair]
  unfold HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
  push Not
  rfl

end GameTheory
