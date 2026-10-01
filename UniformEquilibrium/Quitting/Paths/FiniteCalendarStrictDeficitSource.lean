import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.StrictDeficitFiniteWords

/-! # Raw-calendar strict deficit on the actual finite source words -/

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal raw-calendar margin holds on every actual finite word.
The raw exclusion itself supplies a player, including for an empty word. -/
theorem hasQuittingFiniteWordStrictSingletonDeficit_of_finiteCalendarRaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (hraw : HasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap) :
    HasQuittingFiniteWordStrictSingletonDeficit reward gap := by
  let calendar : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))) := fun _ =>
    Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)
  obtain ⟨who, _⟩ := hraw calendar
  let : Nonempty ι := ⟨who⟩
  have hactual :=
    (hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual reward gap).mp hraw
  intro roots
  exact hactual (quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward))

/-- Accepting the strict raw predicate produces one positive common margin
for every actual finite source word, not a cap-preserving payoff realization. -/
theorem exists_positive_finiteWordStrictSingletonDeficit_of_finiteCalendarRawStrict
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hraw : HasQuittingFiniteCalendarRawStrictExclusion reward) :
    ∃ gap > 0, HasQuittingFiniteWordStrictSingletonDeficit reward gap := by
  let calendar : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))) := fun _ =>
    Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)
  obtain ⟨who, _⟩ := hraw calendar
  let : Nonempty ι := ⟨who⟩
  obtain ⟨gap, hgap, hactual⟩ :=
    exists_positive_actual_strictSingletonDeficit_of_rawStrictExclusion reward hraw
  exact ⟨gap, hgap, fun roots => hactual (quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward))⟩

end GameTheory
