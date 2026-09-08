import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWords

/-! # Actual-source group exclusion on literal finite words -/

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι]

/-- Actual behavioral group exclusion restricts to every literal finite root
word followed by Always Continue. -/
theorem hasQuittingFiniteWordNonconcentratedGroupExclusion_of_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ)
    (hactual : HasQuittingActualNonconcentratedGroupExclusion reward beta) :
    HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta := by
  intro roots
  exact hactual (quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward))

variable [DecidableEq ι] [Nonempty ι]

/-- The raw finite-calendar predicate supplies group exclusion on every
literal finite word. -/
theorem hasQuittingFiniteWordNonconcentratedGroupExclusion_of_raw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ)
    (hraw : HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
      reward beta) :
    HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta :=
  hasQuittingFiniteWordNonconcentratedGroupExclusion_of_actual reward beta
    ((hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual
      reward beta).mp hraw)

end GameTheory
