import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawParameterFormula
import UniformEquilibrium.Quitting.Root.IsolatedRootRewardParameters

/-! # Finite-calendar raw exclusion decisions for isolated-root rewards -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

private theorem certifiedIsolatedRootRewardParameters_denote
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (hdenotes : encoded.Denotes reward) :
    ∀ index,
      ((certifiedIsolatedRootRewardParameters encoded) index).data.RootWithin
        (quittingRewardParameters reward index) := by
  intro index
  exact hdenotes ((quittingRewardTableVariableList players).get index).1
    ((quittingRewardTableVariableList players).get index).2

/-- Execute strict raw exclusion recognition for certified isolated-root rewards. -/
def decideHasQuittingFiniteCalendarRawStrictExclusionAtIsolatedRoots
    (encoded : CertifiedIsolatedRootQuittingReward players) : Bool :=
  decideAtIsolatedRoots (certifiedIsolatedRootRewardParameters encoded)
    rawStrictExclusionParameterFormula

/-- The strict Boolean result is correct for every reward table denoted by the input. -/
theorem decideHasQuittingFiniteCalendarRawStrictExclusionAtIsolatedRoots_eq_true_iff
    [Nonempty (Fin players)]
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (hdenotes : encoded.Denotes reward) :
    decideHasQuittingFiniteCalendarRawStrictExclusionAtIsolatedRoots encoded = true ↔
      HasQuittingFiniteCalendarRawStrictExclusion reward := by
  rw [decideHasQuittingFiniteCalendarRawStrictExclusionAtIsolatedRoots,
    decideAtIsolatedRoots_eq_true_iff
      (certifiedIsolatedRootRewardParameters encoded)
      rawStrictExclusionParameterFormula (quittingRewardParameters reward)]
  · simp
  · exact certifiedIsolatedRootRewardParameters_denote encoded reward hdenotes

/-- Execute weak-subset raw exclusion recognition for certified isolated-root rewards. -/
def decideHasQuittingFiniteCalendarRawWeakSubsetExclusionAtIsolatedRoots
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (owners : Finset (Fin players)) : Bool :=
  decideAtIsolatedRoots (certifiedIsolatedRootRewardParameters encoded)
    (rawWeakSubsetExclusionParameterFormula owners)

/-- The weak-subset Boolean result is correct for every denoted reward table. -/
theorem decideHasQuittingFiniteCalendarRawWeakSubsetExclusionAtIsolatedRoots_eq_true_iff
    [Nonempty (Fin players)]
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (hdenotes : encoded.Denotes reward) (owners : Finset (Fin players)) :
    decideHasQuittingFiniteCalendarRawWeakSubsetExclusionAtIsolatedRoots
        encoded owners = true ↔
      HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners := by
  rw [decideHasQuittingFiniteCalendarRawWeakSubsetExclusionAtIsolatedRoots,
    decideAtIsolatedRoots_eq_true_iff
      (certifiedIsolatedRootRewardParameters encoded)
      (rawWeakSubsetExclusionParameterFormula owners)
      (quittingRewardParameters reward)]
  · simp
  · exact certifiedIsolatedRootRewardParameters_denote encoded reward hdenotes

/-- Execute raw group-exclusion recognition for certified isolated-root rewards. -/
def decideExistsQuittingFiniteCalendarRawGroupExclusionAtIsolatedRoots
    (encoded : CertifiedIsolatedRootQuittingReward players) : Bool :=
  decideAtIsolatedRoots (certifiedIsolatedRootRewardParameters encoded)
    rawGroupExclusionParameterFormula

/-- The group Boolean result is correct for every reward table denoted by the input. -/
theorem decideExistsQuittingFiniteCalendarRawGroupExclusionAtIsolatedRoots_eq_true_iff
    [Nonempty (Fin players)]
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (hdenotes : encoded.Denotes reward) :
    decideExistsQuittingFiniteCalendarRawGroupExclusionAtIsolatedRoots encoded = true ↔
      ∃ beta < 1,
        HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta := by
  rw [decideExistsQuittingFiniteCalendarRawGroupExclusionAtIsolatedRoots,
    decideAtIsolatedRoots_eq_true_iff
      (certifiedIsolatedRootRewardParameters encoded)
      rawGroupExclusionParameterFormula (quittingRewardParameters reward)]
  · simp
  · exact certifiedIsolatedRootRewardParameters_denote encoded reward hdenotes

end GameTheory
