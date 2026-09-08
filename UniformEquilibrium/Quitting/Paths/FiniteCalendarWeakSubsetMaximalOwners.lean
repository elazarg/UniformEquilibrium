import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates

/-! # Maximal owner set for weak finite-calendar exclusion -/

noncomputable section

namespace GameTheory

variable {players : Type} [Fintype players] [DecidableEq players]

/-- The maximal set of players whose own singleton reward is nonnegative. -/
def quittingNonnegativeSingletonOwners
    (reward : {S : Finset players // S.Nonempty} → Payoff players) : Finset players :=
  Finset.univ.filter fun who =>
    0 ≤ reward (quittingSingletonTerminal who) who

omit [DecidableEq players] in
@[simp]
theorem mem_quittingNonnegativeSingletonOwners
    (reward : {S : Finset players // S.Nonempty} → Payoff players) (who : players) :
    who ∈ quittingNonnegativeSingletonOwners reward ↔
      0 ≤ reward (quittingSingletonTerminal who) who := by
  simp [quittingNonnegativeSingletonOwners]

/-- A weak-exclusion owner set can be enlarged to every player having a
nonnegative own-singleton reward. -/
theorem hasQuittingFiniteCalendarRawWeakSubsetExclusion_maximal
    (reward : {S : Finset players // S.Nonempty} → Payoff players)
    (owners : Finset players)
    (hexclusion : HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners) :
    HasQuittingFiniteCalendarRawWeakSubsetExclusion reward
      (quittingNonnegativeSingletonOwners reward) := by
  refine ⟨fun who hwho => (mem_quittingNonnegativeSingletonOwners reward who).mp hwho,
    fun profile => ?_⟩
  obtain ⟨who, hwho, hpayoff⟩ := hexclusion.2 profile
  exact ⟨who,
    (mem_quittingNonnegativeSingletonOwners reward who).mpr
      (hexclusion.1 who hwho),
    hpayoff⟩

/-- Some nonempty weak-exclusion owner set exists exactly when the maximal
nonnegative-singleton owner set is itself nonempty and works. -/
theorem exists_hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_maximal
    (reward : {S : Finset players // S.Nonempty} → Payoff players) :
    (∃ owners : Finset players, owners.Nonempty ∧
        HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners) ↔
      (quittingNonnegativeSingletonOwners reward).Nonempty ∧
        HasQuittingFiniteCalendarRawWeakSubsetExclusion reward
          (quittingNonnegativeSingletonOwners reward) := by
  constructor
  · rintro ⟨owners, howners, hexclusion⟩
    refine ⟨?_, hasQuittingFiniteCalendarRawWeakSubsetExclusion_maximal
      reward owners hexclusion⟩
    obtain ⟨who, hwho⟩ := howners
    exact ⟨who, (mem_quittingNonnegativeSingletonOwners reward who).mpr
      (hexclusion.1 who hwho)⟩
  · rintro ⟨howners, hexclusion⟩
    exact ⟨quittingNonnegativeSingletonOwners reward, howners, hexclusion⟩

end GameTheory
