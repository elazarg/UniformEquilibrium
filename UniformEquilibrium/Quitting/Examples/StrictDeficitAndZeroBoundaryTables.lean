import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates

/-!
# Strict-deficit and zero boundary tables

The first four-player table pays a player one exactly at that player's own
singleton and pays minus one otherwise.  Its aggregate terminal reward is
nonpositive, so every actual profile has a coordinate at most zero and hence
has singleton deficit at least one.  The identically zero table contrasts the
strict boundary: positive strict deficit fails at all-Continue, while group
and every nonempty weak-subset exclusion hold with equality.
-/

noncomputable section

namespace GameTheory.StrictDeficitAndZeroBoundaryTables

/-- A player receives one exactly when that player is the sole quitter, and
minus one at every other nonempty quitting coalition. -/
def strictDeficitReward :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who => if terminal.1 = {who} then 1 else -1

/-- The aggregate reward of every nonempty terminal coalition is
nonpositive. -/
theorem sum_strictDeficitReward_nonpos
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    ∑ who, strictDeficitReward terminal who ≤ 0 := by
  simp only [strictDeficitReward, Fin.sum_univ_four]
  split_ifs <;> simp_all
  norm_num

/-- Every actual profile under the strict table has nonpositive aggregate
terminal payoff. -/
theorem sum_terminalPayoff_strictDeficitReward_nonpos
    (profile : (quittingGame strictDeficitReward).BehaviorProfile) :
    ∑ who, quittingTerminalPayoff strictDeficitReward profile who ≤ 0 := by
  unfold quittingTerminalPayoff
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro terminal _
  rw [← Finset.mul_sum]
  exact mul_nonpos_of_nonneg_of_nonpos
    (quittingAbsorbedMassLimit_nonneg strictDeficitReward profile terminal)
    (sum_strictDeficitReward_nonpos terminal)

/-- The strict table satisfies the actual strict singleton-deficit predicate
with the literal packet margin one. -/
theorem strictDeficitReward_has_actualStrictSingletonDeficit :
    HasQuittingActualStrictSingletonDeficit strictDeficitReward 1 := by
  intro profile
  have hsum := sum_terminalPayoff_strictDeficitReward_nonpos profile
  have hexists : ∃ who,
      quittingTerminalPayoff strictDeficitReward profile who ≤ 0 := by
    by_contra hnone
    push Not at hnone
    have hsumPos : 0 < ∑ who,
        quittingTerminalPayoff strictDeficitReward profile who := by
      apply Finset.sum_pos'
      · intro who _
        exact (hnone who).le
      · exact ⟨0, Finset.mem_univ 0, hnone 0⟩
    linarith
  obtain ⟨who, hwho⟩ := hexists
  refine ⟨who, ?_⟩
  simpa [strictDeficitReward, quittingSingletonTerminal] using hwho

/-- The identically zero four-player quitting reward table. -/
def zeroReward :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun _ _ => 0

/-- Every actual terminal payoff under the zero table is exactly zero. -/
theorem terminalPayoff_zeroReward_eq_zero
    (profile : (quittingGame zeroReward).BehaviorProfile) :
    quittingTerminalPayoff zeroReward profile = 0 := by
  funext who
  unfold quittingTerminalPayoff
  simp [zeroReward]

/-- No positive margin satisfies the actual strict singleton-deficit
predicate for the zero table; the all-Continue profile is the boundary
witness. -/
theorem zeroReward_not_has_actualStrictSingletonDeficit
    (gap : ℝ) (hgap : 0 < gap) :
    ¬ HasQuittingActualStrictSingletonDeficit zeroReward gap := by
  intro hdeficit
  obtain ⟨who, hwho⟩ := hdeficit (quittingAlwaysContinueProfile zeroReward)
  rw [congrFun (terminalPayoff_zeroReward_eq_zero
    (quittingAlwaysContinueProfile zeroReward)) who] at hwho
  simp [zeroReward] at hwho
  linarith

/-- Equivalently, the zero table has no positive actual strict-deficit
parameter. -/
theorem zeroReward_not_exists_positive_actualStrictSingletonDeficit :
    ¬ ∃ gap > 0, HasQuittingActualStrictSingletonDeficit zeroReward gap := by
  rintro ⟨gap, hgap, hdeficit⟩
  exact zeroReward_not_has_actualStrictSingletonDeficit gap hgap hdeficit

/-- The zero table satisfies nonconcentrated group exclusion with the literal
cap one half, and its weighted surplus is exactly zero. -/
theorem zeroReward_has_actualNonconcentratedGroupExclusion :
    HasQuittingActualNonconcentratedGroupExclusion zeroReward ((1 : ℝ) / 2) := by
  intro profile
  refine ⟨fun _ => (1 : ℝ) / 4, ?_, ?_, ?_, ?_⟩
  · intro who
    norm_num
  · norm_num [Fin.sum_univ_four]
  · intro who
    norm_num
  · rw [terminalPayoff_zeroReward_eq_zero profile]
    simp [zeroReward]

/-- Every nonempty player subset witnesses actual weak exclusion for the zero
table, with equality at every selected coordinate. -/
theorem zeroReward_has_actualWeakSubsetExclusion
    (owners : Finset (Fin 4)) (howners : owners.Nonempty) :
    HasQuittingActualWeakSubsetExclusion zeroReward owners := by
  refine ⟨?_, ?_⟩
  · intro who _
    simp [zeroReward]
  · intro profile
    refine ⟨howners.choose, howners.choose_spec, ?_⟩
    rw [congrFun (terminalPayoff_zeroReward_eq_zero profile) howners.choose]
    simp [zeroReward]

end GameTheory.StrictDeficitAndZeroBoundaryTables
