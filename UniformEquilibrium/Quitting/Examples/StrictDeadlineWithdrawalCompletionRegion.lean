import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalCompletionMargins
import UniformEquilibrium.Quitting.Examples.StrictDeadlineWithdrawalQuietExtension
import Mathlib.Analysis.Convex.Basic

/-! # A nonempty open convex completion region for every arbitrary child table

The four nonsingleton pure-child outsider entries are chosen strictly above
their actual future bounds. The seven joined outsider entries are then chosen
strictly below their actual joining bounds. These are eleven distinct final
reward coordinates. All sixteen singleton entries and all thirty-three free
child-recipient nonsingleton entries remain exactly fixed. The resulting
actual games have source-produced uniform-equilibrium payoffs.

This region need not lie in the small reward ball and need not preserve the
advancing-only exclusion witnesses. Not every outsider completion is feasible.
-/

noncomputable section

namespace GameTheory.StrictDeadlineWithdrawal

open FinFourLastPlayerChild GuardedCrossedResponseExamples _root_.Set

def completionRegion (free : ChildCollisionSpace) : Set OutsiderCollisionSpace :=
  (⋂ index : Fin 7, (futureMarginAffine free index) ⁻¹' Ioi 0) ∩
    (⋂ index : Fin 7, (joiningMarginAffine free index) ⁻¹' Ioi 0)

theorem mem_completionRegion_iff (free : ChildCollisionSpace) (outside : OutsiderCollisionSpace) :
    outside ∈ completionRegion free ↔
      (∀ index, 0 < futureMarginAffine free index outside) ∧
        (∀ index, 0 < joiningMarginAffine free index outside) := by
  simp only [completionRegion, mem_inter_iff, mem_iInter, mem_preimage, mem_Ioi]

theorem isOpen_completionRegion (free : ChildCollisionSpace) :
    IsOpen (completionRegion free) :=
  (isOpen_iInter_of_finite fun index =>
    isOpen_Ioi.preimage (futureMarginAffine free index).continuous_of_finiteDimensional).inter
    (isOpen_iInter_of_finite fun index =>
      isOpen_Ioi.preimage (joiningMarginAffine free index).continuous_of_finiteDimensional)

theorem convex_completionRegion (free : ChildCollisionSpace) : Convex ℝ (completionRegion free) :=
  (convex_iInter fun index =>
    Convex.affine_preimage (futureMarginAffine free index) (convex_Ioi 0)).inter
    (convex_iInter fun index =>
      Convex.affine_preimage (joiningMarginAffine free index) (convex_Ioi 0))

/-- The region is exactly strict actual N/F/J feasibility for these fixed raw weights. -/
theorem mem_completionRegion_iff_strict_slacks
    (free : ChildCollisionSpace) (outside : OutsiderCollisionSpace) :
    outside ∈ completionRegion free ↔
      0 < neverSlack (completionReward free outside) ∧
        (∀ A hA, 0 < futureSlack (completionReward free outside) A hA) ∧
        (∀ A hA, 0 < joiningSlack (completionReward free outside) A hA) := by
  rw [mem_completionRegion_iff]
  constructor
  · rintro ⟨hfuture, hjoining⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [completionReward_neverSlack_eq]
      norm_num
    · intro A hA
      obtain ⟨index, rfl⟩ := exists_coalition_index A hA
      simpa only [futureMarginAffine_apply] using hfuture index
    · intro A hA
      obtain ⟨index, rfl⟩ := exists_coalition_index A hA
      simpa only [joiningMarginAffine_apply] using hjoining index
  · rintro ⟨_, hfuture, hjoining⟩
    exact ⟨fun index => by
      rw [futureMarginAffine_apply]
      exact hfuture _ _, fun index => by
      rw [joiningMarginAffine_apply]
      exact hjoining _ _⟩

/-- Singletons keep their fixed source entry; other child entries exceed the future bound by one. -/
def assignedChildOutside (free : ChildCollisionSpace) (index : Fin 7) : ℝ :=
  if (sourceChildTerminal index).1.card = 1 then reward (sourceChildTerminal index) 3
  else reward ⟨{3}, Finset.singleton_nonempty 3⟩ 3 - futureRight free index + 1

/-- Explicit final values for the eleven distinct nonsingleton outsider coordinates. -/
def feasibleOutside (free : ChildCollisionSpace) : OutsiderCollisionSpace :=
  fun terminal => match coalitionCode terminal.1.1 with
    | 3 => assignedChildOutside free 2
    | 5 => assignedChildOutside free 4
    | 6 => assignedChildOutside free 5
    | 7 => assignedChildOutside free 6
    | 9 => assignedChildOutside free 0 + joiningRight free 0 - 1
    | 10 => assignedChildOutside free 1 + joiningRight free 1 - 1
    | 11 => assignedChildOutside free 2 + joiningRight free 2 - 1
    | 12 => assignedChildOutside free 3 + joiningRight free 3 - 1
    | 13 => assignedChildOutside free 4 + joiningRight free 4 - 1
    | 14 => assignedChildOutside free 5 + joiningRight free 5 - 1
    | 15 => assignedChildOutside free 6 + joiningRight free 6 - 1
    | _ => 0

private theorem feasibleOutside_childValue (free : ChildCollisionSpace) (index : Fin 7) :
    completionReward free (feasibleOutside free) (sourceChildTerminal index) 3 =
      assignedChildOutside free index := by
  fin_cases index
  all_goals norm_num +decide [completionReward, completionRewardAffine, feasibleOutside,
    assignedChildOutside, sourceChildTerminal, coalition, child, coalitionCode]

private theorem feasibleOutside_joinedValue (free : ChildCollisionSpace) (index : Fin 7) :
    completionReward free (feasibleOutside free) (sourceJoinedTerminal index) 3 =
      assignedChildOutside free index + joiningRight free index - 1 := by
  fin_cases index
  all_goals norm_num +decide [completionReward, completionRewardAffine, feasibleOutside,
    sourceJoinedTerminal, sourceChildTerminal, coalition, child, coalitionCode]

theorem feasibleOutside_futureSlack_pos (free : ChildCollisionSpace) (index : Fin 7) :
    0 < futureSlack (completionReward free (feasibleOutside free))
      (coalition index) (coalition_nonempty index) := by
  by_cases hsingle : (sourceChildTerminal index).1.card = 1
  · rw [completionReward_futureSingletonSlack_eq free _ index hsingle]
    fin_cases index <;> norm_num [futureSlacks]
  · rw [completionReward_futureSlack_formula, feasibleOutside_childValue,
      assignedChildOutside, ite_eq_right hsingle]
    linarith

/-- Every actual joining margin of the constructed completion is exactly one. -/
theorem feasibleOutside_joiningSlack_eq_one (free : ChildCollisionSpace) (index : Fin 7) :
    joiningSlack (completionReward free (feasibleOutside free))
      (coalition index) (coalition_nonempty index) = 1 := by
  rw [completionReward_joiningSlack_formula, feasibleOutside_joinedValue,
    feasibleOutside_childValue]
  ring

theorem feasibleOutside_mem_completionRegion (free : ChildCollisionSpace) :
    feasibleOutside free ∈ completionRegion free := by
  apply (mem_completionRegion_iff free _).mpr
  constructor
  · intro index
    rw [futureMarginAffine_apply]
    exact feasibleOutside_futureSlack_pos free index
  · intro index
    rw [joiningMarginAffine_apply, feasibleOutside_joiningSlack_eq_one]
    norm_num

theorem completionRegion_open_convex_nonempty (free : ChildCollisionSpace) :
    IsOpen (completionRegion free) ∧ Convex ℝ (completionRegion free) ∧
      (completionRegion free).Nonempty :=
  ⟨isOpen_completionRegion free, convex_completionRegion free,
    feasibleOutside free, feasibleOutside_mem_completionRegion free⟩

/-- This is a canonical actual certificate with freshly computed floors. -/
def completionCertificate (free : ChildCollisionSpace) (outside : OutsiderCollisionSpace)
    (hregion : outside ∈ completionRegion free) :
    DeadlineWithdrawalRewardCertificate (childReward (completionReward free outside)) :=
  certificateOfSlacks (completionReward free outside)
    ((mem_completionRegion_iff_strict_slacks free outside).mp hregion).1.le
    (fun A hA => (((mem_completionRegion_iff_strict_slacks free outside).mp hregion).2.1 A hA).le)
    (fun A hA => (((mem_completionRegion_iff_strict_slacks free outside).mp hregion).2.2 A hA).le)

theorem completionReward_exists_uniformPayoff (free : ChildCollisionSpace)
    (outside : OutsiderCollisionSpace) (hregion : outside ∈ completionRegion free) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame (completionReward free outside)).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_deadlineWithdrawalFamily
    (· = 3) (completionReward free outside)
    (certificateFamily _ (completionCertificate free outside hregion))

/-- For every arbitrary signed 33-vector, an actual completion and fixed UE target are produced. -/
theorem exists_actualCompletion_uniformPayoff (free : ChildCollisionSpace) :
    ∃ (outside : OutsiderCollisionSpace) (payoff : Payoff (Fin 4)),
      outside ∈ completionRegion free ∧
      (∀ coordinate : ChildCollisionCoordinate,
        completionReward free outside coordinate.1.1 coordinate.1.2 = free coordinate) ∧
      (∀ owner who, completionReward free outside ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
        reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who) ∧
      (quittingGame (completionReward free outside)).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hpayoff⟩ := completionReward_exists_uniformPayoff free
    (feasibleOutside free) (feasibleOutside_mem_completionRegion free)
  exact ⟨feasibleOutside free, payoff, feasibleOutside_mem_completionRegion free,
    completionReward_child_coordinate free _, completionReward_singleton free _, hpayoff⟩

end GameTheory.StrictDeadlineWithdrawal
