import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Paths.PureTimeMembershipToggleObstruction
import MathUE.Finset.FinFourNonemptyCoalitions

/-! # Literal fifteen-coalition membership-toggle owners and exact gains

The arrays are in nonempty coalition bitmask order. Actual reward identities
supply the canonical complete deterministic-clock obstruction; arbitrary
hidden later clocks and Never are retained by that existing consumer.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open Math.Finset

/-- The printed profitable toggle owner for masks 1 through 15. -/
def halfCeilingToggleOwner (row : Fin 15) : Fin 4 :=
  ![1, 0, 2, 0, 3, 2, 0, 0, 3, 2, 0, 0, 2, 3, 0] row

/-- The corresponding exact reward gain, not only a lower bound of one. -/
def halfCeilingToggleGain (row : Fin 15) : ℝ :=
  ![1, 1, 3, 7 / 3, 8, 1, 6, 2, 3, 5, 6, 2, 9, 5, 6] row

/-- Members withdraw, nonmembers join the unchanged first coalition. -/
def halfCeilingToggledCoalition (row : Fin 15) : Finset (Fin 4) :=
  if halfCeilingToggleOwner row ∈ finFourCoalitionOfRow row then
    (finFourCoalitionOfRow row).erase (halfCeilingToggleOwner row)
  else insert (halfCeilingToggleOwner row) (finFourCoalitionOfRow row)

/-- Every advertised withdrawal leaves at least one other first quitter. -/
theorem halfCeilingToggledCoalition_nonempty (row : Fin 15) :
    (halfCeilingToggledCoalition row).Nonempty := by
  fin_cases row <;>
    norm_num +decide [halfCeilingToggledCoalition, halfCeilingToggleOwner, finFourCoalitionOfRow]

/-- Literal terminal table evaluation of all fifteen owner/gain entries. -/
theorem halfCeilingToggle_reward_difference (row : Fin 15) :
    halfCeilingReward
        ⟨halfCeilingToggledCoalition row, halfCeilingToggledCoalition_nonempty row⟩
        (halfCeilingToggleOwner row) -
      halfCeilingReward (finFourCoalitionRowEquiv row) (halfCeilingToggleOwner row) =
        halfCeilingToggleGain row := by
  fin_cases row <;>
    norm_num +decide [halfCeilingToggledCoalition, halfCeilingToggleOwner, halfCeilingToggleGain,
      finFourCoalitionRowEquiv, finFourCoalitionOfRow, halfCeilingReward, coalitionCode]

theorem halfCeilingToggleGain_one_le (row : Fin 15) : 1 ≤ halfCeilingToggleGain row := by
  fin_cases row <;> norm_num [halfCeilingToggleGain]

/-- The literal arrays produce the existing table-level full-clock certificate. -/
theorem halfCeiling_literalToggleGap_one :
    HasQuittingPureTimeMembershipToggleGap halfCeilingReward 1 := by
  constructor
  · exact ⟨0, by norm_num [halfCeilingReward, coalitionCode]⟩
  · intro coalition
    obtain ⟨row, rfl⟩ := finFourCoalitionRowEquiv.surjective coalition
    let owner := halfCeilingToggleOwner row
    have hgain := halfCeilingToggle_reward_difference row
    have hlower := halfCeilingToggleGain_one_le row
    by_cases hmember : owner ∈ finFourCoalitionOfRow row
    · have hremaining : ((finFourCoalitionOfRow row).erase owner).Nonempty := by
        simpa only [halfCeilingToggledCoalition, owner, ite_eq_left hmember]
          using halfCeilingToggledCoalition_nonempty row
      right
      refine ⟨owner, hmember, hremaining, ?_⟩
      change halfCeilingReward (finFourCoalitionRowEquiv row) owner + 1 ≤
        halfCeilingReward ⟨(finFourCoalitionOfRow row).erase owner, hremaining⟩ owner
      have htoggled : halfCeilingToggledCoalition row =
          (finFourCoalitionOfRow row).erase owner := by
        exact ite_eq_left hmember
      have hterminal :
          (⟨halfCeilingToggledCoalition row, halfCeilingToggledCoalition_nonempty row⟩ :
            {S : Finset (Fin 4) // S.Nonempty}) =
          ⟨(finFourCoalitionOfRow row).erase owner, hremaining⟩ := Subtype.ext htoggled
      rw [hterminal] at hgain
      change _ - _ = halfCeilingToggleGain row at hgain
      linarith
    · left
      refine ⟨owner, hmember, ?_⟩
      change halfCeilingReward (finFourCoalitionRowEquiv row) owner + 1 ≤
        halfCeilingReward
          ⟨insert owner (finFourCoalitionOfRow row),
            Finset.insert_nonempty owner (finFourCoalitionOfRow row)⟩ owner
      have htoggled : halfCeilingToggledCoalition row =
          insert owner (finFourCoalitionOfRow row) := by
        exact ite_eq_right hmember
      have hterminal :
          (⟨halfCeilingToggledCoalition row, halfCeilingToggledCoalition_nonempty row⟩ :
            {S : Finset (Fin 4) // S.Nonempty}) =
          ⟨insert owner (finFourCoalitionOfRow row),
            Finset.insert_nonempty owner (finFourCoalitionOfRow row)⟩ := Subtype.ext htoggled
      rw [hterminal] at hgain
      change _ - _ = halfCeilingToggleGain row at hgain
      linarith

/-- Never has actual payoff zero; player zero's date-zero solo replacement gains exactly one. -/
theorem halfCeiling_allNever_exact_solo_gain :
    quittingTerminalPayoff halfCeilingReward
        (Function.update
          (quittingPureTimeProfileBehavior halfCeilingReward (fun _ => none)) 0
          (quittingPureTimeBehaviorStrategy halfCeilingReward 0 (some 0))) 0 -
      quittingTerminalPayoff halfCeilingReward
        (quittingPureTimeProfileBehavior halfCeilingReward (fun _ => none)) 0 = 1 := by
  rw [← quittingPureTimeProfileBehavior_update,
    quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
    quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
    quittingFirstStoppingOutcome_all_never]
  have hfirst :
      quittingFirstStoppingOutcome
          (Function.update (fun _ : Fin 4 => none) 0 (some 0)) =
        some ⟨{0}, Finset.singleton_nonempty 0⟩ := by
    apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later (time := 0)
    · intro who hwho
      have heq : who = 0 := Finset.mem_singleton.mp hwho
      subst who
      simp only [Function.update_self]
    · intro who hwho
      have hne : who ≠ 0 := by simpa only [Finset.mem_singleton] using hwho
      simp only [Function.update_of_ne hne, quittingStoppingTimeValue]
      change (0 : ENat) < ⊤
      exact ENat.natCast_lt_top 0
  rw [hfirst]
  norm_num [quittingTerminalOutcomeReward, halfCeilingReward, coalitionCode]

end GameTheory.GuardedCrossedResponseExamples
