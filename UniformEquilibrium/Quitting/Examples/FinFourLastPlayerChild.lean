import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockOriginalCoalitionRows

/-! # Actual Fin4 deletion of player index 3

A single neutral owner for the literal child enumeration and original source
coalition images shared by the strict patient and deadline examples.
-/

noncomputable section

namespace GameTheory.FinFourLastPlayerChild

open scoped BigOperators

abbrev Child := QuittingChildPlayer (fun who : Fin 4 => who = 3)

abbrev child (index : Fin 3) : Child := ⟨index.castSucc, by
  change index.castSucc ≠ (3 : Fin 4)
  intro hequal
  have hvalue : index.val = 3 := congrArg Fin.val hequal
  exact (Nat.ne_of_lt index.isLt) hvalue⟩

instance : Nonempty Child := ⟨child 0⟩

abbrev outside : {who : Fin 4 // who = 3} := ⟨3, rfl⟩

instance : Nonempty {who : Fin 4 // who = 3} := ⟨outside⟩

/-- The actual child-plus-outsider restriction in the canonical source coordinates. -/
abbrev childReward (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :=
  quittingChildWithOutsiderReward table (· = 3) outside

/-- The actual displayed child coalition is evaluated at its original player set. -/
theorem childReward_childCoalition
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) (who : Child) :
    childReward table
        ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ (some who) =
      table ⟨A.map (Function.Embedding.subtype (p := fun who : Fin 4 => who ≠ 3)),
        Finset.map_nonempty.mpr hA⟩ who.1 := by
  simp only [childReward, quittingChildWithOutsiderReward_apply_original,
    quittingChildWithOutsiderOriginalEmbedding_childCoalition,
    quittingChildWithOutsiderOriginalEmbedding_some]

/-- An image by the literal subtype value removes embedding coercions from finite tables. -/
theorem childReward_childCoalition_image
    (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (A : Finset Child) (hA : A.Nonempty) (who : Child) :
    childReward table
        ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ (some who) =
      table ⟨A.image (fun player : Child => player.1), hA.image (fun player => player.1)⟩
        who.1 := by
  simpa only [quittingChildWithOutsiderOriginalEmbedding_some] using
    quittingChildWithOutsiderReward_childCoalition_image table (· = 3) outside A hA
      (some who)

theorem sum_child (function : Child → ℝ) :
    ∑ who, function who = function (child 0) + function (child 1) + function (child 2) := by
  rw [show (Finset.univ : Finset Child) = {child 0, child 1, child 2} by decide]
  simp [child, add_assoc]

abbrev coalition : Fin 7 → Finset Child :=
  ![{child 0}, {child 1}, {child 0, child 1}, {child 2},
    {child 0, child 2}, {child 1, child 2}, {child 0, child 1, child 2}]

theorem coalition_nonempty (index : Fin 7) : (coalition index).Nonempty := by
  fin_cases index <;> decide

theorem exists_coalition_index (A : Finset Child) (hA : A.Nonempty) :
    ∃ index, A = coalition index := by
  exact (by decide : ∀ A : Finset Child, A.Nonempty → ∃ index, A = coalition index) A hA

end GameTheory.FinFourLastPlayerChild

