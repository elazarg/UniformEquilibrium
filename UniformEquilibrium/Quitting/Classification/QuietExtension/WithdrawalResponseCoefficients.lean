import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPointwiseDomination

/-! # Actual raw withdrawal response-row coefficients

The finite row indexing and literal advance/outside coefficients have one owner.
No rational optimizer, fixed-target or uniformization consumer is imported here.
-/

noncomputable section

namespace GameTheory

/-- The actual Never row and the two nonempty-coalition response row families. -/
abbrev WithdrawalResponseRow (ι : Type) :=
  Option (Bool × {coalition : Finset ι // coalition.Nonempty})

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
def withdrawalAdvanceCoefficient
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    WithdrawalResponseRow ι → ι → ℝ
  | none, i => reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  | some (false, coalition), i =>
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ (some i)
  | some (true, coalition), i =>
      reward ⟨cappedClockChildCoalition (insert i coalition.1),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i coalition.1)⟩
          (some i) -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ (some i)

omit [Fintype ι] in
def withdrawalOutsideCoefficient
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) :
    WithdrawalResponseRow ι → ℝ
  | none => reward ⟨{none}, Finset.singleton_nonempty none⟩ none
  | some (false, coalition) =>
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ none
  | some (true, coalition) =>
      reward ⟨cappedClockJoinedCoalition coalition.1,
          cappedClockJoinedCoalition_nonempty coalition.1⟩ none -
        reward ⟨cappedClockChildCoalition coalition.1,
          cappedClockChildCoalition_nonempty coalition.2⟩ none

end GameTheory
