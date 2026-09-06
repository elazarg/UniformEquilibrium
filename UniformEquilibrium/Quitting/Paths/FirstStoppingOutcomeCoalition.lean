import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

namespace GameTheory

/-- A supplied coalition is the first stopping outcome when all its members
stop at one date and every outsider stops strictly later (possibly Never). -/
theorem quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (times : ι → Option ℕ) (coalition : Finset ι) (hne : coalition.Nonempty)
    (time : ℕ) (hinside : ∀ player ∈ coalition, times player = some time)
    (houtside : ∀ player ∉ coalition,
      quittingStoppingTimeValue (some time) < quittingStoppingTimeValue (times player)) :
    letI : Nonempty ι := ⟨hne.choose⟩
    quittingFirstStoppingOutcome times = some ⟨coalition, hne⟩ := by
  letI : Nonempty ι := ⟨hne.choose⟩
  have hmin : quittingEarliestStoppingValue times = (time : WithTop ℕ) := by
    unfold quittingEarliestStoppingValue
    apply le_antisymm
    · have hle := Finset.inf_le
          (f := fun player ↦ quittingStoppingTimeValue (times player))
          (Finset.mem_univ hne.choose)
      rw [hinside hne.choose hne.choose_spec] at hle
      simpa [quittingStoppingTimeValue] using hle
    · apply Finset.le_inf
      intro player _
      by_cases hplayer : player ∈ coalition
      · rw [hinside player hplayer]
        simp [quittingStoppingTimeValue]
      · exact (houtside player hplayer).le
  have hcoalition : quittingEarliestStoppingCoalition times = coalition := by
    ext player
    simp only [quittingEarliestStoppingCoalition, Finset.mem_filter,
      Finset.mem_univ, true_and, hmin]
    constructor
    · intro heq
      by_contra hplayer
      exact (ne_of_gt (houtside player hplayer)) (by
        simpa [quittingStoppingTimeValue] using heq)
    · intro hplayer
      rw [hinside player hplayer]
      rfl
  unfold quittingFirstStoppingOutcome
  rw [hmin, if_neg (by simp)]
  exact congrArg some (Subtype.ext hcoalition)

end GameTheory
