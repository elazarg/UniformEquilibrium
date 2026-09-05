import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Reindexing a finitely supported stopping-time PMF -/

namespace Math.Probability

/-- Restrict a complete stopping time to the first `bound` dates, sending
unsupported later dates to the retained `Never` atom. -/
def finiteStoppingTimeEncode (bound : ℕ) : Option ℕ → Option (Fin bound)
  | none => none
  | some time => if htime : time < bound then some ⟨time, htime⟩ else none

/-- Include a bounded stopping time into the complete stopping-time space. -/
def finiteStoppingTimeDecode (bound : ℕ) : Option (Fin bound) → Option ℕ :=
  Option.map Fin.val

/-- A law with no atoms at or after `bound` can be reindexed as a PMF on
`Option (Fin bound)`, preserving its Never atom exactly. -/
theorem exists_finiteStoppingTimePMF_map_eq
    (law : PMF (Option ℕ)) (bound : ℕ)
    (hsupport : ∀ time, bound ≤ time → law (some time) = 0) :
    ∃ finiteLaw : PMF (Option (Fin bound)),
      finiteLaw.map (finiteStoppingTimeDecode bound) = law ∧
      finiteLaw none = law none := by
  let finiteLaw := law.map (finiteStoppingTimeEncode bound)
  refine ⟨finiteLaw, ?_, ?_⟩
  · change (law.map (finiteStoppingTimeEncode bound)).map
        (finiteStoppingTimeDecode bound) = law
    rw [PMF.map_comp]
    apply PMF.ext
    intro choice
    rw [PMF.map_apply]
    conv_rhs => rw [← PMF.map_id law]
    rw [PMF.map_apply]
    apply tsum_congr
    intro source
    by_cases heq : finiteStoppingTimeDecode bound
        (finiteStoppingTimeEncode bound source) = source
    · simp [heq, Function.comp_apply]
    · cases source with
      | none => simp [finiteStoppingTimeEncode, finiteStoppingTimeDecode] at heq
      | some time =>
          have hlate : bound ≤ time := by
            by_contra hnot
            have hlt : time < bound := Nat.lt_of_not_ge hnot
            simp [finiteStoppingTimeEncode, finiteStoppingTimeDecode, hlt] at heq
          rw [hsupport time hlate]
          simp
  · change law.map (finiteStoppingTimeEncode bound) none = law none
    rw [PMF.map_apply]
    rw [tsum_eq_single none]
    · simp [finiteStoppingTimeEncode]
    · intro source hsource
      cases source with
      | none => exact (hsource rfl).elim
      | some time =>
          by_cases htime : time < bound
          · simp [finiteStoppingTimeEncode, htime]
          · rw [hsupport time (Nat.le_of_not_gt htime)]
            simp

end Math.Probability
