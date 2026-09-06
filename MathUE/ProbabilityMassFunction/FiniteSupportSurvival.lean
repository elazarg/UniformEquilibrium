import MathUE.ProbabilityMassFunction.StoppingLawFiniteTail
import MathUE.Probability.StoppingLawReconstruction

/-! # Survival beyond finite stopping-law support -/

noncomputable section

namespace Math.Probability

open DiscreteHazard

/-- Beyond its finite support, a stopping law's inclusive survival is exactly
its retained Never atom. -/
theorem stoppingLawSurvival_eq_none_of_support_prefix
    (law : PMF (Option ℕ)) (cutoff time : ℕ) (htime : cutoff < time)
    (hsupport : law.support ⊆ ↑(stoppingLawFinitePrefix cutoff)) :
    StoppingLaw.survival law time = (law none).toReal := by
  have htotal : (law none).toReal +
      ∑ date ∈ Finset.range time, (law (some date)).toReal = 1 := by
    rw [← StoppingLaw.none_add_tsum_finiteMass law]
    congr 1
    symm
    apply tsum_eq_sum
    intro date hdate
    have hnot : some date ∉ stoppingLawFinitePrefix cutoff := by
      rw [some_mem_stoppingLawFinitePrefix]
      have hle : time ≤ date := Nat.le_of_not_gt (by simpa using hdate)
      omega
    have hzero : law (some date) = 0 := by
      by_contra hne
      exact hnot (hsupport (by simpa [PMF.mem_support_iff] using hne))
    simp [StoppingLaw.finiteMass, hzero]
  unfold StoppingLaw.survival StoppingLaw.finiteMass
  linarith

end Math.Probability
