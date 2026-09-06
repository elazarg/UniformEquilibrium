import MathUE.ProbabilityMassFunction.FiniteStoppingTimeMenu
import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawCensor
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingGame

/-! # Realizing finite-support stopping laws in finite timing menus -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem exists_finiteDeadlineTimingLaws_of_censoredLaws
    (laws : ι → PMF (Option ℕ)) (cutoff deadline : ℕ)
    (hdeadline : cutoff < deadline) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw (laws who) cutoff := by
  classical
  have hsupport (who : ι) (time : ℕ) (htime : deadline ≤ time) :
      censorLateFiniteStoppingLaw (laws who) cutoff (some time) = 0 := by
    have hnot : some time ∉ stoppingLawFinitePrefix cutoff := by
      simp
      omega
    have hnotSupport : some time ∉
        (censorLateFiniteStoppingLaw (laws who) cutoff).support :=
      fun hmem => hnot
        (censorLateFiniteStoppingLaw_support_subset (laws who) cutoff hmem)
    by_contra hne
    exact hnotSupport (by simpa [PMF.mem_support_iff] using hne)
  have hexists (who : ι) : ∃ law : PMF (Option (Fin deadline)),
      law.map (finiteStoppingTimeDecode deadline) =
        censorLateFiniteStoppingLaw (laws who) cutoff := by
    obtain ⟨law, hlaw, _⟩ := exists_finiteStoppingTimePMF_map_eq
      (censorLateFiniteStoppingLaw (laws who) cutoff) deadline (hsupport who)
    exact ⟨law, hlaw⟩
  choose mixed hmixed using hexists
  refine ⟨mixed, fun who => ?_⟩
  rw [quittingFiniteDeadlineTimingLaw, CompactStoppingLaw.toPMF_ofPMF]
  have hmaps : (mixed who).map quittingFiniteDeadlineTimingActionTime =
      (mixed who).map (finiteStoppingTimeDecode deadline) := by
    congr 1
    funext action
    cases action <;> rfl
  rw [hmaps, hmixed who]

omit [DecidableEq ι] [Nonempty ι] in
/-- A finite-support stopping-law profile realized on a deadline has exactly
the canonical stopping-law behavioral profile. -/
theorem finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (laws : ι → PMF (Option ℕ))
    (hlaws : ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF = laws who) :
    quittingFiniteDeadlineTimingProfile reward deadline mixed =
      quittingStoppingLawProfile reward laws := by
  funext who
  unfold quittingFiniteDeadlineTimingProfile quittingCompactStoppingLawProfile
    quittingStoppingLawProfile
  rw [← hlaws who]

end GameTheory
