import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineReplyCap
import UniformEquilibrium.ProofView.Concepts.Existence.NashExistenceMixed
import MathUE.ProbabilityMassFunction.Simplex

/-! # Actual finite-menu punishment values

The infimum is over independent probability laws on the literal finite timing
menu. Compact simplexes are used only to prove attainment.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) (who : ι) :
    Fintype ((quittingFiniteDeadlineTimingGame reward deadline).Strategy who) := by
  change Fintype (QuittingFiniteDeadlineTimingAction deadline)
  infer_instance

/-- Min-max value against the finite date-or-Never reply menu. The responder's
coordinate in `mixed` is overwritten in every reply comparison. -/
def quittingFiniteMenuPunishmentValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) (who : ι) : ℝ :=
  ⨅ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
    quittingFiniteDeadlineReplyCap reward deadline mixed who

omit [DecidableEq ι] in
private theorem profileFromMixedSimplex_pmfCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingFiniteDeadlineTimingGame reward deadline).profileFromMixedSimplex
      (fun player ↦ Math.ProbabilityMassFunction.stdSimplexEquiv (mixed player)) = mixed := by
  funext player
  apply Math.ProbabilityMassFunction.toVector_injective
  funext action
  dsimp [Math.ProbabilityMassFunction.toVector, KernelGame.profileFromMixedSimplex,
    KernelGame.profileFromWeights, Math.ProbabilityMassFunction.stdSimplexEquiv]
  exact KernelGame.realToPmf_toReal _ _ _ action

theorem continuous_quittingFiniteDeadlineReplyCap_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) (who : ι) :
    Continuous (fun mixed : MixedSimplex ι
        (fun _ ↦ QuittingFiniteDeadlineTimingAction deadline) ↦
      quittingFiniteDeadlineReplyCap reward deadline
        ((quittingFiniteDeadlineTimingGame reward deadline).profileFromMixedSimplex mixed)
        who) := by
  unfold quittingFiniteDeadlineReplyCap
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro action _
  simp_rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU]
  exact (quittingFiniteDeadlineTimingGame reward deadline
    ).continuous_mixedExtension_eu_update_profileFromMixedSimplex who action

/-- The finite-menu punishment minimum is attained by actual independent laws. -/
theorem exists_quittingFiniteMenuPunishmentValue_minimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) (who : ι) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      quittingFiniteDeadlineReplyCap reward deadline mixed who =
        quittingFiniteMenuPunishmentValue reward deadline who ∧
      ∀ other, quittingFiniteMenuPunishmentValue reward deadline who ≤
        quittingFiniteDeadlineReplyCap reward deadline other who := by
  let menu := QuittingFiniteDeadlineTimingAction deadline
  let profile := (quittingFiniteDeadlineTimingGame reward deadline).profileFromMixedSimplex
  letI : Nonempty (MixedSimplex ι (fun _ ↦ menu)) :=
    ⟨fun _ ↦ Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)⟩
  obtain ⟨point, _, hminimum⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (MixedSimplex ι (fun _ ↦ menu))).Nonempty)
    (continuous_quittingFiniteDeadlineReplyCap_simplex reward deadline who).continuousOn
  have hminimumActual (other : ι → PMF menu) :
      quittingFiniteDeadlineReplyCap reward deadline (profile point) who ≤
        quittingFiniteDeadlineReplyCap reward deadline other who := by
    have h := hminimum (Set.mem_univ
      (fun player ↦ Math.ProbabilityMassFunction.stdSimplexEquiv (other player)))
    change quittingFiniteDeadlineReplyCap reward deadline (profile point) who ≤
      quittingFiniteDeadlineReplyCap reward deadline
        ((quittingFiniteDeadlineTimingGame reward deadline).profileFromMixedSimplex
          (fun player ↦ Math.ProbabilityMassFunction.stdSimplexEquiv (other player))) who at h
    rw [profileFromMixedSimplex_pmfCoordinates] at h
    exact h
  have hbound : BddBelow (Set.range fun other : ι → PMF menu ↦
      quittingFiniteDeadlineReplyCap reward deadline other who) := by
    refine ⟨quittingFiniteDeadlineReplyCap reward deadline (profile point) who, ?_⟩
    rintro _ ⟨other, rfl⟩
    exact hminimumActual other
  refine ⟨profile point, ?_, ?_⟩
  · apply le_antisymm
    · exact le_ciInf hminimumActual
    · exact ciInf_le hbound (profile point)
  · intro other
    exact ciInf_le hbound other

end GameTheory
