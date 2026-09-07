import UniformEquilibrium.Quitting.Paths.SparseWholePayoffFiniteMixture
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-! # Sparse finite stopping laws preserving the whole payoff vector -/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One finite stopping law can be sparsified inside its original support,
preserving every player's payoff against the current opponent laws. -/
theorem exists_sparseFiniteStoppingLaw_wholePayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → FinDist (Option ℕ)) (mixer : ι) :
    ∃ sparse : FinDist {choice // choice ∈ (laws mixer).supportFinset},
      Fintype.card {choice // sparse.prob choice ≠ 0} ≤
        Fintype.card ι + 1 ∧
      ∀ observer,
        quittingTerminalPayoff reward
            (quittingStoppingLawProfile reward (Function.update
              (fun who => (laws who).toPMF) mixer
              (sparse.map Subtype.val).toPMF)) observer =
          quittingTerminalPayoff reward
            (quittingStoppingLawProfile reward
              (fun who => (laws who).toPMF)) observer := by
  let profile := quittingStoppingLawProfile reward
    (fun who => (laws who).toPMF)
  obtain ⟨sparse, hcard, heq⟩ :=
    exists_sparseFiniteStoppingLawMixture_wholePayoff_eq reward profile mixer
      (quittingPureTimeBehaviorStrategy reward mixer) (laws mixer)
  refine ⟨sparse, hcard, ?_⟩
  intro observer
  let sparseLaw := (sparse.map Subtype.val).toPMF
  have hsparseProfile : quittingStoppingLawProfile reward (Function.update
      (fun who => (laws who).toPMF) mixer sparseLaw) =
      Function.update profile mixer
        (quittingStoppingLawBehaviorStrategy reward mixer sparseLaw) := by
    funext who
    by_cases hwho : who = mixer
    · subst who
      simp [quittingStoppingLawProfile]
    · simp [profile, quittingStoppingLawProfile, Function.update_of_ne hwho]
  have horiginalProfile : Function.update profile mixer
      (quittingStoppingLawBehaviorStrategy reward mixer (laws mixer).toPMF) =
      profile := by
    apply Function.update_eq_self
  rw [hsparseProfile,
    quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect]
  change (sparse.map Subtype.val).expect (fun choice =>
      quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingPureTimeBehaviorStrategy reward mixer choice)) observer) = _
  rw [FinDist.expect_map]
  have hsparseAffine :=
    quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect
      reward profile mixer observer
        (sparse.map fun choice =>
          quittingPureTimeBehaviorStrategy reward mixer choice.1)
  rw [FinDist.expect_map] at hsparseAffine
  rw [← hsparseAffine]
  rw [heq observer]
  rw [quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect]
  simp only [FinDist.expect_map]
  change Math.Probability.expect (laws mixer).toPMF (fun choice =>
      quittingTerminalPayoff reward
        (Function.update profile mixer
          (quittingPureTimeBehaviorStrategy reward mixer choice)) observer) = _
  rw [← quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
    reward profile mixer observer (laws mixer).toPMF]
  rw [horiginalProfile]

end GameTheory
