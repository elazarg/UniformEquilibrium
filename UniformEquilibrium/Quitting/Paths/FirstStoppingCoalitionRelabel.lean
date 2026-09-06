import MathUE.Probability.FirstStoppingCoalitionRelabel
import UniformEquilibrium.Quitting.Paths.BehaviorFirstStoppingPairLaw
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction

/-! # Relabeling actual reconstructed first-stopping coalition laws -/

noncomputable section

namespace GameTheory

open Math.Probability.DiscreteHazard.StoppingLaw

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Reconstructed behavioral profiles preserve exact coalition masses under
simultaneous relabeling. -/
theorem quittingBehaviorExactFiniteFirstCoalitionMass_relabel
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ)
    (laws : ι → PMF (Option ℕ)) (equiv : ι ≃ κ)
    (coalition : {C : Finset ι // C.Nonempty}) :
    quittingBehaviorExactFiniteFirstCoalitionMass
        (quittingStoppingLawProfile reward (fun who => laws (equiv.symm who)))
        (relabelCoalition equiv coalition) =
      exactFiniteFirstStoppingCoalitionMass laws coalition := by
  change exactFiniteFirstStoppingCoalitionMass
      (fun who => quittingBehaviorStoppingLaw reward
        (quittingStoppingLawProfile reward
          (fun who => laws (equiv.symm who)) who))
      (relabelCoalition equiv coalition) = _
  simp_rw [quittingBehaviorStoppingLaw_stoppingLawProfile]
  exact exactFiniteFirstStoppingCoalitionMass_relabel laws equiv coalition

end GameTheory
