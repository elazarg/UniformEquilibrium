import GameTheory.Math.Probability.Simplex
import MathUE.LinearAlgebra.FiniteConicSparseCombination
import UniformEquilibrium.Quitting.Paths.FiniteStoppingLawMixture

/-! # Sparse finite mixtures preserving every prescribed payoff coordinate

The replacement uses only original positive-support generators.
It preserves prescribed payoffs, not complete response caps.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {Player Generator : Type}
variable [Fintype Player] [DecidableEq Player]

/-- A finite mixture of one player's strategies can be replaced on its
original support by at most `card Player + 1` generators while preserving
the whole payoff vector. -/
theorem exists_sparseFiniteStoppingLawMixture_wholePayoff_eq
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (profile : (quittingGame reward).BehaviorProfile)
    (mixer : Player)
    (strategy : Generator → (quittingGame reward).BehaviorStrategy mixer)
    (mixture : FinDist Generator) :
    ∃ sparse : FinDist {generator // generator ∈ mixture.supportFinset},
      Fintype.card {generator // sparse.prob generator ≠ 0} ≤
        Fintype.card Player + 1 ∧
      ∀ observer,
        quittingTerminalPayoff reward
            (Function.update profile mixer
              (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer
                (sparse.map fun generator => strategy generator.1))) observer =
          quittingTerminalPayoff reward
            (Function.update profile mixer
              (quittingFiniteStoppingLawMixtureBehaviorStrategy reward mixer
                (mixture.map strategy))) observer := by
  let Support := {generator // generator ∈ mixture.supportFinset}
  let vector : Support → Option Player → ℝ := fun generator coordinate =>
    coordinate.elim 1 fun observer =>
      quittingTerminalPayoff reward
        (Function.update profile mixer (strategy generator.1)) observer
  let target : Option Player → ℝ := fun coordinate =>
    ∑ generator : Support, mixture.prob generator.1 * vector generator coordinate
  obtain ⟨coefficient, hcoefficient, hreconstruct, hcard⟩ :=
    Math.LinearAlgebra.exists_nonnegative_finiteCombination_eq_support_card_le
      vector target (fun generator : Support => mixture.prob generator.1)
      (fun generator => mixture.prob_nonneg generator.1) (fun coordinate => rfl)
  have hsum : ∑ generator : Support, coefficient generator = 1 := by
    have hnone := hreconstruct none
    rw [show target none = ∑ generator : Support, mixture.prob generator.1 by
      simp [target, vector]] at hnone
    have horiginalSum := mixture.sum_prob_supportFinset
    rw [← Finset.sum_attach] at horiginalSum
    rw [show (∑ generator : Support, mixture.prob generator.1) = 1 by
      exact horiginalSum] at hnone
    simpa [vector] using hnone
  let sparse : FinDist Support := FinDist.ofSimplex ⟨hcoefficient, hsum⟩
  refine ⟨sparse, ?_, ?_⟩
  · have hsparseProb : sparse.prob = coefficient := by
      exact FinDist.prob_ofSimplex ⟨hcoefficient, hsum⟩
    rw [hsparseProb]
    change Fintype.card {generator : Support // coefficient generator ≠ 0} ≤
      Fintype.card Player + 1
    simpa only [Fintype.card_option] using hcard
  · intro observer
    rw [quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect,
      quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect]
    simp only [FinDist.expect_map]
    rw [FinDist.expect_eq_sum, FinDist.expect_eq_sum_support]
    have hcoordinate := hreconstruct (some observer)
    have hsparseProb : sparse.prob = coefficient := by
      exact FinDist.prob_ofSimplex ⟨hcoefficient, hsum⟩
    rw [hsparseProb]
    change (∑ generator : Support,
      coefficient generator * vector generator (some observer)) = _
    rw [hcoordinate]
    dsimp only [target, vector, Option.elim]
    exact (Finset.sum_subtype mixture.supportFinset (fun _ => Iff.rfl)
      (fun generator : Generator => mixture.prob generator *
        quittingTerminalPayoff reward
          (Function.update profile mixer (strategy generator)) observer)).symm

end GameTheory
