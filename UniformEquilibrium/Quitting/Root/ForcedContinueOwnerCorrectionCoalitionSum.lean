import UniformEquilibrium.Quitting.Root.ForcedContinuePayoffDisplacement
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-! # Owner-deleted coalition expansion of the forced-Continue correction -/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The forced-Continue owner correction is the exact owner-deleted
coalition average of the payoff without the owner minus the payoff with the
owner inserted.  The empty term is the continuation-minus-singleton term. -/
theorem quittingForcedContinueOwnerCorrection_eq_sum_opponentCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool) (owner who : ι) :
    quittingForcedContinueOwnerCorrection reward source root owner who =
      ∑ coalition ∈ (Finset.univ.erase owner).powerset,
        quittingOpponentCoalitionMass root owner coalition *
          (quittingStageCoalitionPayoff reward source coalition who -
            quittingStageCoalitionPayoff reward source
              (insert owner coalition) who) := by
  let projectedReward : {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun terminal _ => reward terminal who
  let projectedSource : Payoff ι := fun _ => source who
  change quittingRootContinuePayoff projectedReward projectedSource root owner -
      quittingRootQuitPayoff projectedReward projectedSource root owner = _
  rw [quittingRootContinuePayoff_eq_sum_opponentCoalitionMass,
    quittingRootQuitPayoff_eq_sum_opponentCoalitionMass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coalition _
  simp only [projectedReward, projectedSource, quittingStageCoalitionPayoff]
  split <;> split <;> ring

end GameTheory
