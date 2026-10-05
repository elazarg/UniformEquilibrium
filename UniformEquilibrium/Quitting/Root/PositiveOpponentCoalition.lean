import UniformEquilibrium.Quitting.Root.OneActiveCoalitionMass
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-! # A positive opponent hazard supplies a nonempty positive coalition atom -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_nonempty_opponentCoalition_of_positive_hazard
    (root : ι → PMF Bool) (player other : ι) (hne : other ≠ player)
    (hpositive : 0 < (root other true).toReal) :
    ∃ coalition ∈ (Finset.univ.erase player).powerset,
      coalition.Nonempty ∧ 0 < quittingOpponentCoalitionMass root player coalition := by
  classical
  by_contra hnot
  have hzero : ∀ coalition ∈ (Finset.univ.erase player).powerset,
      coalition ≠ ∅ → quittingOpponentCoalitionMass root player coalition = 0 := by
    intro coalition hcoalition hnonempty
    apply le_antisymm _ (quittingOpponentCoalitionMass_nonneg root player coalition)
    apply le_of_not_gt
    intro hmass
    exact hnot ⟨coalition, hcoalition, Finset.nonempty_iff_ne_empty.mpr hnonempty, hmass⟩
  have hempty : quittingOpponentCoalitionMass root player ∅ = 1 := by
    rw [← quittingOpponentCoalitionMass_sum_powerset root player]
    symm
    apply Finset.sum_eq_single ∅
    · intro coalition hcoalition hne
      exact hzero coalition hcoalition hne
    · simp
  have hcontinue : quittingRootOpponentContinueMass root player = 1 := by
    have hproduct : (∏ other ∈ Finset.univ.erase player,
        (1 - (root other true).toReal)) = 1 := by
      simpa [quittingOpponentCoalitionMass, pmfBool_false_toReal] using hempty
    rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass,
      quittingRootOpponentAbsorptionMass_eq_one_sub_prod, hproduct]
    ring
  have hle := quittingRootOpponentContinueMass_le_continueProbability_of_ne root hne
  have hsum := quittingRoot_continueProbability_add_quitProbability root other
  linarith

end GameTheory
