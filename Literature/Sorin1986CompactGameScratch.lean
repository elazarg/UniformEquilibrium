import Sorin1986CompactPayoffScratch

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace SequenceForm

/-- Extending a public history by one joint action has the action-sequence
mass prescribed by the realization plans. -/
theorem historyMass_snoc {G : FiniteStageGame}
    (profile : RealizationProfile G) (h : History G)
    (a : JointAction G) :
    historyMass profile (snocHistory h a) = actionMass profile h a := by
  classical
  unfold historyMass actionMass actionWeight
  apply Finset.prod_congr rfl
  intro who _
  exact (profile who).2.2 h a

/-- The joint-action masses leaving a public history sum to its mass. -/
theorem sum_actionMass {G : FiniteStageGame}
    (profile : RealizationProfile G) (h : History G) :
    ∑ a : JointAction G, actionMass profile h a = historyMass profile h := by
  classical
  calc
    ∑ a : JointAction G, actionMass profile h a =
        ∏ who, ∑ own : G.Action who,
          actionWeight (profile who) h own := by
      simpa [actionMass] using
        (Finset.prod_univ_sum
          (fun who : G.Player => (Finset.univ : Finset (G.Action who)))
          (fun who own => actionWeight (profile who) h own)).symm
    _ = historyMass profile h := by
      unfold historyMass
      apply Finset.prod_congr rfl
      intro who _
      exact (profile who).2.1 h

/-- The empty history has mass one. -/
@[simp] theorem historyMass_empty {G : FiniteStageGame}
    (profile : RealizationProfile G) :
    historyMass profile (emptyHistory G) = 1 := by
  classical
  unfold historyMass
  apply Fintype.prod_eq_one
  intro who
  exact (profile who).2.1

end SequenceForm

end Literature.Sorin1986
