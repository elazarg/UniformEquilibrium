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

/-- Split a nonempty public history into its last joint action and preceding
public history. -/
abbrev historySnocEquiv (G : FiniteStageGame) (t : ℕ) :
    JointAction G × PublicHistory G t ≃ PublicHistory G (t + 1) :=
  Fin.snocEquiv (fun _ : Fin (t + 1) => JointAction G)

/-- Public-history masses at every date form a probability distribution. -/
theorem sum_historyMass {G : FiniteStageGame}
    (profile : RealizationProfile G) :
    ∀ t : ℕ, ∑ h : PublicHistory G t,
      historyMass profile ⟨t, h⟩ = 1
  | 0 => by
      simpa [emptyHistory] using historyMass_empty profile
  | t + 1 => by
      let e := historySnocEquiv G t
      calc
        ∑ h' : PublicHistory G (t + 1), historyMass profile ⟨t + 1, h'⟩ =
            ∑ p : JointAction G × PublicHistory G t,
              historyMass profile ⟨t + 1, e p⟩ := by
                exact (e.sum_comp
                  (fun h' => historyMass profile ⟨t + 1, h'⟩)).symm
        _ = ∑ p : JointAction G × PublicHistory G t,
              actionMass profile ⟨t, p.2⟩ p.1 := by
                apply Fintype.sum_congr
                intro p
                change historyMass profile
                    (snocHistory ⟨t, p.2⟩ p.1) = _
                exact historyMass_snoc profile ⟨t, p.2⟩ p.1
        _ = ∑ a : JointAction G, ∑ h : PublicHistory G t,
              actionMass profile ⟨t, h⟩ a := by
                rw [Fintype.sum_prod_type]
        _ = ∑ h : PublicHistory G t, ∑ a : JointAction G,
              actionMass profile ⟨t, h⟩ a := by
                rw [Finset.sum_comm]
        _ = ∑ h : PublicHistory G t,
              historyMass profile ⟨t, h⟩ := by
                apply Fintype.sum_congr
                intro h
                exact sum_actionMass profile ⟨t, h⟩
        _ = 1 := sum_historyMass profile t

/-- The joint history/action masses at a fixed stage also sum to one. -/
theorem sum_stageMass {G : FiniteStageGame}
    (profile : RealizationProfile G) (t : ℕ) :
    ∑ h : PublicHistory G t, ∑ a : JointAction G,
      actionMass profile ⟨t, h⟩ a = 1 := by
  calc
    _ = ∑ h : PublicHistory G t, historyMass profile ⟨t, h⟩ := by
      apply Fintype.sum_congr
      intro h
      exact sum_actionMass profile ⟨t, h⟩
    _ = 1 := sum_historyMass profile t

end SequenceForm

end Literature.Sorin1986
