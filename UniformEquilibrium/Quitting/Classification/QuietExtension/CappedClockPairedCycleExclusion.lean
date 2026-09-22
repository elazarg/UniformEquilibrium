import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFamily
import UniformEquilibrium.Quitting.Cycles.CyclicSingletonEscort

/-!
# No balanced singleton cycle in the paired capped-clock family

The paired singleton columns have no directed escort edge: reciprocal
within-pair entries are both positive, while reciprocal cross-pair entries
are both negative.  The existing arbitrary-period escort necessity therefore
excludes every balanced singleton cycle, both in the four-player table and in
the child table obtained by deleting player `3`.
-/

noncomputable section

namespace GameTheory

namespace CappedClockPairedCycleExclusion

open QuittingLCPClassification

abbrev Player := CappedClockPairedFamily.Player
abbrev Child := CappedClockPairedFamily.Child

private theorem parent_singletonMatrix_eq_boundaryReward
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : CappedClockPairedFamily.Conditions reward)
    (recipient quitter : Player) :
    quittingSingletonMatrix reward recipient quitter =
      quittingSingletonMatrix SolanVieilleBoundary.boundaryReward
        recipient quitter := by
  change reward (quittingSingletonTerminal quitter) recipient -
      reward (quittingSingletonTerminal recipient) recipient =
    SolanVieilleBoundary.boundaryReward
        (quittingSingletonTerminal quitter) recipient -
      SolanVieilleBoundary.boundaryReward
        (quittingSingletonTerminal recipient) recipient
  rw [CappedClockPairedFamily.singleton_rows_eq_boundaryReward
      conditions quitter recipient,
    CappedClockPairedFamily.singleton_rows_eq_boundaryReward
      conditions recipient recipient]

private theorem not_parent_escortEdge
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : CappedClockPairedFamily.Conditions reward)
    (owner nextOwner : Player) :
    ¬ IsQuittingSingletonEscortEdge reward owner nextOwner := by
  rintro ⟨hne, hforward, hreverse⟩
  rw [parent_singletonMatrix_eq_boundaryReward conditions] at hforward hreverse
  fin_cases owner <;> fin_cases nextOwner
  all_goals solve
    | exact hne rfl
    | norm_num [quittingSingletonMatrix,
        SolanVieilleBoundary.boundaryReward] at hforward
    | norm_num [quittingSingletonMatrix,
        SolanVieilleBoundary.boundaryReward] at hreverse

/-- No balanced singleton certificate of any period exists for a paired-family
parent table. -/
theorem not_nonempty_balancedSingletonCycleCertificate
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : CappedClockPairedFamily.Conditions reward) (L : ℕ) :
    ¬Nonempty (BalancedSingletonCycleCertificate (L := L) reward) := by
  rintro ⟨certificate⟩
  obtain ⟨cycle, -⟩ := certificate.exists_escortCycle
  exact not_parent_escortEdge conditions _ _ (cycle.edge 0)

private theorem child_singletonMatrix_eq_boundaryReward
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : CappedClockPairedFamily.Conditions reward)
    (recipient quitter : Child) :
    quittingSingletonMatrix (quittingDeletePlayerReward reward 3)
        recipient quitter =
      quittingSingletonMatrix SolanVieilleBoundary.boundaryReward
        recipient.1 quitter.1 := by
  change quittingDeleteReward reward (· = 3)
        (quittingSingletonTerminal quitter) recipient -
      quittingDeleteReward reward (· = 3)
        (quittingSingletonTerminal recipient) recipient =
    SolanVieilleBoundary.boundaryReward
        (quittingSingletonTerminal quitter.1) recipient.1 -
      SolanVieilleBoundary.boundaryReward
        (quittingSingletonTerminal recipient.1) recipient.1
  simp only [quittingDeleteReward_singletonTerminal]
  rw [CappedClockPairedFamily.singleton_rows_eq_boundaryReward
      conditions quitter.1 recipient.1,
    CappedClockPairedFamily.singleton_rows_eq_boundaryReward
      conditions recipient.1 recipient.1]

private theorem not_child_escortEdge
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : CappedClockPairedFamily.Conditions reward)
    (owner nextOwner : Child) :
    ¬ IsQuittingSingletonEscortEdge
      (quittingDeletePlayerReward reward 3) owner nextOwner := by
  rintro ⟨hne, hforward, hreverse⟩
  rw [child_singletonMatrix_eq_boundaryReward conditions] at hforward hreverse
  fin_cases owner <;> fin_cases nextOwner
  all_goals solve
    | exact hne rfl
    | norm_num [quittingSingletonMatrix,
        SolanVieilleBoundary.boundaryReward] at hforward
    | norm_num [quittingSingletonMatrix,
        SolanVieilleBoundary.boundaryReward] at hreverse

/-- No balanced singleton certificate of any period exists in the child table
obtained by deleting player `3` from a paired-family table. -/
theorem not_nonempty_balancedSingletonCycleCertificate_deleteThree
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : CappedClockPairedFamily.Conditions reward) (L : ℕ) :
    ¬Nonempty (BalancedSingletonCycleCertificate (L := L)
      (quittingDeletePlayerReward reward 3)) := by
  rintro ⟨certificate⟩
  obtain ⟨cycle, -⟩ := certificate.exists_escortCycle
  exact not_child_escortEdge conditions _ _ (cycle.edge 0)

end CappedClockPairedCycleExclusion

end GameTheory
