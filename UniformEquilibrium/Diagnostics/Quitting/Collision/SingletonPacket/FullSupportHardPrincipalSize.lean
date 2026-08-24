/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual

/-!
# Size of the nonprojective principal in the four-player hard residual

Full normal core makes the whole normalized singleton matrix standard Q,
whereas the residual hard class fails projective Q-bar on some nonempty
principal.  The failing principal is therefore proper.  A singleton principal
is projective Q because its normalized diagonal is zero.  Consequently the
actual principal obstruction in the final four-player chamber has cardinality
two or three.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math.LinearProgramming

variable {iota : Type} [Fintype iota] [DecidableEq iota]

private def normalCoreUnivEquiv
    (M : iota → iota → ℝ) (hcore : normalCore M = Finset.univ) :
    normalCore M ≃ (Finset.univ : Finset iota) where
  toFun player := ⟨player.1, Finset.mem_univ player.1⟩
  invFun player := ⟨player.1, by rw [hcore]; exact Finset.mem_univ player.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem reindex_normalPlayerMatrix_eq_univPrincipal
    (M : iota → iota → ℝ) (hcore : normalCore M = Finset.univ) :
    reindexMatrix (normalCoreUnivEquiv M hcore) (normalPlayerMatrix M) =
      principalMatrix M Finset.univ := by
  funext receiver owner
  rfl

/-- If the normal core is full, the hard class's standard-Q normal matrix
transports to the literal full principal matrix. -/
theorem ResidualHardClass.fullPrincipal_standardQ
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (hard : ResidualHardClass reward)
    (hcore : normalCore (normalizedSoloMatrix reward) = Finset.univ) :
    IsStandardQMatrix
      (principalMatrix (normalizedSoloMatrix reward) Finset.univ) := by
  rw [← reindex_normalPlayerMatrix_eq_univPrincipal
    (normalizedSoloMatrix reward) hcore]
  exact isStandardQMatrix_reindexMatrix
    (normalCoreUnivEquiv (normalizedSoloMatrix reward) hcore)
    (normalPlayerMatrix (normalizedSoloMatrix reward)) hard.normal_standardQ

/-- On the full-core hard branch, projective Q fails on a proper nonempty
principal rather than on the whole matrix. -/
theorem ResidualHardClass.exists_proper_nonprojectivePrincipal
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (hard : ResidualHardClass reward)
    (hcore : normalCore (normalizedSoloMatrix reward) = Finset.univ) :
    ∃ players : Finset iota,
      players.Nonempty ∧ players ⊂ Finset.univ ∧
        ¬IsProjectiveQMatrix
          (principalMatrix (normalizedSoloMatrix reward) players) := by
  obtain ⟨players, hplayers, hnot⟩ :=
    exists_nonprojectivePrincipalMatrix_of_not_projectiveQBar
      hard.not_full_projectiveQBar
  refine ⟨players, hplayers, Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ players, ?_⟩, hnot⟩
  intro hplayersUniv
  apply hnot
  rw [hplayersUniv]
  exact (isProjectiveQMatrix_iff_standard_or_homogeneous _).2
    (Or.inl (hard.fullPrincipal_standardQ hcore))

private theorem singletonPrincipal_projectiveQ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (owner : iota) :
    IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) {owner}) := by
  apply (isProjectiveQMatrix_iff_standard_or_homogeneous _).2
  right
  apply Math.LinearProgramming.singletonLCPFeasible_of_diag_eq_zero
    ⟨owner, by simp⟩
  · exact normalizedSoloMatrix_diagonal reward owner
  · intro player
    have hplayer : player.1 = owner := Finset.mem_singleton.mp player.2
    change 0 ≤ normalizedSoloMatrix reward player.1 owner
    rw [hplayer, normalizedSoloMatrix_diagonal]

/-- The nonprojective principal in the final four-player residual has exactly
two or three coordinates. -/
theorem FinFourQuantitativeFullSupportHardResidual.exists_nonprojectivePrincipal_card_two_or_three
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    ∃ players : Finset (Fin 4),
      (players.card = 2 ∨ players.card = 3) ∧
        ¬IsProjectiveQMatrix
          (principalMatrix (normalizedSoloMatrix reward) players) := by
  obtain ⟨players, hplayers, hproper, hnot⟩ :=
    residual.residualHardClass.exists_proper_nonprojectivePrincipal
      residual.normalCore_eq_univ
  have hcardPos : 0 < players.card := Finset.card_pos.mpr hplayers
  have hcardLt : players.card < 4 := by
    have := Finset.card_lt_card hproper
    simpa using this
  have hcardNeOne : players.card ≠ 1 := by
    intro hcard
    obtain ⟨owner, hplayersEq⟩ := Finset.card_eq_one.mp hcard
    subst players
    exact hnot (singletonPrincipal_projectiveQ reward owner)
  refine ⟨players, ?_, hnot⟩
  omega

end QuittingLCPClassification
end GameTheory
