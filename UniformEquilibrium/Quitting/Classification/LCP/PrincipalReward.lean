/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Restricting a quitting reward table to a principal player subset

An arbitrary finite subset of players inherits a literal quitting reward
table.  Singleton normalization commutes exactly with this restriction: the
restricted normalized matrix is the corresponding principal matrix.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Include a coalition of players from a finite subset into the ambient
player set. -/
def quittingPrincipalCoalition (players : Finset ι)
    (coalition : {S : Finset players // S.Nonempty}) :
    {S : Finset ι // S.Nonempty} :=
  ⟨coalition.1.map ⟨Subtype.val, Subtype.val_injective⟩,
    Finset.map_nonempty.mpr coalition.2⟩

/-- Restrict a quitting reward table to coalitions and payoff coordinates in
a finite player subset. -/
def quittingPrincipalReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    {S : Finset players // S.Nonempty} → Payoff players :=
  fun coalition who =>
    reward (quittingPrincipalCoalition players coalition) who.1

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingPrincipalCoalition_singleton
    (players : Finset ι) (who : players) :
    quittingPrincipalCoalition players
        (quittingProjectiveSingletonTerminal who) =
      quittingProjectiveSingletonTerminal who.1 := by
  apply Subtype.ext
  simp [quittingPrincipalCoalition, quittingProjectiveSingletonTerminal]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingPrincipalReward_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) (owner who : players) :
    quittingPrincipalReward reward players
        (quittingProjectiveSingletonTerminal owner) who =
      reward (quittingProjectiveSingletonTerminal owner.1) who.1 := by
  change reward (quittingPrincipalCoalition players
    (quittingProjectiveSingletonTerminal owner)) who.1 = _
  rw [quittingPrincipalCoalition_singleton]

/-- Singleton normalization of the restricted reward table is exactly the
principal matrix of the ambient normalized singleton table. -/
theorem normalizedSoloMatrix_quittingPrincipalReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    normalizedSoloMatrix (quittingPrincipalReward reward players) =
      principalMatrix (normalizedSoloMatrix reward) players := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold principalMatrix
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  funext who owner
  change quittingPrincipalReward reward players
      (quittingProjectiveSingletonTerminal owner) who -
        quittingPrincipalReward reward players
          (quittingProjectiveSingletonTerminal who) who =
    reward (quittingProjectiveSingletonTerminal owner.1) who.1 -
      reward (quittingProjectiveSingletonTerminal who.1) who.1
  rw [quittingPrincipalReward_singleton,
    quittingPrincipalReward_singleton]

/-- A homogeneous solution of a restricted reward table is literally a
homogeneous solution of the ambient principal normalized matrix. -/
theorem hasHomogeneousSimplexSolution_quittingPrincipalReward_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    HasHomogeneousSimplexSolution
        (normalizedSoloMatrix (quittingPrincipalReward reward players)) ↔
      HasHomogeneousSimplexSolution
        (principalMatrix (normalizedSoloMatrix reward) players) := by
  rw [normalizedSoloMatrix_quittingPrincipalReward]

/-- Projective Q for a restricted reward table is literally projective Q for
the corresponding ambient principal normalized matrix. -/
theorem isProjectiveQMatrix_quittingPrincipalReward_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    IsProjectiveQMatrix
        (normalizedSoloMatrix (quittingPrincipalReward reward players)) ↔
      IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) := by
  rw [normalizedSoloMatrix_quittingPrincipalReward]

/-- Standard Q for a restricted reward table is literally standard Q for
the corresponding ambient principal normalized matrix. -/
theorem isStandardQMatrix_quittingPrincipalReward_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    IsStandardQMatrix
        (normalizedSoloMatrix (quittingPrincipalReward reward players)) ↔
      IsStandardQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) := by
  rw [normalizedSoloMatrix_quittingPrincipalReward]

/-- Failure of projective Q on a principal matrix excludes its homogeneous
simplex branch. -/
theorem not_hasHomogeneousSimplexSolution_principal_of_not_projectiveQ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    ¬HasHomogeneousSimplexSolution
      (normalizedSoloMatrix (quittingPrincipalReward reward players)) := by
  rw [normalizedSoloMatrix_quittingPrincipalReward]
  intro hhomogeneous
  exact hnot ((isProjectiveQMatrix_iff_standard_or_homogeneous _).2
    (Or.inr hhomogeneous))

end QuittingLCPClassification
end GameTheory
