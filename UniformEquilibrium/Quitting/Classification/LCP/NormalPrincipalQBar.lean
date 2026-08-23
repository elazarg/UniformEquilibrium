/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalRestriction
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# Projective Q-bar on punishment-normal principal matrices

This file supplies the matrix adapters needed to formulate projective Q-bar
on the players whose solo payoff covers their behavioral punishment value.
This player set is distinct from the recursively screened `normalCore` used
by the Solan--Solan algebraic gate.

The results here are algebraic. In particular, projective Q-bar on the
punishment-normal principal matrix is not assigned a strategic conclusion.
The final counterexample-facing implication is therefore stated relative to
an explicit producer hypothesis.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset
open Math.LinearProgramming
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The players whose own singleton payoff covers their behavioral punishment
value. This is the production minmax-normal set, not the recursive
`normalCore` of the LCP gate. -/
def punishmentNormalPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Finset ι := by
  classical
  exact Finset.univ.filter (IsQuittingNormalPlayer reward)

@[simp] theorem mem_punishmentNormalPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    who ∈ punishmentNormalPlayers reward ↔ IsQuittingNormalPlayer reward who := by
  simp [punishmentNormalPlayers]

/-- The normalized singleton matrix restricted to the punishment-normal
players. -/
def normalizedPunishmentNormalPlayerMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    punishmentNormalPlayers reward → punishmentNormalPlayers reward → ℝ :=
  principalMatrix (normalizedSoloMatrix reward) (punishmentNormalPlayers reward)

/-- Outside the zero-solo class, some player is punishment-normal. -/
theorem punishmentNormalPlayers_nonempty_of_not_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬IsQuittingZeroSolo reward) :
    (punishmentNormalPlayers reward).Nonempty := by
  simp only [IsQuittingZeroSolo, not_forall, not_le] at hnot
  obtain ⟨who, hsolo⟩ := hnot
  refine ⟨who, (mem_punishmentNormalPlayers reward who).2 ?_⟩
  unfold IsQuittingNormalPlayer quittingSoloSelfPayoff
  have hbound := quittingPunishmentValue_le_max_solo reward who
  rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty reward
    (Finset.singleton_nonempty who)] at hbound
  have hpositive : 0 <
      reward ⟨{who}, Finset.singleton_nonempty who⟩ who := by
    simpa [quittingSingletonTerminal] using hsolo
  rw [max_eq_left hpositive.le] at hbound
  simpa [quittingSingletonTerminal] using hbound

/-- Ambient projective Q-bar therefore implies projective Q-bar on the
punishment-normal principal matrix. -/
theorem isProjectiveQBarMatrix_normalizedPunishmentNormalPlayerMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hQ : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)) :
    IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward) :=
  isProjectiveQBarMatrix_principalMatrix _ _ hQ

/-- The standard-Q side together with projective Q-bar on the
punishment-normal principal matrix. This may be strictly broader than
`ProjectiveQBarMatrixBranch`, whose Q-bar hypothesis concerns the full
ambient matrix. -/
structure PunishmentNormalProjectiveQBarMatrixBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop
    extends StandardQMatrixSide reward where
  punishmentNormal_projectiveQBar : IsProjectiveQBarMatrix
    (normalizedPunishmentNormalPlayerMatrix reward)

/-- The strengthened residual class in which projective Q-bar already fails
on the punishment-normal principal matrix. -/
structure PunishmentNormalResidualHardClass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop
    extends StandardQMatrixSide reward where
  not_punishmentNormal_projectiveQBar : ¬IsProjectiveQBarMatrix
    (normalizedPunishmentNormalPlayerMatrix reward)

/-- The existing full-matrix projective branch lies in the weaker
punishment-normal projective branch. -/
theorem ProjectiveQBarMatrixBranch.toPunishmentNormal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : ProjectiveQBarMatrixBranch reward) :
    PunishmentNormalProjectiveQBarMatrixBranch reward where
  toStandardQMatrixSide := h.toStandardQMatrixSide
  punishmentNormal_projectiveQBar :=
    isProjectiveQBarMatrix_normalizedPunishmentNormalPlayerMatrix
      reward h.full_projectiveQBar

/-- Failure on the punishment-normal principal matrix forces failure on the
ambient matrix, so the strengthened residual class embeds in the existing
`ResidualHardClass`. -/
theorem PunishmentNormalResidualHardClass.toResidualHardClass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : PunishmentNormalResidualHardClass reward) :
    ResidualHardClass reward where
  normal_nonempty := h.normal_nonempty
  no_homogeneous := h.no_homogeneous
  normal_standardQ := h.normal_standardQ
  not_full_projectiveQBar := fun hfull =>
    h.not_punishmentNormal_projectiveQBar
      (isProjectiveQBarMatrix_normalizedPunishmentNormalPlayerMatrix
        reward hfull)

/-- The standard-Q side splits exactly according to projective Q-bar on the
punishment-normal principal matrix. -/
theorem StandardQMatrixSide.punishmentNormal_qbar_or_residual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : StandardQMatrixSide reward) :
    PunishmentNormalProjectiveQBarMatrixBranch reward ∨
      PunishmentNormalResidualHardClass reward := by
  classical
  by_cases hQ : IsProjectiveQBarMatrix
      (normalizedPunishmentNormalPlayerMatrix reward)
  · exact Or.inl
      { normal_nonempty := h.normal_nonempty
        no_homogeneous := h.no_homogeneous
        normal_standardQ := h.normal_standardQ
        punishmentNormal_projectiveQBar := hQ }
  · exact Or.inr
      { normal_nonempty := h.normal_nonempty
        no_homogeneous := h.no_homogeneous
        normal_standardQ := h.normal_standardQ
        not_punishmentNormal_projectiveQBar := hQ }

omit [Fintype ι] [DecidableEq ι] in
/-- Negating projective Q-bar exposes a concrete nonempty principal matrix on
which projective Q fails. -/
theorem exists_nonprojectivePrincipalMatrix_of_not_projectiveQBar
    {M : ι → ι → ℝ} (hQ : ¬IsProjectiveQBarMatrix M) :
    ∃ players : Finset ι, players.Nonempty ∧
      ¬IsProjectiveQMatrix (principalMatrix M players) := by
  rw [IsProjectiveQBarMatrix] at hQ
  push Not at hQ
  obtain ⟨players, hplayers, hfailure⟩ := hQ
  exact ⟨players, hplayers, hfailure⟩

/-- A strengthened residual table has a concrete nonempty principal subset
of punishment-normal players on which the normalized singleton matrix is not
projective Q. -/
theorem PunishmentNormalResidualHardClass.exists_allNormal_nonprojectivePrincipal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : PunishmentNormalResidualHardClass reward) :
    ∃ players : Finset (punishmentNormalPlayers reward), players.Nonempty ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedPunishmentNormalPlayerMatrix reward) players) :=
  exists_nonprojectivePrincipalMatrix_of_not_projectiveQBar
    h.not_punishmentNormal_projectiveQBar

/-- The same obstruction with an ambient finite player set: every selected
player is punishment-normal, and the literal ambient principal matrix fails
projective Q. -/
theorem PunishmentNormalResidualHardClass.exists_ambient_allNormal_nonprojectivePrincipal
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : PunishmentNormalResidualHardClass reward) :
    ∃ players : Finset ι, players.Nonempty ∧
      (∀ who ∈ players, IsQuittingNormalPlayer reward who) ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) := by
  obtain ⟨inner, hinner, hnonQ⟩ :=
    h.exists_allNormal_nonprojectivePrincipal
  let outer := punishmentNormalPlayers reward
  let players := flattenPrincipalPlayers outer inner
  refine ⟨players, ?_, ?_, ?_⟩
  · simpa [players, flattenPrincipalPlayers] using hinner
  · intro who hwho
    obtain ⟨hwhoOuter, _⟩ :=
      (mem_flattenPrincipalPlayers outer inner who).1 hwho
    exact (mem_punishmentNormalPlayers reward who).1 hwhoOuter
  · intro hprojective
    apply hnonQ
    have hreindexed : IsProjectiveQMatrix
        (reindexMatrix (nestedPrincipalEquiv outer inner)
          (principalMatrix
            (normalizedPunishmentNormalPlayerMatrix reward) inner)) := by
      rw [show reindexMatrix (nestedPrincipalEquiv outer inner)
          (principalMatrix
            (normalizedPunishmentNormalPlayerMatrix reward) inner) =
          principalMatrix (normalizedSoloMatrix reward) players by
        exact reindexMatrix_nestedPrincipalEquiv_principalMatrix
          (normalizedSoloMatrix reward) outer inner]
      exact hprojective
    exact (isProjectiveQMatrix_reindexMatrix_iff
      (nestedPrincipalEquiv outer inner)
      (principalMatrix
        (normalizedPunishmentNormalPlayerMatrix reward) inner)).1 hreindexed

/-- If projective Q-bar on the punishment-normal principal matrix has a
strategic producer, then a counterexample belongs to the strengthened
residual class. The producer is explicit because this algebraic module does
not claim the open path/strategy compilation theorem. -/
theorem punishmentNormalResidualHardClass_of_producer_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : IsProjectiveQBarMatrix
        (normalizedPunishmentNormalPlayerMatrix reward) →
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    PunishmentNormalResidualHardClass reward := by
  have hstandard :=
    standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot
  refine
    { normal_nonempty := hstandard.normal_nonempty
      no_homogeneous := hstandard.no_homogeneous
      normal_standardQ := hstandard.normal_standardQ
      not_punishmentNormal_projectiveQBar := ?_ }
  exact fun hQ => hnot (hproducer hQ)

/-- Under the same explicit producer hypothesis, every counterexample has an
all-punishment-normal principal obstruction to projective Q. -/
theorem exists_allNormal_nonprojectivePrincipal_of_producer_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : IsProjectiveQBarMatrix
        (normalizedPunishmentNormalPlayerMatrix reward) →
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ players : Finset (punishmentNormalPlayers reward), players.Nonempty ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedPunishmentNormalPlayerMatrix reward) players) :=
  (punishmentNormalResidualHardClass_of_producer_of_not_exists_uniformEquilibriumPayoff
    reward hproducer hnot).exists_allNormal_nonprojectivePrincipal

/-- Ambient-coordinate form of the preceding counterexample obstruction. -/
theorem ambientNormal_obstruction_of_producer_of_noUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : IsProjectiveQBarMatrix
        (normalizedPunishmentNormalPlayerMatrix reward) →
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ players : Finset ι, players.Nonempty ∧
      (∀ who ∈ players, IsQuittingNormalPlayer reward who) ∧
      ¬IsProjectiveQMatrix
        (principalMatrix (normalizedSoloMatrix reward) players) :=
  (punishmentNormalResidualHardClass_of_producer_of_not_exists_uniformEquilibriumPayoff
    reward hproducer hnot).exists_ambient_allNormal_nonprojectivePrincipal

end QuittingLCPClassification
end GameTheory
