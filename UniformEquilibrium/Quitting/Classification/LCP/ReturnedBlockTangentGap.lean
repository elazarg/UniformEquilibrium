/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalPrincipalReward
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

/-!
# Principal-matrix adapters for the returned-block tangent gap

The returned-block obstruction applies literally after restricting a quitting
reward table to any nonempty finite player subset.  This file connects that
generic semantic theorem to principal normalized matrices, the recursive
normal core, and the punishment-normal residual classification.

The blocks below live directly on the restricted player type.  Converting an
ambient block whose off-subset hazards vanish into such a block is a separate
semantic adapter and is not asserted here.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Filter QuittingReturnedProductBlock

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonhomogeneous principal normalized matrix has a uniform returned-block
relative-error gap for its literal restricted reward table. -/
theorem exists_pos_principalReturnedBlock_relativeError_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) (hplayers : players.Nonempty) {K : ℝ}
    (hno : ¬HasHomogeneousSimplexSolution
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock players,
      (∀ phase who, |block.value phase who| ≤ K) →
      0 < block.totalHazard → block.totalHazard ≤ δ →
      c * block.totalHazard ≤
        block.bellmanError (quittingPrincipalReward reward players) +
          block.endpointRegret (quittingPrincipalReward reward players) := by
  letI : Nonempty players := hplayers.to_subtype
  apply exists_pos_relativeError_gap_of_noHomogeneous_of_valueBound
  rwa [normalizedSoloMatrix_quittingPrincipalReward]

/-- Failure of projective Q on a nonempty principal matrix supplies the same
uniform returned-block gap, because projective Q contains the homogeneous
simplex branch. -/
theorem exists_pos_principalReturnedBlock_relativeError_gap_of_not_projectiveQ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) (hplayers : players.Nonempty) {K : ℝ}
    (hnot : ¬IsProjectiveQMatrix
      (principalMatrix (normalizedSoloMatrix reward) players)) :
    ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock players,
      (∀ phase who, |block.value phase who| ≤ K) →
      0 < block.totalHazard → block.totalHazard ≤ δ →
      c * block.totalHazard ≤
        block.bellmanError (quittingPrincipalReward reward players) +
          block.endpointRegret (quittingPrincipalReward reward players) := by
  apply exists_pos_principalReturnedBlock_relativeError_gap
    reward players hplayers
  exact not_hasHomogeneousSimplexSolution_principal_of_not_projectiveQ
    reward players hnot

/-- Arbitrary changing-length returned blocks on a literal principal reward
table expose a homogeneous solution of the corresponding ambient principal
normalized matrix. -/
theorem hasHomogeneousSimplexSolution_principal_of_vanishing_returnedBlocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) (hplayers : players.Nonempty)
    (blocks : ℕ → QuittingReturnedProductBlock players) {K : ℝ}
    (hvalue : ∀ n phase who, |(blocks n).value phase who| ≤ K)
    (hpositive : ∀ n, 0 < (blocks n).totalHazard)
    (hvanish : Tendsto (fun n => (blocks n).totalHazard) atTop (nhds 0))
    (hbellman : Tendsto (fun n =>
      (blocks n).bellmanError (quittingPrincipalReward reward players) /
        (blocks n).totalHazard) atTop (nhds 0))
    (hendpoint : Tendsto (fun n =>
      (blocks n).endpointRegret (quittingPrincipalReward reward players) /
        (blocks n).totalHazard) atTop (nhds 0)) :
    HasHomogeneousSimplexSolution
      (principalMatrix (normalizedSoloMatrix reward) players) := by
  letI : Nonempty players := hplayers.to_subtype
  rw [← normalizedSoloMatrix_quittingPrincipalReward]
  exact hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks
    (quittingPrincipalReward reward players) blocks hvalue hpositive
    hvanish hbellman hendpoint

/-- On `ResidualHardClass`, the literal reward table restricted to the
recursive normal core has a uniform small-hazard returned-block gap. -/
theorem ResidualHardClass.exists_pos_normalCoreReturnedBlock_relativeError_gap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hard : ResidualHardClass reward) {K : ℝ} :
    ∃ δ > 0, ∃ c > 0,
      ∀ block : QuittingReturnedProductBlock
        (normalCore (normalizedSoloMatrix reward)),
        (∀ phase who, |block.value phase who| ≤ K) →
        0 < block.totalHazard → block.totalHazard ≤ δ →
        c * block.totalHazard ≤
          block.bellmanError (quittingPrincipalReward reward
            (normalCore (normalizedSoloMatrix reward))) +
          block.endpointRegret (quittingPrincipalReward reward
            (normalCore (normalizedSoloMatrix reward))) := by
  apply exists_pos_principalReturnedBlock_relativeError_gap reward
    (normalCore (normalizedSoloMatrix reward)) hard.normal_nonempty
  simpa only [normalizedNormalPlayerMatrix, normalPlayerMatrix] using
    hard.no_homogeneous

/-- Direct punishment-normal specialization of the generic principal gap. -/
theorem exists_pos_punishmentNormalReturnedBlock_relativeError_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : (punishmentNormalPlayers reward).Nonempty) {K : ℝ}
    (hno : ¬HasHomogeneousSimplexSolution
      (normalizedPunishmentNormalPlayerMatrix reward)) :
    ∃ δ > 0, ∃ c > 0,
      ∀ block : QuittingReturnedProductBlock (punishmentNormalPlayers reward),
        (∀ phase who, |block.value phase who| ≤ K) →
        0 < block.totalHazard → block.totalHazard ≤ δ →
        c * block.totalHazard ≤
          block.bellmanError (quittingPunishmentNormalReward reward) +
            block.endpointRegret (quittingPunishmentNormalReward reward) := by
  simpa only [quittingPunishmentNormalReward] using
    exists_pos_principalReturnedBlock_relativeError_gap reward
      (punishmentNormalPlayers reward) hplayers
      (by simpa only [normalizedPunishmentNormalPlayerMatrix] using hno)

namespace PunishmentNormalResidualHardClass

/-- A punishment-normal residual table exposes an ambient nonempty subset of
punishment-normal players whose literal restricted reward table has a uniform
returned-block gap. -/
theorem exists_allNormal_principalReturnedBlock_relativeError_gap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hard : PunishmentNormalResidualHardClass reward) {K : ℝ} :
    ∃ players : Finset ι, players.Nonempty ∧
      (∀ who ∈ players, IsQuittingNormalPlayer reward who) ∧
      ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock players,
        (∀ phase who, |block.value phase who| ≤ K) →
        0 < block.totalHazard → block.totalHazard ≤ δ →
        c * block.totalHazard ≤
          block.bellmanError (quittingPrincipalReward reward players) +
            block.endpointRegret (quittingPrincipalReward reward players) := by
  obtain ⟨players, hplayers, hnormal, hnot⟩ :=
    hard.exists_ambient_allNormal_nonprojectivePrincipal
  refine ⟨players, hplayers, hnormal, ?_⟩
  exact exists_pos_principalReturnedBlock_relativeError_gap_of_not_projectiveQ
    reward players hplayers hnot

end PunishmentNormalResidualHardClass

end QuittingLCPClassification
end GameTheory
