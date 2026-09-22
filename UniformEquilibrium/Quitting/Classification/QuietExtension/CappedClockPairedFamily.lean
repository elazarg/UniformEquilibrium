import UniformEquilibrium.Quitting.Classification.BlockDeletion
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockFinFourExistence
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable

/-!
# A paired-singleton capped-clock family

This module turns the paired-family capped-clock rows into an actual raw-table
consumer.  The singleton rows are copied literally from
`SolanVieilleBoundary.boundaryReward`; no other entry of that table is used.
Player `3` is quiet, and its deviations are charged with weight two to player
`2`'s separate capped-clock deviations.

An explicit rational table supplies a concrete member.  Every member lies
outside every exact singleton block-deletion gate because every player's own
singleton reward is one, whereas each such gate requires it to be at most a
nonpositive continue floor.
-/

noncomputable section

namespace GameTheory

open StochasticGame

namespace CappedClockPairedFamily

abbrev Player := Fin 4

/-- The three surviving players after player `3` is made quiet. -/
abbrev Child := QuittingDeletedPlayer (3 : Player)

/-- Child player `2`, to which the outsider's deviation gains are charged. -/
def childTwo : Child := ⟨2, by decide⟩

/-- The owner-`3` option reindexing used by the capped-clock compiler. -/
abbrev parentReward
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :=
  quittingFinFourOwnerOptionReward reward 3

/-- The literal paired singleton source, in the same owner-`3` reindexing. -/
abbrev boundarySingletonSource :=
  parentReward SolanVieilleBoundary.boundaryReward

/-- The nonzero row `2e₂` of the paired-family certificate. -/
def weight (child : Child) : ℝ := if child = childTwo then 2 else 0

private def childEmbedding : Child ↪ Player :=
  Function.Embedding.subtype _

private def optionEmbedding : Child ↪ Option Child where
  toFun := some
  inj' := Option.some_injective Child

private theorem mapped_childCoalition (A : Finset Child) :
    (cappedClockChildCoalition A).map
        (Equiv.optionSubtypeNe (3 : Player)).toEmbedding =
      A.map childEmbedding := by
  change (A.map optionEmbedding).map
      (Equiv.optionSubtypeNe (3 : Player)).toEmbedding = _
  rw [Finset.map_map]
  rfl

private theorem mapped_joinedCoalition (A : Finset Child) :
    (cappedClockJoinedCoalition A).map
        (Equiv.optionSubtypeNe (3 : Player)).toEmbedding =
      insert 3 (A.map childEmbedding) := by
  rw [cappedClockJoinedCoalition, Finset.map_insert, mapped_childCoalition]
  rfl

@[simp] private theorem parentReward_singleton
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (owner who : Option Child) :
    parentReward reward (quittingSingletonTerminal owner) who =
      reward (quittingSingletonTerminal
        (Equiv.optionSubtypeNe (3 : Player) owner))
        (Equiv.optionSubtypeNe (3 : Player) who) := by
  change reward
      ((quittingCoalitionEquiv
        (Equiv.optionSubtypeNe (3 : Player)).symm).symm
          (quittingSingletonTerminal owner))
      (Equiv.optionSubtypeNe (3 : Player) who) = _
  congr 1

@[simp] private theorem parentReward_childCoalition
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (A : Finset Child) (hA : A.Nonempty) (who : Option Child) :
    parentReward reward
        ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ who =
      reward ⟨A.map childEmbedding, Finset.map_nonempty.mpr hA⟩
        (Equiv.optionSubtypeNe (3 : Player) who) := by
  change reward
      ((quittingCoalitionEquiv
        (Equiv.optionSubtypeNe (3 : Player)).symm).symm
          ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩)
      (Equiv.optionSubtypeNe (3 : Player) who) = _
  congr 1
  exact Subtype.ext (mapped_childCoalition A)

@[simp] private theorem parentReward_joinedCoalition
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (A : Finset Child) (who : Option Child) :
    parentReward reward
        ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ who =
      reward
        ⟨insert 3 (A.map childEmbedding), Finset.insert_nonempty 3 _⟩
        (Equiv.optionSubtypeNe (3 : Player) who) := by
  change reward
      ((quittingCoalitionEquiv
        (Equiv.optionSubtypeNe (3 : Player)).symm).symm
          ⟨cappedClockJoinedCoalition A,
            cappedClockJoinedCoalition_nonempty A⟩)
      (Equiv.optionSubtypeNe (3 : Player) who) = _
  congr 1
  exact Subtype.ext (mapped_joinedCoalition A)

/-- Raw paired-family conditions.  All singleton coordinates are fixed by the
actual boundary table.  The remaining fields are exactly the future and join
inequalities after deleting player `3`. -/
structure Conditions
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) : Prop where
  singleton_rows : ∀ owner who : Option Child,
    parentReward reward (quittingSingletonTerminal owner) who =
      boundarySingletonSource (quittingSingletonTerminal owner) who
  future_rows : ∀ A : {A : Finset Child // A.Nonempty},
    1 - parentReward reward
          ⟨cappedClockChildCoalition A.1,
            cappedClockChildCoalition_nonempty A.2⟩ none ≤
      2 * (1 - parentReward reward
          ⟨cappedClockChildCoalition A.1,
            cappedClockChildCoalition_nonempty A.2⟩ (some childTwo))
  join_rows : ∀ A : {A : Finset Child // A.Nonempty},
    parentReward reward
          ⟨cappedClockJoinedCoalition A.1,
            cappedClockJoinedCoalition_nonempty A.1⟩ none -
        parentReward reward
          ⟨cappedClockChildCoalition A.1,
            cappedClockChildCoalition_nonempty A.2⟩ none ≤
      2 * (parentReward reward
          ⟨cappedClockChildCoalition (insert childTwo A.1),
            cappedClockChildCoalition_nonempty
              (Finset.insert_nonempty childTwo A.1)⟩ (some childTwo) -
        parentReward reward
          ⟨cappedClockChildCoalition A.1,
            cappedClockChildCoalition_nonempty A.2⟩ (some childTwo))

@[simp] theorem boundarySingletonSource_self (owner : Option Child) :
    boundarySingletonSource (quittingSingletonTerminal owner) owner = 1 := by
  fin_cases owner <;> rfl

/-- The explicit `2e₂` certificate supplied by every raw paired-family
table. -/
def certificate
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : Conditions reward) :
    CappedClockParentRewardCertificate (parentReward reward) where
  weight := weight
  weight_nonneg := by
    intro child
    unfold weight
    split_ifs <;> norm_num
  never_row := by
    have hnone := (conditions.singleton_rows none none).trans
      (boundarySingletonSource_self none)
    change parentReward reward
      ⟨{none}, Finset.singleton_nonempty none⟩ none = 1 at hnone
    have hchildren (child : Child) :=
      (conditions.singleton_rows (some child) (some child)).trans
        (boundarySingletonSource_self (some child))
    change ∀ child : Child, parentReward reward
      ⟨{some child}, Finset.singleton_nonempty (some child)⟩
        (some child) = 1 at hchildren
    rw [hnone]
    simp_rw [hchildren]
    simp [weight]
  future_row := by
    intro A hA
    have hnone := (conditions.singleton_rows none none).trans
      (boundarySingletonSource_self none)
    change parentReward reward
      ⟨{none}, Finset.singleton_nonempty none⟩ none = 1 at hnone
    have hchildren (child : Child) :=
      (conditions.singleton_rows (some child) (some child)).trans
        (boundarySingletonSource_self (some child))
    change ∀ child : Child, parentReward reward
      ⟨{some child}, Finset.singleton_nonempty (some child)⟩
        (some child) = 1 at hchildren
    rw [hnone]
    simp_rw [hchildren]
    simpa [weight] using conditions.future_rows ⟨A, hA⟩
  join_row := by
    intro A hA
    simpa [weight] using conditions.join_rows ⟨A, hA⟩

/-- Every raw table in the paired family has a uniform-equilibrium payoff.
No equilibrium profile or target is assumed in the criterion. -/
theorem exists_uniformEquilibriumPayoff
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : Conditions reward) :
    ∃ payoff : Payoff Player,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate
    reward 3 (certificate conditions)

/-- An explicit rational member of the paired family. -/
def exampleReward
    (quitters : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  match decide (0 ∈ quitters.1), decide (1 ∈ quitters.1),
      decide (2 ∈ quitters.1), decide (3 ∈ quitters.1) with
  | true, false, false, false => ![1, 4, 0, 0]
  | false, true, false, false => ![4, 1, 0, 0]
  | false, false, true, false => ![0, 0, 1, 4]
  | false, false, false, true => ![0, 0, 4, 1]
  | true, true, false, false => ![2, 2, 1, 2]
  | true, false, true, false => ![2, 1, 2, 4]
  | true, false, false, true => ![2, 0, 1, 2]
  | false, true, true, false => ![0, 2, 2, 4]
  | false, true, false, true => ![1, 2, 0, 2]
  | false, false, true, true => ![1, 1, 2, 2]
  | true, true, true, false => ![1, 2, 0, 0]
  | true, true, false, true => ![0, 1, 0, -1]
  | true, false, true, true => ![0, 0, 0, 1]
  | false, true, true, true => ![0, 0, 1, 0]
  | true, true, true, true => ![-1, -1, -1, -1]
  | false, false, false, false => ![0, 0, 0, 0]

/-- The explicit table satisfies the raw paired-family conditions. -/
theorem exampleReward_conditions : Conditions exampleReward := by
  refine ⟨?_, ?_, ?_⟩
  · intro owner who
    fin_cases owner <;> fin_cases who <;> rfl
  · intro A
    fin_cases A <;>
      norm_num [childEmbedding, childTwo, exampleReward]
  · intro A
    fin_cases A <;>
      norm_num [childEmbedding, childTwo, exampleReward]

/-- The concrete fixture has a uniform-equilibrium payoff through the
raw capped-clock route. -/
theorem exampleReward_exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff Player,
      (quittingGame exampleReward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff exampleReward_conditions

/-- Every player's own singleton reward is one throughout the paired family. -/
theorem singleton_self_eq_one
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : Conditions reward) (owner : Player) :
    reward (quittingSingletonTerminal owner) owner = 1 := by
  let encoded : Option Child :=
    (Equiv.optionSubtypeNe (3 : Player)).symm owner
  have hsource := (conditions.singleton_rows encoded encoded).trans
    (boundarySingletonSource_self encoded)
  dsimp only [encoded] at hsource
  simpa only [parentReward_singleton, Equiv.apply_symm_apply] using hsource

/-- Every paired-family table fails the exact block-deletion gate for every
singleton block. -/
theorem not_blockDispensable
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (conditions : Conditions reward) (owner : Player) :
    ¬ QuittingBlockDispensable reward {owner} owner := by
  intro hgate
  have hnonpos := quittingBlockContinueFloor_nonpos reward {owner} owner
  have hself := singleton_self_eq_one conditions owner
  linarith [hgate.2]

/-- The example table witnesses that the weighted paired family is
nonempty and reaches a table rejected by every exact singleton block
deletion. -/
theorem exampleReward_weighted_not_exact :
    Nonempty (CappedClockParentRewardCertificate
      (parentReward exampleReward)) ∧
      ∀ owner : Player,
        ¬ QuittingBlockDispensable exampleReward {owner} owner :=
  ⟨⟨certificate exampleReward_conditions⟩,
    not_blockDispensable exampleReward_conditions⟩

end CappedClockPairedFamily

end GameTheory
