/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.AKRSTheorem34Dependencies
import UniformEquilibrium.Quitting.Classification.Existence.StationaryPrefixExceptionalOwner

/-!
# Actual-source seams for diffuse stationary-prefix compactification

A diffuse stationarily generated family has an actual stationary root, an
actual finite switch horizon, and an actual punishment sequence at every
scale.  Compactness of the survival through that whole prefix leaves exactly
two source-level attachment problems.  Either a positive amount of the
punishment suffix remains reachable, or joint survival vanishes while one
exceptional owner's player-deleted survival remains positive.  If neither
occurs, the checked deleted-clock transport gives the stationary branch.

The structures below retain the source family and the complete subsequential
survival data.  They are stronger inputs than a bare assertion that the
diffuse residual exists.  The reduction theorem proves that consumers for
these two concrete inputs imply the AKRS diffuse compactification dependency.
It does not claim either attachment consumer.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An actual stationary-prefix source along which the punishment suffix
retains positive limiting prescribed reach. -/
structure QuittingPositiveJointPrefixReachSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  family : QuittingDiffuseStationaryPrefixFamily reward
  selected : ℕ → ℕ
  jointLimit : ℝ
  selected_strictMono : StrictMono selected
  jointLimit_pos : 0 < jointLimit
  joint_tendsto : Tendsto (fun n ↦ family.prefixJointSurvival (selected n))
    atTop (nhds jointLimit)

/-- An actual stationary-prefix source with vanishing joint survival and one
unique possible nonvanishing player-deleted clock. -/
structure QuittingUniqueExceptionalOwnerSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  family : QuittingDiffuseStationaryPrefixFamily reward
  owner : ι
  selected : ℕ → ℕ
  deletedLimit : ℝ
  selected_strictMono : StrictMono selected
  deletedLimit_pos : 0 < deletedLimit
  joint_tendsto_zero : Tendsto
    (fun n ↦ family.prefixJointSurvival (selected n)) atTop (nhds 0)
  ownerDeleted_tendsto : Tendsto
    (fun n ↦ family.prefixDeletedSurvival (selected n) owner)
    atTop (nhds deletedLimit)
  otherDeleted_tendsto_zero : ∀ other, other ≠ owner → Tendsto
    (fun n ↦ family.prefixDeletedSurvival (selected n) other)
    atTop (nhds 0)

/-- Probability that the exceptional owner itself continues throughout the
selected repeated prefix. -/
def QuittingUniqueExceptionalOwnerSource.ownerPrefixSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) : ℝ :=
  ∏ _time ∈ Finset.range (source.family.horizon (source.selected n) + 1),
    (source.family.root (source.selected n) source.owner false).toReal

/-- Joint prefix survival factors as exceptional-owner survival times that
owner's deleted survival. -/
theorem QuittingUniqueExceptionalOwnerSource.joint_eq_deleted_mul_owner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) (n : ℕ) :
    source.family.prefixJointSurvival (source.selected n) =
      source.family.prefixDeletedSurvival (source.selected n) source.owner *
        source.ownerPrefixSurvival n := by
  simpa only [QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival,
    QuittingDiffuseStationaryPrefixFamily.prefixDeletedSurvival,
    QuittingUniqueExceptionalOwnerSource.ownerPrefixSurvival,
    quittingJointSurvivalWeight_eq_prod, quittingSurvivalPrefix, zero_add] using
    quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own
      (fun _ ↦ source.family.root (source.selected n)) source.owner
      (source.family.horizon (source.selected n) + 1)

/-- The exceptional owner's own probability of surviving the repeated prefix
vanishes.  Thus the exceptional clock means that the owner, rather than the
opponents, supplies asymptotically all absorption before the actual suffix. -/
theorem QuittingUniqueExceptionalOwnerSource.ownerPrefixSurvival_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingUniqueExceptionalOwnerSource reward) :
    Tendsto source.ownerPrefixSurvival atTop (nhds 0) := by
  have hdeletedNe : ∀ᶠ n in atTop,
      source.family.prefixDeletedSurvival (source.selected n) source.owner ≠ 0 := by
    have hpositive : ∀ᶠ n in atTop,
        0 < source.family.prefixDeletedSurvival
          (source.selected n) source.owner :=
      (tendsto_order.1 source.ownerDeleted_tendsto).1 0 source.deletedLimit_pos
    exact hpositive.mono fun _ hn ↦ ne_of_gt hn
  have hratio : Tendsto
      (fun n ↦ source.family.prefixJointSurvival (source.selected n) /
        source.family.prefixDeletedSurvival (source.selected n) source.owner)
      atTop (nhds 0) := by
    change Tendsto
      ((fun n ↦ source.family.prefixJointSurvival (source.selected n)) /
        fun n ↦ source.family.prefixDeletedSurvival
          (source.selected n) source.owner) atTop (nhds 0)
    simpa using source.joint_tendsto_zero.div source.ownerDeleted_tendsto
      (ne_of_gt source.deletedLimit_pos)
  apply hratio.congr'
  filter_upwards [hdeletedNe] with n hne
  rw [source.joint_eq_deleted_mul_owner n, mul_div_cancel_left₀ _ hne]

/-- Every diffuse stationarily generated source either already produces the
stationary branch, retains positive actual reach of its punishment suffix, or
has one unique exceptional deleted-clock owner. -/
theorem stationary_or_positiveJointPrefixReachSource_or_uniqueExceptionalOwnerSource
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    QuittingStationaryεEquilibriumExistence reward ∨
      Nonempty (QuittingPositiveJointPrefixReachSource reward) ∨
        Nonempty (QuittingUniqueExceptionalOwnerSource reward) := by
  let family := Classical.choice
    (exists_quittingDiffuseStationaryPrefixFamily hgenerated)
  rcases stationary_or_positivePrefixJointReach_or_uniqueExceptionalOwner
      family id strictMono_id with hstationary | hpositive | hexceptional
  · exact Or.inl hstationary
  · obtain ⟨selected, jointLimit, hselected, hlimitPositive, hlimit⟩ := hpositive
    exact Or.inr (Or.inl ⟨⟨family, selected, jointLimit, hselected,
      hlimitPositive, hlimit⟩⟩)
  · obtain ⟨owner, selected, deletedLimit, hselected, hdeletedPositive,
      hjoint, howner, hother⟩ := hexceptional
    exact Or.inr (Or.inr ⟨⟨family, owner, selected, deletedLimit, hselected,
      hdeletedPositive, hjoint, howner, hother⟩⟩)

/-- The positive-joint-reach attachment obligation at actual source scope. -/
def HasPositiveJointPrefixReachAttachment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ _source : QuittingPositiveJointPrefixReachSource reward,
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward

/-- The unique-exceptional-owner attachment obligation at actual source
scope. -/
def HasUniqueExceptionalOwnerAttachment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ _source : QuittingUniqueExceptionalOwnerSource reward,
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward

/-- The two actual-source attachment consumers imply exactly the diffuse
compactification dependency used by the checked AKRS Theorem 3.4 capstone. -/
theorem hasDiffuseStationarilyGeneratedCompactification_of_sourceAttachments
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hpositive : HasPositiveJointPrefixReachAttachment reward)
    (hexceptional : HasUniqueExceptionalOwnerAttachment reward) :
    HasDiffuseStationarilyGeneratedCompactification reward := by
  intro hgenerated
  rcases
      stationary_or_positiveJointPrefixReachSource_or_uniqueExceptionalOwnerSource
        hgenerated with hstationary | hsources
  · exact Or.inl hstationary
  · cases hsources with
    | inl hsource => exact hpositive (Classical.choice hsource)
    | inr hsource => exact hexceptional (Classical.choice hsource)

end GameTheory
