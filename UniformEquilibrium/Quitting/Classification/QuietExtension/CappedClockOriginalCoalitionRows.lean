import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockSampledLPDual
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge

/-! # Original-coalition formulas for actual child-plus-outsider LP rows

These are source identities for every finite player type. No row coefficient,
cap, or independently chosen restricted reward table is supplied.
-/

noncomputable section

namespace GameTheory.QuittingRawChildSource

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev RawChild (child : Finset ι) := QuittingChildPlayer (· ∉ child)

/-- The actual child-plus-one-outsider table, not a separately supplied fixture. -/
abbrev rawChildReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child : Finset ι) (outside : {who : ι // who ∉ child}) :=
  quittingChildWithOutsiderReward reward (· ∉ child) outside

def rawChildCoalition (child coalition : Finset ι) : Finset (RawChild child) :=
  Finset.univ.filter (fun who => who.1 ∈ coalition)

theorem rawChildCoalition_original_map
    (child coalition : Finset ι) (outside : {who : ι // who ∉ child})
    (hsubset : coalition ⊆ child) :
    (cappedClockChildCoalition (rawChildCoalition child coalition)).map
      (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside) = coalition := by
  ext player
  simp only [cappedClockChildCoalition, Finset.mem_map, rawChildCoalition,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨who, hwho, rfl⟩, heq⟩
    have hvalue : who.1 = player := by
      change who.1 = player at heq
      exact heq
    simpa only [hvalue] using hwho
  · intro hplayer
    let who : RawChild child := ⟨player, not_not.mpr (hsubset hplayer)⟩
    exact ⟨some who, ⟨who, hplayer, rfl⟩, rfl⟩

omit [Fintype ι] in
theorem rawChildReward_eq_original_weight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child : Finset ι) (outside : {who : ι // who ∉ child})
    (terminal : {A : Finset (Option (RawChild child)) // A.Nonempty})
    (original : Finset ι)
    (hmap : terminal.1.map
      (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside) = original)
    (who : Option (RawChild child)) :
    rawChildReward reward child outside terminal who =
      weightOfReward reward original
        (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside who) := by
  have hnonempty : original.Nonempty := hmap ▸ Finset.map_nonempty.mpr terminal.2
  rw [rawChildReward, quittingChildWithOutsiderReward_apply_original]
  simp only [weightOfReward, dite_eq_left hnonempty]
  congr 1
  exact Subtype.ext hmap

theorem rawChild_future_delta
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child coalition : Finset ι) (outside : {who : ι // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty)
    (who : RawChild child) :
    cappedClockExactLPDelta (rawChildReward reward child outside)
      (.future ⟨rawChildCoalition child coalition, hcoalition⟩) who =
      weightOfReward reward {who.1} who.1 - weightOfReward reward coalition who.1 := by
  dsimp only [cappedClockExactLPDelta]
  rw [rawChildReward_eq_original_weight reward child outside _ {who.1} (by simp),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

theorem rawChild_future_base
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child coalition : Finset ι) (outside : {who : ι // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty) :
    cappedClockExactLPBase (rawChildReward reward child outside)
      (.future ⟨rawChildCoalition child coalition, hcoalition⟩) =
      weightOfReward reward {outside.1} outside.1 - weightOfReward reward coalition outside.1 := by
  dsimp only [cappedClockExactLPBase]
  rw [rawChildReward_eq_original_weight reward child outside _ {outside.1} (by simp),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

theorem rawChild_joining_delta
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child coalition : Finset ι) (outside : {who : ι // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty)
    (who : RawChild child) :
    cappedClockExactLPDelta (rawChildReward reward child outside)
      (.joining ⟨rawChildCoalition child coalition, hcoalition⟩) who =
      weightOfReward reward (insert who.1 coalition) who.1 -
        weightOfReward reward coalition who.1 := by
  dsimp only [cappedClockExactLPDelta]
  rw [rawChildReward_eq_original_weight reward child outside _ (insert who.1 coalition) (by
    simp only [cappedClockChildCoalition, Finset.map_insert]
    change insert who.1 ((cappedClockChildCoalition (rawChildCoalition child coalition)).map
      (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside)) = insert who.1 coalition
    exact congrArg (insert who.1) (rawChildCoalition_original_map child coalition outside hsubset)),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

theorem rawChild_joining_base
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (child coalition : Finset ι) (outside : {who : ι // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty) :
    cappedClockExactLPBase (rawChildReward reward child outside)
      (.joining ⟨rawChildCoalition child coalition, hcoalition⟩) =
      weightOfReward reward (insert outside.1 coalition) outside.1 -
        weightOfReward reward coalition outside.1 := by
  dsimp only [cappedClockExactLPBase]
  rw [rawChildReward_eq_original_weight reward child outside _ (insert outside.1 coalition) (by
    simp only [cappedClockJoinedCoalition, Finset.map_insert,
      quittingChildWithOutsiderOriginalEmbedding_none]
    exact congrArg (insert outside.1)
      (rawChildCoalition_original_map child coalition outside hsubset)),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

end GameTheory.QuittingRawChildSource

namespace GameTheory

variable {α : Type} [DecidableEq α]

/-- Actual singleton rewards pulled back from original source coordinates. -/
theorem quittingChildWithOutsiderReward_singleton_original
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (deleted : α → Prop) [DecidablePred deleted] (outside : {who : α // deleted who})
    (owner who : Option (QuittingChildPlayer deleted)) :
    quittingChildWithOutsiderReward reward deleted outside
        ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      reward ⟨{quittingChildWithOutsiderOriginalEmbedding deleted outside owner},
        Finset.singleton_nonempty _⟩
        (quittingChildWithOutsiderOriginalEmbedding deleted outside who) := by
  simpa only [Finset.map_singleton] using
    quittingChildWithOutsiderReward_apply_original reward deleted outside
      ⟨{owner}, Finset.singleton_nonempty owner⟩ who

/-- The actual child coalition is the image of its literal source-player values. -/
theorem quittingChildWithOutsiderReward_childCoalition_image
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (deleted : α → Prop) [DecidablePred deleted] (outside : {who : α // deleted who})
    (A : Finset (QuittingChildPlayer deleted)) (hA : A.Nonempty)
    (who : Option (QuittingChildPlayer deleted)) :
    quittingChildWithOutsiderReward reward deleted outside
        ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ who =
      reward ⟨A.image (fun player => player.1), hA.image (fun player => player.1)⟩
        (quittingChildWithOutsiderOriginalEmbedding deleted outside who) := by
  have hmap : (cappedClockChildCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding deleted outside) =
      A.image (fun player => player.1) :=
    (quittingChildWithOutsiderOriginalEmbedding_childCoalition
      deleted outside A).trans (Finset.map_eq_image _ A)
  simpa only [hmap] using quittingChildWithOutsiderReward_apply_original reward
    deleted outside ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ who

/-- Joining the outsider inserts its actual source-player value in that same image. -/
theorem quittingChildWithOutsiderReward_joinedCoalition_image
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (deleted : α → Prop) [DecidablePred deleted] (outside : {who : α // deleted who})
    (A : Finset (QuittingChildPlayer deleted)) (who : Option (QuittingChildPlayer deleted)) :
    quittingChildWithOutsiderReward reward deleted outside
        ⟨cappedClockJoinedCoalition A, cappedClockJoinedCoalition_nonempty A⟩ who =
      reward ⟨insert outside.1 (A.image (fun player => player.1)),
        Finset.insert_nonempty _ _⟩
        (quittingChildWithOutsiderOriginalEmbedding deleted outside who) := by
  have hmap : (cappedClockChildCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding deleted outside) =
      A.image (fun player => player.1) :=
    (quittingChildWithOutsiderOriginalEmbedding_childCoalition
      deleted outside A).trans (Finset.map_eq_image _ A)
  have hjoined : (cappedClockJoinedCoalition A).map
      (quittingChildWithOutsiderOriginalEmbedding deleted outside) =
      insert outside.1 (A.image (fun player => player.1)) := by
    rw [cappedClockJoinedCoalition, Finset.map_insert,
      quittingChildWithOutsiderOriginalEmbedding_none]
    exact congrArg (insert outside.1) hmap
  simpa only [hjoined] using quittingChildWithOutsiderReward_apply_original reward
    deleted outside ⟨cappedClockJoinedCoalition A, cappedClockJoinedCoalition_nonempty A⟩ who

end GameTheory
