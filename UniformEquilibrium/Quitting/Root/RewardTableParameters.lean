import UniformEquilibrium.Quitting.Root.RewardTableCoordinates
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-! # Deterministic parameters for quitting reward tables -/

namespace GameTheory

open scoped BigOperators

variable {players : Nat}

private def quittingCoalitionCode (coalition : Finset (Fin players)) : Nat :=
  ∑ player ∈ coalition, 2 ^ player.val

private theorem quittingCoalitionCode_injective :
    Function.Injective (@quittingCoalitionCode players) := by
  intro left right hequal
  have himage : left.image Fin.val = right.image Fin.val := by
    apply Finset.geomSum_injective (n := 2) (by omega)
    change (∑ i ∈ left.image Fin.val, 2 ^ i) =
      ∑ i ∈ right.image Fin.val, 2 ^ i
    rw [Finset.sum_image (fun _ _ _ _ hequal => Fin.ext hequal),
      Finset.sum_image (fun _ _ _ _ hequal => Fin.ext hequal)]
    exact hequal
  exact Finset.image_injective Fin.val_injective himage

private def quittingRewardTableVariableOrderKey
    (entry : QuittingRewardTableVariable (Fin players)) :
    Lex (Nat × Fin players) :=
  toLex (quittingCoalitionCode entry.1.1, entry.2)

private theorem quittingRewardTableVariableOrderKey_injective :
    Function.Injective (@quittingRewardTableVariableOrderKey players) := by
  intro left right hequal
  have hpair := toLex.injective hequal
  apply Prod.ext
  · apply Subtype.ext
    exact quittingCoalitionCode_injective (congrArg Prod.fst hpair)
  · exact congrArg
      (fun pair : Nat × Fin players => pair.2) hpair

private def quittingRewardTableVariableLE
    (left right : QuittingRewardTableVariable (Fin players)) : Prop :=
  quittingRewardTableVariableOrderKey left ≤
    quittingRewardTableVariableOrderKey right

private instance : DecidableRel (@quittingRewardTableVariableLE players) :=
  fun left right => by
    unfold quittingRewardTableVariableLE
    infer_instance

private instance : Std.Total (@quittingRewardTableVariableLE players) where
  total left right := le_total (quittingRewardTableVariableOrderKey left)
    (quittingRewardTableVariableOrderKey right)

private instance : IsTrans (QuittingRewardTableVariable (Fin players))
    (@quittingRewardTableVariableLE players) where
  trans _ _ _ := le_trans

private instance : Std.Antisymm (@quittingRewardTableVariableLE players) where
  antisymm _ _ hleft hright :=
    quittingRewardTableVariableOrderKey_injective (le_antisymm hleft hright)

/-- The deterministic lexicographic list of all terminal-reward entries. -/
def quittingRewardTableVariableList (players : Nat) :
    List (QuittingRewardTableVariable (Fin players)) :=
  (Finset.univ : Finset (QuittingRewardTableVariable (Fin players))).sort
    quittingRewardTableVariableLE

/-- The number of independent entries in a quitting reward table. -/
def quittingRewardParameterCount (players : Nat) : Nat :=
  (quittingRewardTableVariableList players).length

/-- The deterministic index of a terminal-reward entry. -/
def quittingRewardTableVariableIndex
    (entry : QuittingRewardTableVariable (Fin players)) :
    Fin (quittingRewardParameterCount players) :=
  ⟨(quittingRewardTableVariableList players).idxOf entry,
    List.idxOf_lt_length_of_mem (by simp [quittingRewardTableVariableList])⟩

@[simp]
theorem quittingRewardTableVariableList_get_index
    (entry : QuittingRewardTableVariable (Fin players)) :
    (quittingRewardTableVariableList players).get
      (quittingRewardTableVariableIndex entry) = entry := by
  apply List.getElem_idxOf

@[simp]
theorem quittingRewardTableVariableIndex_get
    (index : Fin (quittingRewardParameterCount players)) :
    quittingRewardTableVariableIndex
      ((quittingRewardTableVariableList players).get index) = index := by
  apply Fin.ext
  exact List.Nodup.idxOf_getElem
    (Finset.sort_nodup
      (Finset.univ : Finset (QuittingRewardTableVariable (Fin players)))
        quittingRewardTableVariableLE)
    index index.isLt

/-- Decode the deterministic reward parameter block into a real reward table. -/
def quittingRewardFromParameters
    (parameters : Fin (quittingRewardParameterCount players) → ℝ) :
    {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players) :=
  fun terminal observer =>
    parameters (quittingRewardTableVariableIndex (terminal, observer))

/-- Encode a real reward table in the deterministic parameter order. -/
def quittingRewardParameters
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players)) :
    Fin (quittingRewardParameterCount players) → ℝ :=
  fun index =>
    reward ((quittingRewardTableVariableList players).get index).1
      ((quittingRewardTableVariableList players).get index).2

@[simp]
theorem quittingRewardFromParameters_encode
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players)) :
    quittingRewardFromParameters (quittingRewardParameters reward) = reward := by
  funext terminal observer
  change reward
      ((quittingRewardTableVariableList players).get
        (quittingRewardTableVariableIndex (terminal, observer))).1
      ((quittingRewardTableVariableList players).get
        (quittingRewardTableVariableIndex (terminal, observer))).2 = _
  rw [quittingRewardTableVariableList_get_index]

@[simp]
theorem quittingRewardParameters_decode
    (parameters : Fin (quittingRewardParameterCount players) → ℝ) :
    quittingRewardParameters (quittingRewardFromParameters parameters) = parameters := by
  funext index
  change parameters (quittingRewardTableVariableIndex
      ((quittingRewardTableVariableList players).get index)) = parameters index
  rw [quittingRewardTableVariableIndex_get]

end GameTheory
