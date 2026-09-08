import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic

/-! # Deterministic parameters for finite quitting calendars -/

namespace GameTheory

/-- One raw coordinate of a finite quitting calendar. -/
abbrev QuittingFiniteCalendarVariable (players : Type) (deadline : Nat) :=
  players × Option (Fin deadline)

variable {players deadline : Nat}

private def quittingFiniteCalendarVariableOrderKey
    (entry : QuittingFiniteCalendarVariable (Fin players) deadline) :
    Lex (Nat × Nat) :=
  toLex (entry.1.val, entry.2.elim 0 fun time => time.val + 1)

private theorem quittingFiniteCalendarVariableOrderKey_injective :
    Function.Injective (@quittingFiniteCalendarVariableOrderKey players deadline) := by
  rintro ⟨player, choice⟩ ⟨otherPlayer, otherChoice⟩ hequal
  have hpair := toLex.injective hequal
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst hpair)
  · cases choice with
    | none =>
        cases otherChoice with
        | none => rfl
        | some otherTime => simp at hpair
    | some time =>
        cases otherChoice with
        | none => simp at hpair
        | some otherTime =>
            apply congrArg some
            apply Fin.ext
            exact Nat.add_right_cancel (congrArg Prod.snd hpair)

private def quittingFiniteCalendarVariableLE
    (left right : QuittingFiniteCalendarVariable (Fin players) deadline) : Prop :=
  quittingFiniteCalendarVariableOrderKey left ≤
    quittingFiniteCalendarVariableOrderKey right

private instance : DecidableRel
    (@quittingFiniteCalendarVariableLE players deadline) :=
  fun left right => by
    unfold quittingFiniteCalendarVariableLE
    infer_instance

private instance : Std.Total
    (@quittingFiniteCalendarVariableLE players deadline) where
  total left right := le_total (quittingFiniteCalendarVariableOrderKey left)
    (quittingFiniteCalendarVariableOrderKey right)

private instance : IsTrans
    (QuittingFiniteCalendarVariable (Fin players) deadline)
    (@quittingFiniteCalendarVariableLE players deadline) where
  trans _ _ _ := le_trans

private instance : Std.Antisymm
    (@quittingFiniteCalendarVariableLE players deadline) where
  antisymm _ _ hleft hright :=
    quittingFiniteCalendarVariableOrderKey_injective (le_antisymm hleft hright)

/-- The deterministic lexicographic list of finite-calendar coordinates. -/
def quittingFiniteCalendarVariableList (players deadline : Nat) :
    List (QuittingFiniteCalendarVariable (Fin players) deadline) :=
  (Finset.univ : Finset
    (QuittingFiniteCalendarVariable (Fin players) deadline)).sort
      quittingFiniteCalendarVariableLE

/-- The number of raw coordinates in a finite quitting calendar. -/
def quittingFiniteCalendarParameterCount (players deadline : Nat) : Nat :=
  (quittingFiniteCalendarVariableList players deadline).length

@[simp]
theorem quittingFiniteCalendarParameterCount_eq :
    quittingFiniteCalendarParameterCount players deadline =
      players * (deadline + 1) := by
  simp [quittingFiniteCalendarParameterCount, quittingFiniteCalendarVariableList,
    Fintype.card_prod, Fintype.card_option]

/-- The deterministic index of a finite-calendar coordinate. -/
def quittingFiniteCalendarVariableIndex
    (entry : QuittingFiniteCalendarVariable (Fin players) deadline) :
    Fin (quittingFiniteCalendarParameterCount players deadline) :=
  ⟨(quittingFiniteCalendarVariableList players deadline).idxOf entry,
    List.idxOf_lt_length_of_mem (by simp [quittingFiniteCalendarVariableList])⟩

@[simp]
theorem quittingFiniteCalendarVariableList_get_index
    (entry : QuittingFiniteCalendarVariable (Fin players) deadline) :
    (quittingFiniteCalendarVariableList players deadline).get
      (quittingFiniteCalendarVariableIndex entry) = entry := by
  apply List.getElem_idxOf

@[simp]
theorem quittingFiniteCalendarVariableIndex_get
    (index : Fin (quittingFiniteCalendarParameterCount players deadline)) :
    quittingFiniteCalendarVariableIndex
      ((quittingFiniteCalendarVariableList players deadline).get index) = index := by
  apply Fin.ext
  exact List.Nodup.idxOf_getElem
    (Finset.sort_nodup
      (Finset.univ : Finset
        (QuittingFiniteCalendarVariable (Fin players) deadline))
        quittingFiniteCalendarVariableLE)
    index index.isLt

/-- Decode the deterministic parameter block into calendar coordinates. -/
def quittingFiniteCalendarFromParameters
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ) :
    QuittingFiniteCalendarVariable (Fin players) deadline → ℝ :=
  fun entry => parameters (quittingFiniteCalendarVariableIndex entry)

/-- Encode finite-calendar coordinates in deterministic parameter order. -/
def quittingFiniteCalendarParameters
    (calendar : QuittingFiniteCalendarVariable (Fin players) deadline → ℝ) :
    Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ :=
  fun index => calendar ((quittingFiniteCalendarVariableList players deadline).get index)

@[simp]
theorem quittingFiniteCalendarFromParameters_encode
    (calendar : QuittingFiniteCalendarVariable (Fin players) deadline → ℝ) :
    quittingFiniteCalendarFromParameters (quittingFiniteCalendarParameters calendar) =
      calendar := by
  funext entry
  change calendar
      ((quittingFiniteCalendarVariableList players deadline).get
        (quittingFiniteCalendarVariableIndex entry)) = calendar entry
  rw [quittingFiniteCalendarVariableList_get_index]

@[simp]
theorem quittingFiniteCalendarParameters_decode
    (parameters : Fin (quittingFiniteCalendarParameterCount players deadline) → ℝ) :
    quittingFiniteCalendarParameters
        (quittingFiniteCalendarFromParameters parameters) = parameters := by
  funext index
  change parameters
      (quittingFiniteCalendarVariableIndex
        ((quittingFiniteCalendarVariableList players deadline).get index)) =
    parameters index
  rw [quittingFiniteCalendarVariableIndex_get]

end GameTheory
