import Mathlib.Data.List.Basic
import Mathlib.Data.Sign.Defs

/-!
# Tagged alternating-row condensation

This executable transformation removes point rows whose retained polynomial
columns contain no zero.  Payloads are opaque and travel with their complete
rows, so the transformation can retain cut origins or inferred signs without
examining them.
-/

namespace MathUE.OrderedRealSignDiagram

/-- Extract the entries at point positions from an alternating row list. -/
def pointEntries : List β → List β
  | _left :: point :: rest => point :: pointEntries rest
  | _ => []

/-- Remove a point row when none of its retained polynomial signs is zero.
The interval immediately to its right is removed at the same time. -/
def condenseTaggedRows : List (List SignType × α) → List (List SignType × α)
  | left :: point :: rest =>
      let tail := condenseTaggedRows rest
      if 0 ∈ point.1 then left :: point :: tail else left :: tail.drop 1
  | rows => rows

@[simp] theorem condenseTaggedRows_nil :
    condenseTaggedRows ([] : List (List SignType × α)) = [] :=
  rfl

@[simp] theorem condenseTaggedRows_singleton (row : List SignType × α) :
    condenseTaggedRows [row] = [row] :=
  rfl

/-- Condensation preserves the first tagged row whenever one exists. -/
theorem head?_condenseTaggedRows (rows : List (List SignType × α)) :
    (condenseTaggedRows rows).head? = rows.head? := by
  cases rows with
  | nil => rfl
  | cons left rest =>
      cases rest with
      | nil => rfl
      | cons point rest =>
          rw [condenseTaggedRows]
          split <;> rfl

private theorem pointEntries_cons_drop_tail (left : β) (tail : List β) :
    pointEntries (left :: tail.drop 1) = pointEntries tail := by
  cases tail with
  | nil => rfl
  | cons first rest =>
      cases rest <;> rfl

/-- Exact trace invariant: the output point entries are precisely the input
point entries whose sign row contains a zero, in their original order and with
their payloads unchanged. -/
theorem pointEntries_condenseTaggedRows :
    ∀ rows : List (List SignType × α),
      pointEntries (condenseTaggedRows rows) =
        (pointEntries rows).filter (fun point => decide (0 ∈ point.1))
  | [] => rfl
  | [left] => rfl
  | left :: point :: rest => by
      rw [condenseTaggedRows]
      split
      · rename_i hzero
        simp [pointEntries, hzero, pointEntries_condenseTaggedRows rest]
      · rename_i hnoZero
        rw [pointEntries_cons_drop_tail]
        simp [pointEntries, hnoZero, pointEntries_condenseTaggedRows rest]

/-- Retained tagged point entries form an order-preserving sublist of the
original point entries. -/
theorem pointEntries_condenseTaggedRows_sublist
    (rows : List (List SignType × α)) :
    List.Sublist (pointEntries (condenseTaggedRows rows)) (pointEntries rows) := by
  rw [pointEntries_condenseTaggedRows]
  exact List.filter_sublist

/-- Point payloads are exactly those attached to retained original point rows,
in original order. -/
theorem pointPayloads_condenseTaggedRows
    (rows : List (List SignType × α)) :
    (pointEntries (condenseTaggedRows rows)).map Prod.snd =
      ((pointEntries rows).filter (fun point => decide (0 ∈ point.1))).map Prod.snd := by
  rw [pointEntries_condenseTaggedRows]

end MathUE.OrderedRealSignDiagram
