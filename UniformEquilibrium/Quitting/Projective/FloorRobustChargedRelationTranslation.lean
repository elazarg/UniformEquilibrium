import UniformEquilibrium.Quitting.Projective.FloorRobustChargedRelation
import UniformEquilibrium.Quitting.Projective.RobustChargedRelationTranslation

/-! # Common upward translation and zero-extension drift with endpoint floors -/

noncomputable section

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {coalition : Finset player // coalition.Nonempty} → Payoff player}
variable {floor : Payoff player} {epsilon bound : ℝ}

/-- The inner approximate floor improves under a nonnegative common translation. -/
def QuittingFloorRobustChargedState.vectorTranslate
    (state : QuittingFloorRobustChargedState floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    QuittingFloorRobustChargedState floor epsilon (bound + 1) :=
  ⟨quittingPayoffVectorTranslate state.1 shift, fun who ↦
    ⟨quittingPayoffVectorTranslate_mem_enlargedBox state.forgetFloor shift epsilon
      hshiftNonneg hshiftUpper hepsilonMax who, by
      have hfloor := (state.2 who).2
      dsimp only [quittingPayoffVectorTranslate]
      linarith [hshiftNonneg who]⟩⟩

/-- Every floor-bearing inner edge translates to an outer edge with the same literal root. -/
def QuittingFloorRobustChargedEdge.vectorTranslate
    (edge : QuittingFloorRobustChargedEdge reward floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    QuittingFloorRobustChargedEdge reward floor epsilon (bound + 1) := by
  refine ⟨QuittingRobustChargedEdge.vectorTranslate edge.1 shift hepsilon hepsilonMax
    hshiftNonneg hshiftUpper, ?_⟩
  intro who
  simp only [QuittingRobustChargedEdge.vectorTranslate_source,
    QuittingRobustChargedEdge.vectorTranslate_target, quittingPayoffVectorTranslate]
  have hfloor := edge.2 who
  constructor <;> linarith [hshiftNonneg who]

@[simp] theorem QuittingFloorRobustChargedEdge.vectorTranslate_root
    (edge : QuittingFloorRobustChargedEdge reward floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (edge.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper).1.1.1.2 =
      edge.1.1.1.2 := rfl

@[simp] theorem QuittingFloorRobustChargedEdge.vectorTranslate_src
    (edge : QuittingFloorRobustChargedEdge reward floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (quittingFloorRobustChargedRelation reward floor epsilon (bound + 1)).src
        (edge.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper) =
      QuittingFloorRobustChargedState.vectorTranslate
        ((quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).src edge)
        shift hepsilon hepsilonMax hshiftNonneg hshiftUpper := rfl

@[simp] theorem QuittingFloorRobustChargedEdge.vectorTranslate_tgt
    (edge : QuittingFloorRobustChargedEdge reward floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (quittingFloorRobustChargedRelation reward floor epsilon (bound + 1)).tgt
        (edge.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper) =
      QuittingFloorRobustChargedState.vectorTranslate
        ((quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).tgt edge)
        shift hepsilon hepsilonMax hshiftNonneg hshiftUpper := rfl

@[simp] theorem QuittingFloorRobustChargedEdge.vectorTranslate_charge
    (edge : QuittingFloorRobustChargedEdge reward floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (quittingFloorRobustChargedRelation reward floor epsilon (bound + 1)).charge
        (edge.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper) =
      (quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).charge edge := rfl

omit [Fintype player] [DecidableEq player] in
/-- The ambient zero extension reads the actual outer value at every translated inner state. -/
theorem extend_floorRobustValue_vectorTranslate
    (value : QuittingFloorRobustChargedState floor epsilon (bound + 1) → ℝ)
    (state : QuittingFloorRobustChargedState floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    Function.extend Subtype.val value (fun _ ↦ 0)
        (quittingPayoffVectorTranslate state.1 shift) =
      value (state.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper) :=
  Subtype.val_injective.extend_apply value (fun _ ↦ 0)
    (state.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper)

/-- Outer potential drift remains literal after zero extension and every admissible common
translation. This is the input required by one-sided smoothing on the inner floor domain. -/
theorem floorRobust_zeroExtension_translated_drift
    (value : QuittingFloorRobustChargedState floor epsilon (bound + 1) → ℝ)
    (hpotential : (quittingFloorRobustChargedRelation reward floor epsilon (bound + 1)).IsPotential
      value)
    (edge : QuittingFloorRobustChargedEdge reward floor (epsilon / 4) bound)
    (shift : Payoff player) (hepsilon : 0 ≤ epsilon) (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who) (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).charge edge +
        Function.extend Subtype.val value (fun _ ↦ 0)
          (quittingPayoffVectorTranslate edge.1.1.2.1 shift) ≤
      Function.extend Subtype.val value (fun _ ↦ 0)
        (quittingPayoffVectorTranslate edge.1.1.1.1.1 shift) := by
  have htarget := extend_floorRobustValue_vectorTranslate value
    ((quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).tgt edge)
    shift hepsilon hepsilonMax hshiftNonneg hshiftUpper
  have hsource := extend_floorRobustValue_vectorTranslate value
    ((quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).src edge)
    shift hepsilon hepsilonMax hshiftNonneg hshiftUpper
  have htranslated := hpotential
    (edge.vectorTranslate shift hepsilon hepsilonMax hshiftNonneg hshiftUpper)
  rw [QuittingFloorRobustChargedEdge.vectorTranslate_src,
    QuittingFloorRobustChargedEdge.vectorTranslate_tgt,
    QuittingFloorRobustChargedEdge.vectorTranslate_charge] at htranslated
  change _ + Function.extend Subtype.val value (fun _ ↦ 0)
      (quittingPayoffVectorTranslate
        ((quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).tgt edge).1 shift) ≤
    Function.extend Subtype.val value (fun _ ↦ 0)
      (quittingPayoffVectorTranslate
        ((quittingFloorRobustChargedRelation reward floor (epsilon / 4) bound).src edge).1 shift)
  rw [htarget, hsource]
  linarith

end GameTheory
