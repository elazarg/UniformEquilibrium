import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # Finite compression of arbitrary response-block labels

Only labels used by the finite player set matter. Compression retains all
block equalities and the actual response-invariance condition, without a
finiteness or surjectivity assumption on the original label type.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*}

theorem exists_responseInvariant_finite_compression
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → κ)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block) :
    ∃ compressed : ι → Fin (Fintype.card ι),
      (∀ first second, compressed first = compressed second ↔ block first = block second) ∧
        QuittingResponseInvariantOnUnitCube reward compressed := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · let := hempty
    refine ⟨fun player => isEmptyElim player, ?_, ?_⟩
    · intro first
      exact isEmptyElim first
    · intro point hpoint first
      exact isEmptyElim first
  · let := hnonempty
    let representative : κ → ι := fun label =>
      if h : ∃ player, block player = label then Classical.choose h else Classical.arbitrary ι
    let code : κ → Fin (Fintype.card ι) := fun label =>
      Fintype.equivFin ι (representative label)
    let compressed : ι → Fin (Fintype.card ι) := fun player => code (block player)
    have hrepresentative (player : ι) :
        block (representative (block player)) = block player := by
      have hexists : ∃ other, block other = block player := ⟨player, rfl⟩
      dsimp only [representative]
      rw [dite_eq_left hexists]
      exact Classical.choose_spec hexists
    refine ⟨compressed, ?_, ?_⟩
    · intro first second
      constructor
      · intro heq
        have hrep : representative (block first) = representative (block second) :=
          (Fintype.equivFin ι).injective heq
        exact (hrepresentative first).symm.trans
          ((congrArg block hrep).trans (hrepresentative second))
      · intro heq
        exact congrArg code heq
    · intro point hpoint first second hsame
      have hblock : block first = block second := by
        have hrep : representative (block first) = representative (block second) :=
          (Fintype.equivFin ι).injective hsame
        exact (hrepresentative first).symm.trans
          ((congrArg block hrep).trans (hrepresentative second))
      exact hresponse (fun label => point (code label))
        (fun label => hpoint (code label)) first second hblock

end GameTheory
