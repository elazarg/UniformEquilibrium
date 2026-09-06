import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases

/-! # Relabeling pairs of edges on four vertices -/

namespace Math

def finFourFirstPair : Finset (Fin 4) := {0, 1}
def finFourAdjacentPair : Finset (Fin 4) := {0, 2}
def finFourDisjointPair : Finset (Fin 4) := {2, 3}

private def firstThree : Fin 3 → Fin 4 | 0 => 0 | 1 => 1 | 2 => 2

private theorem firstThree_injective : Function.Injective firstThree := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [firstThree]

private theorem exists_adjacent_relabel (a b c : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e : Equiv.Perm (Fin 4),
      finFourFirstPair.map e.toEmbedding = {a, b} ∧
      finFourAdjacentPair.map e.toEmbedding = {a, c} := by
  let target : Fin 3 → Fin 4 := fun | 0 => a | 1 => b | 2 => c
  have ht : Function.Injective target := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [target]
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    firstThree target firstThree_injective ht
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  simp [firstThree, target] at he0 he1 he2
  refine ⟨e, ?_, ?_⟩ <;>
    simp [finFourFirstPair, finFourAdjacentPair, he0, he1, he2]

private theorem exists_disjoint_relabel (a b c d : Fin 4)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ e : Equiv.Perm (Fin 4),
      finFourFirstPair.map e.toEmbedding = {a, b} ∧
      finFourDisjointPair.map e.toEmbedding = {c, d} := by
  let target : Fin 4 → Fin 4 := fun | 0 => a | 1 => b | 2 => c | 3 => d
  have ht : Function.Injective target := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [target]
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (Equiv.refl (Fin 4)) target (Equiv.refl (Fin 4)).injective ht
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  have he3 := he 3
  simp [target] at he0 he1 he2 he3
  refine ⟨e, ?_, ?_⟩ <;>
    simp [finFourFirstPair, finFourDisjointPair, he0, he1, he2, he3]

/-- Every ordered pair of distinct `K₄` edges is a relabeling of a canonical
adjacent or disjoint ordered pair. -/
theorem exists_finFour_pair_relabel
    (first second : Finset (Fin 4)) (hfirst : first.card = 2)
    (hsecond : second.card = 2) (hne : first ≠ second) :
    ∃ e : Equiv.Perm (Fin 4),
      (finFourFirstPair.map e.toEmbedding = first ∧
        finFourAdjacentPair.map e.toEmbedding = second) ∨
      (finFourFirstPair.map e.toEmbedding = first ∧
        finFourDisjointPair.map e.toEmbedding = second) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hfirst
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hsecond
  by_cases hac : a = c
  · subst c
    have hbd : b ≠ d := by intro h; subst d; exact hne rfl
    obtain ⟨e, h₁, h₂⟩ := exists_adjacent_relabel a b d hab hcd hbd
    exact ⟨e, Or.inl ⟨h₁, h₂⟩⟩
  · by_cases had : a = d
    · subst d
      have hbc : b ≠ c := by
        intro h; subst c; apply hne; ext x; simp [or_comm]
      obtain ⟨e, h₁, h₂⟩ := exists_adjacent_relabel a b c hab hcd.symm hbc
      exact ⟨e, Or.inl ⟨h₁, by simpa [Finset.pair_comm] using h₂⟩⟩
    · by_cases hbc : b = c
      · subst c
        obtain ⟨e, h₁, h₂⟩ := exists_adjacent_relabel b a d hab.symm hcd had
        exact ⟨e, Or.inl ⟨by simpa [Finset.pair_comm] using h₁, h₂⟩⟩
      · by_cases hbd : b = d
        · subst d
          obtain ⟨e, h₁, h₂⟩ := exists_adjacent_relabel b a c hab.symm hcd.symm hac
          exact ⟨e, Or.inl ⟨by simpa [Finset.pair_comm] using h₁,
            by simpa [Finset.pair_comm] using h₂⟩⟩
        · obtain ⟨e, h₁, h₂⟩ :=
            exists_disjoint_relabel a b c d hab hcd hac had hbc hbd
          exact ⟨e, Or.inr ⟨h₁, h₂⟩⟩

end Math
