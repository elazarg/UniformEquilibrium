import Mathlib

/-!
# Coalition orbit transport

This coalition-specific experiment isolates the elementary group-action
reduction used by `ideas/CoalitionSplittingGroupActions.md`.

Player permutations act on coalitions, preserve complements and cardinality,
and make all singleton splits conjugate.  More abstractly, for a transitive
player action, one property at an orbit representative extends to every
player as soon as the property transports under the action.
-/

noncomputable section

namespace Research.CoalitionOrbitTransport

variable {ι : Type}

/-- Image of a coalition under a player permutation. -/
def permuteCoalition (permutation : Equiv.Perm ι)
    (coalition : Finset ι) : Finset ι :=
  coalition.map permutation.toEmbedding

@[simp] theorem mem_permuteCoalition
    (permutation : Equiv.Perm ι) (coalition : Finset ι) (player : ι) :
    player ∈ permuteCoalition permutation coalition ↔
      permutation.symm player ∈ coalition := by
  constructor
  · intro membership
    rw [permuteCoalition, Finset.mem_map] at membership
    obtain ⟨source, source_mem, mapped⟩ := membership
    simpa [← mapped] using source_mem
  · intro membership
    rw [permuteCoalition, Finset.mem_map]
    exact ⟨permutation.symm player, membership,
      permutation.apply_symm_apply player⟩

@[simp] theorem card_permuteCoalition
    (permutation : Equiv.Perm ι) (coalition : Finset ι) :
    (permuteCoalition permutation coalition).card = coalition.card := by
  simp [permuteCoalition]

@[simp] theorem permuteCoalition_empty (permutation : Equiv.Perm ι) :
    permuteCoalition permutation ∅ = ∅ := by
  simp [permuteCoalition]

@[simp] theorem permuteCoalition_univ [Fintype ι]
    (permutation : Equiv.Perm ι) :
    permuteCoalition permutation Finset.univ = Finset.univ := by
  classical
  ext player
  simp

/-- Player relabeling commutes with taking the complementary side of a split. -/
theorem permuteCoalition_compl
    [Fintype ι] [DecidableEq ι]
    (permutation : Equiv.Perm ι) (coalition : Finset ι) :
    permuteCoalition permutation (Finset.univ \ coalition) =
      Finset.univ \ permuteCoalition permutation coalition := by
  ext player
  simp

@[simp] theorem permuteCoalition_singleton
    (permutation : Equiv.Perm ι) (player : ι) :
    permuteCoalition permutation {player} = {permutation player} := by
  classical
  ext candidate
  rw [mem_permuteCoalition, Finset.mem_singleton, Finset.mem_singleton]
  constructor
  · intro equality
    calc
      candidate = permutation (permutation.symm candidate) :=
        (permutation.apply_symm_apply candidate).symm
      _ = permutation player := congrArg permutation equality
  · intro equality
    calc
      permutation.symm candidate =
          permutation.symm (permutation player) :=
        congrArg permutation.symm equality
      _ = player := permutation.symm_apply_apply player

/-- All singleton-versus-complement splits are in one orbit under the full
player permutation group. -/
theorem exists_permutation_singleton_to_singleton
    (first last : ι) :
    ∃ permutation : Equiv.Perm ι,
      permuteCoalition permutation {first} = {last} := by
  classical
  exact ⟨Equiv.swap first last, by simp⟩

/-- Coalitions of the same cardinality are conjugate under the full player
permutation group. -/
theorem exists_permutation_coalition_to_coalition
    (first last : Finset ι) (card_eq : first.card = last.card) :
    ∃ permutation : Equiv.Perm ι,
      permuteCoalition permutation first = last := by
  simpa only [permuteCoalition] using
    Equiv.Perm.exists_map_finset_eq first last card_eq

/-- Cardinality completely classifies coalition orbits under all player
permutations. -/
theorem exists_permutation_coalition_to_coalition_iff
    (first last : Finset ι) :
    (∃ permutation : Equiv.Perm ι,
      permuteCoalition permutation first = last) ↔
      first.card = last.card := by
  constructor
  · rintro ⟨permutation, equality⟩
    rw [← equality, card_permuteCoalition]
  · exact exists_permutation_coalition_to_coalition first last

/-! ## Abstract transport from one player-orbit representative -/

variable {Gamma Player : Type} [Group Gamma] [MulAction Gamma Player]
  [MulAction.IsPretransitive Gamma Player]

/-- In a transitive action, an action-stable property needs to be proved at
only one representative.  In the intended application `property i` is the
existence of player `i`'s singleton-split one-sided uniform security
certificate, and `transport` is supplied by a stochastic-game automorphism. -/
theorem forall_of_representative_of_transport
    (property : Player → Prop) (representative : Player)
    (atRepresentative : property representative)
    (transport : ∀ (g : Gamma) (player : Player),
      property player → property (g • player)) :
    ∀ player, property player := by
  intro player
  obtain ⟨g, moved⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := Gamma)
      representative player
  rw [← moved]
  exact transport g representative atRepresentative

end Research.CoalitionOrbitTransport
