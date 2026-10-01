import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientPermutation
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual reward automorphisms and their player-orbit response quotient

The blocks are the canonical `MulAction.orbitRel` quotient of an arbitrary
subgroup of player permutations. Finite labels and representatives are
constructed internally; neither response invariance nor favorable blocks
are inputs. The reward hypothesis concerns every actual terminal coordinate.
-/

noncomputable section

open scoped Classical

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- The actual player-orbit quotient, not a separately supplied partition. -/
abbrev QuittingPlayerOrbit (group : Subgroup (Equiv.Perm ι)) :=
  MulAction.orbitRel.Quotient group ι

/-- Number of orbits, including zero for an empty player type. -/
def quittingPlayerOrbitCount (group : Subgroup (Equiv.Perm ι)) : ℕ :=
  Fintype.card (QuittingPlayerOrbit group)

/-- Finite labels of the canonical subgroup orbits. -/
def quittingPlayerOrbitBlock (group : Subgroup (Equiv.Perm ι)) :
    ι → Fin (quittingPlayerOrbitCount group) :=
  fun who => Fintype.equivFin (QuittingPlayerOrbit group)
    (Quotient.mk (MulAction.orbitRel group ι) who)

/-- Choose one original player in each nonempty orbit. -/
def quittingPlayerOrbitRepresentative (group : Subgroup (Equiv.Perm ι)) :
    Fin (quittingPlayerOrbitCount group) → ι :=
  fun coordinate => ((Fintype.equivFin (QuittingPlayerOrbit group)).symm coordinate).out

/-- Equality of the constructed labels is exactly the canonical orbit relation. -/
theorem quittingPlayerOrbitBlock_eq_iff (group : Subgroup (Equiv.Perm ι))
    (first second : ι) :
    quittingPlayerOrbitBlock group first = quittingPlayerOrbitBlock group second ↔
      MulAction.orbitRel group ι first second := by
  constructor
  · intro hequal
    exact Quotient.exact
      ((Fintype.equivFin (QuittingPlayerOrbit group)).injective hequal)
  · intro horbit
    exact congrArg (Fintype.equivFin (QuittingPlayerOrbit group)) (Quotient.sound horbit)

/-- The representative is a section of the actual orbit labeling. -/
theorem quittingPlayerOrbitBlock_representative (group : Subgroup (Equiv.Perm ι))
    (coordinate : Fin (quittingPlayerOrbitCount group)) :
    quittingPlayerOrbitBlock group (quittingPlayerOrbitRepresentative group coordinate) =
      coordinate := by
  unfold quittingPlayerOrbitBlock quittingPlayerOrbitRepresentative
  rw [Quotient.out_eq]
  exact (Fintype.equivFin (QuittingPlayerOrbit group)).apply_symm_apply coordinate

/-- Every subgroup element preserves the internally constructed orbit label. -/
theorem quittingPlayerOrbitBlock_apply (group : Subgroup (Equiv.Perm ι))
    (element : group) (who : ι) :
    quittingPlayerOrbitBlock group ((element : Equiv.Perm ι) who) =
      quittingPlayerOrbitBlock group who := by
  apply (quittingPlayerOrbitBlock_eq_iff group _ who).mpr
  exact ⟨element, rfl⟩

variable [DecidableEq ι]

/-- Literal whole-table covariance yields equality of the actual individual
response residuals on subgroup orbits. No reward signs are required. -/
theorem responseInvariant_of_reward_subgroup_automorphisms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (group : Subgroup (Equiv.Perm ι))
    (hcovariance : ∀ (element : group) terminal who,
      reward (quittingCoalitionEquiv (element : Equiv.Perm ι) terminal)
        ((element : Equiv.Perm ι) who) = reward terminal who) :
    QuittingResponseInvariantOnUnitCube reward (quittingPlayerOrbitBlock group) := by
  intro point _ first second hequal
  have horbit := (quittingPlayerOrbitBlock_eq_iff group first second).mp hequal
  obtain ⟨element, helement⟩ := horbit
  change (element : Equiv.Perm ι) second = first at helement
  have hinvariant (who : ι) :
      quittingBlockLift (quittingPlayerOrbitBlock group) point
          ((element : Equiv.Perm ι) who) =
        quittingBlockLift (quittingPlayerOrbitBlock group) point who := by
    unfold quittingBlockLift
    rw [quittingPlayerOrbitBlock_apply]
  have hrow (terminal : {S : Finset ι // S.Nonempty}) :
      reward (quittingCoalitionEquiv (element : Equiv.Perm ι) terminal)
          ((element : Equiv.Perm ι) second) = reward terminal second + 0 := by
    rw [add_zero]
    exact hcovariance element terminal second
  have hresponse := quittingDiscountedDisplacement_equiv_centered
    (element : Equiv.Perm ι) (quittingBlockLift (quittingPlayerOrbitBlock group) point)
    hinvariant reward second 0 hrow
  rwa [helement] at hresponse

end GameTheory
