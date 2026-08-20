/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargeCapacity

/-!
# Exact punishment-floor prefixes as admissible charged paths

Every exact punishment-floor prefix is a literal path in the full
floor-admissible charged relation.  The decoding preserves every displayed
value, root, and absorption charge.  This module also names the remaining
capacity of the global admissible budget-to-go at an arbitrary boxed state.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-! ## Exact prefixes are admissible charged paths -/

/-- The root stored at one prefix value.  At time zero it is irrelevant;
later it records the root which produced that value. -/
def quittingFinitePrefixStoredRoot
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ℕ → QuittingRootSimplex ι
  | 0 => quittingAllContinueSimplexRoot
  | time + 1 => fun who ↦ stdSimplexEquiv (cert.roots time who)

@[simp]
theorem quittingRootOfSimplex_finitePrefixStoredRoot_succ
    (cert : QuittingPunishmentFloorFinitePrefix reward) (time : ℕ) :
    quittingRootOfSimplex (quittingFinitePrefixStoredRoot cert (time + 1)) =
      cert.roots time := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (cert.roots time who)

/-- One displayed prefix value as a boxed floor-admissible state. -/
def quittingFinitePrefixAdmissibleState
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time ≤ cert.horizon) :
    QuittingPunishmentFloorAdmissibleState reward :=
  ⟨⟨(cert.value time, quittingFinitePrefixStoredRoot cert time),
      cert.value_mem time htime⟩,
    fun who ↦ quittingPunishmentValue_le_finitePrefixValue
      cert time htime who⟩

/-- One exact prefix transition as an edge of the full admissible relation. -/
def quittingFinitePrefixAdmissibleEdge
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time < cert.horizon) :
    QuittingPunishmentFloorAdmissibleEdge reward where
  tail := quittingFinitePrefixAdmissibleState cert time htime.le
  current := quittingFinitePrefixAdmissibleState cert (time + 1) htime
  exactEdge := by
    constructor
    · change cert.value (time + 1) = quittingRootSuccessorPayoff reward
        (cert.value time)
          (quittingRootOfSimplex
            (quittingFinitePrefixStoredRoot cert (time + 1)))
      rw [quittingRootOfSimplex_finitePrefixStoredRoot_succ]
      exact cert.policy time htime
    · change IsεQuittingRootEndpointNash reward (cert.value time) 0
        (quittingRootOfSimplex
          (quittingFinitePrefixStoredRoot cert (time + 1)))
      rw [quittingRootOfSimplex_finitePrefixStoredRoot_succ]
      exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (cert.value time) (cert.roots time)).2
          (cert.exactNash time htime)

/-- The initial segment of an exact prefix, as a literal admissible path. -/
def quittingFinitePrefixAdmissiblePath
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ∀ (time : ℕ) (htime : time ≤ cert.horizon),
      (AdmissibleRelation reward).Path
        (quittingFinitePrefixAdmissibleState cert 0 (by omega))
        (quittingFinitePrefixAdmissibleState cert time htime)
  | 0, htime => ChargedRelation.Path.nil _
  | time + 1, htime => by
      let path := quittingFinitePrefixAdmissiblePath cert time (by omega)
      let edge := quittingFinitePrefixAdmissibleEdge cert time (by omega)
      exact path.append (ChargedRelation.Path.edge edge rfl rfl)

/-- Decoding preserves the exact cumulative absorption charge. -/
theorem chargeSum_quittingFinitePrefixAdmissiblePath
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ∀ (time : ℕ) (htime : time ≤ cert.horizon),
      (quittingFinitePrefixAdmissiblePath cert time htime).chargeSum =
        ∑ offset ∈ Finset.range time,
          quittingRootAbsorptionMass (cert.roots offset)
  | 0, htime => by
      simp [quittingFinitePrefixAdmissiblePath]
  | time + 1, htime => by
      rw [Finset.sum_range_succ]
      simp only [quittingFinitePrefixAdmissiblePath,
        ChargedRelation.Path.chargeSum_append,
        ChargedRelation.Path.chargeSum_edge]
      rw [chargeSum_quittingFinitePrefixAdmissiblePath cert time]
      change _ + quittingRootAbsorptionMass
          (quittingRootOfSimplex
            (quittingFinitePrefixStoredRoot cert (time + 1))) = _
      rw [quittingRootOfSimplex_finitePrefixStoredRoot_succ]

/-- The full decoded prefix has exactly the certificate's charge. -/
theorem chargeSum_quittingFinitePrefixAdmissiblePath_horizon
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    (quittingFinitePrefixAdmissiblePath cert cert.horizon (by omega)).chargeSum =
      cert.charge := by
  rw [chargeSum_quittingFinitePrefixAdmissiblePath]
  rfl

/-! ## Remaining global admissible capacity -/

/-- Remaining capacity of the full floor-admissible budget-to-go at an
arbitrary boxed state. -/
def quittingPunishmentFloorAdmissibleRemainingCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (state : QuittingPunishmentFloorAdmissibleState reward) : ℝ :=
  quittingPunishmentFloorPrefixChargeBound reward -
    quittingPunishmentFloorAdmissiblePotential reward state

end GameTheory
