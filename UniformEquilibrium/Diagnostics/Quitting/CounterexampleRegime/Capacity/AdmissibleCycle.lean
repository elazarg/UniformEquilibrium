/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation

/-!
# Positive cycles in the full punishment-floor admissible relation

Every path in the full floor-admissible exact Nash--Bellman relation decodes
to a literal punishment-floor finite prefix.  A positive closed path can
therefore be iterated to produce prefixes of arbitrarily large absorption
charge and hence a uniform-equilibrium payoff.

This is a consumer for an exact return.  It does not construct an admissible
edge or return path from stopping-law reset geometry.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleRelation :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-- A positive closed admissible path produces exact punishment-floor
prefixes above every real charge threshold. -/
theorem exists_floorPrefix_charge_gt_of_positive_admissible_cycle
    {state : QuittingPunishmentFloorAdmissibleState reward}
    (cycle : AdmissibleRelation.Path state state)
    (hpositive : 0 < cycle.chargeSum) (bound : ℝ) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      bound < cert.charge := by
  obtain ⟨count, hcount⟩ := exists_nat_gt (bound / cycle.chargeSum)
  let path := cycle.iterate count
  refine ⟨QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix
    path, ?_⟩
  rw [QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge,
    ChargedRelation.Path.chargeSum_iterate]
  exact (div_lt_iff₀ hpositive).mp hcount

private theorem nonempty_of_positive_admissible_cycle
    {state : QuittingPunishmentFloorAdmissibleState reward}
    (cycle : AdmissibleRelation.Path state state)
    (hpositive : 0 < cycle.chargeSum) : Nonempty ι := by
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · letI : IsEmpty ι := hempty
    exfalso
    have hedgeZero : ∀ edge : QuittingPunishmentFloorAdmissibleEdge reward,
        edge.toBoxEdge.absorptionCharge = 0 := by
      intro edge
      unfold QuittingPunishmentFloorBoxEdge.absorptionCharge
      have hroot : edge.toBoxEdge.root = quittingAllContinueRoot := by
        funext who
        exact isEmptyElim who
      rw [hroot, quittingRootAbsorptionMass_allContinueRoot]
    have pathChargeSum_eq_zero :
        ∀ {source target : QuittingPunishmentFloorAdmissibleState reward}
          (path : AdmissibleRelation.Path source target),
          path.chargeSum = 0 := by
      intro source target path
      induction path with
      | nil state => rfl
      | cons edge rest ih =>
          rw [ChargedRelation.Path.chargeSum_cons, ih, add_zero]
          exact hedgeZero edge
    have hzero : cycle.chargeSum = 0 := pathChargeSum_eq_zero cycle
    linarith
  · exact hnonempty

/-- A positive cycle in the full floor-admissible predecessor relation
certifies existence of a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_positive_admissible_cycle
    {state : QuittingPunishmentFloorAdmissibleState reward}
    (cycle : AdmissibleRelation.Path state state)
    (hpositive : 0 < cycle.chargeSum) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  letI : Nonempty ι :=
    nonempty_of_positive_admissible_cycle cycle hpositive
  apply quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge reward
  intro chargeTarget _hchargeTarget
  obtain ⟨cert, hcharge⟩ :=
    exists_floorPrefix_charge_gt_of_positive_admissible_cycle
      cycle hpositive chargeTarget
  exact ⟨cert, hcharge.le⟩

/-- A positive admissible edge followed by an exact return path certifies a
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_positive_admissible_return
    (edge : QuittingPunishmentFloorAdmissibleEdge reward)
    (returnPath : AdmissibleRelation.Path edge.current edge.tail)
    (hpositive : 0 < edge.toBoxEdge.absorptionCharge) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformPayoff_of_positive_admissible_cycle
    (ChargedRelation.Path.cons edge returnPath)
  change 0 < edge.toBoxEdge.absorptionCharge + returnPath.chargeSum
  nlinarith [returnPath.chargeSum_nonneg]

namespace QuittingCounterexampleRegime

/-- Every closed path in the full floor-admissible predecessor relation has
zero charge inside a counterexample regime. -/
theorem admissible_cycle_chargeSum_eq_zero
    (regime : QuittingCounterexampleRegime reward)
    {state : QuittingPunishmentFloorAdmissibleState reward}
    (cycle : AdmissibleRelation.Path state state) :
    cycle.chargeSum = 0 := by
  have hbudget : AdmissibleRelation.HasFiniteBudget :=
    quittingPunishmentFloorAdmissible_hasFiniteBudget_of_finitePrefixChargeBound
      regime.prefixCharge_le
  have hnotPositive : ¬ 0 < cycle.chargeSum := by
    intro hpositive
    exact AdmissibleRelation.not_hasFiniteBudget_of_positive_cycle
      cycle hpositive hbudget
  exact le_antisymm (le_of_not_gt hnotPositive) cycle.chargeSum_nonneg

end QuittingCounterexampleRegime

end GameTheory
