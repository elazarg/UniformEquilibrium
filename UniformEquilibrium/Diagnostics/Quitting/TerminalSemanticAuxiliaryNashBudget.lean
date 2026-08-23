/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticWeightedAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

/-!
# Weight-one auxiliary Nash budget and positive minimum plateau

The weighted auxiliary-target budget is the canonical argument.  This module
retains the original unweighted API as weight-one corollaries and packages its
global positive-minimum plateau consequence.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

omit [DecidableEq ι] in
/-- Weight one identifies weighted terminal-semantic debt with total debt. -/
@[simp]
theorem quittingTerminalSemanticWeightedDebtSum_one
    (pair : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair =
      quittingTerminalSemanticDebtSum pair := by
  simp [quittingTerminalSemanticWeightedDebtSum,
    quittingTerminalSemanticDebtSum]

/-- The unweighted absorption budget is the weight-one weighted budget. -/
theorem minimumTerminalSemantic_auxiliaryNash_budget
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hh : ∀ who, 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - h who) ≤ 0 := by
  have hminimumOne : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair ≤
        quittingTerminalSemanticWeightedDebtSum (fun _ => 1) candidate := by
    simpa using hminimum
  simpa using minimumTerminalSemantic_weightedAuxiliaryNash_budget
    (reward := reward) (fun _ => 1) pair h root hpair hminimumOne
      (fun _ => zero_le_one) hh hnash

/-- The unweighted open auxiliary cube is the weight-one anisotropic moat. -/
theorem minimumTerminalSemantic_auxiliaryNash_eq_allContinue
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hh : ∀ who, 0 ≤ h who)
    (hstrict : ∀ who, h who < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hminimumOne : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair ≤
        quittingTerminalSemanticWeightedDebtSum (fun _ => 1) candidate := by
    simpa using hminimum
  have hpositiveOne :
      0 < quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair := by
    simpa using hpositive
  apply minimumTerminalSemantic_weightedAuxiliaryNash_eq_allContinue
    (reward := reward) (fun _ => 1) pair h root hpair hminimumOne hpositiveOne
      (fun _ => zero_le_one) hh
  · simpa using hstrict
  · exact hnash

/-- The unweighted critical face is the weight-one weighted critical face. -/
theorem minimumTerminalSemantic_auxiliaryNash_criticalFace
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hh : ∀ who, 0 ≤ h who)
    (hle : ∀ who, h who ≤ quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    quittingRootCollisionMass root = 0 ∧
      ∀ who, 0 < quittingRootCoalitionMass root {who} →
        h who = quittingTerminalSemanticDebtSum pair := by
  have hminimumOne : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair ≤
        quittingTerminalSemanticWeightedDebtSum (fun _ => 1) candidate := by
    simpa using hminimum
  have hpositiveOne :
      0 < quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair := by
    simpa using hpositive
  simpa using minimumTerminalSemantic_weightedAuxiliaryNash_criticalFace
    (reward := reward) (fun _ => 1) pair h root hpair hminimumOne hpositiveOne
      (fun _ => zero_le_one) hh (by simpa using hle) hnash

/-- Every exact Nash root against the prescribed coordinate of a positive
minimum semantic pair is collision-free.  Any singleton quitter carries the
entire total debt. -/
theorem minimumTerminalSemantic_exactNash_criticalFace
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingRootCollisionMass root = 0 ∧
      ∀ who, 0 < quittingRootCoalitionMass root {who} →
        quittingTerminalSemanticDebt pair who =
          quittingTerminalSemanticDebtSum pair := by
  let debt : Payoff ι := fun who => quittingTerminalSemanticDebt pair who
  have hdebtNonneg : ∀ who, 0 ≤ debt who := fun who =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  have hdebtLe : ∀ who,
      debt who ≤ quittingTerminalSemanticDebtSum pair := by
    intro who
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have htail : pair.2 - debt = pair.1 := by
    funext who
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hnashAux : IsεQuittingRootNash reward (pair.2 - debt) 0 root := by
    rw [htail]
    exact hnash
  simpa [debt] using minimumTerminalSemantic_auxiliaryNash_criticalFace
    (reward := reward) pair debt root hpair hminimum hpositive hdebtNonneg
      hdebtLe hnashAux

/-- The unweighted singleton margin is the weight-one weighted margin. -/
theorem minimumTerminalSemantic_singletonMargin
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    quittingTerminalSemanticDebtSum pair ≤ pair.2 who -
      reward (quittingSingletonTerminal who) who := by
  have hminimumOne : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair ≤
        quittingTerminalSemanticWeightedDebtSum (fun _ => 1) candidate := by
    simpa using hminimum
  have hpositiveOne :
      0 < quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair := by
    simpa using hpositive
  simpa using minimumTerminalSemantic_weightedSingletonMargin
    (reward := reward) (fun _ => 1) pair hpair hminimumOne hpositiveOne
      (fun _ => zero_lt_one) who

/-- Every positive minimum semantic pair is an exact all-Continue Nash
self-loop, and has the quantitative singleton margin above. -/
theorem minimumTerminalSemantic_is_allContinuePlateau
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
        pair ∧
      ∀ who, quittingTerminalSemanticDebtSum pair ≤ pair.2 who -
        reward (quittingSingletonTerminal who) who := by
  have hminimumOne : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair ≤
        quittingTerminalSemanticWeightedDebtSum (fun _ => 1) candidate := by
    simpa using hminimum
  have hpositiveOne :
      0 < quittingTerminalSemanticWeightedDebtSum (fun _ => 1) pair := by
    simpa using hpositive
  obtain ⟨hnash, hprefix⟩ :=
    minimumTerminalSemantic_weightedIs_allContinuePlateau
      (reward := reward) (fun _ => 1) pair hpair hminimumOne hpositiveOne
        (fun _ => zero_lt_one)
  exact ⟨hnash, hprefix,
    minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hpair hminimum hpositive⟩

/-! ## The intrinsic plateau and its exact global characterization -/

/-- A positive minimum terminal-semantic pair on the all-Continue Nash face. -/
def HasPositiveMinimumTerminalSemanticPlateau
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ pair : QuittingTerminalSemanticPair ι,
    pair ∈ quittingTerminalSemanticCarrier reward ∧
    (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    (∃ who, 0 < quittingTerminalSemanticDebt pair who) ∧
    IsεQuittingRootNash reward pair.1 0
      (quittingAllContinueRoot : ι → PMF Bool) ∧
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair = pair

/-- Positive minimum debt is exactly the all-Continue plateau package. -/
theorem hasPositiveMinimumTerminalSemanticDebt_iff_terminalSemanticPlateau
    [Nonempty ι] :
    HasPositiveMinimumTerminalSemanticDebt reward ↔
      HasPositiveMinimumTerminalSemanticPlateau reward := by
  constructor
  · rintro ⟨pair, hpair, hminimum, hpositive⟩
    have hnonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
    have hcoordinate : ∃ who, 0 < quittingTerminalSemanticDebt pair who := by
      by_contra hnone
      have hzero : ∀ who, quittingTerminalSemanticDebt pair who = 0 := by
        intro who
        exact le_antisymm
          (le_of_not_gt fun hwho => hnone ⟨who, hwho⟩) (hnonneg who)
      unfold quittingTerminalSemanticDebtSum at hpositive
      simp only [hzero, Finset.sum_const_zero] at hpositive
      exact (lt_irrefl 0) hpositive
    obtain ⟨hnash, hprefix, _hmargin⟩ :=
      minimumTerminalSemantic_is_allContinuePlateau
        (reward := reward) pair hpair hminimum hpositive
    exact ⟨pair, hpair, hminimum, hcoordinate, hnash, hprefix⟩
  · rintro ⟨pair, hpair, hminimum, ⟨who, hwho⟩, _hnash, _hprefix⟩
    have hnonneg : ∀ player, 0 ≤ quittingTerminalSemanticDebt pair player :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
    have hpositive : 0 < quittingTerminalSemanticDebtSum pair := by
      unfold quittingTerminalSemanticDebtSum
      exact Finset.sum_pos' (fun player _ => hnonneg player)
        ⟨who, Finset.mem_univ who, hwho⟩
    exact ⟨pair, hpair, hminimum, hpositive⟩

/-- A finite quitting game lacks a uniform-equilibrium payoff exactly when it
has a positive minimum all-Continue terminal-semantic plateau. -/
theorem not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticPlateau
    [Nonempty ι] :
    (¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      HasPositiveMinimumTerminalSemanticPlateau reward := by
  rw [not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt,
    hasPositiveMinimumTerminalSemanticDebt_iff_terminalSemanticPlateau]

/-- Every terminal exploitability witness supplies the canonical positive
minimum all-Continue semantic plateau. -/
theorem noUniformPayoff_implies_positiveMinimumSemanticPlateau
    [Nonempty ι]
    (witness : QuittingTerminalExploitabilityWitness reward) :
    HasPositiveMinimumTerminalSemanticPlateau reward :=
  not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticPlateau.mp
    witness.not_exists_uniformEquilibriumPayoff

end GameTheory
