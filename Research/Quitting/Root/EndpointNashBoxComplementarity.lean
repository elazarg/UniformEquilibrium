/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.ModTwoBoxComplementarityParity
import MathUE.PMFProduct.Bool
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Endpoint Nash as box complementarity

This module gives an exact semantic bridge between Boolean product-root Nash
and the generic unit-cube complementarity interface.  The bridge is explicit
data: this file proves its logical consequences but does not assert that a
parity implementation or a regularity certificate exists.
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.PMFProduct Math.ProbabilityMassFunction Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Boolean simplex point whose `true` coordinate is a unit-interval
coordinate. -/
private def quittingUnitCubeRootSimplex (point : UnitCube ι) :
    QuittingRootSimplex ι :=
  fun who => ⟨fun action => if action then point who else 1 - point who, by
    constructor
    · intro action
      cases action <;> simp only [Bool.false_eq_true, ↓reduceIte, eq_self]
      · exact sub_nonneg.mpr (point who).property.2
      · exact (point who).property.1
    · simp⟩

/-- Canonical Boolean product root represented by a unit-cube point. -/
private def quittingUnitCubeRoot (point : UnitCube ι) : ι → PMF Bool :=
  fun who => bernoulliBoolEquiv (point who)

omit [DecidableEq ι] in
@[simp] private theorem quittingUnitCubeRoot_true_toReal
    (point : UnitCube ι) (who : ι) :
    ((quittingUnitCubeRoot point who) true).toReal = (point who : ℝ) := by
  simp [quittingUnitCubeRoot]

omit [DecidableEq ι] in
@[simp] private theorem quittingUnitCubeRoot_false_toReal
    (point : UnitCube ι) (who : ι) :
    ((quittingUnitCubeRoot point who) false).toReal = 1 - (point who : ℝ) := by
  simp [quittingUnitCubeRoot]

/-- The canonical coordinate-preserving equivalence between unit-cube points
and Boolean product roots. -/
private def quittingUnitCubeRootEquiv : UnitCube ι ≃ (ι → PMF Bool) :=
  Equiv.piCongrRight fun _ => bernoulliBoolEquiv

omit [DecidableEq ι] in
private theorem quittingUnitCubeRoot_eq_rootOfSimplex
    (point : UnitCube ι) :
    quittingUnitCubeRoot point =
      quittingRootOfSimplex (quittingUnitCubeRootSimplex point) := by
  funext who
  apply toVector_injective
  funext action
  cases action
  · change ((quittingUnitCubeRoot point who) false).toReal =
      ((quittingRootOfSimplex (quittingUnitCubeRootSimplex point) who) false).toReal
    rw [quittingUnitCubeRoot_false_toReal,
      quittingRootOfSimplex_apply_toReal]
    rfl
  · change ((quittingUnitCubeRoot point who) true).toReal =
      ((quittingRootOfSimplex (quittingUnitCubeRootSimplex point) who) true).toReal
    rw [quittingUnitCubeRoot_true_toReal,
      quittingRootOfSimplex_apply_toReal]
    rfl

private theorem continuous_quittingUnitCubeRootEndpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) (who : ι) :
    Continuous (fun point : UnitCube ι =>
      quittingRootEndpointDifference reward cap (quittingUnitCubeRoot point) who) := by
  have hroot : Continuous (fun point : UnitCube ι =>
      quittingUnitCubeRootSimplex point) := by
    apply continuous_pi
    intro player
    apply Continuous.subtype_mk
    apply continuous_pi
    intro action
    have hcoordinate : Continuous (fun point : UnitCube ι =>
        (point player : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply player)
    cases action
    · exact continuous_const.sub hcoordinate
    · exact hcoordinate
  have hsimplex : Continuous (fun point : UnitCube ι =>
      (cap, quittingUnitCubeRootSimplex point)) :=
    continuous_const.prodMk hroot
  let endpoint : Payoff ι × QuittingRootSimplex ι → ℝ := fun point =>
    quittingRootEndpointDifference reward point.1
      (quittingRootOfSimplex point.2) who
  have hcontinuous : Continuous (fun point : UnitCube ι =>
      quittingRootEndpointDifference reward cap
        (quittingRootOfSimplex (quittingUnitCubeRootSimplex point)) who) := by
    change Continuous (endpoint ∘ fun point =>
      (cap, quittingUnitCubeRootSimplex point))
    exact (continuous_quittingRootEndpointDifference_simplex reward who).comp
      hsimplex
  simpa only [quittingUnitCubeRoot_eq_rootOfSimplex] using hcontinuous

/-- A coordinate-preserving equivalence between the real unit cube and
Boolean PMF roots, together with the quitting endpoint gain field. -/
structure QuittingEndpointNashBoxBridge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) where
  problem : BoxComplementarityProblem ι
  rootEquiv : UnitCube ι ≃ (ι → PMF Bool)
  quitProbability_eq : ∀ point who,
    ((rootEquiv point who) true).toReal = (point who : ℝ)
  continueProbability_eq : ∀ point who,
    ((rootEquiv point who) false).toReal = 1 - (point who : ℝ)
  gain_eq : ∀ point who,
    problem.gain point who =
      quittingRootEndpointDifference reward cap (rootEquiv point) who

/-- The canonical endpoint-Nash complementarity bridge exists for every
finite quitting reward table and every declared cap. -/
noncomputable def quittingEndpointNashBoxBridge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) : QuittingEndpointNashBoxBridge reward cap where
  problem := {
    gain := fun point who =>
      quittingRootEndpointDifference reward cap (quittingUnitCubeRoot point) who
    continuous_gain := continuous_quittingUnitCubeRootEndpointDifference reward cap }
  rootEquiv := quittingUnitCubeRootEquiv
  quitProbability_eq := quittingUnitCubeRoot_true_toReal
  continueProbability_eq := quittingUnitCubeRoot_false_toReal
  gain_eq := fun _ _ => rfl

namespace QuittingEndpointNashBoxBridge

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {cap : Payoff ι}

/-- Box complementarity is exactly unrestricted mixed root Nash at the same
fixed quitting cap vector. -/
theorem isSolution_iff_isZeroQuittingRootNash
    (bridge : QuittingEndpointNashBoxBridge reward cap)
    (point : UnitCube ι) :
    bridge.problem.IsSolution point ↔
      IsεQuittingRootNash reward cap 0 (bridge.rootEquiv point) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  constructor
  · intro hsolution who
    have hwho := hsolution who
    let probability : ℝ := point who
    have hprobability := (point who).property
    by_cases hzero : probability = 0
    · have hgain : bridge.problem.gain point who ≤ 0 := hwho.1 hzero
      rw [bridge.continueProbability_eq, bridge.quitProbability_eq,
        ← bridge.gain_eq]
      dsimp only [probability] at hzero hprobability
      constructor <;> nlinarith
    · by_cases hone : probability = 1
      · have hgain : 0 ≤ bridge.problem.gain point who := hwho.2.1 hone
        rw [bridge.continueProbability_eq, bridge.quitProbability_eq,
          ← bridge.gain_eq]
        dsimp only [probability] at hone hprobability
        constructor <;> nlinarith
      · have hpositive : 0 < probability :=
          lt_of_le_of_ne hprobability.1 (Ne.symm hzero)
        have hlt : probability < 1 := lt_of_le_of_ne hprobability.2 hone
        have hgain : bridge.problem.gain point who = 0 :=
          hwho.2.2 hpositive hlt
        rw [bridge.continueProbability_eq, bridge.quitProbability_eq,
          ← bridge.gain_eq, hgain]
        constructor <;> norm_num
  · intro hnash who
    have hendpoint := hnash who
    let probability : ℝ := point who
    have hprobability := (point who).property
    rw [bridge.continueProbability_eq, bridge.quitProbability_eq,
      ← bridge.gain_eq] at hendpoint
    constructor
    · intro hzero
      nlinarith [hendpoint.1]
    constructor
    · intro hone
      nlinarith [hendpoint.2]
    · intro hpositive hlt
      apply le_antisymm
      · nlinarith [hendpoint.1]
      · nlinarith [hendpoint.2]

/-- Set-membership form of the endpoint-Nash equivalence. -/
theorem mem_solutionSet_iff_isZeroQuittingRootNash
    (bridge : QuittingEndpointNashBoxBridge reward cap)
    (point : UnitCube ι) :
    point ∈ bridge.problem.solutionSet ↔
      IsεQuittingRootNash reward cap 0 (bridge.rootEquiv point) :=
  bridge.isSolution_iff_isZeroQuittingRootNash point

/-- Regularity transported back from the parity API to Boolean product roots.
This is a definition, not a claim that any displayed root is regular. -/
def IsParityRegularRoot
    (bridge : QuittingEndpointNashBoxBridge reward cap)
    (spec : ModTwoBoxComplementarityParitySpec ι)
    (root : ι → PMF Bool) : Prop :=
  spec.IsRegular bridge.problem (bridge.rootEquiv.symm root)

/-- Literal regularity bridge at a cube point. -/
theorem isParityRegularRoot_rootEquiv_iff
    (bridge : QuittingEndpointNashBoxBridge reward cap)
    (spec : ModTwoBoxComplementarityParitySpec ι)
    (point : UnitCube ι) :
    bridge.IsParityRegularRoot spec (bridge.rootEquiv point) ↔
      spec.IsRegular bridge.problem point := by
  simp [IsParityRegularRoot]

/-- A parity-regular Boolean root is an exact root Nash at the same cap. -/
theorem IsParityRegularRoot.isZeroQuittingRootNash
    (bridge : QuittingEndpointNashBoxBridge reward cap)
    (spec : ModTwoBoxComplementarityParitySpec ι)
    {root : ι → PMF Bool}
    (hregular : bridge.IsParityRegularRoot spec root) :
    IsεQuittingRootNash reward cap 0 root := by
  have hsolution := spec.regular_isSolution bridge.problem
    (bridge.rootEquiv.symm root) hregular
  have hnash := (bridge.isSolution_iff_isZeroQuittingRootNash
    (bridge.rootEquiv.symm root)).1 hsolution
  simpa using hnash

end QuittingEndpointNashBoxBridge

end GameTheory
