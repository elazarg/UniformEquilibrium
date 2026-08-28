/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.ModTwoBoxComplementarityParity
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Endpoint Nash as box complementarity

This module gives an exact semantic bridge between Boolean product-root Nash
and the generic unit-cube complementarity interface.  The bridge is explicit
data: this file proves its logical consequences but does not assert that a
parity implementation or a regularity certificate exists.
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

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
