/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.StrictRayTailNormalizedCapFlow
import Research.Quitting.Root.EndpointNashBoxComplementarity

/-!
# Conditional mod-two binding-cardinality reduction for a strict Fin4 ray

This module is an executable specification of the missing component-parity
step.  It does not construct a parity theory or the local binding-pair
certificate.  Every theorem takes both pieces of data explicitly.

The source-honest conclusion does not assume that all Continue is the unique
exact root at the limiting cap.  It returns a positive-absorption exact root
at that same cap when uniqueness fails; only the uniqueness arm contracts a
proper binding face to cardinality three.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability Set

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The additional hypothesis not supplied by the current strict-ray source:
all Continue is the unique exact root at the limiting cap. -/
def HasUniqueAllContinueAtCapLimit
    (flow : FinFourStrictRayForwardExactCapTail packet) : Prop :=
  ∀ candidate : Fin 4 → PMF Bool,
    IsεQuittingRootNash reward flow.forward.capLimit 0 candidate →
      candidate = (quittingAllContinueRoot : Fin 4 → PMF Bool)

/-- Finite, regular, even local data for one box-complementarity problem. -/
structure FinFourBindingPairFiniteRegularEvenData
    (parity : ModTwoBoxComplementarityParitySpec (Fin 4))
    (problem : BoxComplementarityProblem (Fin 4))
    (neighborhood : Set (UnitCube (Fin 4))) where
  solutions_finite : (problem.solutionsIn neighborhood).Finite
  solutions_regular : ∀ point ∈ problem.solutionsIn neighborhood,
    parity.IsRegular problem point
  solutions_even : Even (problem.solutionsIn neighborhood).ncard

/-- Two honest ways to compute zero local parity at a finite ray cap.

The direct constructor applies when the original local solution set is
already finite, regular, and even.  The perturbed constructor instead carries
a common-isolating homotopy to a finite regular even endpoint; it is the route
needed when the unperturbed local component is nonfinite or nonregular. -/
inductive FinFourBindingPairLocalParityZero
    (parity : ModTwoBoxComplementarityParitySpec (Fin 4))
    (problem : BoxComplementarityProblem (Fin 4))
    (neighborhood : Set (UnitCube (Fin 4))) : Type
  | direct
      (data : FinFourBindingPairFiniteRegularEvenData parity problem neighborhood)
  | perturbed
      (family : Set.Icc (0 : ℝ) 1 → BoxComplementarityProblem (Fin 4))
      (source_eq : family unitIntervalZero = problem)
      (continuous : IsContinuousBoxComplementarityFamily (Fin 4) family)
      (common_isolating : ∀ parameter,
        (family parameter).IsIsolating neighborhood)
      (target : FinFourBindingPairFiniteRegularEvenData parity
        (family unitIntervalOne) neighborhood)

namespace FinFourBindingPairLocalParityZero

/-- Either local computation route gives literal zero parity for the original
finite-cap problem. -/
theorem localParity_eq_zero
    {parity : ModTwoBoxComplementarityParitySpec (Fin 4)}
    {problem : BoxComplementarityProblem (Fin 4)}
    {neighborhood : Set (UnitCube (Fin 4))}
    (computation : FinFourBindingPairLocalParityZero parity problem neighborhood)
    (hisolating : problem.IsIsolating neighborhood) :
    parity.localParity problem neighborhood = 0 := by
  cases computation with
  | direct data =>
      exact parity.localParity_eq_zero_of_finite_regular_even
        problem neighborhood hisolating data.solutions_finite
        data.solutions_regular data.solutions_even
  | perturbed family source_eq continuous common_isolating target =>
      have hhomotopy := parity.localParity_eq_of_common_isolating_homotopy
        family neighborhood continuous common_isolating
      have htarget := parity.localParity_eq_zero_of_finite_regular_even
        (family unitIntervalOne) neighborhood
        (common_isolating unitIntervalOne) target.solutions_finite
        target.solutions_regular target.solutions_even
      rw [source_eq] at hhomotopy
      exact hhomotopy.trans htarget

end FinFourBindingPairLocalParityZero

/-- The finite-cap parity witness used when the limiting binding face has two
coordinates.  The bridge is at an actual sufficiently late ray cap, not at
the limiting cap.  `late_currentHazard_supported_binding` records the exact
eventual property used to choose that time, and `contains_every_solution`
retains the required finite-cap solution localization. -/
structure FinFourBindingPairFiniteCapParityWitness
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (parity : ModTwoBoxComplementarityParitySpec (Fin 4)) where
  time : ℕ
  bridge : QuittingEndpointNashBoxBridge reward (flow.forward.pair time).2
  late_currentHazard_supported_binding : ∀ who,
    0 < flow.forward.currentHazard time who →
      who ∈ flow.forward.bindingFinset
  neighborhood : Set (UnitCube (Fin 4))
  isolating : bridge.problem.IsIsolating neighborhood
  localZero : FinFourBindingPairLocalParityZero parity bridge.problem neighborhood
  contains_every_solution : ∀ point,
    bridge.problem.IsSolution point → point ∈ neighborhood

namespace FinFourBindingPairFiniteCapParityWitness

/-- Literal zero local parity at the selected finite cap. -/
theorem localParity_eq_zero
    {flow : FinFourStrictRayForwardExactCapTail packet}
    {parity : ModTwoBoxComplementarityParitySpec (Fin 4)}
    (witness : FinFourBindingPairFiniteCapParityWitness flow parity) :
    parity.localParity witness.bridge.problem witness.neighborhood = 0 :=
  witness.localZero.localParity_eq_zero witness.isolating

end FinFourBindingPairFiniteCapParityWitness

/-- Open local certificate for excluding a two-coordinate binding face.

No field asserts that this certificate exists.  In the binding-pair case it
must select one late finite cap and supply either a direct local parity count
or a common-isolating perturbation count there. -/
structure FinFourBindingPairParityCertificate
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (parity : ModTwoBoxComplementarityParitySpec (Fin 4)) where
  binding_card_ne_one :
    HasUniqueAllContinueAtCapLimit flow →
      flow.forward.bindingFinset.card ≠ 1
  pairCase : HasUniqueAllContinueAtCapLimit flow →
    flow.forward.bindingFinset.card = 2 →
      FinFourBindingPairFiniteCapParityWitness flow parity

namespace FinFourBindingPairParityCertificate

variable {flow : FinFourStrictRayForwardExactCapTail packet}
variable {parity : ModTwoBoxComplementarityParitySpec (Fin 4)}

/-- The binding set of an actual positive-hazard forward tail is nonempty. -/
theorem bindingFinset_nonempty
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    flow.forward.bindingFinset.Nonempty := by
  obtain ⟨time, hsupported⟩ :=
    flow.forward.eventually_currentHazard_supported_binding.exists
  by_contra hempty
  have hbinding : flow.forward.bindingFinset = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hzero : ∀ who, flow.forward.currentHazard time who = 0 := by
    intro who
    apply le_antisymm
    · apply le_of_not_gt
      intro hpositive
      have hmem := hsupported who hpositive
      rw [hbinding] at hmem
      simp at hmem
    · exact flow.forward.currentHazard_nonneg time who
  have hsum := flow.forward.sum_currentHazard time
  simp only [hzero, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- The supplied local parity calculation excludes a binding pair under the
explicit limiting-root uniqueness hypothesis. -/
theorem bindingFinset_card_ne_two_of_unique_allContinue
    (certificate : FinFourBindingPairParityCertificate flow parity)
    (hunique : HasUniqueAllContinueAtCapLimit flow) :
    flow.forward.bindingFinset.card ≠ 2 := by
  intro hcard
  let finiteCap := certificate.pairCase hunique hcard
  have hlocalZero : parity.localParity finiteCap.bridge.problem
      finiteCap.neighborhood = 0 := finiteCap.localParity_eq_zero
  obtain ⟨point, hsolution, houtside⟩ :=
    parity.exists_solution_not_mem_of_localParity_ne_one
      finiteCap.bridge.problem finiteCap.neighborhood finiteCap.isolating (by
        rw [hlocalZero]
        exact zero_ne_one)
  exact houtside (finiteCap.contains_every_solution point hsolution)

/-- With unique all Continue at the limiting cap, a strict Fin4 forward tail
has either full binding support or a binding face of cardinality three. -/
theorem bindingFinset_eq_univ_or_card_eq_three_of_unique_allContinue
    (certificate : FinFourBindingPairParityCertificate flow parity)
    (hunique : HasUniqueAllContinueAtCapLimit flow) :
    flow.forward.bindingFinset = Finset.univ ∨
      flow.forward.bindingFinset.card = 3 := by
  by_cases huniv : flow.forward.bindingFinset = Finset.univ
  · exact Or.inl huniv
  right
  have hstrict : flow.forward.bindingFinset ⊂ (Finset.univ : Finset (Fin 4)) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, huniv⟩
  have hcardLt : flow.forward.bindingFinset.card < 4 := by
    simpa using Finset.card_lt_card hstrict
  have hcardPos : 0 < flow.forward.bindingFinset.card :=
    Finset.card_pos.mpr (bindingFinset_nonempty flow)
  have hcardNeOne := certificate.binding_card_ne_one hunique
  have hcardNeTwo :=
    certificate.bindingFinset_card_ne_two_of_unique_allContinue hunique
  omega

private theorem root_eq_allContinue_of_absorption_eq_zero
    (root : Fin 4 → PMF Bool)
    (hzero : quittingRootAbsorptionMass root = 0) :
    root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at hzero
    linarith
  funext who
  simpa [quittingAllContinueRoot] using
    eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

/-- Source-honest cardinality projection.  Failure of limiting-root
uniqueness returns an actual positive-absorption exact root at the same
limiting cap; otherwise the same forward tail has full or cardinal-three
binding support. -/
theorem positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three
    (certificate : FinFourBindingPairParityCertificate flow parity) :
    (∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward flow.forward.capLimit 0 root ∧
        0 < quittingRootAbsorptionMass root) ∨
      flow.forward.bindingFinset = Finset.univ ∨
        flow.forward.bindingFinset.card = 3 := by
  by_cases hunique : HasUniqueAllContinueAtCapLimit flow
  · exact Or.inr
      (certificate.bindingFinset_eq_univ_or_card_eq_three_of_unique_allContinue
        hunique)
  · left
    rw [HasUniqueAllContinueAtCapLimit] at hunique
    push Not at hunique
    obtain ⟨root, hnash, hne⟩ := hunique
    refine ⟨root, hnash, ?_⟩
    have habsorptionNe : quittingRootAbsorptionMass root ≠ 0 := by
      intro hzero
      exact hne (root_eq_allContinue_of_absorption_eq_zero root hzero)
    exact lt_of_le_of_ne (quittingRootAbsorptionMass_nonneg _)
      (Ne.symm habsorptionNe)

end FinFourBindingPairParityCertificate

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
