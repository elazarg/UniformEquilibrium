/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.BoxComplementaritySpernerLocalCount

/-!
# Eventual local parity after solution localization

An open set containing the complete box-complementarity solution set has the
same finite-mesh complete-simplex count as the whole cube at every sufficiently
fine resolution.  Hence that local count is eventually one modulo two.

This is the finite-mesh localization needed by the strict Fin4 binding-pair
argument.  It does not construct cross-resolution subdivision invariance,
homotopy invariance, a regularity theory, or a
`ModTwoBoxComplementarityParitySpec` inhabitant.  To obtain a contradiction it
is enough to compute zero local parity eventually for the explicit finite-cap
binding-pair component at the same resolutions.
-/

noncomputable section

namespace Math

open Set

variable {n : ℕ}

/-- If every solution lies in an open region, every sufficiently fine complete
simplex has its selected anchor in that region.  Consequently its local count
is the global odd count. -/
theorem BoxComplementarityProblem.eventually_localCompleteSimplexParity_eq_one
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hopen : IsOpen region)
    (hsolutions : problem.solutionSet ⊆ region) :
    ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
      boxComplementarityLocalCompleteSimplexParity problem p hp region = 1 := by
  have hcompact : IsCompact (regionᶜ) := by
    simpa only [Set.univ_inter] using
      isCompact_univ.inter_right hopen.isClosed_compl
  have hdisjoint : Disjoint (regionᶜ) problem.solutionSet := by
    rw [Set.disjoint_left]
    intro point houtside hsolution
    exact houtside (hsolutions hsolution)
  obtain ⟨threshold, hcleared⟩ :=
    problem.eventually_no_completeSimplexVertexIn_of_compact
      regionᶜ hcompact hdisjoint
  refine ⟨threshold, ?_⟩
  intro p hpFine hp
  have hcoherent :=
    boxComplementarityLocalCompleteSimplexParity_eq_of_difference_subset_cleared
      problem p hp region Set.univ regionᶜ (by
        intro point hpoint
        rcases hpoint with ⟨-, hnotUniv⟩ | ⟨-, houtside⟩
        · exact False.elim (hnotUniv (Set.mem_univ point))
        · exact houtside)
      (hcleared p hpFine)
  rw [hcoherent]
  exact boxComplementarityLocalCompleteSimplexParity_univ problem p hp

/-- An eventual zero calculation for a region containing every solution
contradicts global cubical-Sperner oddness.  This is a one-problem,
same-resolution consumer; no comparison between two mesh sizes is used. -/
theorem BoxComplementarityProblem.not_eventually_localCompleteSimplexParity_eq_zero
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hopen : IsOpen region)
    (hsolutions : problem.solutionSet ⊆ region)
    (hzero : ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
      boxComplementarityLocalCompleteSimplexParity problem p hp region = 0) :
    False := by
  obtain ⟨oneThreshold, hone⟩ :=
    problem.eventually_localCompleteSimplexParity_eq_one
      region hopen hsolutions
  obtain ⟨zeroThreshold, hzero⟩ := hzero
  let p := max (max oneThreshold zeroThreshold) 1
  have hp : 0 < p := by
    dsimp only [p]
    omega
  have hpOne : oneThreshold ≤ p := by
    dsimp only [p]
    omega
  have hpZero : zeroThreshold ≤ p := by
    dsimp only [p]
    omega
  have hzeroOne : (0 : ZMod 2) = 1 :=
    (hzero p hpZero hp).symm.trans (hone p hpOne hp)
  exact zero_ne_one hzeroOne

end Math
