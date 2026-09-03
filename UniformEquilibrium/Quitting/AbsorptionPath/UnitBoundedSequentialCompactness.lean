/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.CommonLimitJumpSubsequence
import UniformEquilibrium.Quitting.AbsorptionPath.LimitJumpRootLocalization
import UniformEquilibrium.Quitting.AbsorptionPath.SingletonDerivativeWeakLimit

/-!
# Sequential compactness of unit-bounded absorption paths

Rational-coordinate product compactness reconstructs a càdlàg limit.  The
closed absorption-path conditions bundle that candidate as an absorption
path, and one further diagonal subsequence retains literal source
realizations of every limit jump.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The càdlàg path reconstructed from a simultaneous rational-coordinate
limit satisfies all four defining absorption-path conditions.  The jump-root
and singleton-derivative conclusions are stated literally in the proof. -/
theorem isAbsorptionPath_cadlagPathOfAbsorptionRationalSample
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (subsequence : ℕ → ℕ)
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (hsourceBounded : ∀ rank,
      HasUnitBoundedTotalMass (sequence (subsequence rank)))
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    IsAbsorptionPath (cadlagPathOfAbsorptionRationalSample sample) := by
  let limit := cadlagPathOfAbsorptionRationalSample sample
  have hclock : ∀ time ∈ Icc (0 : ℝ) 1,
      time ≤ pathTotal limit time :=
    clock_le_pathTotal_cadlagPathOfAbsorptionRationalSample hsample
  have hbound : ∀ time ∈ Icc (0 : ℝ) 1,
      pathTotal limit time ≤ 1 :=
    pathTotal_cadlagPathOfAbsorptionRationalSample_le_one hsample
  have hgap : MathUE.HasClockGapOn (pathTotal limit) (Icc 0 1) :=
    hasClockGapOn_pathTotal_cadlagPathOfAbsorptionRationalSample
      hsample hconverges
  have hweak : WeaklyConvergesAbsorptionPathsToCadlag
      (sequence ∘ subsequence) limit :=
    weaklyConvergesToCadlag_of_rationalSample_tendsto hsample hconverges
  refine ⟨hclock,
    hasConstantTotalOnGapComponents_cadlagPathOfAbsorptionRationalSample
      hsample hconverges, ?_, ?_⟩
  · exact everyJump_hasNormalizedRoot_of_unitBoundedWeakLimit
      hclock hbound hgap hsourceBounded hweak
  · exact rightDerivative_supports_singletons_of_unitBoundedWeakLimit
      hclock hbound hgap hsourceBounded hweak

/-- Bundle the rational-envelope candidate with its checked absorption-path
conditions. -/
noncomputable def absorptionPathOfAbsorptionRationalSample
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (subsequence : ℕ → ℕ)
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (hsourceBounded : ∀ rank,
      HasUnitBoundedTotalMass (sequence (subsequence rank)))
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) : AbsorptionPath (ι := ι) :=
  ⟨cadlagPathOfAbsorptionRationalSample sample,
    isAbsorptionPath_cadlagPathOfAbsorptionRationalSample sequence
      subsequence sample hsourceBounded hsample hconverges⟩

/-- The bundled rational-envelope limit retains unit-bounded total mass. -/
theorem hasUnitBoundedTotalMass_absorptionPathOfAbsorptionRationalSample
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (subsequence : ℕ → ℕ)
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (hsourceBounded : ∀ rank,
      HasUnitBoundedTotalMass (sequence (subsequence rank)))
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    HasUnitBoundedTotalMass
      (absorptionPathOfAbsorptionRationalSample sequence subsequence sample
        hsourceBounded hsample hconverges) := by
  intro time htime
  exact pathTotal_cadlagPathOfAbsorptionRationalSample_le_one
    hsample time htime

/-- The selected source subsequence weakly converges at every continuity
point to the bundled rational-envelope absorption path. -/
theorem weaklyConvergesAbsorptionPaths_absorptionPathOfRationalSample
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (subsequence : ℕ → ℕ)
    (sample : {coalition : Finset ι // coalition.Nonempty} →
      ℚ → Icc (0 : ℝ) 1)
    (hsourceBounded : ∀ rank,
      HasUnitBoundedTotalMass (sequence (subsequence rank)))
    (hsample : IsUnitBoundedAbsorptionRationalSample sample)
    (hconverges :
      Tendsto (absorptionPathRationalSample ∘ sequence ∘ subsequence)
        atTop (nhds sample)) :
    WeaklyConvergesAbsorptionPaths (sequence ∘ subsequence)
      (absorptionPathOfAbsorptionRationalSample sequence subsequence sample
        hsourceBounded hsample hconverges) := by
  exact weaklyConvergesToCadlag_of_rationalSample_tendsto hsample hconverges

/-- Every sequence of unit-bounded absorption paths has a weakly convergent
strict subsequence whose bundled limit is again unit bounded. -/
theorem unitBoundedAbsorptionPathWeakSequentialCompactness :
    UnitBoundedAbsorptionPathWeakSequentialCompactness (ι := ι) := by
  intro sequence hsourceBounded
  obtain ⟨sample, subsequence, hsubsequenceStrict, hconverges⟩ :=
    exists_rationalSample_tendsto_subsequence sequence
  have hsubsequenceBounded : ∀ rank,
      HasUnitBoundedTotalMass (sequence (subsequence rank)) :=
    fun rank ↦ hsourceBounded (subsequence rank)
  have hsample : IsUnitBoundedAbsorptionRationalSample sample :=
    isUnitBoundedAbsorptionRationalSample_of_tendsto
      hsubsequenceBounded hconverges
  let limit := absorptionPathOfAbsorptionRationalSample sequence subsequence
    sample hsubsequenceBounded hsample hconverges
  refine ⟨limit, subsequence, hsubsequenceStrict, ?_, ?_⟩
  · exact hasUnitBoundedTotalMass_absorptionPathOfAbsorptionRationalSample
      sequence subsequence sample hsubsequenceBounded hsample hconverges
  · exact weaklyConvergesAbsorptionPaths_absorptionPathOfRationalSample
      sequence subsequence sample hsubsequenceBounded hsample hconverges

/-- Unit-bounded absorption paths are sequentially compact in the weak path
topology.  One common strict subsequence converges at every continuity point,
its limit is a unit-bounded absorption path, and every limit jump has a
convergent literal source-jump realization along that same subsequence. -/
theorem exists_unitBoundedAbsorptionPath_limit_subsequence
    (sequence : ℕ → AbsorptionPath (ι := ι))
    (hsourceBounded : ∀ index,
      HasUnitBoundedTotalMass (sequence index)) :
    ∃ (limit : AbsorptionPath (ι := ι)) (subsequence : ℕ → ℕ),
      StrictMono subsequence ∧
        HasUnitBoundedTotalMass limit ∧
        WeaklyConvergesAbsorptionPaths (sequence ∘ subsequence) limit ∧
        HasSourceApproximationsForLimitJumps
          (sequence ∘ subsequence) limit := by
  exact unitBoundedAbsorptionPathSequentialCompactness_of_weakSequentialCompactness
    unitBoundedAbsorptionPathWeakSequentialCompactness sequence hsourceBounded

/-- The literal compactness theorem discharges the shared corrected
unit-bounded sequential-compactness interface. -/
theorem unitBoundedAbsorptionPathSequentialCompactness :
    UnitBoundedAbsorptionPathSequentialCompactness (ι := ι) := by
  intro sequence hsourceBounded
  exact exists_unitBoundedAbsorptionPath_limit_subsequence
    sequence hsourceBounded

end GameTheory.QuittingAbsorptionPath
