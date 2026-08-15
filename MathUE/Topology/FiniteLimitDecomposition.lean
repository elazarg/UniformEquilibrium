/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Finite endpoint limit decompositions

These helpers isolate the finite-sum and finite-product limit arguments used
by analytic endpoint constructions from any game-semantic definitions.
-/

noncomputable section

namespace Math

open Filter Set Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- An endpoint value with an eventual finite decomposition is the limit of
its finite terms plus the residual term. -/
theorem endpoint_eq_finsetSum_mul_add_of_tendsto
    (value residual : ℝ → ℝ) (weight : ι → ℝ → ℝ)
    (limitWeight term : ι → ℝ)
    (hweight : ∀ owner, Tendsto (weight owner)
      (𝓝[>] (0 : ℝ)) (𝓝 (limitWeight owner)))
    (hresidual : Tendsto residual (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hexact : (fun t => value t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => (∑ owner, weight owner t * term owner) + residual t))
    (hvalue : Tendsto value (𝓝[>] (0 : ℝ)) (𝓝 (value 0))) :
    value 0 = ∑ owner, limitWeight owner * term owner := by
  have hsum : Tendsto
      (fun t => ∑ owner, weight owner t * term owner)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ owner, limitWeight owner * term owner)) := by
    apply tendsto_finsetSum Finset.univ
    intro owner _
    exact (hweight owner).mul tendsto_const_nhds
  have hright := hsum.add hresidual
  have hfromRight := hright.congr' hexact.symm
  simpa using tendsto_nhds_unique hvalue hfromRight

/-- If every coordinate vanishes at the endpoint, the excluded product of
their complements converges to one. -/
theorem excludedProduct_tendsto_one_of_tendsto_zero
    (coordinate : ι → ℝ → ℝ)
    (hzero : ∀ other, Tendsto (coordinate other)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (owner : ι) :
    Tendsto
      (fun t : ℝ => ∏ other ∈ Finset.univ.erase owner,
        (1 - coordinate other t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hprod : Tendsto
      (fun t : ℝ => ∏ other ∈ Finset.univ.erase owner,
        (1 - coordinate other t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∏ _other ∈ Finset.univ.erase owner, (1 : ℝ))) :=
    tendsto_finsetProd (Finset.univ.erase owner)
      (fun other _ => by
        simpa using hone.sub (hzero other))
  simpa using hprod

/-- Along any filter, a real-valued function eventually dominated in absolute
value by a vanishing bound also tends to zero. -/
theorem tendsto_zero_of_abs_le_of_tendsto_zero
    {index : Type*} {filter : Filter index}
    (f bound : index → ℝ)
    (hbound : Tendsto bound filter (𝓝 0))
    (hle : ∀ᶠ t in filter, |f t| ≤ bound t) :
    Tendsto f filter (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun t => abs_nonneg (f t)) hle hbound

end Math
