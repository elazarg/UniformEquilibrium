/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Defs.Filter

/-!
# Compact gap alternatives for finite semantic faces

These lemmas isolate the compactness step used by both strict-toggle semantic
residuals.  They retain the compact carrier and continuity hypotheses rather
than presenting positivity of a minimum as an automatic finite-dimensional
fact.
-/

namespace GameTheory

open Filter

variable {X : Type} [TopologicalSpace X]

/-- A continuous screen on a nonempty compact carrier either accepts a point
at level zero or has a strictly positive attained uniform gap. -/
theorem exists_nonpos_or_pos_compactGap
    (carrier : Set X) (hcompact : IsCompact carrier) (hnonempty : carrier.Nonempty)
    (screen : X → ℝ) (hcontinuous : ContinuousOn screen carrier) :
    (∃ point ∈ carrier, screen point ≤ 0) ∨
      ∃ gamma : ℝ, 0 < gamma ∧ ∀ point ∈ carrier, gamma ≤ screen point := by
  obtain ⟨minimizer, hminimizer, hminimal⟩ :=
    hcompact.exists_isMinOn hnonempty hcontinuous
  by_cases haccept : screen minimizer ≤ 0
  · exact Or.inl ⟨minimizer, hminimizer, haccept⟩
  · exact Or.inr ⟨screen minimizer, lt_of_not_ge haccept,
      fun point hpoint => hminimal hpoint⟩

/-- If zero is excluded pointwise, a continuous nonnegative defect has a
strictly positive lower bound on a nonempty compact carrier. -/
theorem exists_pos_compactGap_of_pos
    (carrier : Set X) (hcompact : IsCompact carrier) (hnonempty : carrier.Nonempty)
    (defect : X → ℝ) (hcontinuous : ContinuousOn defect carrier)
    (hpositive : ∀ point ∈ carrier, 0 < defect point) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ point ∈ carrier, gamma ≤ defect point := by
  obtain ⟨minimizer, hminimizer, hminimal⟩ :=
    hcompact.exists_isMinOn hnonempty hcontinuous
  exact ⟨defect minimizer, hpositive minimizer hminimizer,
    fun point hpoint => hminimal hpoint⟩

omit [TopologicalSpace X] in
/-- A sequence whose nonnegative defect tends to zero cannot eventually stay
in a carrier on which the defect has a fixed positive gap. -/
theorem eventually_not_mem_of_tendsto_zero_of_pos_gap
    {index : Type} {filter : Filter index}
    (carrier : Set X) (defect : X → ℝ) (points : index → X)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ point ∈ carrier, gamma ≤ defect point)
    (htendsto : Tendsto (fun n => defect (points n)) filter (nhds 0)) :
    ∀ᶠ n in filter, points n ∉ carrier := by
  have hsmall : ∀ᶠ n in filter, defect (points n) < gamma :=
    (tendsto_order.1 htendsto).2 gamma hgamma
  filter_upwards [hsmall] with n hn
  intro hmem
  exact (not_lt_of_ge (hgap (points n) hmem)) hn

end GameTheory
