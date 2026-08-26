/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Robust positivity on a compact fiber

A jointly continuous real defect that is strictly positive on a closed subset
of a compact fiber has one positive lower bound throughout that subset. The
same bound, weakened by a factor of two, persists for every nearby parameter.

The closed subset may be empty. In that case the conclusion is vacuous and a
unit moat is returned.
-/

noncomputable section

namespace Math
namespace Topology

open Filter Set
open scoped Topology

/-- Strict positivity of a jointly continuous defect on a closed subset of a
compact fiber persists as one uniform positive moat on a neighborhood of the
parameter. No metric, explicit neighborhood radius, or quantitative modulus
is required. -/
theorem exists_eventually_uniform_pos_on_closed_of_compactSpace
    {Parameter Point : Type*}
    [TopologicalSpace Parameter] [TopologicalSpace Point] [CompactSpace Point]
    (defect : Parameter → Point → ℝ)
    (hdefect : Continuous fun pair : Parameter × Point =>
      defect pair.1 pair.2)
    (high : Set Point) (hhigh : IsClosed high)
    (parameter : Parameter)
    (hpositive : ∀ point ∈ high, 0 < defect parameter point) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearby in nhds parameter,
        ∀ point ∈ high, moat ≤ defect nearby point := by
  by_cases hhighNonempty : high.Nonempty
  · have hhighCompact : IsCompact high := hhigh.isCompact
    have hfixedContinuous : Continuous (defect parameter) := by
      exact hdefect.comp (continuous_const.prodMk continuous_id)
    obtain ⟨selected, hselectedHigh, hselectedMin⟩ :=
      hhighCompact.exists_isMinOn hhighNonempty
        hfixedContinuous.continuousOn
    have hselectedPositive : 0 < defect parameter selected :=
      hpositive selected hselectedHigh
    let moat := defect parameter selected / 2
    let bad : Set (Parameter × Point) :=
      {pair | pair.2 ∈ high ∧ defect pair.1 pair.2 ≤ moat}
    have hbadClosed : IsClosed bad := by
      exact (hhigh.preimage continuous_snd).inter
        (isClosed_le hdefect continuous_const)
    have hprojectionClosed : IsClosed (Prod.fst '' bad) :=
      isClosedMap_fst_of_compactSpace bad hbadClosed
    have hparameterNotBad : parameter ∉ Prod.fst '' bad := by
      rintro ⟨⟨nearby, point⟩, hpointBad, hnearby⟩
      change nearby = parameter at hnearby
      subst nearby
      have hlower := hselectedMin hpointBad.1
      have hupper : defect parameter point ≤
          defect parameter selected / 2 := by
        simpa only [moat] using hpointBad.2
      exact (not_le_of_gt (half_lt_self hselectedPositive))
        (hlower.trans hupper)
    refine ⟨moat, half_pos hselectedPositive, ?_⟩
    refine Filter.mem_of_superset
      (hprojectionClosed.isOpen_compl.mem_nhds hparameterNotBad) ?_
    intro nearby hnear point hpointHigh
    apply le_of_not_gt
    intro hsmall
    exact hnear ⟨(nearby, point), ⟨hpointHigh, hsmall.le⟩, rfl⟩
  · refine ⟨1, zero_lt_one, Filter.Eventually.of_forall ?_⟩
    intro nearby point hpointHigh
    exact False.elim (hhighNonempty ⟨point, hpointHigh⟩)

end Topology
end Math
