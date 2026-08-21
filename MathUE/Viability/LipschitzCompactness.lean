/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Compactness of uniformly Lipschitz trajectories

Arzelà--Ascoli makes the family of trajectories with one Lipschitz constant
and a common compact range compact in the uniform topology.  This is the
compact-limit layer used for polygonal viability approximations.
-/

namespace Math
namespace Viability

open Filter Set

variable {Domain State : Type*}
  [PseudoMetricSpace Domain] [CompactSpace Domain]
  [PseudoMetricSpace State] [T2Space State]

/-- Bounded continuous paths with Lipschitz constant `constant` and image in
`rangeSet`. -/
def compactRangeLipschitzFamily (constant : NNReal) (rangeSet : Set State) :
    Set (BoundedContinuousFunction Domain State) :=
  {path | LipschitzWith constant path ∧ ∀ time, path time ∈ rangeSet}

omit [CompactSpace Domain] [T2Space State] in
/-- The common-range uniformly Lipschitz family is closed. -/
theorem isClosed_compactRangeLipschitzFamily
    (constant : NNReal) {rangeSet : Set State} (hrange : IsClosed rangeSet) :
    IsClosed (compactRangeLipschitzFamily
      (Domain := Domain) constant rangeSet) := by
  have hlipschitz (first second : Domain) : IsClosed
      {path : BoundedContinuousFunction Domain State |
        dist (path first) (path second) ≤
          constant * dist first second} := by
    exact isClosed_le
      ((BoundedContinuousFunction.lipschitz_eval_const first).continuous.dist
        (BoundedContinuousFunction.lipschitz_eval_const second).continuous)
      continuous_const
  have himage (time : Domain) : IsClosed
      {path : BoundedContinuousFunction Domain State | path time ∈ rangeSet} :=
    hrange.preimage
      (BoundedContinuousFunction.lipschitz_eval_const time).continuous
  rw [show compactRangeLipschitzFamily
      (Domain := Domain) constant rangeSet =
        (⋂ first, ⋂ second, {path |
          dist (path first) (path second) ≤
            constant * dist first second}) ∩
          ⋂ time, {path | path time ∈ rangeSet} by
    ext path
    simp only [compactRangeLipschitzFamily, mem_setOf_eq, mem_inter_iff,
      mem_iInter, lipschitzWith_iff_dist_le_mul]
    ]
  exact (isClosed_iInter fun first => isClosed_iInter (hlipschitz first)).inter
    (isClosed_iInter himage)

/-- **Lipschitz Arzelà--Ascoli.**  A common compact range and one Lipschitz
constant make the full trajectory family compact in uniform distance. -/
theorem isCompact_compactRangeLipschitzFamily
    (constant : NNReal) {rangeSet : Set State} (hrange : IsCompact rangeSet) :
    IsCompact (compactRangeLipschitzFamily
      (Domain := Domain) constant rangeSet) := by
  apply BoundedContinuousFunction.arzela_ascoli₂ rangeSet hrange
    (compactRangeLipschitzFamily (Domain := Domain) constant rangeSet)
    (isClosed_compactRangeLipschitzFamily constant hrange.isClosed)
  · intro path time hpath
    exact hpath.2 time
  · exact (LipschitzWith.uniformEquicontinuous
      ((↑) : compactRangeLipschitzFamily
        (Domain := Domain) constant rangeSet → Domain → State)
      constant fun path => path.property.1).equicontinuous

/-- Every sequence of common-range uniformly Lipschitz paths has a uniformly
convergent subsequence whose limit has the same range and Lipschitz bound. -/
theorem exists_tendsto_subsequence_compactRangeLipschitzFamily
    (constant : NNReal) {rangeSet : Set State} (hrange : IsCompact rangeSet)
    (path : ℕ → BoundedContinuousFunction Domain State)
    (hpath : ∀ n, path n ∈ compactRangeLipschitzFamily constant rangeSet) :
    ∃ limit ∈ compactRangeLipschitzFamily constant rangeSet,
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (path ∘ subsequence) atTop (nhds limit) := by
  have hfrequent : ∃ᶠ n in atTop,
      path n ∈ compactRangeLipschitzFamily constant rangeSet :=
    Frequently.of_forall hpath
  obtain ⟨limit, hlimit, subsequence, hsubsequence, htendsto⟩ :=
    (isCompact_compactRangeLipschitzFamily constant hrange).isSeqCompact
      |>.subseq_of_frequently_in hfrequent
  exact ⟨limit, hlimit, subsequence, hsubsequence, htendsto⟩

end Viability
end Math
