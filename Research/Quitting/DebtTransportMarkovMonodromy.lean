/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.StationaryCommunicatingClass

/-!
# Debt transport is stationary Markov monodromy

A closed word of nonnegative debt transports is naturally a Markov kernel on
the time-expanded player set.  The debt vector is a stationary, generally
non-full-support weight.  The generic stationary-return theorem requires only
nonnegativity everywhere and positivity at the source of the selected edge.

Thus every positive debt-transfer edge lies on a recurrent support cycle.
The resulting object is a Markov/transportation-polytope object, not a group
in general.  A permutation or group orbit appears only after a deterministic
extremalization which is not asserted here.
-/

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {S : Type*}

/-- A finite stationary debt monodromy.  This is the abstract return kernel
obtained by composing a closed word of normalized nonnegative debt
transports. -/
structure StationaryDebtMonodromy (S : Type*) [Fintype S] where
  kernel : S → PMF S
  debt : S → ℝ
  debt_nonneg : ∀ state, 0 ≤ debt state
  stationary : ∀ destination,
    ∑ source, debt source * (kernel source destination).toReal =
      debt destination

namespace StationaryDebtMonodromy

/-- Every positive edge in a stationary debt monodromy lies on a support
cycle. -/
theorem supportEdge_returns
    [Fintype S]
    (M : StationaryDebtMonodromy S)
    {source destination : S}
    (hsource : 0 < M.debt source)
    (hstep : PMFSupportStep M.kernel source destination) :
    PMFReachable M.kernel destination source :=
  supportStep_returns_of_stationary_nonnegative
    M.kernel M.debt M.debt_nonneg M.stationary hsource hstep

/-- A positive stationary edge also forces positive debt at its destination.
This identifies the positive-debt support as a closed recurrent carrier. -/
theorem debt_pos_of_supportEdge
    [Fintype S]
    (M : StationaryDebtMonodromy S)
    {source destination : S}
    (hsource : 0 < M.debt source)
    (hstep : PMFSupportStep M.kernel source destination) :
    0 < M.debt destination := by
  rw [← M.stationary destination]
  apply Finset.sum_pos'
  · intro state _
    exact mul_nonneg (M.debt_nonneg state) ENNReal.toReal_nonneg
  · refine ⟨source, Finset.mem_univ _, ?_⟩
    exact mul_pos hsource
      (ENNReal.toReal_pos hstep
        (PMF.apply_ne_top (M.kernel source) destination))

/-- Positive support edges are mutually reachable. -/
theorem supportEdge_communicates
    [Fintype S]
    (M : StationaryDebtMonodromy S)
    {source destination : S}
    (hsource : 0 < M.debt source)
    (hstep : PMFSupportStep M.kernel source destination) :
    PMFCommunicates M.kernel source destination :=
  ⟨Relation.ReflTransGen.single hstep,
    M.supportEdge_returns hsource hstep⟩

end StationaryDebtMonodromy

end Probability
end Math
