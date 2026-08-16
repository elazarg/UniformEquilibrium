/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.GraphDirectedPeriodicLift

/-!
# Periodic lifts are dense in a contracting full shift

For a one-vertex graph-directed compact system, every edge sequence is an
admissible full-shift code. For a positive `period`, repeat the code's first
`period` symbols. The resulting code and its unique compatible pullback lift
are periodic, and common-prefix continuity bounds the initial-value error by
`contraction ^ period * diameterBudget`.

At `period = 0`, periodicization is the original code, the asserted period
identity is vacuous, and the theorem gives the diameter bound. Keeping this
case makes the statements premise-free without attributing positive-period
content to it.
-/

noncomputable section

namespace Math
namespace Topology

variable {Edge Point : Type*} [MetricSpace Point]

/-- Repeat the first `period` entries of a one-sided code. For period zero,
the code is unchanged. -/
def periodicizeCode (code : ℕ → Edge) (period : ℕ) : ℕ → Edge :=
  fun time ↦ code (time % period)

@[simp] theorem periodicizeCode_zero (code : ℕ → Edge) :
    periodicizeCode code 0 = code := by
  funext time
  simp [periodicizeCode]

/-- Periodicization has the requested period. At period zero this is the
reflexive identity. -/
theorem periodicizeCode_add_period
    (code : ℕ → Edge) (period time : ℕ) :
    periodicizeCode code period (time + period) =
      periodicizeCode code period time := by
  unfold periodicizeCode
  rw [Nat.add_mod_right]

/-- Periodicization preserves the entire initial block. -/
theorem periodicizeCode_eq_of_lt
    (code : ℕ → Edge) {period time : ℕ} (htime : time < period) :
    periodicizeCode code period time = code time := by
  simp [periodicizeCode, Nat.mod_eq_of_lt htime]

/-- Every code on a one-vertex graph is admissible. -/
theorem GraphDirectedCompactSystem.fullShift_isAdmissiblePath
    (system : GraphDirectedCompactSystem Unit Edge Point)
    (code : ℕ → Edge) :
    system.IsAdmissiblePath (fun _ ↦ ()) code := by
  intro time
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Every compatible full-shift lift admits a lift of the periodicized code
whose initial value satisfies the common-prefix contraction bound. For a
positive period the new code and lift are genuinely periodic; at period zero
the periodicity equation is vacuous and the code is unchanged. -/
theorem GraphDirectedCompactSystem.exists_periodicLift_close
    (system : GraphDirectedCompactSystem Unit Edge Point)
    {contraction : ℝ}
    (hcontraction0 : 0 ≤ contraction)
    (hcontraction1 : contraction < 1)
    (hcontract : system.IsUniformContraction contraction)
    (code : ℕ → Edge) {value : ℕ → Point}
    (hvalue : system.IsCompatiblePullbackPath (fun _ ↦ ()) code value)
    (period : ℕ) :
    ∃ periodicValue : ℕ → Point,
      system.IsCompatiblePullbackPath (fun _ ↦ ())
          (periodicizeCode code period) periodicValue ∧
        (∀ time, periodicValue (time + period) = periodicValue time) ∧
        dist (periodicValue 0) (value 0) ≤
          contraction ^ period * system.diameterBudget := by
  let periodicCode := periodicizeCode code period
  have hperiodicPath :=
    GraphDirectedCompactSystem.fullShift_isAdmissiblePath system periodicCode
  obtain ⟨periodicValue, hperiodicValue⟩ :=
    system.exists_compatiblePullbackPath
      (fun _ ↦ ()) periodicCode hperiodicPath
  refine ⟨periodicValue, hperiodicValue, ?_, ?_⟩
  · apply system.compatiblePullbackPath_periodic
      (fun _ ↦ ()) periodicCode hperiodicPath period
      (fun _ ↦ rfl) (fun time ↦ ?_)
      hcontraction0 hcontraction1 hcontract hperiodicValue
    exact periodicizeCode_add_period code period time
  · apply dist_compatiblePullbackPath_le_pow_mul_diameter_of_commonPrefix
      system (fun _ ↦ ()) (fun _ ↦ ()) periodicCode code
      hperiodicPath
      (GraphDirectedCompactSystem.fullShift_isAdmissiblePath system code)
      hcontraction0 hcontract hperiodicValue hvalue 0 period
    · intro offset hoffset
      simpa using periodicizeCode_eq_of_lt code hoffset
    · rfl

end Topology
end Math
