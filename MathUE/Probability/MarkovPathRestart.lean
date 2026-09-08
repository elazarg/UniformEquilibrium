import MathUE.Probability.MarkovPathConcentration
import MathUE.Probability.TrajectoryPrefixRestriction

/-!
# One-step restriction of a Markov path law

This module specializes exact trajectory-prefix restriction to a homogeneous
Markov kernel. The continuation is expressed as an absolute-time trajectory.
-/

namespace Math.MarkovPath

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {State : Type*} [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Restricting `lawFrom` to its next state produces the exact absolute-time continuation. -/
theorem lawFrom_restrict_next_eq_smul_traj
    (transition : Kernel State State) [IsMarkovKernel transition]
    (start next : State) :
    (lawFrom transition start).restrict {path | path 1 = next} =
      transition start {next} •
        Kernel.traj (trajectoryKernel transition) 1
          (Kernel.extendPrefix (X := fun _ : ℕ => State)
            0 (initialPrefix start) next) := by
  let exactPrefix := Kernel.extendPrefix (X := fun _ : ℕ => State)
    0 (initialPrefix start) next
  let exactEvent := {path : ℕ → State |
    Preorder.frestrictLe 1 path = exactPrefix}
  have hevents : {path : ℕ → State | path 1 = next} =ᵐ[lawFrom transition start]
      exactEvent := by
    filter_upwards [ae_startsAt transition start] with path hstart
    change (path 1 = next) = (Preorder.frestrictLe 1 path = exactPrefix)
    apply propext
    constructor
    · intro hnext
      funext index
      have hindex : (index : ℕ) = 0 ∨ (index : ℕ) = 1 := by
        have hle := Finset.mem_Iic.mp index.property
        omega
      rcases hindex with hzero | hone
      · have hindexEq : index = ⟨0, Finset.mem_Iic.mpr (by omega)⟩ :=
          Subtype.ext hzero
        rw [hindexEq]
        simpa [Preorder.frestrictLe, exactPrefix, Kernel.extendPrefix,
          _root_.IicProdIoc, initialPrefix, StartsAt] using hstart
      · have hindexEq : index = ⟨1, Finset.mem_Iic.mpr le_rfl⟩ :=
          Subtype.ext hone
        rw [hindexEq]
        change path 1 = exactPrefix ⟨1, Finset.mem_Iic.mpr le_rfl⟩
        rw [show exactPrefix = Kernel.extendPrefix (X := fun _ : ℕ => State)
          0 (initialPrefix start) next by rfl, Kernel.extendPrefix_last]
        exact hnext
    · intro hprefix
      have hlast := congrFun hprefix ⟨1, Finset.mem_Iic.mpr le_rfl⟩
      change path 1 = exactPrefix ⟨1, Finset.mem_Iic.mpr le_rfl⟩ at hlast
      rw [show exactPrefix = Kernel.extendPrefix (X := fun _ : ℕ => State)
        0 (initialPrefix start) next by rfl, Kernel.extendPrefix_last] at hlast
      exact hlast
  rw [Measure.restrict_congr_set hevents]
  change (Kernel.traj (trajectoryKernel transition) 0 (initialPrefix start)).restrict
      exactEvent = _
  rw [Kernel.traj_restrict_extendPrefix]
  change (transition.comap (lastPrefix 0) (measurable_lastPrefix 0))
      (initialPrefix start) {next} • _ = _
  rw [Kernel.comap_apply]
  simp [lastPrefix, initialPrefix]

end

end Math.MarkovPath
