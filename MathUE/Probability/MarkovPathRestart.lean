import MathUE.Probability.MarkovPathConcentration
import MathUE.Probability.TrajectoryPrefixRestriction

/-!
# Restriction and restart of a homogeneous Markov path law

This module specializes exact trajectory-prefix restriction to a homogeneous
Markov kernel and identifies the continuation with the same kernel's law from
the next state. The restriction identity remains valid for zero-probability
successors and does not require a countable state space.
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

noncomputable section

variable {State : Type*} [MeasurableSpace State]

def dropPrefix (time : ℕ) :
    ((index : Finset.Iic (time + 1)) → State) →
      ((index : Finset.Iic time) → State) :=
  fun path index => path ⟨index.1 + 1, Finset.mem_Iic.mpr (by
    have hindex := Finset.mem_Iic.mp index.property
    omega)⟩

theorem measurable_dropPrefix (time : ℕ) :
    Measurable (dropPrefix (State := State) time) := by
  exact measurable_pi_lambda _ fun index => measurable_pi_apply _

private theorem partialTraj_succ_apply {Y : ℕ → Type*} [∀ time, MeasurableSpace (Y time)]
    {transition : (time : ℕ) →
      Kernel ((index : Finset.Iic time) → Y index) (Y (time + 1))}
    [∀ time, IsMarkovKernel (transition time)] (time : ℕ)
    (initial : (index : Finset.Iic time) → Y index) :
    Kernel.partialTraj transition time (time + 1) initial =
      (transition time initial).map fun next =>
        _root_.IicProdIoc (X := Y) time (time + 1)
          (initial, MeasurableEquiv.piSingleton (X := Y) time next) := by
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ measurable_IicProdIoc,
    Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton time).measurable,
    Measure.dirac_prod, Measure.map_map measurable_IicProdIoc (by fun_prop),
    Measure.map_map (by fun_prop) (MeasurableEquiv.piSingleton time).measurable]
  rfl

theorem trajectoryKernel_dropPrefix (transition : Kernel State State)
    [IsMarkovKernel transition] (time : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => State)
        (trajectoryKernel transition) (time + 1) (time + 2)).map
        (dropPrefix (State := State) (time + 1)) =
      (Kernel.partialTraj (X := fun _ : ℕ => State)
        (trajectoryKernel transition) time (time + 1)).comap
          (dropPrefix (State := State) time)
          (measurable_dropPrefix (State := State) time) := by
  ext initial
  rw [Kernel.map_apply _ (measurable_dropPrefix (State := State) (time + 1))]
  rw [partialTraj_succ_apply]
  have hextend : Measurable (fun next : State =>
      _root_.IicProdIoc (X := fun _ : ℕ => State) (time + 1) (time + 2)
        (initial, MeasurableEquiv.piSingleton
          (X := fun _ : ℕ => State) (time + 1) next)) := by
    exact measurable_IicProdIoc.comp
      (measurable_const.prodMk (MeasurableEquiv.piSingleton (time + 1)).measurable)
  rw [Measure.map_map (measurable_dropPrefix (State := State) (time + 1)) hextend]
  rw [Kernel.comap_apply, partialTraj_succ_apply]
  have htransition :
      trajectoryKernel transition (time + 1) initial =
        trajectoryKernel transition time (dropPrefix time initial) := by
    simp [trajectoryKernel, lastPrefix, dropPrefix]
  rw [htransition]
  have hmaps :
      (dropPrefix (State := State) (time + 1) ∘ fun next =>
        _root_.IicProdIoc (X := fun _ : ℕ => State) (time + 1) (time + 2)
          (initial, MeasurableEquiv.piSingleton
            (X := fun _ : ℕ => State) (time + 1) next)) =
      fun next => _root_.IicProdIoc (X := fun _ : ℕ => State) time (time + 1)
        (dropPrefix time initial,
          MeasurableEquiv.piSingleton (X := fun _ : ℕ => State) time next) := by
    funext next index
    have hshift : index.1 + 1 ≤ time + 1 ↔ index.1 ≤ time := by omega
    by_cases hindex : index.1 ≤ time
    · simp [Function.comp_apply, dropPrefix, _root_.IicProdIoc,
        MeasurableEquiv.piSingleton, hindex, hshift.mpr hindex]
    · simp [Function.comp_apply, dropPrefix, _root_.IicProdIoc,
        MeasurableEquiv.piSingleton, hindex, hshift.not.mpr hindex]
  rw [hmaps]

theorem trajectoryKernel_partialTraj_dropPrefix
    (transition : Kernel State State) [IsMarkovKernel transition]
    {time : ℕ} (htime : 1 ≤ time) :
    (Kernel.partialTraj (X := fun _ : ℕ => State)
        (trajectoryKernel transition) 1 (time + 1)).map
        (dropPrefix (State := State) time) =
      (Kernel.partialTraj (X := fun _ : ℕ => State)
        (trajectoryKernel transition) 0 time).comap
          (dropPrefix (State := State) 0)
          (measurable_dropPrefix (State := State) 0) := by
  induction time, htime using Nat.le_induction with
  | base =>
      exact trajectoryKernel_dropPrefix transition 0
  | succ time htime inductionHypothesis =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.succ_le_succ (Nat.zero_le time))]
      rw [Kernel.map_comp]
      rw [trajectoryKernel_dropPrefix]
      rw [← Kernel.comp_map _ _ (measurable_dropPrefix (State := State) time)]
      rw [inductionHypothesis]
      rw [← Kernel.comp_deterministic_eq_comap]
      rw [← Kernel.comp_assoc]
      rw [Kernel.comp_deterministic_eq_comap]
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le time)]

/-- Drop the initial coordinate of an infinite path. -/
def dropFirst (path : ℕ → State) (time : ℕ) : State := path (time + 1)

theorem measurable_dropFirst : Measurable (dropFirst (State := State)) := by
  exact measurable_pi_lambda _ fun time => measurable_pi_apply (time + 1)

def prependInitialPrefix (start : State) :
    ((index : Finset.Iic 0) → State) → ((index : Finset.Iic 1) → State) :=
  fun initial => Kernel.extendPrefix (X := fun _ : ℕ => State)
    0 (initialPrefix start) (initial ⟨0, Finset.mem_Iic.mpr le_rfl⟩)

theorem measurable_prependInitialPrefix (start : State) :
    Measurable (prependInitialPrefix (State := State) start) := by
  apply measurable_pi_lambda
  intro index
  by_cases hindex : index.1 ≤ 0
  · simp [prependInitialPrefix, Kernel.extendPrefix, _root_.IicProdIoc, hindex]
  · have hone : index.1 = 1 := by
      have hle := Finset.mem_Iic.mp index.property
      omega
    have hindexEq : index = ⟨1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hone
    rw [hindexEq]
    have hfun :
        (fun initial => prependInitialPrefix start initial
          (⟨1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 1)) =
        fun initial => initial
          (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0) := by
      funext initial
      exact Kernel.extendPrefix_last (X := fun _ : ℕ => State)
        0 (initialPrefix start)
        (initial ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
    rw [hfun]
    exact measurable_pi_apply _

theorem dropPrefix_zero_prependInitialPrefix (start : State) :
    dropPrefix (State := State) 0 ∘ prependInitialPrefix start = id := by
  funext initial
  funext index
  have hindexEq : index = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subsingleton.elim _ _
  rw [hindexEq]
  simp [Function.comp_apply, dropPrefix, prependInitialPrefix,
    Kernel.extendPrefix_last]

omit [MeasurableSpace State] in
theorem frestrictLe_dropFirst (time : ℕ) :
    Preorder.frestrictLe time ∘ dropFirst (State := State) =
      dropPrefix time ∘ Preorder.frestrictLe (time + 1) := by
  funext path index
  rfl

theorem traj_one_dropFirst_comap_eq_traj_zero
    (transition : Kernel State State) [IsMarkovKernel transition]
    (start : State) :
    ((Kernel.traj (X := fun _ : ℕ => State)
        (trajectoryKernel transition) 1).map
        (dropFirst (State := State))).comap
          (prependInitialPrefix start) (measurable_prependInitialPrefix start) =
      Kernel.traj (X := fun _ : ℕ => State)
        (trajectoryKernel transition) 0 := by
  apply Kernel.eq_traj' (X := fun _ : ℕ => State)
    (trajectoryKernel transition) 1
  intro time htime
  rw [← Kernel.comap_map_comm _ (measurable_prependInitialPrefix start)
    (Preorder.measurable_frestrictLe time)]
  rw [← Kernel.map_comp_right _ measurable_dropFirst
    (Preorder.measurable_frestrictLe time)]
  rw [frestrictLe_dropFirst]
  rw [Kernel.map_comp_right _ (Preorder.measurable_frestrictLe (time + 1))
    (measurable_dropPrefix time)]
  rw [Kernel.traj_map_frestrictLe]
  rw [trajectoryKernel_partialTraj_dropPrefix transition htime]
  rw [← Kernel.comap_comp_right _ (measurable_prependInitialPrefix start)
    (measurable_dropPrefix 0)]
  ext initial measurableSet
  rw [Kernel.comap_apply]
  have hcomp := congrFun (dropPrefix_zero_prependInitialPrefix start) initial
  rw [hcomp]
  rfl

theorem traj_one_map_dropFirst_eq_lawFrom
    (transition : Kernel State State) [IsMarkovKernel transition]
    (start next : State) :
    (Kernel.traj (trajectoryKernel transition) 1
        (Kernel.extendPrefix (X := fun _ : ℕ => State)
          0 (initialPrefix start) next)).map
        (dropFirst (State := State)) =
      lawFrom transition next := by
  have hkernel := traj_one_dropFirst_comap_eq_traj_zero transition start
  have happ := congrArg
    (fun kernel => kernel (initialPrefix next)) hkernel
  rw [Kernel.comap_apply, Kernel.map_apply _ measurable_dropFirst] at happ
  simpa [prependInitialPrefix, initialPrefix, lawFrom] using happ

/-- Prepend a prescribed initial state to an infinite path. -/
def prependFirst (start : State) (path : ℕ → State) : ℕ → State
  | 0 => start
  | time + 1 => path time

theorem measurable_prependFirst (start : State) :
    Measurable (prependFirst (State := State) start) := by
  exact measurable_pi_lambda _ fun time => by
    cases time with
    | zero => exact measurable_const
    | succ time => exact measurable_pi_apply time

omit [MeasurableSpace State] in
theorem dropFirst_prependFirst (start : State) :
    dropFirst (State := State) ∘ prependFirst start = id := by
  funext path time
  rfl

theorem traj_one_eq_map_lawFrom_prependFirst
    [MeasurableSingletonClass State]
    (transition : Kernel State State) [IsMarkovKernel transition]
    (start next : State) :
    Kernel.traj (trajectoryKernel transition) 1
        (Kernel.extendPrefix (X := fun _ : ℕ => State)
          0 (initialPrefix start) next) =
      (lawFrom transition next).map (prependFirst start) := by
  let initialSegment := Kernel.extendPrefix (X := fun _ : ℕ => State)
    0 (initialPrefix start) next
  let continuation := Kernel.traj (X := fun _ : ℕ => State)
    (trajectoryKernel transition) 1 initialSegment
  have hprefix := Kernel.ae_traj_frestrictLe_eq (X := fun _ : ℕ => State)
    (trajectoryKernel transition) 1 initialSegment
  have hinverse : prependFirst start ∘ dropFirst (State := State) =ᵐ[continuation] id := by
    filter_upwards [hprefix] with path hpath
    funext time
    cases time with
    | zero =>
        have hzero := congrFun hpath
          (⟨0, Finset.mem_Iic.mpr (by omega)⟩ : Finset.Iic 1)
        simpa [Preorder.frestrictLe, initialSegment, Kernel.extendPrefix,
          _root_.IicProdIoc, initialPrefix, prependFirst] using hzero.symm
    | succ time => rfl
  calc
    continuation = continuation.map id := Measure.map_id.symm
    _ = continuation.map (prependFirst start ∘ dropFirst) :=
      (Measure.map_congr hinverse).symm
    _ = (continuation.map dropFirst).map (prependFirst start) :=
      (Measure.map_map (measurable_prependFirst start) measurable_dropFirst).symm
    _ = (lawFrom transition next).map (prependFirst start) := by
      rw [show continuation.map dropFirst = lawFrom transition next by
        exact traj_one_map_dropFirst_eq_lawFrom transition start next]

theorem lawFrom_restrict_next_eq_smul_map_prependFirst
    [MeasurableSingletonClass State]
    (transition : Kernel State State) [IsMarkovKernel transition]
    (start next : State) :
    (lawFrom transition start).restrict {path | path 1 = next} =
      transition start {next} •
        (lawFrom transition next).map (prependFirst start) := by
  rw [lawFrom_restrict_next_eq_smul_traj]
  rw [traj_one_eq_map_lawFrom_prependFirst]

end

end Math.MarkovPath
