import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Exact finite-prefix restriction for Ionescu--Tulcea trajectories

This module records exact finite-prefix concentration and the one-successor restriction identity
for a trajectory with a possibly time-dependent state family.
-/

namespace ProbabilityTheory.Kernel

open MeasureTheory Set

noncomputable section

variable {X : ℕ → Type*} [∀ time, MeasurableSpace (X time)]
  [∀ time, MeasurableSingletonClass (X time)]

variable (transition : (time : ℕ) →
  Kernel ((index : Finset.Iic time) → X index) (X (time + 1)))
  [∀ time, IsMarkovKernel (transition time)]

/-- Extend a finite trajectory prefix by one displayed successor. -/
def extendPrefix (time : ℕ) (initial : (index : Finset.Iic time) → X index)
    (next : X (time + 1)) : (index : Finset.Iic (time + 1)) → X index :=
  _root_.IicProdIoc (X := X) time (time + 1)
    (initial, MeasurableEquiv.piSingleton (X := X) time next)

omit [∀ time, MeasurableSingletonClass (X time)] in
theorem extendPrefix_last (time : ℕ)
    (initial : (index : Finset.Iic time) → X index) (next : X (time + 1)) :
    extendPrefix time initial next ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩ = next := by
  simp [extendPrefix, _root_.IicProdIoc, MeasurableEquiv.piSingleton]

theorem ae_traj_frestrictLe_eq (time : ℕ)
    (initial : (index : Finset.Iic time) → X index) :
    ∀ᵐ path ∂traj transition time initial,
      Preorder.frestrictLe time path = initial := by
  have hmarginal := traj_map_frestrictLe_apply
    (κ := transition) time time initial
  rw [partialTraj_self, id_apply] at hmarginal
  have hevent : {path : (time : ℕ) → X time |
      Preorder.frestrictLe time path = initial} =
      Preorder.frestrictLe time ⁻¹'
        ({initial} : Set ((index : Finset.Iic time) → X index)) := by
    rfl
  change ∀ᵐ path ∂traj transition time initial,
    path ∈ {path : (time : ℕ) → X time |
      Preorder.frestrictLe time path = initial}
  rw [hevent]
  rw [ae_mem_iff_measure_eq ((measurableSet_singleton initial).preimage (by fun_prop)
    |>.nullMeasurableSet)]
  rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton initial)]
  rw [hmarginal]
  simp

theorem traj_restrict_prefix_eq_self (time : ℕ)
    (initial : (index : Finset.Iic time) → X index) :
    (traj transition time initial).restrict
      {path | Preorder.frestrictLe time path = initial} =
        traj transition time initial := by
  exact Measure.restrict_eq_self_of_ae_mem
    (ae_traj_frestrictLe_eq transition time initial)

theorem traj_restrict_prefix_eq_zero (time : ℕ)
    (initial other : (index : Finset.Iic time) → X index)
    (hne : initial ≠ other) :
    (traj transition time initial).restrict
      {path | Preorder.frestrictLe time path = other} = 0 := by
  rw [Measure.restrict_eq_zero, measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_traj_frestrictLe_eq transition time initial] with path hpath
  exact fun heq => hne (hpath.symm.trans heq)

theorem partialTraj_succ_singleton (time : ℕ)
    (initial : (index : Finset.Iic time) → X index) (next : X (time + 1)) :
    partialTraj transition time (time + 1) initial
      {extendPrefix time initial next} = transition time initial {next} := by
  rw [partialTraj_succ_self, Kernel.map_apply]
  · rw [Measure.map_apply measurable_IicProdIoc (measurableSet_singleton _)]
    rw [Kernel.prod_apply, Kernel.id_apply, Kernel.map_apply _
      (MeasurableEquiv.piSingleton (X := X) time).measurable]
    have hpreimage :
        _root_.IicProdIoc (X := X) time (time + 1) ⁻¹'
            {extendPrefix time initial next} =
          {(initial, MeasurableEquiv.piSingleton (X := X) time next)} := by
      ext pair
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (MeasurableEquiv.IicProdIoc (X := X)
        (Nat.le_add_right time 1)).injective.eq_iff
    rw [hpreimage]
    rw [show {(initial, MeasurableEquiv.piSingleton (X := X) time next)} =
        {initial} ×ˢ {MeasurableEquiv.piSingleton (X := X) time next} by
      ext pair
      simp]
    rw [Measure.prod_prod]
    rw [Measure.dirac_apply' _ (measurableSet_singleton initial)]
    rw [(MeasurableEquiv.piSingleton (X := X) time).map_apply]
    have hsingleton :
        (MeasurableEquiv.piSingleton (X := X) time :
            X (time + 1) → ((index : Finset.Ioc time (time + 1)) → X index)) ⁻¹'
            {MeasurableEquiv.piSingleton (X := X) time next} = {next} := by
      ext state
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact (MeasurableEquiv.piSingleton (X := X) time).injective.eq_iff
    rw [hsingleton]
    simp
  · exact measurable_IicProdIoc

/-- Restricting a trajectory to one exact successor prefix leaves precisely the trajectory
continued from that prefix, scaled by the one-step transition mass. -/
theorem traj_restrict_extendPrefix (time : ℕ)
    (initial : (index : Finset.Iic time) → X index) (next : X (time + 1)) :
    (traj transition time initial).restrict
        {path | Preorder.frestrictLe (time + 1) path = extendPrefix time initial next} =
      transition time initial {next} •
        traj transition (time + 1) (extendPrefix time initial next) := by
  let extended := extendPrefix time initial next
  let event := {path : (time : ℕ) → X time |
    Preorder.frestrictLe (time + 1) path = extended}
  have hevent : MeasurableSet event := by
    exact (measurableSet_singleton extended).preimage (by fun_prop)
  change (traj transition time initial).restrict event =
    transition time initial {next} • traj transition (time + 1) extended
  have hdecomp := congrArg
    (fun kernel : Kernel ((index : Finset.Iic time) → X index)
        ((time : ℕ) → X time) => kernel initial)
    (traj_comp_partialTraj (κ := transition) (Nat.le_add_right time 1))
  rw [← hdecomp]
  have hrestrict := congrArg
    (fun kernel : Kernel ((index : Finset.Iic time) → X index)
        ((time : ℕ) → X time) => kernel initial)
    (Kernel.comp_restrict
      (κ := partialTraj transition time (time + 1))
      (η := traj transition (time + 1)) hevent)
  change ((traj transition (time + 1) ∘ₖ
    partialTraj transition time (time + 1)).restrict hevent) initial = _
  rw [← hrestrict]
  ext set hset
  rw [Kernel.comp_apply' _ _ _ hset]
  have hpoint (finitePrefix : (index : Finset.Iic (time + 1)) → X index) :
      ((traj transition (time + 1) finitePrefix).restrict event) set =
        ({extended} : Set ((index : Finset.Iic (time + 1)) → X index)).indicator
          (fun _ => traj transition (time + 1) extended set) finitePrefix := by
    by_cases hprefix : finitePrefix = extended
    · subst finitePrefix
      rw [traj_restrict_prefix_eq_self]
      simp
    · rw [traj_restrict_prefix_eq_zero transition (time + 1)
        finitePrefix extended hprefix]
      simp [hprefix]
  conv_lhs =>
    enter [2, finitePrefix]
    rw [Kernel.restrict_apply]
    rw [hpoint finitePrefix]
  rw [lintegral_indicator (measurableSet_singleton extended)]
  rw [lintegral_singleton]
  rw [partialTraj_succ_singleton transition time initial next]
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_comm _ _

end

end ProbabilityTheory.Kernel
