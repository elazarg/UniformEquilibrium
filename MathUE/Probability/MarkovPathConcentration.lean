import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Supported paths of a Markov kernel

This module records the missing carrier fact for a path law already supplied by
Ionescu--Tulcea: if every transition is almost surely in a measurable edge relation, then
almost every generated path follows that relation at every time.
-/

namespace Math.MarkovPath

open MeasureTheory ProbabilityTheory Set

noncomputable section

variable {State : Type*} [MeasurableSpace State]

/-- The last coordinate in a finite trajectory prefix. -/
def lastPrefix (time : ℕ) (history : (i : Finset.Iic time) → State) : State :=
  history ⟨time, Finset.mem_Iic.mpr le_rfl⟩

theorem measurable_lastPrefix (time : ℕ) : Measurable (lastPrefix (State := State) time) := by
  exact measurable_pi_apply _

/-- A Markov kernel, regarded as the history-dependent kernel expected by Ionescu--Tulcea. -/
def trajectoryKernel (transition : Kernel State State) (time : ℕ) :
    Kernel ((i : Finset.Iic time) → State) State :=
  transition.comap (lastPrefix time) (measurable_lastPrefix time)

instance trajectoryKernel_isMarkov (transition : Kernel State State)
    [IsMarkovKernel transition] (time : ℕ) :
    IsMarkovKernel (trajectoryKernel transition time) := by
  unfold trajectoryKernel
  infer_instance

/-- The singleton prefix used to start `Kernel.traj` at a prescribed state. -/
def initialPrefix (start : State) : (i : Finset.Iic 0) → State :=
  fun _ => start

/-- The Ionescu--Tulcea path law of a Markov kernel from a prescribed state. -/
def lawFrom (transition : Kernel State State) [IsMarkovKernel transition]
    (start : State) : Measure (ℕ → State) :=
  Kernel.traj (trajectoryKernel transition) 0 (initialPrefix start)

instance lawFrom_isProbability (transition : Kernel State State)
    [IsMarkovKernel transition] (start : State) :
    IsProbabilityMeasure (lawFrom transition start) := by
  unfold lawFrom
  infer_instance

/-- The coordinate at time one under `lawFrom` has the prescribed transition law. -/
theorem map_lawFrom_one (transition : Kernel State State) [IsMarkovKernel transition]
    (start : State) :
    (lawFrom transition start).map (fun path => path 1) = transition start := by
  have hkernel := Kernel.map_traj_succ_self
    (X := fun _ : ℕ => State) (κ := trajectoryKernel transition) (a := 0)
  have happ := congrArg
    (fun kernel => kernel (initialPrefix start)) hkernel
  rw [Kernel.map_apply _ (by fun_prop)] at happ
  simpa [lawFrom, trajectoryKernel, lastPrefix, initialPrefix] using happ

/-- A path follows the displayed edge relation at every adjacent pair. -/
def Follows (allowed : Set (State × State)) (path : ℕ → State) : Prop :=
  ∀ time, (path time, path (time + 1)) ∈ allowed

theorem measurableSet_follows (allowed : Set (State × State))
    (hallowed : MeasurableSet allowed) :
    MeasurableSet {path : ℕ → State | Follows allowed path} := by
  rw [show {path : ℕ → State | Follows allowed path} =
      ⋂ time, (fun path => (path time, path (time + 1))) ⁻¹' allowed by
    ext path
    simp [Follows]]
  exact MeasurableSet.iInter fun _ => hallowed.preimage (by fun_prop)

theorem ae_follows_of_transition
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (hallowed : MeasurableSet allowed)
    (hsupported : ∀ state, ∀ᵐ next ∂transition state, (state, next) ∈ allowed)
    (start : State) :
    ∀ᵐ path ∂lawFrom transition start, Follows allowed path := by
  unfold Follows
  rw [ae_all_iff]
  intro time
  let prefixLaw := Kernel.partialTraj (X := fun _ : ℕ => State)
    (trajectoryKernel transition) 0 time (initialPrefix start)
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => State) (κ := trajectoryKernel transition) (a := 0) (b := time)
    (x₀ := initialPrefix start) (Nat.zero_le time)
  have hmeasurablePair : Measurable
      (fun pair : ((i : Finset.Iic time) → State) × State =>
        (lastPrefix time pair.1, pair.2)) :=
    ((measurable_lastPrefix time).comp measurable_fst).prodMk measurable_snd
  have hmeasurableAllowed : MeasurableSet
      {pair : ((i : Finset.Iic time) → State) × State |
        (lastPrefix time pair.1, pair.2) ∈ allowed} :=
    hallowed.preimage hmeasurablePair
  have hpairs : ∀ᵐ pair ∂prefixLaw ⊗ₘ trajectoryKernel transition time,
      (lastPrefix time pair.1, pair.2) ∈ allowed := by
    apply Measure.ae_compProd_of_ae_ae
    · exact hmeasurableAllowed
    · filter_upwards [] with history
      simpa [trajectoryKernel, lastPrefix] using hsupported (lastPrefix time history)
  rw [hpair] at hpairs
  have hpath := (ae_map_iff (by fun_prop) hmeasurableAllowed).mp hpairs
  simpa [lawFrom, lastPrefix] using hpath

/-- Paths whose every adjacent pair lies in `allowed`. -/
abbrev SupportedPath (allowed : Set (State × State)) :=
  {path : ℕ → State // Follows allowed path}

/-- The generated path law transported to its almost-sure supported carrier. -/
def supportedLaw
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (start : State) : Measure (SupportedPath allowed) :=
  Measure.comap Subtype.val (lawFrom transition start)

theorem map_supportedLaw
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (hallowed : MeasurableSet allowed)
    (hsupported : ∀ state, ∀ᵐ next ∂transition state, (state, next) ∈ allowed)
    (start : State) :
    (supportedLaw transition allowed start).map Subtype.val = lawFrom transition start := by
  unfold supportedLaw
  calc
    (Measure.comap Subtype.val (lawFrom transition start)).map Subtype.val =
        (lawFrom transition start).restrict {path | Follows allowed path} := by
      exact map_comap_subtype_coe (measurableSet_follows allowed hallowed) _
    _ = lawFrom transition start :=
      Measure.restrict_eq_self_of_ae_mem
        (ae_follows_of_transition transition allowed hallowed hsupported start)

theorem supportedLaw_isProbability
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (hallowed : MeasurableSet allowed)
    (hsupported : ∀ state, ∀ᵐ next ∂transition state, (state, next) ∈ allowed)
    (start : State) :
    IsProbabilityMeasure (supportedLaw transition allowed start) := by
  constructor
  have hmap := map_supportedLaw transition allowed hallowed hsupported start
  have huniv := congrArg (fun measure : Measure (ℕ → State) => measure Set.univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at huniv
  simpa using huniv

section Started

variable [MeasurableSingletonClass State]

/-- A path starts at the displayed state. -/
def StartsAt (start : State) (path : ℕ → State) : Prop :=
  path 0 = start

theorem measurableSet_startsAt (start : State) :
    MeasurableSet {path : ℕ → State | StartsAt start path} := by
  exact measurableSet_singleton start |>.preimage (measurable_pi_apply 0)

theorem ae_startsAt
    (transition : Kernel State State) [IsMarkovKernel transition]
    (start : State) :
    ∀ᵐ path ∂lawFrom transition start, StartsAt start path := by
  have hprefix := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => State) (κ := trajectoryKernel transition)
    0 0 (initialPrefix start)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at hprefix
  have hevent : {path : ℕ → State | StartsAt start path} =
      Preorder.frestrictLe 0 ⁻¹'
        ({initialPrefix start} : Set ((i : Finset.Iic 0) → State)) := by
    ext path
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, StartsAt]
    constructor
    · intro hstart
      funext index
      have hindex : (index : ℕ) = 0 :=
        Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp index.property)
      simpa [Preorder.frestrictLe, initialPrefix, hindex] using hstart
    · intro hprefixValue
      have hzero := congrFun hprefixValue ⟨0, Finset.mem_Iic.mpr le_rfl⟩
      simpa [Preorder.frestrictLe, initialPrefix] using hzero
  change ∀ᵐ path ∂lawFrom transition start,
    path ∈ {path : ℕ → State | StartsAt start path}
  rw [ae_mem_iff_measure_eq (measurableSet_startsAt start).nullMeasurableSet]
  rw [hevent, ← Measure.map_apply (by fun_prop)
    (measurableSet_singleton (initialPrefix start))]
  rw [show lawFrom transition start =
      Kernel.traj (trajectoryKernel transition) 0 (initialPrefix start) by rfl]
  rw [hprefix]
  simp

/-- Paths that start at `start` and whose adjacent pairs all lie in `allowed`. -/
abbrev SupportedPathFrom (allowed : Set (State × State)) (start : State) :=
  {path : ℕ → State // StartsAt start path ∧ Follows allowed path}

/-- The generated path law transported to the literal started-and-supported carrier. -/
def supportedLawFrom
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (start : State) :
    Measure (SupportedPathFrom allowed start) :=
  Measure.comap Subtype.val (lawFrom transition start)

theorem map_supportedLawFrom
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (hallowed : MeasurableSet allowed)
    (hsupported : ∀ state, ∀ᵐ next ∂transition state, (state, next) ∈ allowed)
    (start : State) :
    (supportedLawFrom transition allowed start).map Subtype.val =
      lawFrom transition start := by
  have hcarrier : MeasurableSet
      {path : ℕ → State | StartsAt start path ∧ Follows allowed path} :=
    (measurableSet_startsAt start).inter (measurableSet_follows allowed hallowed)
  unfold supportedLawFrom
  calc
    (Measure.comap Subtype.val (lawFrom transition start)).map Subtype.val =
        (lawFrom transition start).restrict
          {path | StartsAt start path ∧ Follows allowed path} := by
      exact map_comap_subtype_coe hcarrier _
    _ = lawFrom transition start := Measure.restrict_eq_self_of_ae_mem <| by
      filter_upwards [ae_startsAt transition start,
        ae_follows_of_transition transition allowed hallowed hsupported start] with
        path hstart hfollows
      exact ⟨hstart, hfollows⟩

theorem supportedLawFrom_isProbability
    (transition : Kernel State State) [IsMarkovKernel transition]
    (allowed : Set (State × State)) (hallowed : MeasurableSet allowed)
    (hsupported : ∀ state, ∀ᵐ next ∂transition state, (state, next) ∈ allowed)
    (start : State) :
    IsProbabilityMeasure (supportedLawFrom transition allowed start) := by
  constructor
  have hmap := map_supportedLawFrom transition allowed hallowed hsupported start
  have huniv := congrArg (fun measure : Measure (ℕ → State) => measure Set.univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at huniv
  simpa using huniv

end Started

end

end Math.MarkovPath
