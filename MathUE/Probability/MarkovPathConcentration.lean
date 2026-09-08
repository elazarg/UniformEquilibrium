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

end

end Math.MarkovPath
