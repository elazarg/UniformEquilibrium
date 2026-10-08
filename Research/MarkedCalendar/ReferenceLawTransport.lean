import Research.MarkedCalendar.FiniteLawChart
import MathUE.Probability.FiniteSignedConditioning
import MathUE.MeasureTheory.SignedConditioning

/-! # Actual finite-law transport on an unchanged reference chart

A finite law on the old positive-cell carrier determines a literal original
stopping law, including Never. The reference density compiler recovers this
law through the old decoder. Independent products have exactly the original
terminal-outcome law, and every original pure reply has exactly the updated
outcome law against these opponents. Unsupported finite deadlines and empty
opponent products are included.

No replacement average chart is identified with the reference chart. Signed
conditioning on any finite cell event commutes with this one density compiler;
the decoded event mass and its signed radius are derived from the actual finite
law. Moving-law convergence and complete-cap transport are separate obligations;
no cap or convergence oracle is used here.
-/

noncomputable section

open Set Filter MeasureTheory GameTheory.Math.Probability

namespace GameTheory.MarkedCalendarChart

variable {ι : Type} [Fintype ι] [Nonempty ι]

attribute [local instance] outcomeMeasurableSpace outcomeMeasurableSingletonClass

/-- The discrete measurable space on literal original stopping choices, used only locally. -/
@[instance_reducible]
def stoppingChoiceMeasurableSpace : MeasurableSpace (Option ℕ) := ⊤

attribute [local instance] stoppingChoiceMeasurableSpace

local instance stoppingChoiceMeasurableSingletonClass :
    MeasurableSingletonClass (Option ℕ) where
  measurableSet_singleton _ := trivial

/-- A literal original stopping law on the old cell clocks, not on a newly averaged chart. -/
def referenceOriginalLaw (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) : FinDist (Option ℕ) :=
  p.map (fun a : Cell reference => originalChoice a)

theorem referenceOriginalLaw_cellLaw (reference : ι → FinDist (Option ℕ)) (i : ι) :
    referenceOriginalLaw reference (cellLaw reference i) = reference i :=
  cellLaw_map_originalChoice reference i

/-- A decoded old-cell event has exactly its finite-law mass, including decoder fallback. -/
theorem referenceLaw_decodeCell_event_real (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) (event : Set (Cell reference)) :
    (referenceLaw reference p : Measure unitInterval).real (decodeCell reference ⁻¹' event) =
      p.probOf event := by
  have hevent : MeasurableSet event := event.toFinite.measurableSet
  rw [← map_measureReal_apply (measurable_decodeCell reference) hevent]
  change ((referenceMeasure reference p).map (decodeCell reference)).real event = p.probOf event
  rw [referenceMeasure_map_decodeCell, FinDist.toMeasure_real_apply p hevent]

/-- The finite and measurable constructors use the same derived closed signed radius. -/
theorem referenceLaw_signedCondRadius (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) (event : Set (Cell reference)) :
    (referenceLaw reference p).signedCondRadius (decodeCell reference ⁻¹' event) =
      p.signedCondRadius event := by
  rw [ProbabilityMeasure.signedCondRadius, FinDist.signedCondRadius,
    referenceLaw_decodeCell_event_real]

/-- Signed finite conditioning compiles to the actual measurable signed law on the OLD chart.
The decoded event's normalizer and radius are derived, not extra supplied hypotheses. -/
theorem referenceLaw_signedCond (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) (event : Set (Cell reference))
    (hmass : 0 < p.probOf event) (parameter : ℝ)
    (hparameter : |parameter| ≤ p.signedCondRadius event) :
    referenceLaw reference (p.signedCond event hmass parameter hparameter) =
      (referenceLaw reference p).signedCond (decodeCell reference ⁻¹' event)
        (event.toFinite.measurableSet.preimage (measurable_decodeCell reference))
        (by rw [referenceLaw_decodeCell_event_real]; exact hmass) parameter
        (by rw [referenceLaw_signedCondRadius]; exact hparameter) := by
  classical
  have hformula (x : unitInterval) :
      referenceDensity reference (p.signedCond event hmass parameter hparameter) x =
        referenceDensity reference p x *
          (referenceLaw reference p).signedCondLikelihood
            (decodeCell reference ⁻¹' event) parameter x := by
    by_cases hx : ∃ cell : Cell reference, x ∈ interval reference cell
    · obtain ⟨cell, hcell⟩ := hx
      rw [referenceDensity_eq_of_mem_interval reference _ hcell,
        referenceDensity_eq_of_mem_interval reference p hcell,
        FinDist.prob_signedCond, FinDist.signedCondWeight,
        ProbabilityMeasure.signedCondLikelihood, referenceLaw_decodeCell_event_real]
      simp only [Set.indicator_apply, mem_preimage,
        decodeCell_of_mem_interval reference hcell]
      ring
    · have hnot : ∀ cell : Cell reference, x ∉ interval reference cell :=
        fun cell hcell => hx ⟨cell, hcell⟩
      rw [referenceDensity_eq_zero_of_notMem reference _ hnot,
        referenceDensity_eq_zero_of_notMem reference p hnot, zero_mul]
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.coe_signedCond]
  change volume.withDensity (fun x => ENNReal.ofReal
      (referenceDensity reference (p.signedCond event hmass parameter hparameter) x)) =
    (volume.withDensity (fun x => ENNReal.ofReal (referenceDensity reference p x))).withDensity
      (fun x => ENNReal.ofReal ((referenceLaw reference p).signedCondLikelihood
        (decodeCell reference ⁻¹' event) parameter x))
  rw [← withDensity_mul volume (measurable_referenceDensity reference p).ennreal_ofReal
    ((referenceLaw reference p).measurable_signedCondLikelihood
      (decodeCell reference ⁻¹' event)
      (event.toFinite.measurableSet.preimage (measurable_decodeCell reference))
      parameter).ennreal_ofReal]
  apply withDensity_congr_ae
  apply Eventually.of_forall
  intro x
  change ENNReal.ofReal
      (referenceDensity reference (p.signedCond event hmass parameter hparameter) x) =
    ENNReal.ofReal (referenceDensity reference p x) *
      ENNReal.ofReal ((referenceLaw reference p).signedCondLikelihood
        (decodeCell reference ⁻¹' event) parameter x)
  rw [hformula, ENNReal.ofReal_mul (referenceDensity_nonneg reference p x)]

theorem referenceOriginalLaw_map_stoppingTimeValue (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) :
    (referenceOriginalLaw reference p).map quittingStoppingTimeValue =
      p.map (fun a : Cell reference => (a : WithTop ℕ)) := by
  rw [referenceOriginalLaw, FinDist.map_comp]
  apply congrArg (fun f => p.map f)
  funext a
  exact stoppingTimeValue_originalChoice a

/-- Original clock support is derived from the actual old cell carrier. -/
theorem referenceOriginalLaw_clock_support_subset (reference : ι → FinDist (Option ℕ))
    (p : FinDist (Cell reference)) :
    ((referenceOriginalLaw reference p).map quittingStoppingTimeValue).support ⊆
      (averageClockLaw reference).support := by
  rw [referenceOriginalLaw_map_stoppingTimeValue, FinDist.support_map]
  rintro clock ⟨a, _, rfl⟩
  exact FinDist.mem_supportFinset.mp a.property

/-- Scalar decoder transport recovers the actual original stopping law, including Never. -/
theorem referenceMeasure_map_originalChoice_decodeCell
    (reference : ι → FinDist (Option ℕ)) (p : FinDist (Cell reference)) :
    (referenceMeasure reference p).map (fun x => originalChoice (decodeCell reference x)) =
      (referenceOriginalLaw reference p).toMeasure := by
  change (referenceMeasure reference p).map
    ((fun a : Cell reference => originalChoice a) ∘ decodeCell reference) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_decodeCell reference),
    referenceMeasure_map_decodeCell, FinDist.toMeasure_map _ _ (measurable_of_countable _)]
  rfl

/-- The same decoder transports any finite tuple, including a deleted-player empty tuple. -/
theorem referenceProduct_map_decodeCell {κ : Type*} [Fintype κ]
    (reference : ι → FinDist (Option ℕ)) (p : κ → FinDist (Cell reference)) :
    (Measure.pi (fun j => referenceMeasure reference (p j))).map
        (fun sample j => decodeCell reference (sample j)) = (FinDist.pi p).toMeasure := by
  rw [Measure.pi_map_pi (fun _ => (measurable_decodeCell reference).aemeasurable)]
  simp only [referenceMeasure_map_decodeCell, FinDist.toMeasure_pi]

theorem referenceCellProduct_map_originalChoice {κ : Type*} [Fintype κ]
    (reference : ι → FinDist (Option ℕ)) (p : κ → FinDist (Cell reference)) :
    (FinDist.pi p).map (fun sample j => originalChoice (sample j)) =
      FinDist.pi (fun j => referenceOriginalLaw reference (p j)) :=
  (FinDist.pi_map (fun (_ : κ) (a : Cell reference) => originalChoice a) p).symm

/-- Exact prescribed outcome transport on the old reference calendar for the actual modified
finite laws. The output is the original terminal-outcome type, not just coalition labels. -/
theorem referenceProduct_map_outcome (reference : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell reference)) :
    (Measure.pi (fun i => referenceMeasure reference (p i))).map (chartOutcome reference) =
      ((FinDist.pi (fun i => referenceOriginalLaw reference (p i))).map
        quittingFirstStoppingOutcome).toMeasure := by
  let decode := fun sample : ι → unitInterval => fun i => decodeCell reference (sample i)
  let read := fun sample : ι → Cell reference =>
    quittingFirstStoppingOutcome (fun i => originalChoice (sample i))
  have hdecode : Measurable decode :=
    Measurable.of_eval fun i => (measurable_decodeCell reference).comp (measurable_pi_apply i)
  have hae : chartOutcome reference
      =ᵐ[Measure.pi (fun i => referenceMeasure reference (p i))] read ∘ decode :=
    ae_chartOutcome_eq_originalOutcome_of_absolutelyContinuous reference
      (fun i => referenceMeasure reference (p i))
      (fun i => referenceMeasure_absolutelyContinuous reference (p i))
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_of_countable read) hdecode,
    referenceProduct_map_decodeCell, FinDist.toMeasure_map _ _ (measurable_of_countable read)]
  change ((FinDist.pi p).map
    (quittingFirstStoppingOutcome ∘ (fun sample i => originalChoice (sample i)))).toMeasure = _
  rw [← FinDist.map_comp, referenceCellProduct_map_originalChoice]

theorem referenceProduct_real_none (reference : ι → FinDist (Option ℕ))
    (p : ι → FinDist (Cell reference)) :
    (Measure.pi (fun i => referenceMeasure reference (p i))).real
        {sample | chartOutcome reference sample = none} =
      ((FinDist.pi (fun i => referenceOriginalLaw reference (p i))).map
        quittingFirstStoppingOutcome).prob none := by
  change (Measure.pi (fun i => referenceMeasure reference (p i))).real
    (chartOutcome reference ⁻¹' {none}) = _
  rw [← map_measureReal_apply (measurable_chartOutcome reference)
    (measurableSet_singleton (none : QuittingTerminalOutcome ι)),
    referenceProduct_map_outcome, FinDist.toMeasure_real_singleton]

section Replies

variable [DecidableEq ι]

/-- Every original response is legal here, whether or not its date belongs to the old source
support. The finite-cell law of the opponents and the reference calendar remain unchanged. -/
theorem referenceOpponentProduct_map_responseOutcome
    (reference : ι → FinDist (Option ℕ)) (p : ι → FinDist (Cell reference))
    (who : ι) (choice : Option ℕ) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => referenceMeasure reference (p j.val))).map
        (chartResponseOutcome reference who choice) =
      ((FinDist.pi (fun j : {j : ι // j ≠ who} =>
        referenceOriginalLaw reference (p j.val))).map
        (fun times => quittingFirstStoppingOutcome
          ((Equiv.funSplitAt who (Option ℕ)).symm (choice, times)))).toMeasure := by
  let decode := fun sample : {j : ι // j ≠ who} → unitInterval =>
    fun j => decodeCell reference (sample j)
  let read := fun sample : {j : ι // j ≠ who} → Cell reference =>
    quittingFirstStoppingOutcome ((Equiv.funSplitAt who (Option ℕ)).symm
      (choice, fun j => originalChoice (sample j)))
  have hdecode : Measurable decode :=
    Measurable.of_eval fun j => (measurable_decodeCell reference).comp (measurable_pi_apply j)
  have hae : chartResponseOutcome reference who choice
      =ᵐ[Measure.pi (fun j : {j : ι // j ≠ who} => referenceMeasure reference (p j.val))]
      read ∘ decode :=
    ae_chartResponseOutcome_eq_originalOutcome_of_absolutelyContinuous reference who choice
      (fun j => referenceMeasure reference (p j.val))
      (fun j => referenceMeasure_absolutelyContinuous reference (p j.val))
  rw [Measure.map_congr hae,
    ← Measure.map_map (measurable_of_countable read) hdecode,
    referenceProduct_map_decodeCell,
    FinDist.toMeasure_map _ _ (measurable_of_countable read)]
  change ((FinDist.pi (fun j : {j : ι // j ≠ who} => p j.val)).map
    ((fun times => quittingFirstStoppingOutcome
      ((Equiv.funSplitAt who (Option ℕ)).symm (choice, times))) ∘
        (fun sample j => originalChoice (sample j)))).toMeasure = _
  rw [← FinDist.map_comp, referenceCellProduct_map_originalChoice]

/-- The exact original updated finite-law outcome, including literal Never. -/
theorem referenceOpponentProduct_map_responseOutcome_update
    (reference : ι → FinDist (Option ℕ)) (p : ι → FinDist (Cell reference))
    (who : ι) (choice : Option ℕ) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => referenceMeasure reference (p j.val))).map
        (chartResponseOutcome reference who choice) =
      ((FinDist.pi (Function.update (fun i => referenceOriginalLaw reference (p i))
        who (FinDist.pure choice))).map quittingFirstStoppingOutcome).toMeasure := by
  rw [referenceOpponentProduct_map_responseOutcome, pi_update_pure_eq_map_opponents,
    FinDist.map_comp]
  rfl

theorem referenceOpponentProduct_real_response_none
    (reference : ι → FinDist (Option ℕ)) (p : ι → FinDist (Cell reference))
    (who : ι) (choice : Option ℕ) :
    (Measure.pi (fun j : {j : ι // j ≠ who} => referenceMeasure reference (p j.val))).real
        {sample | chartResponseOutcome reference who choice sample = none} =
      ((FinDist.pi (Function.update (fun i => referenceOriginalLaw reference (p i))
        who (FinDist.pure choice))).map quittingFirstStoppingOutcome).prob none := by
  change (Measure.pi
    (fun j : {j : ι // j ≠ who} => referenceMeasure reference (p j.val))).real
    (chartResponseOutcome reference who choice ⁻¹' {none}) = _
  rw [← map_measureReal_apply (measurable_chartResponseOutcome reference who choice)
    (measurableSet_singleton (none : QuittingTerminalOutcome ι)),
    referenceOpponentProduct_map_responseOutcome_update, FinDist.toMeasure_real_singleton]

end Replies

end GameTheory.MarkedCalendarChart
