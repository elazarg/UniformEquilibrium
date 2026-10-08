import Mathlib.Probability.Process.FiniteDimensionalLaws
import UniformEquilibrium.Certificates.Public.FixedPrefixAccounting
import UniformEquilibrium.Certificates.Public.TerminalChildLawTransfer
import UniformEquilibrium.ProofView.Concepts.Stochastic.Core.Probability.InfinitePlayMeasure

/-!
# Actual infinite-play law after a completed public history

Restricting an actual infinite-play law to one completed history and dropping
that history produces the rebased profile's law multiplied by the history's
actual probability. The current action is freshly drawn, not conditioned on.
The identity includes zero-probability histories and arbitrary full-history
behavior profiles. It does not assert a random first-arrival decomposition.
-/

noncomputable section

namespace GameTheory.StochasticGame

open MeasureTheory ProbabilityTheory

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]

private def coordinateWindow (length time : ℕ)
    (coords : (index : Finset.Iic (length + time)) → G.StageOutcome) :
    (index : Finset.Iic time) → G.StageOutcome :=
  fun index => coords ⟨length + index.1,
    Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp index.2) length)⟩

private def completedCoordinatePrefix (length time : ℕ)
    (coords : (index : Finset.Iic (length + time)) → G.StageOutcome) : G.Hist length :=
  G.histOfIic length fun index => coords ⟨index.1,
    Finset.mem_Iic.mpr ((Finset.mem_Iic.mp index.2).trans (Nat.le_add_right length time))⟩

omit [Fintype ι] in
private theorem coordinateWindow_reconstruct_append {length time : ℕ}
    (base : G.Hist length) (suffix : G.Hist time) (action : G.JointAct) :
    coordinateWindow G length time
        (G.reconstructCoords (length + time) (G.appendHist base suffix) action) =
      G.reconstructCoords time suffix action := by
  funext index
  by_cases hindex : index.1 < time
  · have hfull : length + index.1 < length + time := Nat.add_lt_add_left hindex length
    have hfin : (⟨length + index.1, hfull⟩ : Fin (length + time)) =
        Fin.natAdd length ⟨index.1, hindex⟩ := rfl
    simp only [coordinateWindow, reconstructCoords, hfull, hindex, ↓reduceDIte,
      appendHist, hfin, Fin.append_right]
  · have hfull : ¬length + index.1 < length + time := by omega
    simp only [coordinateWindow, reconstructCoords, hfull, hindex, ↓reduceDIte,
      appendHist_snd]

omit [Fintype ι] in
private theorem completedCoordinatePrefix_reconstruct {length time : ℕ}
    (history : G.Hist (length + time)) (action : G.JointAct) :
    completedCoordinatePrefix G length time (G.reconstructCoords (length + time) history action) =
      G.terminalPrefix history := by
  apply Prod.ext
  · funext index
    have hindex : index.1 < length + time :=
      lt_of_lt_of_le index.2 (Nat.le_add_right length time)
    simp only [completedCoordinatePrefix, histOfIic, reconstructCoords, hindex,
      ↓reduceDIte, terminalPrefix]
    rfl
  · cases time with
    | zero =>
        simp only [completedCoordinatePrefix, histOfIic, reconstructCoords, Nat.add_zero,
          lt_self_iff_false, ↓reduceDIte, terminalPrefix]
    | succ time =>
        have hindex : length < length + (time + 1) := by omega
        simp only [completedCoordinatePrefix, histOfIic, reconstructCoords, hindex,
          ↓reduceDIte, terminalPrefix]
        rfl

private def coordinateLawAfter (profile : G.BehaviorProfile) {length : ℕ}
    (base : G.Hist length) (time : ℕ) :
    PMF ((index : Finset.Iic (length + time)) → G.StageOutcome) :=
  (G.histDistAfter profile base time).bind fun history =>
    (G.stageActionDist profile history).map (G.reconstructCoords (length + time) history)

private theorem coordsDist_add_eq_bind_coordinateLawAfter
    (profile : G.BehaviorProfile) (initial : G.State) (length time : ℕ) :
    G.coordsDist profile initial (length + time) =
      (G.histDist profile initial length).bind
        (fun base => coordinateLawAfter G profile base time) := by
  rw [G.coordsDist_eq_histDist_bind, G.histDist_add_eq_bind_histDistAfter, PMF.bind_bind]
  rfl

private theorem coordinateLawAfter_map_window (profile : G.BehaviorProfile) {length : ℕ}
    (base : G.Hist length) (time : ℕ) :
    (coordinateLawAfter G profile base time).map (coordinateWindow G length time) =
      G.coordsDist (G.afterHistoryProfile profile base) base.2 time := by
  unfold coordinateLawAfter histDistAfter
  rw [PMF.bind_map, PMF.map_bind, G.coordsDist_eq_histDist_bind]
  apply congrArg
  funext suffix
  change ((G.stageActionDist profile (G.appendHist base suffix)).map
    (G.reconstructCoords (length + time) (G.appendHist base suffix))).map
      (coordinateWindow G length time) =
    (G.stageActionDist (G.afterHistoryProfile profile base) suffix).map
      (G.reconstructCoords time suffix)
  rw [PMF.map_comp]
  have hfunction :
      coordinateWindow G length time ∘
          G.reconstructCoords (length + time) (G.appendHist base suffix) =
        G.reconstructCoords time suffix := by
    funext action
    exact coordinateWindow_reconstruct_append G base suffix action
  rw [hfunction, G.stageActionDist_afterHistoryProfile]

private theorem coordinateLawAfter_prefix_of_support (profile : G.BehaviorProfile) {length : ℕ}
    (base : G.Hist length) (time : ℕ)
    (coords : (index : Finset.Iic (length + time)) → G.StageOutcome)
    (hsupport : coords ∈ (coordinateLawAfter G profile base time).support) :
    completedCoordinatePrefix G length time coords = base := by
  rw [coordinateLawAfter, PMF.mem_support_bind_iff] at hsupport
  obtain ⟨history, hhistory, hcoords⟩ := hsupport
  obtain ⟨action, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hcoords
  rw [completedCoordinatePrefix_reconstruct]
  rw [histDistAfter] at hhistory
  obtain ⟨suffix, hsuffix, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hhistory
  exact G.terminalPrefix_appendHist base suffix
    (G.startsAt_of_mem_support_histDist (G.afterHistoryProfile profile base) base.2
      time suffix hsuffix)

section CountableLaws

variable [Countable G.State] [∀ who, Countable (G.Act who)]

private theorem coordinateLawAfter_ae_prefix (profile : G.BehaviorProfile) {length : ℕ}
    (base : G.Hist length) (time : ℕ) :
    ∀ᵐ coords ∂(coordinateLawAfter G profile base time).toMeasure,
      completedCoordinatePrefix G length time coords = base := by
  rw [ae_iff]
  apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete).mpr
  refine Set.disjoint_left.mpr ?_
  intro coords hcoords hnot
  exact hnot (coordinateLawAfter_prefix_of_support G profile base time coords hcoords)

private theorem restricted_coordsDist_map_window
    (profile : G.BehaviorProfile) (initial : G.State) {length : ℕ}
    (base : G.Hist length) (time : ℕ) :
    ((G.coordsDist profile initial (length + time)).toMeasure.restrict
        {coords | completedCoordinatePrefix G length time coords = base}).map
          (coordinateWindow G length time) =
      G.histDist profile initial length base •
        (G.coordsDist (G.afterHistoryProfile profile base) base.2 time).toMeasure := by
  classical
  ext set hset
  rw [Measure.map_apply Measurable.of_discrete hset,
    Measure.restrict_apply (Measurable.of_discrete hset),
    coordsDist_add_eq_bind_coordinateLawAfter, PMF.toMeasure_bind_apply
      (G.histDist profile initial length) (fun other => coordinateLawAfter G profile other time)
      _ ((Measurable.of_discrete hset).inter MeasurableSet.of_discrete), Measure.smul_apply,
    smul_eq_mul]
  have hterm (other : G.Hist length) :
      (coordinateLawAfter G profile other time).toMeasure
          ((coordinateWindow G length time) ⁻¹' set ∩
            {coords | completedCoordinatePrefix G length time coords = base}) =
        if other = base then
          (G.coordsDist (G.afterHistoryProfile profile base) base.2 time).toMeasure set
        else 0 := by
    by_cases hother : other = base
    · subst other
      rw [ite_eq_left rfl]
      have hevent := coordinateLawAfter_ae_prefix G profile base time
      have heq :
          ((coordinateWindow G length time) ⁻¹' set ∩
              {coords | completedCoordinatePrefix G length time coords = base}) =ᵐ[
                (coordinateLawAfter G profile base time).toMeasure]
            (coordinateWindow G length time) ⁻¹' set := by
        filter_upwards [hevent] with coords hcoords
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hcoords, and_true]
      rw [measure_congr heq]
      rw [← PMF.toMeasure_map_apply _ _ _ Measurable.of_discrete hset,
        coordinateLawAfter_map_window]
    · rw [ite_eq_right hother]
      apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete).mpr
      refine Set.disjoint_left.mpr ?_
      intro coords hcoords hsetCoords
      exact hother ((coordinateLawAfter_prefix_of_support G profile other time coords
        hcoords).symm.trans hsetCoords.2)
  simp only [hterm, mul_ite, mul_zero, tsum_ite_eq]

/-- A completed-history restriction restarts the actual full-profile law, including zero mass. -/
theorem infinitePlayMeasure_restrict_histOfPlay_map_suffix
    (profile : G.BehaviorProfile) (initial : G.State) {length : ℕ}
    (base : G.Hist length) :
    ((G.infinitePlayMeasure profile initial).restrict
        {play | G.histOfPlay length play = base}).map (fun play time => play (length + time)) =
      G.histDist profile initial length base •
        G.infinitePlayMeasure (G.afterHistoryProfile profile base) base.2 := by
  let left : Measure G.Play :=
    ((G.infinitePlayMeasure profile initial).restrict
      {play | G.histOfPlay length play = base}).map (fun play time => play (length + time))
  let right : Measure G.Play := G.histDist profile initial length base •
    G.infinitePlayMeasure (G.afterHistoryProfile profile base) base.2
  have hprojection (time : ℕ) :
      left.map (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time) =
        ((G.coordsDist profile initial (length + time)).toMeasure.restrict
          {coords | completedCoordinatePrefix G length time coords = base}).map
            (coordinateWindow G length time) := by
    rw [← G.map_frestrictLe_infinitePlayMeasure profile initial (length + time),
      Measure.restrict_map
        (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) (length + time))
        MeasurableSet.of_discrete,
      Measure.map_map Measurable.of_discrete
        (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) (length + time))]
    dsimp only [left]
    rw [Measure.map_map (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) time)
      (Measurable.of_eval fun index => measurable_pi_apply (length + index))]
    rfl
  let family (indices : Finset ℕ) : Measure ((index : indices) → G.StageOutcome) :=
    left.map indices.restrict
  have hfamily : IsProjectiveMeasureFamily (α := fun _ : ℕ => G.StageOutcome) family :=
    ProbabilityTheory.isProjectiveMeasureFamily_map_restrict
      (P := left) (X := fun time (play : G.Play) => play time)
      (fun time => (measurable_pi_apply time).aemeasurable)
  let (indices : Finset ℕ) : IsFiniteMeasure (family indices) := by
    dsimp [family, left]
    infer_instance
  have hleft : IsProjectiveLimit left family := fun _ => rfl
  have hright : IsProjectiveLimit right family := by
    apply (isProjectiveLimit_nat_iff hfamily _).mpr
    intro time
    change right.map (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time) =
      left.map (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) time)
    rw [hprojection, restricted_coordsDist_map_window]
    dsimp only [right]
    rw [Measure.map_smul _
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) time).aemeasurable,
      G.map_frestrictLe_infinitePlayMeasure]
  exact hleft.unique hright

end CountableLaws

end GameTheory.StochasticGame
