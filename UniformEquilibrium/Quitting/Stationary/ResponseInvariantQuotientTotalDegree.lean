import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientDegreeEscape
import MathUE.Topology.BoxComplementarityNonzeroSetDegree

/-!
# Entire nonzero stationary quotient degree in the fixed global chart

The exterior selects every nonzero quotient fixed point, including strategy
boundary points and nonisolated families. Its degree is the normalized
integer degree in the explicit `[-2,2]` chart.
-/

noncomputable section

namespace GameTheory

open Set _root_.Math _root_.Math.Topology _root_.Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- All nonzero fixed points of the literal stationary response quotient. -/
def quittingQuotientNonzeroFixedPointSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) : Set (Fin k → ℝ) :=
  {source | source ≠ 0 ∧
    quittingQuotientStationaryClippedMap reward block representative source = source}

/-- Quotient clipping is a self-map of the fixed global signed rectangle. -/
theorem quittingQuotientStationaryClippedMap_mapsTo_globalRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    MapsTo (quittingQuotientStationaryClippedMap reward block representative)
      (Icc (fun _ : Fin k => (-2 : ℝ)) (fun _ => 2))
      (Icc (fun _ : Fin k => (-2 : ℝ)) (fun _ => 2)) := by
  intro source _
  have hcube := quittingQuotientStationaryClippedMap_mem_unitCube
    reward block representative source
  constructor <;> intro coordinate
  · have hzero := hcube.1 coordinate
    change 0 ≤ quittingQuotientStationaryClippedMap reward block representative
      source coordinate at hzero
    change -2 ≤ quittingQuotientStationaryClippedMap reward block representative
      source coordinate
    linarith
  · have hone := hcube.2 coordinate
    change quittingQuotientStationaryClippedMap reward block representative
      source coordinate ≤ 1 at hone
    change quittingQuotientStationaryClippedMap reward block representative
      source coordinate ≤ 2
    linarith

/-- The actual global problem selects exactly quotient fixed points. -/
theorem quittingQuotientGlobalProblem_isSolution_iff_fixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (point : UnitCube (Fin k)) :
    (quittingQuotientGlobalProblem reward block representative).IsSolution point ↔
      quittingQuotientStationaryClippedMap reward block representative
        (quittingQuotientGlobalChart point) = quittingQuotientGlobalChart point := by
  exact (BoxComplementarityProblem.isSolution_of_selfMap_iff
    (fun _ : Fin k => -2) (fun _ => 2) (by intro; norm_num)
    (quittingQuotientStationaryClippedMap reward block representative)
    (continuous_quittingQuotientStationaryClippedMap reward block representative).continuousOn
    (quittingQuotientStationaryClippedMap_mapsTo_globalRectangle
      reward block representative) point).trans eq_comm

/-- The complete nonzero quotient fixed-point set has normalized total degree
`1−κ(A)` in one explicit chart. Neither root finiteness nor regularity is assumed. -/
theorem exists_globalQuotient_entireNonzeroSet_degree_eq_one_sub_r0Degree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hR0 : IsR0Matrix
      (quittingResponseQuotientMatrix reward block representative)) :
    ∃ radius : ℝ, 0 < radius ∧ radius < 1 ∧
      (∀ source : Fin k → ℝ, ‖source‖ ≤ radius →
        quittingQuotientStationaryClippedMap reward block representative source = source →
          source = 0) ∧
      ∃ horigin : (quittingQuotientGlobalProblem reward block representative).IsIsolating
          (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius),
      ∃ houtside : (quittingQuotientGlobalProblem reward block representative).IsIsolating
          (closure (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius))ᶜ,
        (quittingQuotientGlobalProblem reward block representative).localDegree
            (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius) horigin =
          r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 ∧
        (quittingQuotientGlobalProblem reward block representative).solutionsIn
            (closure (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius))ᶜ =
          quittingQuotientGlobalChart ⁻¹'
            quittingQuotientNonzeroFixedPointSet reward block representative ∧
        quittingQuotientGlobalChart ''
            (quittingQuotientGlobalProblem reward block representative).solutionsIn
              (closure (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius))ᶜ =
          quittingQuotientNonzeroFixedPointSet reward block representative ∧
        (quittingQuotientGlobalProblem reward block representative).localDegree
            (closure (quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius))ᶜ houtside =
          1 - r0Degree (quittingResponseQuotientMatrix reward block representative) hR0 := by
  obtain ⟨radius, hradius, hsmall, hisolation, horigin, hdegree⟩ :=
    exists_globalQuotient_originIsolation_localDegree_eq_r0Degree
      reward block representative hrepresentative hR0
  let actual := quittingQuotientGlobalProblem reward block representative
  let region : Set (UnitCube (Fin k)) :=
    quittingQuotientGlobalChart ⁻¹' Metric.ball 0 radius
  have hcover (source : Fin k → ℝ) (_hnonzero : source ≠ 0)
      (hfixed : quittingQuotientStationaryClippedMap reward block representative source =
        source) : ∃ point, quittingQuotientGlobalChart point = source := by
    have hcube := quittingQuotientStationaryClippedMap_mem_unitCube
      reward block representative source
    rw [hfixed] at hcube
    let point : UnitCube (Fin k) := fun coordinate =>
      ⟨(source coordinate + 2) / 4, by
        have hzero := hcube.1 coordinate
        have hone := hcube.2 coordinate
        change 0 ≤ source coordinate at hzero
        change source coordinate ≤ 1 at hone
        constructor <;> linarith⟩
    refine ⟨point, ?_⟩
    funext coordinate
    dsimp [quittingQuotientGlobalChart, rectangularCubePoint, rectangularPoint, point]
    ring
  obtain ⟨hselected, himage, htotal⟩ :=
    actual.entireNonzeroSet_degree_compl_origin quittingQuotientGlobalChart
      (continuous_rectangularCubePoint (fun _ : Fin k => -2) (fun _ => 2))
      (fun source =>
        quittingQuotientStationaryClippedMap reward block representative source = source)
      radius hradius
      (quittingQuotientGlobalProblem_isSolution_iff_fixedPoint reward block representative)
      hisolation hcover horigin
  refine ⟨radius, hradius, hsmall, hisolation, horigin,
    actual.isIsolating_compl_closure region horigin, hdegree, hselected, himage, ?_⟩
  exact htotal.trans (congrArg (fun index : ℤ => 1 - index) hdegree)

end GameTheory
