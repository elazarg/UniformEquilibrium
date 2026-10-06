import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import MathUE.Interval.UnitIntervalClip
import MathUE.Topology.BoxComplementarityProblem
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Full polynomial endpoint gains and literal clipping

The full coalition-cube coordinate derivative extends the exact endpoint
gap to arbitrary real hazards. Its clipping fixed points are precisely actual
exact roots, including zero, simultaneous, and sure hazards. No selected root,
local Jacobian, degree, or restricted active-face replacement is supplied.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The existing full multilinear cube, differentiated in each player's own
coordinate, supplies the real-hazard endpoint polynomial. -/
def quittingRealHazardEndpointGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hazard : ι → ℝ) : ι → ℝ :=
  fun player => (quittingStageCenteredCoalGame reward tail player).coordinateDerivative
    hazard player

theorem quittingRealHazardEndpointGap_hazardOfRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (player : ι) :
    quittingRealHazardEndpointGap reward tail (hazardOfRoot root) player =
      quittingRootEndpointDifference reward tail root player :=
  (quittingRootEndpointDifference_eq_mobiusCoordinateDerivative reward tail root player).symm

/-- Every full gap is smooth as a polynomial on all real hazards. This does
not assert global differentiability of the clipped map. -/
theorem contDiff_quittingRealHazardEndpointGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (order : WithTop ℕ∞) (player : ι) :
    ContDiff ℝ order (fun hazard => quittingRealHazardEndpointGap reward tail hazard player) := by
  unfold quittingRealHazardEndpointGap CoalGame.coordinateDerivative
  apply ContDiff.sum
  intro coalition _
  by_cases hplayer : player ∈ coalition
  · simp only [hplayer, ite_true]
    apply contDiff_const.mul
    apply contDiff_prod
    intro who _
    exact contDiff_apply ℝ ℝ who
  · simp only [hplayer, ite_false]
    exact contDiff_const

theorem continuous_quittingRealHazardEndpointGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    Continuous (quittingRealHazardEndpointGap reward tail) :=
  continuous_pi fun player =>
    (contDiff_quittingRealHazardEndpointGap reward tail 0 player).continuous

/-- The literal full clipping map is defined even at signed ambient hazards. -/
def quittingFullClippedEndpointMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hazard : ι → ℝ) : ι → ℝ :=
  fun player => min 1 (max 0
    (hazard player + quittingRealHazardEndpointGap reward tail hazard player))

theorem continuous_quittingFullClippedEndpointMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    Continuous (quittingFullClippedEndpointMap reward tail) := by
  apply continuous_pi
  intro player
  have hgap : Continuous (fun hazard : ι → ℝ =>
      quittingRealHazardEndpointGap reward tail hazard player) :=
    (contDiff_quittingRealHazardEndpointGap reward tail 0 player).continuous
  exact continuous_const.min (continuous_const.max
    ((continuous_apply player).add hgap))

/-- Clipping maps every ambient real vector into the closed probability cube. -/
theorem quittingFullClippedEndpointMap_mem_unitCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) (hazard : ι → ℝ) :
    quittingFullClippedEndpointMap reward tail hazard ∈ Icc (fun _ => 0) (fun _ => 1) := by
  constructor
  · intro player
    exact le_min zero_le_one (le_max_left _ _)
  · intro player
    exact min_le_left _ _

/-- The scalar clipping theorem supplies both played-action comparisons on
the entire closed cube, not just interior indifference. -/
theorem quittingFullClippedEndpointMap_eq_self_iff_complementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hone : ∀ player, hazard player ≤ 1) :
    quittingFullClippedEndpointMap reward tail hazard = hazard ↔
      IsExactRowComplementary hazard (quittingRealHazardEndpointGap reward tail hazard) := by
  rw [funext_iff]
  apply forall_congr'
  intro player
  change min 1 (max 0 (hazard player +
    quittingRealHazardEndpointGap reward tail hazard player)) = hazard player ↔ _
  rw [Math.UnitIntervalClip.clipped_unitInterval_add_eq_self_iff
    (hzero player) (hone player)]
  constructor
  · rintro ⟨hatZero, hmiddle, hatOne⟩
    constructor
    · intro hpositive
      by_cases hfull : hazard player = 1
      · exact hatOne hfull
      · exact (hmiddle hpositive (lt_of_le_of_ne (hone player) hfull)).ge
    · intro hbelow
      by_cases hempty : hazard player = 0
      · exact hatZero hempty
      · exact (hmiddle (lt_of_le_of_ne (hzero player) (Ne.symm hempty)) hbelow).le
  · rintro ⟨hpositive, hbelow⟩
    refine ⟨fun h => hbelow (by rw [h]; norm_num), ?_,
      fun h => hpositive (by rw [h]; norm_num)⟩
    exact fun hpos hlt => le_antisymm (hbelow hlt) (hpositive hpos)

/-- Every literal product root is exact Nash exactly when its full clipped
hazard vector is fixed. Inactive and sure-quit endpoint inequalities remain. -/
theorem quittingFullClippedEndpointMap_hazardOfRoot_eq_self_iff_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) :
    quittingFullClippedEndpointMap reward tail (hazardOfRoot root) = hazardOfRoot root ↔
      IsεQuittingRootNash reward tail 0 root := by
  rw [quittingFullClippedEndpointMap_eq_self_iff_complementary reward tail _
    (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root)]
  have hgap : quittingRealHazardEndpointGap reward tail (hazardOfRoot root) =
      fun player => gainValue (weightOfReward reward) (hazardOfRoot root) player
        (tail player) := by
    funext player
    rw [quittingRealHazardEndpointGap_hazardOfRoot,
      quittingRootEndpointDifference_eq_gainValue]
  rw [hgap]
  exact (isExactRowComplementary_hazardOfRoot_iff reward tail root).trans
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root)

/-- Conversely, every fixed hazard in the cube has its actual coin-family
exact root; the endpoint bridge is not limited to preselected PMF roots. -/
theorem quittingFullClippedEndpointMap_eq_self_iff_isZeroNash_rootOfHazard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hone : ∀ player, hazard player ≤ 1) :
    quittingFullClippedEndpointMap reward tail hazard = hazard ↔
      IsεQuittingRootNash reward tail 0 (rootOfHazard hazard hzero hone) := by
  simpa only [hazardOfRoot_rootOfHazard] using
    quittingFullClippedEndpointMap_hazardOfRoot_eq_self_iff_isZeroNash reward tail
      (rootOfHazard hazard hzero hone)

/-- The actual full endpoint field as a continuous cube-complementarity
problem, ready for the canonical degree implementation. -/
def quittingFullEndpointProblem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    Math.BoxComplementarityProblem ι where
  gain point := quittingRealHazardEndpointGap reward tail (fun player => (point player : ℝ))
  continuous_gain player := by
    have hgap : Continuous (fun hazard : ι → ℝ =>
        quittingRealHazardEndpointGap reward tail hazard player) :=
      (contDiff_quittingRealHazardEndpointGap reward tail 0 player).continuous
    exact hgap.comp (continuous_pi fun who => (continuous_apply who).subtype_val)

theorem quittingFullEndpointProblem_isSolution_iff_clippedFixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (point : Math.UnitCube ι) :
    (quittingFullEndpointProblem reward tail).IsSolution point ↔
      quittingFullClippedEndpointMap reward tail (fun player => (point player : ℝ)) =
        (fun player => (point player : ℝ)) := by
  rw [funext_iff]
  apply forall_congr'
  intro player
  change ((_ = 0 → _ ≤ 0) ∧ (_ = 1 → 0 ≤ _) ∧ (0 < _ → _ < 1 → _ = 0)) ↔
    min 1 (max 0 ((point player : ℝ) +
      quittingRealHazardEndpointGap reward tail (fun who => (point who : ℝ)) player)) = _
  rw [Math.UnitIntervalClip.clipped_unitInterval_add_eq_self_iff
    (point player).property.1 (point player).property.2]
  dsimp only [quittingFullEndpointProblem]
  tauto

theorem quittingFullEndpointProblem_isSolution_iff_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (point : Math.UnitCube ι) :
    (quittingFullEndpointProblem reward tail).IsSolution point ↔
      IsεQuittingRootNash reward tail 0
        (rootOfHazard (fun player => (point player : ℝ))
          (fun player => (point player).property.1) (fun player => (point player).property.2)) :=
  (quittingFullEndpointProblem_isSolution_iff_clippedFixedPoint reward tail point).trans
    (quittingFullClippedEndpointMap_eq_self_iff_isZeroNash_rootOfHazard reward tail _
      (fun player => (point player).property.1) (fun player => (point player).property.2))

end GameTheory
