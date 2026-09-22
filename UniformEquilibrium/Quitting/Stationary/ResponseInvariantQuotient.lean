import UniformEquilibrium.Quitting.Stationary.DiscountedAmbientDerivative
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Raw stationary-response invariant block quotients

The stationary response residual is the zero-discount instance of the
source-owned polynomial displacement. Equality of its individual rows on
the block-constant unit cube forces equality of their raw singleton
matrix row sums within each block.
-/

noncomputable section

namespace GameTheory

open Set QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {k : ℕ}

/-- Repeat each block coordinate at every original player in that block. -/
def quittingBlockLift (block : ι → Fin k) (point : Fin k → ℝ) : ι → ℝ :=
  fun who => point (block who)

/-- The literal raw response-invariance condition on the block-constant
closed unit cube. The residual uses every original reward coordinate. -/
def QuittingResponseInvariantOnUnitCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) : Prop :=
  ∀ point : Fin k → ℝ,
    (∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1) →
      ∀ first second : ι, block first = block second →
        quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) first =
          quittingDiscountedDisplacement reward 0
            (quittingBlockLift block point) second

/-- The singleton matrix row sum over one literal block. -/
def quittingSingletonBlockRowSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (who : ι) (coordinate : Fin k) : ℝ :=
  ∑ player, if block player = coordinate then
    quittingSingletonMatrix reward who player else 0

private def quittingBlockLiftCLM (block : ι → Fin k) :
    (Fin k → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun who => ContinuousLinearMap.proj (block who)

private def quittingBlockPathCLM (block : ι → Fin k) :
    (Fin k → ℝ) →L[ℝ] ℝ × (ι → ℝ) :=
  (ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).comp (quittingBlockLiftCLM block)

omit [Fintype ι] [DecidableEq ι] in
private theorem quittingBlockLiftCLM_apply
    (block : ι → Fin k) (point : Fin k → ℝ) :
    quittingBlockLiftCLM block point = quittingBlockLift block point := by
  funext who
  rfl

private theorem hasFDerivAt_quittingBlockResponse_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (who : ι) :
    HasFDerivAt
      (fun point : Fin k → ℝ =>
        quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) who)
      ((quittingDiscountedSingletonLinearization reward who).comp
        (quittingBlockPathCLM block)) 0 := by
  have hsource := hasFDerivAt_quittingDiscountedDisplacement_zero reward who
  have hpath : HasFDerivAt (quittingBlockPathCLM block)
      (quittingBlockPathCLM block) (0 : Fin k → ℝ) :=
    (quittingBlockPathCLM block).hasFDerivAt
  have hsourceAt : HasFDerivAt
      (fun point : ℝ × (ι → ℝ) =>
        quittingDiscountedDisplacement reward point.1 point.2 who)
      (quittingDiscountedSingletonLinearization reward who)
      (quittingBlockPathCLM block (0 : Fin k → ℝ)) := by
    simpa only [map_zero] using hsource
  have hcomp := hsourceAt.comp 0 hpath
  simpa only [Function.comp_def, quittingBlockPathCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    quittingBlockLiftCLM_apply] using hcomp

omit [DecidableEq ι] in
private theorem quittingBlockResponseLinearization_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (who : ι) (point : Fin k → ℝ) :
    ((quittingDiscountedSingletonLinearization reward who).comp
        (quittingBlockPathCLM block)) point =
      -∑ player, point (block player) * quittingSingletonMatrix reward who player := by
  rw [ContinuousLinearMap.comp_apply,
    quittingDiscountedSingletonLinearization_apply]
  simp only [quittingBlockPathCLM, quittingBlockLiftCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, zero_mul,
    zero_sub]

omit [DecidableEq ι] in
private theorem quittingBlockRowSum_eq_basis_linearization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (who : ι) (coordinate : Fin k) :
    (∑ player, (Pi.single coordinate (1 : ℝ) : Fin k → ℝ) (block player) *
      quittingSingletonMatrix reward who player) =
        quittingSingletonBlockRowSum reward block who coordinate := by
  unfold quittingSingletonBlockRowSum
  apply Finset.sum_congr rfl
  intro player _
  by_cases hplayer : block player = coordinate
  · simp [hplayer]
  · simp [hplayer]

/-- Literal response invariance on the unit cube makes the singleton
matrix row sum independent of the player chosen within a block. -/
theorem quittingSingletonBlockRowSum_eq_of_responseInvariant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (first second : ι) (hblock : block first = block second)
    (coordinate : Fin k) :
    quittingSingletonBlockRowSum reward block first coordinate =
      quittingSingletonBlockRowSum reward block second coordinate := by
  let cube : Set (Fin k → ℝ) := univ.pi fun _ => Icc (0 : ℝ) 1
  have hunique : UniqueDiffWithinAt ℝ cube (0 : Fin k → ℝ) :=
    UniqueDiffWithinAt.univ_pi fun _ => uniqueDiffOn_Icc_zero_one 0 (by simp)
  let firstResponse := fun point : Fin k → ℝ =>
    quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) first
  let secondResponse := fun point : Fin k → ℝ =>
    quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) second
  have heqOn : EqOn firstResponse secondResponse cube := by
    intro point hpoint
    exact hresponse point (fun coordinate => hpoint coordinate (mem_univ _))
      first second hblock
  have hzero : firstResponse 0 = secondResponse 0 :=
    hresponse 0 (by intro coordinate; simp) first second hblock
  have hfirst : HasFDerivWithinAt firstResponse
      ((quittingDiscountedSingletonLinearization reward first).comp
        (quittingBlockPathCLM block)) cube 0 :=
    (hasFDerivAt_quittingBlockResponse_zero reward block first).hasFDerivWithinAt
  have hsecondOn : HasFDerivWithinAt secondResponse
      ((quittingDiscountedSingletonLinearization reward second).comp
        (quittingBlockPathCLM block)) cube 0 :=
    (hasFDerivAt_quittingBlockResponse_zero reward block second).hasFDerivWithinAt
  have hsecond : HasFDerivWithinAt firstResponse
      ((quittingDiscountedSingletonLinearization reward second).comp
        (quittingBlockPathCLM block)) cube 0 :=
    hsecondOn.congr heqOn hzero
  have hlinear := hunique.eq hfirst hsecond
  have hb := congrArg (fun linear : (Fin k → ℝ) →L[ℝ] ℝ =>
    linear (Pi.single coordinate (1 : ℝ) : Fin k → ℝ)) hlinear
  rw [quittingBlockResponseLinearization_apply,
    quittingBlockResponseLinearization_apply,
    neg_inj,
    quittingBlockRowSum_eq_basis_linearization,
    quittingBlockRowSum_eq_basis_linearization] at hb
  exact hb

/-- Choose one original player in each block and use the literal singleton
matrix row sums. These are sums, including the diagonal block. -/
def quittingResponseQuotientMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun row coordinate =>
    quittingSingletonBlockRowSum reward block (representative row) coordinate

omit [DecidableEq ι] in
private theorem sum_mul_blockLift_eq_sum_rowSum
    (block : ι → Fin k) (row : ι → ℝ) (point : Fin k → ℝ) :
    (∑ player, row player * point (block player)) =
      ∑ coordinate, (∑ player, if block player = coordinate then row player else 0) *
        point coordinate := by
  calc
    (∑ player, row player * point (block player)) =
        ∑ player, ∑ coordinate,
          if block player = coordinate then row player * point coordinate else 0 := by
      apply Finset.sum_congr rfl
      intro player _
      simp
    _ = ∑ coordinate, ∑ player,
          if block player = coordinate then row player * point coordinate else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ coordinate,
          (∑ player, if block player = coordinate then row player else 0) *
            point coordinate := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro player _
      by_cases hplayer : block player = coordinate <;> simp [hplayer]

/-- Raw response invariance makes the quotient matrix intertwine the
original singleton matrix with the block lift: `Γ E = E A`. -/
theorem quittingSingletonMatrix_mulVec_blockLift_eq_quotient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (hresponse : QuittingResponseInvariantOnUnitCube reward block)
    (point : Fin k → ℝ) :
    (quittingSingletonMatrix reward).mulVec (quittingBlockLift block point) =
      quittingBlockLift block
        ((quittingResponseQuotientMatrix reward block representative).mulVec point) := by
  funext who
  change (∑ player, quittingSingletonMatrix reward who player * point (block player)) =
    ∑ coordinate,
      quittingResponseQuotientMatrix reward block representative (block who) coordinate *
        point coordinate
  rw [sum_mul_blockLift_eq_sum_rowSum]
  apply Finset.sum_congr rfl
  intro coordinate _
  congr 1
  exact quittingSingletonBlockRowSum_eq_of_responseInvariant reward block hresponse
    who (representative (block who)) (hrepresentative (block who)).symm coordinate

/-- The literal quotient of the stationary residual map, clipped in each
block coordinate on the whole ambient space. A fixed point is automatically
in the quotient strategy cube. -/
def quittingQuotientStationaryClippedMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (point : Fin k → ℝ) : Fin k → ℝ :=
  fun coordinate => min 1 (max 0
    (point coordinate + quittingDiscountedDisplacement reward 0
      (quittingBlockLift block point) (representative coordinate)))

/-- The actual quotient clipped map is continuous in ambient real hazards. -/
theorem continuous_quittingQuotientStationaryClippedMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    Continuous (quittingQuotientStationaryClippedMap reward block representative) := by
  have hpath : Continuous fun point : Fin k → ℝ =>
      ((0 : ℝ), quittingBlockLift block point) := by
    have hlift : Continuous (quittingBlockLiftCLM block) :=
      (quittingBlockLiftCLM block).continuous
    simpa only [quittingBlockLiftCLM_apply] using continuous_const.prodMk hlift
  apply continuous_pi
  intro coordinate
  exact continuous_const.min (continuous_const.max
    ((continuous_apply coordinate).add
      ((continuous_quittingDiscountedDisplacement reward
        (representative coordinate)).comp hpath)))

/-- The quotient clipping map has image in the closed unit cube. -/
theorem quittingQuotientStationaryClippedMap_mem_unitCube
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (point : Fin k → ℝ) :
    quittingQuotientStationaryClippedMap reward block representative point ∈
      Icc (0 : Fin k → ℝ) 1 := by
  constructor <;> intro coordinate
  · exact le_min (by norm_num) (le_max_left _ _)
  · exact min_le_left _ _

/-- Coordinatewise fixed-point signs of the literal quotient response map.
The unit-cube premises describe the queried point; they do not assert a root. -/
theorem quittingQuotientStationaryClippedMap_eq_self_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (point : Fin k → ℝ)
    (hzero : ∀ coordinate, 0 ≤ point coordinate)
    (hone : ∀ coordinate, point coordinate ≤ 1) :
    quittingQuotientStationaryClippedMap reward block representative point = point ↔
      ∀ coordinate,
        (point coordinate = 0 →
          quittingDiscountedDisplacement reward 0 (quittingBlockLift block point)
            (representative coordinate) ≤ 0) ∧
        (0 < point coordinate → point coordinate < 1 →
          quittingDiscountedDisplacement reward 0 (quittingBlockLift block point)
            (representative coordinate) = 0) ∧
        (point coordinate = 1 →
          0 ≤ quittingDiscountedDisplacement reward 0 (quittingBlockLift block point)
            (representative coordinate)) := by
  rw [funext_iff]
  exact forall_congr' fun coordinate =>
    Math.UnitIntervalClip.clipped_unitInterval_add_eq_self_iff
      (hzero coordinate) (hone coordinate)

end GameTheory
