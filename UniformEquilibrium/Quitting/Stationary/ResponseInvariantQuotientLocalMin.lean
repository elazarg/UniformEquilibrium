import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient
import UniformEquilibrium.Quitting.Stationary.DiscountedClippedScaling

/-!
# Local minimum field of the stationary-response quotient

The actual quotient clipping field agrees near all-Continue with the
minimum complementarity field. The upper clip is removed by continuity,
while the lower clip remains exact.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- Literal displacement of the quotient clipped map. -/
def quittingQuotientFixedPointField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (point : Fin k → ℝ) : Fin k → ℝ :=
  point - quittingQuotientStationaryClippedMap reward block representative point

/-- The minimum map retaining the original response polynomial. -/
def quittingQuotientMinField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (point : Fin k → ℝ) : Fin k → ℝ :=
  fun coordinate => min (point coordinate)
    (-quittingQuotientResponse reward block representative point coordinate)

theorem quittingQuotientResponse_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    quittingQuotientResponse reward block representative 0 = 0 := by
  funext coordinate
  exact quittingDiscountedDisplacement_zero reward (representative coordinate)

theorem continuous_quittingQuotientResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    Continuous (quittingQuotientResponse reward block representative) := by
  have hlift : Continuous (quittingBlockLift block) := by
    change Continuous (fun point : Fin k → ℝ => fun who => point (block who))
    fun_prop
  apply continuous_pi
  intro coordinate
  exact (continuous_quittingDiscountedDisplacement reward
    (representative coordinate)).comp (continuous_const.prodMk hlift)

/-- Upper clipping is inactive in one ambient neighborhood of all-Continue. -/
theorem eventually_quittingQuotient_upperClip_inactive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι) :
    ∀ᶠ point : Fin k → ℝ in 𝓝 0,
      ∀ coordinate,
        point coordinate + quittingQuotientResponse reward block representative
          point coordinate < 1 := by
  apply Filter.eventually_all.mpr
  intro coordinate
  have hcontinuous : Continuous (fun point : Fin k → ℝ =>
      point coordinate + quittingQuotientResponse reward block representative
        point coordinate) :=
    (continuous_apply coordinate).add
      ((continuous_apply coordinate).comp
        (continuous_quittingQuotientResponse reward block representative))
  have hzero : (0 : Fin k → ℝ) coordinate +
      quittingQuotientResponse reward block representative 0 coordinate = 0 := by
    simp [quittingQuotientResponse_zero]
  have hlt : (fun point : Fin k → ℝ =>
      point coordinate + quittingQuotientResponse reward block representative
        point coordinate) 0 < 1 := by
    simpa only [hzero] using (show (0 : ℝ) < 1 by norm_num)
  exact hcontinuous.continuousAt.eventually (isOpen_Iio.mem_nhds hlt)

/-- On the local upper-clip-inactive set, the actual quotient fixed-point
field is exactly its minimum field on the whole signed ambient chart. -/
theorem quittingQuotientFixedPointField_eq_minField
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (block : ι → Fin k) (representative : Fin k → ι)
    (hrepresentative : ∀ coordinate, block (representative coordinate) = coordinate)
    (point : Fin k → ℝ)
    (hupper : ∀ coordinate,
      point coordinate + quittingQuotientResponse reward block representative
        point coordinate ≤ 1) :
    quittingQuotientFixedPointField reward block representative point =
      quittingQuotientMinField reward block representative point := by
  funext coordinate
  have hsource := quittingDiscountedClippedMap_sub_eq_min reward 0
    (quittingBlockLift block point) (representative coordinate)
      (by simpa [quittingBlockLift, quittingQuotientResponse,
        hrepresentative coordinate] using hupper coordinate)
  simpa [quittingQuotientFixedPointField, quittingQuotientMinField,
    quittingQuotientStationaryClippedMap, quittingQuotientResponse,
    quittingBlockLift, quittingDiscountedClippedMap,
    hrepresentative coordinate] using hsource

end GameTheory
