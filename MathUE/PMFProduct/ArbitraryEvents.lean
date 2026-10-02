import MathUE.PMFProduct.Conditioning
import MathUE.ProbabilityMassFunction.ConditioningTotalVariation

/-! # Coordinate events for finite products of arbitrary discrete laws

The number of independent factors is finite. Their sample types need not be
finite, so these formulas apply directly to complete stopping clocks.
-/

noncomputable section

namespace Math.ProbabilityMassFunction

open Math.Probability

theorem pmfMass_singleton {Ω : Type*} (law : PMF Ω) (point : Ω) :
    pmfMass law (fun other => other = point) = law point := by
  classical
  unfold pmfMass
  rw [tsum_eq_single point]
  · simp [pmfMask]
  · intro other hother
    simp [pmfMask, hother]

open Classical in
theorem expect_indicator_eq_pmfMass_toReal {Ω : Type*}
    (law : PMF Ω) (event : Ω → Prop) :
    expect law (fun point => if event point then 1 else 0) =
      (pmfMass law event).toReal := by
  classical
  rw [pmfMass_toReal_eq_tsum_mask]
  unfold expect
  apply tsum_congr
  intro point
  by_cases hpoint : event point <;> simp [hpoint]

/-- A local bound need only hold on the law's support. -/
theorem abs_expect_sub_le_mul_pmfMass_of_support {Ω : Type*}
    (law : PMF Ω) (left right : Ω → ℝ) (event : Set Ω)
    {bound observableBound : ℝ} (hbound : 0 ≤ bound)
    (hleft : ∀ point, |left point| ≤ observableBound)
    (hright : ∀ point, |right point| ≤ observableBound)
    (hlocal : ∀ point, law point ≠ 0 →
      |left point - right point| ≤ bound * event.indicator (fun _ => 1) point) :
    |expect law left - expect law right| ≤
      bound * (pmfMass law fun point => point ∈ event).toReal := by
  classical
  let masked := fun point => if law point ≠ 0 then left point else right point
  have hmasked : expect law left = expect law masked := by
    apply expect_congr_of_ne_zero
    intro point hpoint
    simp [masked, hpoint]
  rw [hmasked]
  apply abs_expect_sub_le_mul_pmfMass law masked right event
    (bound := bound) (observableBound := observableBound)
  · intro point
    by_cases hpoint : law point = 0
    · simpa [masked, hpoint] using hright point
    · simpa [masked, hpoint] using hleft point
  · exact hright
  · intro point
    by_cases hpoint : law point ≠ 0
    · simpa [masked, hpoint] using hlocal point hpoint
    · simp only [masked, hpoint, ite_false, sub_self, abs_zero]
      apply mul_nonneg hbound
      by_cases hevent : point ∈ event <;> simp [hevent]

end Math.ProbabilityMassFunction

namespace Math.PMFProduct

open Math.ProbabilityMassFunction

theorem pmfMass_pmfPi_coord_arbitrary {ι Ω : Type*} [Fintype ι]
    (laws : ι → PMF Ω) (coordinate : ι) (event : Ω → Prop) :
    pmfMass (pmfPi laws) (fun times => event (times coordinate)) =
      pmfMass (laws coordinate) event := by
  classical
  have hevent : (fun times : ι → Ω => event (times coordinate)) =
      (fun times : ι → Ω =>
        ∀ other, if other = coordinate then event (times other) else True) := by
    funext times
    apply propext
    constructor
    · intro h other
      by_cases hother : other = coordinate <;> simp [hother, h]
    · intro h
      simpa using h coordinate
  rw [hevent]
  let events : ι → Ω → Prop := fun other time =>
    if other = coordinate then event time else True
  change pmfMass (pmfPi laws) (fun times => ∀ other, events other (times other)) = _
  rw [pmfMass_pmfPi_forall]
  dsimp only [events]
  have hfactor : ∀ other,
      pmfMass (laws other) (fun time =>
          if other = coordinate then event time else True) =
        if other = coordinate then pmfMass (laws coordinate) event else 1 := by
    intro other
    by_cases hother : other = coordinate <;> simp [hother, pmfMass_true]
  simp_rw [hfactor]
  simp

theorem pmfMass_pmfPi_pair_arbitrary {ι Ω : Type*} [Fintype ι]
    (laws : ι → PMF Ω) (first second : ι) (hdifferent : first ≠ second)
    (firstEvent secondEvent : Ω → Prop) :
    pmfMass (pmfPi laws) (fun times =>
      firstEvent (times first) ∧ secondEvent (times second)) =
      pmfMass (laws first) firstEvent * pmfMass (laws second) secondEvent := by
  classical
  have hevent :
      (fun times : ι → Ω => firstEvent (times first) ∧ secondEvent (times second)) =
      (fun times : ι → Ω => ∀ other,
        if other = first then firstEvent (times other)
        else if other = second then secondEvent (times other) else True) := by
    funext times
    apply propext
    constructor
    · rintro ⟨hfirst, hsecond⟩ other
      by_cases hotherFirst : other = first
      · simpa [hotherFirst] using hfirst
      · by_cases hotherSecond : other = second
        · simpa [hotherSecond, Ne.symm hdifferent] using hsecond
        · simp [hotherFirst, hotherSecond]
    · intro h
      exact ⟨by simpa using h first, by simpa [Ne.symm hdifferent] using h second⟩
  rw [hevent]
  let events : ι → Ω → Prop := fun other time =>
    if other = first then firstEvent time
    else if other = second then secondEvent time else True
  change pmfMass (pmfPi laws) (fun times => ∀ other, events other (times other)) = _
  rw [pmfMass_pmfPi_forall]
  dsimp only [events]
  have hfactor : ∀ other,
      pmfMass (laws other) (fun time =>
        if other = first then firstEvent time
        else if other = second then secondEvent time else True) =
        (if other = first then pmfMass (laws first) firstEvent else 1) *
        (if other = second then pmfMass (laws second) secondEvent else 1) := by
    intro other
    by_cases hotherFirst : other = first
    · simp [hotherFirst, hdifferent]
    · by_cases hotherSecond : other = second
      · subst other
        simp [Ne.symm hdifferent]
      · simp [hotherFirst, hotherSecond, pmfMass_true]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp

theorem pmfPi_coordinate_ne_zero {ι Ω : Type*} [Fintype ι]
    (laws : ι → PMF Ω) (times : ι → Ω) (coordinate : ι)
    (htimes : pmfPi laws times ≠ 0) : laws coordinate (times coordinate) ≠ 0 := by
  classical
  rw [pmfPi_apply] at htimes
  exact (Finset.prod_ne_zero_iff.mp htimes) coordinate (Finset.mem_univ coordinate)

end Math.PMFProduct
