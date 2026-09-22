import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseEscape
import UniformEquilibrium.Quitting.Circulation.SingletonFaceCirculation
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientBellman
import UniformEquilibrium.Quitting.Stationary.HeterogeneousConstrainedFaceNash

/-! # Guard transport from the crossed auxiliary map to original players -/

noncomputable section

namespace GameTheory

open Set Math.LinearProgramming

variable {n : ℕ}

/-- An outsider is active at the literal hazard row. -/
def quittingCrossedOutsiderPositive
    (first second : Fin n) (hazard : Fin n → ℝ) : Prop :=
  ∃ outsider, outsider ≠ first ∧ outsider ≠ second ∧ 0 < hazard outsider

/-- The outsider coordinates `J = I \ {first, second}` in the source guard. -/
abbrev QuittingCrossedOutsider (first second : Fin n) :=
  {coordinate : Fin n // coordinate ≠ first ∧ coordinate ≠ second}

/-- A literal source-face row, with both selected coordinates displayed and
the remaining coordinates supplied by `z : [0,1]^J`. -/
def quittingCrossedGuardRow (first second : Fin n)
    (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ) : Fin n → ℝ :=
  fun coordinate =>
    if hfirst : coordinate = first then firstRate
    else if hsecond : coordinate = second then secondRate
    else z ⟨coordinate, hfirst, hsecond⟩

/-- The packet's literal `(q_partner,z)` guards `G_h`. The recipient's own
coordinate is set to zero because its residual does not depend on it. -/
structure QuittingCrossedSourceGuards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) : Prop where
  lowerFirst : ∀ z : QuittingCrossedOutsider first second → ℝ,
    (∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1) → z ≠ 0 →
    0 < quittingDiscountedDisplacement reward 0
      (quittingCrossedGuardRow first second 0 0 z) first
  lowerSecond : ∀ z : QuittingCrossedOutsider first second → ℝ,
    (∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1) → z ≠ 0 →
    0 < quittingDiscountedDisplacement reward 0
      (quittingCrossedGuardRow first second 0 0 z) second
  upperFirst : ∀ z : QuittingCrossedOutsider first second → ℝ,
    (∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1) →
    quittingDiscountedDisplacement reward 0
      (quittingCrossedGuardRow first second 0 height z) first < 0
  upperSecond : ∀ z : QuittingCrossedOutsider first second → ℝ,
    (∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1) →
    quittingDiscountedDisplacement reward 0
      (quittingCrossedGuardRow first second height 0 z) second < 0

/-- The paper's strict guards, expressed on the full auxiliary box. The
response of each selected recipient is tested at its partner's zero and
ceiling faces; no original-game action set is clipped. -/
structure QuittingCrossedGuards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) : Prop where
  lowerFirst : ∀ hazard,
    (∀ coordinate, 0 ≤ hazard coordinate ∧
      hazard coordinate ≤ quittingCrossedCeiling first second height coordinate) →
    hazard second = 0 → quittingCrossedOutsiderPositive first second hazard →
    0 < quittingDiscountedDisplacement reward 0 hazard first
  lowerSecond : ∀ hazard,
    (∀ coordinate, 0 ≤ hazard coordinate ∧
      hazard coordinate ≤ quittingCrossedCeiling first second height coordinate) →
    hazard first = 0 → quittingCrossedOutsiderPositive first second hazard →
    0 < quittingDiscountedDisplacement reward 0 hazard second
  upperFirst : ∀ hazard,
    (∀ coordinate, 0 ≤ hazard coordinate ∧
      hazard coordinate ≤ quittingCrossedCeiling first second height coordinate) →
    hazard second = height →
    quittingDiscountedDisplacement reward 0 hazard first < 0
  upperSecond : ∀ hazard,
    (∀ coordinate, 0 ≤ hazard coordinate ∧
      hazard coordinate ≤ quittingCrossedCeiling first second height coordinate) →
    hazard first = height →
    quittingDiscountedDisplacement reward 0 hazard second < 0

/-- At any crossed fixed point with an active outsider, both selected hazards
are strictly between zero and the auxiliary height. -/
theorem quittingCrossedClippedMap_fixed_selected_interior_of_outsider
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ) (hheight : 0 < height)
    (hguard : QuittingCrossedGuards reward first second height)
    (hazard : Fin n → ℝ)
    (hfixed : quittingCrossedClippedMap reward first second height hazard = hazard)
    (hout : quittingCrossedOutsiderPositive first second hazard) :
    0 < hazard first ∧ hazard first < height ∧
      0 < hazard second ∧ hazard second < height := by
  have hbox := quittingCrossedClippedMap_fixed_mem_box reward first second height
    hheight.le hazard hfixed
  have hfaces := (quittingCrossedClippedMap_eq_self_iff reward first second height
    hheight hazard (fun coordinate => (hbox coordinate).1)
      (fun coordinate => (hbox coordinate).2)).mp hfixed
  have hfirstCeiling : quittingCrossedCeiling first second height first = height := by
    simp [quittingCrossedCeiling]
  have hsecondCeiling : quittingCrossedCeiling first second height second = height := by
    simp [quittingCrossedCeiling]
  have hfirst0 : 0 < hazard first := by
    by_contra hnot
    have hz : hazard first = 0 := le_antisymm (le_of_not_gt hnot) (hbox first).1
    have hpositive := hguard.lowerSecond hazard hbox hz hout
    have hnegative := (hfaces first).1 hz
    simp only [quittingCrossedResponse, Equiv.swap_apply_left] at hnegative
    linarith
  have hfirstUpper : hazard first < height := by
    by_contra hnot
    have ht : hazard first = height :=
      le_antisymm (by rw [← hfirstCeiling]; exact (hbox first).2)
        (le_of_not_gt hnot)
    have hnegative := hguard.upperSecond hazard hbox ht
    have hpositive := (hfaces first).2.2 (by rw [hfirstCeiling, ht])
    simp only [quittingCrossedResponse, Equiv.swap_apply_left] at hpositive
    linarith
  have hsecond0 : 0 < hazard second := by
    by_contra hnot
    have hz : hazard second = 0 := le_antisymm (le_of_not_gt hnot) (hbox second).1
    have hpositive := hguard.lowerFirst hazard hbox hz hout
    have hnegative := (hfaces second).1 hz
    simp only [quittingCrossedResponse, Equiv.swap_apply_right] at hnegative
    linarith
  have hsecondUpper : hazard second < height := by
    by_contra hnot
    have ht : hazard second = height :=
      le_antisymm (by rw [← hsecondCeiling]; exact (hbox second).2)
        (le_of_not_gt hnot)
    have hnegative := hguard.upperFirst hazard hbox ht
    have hpositive := (hfaces second).2.2 (by rw [hsecondCeiling, ht])
    simp only [quittingCrossedResponse, Equiv.swap_apply_right] at hpositive
    linarith
  exact ⟨hfirst0, hfirstUpper, hsecond0, hsecondUpper⟩

/-- Exact two-coalition expansion of the original residual on an axis with
one active opponent. This is equation (4.2) in the source packet. -/
theorem quittingDiscountedDisplacement_singletonRow_of_ne
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    {owner recipient : Fin n} (hne : recipient ≠ owner) (rate : ℝ) :
    quittingDiscountedDisplacement reward 0 (singletonRow rate owner) recipient =
      rate * ((1 - rate) * (weightOfReward reward) {recipient} recipient +
        rate * (weightOfReward reward) {recipient, owner} recipient -
        (weightOfReward reward) {owner} recipient) := by
  unfold quittingDiscountedDisplacement
  rw [sigmaValue_singletonRow_of_ne (weightOfReward reward) rate hne,
    excludedValue_singletonRow_of_ne (weightOfReward reward) rate hne]
  unfold continueMassExcl
  rw [prod_one_sub_singletonRow]
  have howner : owner ∈ Finset.univ.erase recipient :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ owner⟩
  simp only [howner, ite_true]
  ring

/-- The affine bracket in the selected-only residual is negative throughout
the guarded interval when reciprocal singleton rankings are positive. -/
private theorem crossed_axis_bracket_neg
    {height rate solo collision other : ℝ}
    (hheight : 0 < height) (hrate : 0 ≤ rate) (hrateHeight : rate ≤ height)
    (hreciprocal : 0 < other - solo)
    (hupper : height * ((1 - height) * solo + height * collision - other) < 0) :
    (1 - rate) * solo + rate * collision - other < 0 := by
  have hbracketHeight : (1 - height) * solo + height * collision - other < 0 := by
    nlinarith
  by_cases hslope : 0 ≤ collision - solo
  · have hdiff : 0 ≤ (height - rate) * (collision - solo) :=
      mul_nonneg (sub_nonneg.mpr hrateHeight) hslope
    nlinarith
  · have hslopeNeg : collision - solo < 0 := lt_of_not_ge hslope
    have hdiff : 0 ≤ rate * (solo - collision) :=
      mul_nonneg hrate (by linarith)
    nlinarith

/-- At zero discount the residual ignores its recipient's own hazard. -/
theorem quittingDiscountedDisplacement_congr_off_self
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (firstRow secondRow : Fin n → ℝ) (recipient : Fin n)
    (hagree : ∀ other, other ≠ recipient → firstRow other = secondRow other) :
    quittingDiscountedDisplacement reward 0 firstRow recipient =
      quittingDiscountedDisplacement reward 0 secondRow recipient := by
  simp only [quittingDiscountedDisplacement, sub_zero, one_mul]
  exact heterogeneousFaceNumerator_congr_off_self
    (weightOfReward reward) firstRow secondRow recipient hagree

private theorem quittingCrossedGuardRow_first
    (first second : Fin n) (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ) :
    quittingCrossedGuardRow first second firstRate secondRate z first = firstRate := by
  simp [quittingCrossedGuardRow]

private theorem quittingCrossedGuardRow_second
    (first second : Fin n) (hdistinct : first ≠ second)
    (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ) :
    quittingCrossedGuardRow first second firstRate secondRate z second = secondRate := by
  simp [quittingCrossedGuardRow, hdistinct.symm]

private theorem quittingCrossedGuardRow_outsider
    (first second : Fin n) (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ)
    (outsider : QuittingCrossedOutsider first second) :
    quittingCrossedGuardRow first second firstRate secondRate z outsider = z outsider := by
  simp [quittingCrossedGuardRow, outsider.property.1, outsider.property.2]

private theorem quittingCrossedGuardRow_mem_box
    (first second : Fin n) (hdistinct : first ≠ second)
    (height firstRate secondRate : ℝ)
    (hfirst : 0 ≤ firstRate ∧ firstRate ≤ height)
    (hsecond : 0 ≤ secondRate ∧ secondRate ≤ height)
    (z : QuittingCrossedOutsider first second → ℝ)
    (hz : ∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1) :
    ∀ coordinate, 0 ≤ quittingCrossedGuardRow first second firstRate secondRate z coordinate ∧
      quittingCrossedGuardRow first second firstRate secondRate z coordinate ≤
        quittingCrossedCeiling first second height coordinate := by
  intro coordinate
  by_cases hf : coordinate = first
  · subst coordinate
    rw [quittingCrossedGuardRow_first]
    simpa [quittingCrossedCeiling] using hfirst
  by_cases hs : coordinate = second
  · subst coordinate
    rw [quittingCrossedGuardRow_second first second hdistinct]
    simpa [quittingCrossedCeiling] using hsecond
  let outsider : QuittingCrossedOutsider first second := ⟨coordinate, hf, hs⟩
  have hrow := quittingCrossedGuardRow_outsider first second firstRate secondRate z outsider
  change quittingCrossedGuardRow first second firstRate secondRate z coordinate =
    z outsider at hrow
  rw [hrow]
  simpa [quittingCrossedCeiling, hf, hs] using hz outsider

private theorem quittingCrossedGuardRow_outsiderPositive_iff
    (first second : Fin n) (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ)
    (hz : ∀ outsider, 0 ≤ z outsider) :
    quittingCrossedOutsiderPositive first second
      (quittingCrossedGuardRow first second firstRate secondRate z) ↔ z ≠ 0 := by
  constructor
  · rintro ⟨coordinate, hfirst, hsecond, hpositive⟩ hzero
    have hrow := quittingCrossedGuardRow_outsider first second firstRate secondRate z
      ⟨coordinate, hfirst, hsecond⟩
    rw [hrow, hzero] at hpositive
    exact (lt_irrefl (0 : ℝ) hpositive).elim
  · intro hnonzero
    have hexists : ∃ outsider, z outsider ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hnonzero
      funext outsider
      exact hnone outsider
    obtain ⟨outsider, hnonzeroValue⟩ := hexists
    have hpositive : 0 < z outsider :=
      lt_of_le_of_ne (hz outsider) (Ne.symm hnonzeroValue)
    exact ⟨outsider.val, outsider.property.1, outsider.property.2,
      (quittingCrossedGuardRow_outsider first second firstRate secondRate z outsider).symm ▸
        hpositive⟩

private theorem quittingDiscountedDisplacement_eq_guardRow_first
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (hazard : Fin n → ℝ) (secondRate : ℝ) (hsecond : hazard second = secondRate) :
    quittingDiscountedDisplacement reward 0 hazard first =
      quittingDiscountedDisplacement reward 0
        (quittingCrossedGuardRow first second 0 secondRate
          (fun outsider => hazard outsider)) first := by
  apply quittingDiscountedDisplacement_congr_off_self
  intro other hother
  by_cases hs : other = second
  · subst other
    rw [hsecond, quittingCrossedGuardRow_second first second hdistinct]
  · let outsider : QuittingCrossedOutsider first second := ⟨other, hother, hs⟩
    have hrow := quittingCrossedGuardRow_outsider first second 0 secondRate
      (fun outsider : QuittingCrossedOutsider first second => hazard outsider) outsider
    change quittingCrossedGuardRow first second 0 secondRate
      (fun outsider : QuittingCrossedOutsider first second => hazard outsider) other =
        hazard other at hrow
    exact hrow.symm

private theorem quittingDiscountedDisplacement_eq_guardRow_second
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n)
    (hazard : Fin n → ℝ) (firstRate : ℝ) (hfirst : hazard first = firstRate) :
    quittingDiscountedDisplacement reward 0 hazard second =
      quittingDiscountedDisplacement reward 0
        (quittingCrossedGuardRow first second firstRate 0
          (fun outsider => hazard outsider)) second := by
  apply quittingDiscountedDisplacement_congr_off_self
  intro other hother
  by_cases hf : other = first
  · subst other
    rw [hfirst, quittingCrossedGuardRow_first]
  · let outsider : QuittingCrossedOutsider first second := ⟨other, hf, hother⟩
    have hrow := quittingCrossedGuardRow_outsider first second firstRate 0
      (fun outsider : QuittingCrossedOutsider first second => hazard outsider) outsider
    change quittingCrossedGuardRow first second firstRate 0
      (fun outsider : QuittingCrossedOutsider first second => hazard outsider) other =
        hazard other at hrow
    exact hrow.symm

/-- The full-box guard interface is exactly the packet's literal `G_h` for
distinct selected players. No own-hazard quantifier is added to the source
guard: it is removed using the proved off-self residual invariance. -/
theorem quittingCrossedSourceGuards_iff_fullBoxGuards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height) :
    QuittingCrossedSourceGuards reward first second height ↔
      QuittingCrossedGuards reward first second height := by
  constructor
  · intro hsource
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hazard hbox hsecond hout
      let z : QuittingCrossedOutsider first second → ℝ := fun outsider => hazard outsider
      have hz (outsider : QuittingCrossedOutsider first second) :
          0 ≤ z outsider ∧ z outsider ≤ 1 := by
        have h := hbox outsider
        simpa [z, quittingCrossedCeiling, outsider.property.1,
          outsider.property.2] using h
      have hnonzero : z ≠ 0 := by
        intro hz0
        obtain ⟨outsider, hf, hs, hpositive⟩ := hout
        have hzero := congrFun hz0
          (⟨outsider, hf, hs⟩ : QuittingCrossedOutsider first second)
        change hazard outsider = 0 at hzero
        linarith
      rw [quittingDiscountedDisplacement_eq_guardRow_first
        reward first second hdistinct hazard 0 hsecond]
      exact hsource.lowerFirst z hz hnonzero
    · intro hazard hbox hfirst hout
      let z : QuittingCrossedOutsider first second → ℝ := fun outsider => hazard outsider
      have hz (outsider : QuittingCrossedOutsider first second) :
          0 ≤ z outsider ∧ z outsider ≤ 1 := by
        have h := hbox outsider
        simpa [z, quittingCrossedCeiling, outsider.property.1,
          outsider.property.2] using h
      have hnonzero : z ≠ 0 := by
        intro hz0
        obtain ⟨outsider, hf, hs, hpositive⟩ := hout
        have hzero := congrFun hz0
          (⟨outsider, hf, hs⟩ : QuittingCrossedOutsider first second)
        change hazard outsider = 0 at hzero
        linarith
      rw [quittingDiscountedDisplacement_eq_guardRow_second
        reward first second hazard 0 hfirst]
      exact hsource.lowerSecond z hz hnonzero
    · intro hazard hbox hsecond
      let z : QuittingCrossedOutsider first second → ℝ := fun outsider => hazard outsider
      have hz (outsider : QuittingCrossedOutsider first second) :
          0 ≤ z outsider ∧ z outsider ≤ 1 := by
        have h := hbox outsider
        simpa [z, quittingCrossedCeiling, outsider.property.1,
          outsider.property.2] using h
      rw [quittingDiscountedDisplacement_eq_guardRow_first
        reward first second hdistinct hazard height hsecond]
      exact hsource.upperFirst z hz
    · intro hazard hbox hfirst
      let z : QuittingCrossedOutsider first second → ℝ := fun outsider => hazard outsider
      have hz (outsider : QuittingCrossedOutsider first second) :
          0 ≤ z outsider ∧ z outsider ≤ 1 := by
        have h := hbox outsider
        simpa [z, quittingCrossedCeiling, outsider.property.1,
          outsider.property.2] using h
      rw [quittingDiscountedDisplacement_eq_guardRow_second
        reward first second hazard height hfirst]
      exact hsource.upperSecond z hz
  · intro hfull
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz hnonzero
      have hbox := quittingCrossedGuardRow_mem_box first second hdistinct height 0 0
        ⟨le_rfl, hheight.le⟩ ⟨le_rfl, hheight.le⟩ z hz
      exact hfull.lowerFirst _ hbox
        (quittingCrossedGuardRow_second first second hdistinct 0 0 z)
        ((quittingCrossedGuardRow_outsiderPositive_iff first second 0 0 z
          (fun outsider => (hz outsider).1)).mpr hnonzero)
    · intro z hz hnonzero
      have hbox := quittingCrossedGuardRow_mem_box first second hdistinct height 0 0
        ⟨le_rfl, hheight.le⟩ ⟨le_rfl, hheight.le⟩ z hz
      exact hfull.lowerSecond _ hbox (quittingCrossedGuardRow_first first second 0 0 z)
        ((quittingCrossedGuardRow_outsiderPositive_iff first second 0 0 z
          (fun outsider => (hz outsider).1)).mpr hnonzero)
    · intro z hz
      have hbox := quittingCrossedGuardRow_mem_box first second hdistinct
        height 0 height ⟨le_rfl, hheight.le⟩ ⟨hheight.le, le_rfl⟩ z hz
      exact hfull.upperFirst _ hbox
        (quittingCrossedGuardRow_second first second hdistinct 0 height z)
    · intro z hz
      have hbox := quittingCrossedGuardRow_mem_box first second hdistinct
        height height 0 ⟨hheight.le, le_rfl⟩ ⟨le_rfl, hheight.le⟩ z hz
      exact hfull.upperSecond _ hbox (quittingCrossedGuardRow_first first second height 0 z)

/-- A singleton row at the selected auxiliary ceiling belongs to the box. -/
private theorem crossed_singletonRow_height_mem_box
    (first second : Fin n) (height : ℝ)
    (hheight : 0 < height)
    (owner : Fin n) (howner : owner = first ∨ owner = second) :
    ∀ coordinate, 0 ≤ singletonRow height owner coordinate ∧
      singletonRow height owner coordinate ≤
        quittingCrossedCeiling first second height coordinate := by
  intro coordinate
  by_cases hcoordinate : coordinate = owner
  · subst coordinate
    rw [singletonRow_self]
    constructor
    · exact hheight.le
    · rcases howner with rfl | rfl <;> simp [quittingCrossedCeiling]
  · rw [singletonRow_of_ne height hcoordinate]
    constructor
    · exact le_rfl
    · unfold quittingCrossedCeiling
      split_ifs <;> linarith

/-- Reciprocal singleton ranking and a strict upper guard make every
positive selected-axis response strictly negative below the ceiling. -/
private theorem crossed_selected_axis_response_neg
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    {owner recipient : Fin n} (hne : recipient ≠ owner)
    {height rate : ℝ} (hheight : 0 < height)
    (hrate : 0 < rate) (hrateHeight : rate ≤ height)
    (hreciprocal : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward recipient owner)
    (hupper : quittingDiscountedDisplacement reward 0
      (singletonRow height owner) recipient < 0) :
    quittingDiscountedDisplacement reward 0 (singletonRow rate owner) recipient < 0 := by
  let r := weightOfReward reward
  have hranking : 0 < r {owner} recipient - r {recipient} recipient := by
    simpa [r, QuittingLCPClassification.quittingSingletonMatrix,
      weightOfReward] using hreciprocal
  rw [quittingDiscountedDisplacement_singletonRow_of_ne reward hne height] at hupper
  rw [quittingDiscountedDisplacement_singletonRow_of_ne reward hne rate]
  have hbracket := crossed_axis_bracket_neg hheight hrate.le hrateHeight
    hranking hupper
  nlinarith [mul_pos hrate (neg_pos.mpr hbracket)]

/-- Reciprocal singleton rankings and the upper guards exclude every
selected-only nonzero fixed point; an escaping fixed point must activate an
outsider. -/
theorem quittingCrossedClippedMap_fixed_outsiderPositive_of_nonzero
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height)
    (hguard : QuittingCrossedGuards reward first second height)
    (hreciprocalFirst : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward first second)
    (hreciprocalSecond : 0 < QuittingLCPClassification.quittingSingletonMatrix
      reward second first)
    (hazard : Fin n → ℝ) (hpointNe : hazard ≠ 0)
    (hfixed : quittingCrossedClippedMap reward first second height hazard = hazard) :
    quittingCrossedOutsiderPositive first second hazard := by
  have hbox := quittingCrossedClippedMap_fixed_mem_box reward first second height
    hheight.le hazard hfixed
  have hfaces := (quittingCrossedClippedMap_eq_self_iff reward first second height
    hheight hazard (fun coordinate => (hbox coordinate).1)
      (fun coordinate => (hbox coordinate).2)).mp hfixed
  have hcrossedNonneg (coordinate : Fin n) (hpositive : 0 < hazard coordinate) :
      0 ≤ quittingCrossedResponse reward first second hazard coordinate := by
    by_cases hlt : hazard coordinate <
        quittingCrossedCeiling first second height coordinate
    · rw [(hfaces coordinate).2.1 hpositive hlt]
    · exact (hfaces coordinate).2.2
        (le_antisymm (hbox coordinate).2 (le_of_not_gt hlt))
  by_contra hnoOutsider
  have hzeroOuts (coordinate : Fin n) (hfirst : coordinate ≠ first)
      (hsecond : coordinate ≠ second) : hazard coordinate = 0 := by
    by_contra hnonzero
    have hpositive : 0 < hazard coordinate :=
      lt_of_le_of_ne (hbox coordinate).1 (Ne.symm hnonzero)
    exact hnoOutsider ⟨coordinate, hfirst, hsecond, hpositive⟩
  have hfirstCeiling : quittingCrossedCeiling first second height first = height := by
    simp [quittingCrossedCeiling]
  have hsecondCeiling : quittingCrossedCeiling first second height second = height := by
    simp [quittingCrossedCeiling]
  have hfirstZero : hazard first = 0 := by
    by_contra hnonzero
    have hpositive : 0 < hazard first :=
      lt_of_le_of_ne (hbox first).1 (Ne.symm hnonzero)
    have hrateHeight : hazard first ≤ height := by
      rw [← hfirstCeiling]
      exact (hbox first).2
    have hupper : quittingDiscountedDisplacement reward 0
        (singletonRow height first) second < 0 :=
      hguard.upperSecond (singletonRow height first)
        (crossed_singletonRow_height_mem_box first second height hheight first (Or.inl rfl))
        (singletonRow_self height first)
    have haxisNeg := crossed_selected_axis_response_neg reward hdistinct.symm
      hheight hpositive hrateHeight hreciprocalSecond hupper
    have hsame : quittingDiscountedDisplacement reward 0 hazard second =
        quittingDiscountedDisplacement reward 0
          (singletonRow (hazard first) first) second := by
      apply quittingDiscountedDisplacement_congr_off_self
      intro other hother
      by_cases howner : other = first
      · subst other
        simp
      · rw [singletonRow_of_ne _ howner]
        exact hzeroOuts other howner hother
    have hnonneg := hcrossedNonneg first hpositive
    simp only [quittingCrossedResponse, Equiv.swap_apply_left] at hnonneg
    rw [hsame] at hnonneg
    linarith
  have hsecondZero : hazard second = 0 := by
    by_contra hnonzero
    have hpositive : 0 < hazard second :=
      lt_of_le_of_ne (hbox second).1 (Ne.symm hnonzero)
    have hrateHeight : hazard second ≤ height := by
      rw [← hsecondCeiling]
      exact (hbox second).2
    have hupper : quittingDiscountedDisplacement reward 0
        (singletonRow height second) first < 0 :=
      hguard.upperFirst (singletonRow height second)
        (crossed_singletonRow_height_mem_box first second height hheight second (Or.inr rfl))
        (singletonRow_self height second)
    have haxisNeg := crossed_selected_axis_response_neg reward hdistinct
      hheight hpositive hrateHeight hreciprocalFirst hupper
    have hsame : quittingDiscountedDisplacement reward 0 hazard first =
        quittingDiscountedDisplacement reward 0
          (singletonRow (hazard second) second) first := by
      apply quittingDiscountedDisplacement_congr_off_self
      intro other hother
      by_cases howner : other = second
      · subst other
        simp
      · rw [singletonRow_of_ne _ howner]
        exact hzeroOuts other hother howner
    have hnonneg := hcrossedNonneg second hpositive
    simp only [quittingCrossedResponse, Equiv.swap_apply_right] at hnonneg
    rw [hsame] at hnonneg
    linarith
  apply hpointNe
  funext coordinate
  by_cases hfirst : coordinate = first
  · subst coordinate
    exact hfirstZero
  by_cases hsecond : coordinate = second
  · subst coordinate
    exact hsecondZero
  exact hzeroOuts coordinate hfirst hsecond

/-- Once an outsider is active, the crossed auxiliary fixed point satisfies
the unswapped original-player stationary face conditions at every coordinate. -/
theorem quittingDiscountedClippedMap_fixed_of_crossed_fixed_guards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (height : ℝ)
    (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hguard : QuittingCrossedGuards reward first second height)
    (hazard : Fin n → ℝ)
    (hfixed : quittingCrossedClippedMap reward first second height hazard = hazard)
    (hout : quittingCrossedOutsiderPositive first second hazard) :
    quittingDiscountedClippedMap reward 0 hazard = hazard := by
  have hbox := quittingCrossedClippedMap_fixed_mem_box reward first second height
    hheight.le hazard hfixed
  have hzero (coordinate : Fin n) : 0 ≤ hazard coordinate := (hbox coordinate).1
  have hone (coordinate : Fin n) : hazard coordinate ≤ 1 := by
    have hceiling : quittingCrossedCeiling first second height coordinate ≤ 1 := by
      unfold quittingCrossedCeiling
      split_ifs <;> linarith
    exact (hbox coordinate).2.trans hceiling
  have hfaces := (quittingCrossedClippedMap_eq_self_iff reward first second height
    hheight hazard hzero (fun coordinate => (hbox coordinate).2)).mp hfixed
  obtain ⟨hfirstPos, hfirstLt, hsecondPos, hsecondLt⟩ :=
    quittingCrossedClippedMap_fixed_selected_interior_of_outsider reward
      first second height hheight hguard hazard hfixed hout
  have hfirstResidual : quittingDiscountedDisplacement reward 0 hazard first = 0 := by
    have h := (hfaces second).2.1 hsecondPos (by
      simpa [quittingCrossedCeiling] using hsecondLt)
    simpa only [quittingCrossedResponse, Equiv.swap_apply_right] using h
  have hsecondResidual : quittingDiscountedDisplacement reward 0 hazard second = 0 := by
    have h := (hfaces first).2.1 hfirstPos (by
      simpa [quittingCrossedCeiling] using hfirstLt)
    simpa only [quittingCrossedResponse, Equiv.swap_apply_left] using h
  apply (quittingDiscountedClippedMap_eq_self_iff reward 0 hazard hzero hone).mpr
  intro coordinate
  by_cases hfirst : coordinate = first
  · subst coordinate
    exact ⟨fun hz => (hfirstPos.ne' hz).elim,
      fun _ _ => hfirstResidual,
      fun htop => ((lt_of_lt_of_le hfirstLt hheightOne).ne htop).elim⟩
  by_cases hsecond : coordinate = second
  · subst coordinate
    exact ⟨fun hz => (hsecondPos.ne' hz).elim,
      fun _ _ => hsecondResidual,
      fun htop => ((lt_of_lt_of_le hsecondLt hheightOne).ne htop).elim⟩
  have hceiling : quittingCrossedCeiling first second height coordinate = 1 := by
    simp [quittingCrossedCeiling, hfirst, hsecond]
  simpa only [quittingCrossedResponse,
    Equiv.swap_apply_of_ne_of_ne hfirst hsecond, hceiling] using hfaces coordinate

end GameTheory
