import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawTests

/-! # Raw strict comparisons produce the literal crossed source guards -/

noncomputable section

namespace GameTheory

variable {n : ℕ}

/-- The two selected reward rows satisfy packet (L) and the unit-ceiling (U). -/
structure QuittingCrossedStrictRawUnitGuards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) : Prop where
  lowerFirst : QuittingCrossedStrictLowerRanking reward first second
  lowerSecond : QuittingCrossedStrictLowerRanking reward second first
  upperFirst : QuittingCrossedStrictUnitJoining reward first second
  upperSecond : QuittingCrossedStrictUnitJoining reward second first

private theorem rawGuardRow_outsider_eq
    (first second : Fin n) (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ)
    (coordinate : Fin n) (hfirst : coordinate ≠ first) (hsecond : coordinate ≠ second) :
    quittingCrossedGuardRow first second firstRate secondRate z coordinate =
      z ⟨coordinate, hfirst, hsecond⟩ := by
  simp [quittingCrossedGuardRow, hfirst, hsecond]

private theorem rawGuardRow_box
    (first second : Fin n) (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ)
    (hz : ∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1)
    (recipient partner : Fin n)
    (houtsiders : ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      coordinate ≠ first ∧ coordinate ≠ second) :
    ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 ≤ quittingCrossedGuardRow first second firstRate secondRate z coordinate ∧
        quittingCrossedGuardRow first second firstRate secondRate z coordinate ≤ 1 := by
  intro coordinate hcoordinate
  obtain ⟨hfirst, hsecond⟩ := houtsiders coordinate hcoordinate
  rw [rawGuardRow_outsider_eq first second firstRate secondRate z coordinate
    hfirst hsecond]
  exact hz ⟨coordinate, hfirst, hsecond⟩

private theorem rawGuardRow_active
    (first second : Fin n) (firstRate secondRate : ℝ)
    (z : QuittingCrossedOutsider first second → ℝ)
    (hz : ∀ outsider, 0 ≤ z outsider)
    (hnonzero : z ≠ 0)
    (recipient partner : Fin n)
    (hmem : ∀ outsider : QuittingCrossedOutsider first second,
      outsider.val ∈ quittingCrossedRawOutsiders recipient partner) :
    ∃ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 < quittingCrossedGuardRow first second firstRate secondRate z coordinate := by
  have hexists : ∃ outsider, z outsider ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hnonzero
    funext outsider
    exact hnone outsider
  obtain ⟨outsider, hvalue⟩ := hexists
  refine ⟨outsider.val, hmem outsider, ?_⟩
  rw [rawGuardRow_outsider_eq first second firstRate secondRate z outsider.val
    outsider.property.1 outsider.property.2]
  exact lt_of_le_of_ne (hz outsider) (Ne.symm hvalue)

/-- The finite reward comparisons imply exactly the packet's four `G₁`
inequalities, quantified over the full literal outsider box. -/
theorem quittingCrossedSourceGuards_of_strictRawUnitGuards
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (hraw : QuittingCrossedStrictRawUnitGuards reward first second) :
    QuittingCrossedSourceGuards reward first second 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz hnonzero
    let hazard := quittingCrossedGuardRow first second 0 0 z
    have hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders first second,
        0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1 := by
      apply rawGuardRow_box first second 0 0 z hz first second
      intro coordinate hcoordinate
      simp only [quittingCrossedRawOutsiders, Finset.mem_erase,
        Finset.mem_univ, and_true] at hcoordinate
      exact ⟨hcoordinate.2, hcoordinate.1⟩
    have hactive : ∃ coordinate ∈ quittingCrossedRawOutsiders first second,
        0 < hazard coordinate := by
      apply rawGuardRow_active first second 0 0 z (fun outsider => (hz outsider).1)
        hnonzero first second
      intro outsider
      simp [quittingCrossedRawOutsiders, outsider.property.1, outsider.property.2]
    exact quittingCrossed_displacement_partner_zero_pos_of_lowerRanking
      reward hazard first second hdistinct.symm
      (by simp [hazard, quittingCrossedGuardRow, hdistinct.symm])
      hbox hactive hraw.lowerFirst
  · intro z hz hnonzero
    let hazard := quittingCrossedGuardRow first second 0 0 z
    have hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders second first,
        0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1 := by
      apply rawGuardRow_box first second 0 0 z hz second first
      intro coordinate hcoordinate
      simp only [quittingCrossedRawOutsiders, Finset.mem_erase,
        Finset.mem_univ, and_true] at hcoordinate
      exact ⟨hcoordinate.1, hcoordinate.2⟩
    have hactive : ∃ coordinate ∈ quittingCrossedRawOutsiders second first,
        0 < hazard coordinate := by
      apply rawGuardRow_active first second 0 0 z (fun outsider => (hz outsider).1)
        hnonzero second first
      intro outsider
      simp [quittingCrossedRawOutsiders, outsider.property.1, outsider.property.2]
    exact quittingCrossed_displacement_partner_zero_pos_of_lowerRanking
      reward hazard second first hdistinct
      (by simp [hazard, quittingCrossedGuardRow])
      hbox hactive hraw.lowerSecond
  · intro z hz
    let hazard := quittingCrossedGuardRow first second 0 1 z
    have hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders first second,
        0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1 := by
      apply rawGuardRow_box first second 0 1 z hz first second
      intro coordinate hcoordinate
      simp only [quittingCrossedRawOutsiders, Finset.mem_erase,
        Finset.mem_univ, and_true] at hcoordinate
      exact ⟨hcoordinate.2, hcoordinate.1⟩
    exact quittingCrossed_displacement_partner_one_neg_of_unitJoining
      reward hazard first second hdistinct.symm
      (by simp [hazard, quittingCrossedGuardRow, hdistinct.symm])
      hbox hraw.upperFirst
  · intro z hz
    let hazard := quittingCrossedGuardRow first second 1 0 z
    have hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders second first,
        0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1 := by
      apply rawGuardRow_box first second 1 0 z hz second first
      intro coordinate hcoordinate
      simp only [quittingCrossedRawOutsiders, Finset.mem_erase,
        Finset.mem_univ, and_true] at hcoordinate
      exact ⟨hcoordinate.1, hcoordinate.2⟩
    exact quittingCrossed_displacement_partner_one_neg_of_unitJoining
      reward hazard second first hdistinct
      (by simp [hazard, quittingCrossedGuardRow])
      hbox hraw.upperSecond

end GameTheory
