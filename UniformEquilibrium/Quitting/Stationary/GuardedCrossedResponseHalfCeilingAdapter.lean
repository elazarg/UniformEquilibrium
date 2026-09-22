import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingCoefficients

/-! # Literal half-ceiling source guards from lower rankings and nine coefficients -/

noncomputable section

namespace GameTheory

/-- Packet (L) for both selected players and all nine strict upper coefficients
for each of their half-ceiling residual polynomials. -/
structure QuittingHalfStrictRawGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop where
  lowerFirst : QuittingCrossedStrictLowerRanking reward 0 1
  lowerSecond : QuittingCrossedStrictLowerRanking reward 1 0
  upper : QuittingHalfStrictBernsteinUpper reward

private theorem halfGuardRow_box
    (firstRate secondRate : ℝ) (z : QuittingCrossedOutsider (0 : Fin 4) 1 → ℝ)
    (hz : ∀ outsider, 0 ≤ z outsider ∧ z outsider ≤ 1)
    (recipient partner : Fin 4)
    (hset : ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      coordinate ≠ 0 ∧ coordinate ≠ 1) :
    ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 ≤ quittingCrossedGuardRow 0 1 firstRate secondRate z coordinate ∧
        quittingCrossedGuardRow 0 1 firstRate secondRate z coordinate ≤ 1 := by
  intro coordinate hcoordinate
  obtain ⟨hzero, hone⟩ := hset coordinate hcoordinate
  simpa [quittingCrossedGuardRow, hzero, hone] using
    hz ⟨coordinate, hzero, hone⟩

private theorem halfGuardRow_active
    (firstRate secondRate : ℝ) (z : QuittingCrossedOutsider (0 : Fin 4) 1 → ℝ)
    (hz : ∀ outsider, 0 ≤ z outsider) (hnonzero : z ≠ 0)
    (recipient partner : Fin 4)
    (hmem : ∀ outsider : QuittingCrossedOutsider (0 : Fin 4) 1,
      outsider.val ∈ quittingCrossedRawOutsiders recipient partner) :
    ∃ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 < quittingCrossedGuardRow 0 1 firstRate secondRate z coordinate := by
  have hexists : ∃ outsider, z outsider ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hnonzero
    funext outsider
    exact hnone outsider
  obtain ⟨outsider, hvalue⟩ := hexists
  refine ⟨outsider.val, hmem outsider, ?_⟩
  have hrow : quittingCrossedGuardRow 0 1 firstRate secondRate z outsider.val =
      z outsider := by
    simp [quittingCrossedGuardRow, outsider.property.1, outsider.property.2]
  rw [hrow]
  exact lt_of_le_of_ne (hz outsider) (Ne.symm hvalue)

private theorem first_halfGuardRow_eq
    (z : QuittingCrossedOutsider (0 : Fin 4) 1 → ℝ) :
    quittingCrossedGuardRow 0 1 0 (1 / 2) z =
      halfFirstRow (z ⟨2, by decide, by decide⟩) (z ⟨3, by decide, by decide⟩) := by
  funext coordinate
  fin_cases coordinate <;> simp [quittingCrossedGuardRow, halfFirstRow]

private theorem second_halfGuardRow_eq
    (z : QuittingCrossedOutsider (0 : Fin 4) 1 → ℝ) :
    quittingCrossedGuardRow 0 1 (1 / 2) 0 z =
      halfSecondRow (z ⟨2, by decide, by decide⟩) (z ⟨3, by decide, by decide⟩) := by
  funext coordinate
  fin_cases coordinate <;> simp [quittingCrossedGuardRow, halfSecondRow]

/-- The paper's half-ceiling coefficient test implies all four literal `G₁/₂`
source guards for the original four-player reward table. -/
theorem quittingCrossedSourceGuards_of_halfStrictRawGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hraw : QuittingHalfStrictRawGuards reward) :
    QuittingCrossedSourceGuards reward 0 1 (1 / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz hnonzero
    let hazard := quittingCrossedGuardRow 0 1 0 0 z
    have hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders (0 : Fin 4) 1,
        0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1 := by
      apply halfGuardRow_box 0 0 z hz 0 1
      intro coordinate hcoordinate
      simp only [quittingCrossedRawOutsiders, Finset.mem_erase,
        Finset.mem_univ, and_true] at hcoordinate
      exact ⟨hcoordinate.2, hcoordinate.1⟩
    have hactive : ∃ coordinate ∈ quittingCrossedRawOutsiders (0 : Fin 4) 1,
        0 < hazard coordinate := by
      apply halfGuardRow_active 0 0 z (fun outsider => (hz outsider).1)
        hnonzero 0 1
      intro outsider
      simp [quittingCrossedRawOutsiders, outsider.property.1, outsider.property.2]
    exact quittingCrossed_displacement_partner_zero_pos_of_lowerRanking
      reward hazard 0 1 (by decide) (by simp [hazard, quittingCrossedGuardRow])
      hbox hactive hraw.lowerFirst
  · intro z hz hnonzero
    let hazard := quittingCrossedGuardRow 0 1 0 0 z
    have hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders (1 : Fin 4) 0,
        0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1 := by
      apply halfGuardRow_box 0 0 z hz 1 0
      intro coordinate hcoordinate
      simp only [quittingCrossedRawOutsiders, Finset.mem_erase,
        Finset.mem_univ, and_true] at hcoordinate
      exact ⟨hcoordinate.1, hcoordinate.2⟩
    have hactive : ∃ coordinate ∈ quittingCrossedRawOutsiders (1 : Fin 4) 0,
        0 < hazard coordinate := by
      apply halfGuardRow_active 0 0 z (fun outsider => (hz outsider).1)
        hnonzero 1 0
      intro outsider
      simp [quittingCrossedRawOutsiders, outsider.property.1, outsider.property.2]
    exact quittingCrossed_displacement_partner_zero_pos_of_lowerRanking
      reward hazard 1 0 (by decide) (by simp [hazard, quittingCrossedGuardRow])
      hbox hactive hraw.lowerSecond
  · intro z hz
    let x := z ⟨2, by decide, by decide⟩
    let y := z ⟨3, by decide, by decide⟩
    have hx : 0 ≤ x ∧ x ≤ 1 := hz ⟨2, by decide, by decide⟩
    have hy : 0 ≤ y ∧ y ≤ 1 := hz ⟨3, by decide, by decide⟩
    rw [first_halfGuardRow_eq]
    exact quittingHalfFirstResidual_neg_of_coefficients reward hraw.upper x y hx hy
  · intro z hz
    let x := z ⟨2, by decide, by decide⟩
    let y := z ⟨3, by decide, by decide⟩
    have hx : 0 ≤ x ∧ x ≤ 1 := hz ⟨2, by decide, by decide⟩
    have hy : 0 ≤ y ∧ y ≤ 1 := hz ⟨3, by decide, by decide⟩
    rw [second_halfGuardRow_eq]
    exact quittingHalfSecondResidual_neg_of_coefficients reward hraw.upper x y hx hy

end GameTheory
