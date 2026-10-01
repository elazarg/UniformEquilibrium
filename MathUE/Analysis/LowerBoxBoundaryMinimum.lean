import MathUE.Analysis.LowerBoxBoundarySmoothDrift

/-! # One-sided derivative signs at lower-box-boundary minima

This module extends the canonical lower boundary. Face columns need only be
bounded weakly above; that includes adaptive rectangles with frozen upper faces.
-/

noncomputable section

namespace Math

open Set Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem lowerBoxBoundary_minimum_coordinate_move_nonneg
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (player other : ι) (hne : other ≠ player)
    (hother : point other = lower other) (replacement : ℝ)
    (hreplacement : replacement ∈ Set.Icc (lower player) (upper player)) :
    0 ≤ (replacement - point player) * derivative (Pi.single player 1) := by
  let target := Function.update point player replacement
  have htarget : target ∈ Set.Icc lower upper := by
    constructor <;> intro who
    · by_cases heq : who = player
      · subst who
        simpa [target] using hreplacement.1
      · simpa [target, heq] using hpoint.1.1 who
    · by_cases heq : who = player
      · subst who
        simpa [target] using hreplacement.2
      · simpa [target, heq] using hpoint.1.2 who
  have hsegment : segment ℝ point target ⊆ lowerBoxBoundary lower upper := by
    apply (segment_subset_iff ℝ).mpr
    intro a b ha hb hab
    refine ⟨(convex_Icc lower upper) hpoint.1 htarget ha hb hab, other, ?_⟩
    have htargetOther : target other = lower other := by
      simpa [target, hne] using hother
    change a * point other + b * target other = lower other
    rw [hother, htargetOther, ← add_mul, hab, one_mul]
  have hlocal : IsLocalMinOn potential (lowerBoxBoundary lower upper) point :=
    Filter.mem_of_superset self_mem_nhdsWithin hmin
  have hnonneg := hlocal.hasFDerivWithinAt_nonneg hdiff.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hsegment)
  have hmove : target - point = (replacement - point player) • Pi.single player 1 := by
    ext who
    by_cases heq : who = player
    · subst who
      simp [target]
    · simp [target, heq]
  simpa only [hmove, map_smul, smul_eq_mul] using hnonneg

/-- The partial derivative at an upper face is nonpositive. The preserved
lower binding is obtained from boundary membership, even on intersections. -/
theorem lowerBoxBoundary_minimum_partial_nonpos
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (player : ι) (hplayer : point player = upper player)
    (hwidth : lower player < upper player) :
    derivative (Pi.single player 1) ≤ 0 := by
  obtain ⟨other, hother⟩ := hpoint.2
  have hne : other ≠ player := by
    intro heq
    subst other
    linarith
  have hmove := lowerBoxBoundary_minimum_coordinate_move_nonneg
    lower upper point potential derivative hpoint hmin hdiff player other hne hother
    (lower player) ⟨le_rfl, hwidth.le⟩
  rw [hplayer] at hmove
  nlinarith

/-- An interior coordinate has zero partial derivative, while another lower
coordinate remains binding throughout each permitted variation. -/
theorem lowerBoxBoundary_minimum_partial_eq_zero
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (player : ι) (hlower : lower player < point player)
    (hupper : point player < upper player) :
    derivative (Pi.single player 1) = 0 := by
  obtain ⟨other, hother⟩ := hpoint.2
  have hne : other ≠ player := by
    intro heq
    subst other
    linarith
  have hdown := lowerBoxBoundary_minimum_coordinate_move_nonneg
    lower upper point potential derivative hpoint hmin hdiff player other hne hother
    (lower player) ⟨le_rfl, hlower.le.trans hupper.le⟩
  have hup := lowerBoxBoundary_minimum_coordinate_move_nonneg
    lower upper point potential derivative hpoint hmin hdiff player other hne hother
    (upper player) ⟨hlower.le.trans hupper.le, le_rfl⟩
  nlinarith

/-- Positive face drift forbids a boundary minimum with a unique lower binding.
The upper-column bounds are weak, as required by adaptive reflection boxes. -/
theorem lowerBoxBoundary_minimum_has_two_bindings
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hdrift : ∀ player, point player = lower player →
      0 < derivative (point - face player)) :
    ∀ player, ∃ other, point other = lower other ∧ other ≠ player := by
  intro player
  by_contra hnone
  have honly : ∀ other, point other = lower other → other = player := by
    intro other hbind
    by_contra hne
    exact hnone ⟨other, hbind, hne⟩
  have hplayer : point player = lower player := by
    obtain ⟨owner, howner⟩ := hpoint.2
    simpa only [honly owner howner] using howner
  have hnonpos : derivative (point - face player) ≤ 0 := by
    conv_lhs => rw [pi_eq_sum_univ' (point - face player)]
    rw [map_sum]
    apply Finset.sum_nonpos
    intro other _
    rw [map_smul]
    change (point other - face player other) * derivative (Pi.single other 1) ≤ 0
    by_cases heq : other = player
    · subst other
      simp [hplayer, hdiagonal player]
    · have hlower : lower other < point other := by
        apply lt_of_le_of_ne (hpoint.1.1 other)
        intro hequal
        exact heq (honly other hequal.symm)
      by_cases hupper : point other = upper other
      · have hpartial := lowerBoxBoundary_minimum_partial_nonpos lower upper point
          potential derivative hpoint hmin hdiff other hupper (hwidth other)
        exact mul_nonpos_of_nonneg_of_nonpos
          (by rw [hupper]; exact sub_nonneg.mpr (hfaceUpper player other)) hpartial
      · have hstrict : point other < upper other :=
          lt_of_le_of_ne (hpoint.1.2 other) hupper
        rw [lowerBoxBoundary_minimum_partial_eq_zero lower upper point potential
          derivative hpoint hmin hdiff other hlower hstrict]
        simp
  exact (not_lt_of_ge hnonpos) (hdrift player hplayer)

/-- All one-sided derivative signs at a boundary minimum follow from positive
face drift; no gradient-zero assertion is made at upper faces. -/
theorem lowerBoxBoundary_minimum_partial_signs
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hdrift : ∀ player, point player = lower player →
      0 < derivative (point - face player)) :
    ∀ player,
      (point player = lower player → 0 ≤ derivative (Pi.single player 1)) ∧
      (lower player < point player → point player < upper player →
        derivative (Pi.single player 1) = 0) ∧
      (point player = upper player → derivative (Pi.single player 1) ≤ 0) := by
  have htwo := lowerBoxBoundary_minimum_has_two_bindings lower upper point potential
    derivative face hpoint hmin hdiff hwidth hdiagonal hfaceUpper hdrift
  intro player
  refine ⟨?_, ?_, ?_⟩
  · intro hplayer
    obtain ⟨other, hother, hne⟩ := htwo player
    exact lowerBoxBoundary_minimum_partial_nonneg lower upper point potential derivative
      hpoint hmin hdiff player other hne hplayer hother (hwidth player)
  · exact lowerBoxBoundary_minimum_partial_eq_zero lower upper point potential derivative
      hpoint hmin hdiff player
  · intro hplayer
    exact lowerBoxBoundary_minimum_partial_nonpos lower upper point potential derivative
      hpoint hmin hdiff player hplayer (hwidth player)

/-- Positive face drift forces some strictly positive lower partial. -/
theorem lowerBoxBoundary_minimum_pos_lower_partial
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hdrift : ∀ player, point player = lower player →
      0 < derivative (point - face player)) :
    ∃ player, point player = lower player ∧ 0 < derivative (Pi.single player 1) := by
  have hsigns := lowerBoxBoundary_minimum_partial_signs lower upper point potential
    derivative face hpoint hmin hdiff hwidth hdiagonal hfaceUpper hdrift
  by_contra hnone
  have hzero : ∀ player, point player = lower player →
      derivative (Pi.single player 1) = 0 := by
    intro player hbind
    exact le_antisymm (le_of_not_gt (fun hpos => hnone ⟨player, hbind, hpos⟩))
      ((hsigns player).1 hbind)
  obtain ⟨owner, howner⟩ := hpoint.2
  have hnonpos : derivative (point - face owner) ≤ 0 := by
    conv_lhs => rw [pi_eq_sum_univ' (point - face owner)]
    rw [map_sum]
    apply Finset.sum_nonpos
    intro player _
    rw [map_smul]
    change (point player - face owner player) * derivative (Pi.single player 1) ≤ 0
    by_cases hlower : point player = lower player
    · rw [hzero player hlower]
      simp
    · by_cases hupper : point player = upper player
      · exact mul_nonpos_of_nonneg_of_nonpos
          (by rw [hupper]; exact sub_nonneg.mpr (hfaceUpper owner player))
          ((hsigns player).2.2 hupper)
      · have hstrictLower : lower player < point player :=
          lt_of_le_of_ne (hpoint.1.1 player) (Ne.symm hlower)
        have hstrictUpper : point player < upper player :=
          lt_of_le_of_ne (hpoint.1.2 player) hupper
        rw [(hsigns player).2.1 hstrictLower hstrictUpper]
        simp
  exact (not_lt_of_ge hnonpos) (hdrift owner howner)

/-- The derivative points strictly upward toward every boxed target strictly
above all lower faces. Upper coordinates of the target may still bind. -/
theorem lowerBoxBoundary_minimum_derivative_toward_strictLower_pos
    (lower upper point : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) (face : ι → ι → ℝ)
    (hpoint : point ∈ lowerBoxBoundary lower upper)
    (hmin : IsMinOn potential (lowerBoxBoundary lower upper) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hwidth : ∀ player, lower player < upper player)
    (hdiagonal : ∀ player, face player player = lower player)
    (hfaceUpper : ∀ player other, face player other ≤ upper other)
    (hdrift : ∀ player, point player = lower player →
      0 < derivative (point - face player))
    (target : ι → ℝ) (htargetLower : ∀ player, lower player < target player)
    (htargetUpper : target ≤ upper) :
    0 < derivative (target - point) := by
  have hsigns := lowerBoxBoundary_minimum_partial_signs lower upper point potential
    derivative face hpoint hmin hdiff hwidth hdiagonal hfaceUpper hdrift
  obtain ⟨owner, howner, hpositive⟩ := lowerBoxBoundary_minimum_pos_lower_partial
    lower upper point potential derivative face hpoint hmin hdiff hwidth hdiagonal
    hfaceUpper hdrift
  conv_rhs => rw [pi_eq_sum_univ' (target - point)]
  rw [map_sum]
  apply Finset.sum_pos'
  · intro player _
    rw [map_smul]
    change 0 ≤ (target player - point player) * derivative (Pi.single player 1)
    by_cases hlower : point player = lower player
    · exact mul_nonneg (by rw [hlower]; exact (sub_pos.mpr (htargetLower player)).le)
        ((hsigns player).1 hlower)
    · by_cases hupper : point player = upper player
      · exact mul_nonneg_of_nonpos_of_nonpos
          (by rw [hupper]; exact sub_nonpos.mpr (htargetUpper player))
          ((hsigns player).2.2 hupper)
      · have hstrictLower : lower player < point player :=
          lt_of_le_of_ne (hpoint.1.1 player) (Ne.symm hlower)
        have hstrictUpper : point player < upper player :=
          lt_of_le_of_ne (hpoint.1.2 player) hupper
        rw [(hsigns player).2.1 hstrictLower hstrictUpper]
        simp
  · refine ⟨owner, Finset.mem_univ _, ?_⟩
    rw [map_smul]
    change 0 < (target owner - point owner) * derivative (Pi.single owner 1)
    rw [howner]
    exact mul_pos (sub_pos.mpr (htargetLower owner)) hpositive

end Math
