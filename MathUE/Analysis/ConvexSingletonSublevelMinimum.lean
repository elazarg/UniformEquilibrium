import MathUE.Analysis.LowerBoxDerivativeCone

/-! # A singleton-sublevel minimum supports its whole convex region

The minimum is on the sublevel part of the region, not on the region itself.
The segment argument and the lower-box partial signs cover all target directions.
-/

noncomputable section

namespace Math

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem convex_singletonSublevel_minimum_apply_sub_nonneg
    (lower upper point target : ι → ℝ) (region : Set (ι → ℝ))
    (hconvex : Convex ℝ region) (hpointRegion : point ∈ region) (htargetRegion : target ∈ region)
    (hpointBox : point ∈ Icc lower upper) (htargetUpper : target ≤ upper)
    (potential : (ι → ℝ) → ℝ) (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hmin : IsMinOn potential (region ∩ {value | ∃ player, value player ≤ lower player}) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hsigns : ∀ player,
      (point player = lower player → 0 ≤ derivative (Pi.single player 1)) ∧
      (lower player < point player → point player < upper player →
        derivative (Pi.single player 1) = 0) ∧
      (point player = upper player → derivative (Pi.single player 1) ≤ 0)) :
    0 ≤ derivative (target - point) := by
  classical
  by_cases htargetBinding : ∀ player, point player = lower player → lower player ≤ target player
  · exact lowerBox_partial_signs_apply_sub_nonneg lower upper point target derivative
      hpointBox hsigns htargetBinding htargetUpper
  · simp only [not_forall, not_le] at htargetBinding
    obtain ⟨player, hbind, hbelow⟩ := htargetBinding
    have hsegment : segment ℝ point target ⊆
        region ∩ {value | ∃ player, value player ≤ lower player} := by
      apply (segment_subset_iff ℝ).mpr
      intro a b ha hb hab
      refine ⟨hconvex hpointRegion htargetRegion ha hb hab, player, ?_⟩
      change a * point player + b * target player ≤ lower player
      calc
        a * point player + b * target player ≤ a * lower player + b * lower player :=
          add_le_add (by rw [hbind]) (mul_le_mul_of_nonneg_left hbelow.le hb)
        _ = lower player := by rw [← add_mul, hab, one_mul]
    have hlocal : IsLocalMinOn potential
        (region ∩ {value | ∃ player, value player ≤ lower player}) point :=
      Filter.mem_of_superset self_mem_nhdsWithin hmin
    exact hlocal.hasFDerivWithinAt_nonneg hdiff.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset hsegment)

end Math
