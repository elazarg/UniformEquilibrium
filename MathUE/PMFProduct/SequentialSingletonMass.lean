import MathUE.PMFProduct.SmallHazardExpectation

/-!
# Ordered singleton resolution of a Bernoulli row

Resolving simultaneous Bernoulli events in a fixed order leaves the no-event
probability unchanged. Each singleton gains nonnegative mass, whose total is
exactly the original collision mass. The division-free coordinate defect is
bounded by the coordinate hazard times total absorption. These are the row
estimates in Solan--Vieille 2002, Lemma 9; no conditional denominator is needed.
-/

noncomputable section

namespace Math.PMFProduct

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- First-event mass when Bernoulli coordinates are resolved in order. -/
def orderedSingletonMass (x : ι → ℝ) (owner : ι) : ℝ :=
  x owner * ∏ other ∈ Finset.univ.filter (fun other => other < owner), (1 - x other)

/-- Ordered singleton masses exhaust exactly the absorption probability. -/
theorem sum_orderedSingletonMass (x : ι → ℝ) :
    ∑ owner, orderedSingletonMass x owner = 1 - continueMass x := by
  have h := Finset.prod_one_sub_ordered (Finset.univ : Finset ι) x
  change continueMass x = 1 - ∑ owner, orderedSingletonMass x owner at h
  linarith

/-- Coordinate mass gained by resolving a collision in favor of its first owner. -/
theorem orderedSingletonMass_sub_coalitionMass_bounds
    (x : ι → ℝ) (h0 : ∀ who, 0 ≤ x who) (h1 : ∀ who, x who ≤ 1) (owner : ι) :
    0 ≤ orderedSingletonMass x owner - coalitionMass x {owner} ∧
      orderedSingletonMass x owner - coalitionMass x {owner} ≤
        x owner * (1 - continueMass x) := by
  let before := Finset.univ.filter (fun other : ι => other < owner)
  let after := Finset.univ.filter (fun other : ι => owner < other)
  let prefixContinue : ℝ := ∏ other ∈ before, (1 - x other)
  let suffix : ℝ := ∏ other ∈ after, (1 - x other)
  have hpartition : (Finset.univ : Finset ι).erase owner = before ∪ after := by
    ext other
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      before, after, Finset.mem_filter, true_and]
    exact ne_iff_lt_or_gt
  have hdisjoint : Disjoint before after := by
    apply Finset.disjoint_left.mpr
    intro other hbefore hafter
    exact (lt_asymm (Finset.mem_filter.mp hbefore).2) (Finset.mem_filter.mp hafter).2
  have hprefix0 : 0 ≤ prefixContinue :=
    Finset.prod_nonneg fun other _ => sub_nonneg.mpr (h1 other)
  have hprefix1 : prefixContinue ≤ 1 :=
    Finset.prod_le_one₀ (fun other _ => sub_nonneg.mpr (h1 other))
      (fun other _ => by linarith [h0 other])
  have hsuffix0 : 0 ≤ suffix :=
    Finset.prod_nonneg fun other _ => sub_nonneg.mpr (h1 other)
  have hsuffix1 : suffix ≤ 1 :=
    Finset.prod_le_one₀ (fun other _ => sub_nonneg.mpr (h1 other))
      (fun other _ => by linarith [h0 other])
  have hcoalition : coalitionMass x {owner} = x owner * prefixContinue * suffix := by
    rw [coalitionMass_singleton, hpartition, Finset.prod_union hdisjoint]
    dsimp [prefixContinue, suffix]
    ring
  have hfull : continueMass x = (1 - x owner) * prefixContinue * suffix := by
    unfold continueMass
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
      (fun other => 1 - x other) (Finset.mem_univ owner),
      hpartition, Finset.prod_union hdisjoint]
    dsimp [prefixContinue, suffix]
    ring
  have hfactor1 : (1 - x owner) * prefixContinue ≤ 1 := by
    calc
      (1 - x owner) * prefixContinue ≤ 1 * prefixContinue :=
        mul_le_mul_of_nonneg_right (by linarith [h0 owner]) hprefix0
      _ ≤ 1 := by simpa using hprefix1
  have hfullSuffix : continueMass x ≤ suffix := by
    rw [hfull]
    exact mul_le_of_le_one_left hsuffix0 hfactor1
  have hdefect : orderedSingletonMass x owner - coalitionMass x {owner} =
      x owner * prefixContinue * (1 - suffix) := by
    rw [hcoalition]
    change x owner * prefixContinue - x owner * prefixContinue * suffix = _
    ring
  rw [hdefect]
  refine ⟨mul_nonneg (mul_nonneg (h0 owner) hprefix0) (sub_nonneg.mpr hsuffix1), ?_⟩
  calc
    x owner * prefixContinue * (1 - suffix) ≤ x owner * (1 - suffix) := by
      have h := mul_le_of_le_one_right
        (mul_nonneg (h0 owner) (sub_nonneg.mpr hsuffix1)) hprefix1
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    _ ≤ x owner * (1 - continueMass x) :=
      mul_le_mul_of_nonneg_left (by linarith) (h0 owner)

/-- The total singleton gain is exactly the mass of simultaneous events. -/
theorem sum_orderedSingletonMass_sub_coalitionMass (x : ι → ℝ) :
    ∑ owner, (orderedSingletonMass x owner - coalitionMass x {owner}) =
      collisionMass x := by
  rw [Finset.sum_sub_distrib, sum_orderedSingletonMass]
  have h := singletonMass_add_collisionMass x
  unfold singletonMass at h
  linarith

/-- Small individual hazards bound collision mass relative to absorption,
without any lower bound on the absorption denominator. -/
theorem collisionMass_le_card_mul_maxHazard_mul_absorption
    (x : ι → ℝ) (h0 : ∀ who, 0 ≤ x who) (h1 : ∀ who, x who ≤ 1)
    {ε : ℝ} (hsmall : ∀ who, x who ≤ ε) :
    collisionMass x ≤ (Fintype.card ι : ℝ) * ε * (1 - continueMass x) := by
  have habsorption0 := sub_nonneg.mpr (continueMass_le_one h0 h1)
  rw [← sum_orderedSingletonMass_sub_coalitionMass]
  calc
    (∑ owner, (orderedSingletonMass x owner - coalitionMass x {owner})) ≤
        ∑ _owner : ι, ε * (1 - continueMass x) := by
      apply Finset.sum_le_sum
      intro owner _
      exact (orderedSingletonMass_sub_coalitionMass_bounds x h0 h1 owner).2.trans
        (mul_le_mul_of_nonneg_right (hsmall owner) habsorption0)
    _ = (Fintype.card ι : ℝ) * ε * (1 - continueMass x) := by simp; ring

/-- Expected reward after resolving the Bernoulli coordinates in order.
The continuation value is used precisely when no coordinate acts. -/
def orderedSingletonExpectation
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ) : ℝ :=
  continueMass x * tail + ∑ owner, orderedSingletonMass x owner * terminal {owner}

/-- Exact reward defect of ordered resolution: gained singleton mass minus
the rewards of the simultaneous outcomes that have been resolved. -/
theorem orderedSingletonExpectation_sub_smallHazardExpectation_eq
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ) :
    orderedSingletonExpectation terminal tail x - smallHazardExpectation terminal tail x =
      (∑ owner, (orderedSingletonMass x owner - coalitionMass x {owner}) *
        terminal {owner}) -
      ∑ coalition ∈ Finset.univ.filter (fun coalition : Finset ι => 2 ≤ coalition.card),
        coalitionMass x coalition * terminal coalition := by
  have hcanonical := smallHazardExpectation_sub_tail_sub_linearization_eq terminal tail x
  have hlinear : smallHazardLinearization terminal tail x =
      (∑ owner, x owner * terminal {owner}) - (∑ owner, x owner) * tail := by
    unfold smallHazardLinearization
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  have hactual : (∑ owner, (coalitionMass x {owner} - x owner) * terminal {owner}) =
      (∑ owner, coalitionMass x {owner} * terminal {owner}) -
        ∑ owner, x owner * terminal {owner} := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  have hdefect : (∑ owner, (orderedSingletonMass x owner - coalitionMass x {owner}) *
      terminal {owner}) = (∑ owner, orderedSingletonMass x owner * terminal {owner}) -
        ∑ owner, coalitionMass x {owner} * terminal {owner} := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [hlinear, hactual] at hcanonical
  rw [hdefect]
  unfold orderedSingletonExpectation
  nlinarith

/-- Ordered resolution changes a bounded reward by at most twice its bound
times collision mass. The continuation value cancels exactly. -/
theorem abs_orderedSingletonExpectation_sub_smallHazardExpectation_le
    (terminal : Finset ι → ℝ) (tail : ℝ) (x : ι → ℝ)
    (h0 : ∀ who, 0 ≤ x who) (h1 : ∀ who, x who ≤ 1)
    {M : ℝ} (hterminal : ∀ coalition, coalition.Nonempty → |terminal coalition| ≤ M) :
    |orderedSingletonExpectation terminal tail x - smallHazardExpectation terminal tail x| ≤
      2 * M * collisionMass x := by
  have hsingle : |∑ owner,
      (orderedSingletonMass x owner - coalitionMass x {owner}) * terminal {owner}| ≤
      M * collisionMass x := by
    calc
      |_| ≤ ∑ owner,
          |(orderedSingletonMass x owner - coalitionMass x {owner}) * terminal {owner}| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ owner, (orderedSingletonMass x owner - coalitionMass x {owner}) * M := by
        apply Finset.sum_le_sum
        intro owner _
        rw [abs_mul, abs_of_nonneg
          (orderedSingletonMass_sub_coalitionMass_bounds x h0 h1 owner).1]
        exact mul_le_mul_of_nonneg_left
          (hterminal {owner} (Finset.singleton_nonempty _))
          (orderedSingletonMass_sub_coalitionMass_bounds x h0 h1 owner).1
      _ = M * collisionMass x := by
        rw [← Finset.sum_mul, sum_orderedSingletonMass_sub_coalitionMass, mul_comm]
  have hcollision : |∑ coalition ∈ Finset.univ.filter
      (fun coalition : Finset ι => 2 ≤ coalition.card),
      coalitionMass x coalition * terminal coalition| ≤ M * collisionMass x := by
    calc
      |_| ≤ ∑ coalition ∈ Finset.univ.filter
          (fun coalition : Finset ι => 2 ≤ coalition.card),
          |coalitionMass x coalition * terminal coalition| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ coalition ∈ Finset.univ.filter
          (fun coalition : Finset ι => 2 ≤ coalition.card), coalitionMass x coalition * M := by
        apply Finset.sum_le_sum
        intro coalition hcoalition
        rw [abs_mul, abs_of_nonneg (coalitionMass_nonneg x h0 h1 coalition)]
        apply mul_le_mul_of_nonneg_left _ (coalitionMass_nonneg x h0 h1 coalition)
        apply hterminal coalition
        apply Finset.card_pos.mp
        have hcard := (Finset.mem_filter.mp hcoalition).2
        omega
      _ = M * collisionMass x := by rw [← Finset.sum_mul]; simp [collisionMass, mul_comm]
  rw [orderedSingletonExpectation_sub_smallHazardExpectation_eq]
  exact (abs_sub _ _).trans ((add_le_add hsingle hcollision).trans_eq (by ring))

end Math.PMFProduct
