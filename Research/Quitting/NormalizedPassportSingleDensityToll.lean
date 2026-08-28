/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NormalizedPassportMinimizer

/-!
# Single-density normalized-passport tolls

A common positive proportionality between actual gain and marked mass makes
the two normalized-passport inequalities equivalent.  At a minimizer of that
single slice, the exact prefix ledger gives an arbitrary-root tent bound and
the corrected local alternative: zero slack, or positive slack together with
a linear toll on its displayed absorption ball.

The family and proportionality are supplied here.  This module constructs no
quitting-game source, regenerated family, or terminal consumer.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingMarkedPairDecoratedFamily

variable (family : QuittingMarkedPairDecoratedFamily reward)

/-- A proportionality verified on every supplied base row extends to the
whole closed arbitrary-prefix carrier. -/
theorem actualGain_eq_gap_mul_markedMass_of_base
    (gap : ℝ)
    (hbase : ∀ rank,
      (family.baseDecoration rank).actualGain =
        gap * (family.baseDecoration rank).markedMass)
    {point : QuittingMarkedPairDecoration ι}
    (hpoint : point ∈ family.prefixOrbitCarrier) :
    point.actualGain = gap * point.markedMass := by
  have hclosed : IsClosed {candidate : QuittingMarkedPairDecoration ι |
      candidate.actualGain = gap * candidate.markedMass} := by
    exact isClosed_eq (continuous_snd.comp continuous_snd)
      (continuous_const.mul (continuous_fst.comp continuous_snd))
  apply closure_minimal (s := family.rawPrefixOrbit) _ hclosed hpoint
  rintro candidate ⟨rank, roots, rfl⟩
  change (family.rawDecoration rank roots).actualGain =
    gap * (family.rawDecoration rank roots).markedMass
  rw [family.rawDecoration_actualGain_eq_prefixSurvival_mul,
    family.rawDecoration_markedMass_eq_prefixSurvival_mul, hbase rank]
  ring

end QuittingMarkedPairDecoratedFamily

/-- A minimizer of a normalized-passport slice whose gain coordinate is one
fixed positive multiple of its marked-mass coordinate throughout the closed
prefix carrier. -/
structure QuittingSingleDensityPassportMinimizer
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι) where
  gap : ℝ
  density : ℝ
  gap_pos : 0 < gap
  density_pos : 0 < density
  point : QuittingMarkedPairDecoration ι
  carrier_identity : ∀ candidate ∈ family.prefixOrbitCarrier,
    candidate.actualGain = gap * candidate.markedMass
  point_mem : point ∈
    family.normalizedPassportSlice minimum density (gap * density)
  point_minimal : ∀ candidate ∈
      family.normalizedPassportSlice minimum density (gap * density),
    point.wholeDebt ≤ candidate.wholeDebt
  pointDebt_pos : 0 < point.wholeDebt

namespace QuittingSingleDensityPassportMinimizer

variable {family : QuittingMarkedPairDecoratedFamily reward}
variable {minimum : QuittingTerminalSemanticPair ι}

/-- Excess marked mass above the one-density constraint. -/
def slack (data : QuittingSingleDensityPassportMinimizer family minimum) : ℝ :=
  data.point.markedMass - data.density * data.point.wholeDebt

/-- The displayed minimizer has nonnegative density slack. -/
theorem slack_nonneg
    (data : QuittingSingleDensityPassportMinimizer family minimum) :
    0 ≤ data.slack := by
  exact sub_nonneg.mpr data.point_mem.2.2.1

/-- The marked mass at a positive-debt single-density minimizer is positive. -/
theorem point_markedMass_pos
    (data : QuittingSingleDensityPassportMinimizer family minimum) :
    0 < data.point.markedMass := by
  exact (mul_pos data.density_pos data.pointDebt_pos).trans_le
    data.point_mem.2.2.1

/-- The gain coordinate of the selected point has the same fixed density. -/
theorem point_actualGain_eq
    (data : QuittingSingleDensityPassportMinimizer family minimum) :
    data.point.actualGain = data.gap * data.point.markedMass :=
  data.carrier_identity data.point data.point_mem.1

/-- On the proportional carrier, the gain constraint is exactly the marked
mass constraint. -/
theorem gain_constraint_iff_mass_constraint
    (data : QuittingSingleDensityPassportMinimizer family minimum)
    {candidate : QuittingMarkedPairDecoration ι}
    (hcarrier : candidate ∈ family.prefixOrbitCarrier) :
    (data.gap * data.density) * candidate.wholeDebt ≤ candidate.actualGain ↔
      data.density * candidate.wholeDebt ≤ candidate.markedMass := by
  rw [data.carrier_identity candidate hcarrier]
  constructor
  · intro hgain
    nlinarith [data.gap_pos]
  · intro hmass
    calc
      (data.gap * data.density) * candidate.wholeDebt =
          data.gap * (data.density * candidate.wholeDebt) := by ring
      _ ≤ data.gap * candidate.markedMass :=
        mul_le_mul_of_nonneg_left hmass data.gap_pos.le

/-- Exact arbitrary-root feasibility criterion for the one-density slice. -/
theorem prefixMap_mem_slice_iff
    (data : QuittingSingleDensityPassportMinimizer family minimum)
    (root : ι → PMF Bool) :
    family.prefixMap root data.point ∈
        family.normalizedPassportSlice minimum data.density
          (data.gap * data.density) ↔
      data.density *
          quittingRootTotalNashDefect reward data.point.whole.1.2 root ≤
        quittingStationaryContinueMass root * data.slack := by
  have hcarrier := family.prefixMap_mem_carrier root data.point_mem.1
  have htail : (family.prefixMap root data.point).tailDebt =
      quittingTerminalSemanticDebtSum minimum := by
    simpa [QuittingMarkedPairDecoration.tailDebt,
      QuittingMarkedPairDecoratedFamily.prefixMap] using data.point_mem.2.1
  rw [show family.prefixMap root data.point ∈
      family.normalizedPassportSlice minimum data.density
        (data.gap * data.density) ↔
      data.density * (family.prefixMap root data.point).wholeDebt ≤
        (family.prefixMap root data.point).markedMass by
    constructor
    · exact fun hpoint ↦ hpoint.2.2.1
    · intro hmass
      exact ⟨hcarrier, htail, hmass,
        (data.gain_constraint_iff_mass_constraint hcarrier).2 hmass⟩]
  rw [family.prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect]
  change data.density *
      (quittingStationaryContinueMass root * data.point.wholeDebt +
        quittingRootTotalNashDefect reward data.point.whole.1.2 root) ≤
      quittingStationaryContinueMass root * data.point.markedMass ↔ _
  unfold slack
  constructor <;> intro h <;> nlinarith

/-- The arbitrary-root global tent bound.  It remains valid at zero slack:
then the second tent arm is zero and no positive toll is inferred. -/
theorem rootDefect_ge_min_tent
    (data : QuittingSingleDensityPassportMinimizer family minimum)
    (root : ι → PMF Bool) :
    min
        (data.point.wholeDebt * quittingRootAbsorptionMass root)
        (quittingStationaryContinueMass root * data.slack / data.density) ≤
      quittingRootTotalNashDefect reward data.point.whole.1.2 root := by
  let defect := quittingRootTotalNashDefect reward data.point.whole.1.2 root
  by_cases hfeasible : family.prefixMap root data.point ∈
      family.normalizedPassportSlice minimum data.density
        (data.gap * data.density)
  · have hminimal := data.point_minimal _ hfeasible
    have hledger := family.prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect
      root data.point
    have hfirst : data.point.wholeDebt * quittingRootAbsorptionMass root ≤
        defect := by
      change data.point.wholeDebt *
          (1 - quittingStationaryContinueMass root) ≤ defect
      change data.point.wholeDebt ≤ (family.prefixMap root data.point).wholeDebt
        at hminimal
      rw [hledger] at hminimal
      dsimp only [defect]
      nlinarith
    exact (min_le_left _ _).trans hfirst
  · have hinfeasible : ¬data.density * defect ≤
        quittingStationaryContinueMass root * data.slack := by
      intro hcriterion
      exact hfeasible ((data.prefixMap_mem_slice_iff root).2 hcriterion)
    have hsecond :
        quittingStationaryContinueMass root * data.slack / data.density ≤
          defect := by
      apply (div_le_iff₀ data.density_pos).2
      simpa only [mul_comm] using le_of_not_ge hinfeasible
    exact (min_le_right _ _).trans hsecond

/-- Positive slack gives the sharp linear absorption toll throughout the
displayed small-absorption ball. -/
theorem rootDefect_ge_debt_mul_absorption_of_le_slack_div_mass
    (data : QuittingSingleDensityPassportMinimizer family minimum)
    (hslack : 0 < data.slack)
    (root : ι → PMF Bool)
    (habsorption : quittingRootAbsorptionMass root ≤
      data.slack / data.point.markedMass) :
    data.point.wholeDebt * quittingRootAbsorptionMass root ≤
      quittingRootTotalNashDefect reward data.point.whole.1.2 root := by
  let absorption := quittingRootAbsorptionMass root
  let continuation := quittingStationaryContinueMass root
  let defect := quittingRootTotalNashDefect reward data.point.whole.1.2 root
  have hmassProduct : absorption * data.point.markedMass ≤ data.slack := by
    exact (le_div_iff₀ data.point_markedMass_pos).mp habsorption
  by_contra hnot
  have hdefectLt : defect < data.point.wholeDebt * absorption :=
    lt_of_not_ge hnot
  have habsorptionEq : absorption = 1 - continuation := rfl
  have hmassEq : data.point.markedMass =
      data.density * data.point.wholeDebt + data.slack := by
    unfold slack
    ring
  have hcriterion : data.density * defect ≤ continuation * data.slack := by
    rw [hmassEq] at hmassProduct
    nlinarith [data.density_pos, data.pointDebt_pos, hslack,
      quittingRootAbsorptionMass_nonneg root,
      quittingStationaryContinueMass_nonneg root]
  have hfeasible := (data.prefixMap_mem_slice_iff root).2 hcriterion
  have hminimal := data.point_minimal _ hfeasible
  have hledger := family.prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect
    root data.point
  change data.point.wholeDebt ≤ (family.prefixMap root data.point).wholeDebt
    at hminimal
  rw [hledger] at hminimal
  dsimp only [defect, absorption, continuation] at hdefectLt hminimal
  unfold quittingRootAbsorptionMass at hdefectLt
  nlinarith

/-- Corrected local alternative: saturation, or positive slack together with
the linear toll.  No false exclusive dichotomy is asserted. -/
theorem slack_eq_zero_or_positive_with_local_toll
    (data : QuittingSingleDensityPassportMinimizer family minimum) :
    data.slack = 0 ∨
      (0 < data.slack ∧
        ∀ root : ι → PMF Bool,
          quittingRootAbsorptionMass root ≤
              data.slack / data.point.markedMass →
            data.point.wholeDebt * quittingRootAbsorptionMass root ≤
              quittingRootTotalNashDefect reward data.point.whole.1.2 root) := by
  rcases data.slack_nonneg.eq_or_lt with hzero | hpositive
  · exact Or.inl hzero.symm
  · exact Or.inr ⟨hpositive, fun root hroot ↦
      data.rootDefect_ge_debt_mul_absorption_of_le_slack_div_mass
        hpositive root hroot⟩

/-- At canonical half-density saturation, marked mass, gain, and debt have
the exact common ratio advertised by the scalar passport. -/
theorem saturation_ratio
    (data : QuittingSingleDensityPassportMinimizer family minimum)
    (reference : QuittingMarkedPairDecoration ι)
    (hreference : reference ∈ family.prefixOrbitCarrier)
    (hreferenceDebt : 0 < reference.wholeDebt)
    (hreferenceMass : 0 < reference.markedMass)
    (hdensity : data.density =
      reference.markedMass / (2 * reference.wholeDebt))
    (hsaturation : data.slack = 0) :
    data.point.markedMass / reference.markedMass =
        data.point.actualGain / reference.actualGain ∧
      data.point.actualGain / reference.actualGain =
        data.point.wholeDebt / (2 * reference.wholeDebt) := by
  have hpointMass : data.point.markedMass =
      data.density * data.point.wholeDebt := by
    unfold slack at hsaturation
    linarith
  have hpointGain := data.point_actualGain_eq
  have hreferenceGain := data.carrier_identity reference hreference
  have hgapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  have hrefDebtNe : reference.wholeDebt ≠ 0 := ne_of_gt hreferenceDebt
  have hrefMassNe : reference.markedMass ≠ 0 := ne_of_gt hreferenceMass
  constructor
  · rw [hpointGain, hreferenceGain]
    field_simp [hgapNe, hrefMassNe]
  · rw [hpointGain, hreferenceGain, hpointMass, hdensity]
    field_simp [hgapNe, hrefDebtNe, hrefMassNe]

end QuittingSingleDensityPassportMinimizer

end GameTheory
