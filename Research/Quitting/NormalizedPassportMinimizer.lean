/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NormalizedPassportPrefixOrbit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedVariational
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CapDebtBellmanReduction
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Normalized-passport minimizers

The arbitrary-prefix orbit carrier from
`Research.Quitting.NormalizedPassportPrefixOrbit` is compact.  Intersecting it
with a fixed minimum tail fibre and two homogeneous density inequalities gives
a compact normalized slice.  A positive-debt slice minimizer admits only the
all-Continue exact cap--Nash root.

This minimizer belongs to the enlarged arbitrary-prefix closure.  It is not
asserted to belong to, or to be attained by, the original supplied cluster.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingMarkedPairDecoration

def wholeDebt (point : QuittingMarkedPairDecoration ι) : ℝ :=
  quittingTerminalSemanticDebtSum point.whole.1

def tailDebt (point : QuittingMarkedPairDecoration ι) : ℝ :=
  quittingTerminalSemanticDebtSum point.tail.1

omit [DecidableEq ι] in
theorem continuous_wholeDebt :
    Continuous (wholeDebt : QuittingMarkedPairDecoration ι → ℝ) := by
  unfold wholeDebt QuittingMarkedPairDecoration.whole
  have hprojection : Continuous
      (fun point : QuittingMarkedPairDecoration ι => point.1.1.1) := by
    fun_prop
  exact continuous_quittingTerminalSemanticDebtSum.comp hprojection

omit [DecidableEq ι] in
theorem continuous_tailDebt :
    Continuous (tailDebt : QuittingMarkedPairDecoration ι → ℝ) := by
  unfold tailDebt QuittingMarkedPairDecoration.tail
  have hprojection : Continuous
      (fun point : QuittingMarkedPairDecoration ι => point.1.2.1) := by
    fun_prop
  exact continuous_quittingTerminalSemanticDebtSum.comp hprojection

end QuittingMarkedPairDecoration

namespace QuittingMarkedPairDecoratedFamily

variable (family : QuittingMarkedPairDecoratedFamily reward)

/-- Canonical compact box containing every raw decorated descendant. -/
def prefixOrbitAmbient (_family : QuittingMarkedPairDecoratedFamily reward) :
    Set (QuittingMarkedPairDecoration ι) :=
  (quittingTerminalSemanticLawCarrier reward ×ˢ
      quittingTerminalSemanticLawCarrier reward) ×ˢ
    (Set.Icc 0 1 ×ˢ Set.Icc 0 (2 * quittingRewardBound reward))

theorem prefixOrbitAmbient_isCompact :
    IsCompact family.prefixOrbitAmbient := by
  exact ((quittingTerminalSemanticLawCarrier_isCompact reward).prod
    (quittingTerminalSemanticLawCarrier_isCompact reward)).prod
      (isCompact_Icc.prod isCompact_Icc)

theorem rawDecoration_actualGain_nonneg (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    0 ≤ (family.rawDecoration rank roots).actualGain := by
  induction roots with
  | nil => simpa [rawDecoration, baseDecoration] using family.actualGain_pos rank |>.le
  | cons root roots ih =>
      rw [rawDecoration_cons]
      exact mul_nonneg (quittingStationaryContinueMass_nonneg root) ih

/-- Every raw decoration lies in the canonical compact box. -/
theorem rawDecoration_mem_ambient (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    family.rawDecoration rank roots ∈ family.prefixOrbitAmbient := by
  have hwhole := quittingTerminalSemanticLawPoint_mem_carrier reward
    (family.descendantProfile rank roots)
  have htail := quittingTerminalSemanticLawPoint_mem_carrier reward
    (quittingAllContinueProfileSpine reward (family.profile rank)
      (family.mark rank + 1))
  have hmassNonneg := quittingStageCoalitionMass_nonneg reward
    (family.descendantProfile rank roots) (family.descendantMark rank roots)
      family.terminal
  have hmassLe := (quittingStageCoalitionMass_le_liveMass reward
    (family.descendantProfile rank roots) (family.descendantMark rank roots)
      family.terminal).trans
        (quittingLiveMass_le_one reward (family.descendantProfile rank roots)
          (family.descendantMark rank roots))
  let endpointValue := quittingTerminalPayoff reward
    (family.descendantProfile rank roots) family.gainMover
  let sourceValue := quittingTerminalPayoff reward
    (family.descendantSourceProfile rank roots) family.gainMover
  have hendpoint := abs_quittingTerminalPayoff_le_quittingRewardBound reward
    (family.descendantProfile rank roots) family.gainMover
  have hsource := abs_quittingTerminalPayoff_le_quittingRewardBound reward
    (family.descendantSourceProfile rank roots) family.gainMover
  have hgainLe : endpointValue - sourceValue ≤
      2 * quittingRewardBound reward := by
    have hfirst : endpointValue ≤ quittingRewardBound reward :=
      le_trans (le_abs_self endpointValue) hendpoint
    have hsourceLower : -quittingRewardBound reward ≤ sourceValue :=
      (abs_le.mp hsource).1
    have hsecond : -sourceValue ≤ quittingRewardBound reward := by
      linarith
    dsimp only [endpointValue, sourceValue] at hfirst hsecond ⊢
    linarith
  have hgainNonneg : 0 ≤ endpointValue - sourceValue := by
    dsimp only [endpointValue, sourceValue]
    rw [← family.rawDecoration_actualGain_eq rank roots]
    exact family.rawDecoration_actualGain_nonneg rank roots
  rw [prefixOrbitAmbient]
  change ((family.rawDecoration rank roots).whole ∈
        quittingTerminalSemanticLawCarrier reward ∧
      (family.rawDecoration rank roots).tail ∈
        quittingTerminalSemanticLawCarrier reward) ∧
    ((family.rawDecoration rank roots).markedMass ∈ Set.Icc 0 1 ∧
      (family.rawDecoration rank roots).actualGain ∈
        Set.Icc 0 (2 * quittingRewardBound reward))
  rw [family.rawDecoration_whole_eq, family.rawDecoration_tail_eq,
    family.rawDecoration_markedMass_eq, family.rawDecoration_actualGain_eq]
  exact ⟨⟨hwhole, htail⟩,
    ⟨⟨hmassNonneg, hmassLe⟩,
      ⟨hgainNonneg, hgainLe⟩⟩⟩

/-- The closed arbitrary-prefix orbit carrier is compact. -/
theorem prefixOrbitCarrier_isCompact :
    IsCompact family.prefixOrbitCarrier := by
  apply family.prefixOrbitAmbient_isCompact.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro point ⟨rank, roots, rfl⟩
    exact family.rawDecoration_mem_ambient rank roots
  · exact family.prefixOrbitAmbient_isCompact.isClosed

/-- The closed orbit carrier remains inside the canonical ambient box. -/
theorem prefixOrbitCarrier_subset_ambient :
    family.prefixOrbitCarrier ⊆ family.prefixOrbitAmbient := by
  apply closure_minimal
  · rintro point ⟨rank, roots, rfl⟩
    exact family.rawDecoration_mem_ambient rank roots
  · exact family.prefixOrbitAmbient_isCompact.isClosed

/-- Projection of a joint semantic/law carrier point remains in the ordinary
semantic carrier. -/
theorem semantic_mem_carrier_of_law_mem_carrier
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    point.1 ∈ quittingTerminalSemanticCarrier reward := by
  unfold quittingTerminalSemanticLawCarrier at hpoint
  unfold quittingTerminalSemanticCarrier
  apply map_mem_closure continuous_fst hpoint
  rintro candidate ⟨profile, rfl⟩
  exact ⟨profile, rfl⟩

/-- The whole semantic coordinate of every decorated carrier point is a
genuine semantic-carrier point. -/
theorem whole_semantic_mem_carrier
    {point : QuittingMarkedPairDecoration ι}
    (hpoint : point ∈ family.prefixOrbitCarrier) :
    point.whole.1 ∈ quittingTerminalSemanticCarrier reward := by
  have hambient := family.prefixOrbitCarrier_subset_ambient hpoint
  exact semantic_mem_carrier_of_law_mem_carrier point.whole hambient.1.1

/-- Fixed-tail normalized passport slice. -/
def normalizedPassportSlice
    (minimum : QuittingTerminalSemanticPair ι) (massDensity gainDensity : ℝ) :
    Set (QuittingMarkedPairDecoration ι) :=
  family.prefixOrbitCarrier ∩
    {point | point.tailDebt = quittingTerminalSemanticDebtSum minimum ∧
      massDensity * point.wholeDebt ≤ point.markedMass ∧
      gainDensity * point.wholeDebt ≤ point.actualGain}

theorem normalizedPassportSlice_isClosed
    (minimum : QuittingTerminalSemanticPair ι) (massDensity gainDensity : ℝ) :
    IsClosed (family.normalizedPassportSlice minimum massDensity gainDensity) := by
  have htail : IsClosed {point : QuittingMarkedPairDecoration ι |
      point.tailDebt = quittingTerminalSemanticDebtSum minimum} :=
    isClosed_eq QuittingMarkedPairDecoration.continuous_tailDebt continuous_const
  have hmass : IsClosed {point : QuittingMarkedPairDecoration ι |
      massDensity * point.wholeDebt ≤ point.markedMass} :=
    isClosed_le (continuous_const.mul
      QuittingMarkedPairDecoration.continuous_wholeDebt)
        (continuous_fst.comp continuous_snd)
  have hgain : IsClosed {point : QuittingMarkedPairDecoration ι |
      gainDensity * point.wholeDebt ≤ point.actualGain} :=
    isClosed_le (continuous_const.mul
      QuittingMarkedPairDecoration.continuous_wholeDebt)
        (continuous_snd.comp continuous_snd)
  exact isClosed_closure.inter (htail.inter (hmass.inter hgain))

theorem normalizedPassportSlice_isCompact
    (minimum : QuittingTerminalSemanticPair ι) (massDensity gainDensity : ℝ) :
    IsCompact (family.normalizedPassportSlice minimum massDensity gainDensity) := by
  apply family.prefixOrbitCarrier_isCompact.of_isClosed_subset
    (family.normalizedPassportSlice_isClosed minimum massDensity gainDensity)
  intro point hpoint
  exact hpoint.1

/-- Simultaneous decorated limit data used only to prove that a normalized
slice is nonempty.  No minimizer is supplied here. -/
structure ConvergentPassport
    (minimum : QuittingTerminalSemanticPair ι) where
  limit : QuittingMarkedPairDecoration ι
  tendsto_base : Tendsto family.baseDecoration atTop (nhds limit)
  tailDebt_eq : limit.tailDebt = quittingTerminalSemanticDebtSum minimum
  wholeDebt_pos : 0 < limit.wholeDebt
  markedMass_pos : 0 < limit.markedMass
  actualGain_pos : 0 < limit.actualGain

namespace ConvergentPassport

variable {family : QuittingMarkedPairDecoratedFamily reward}
variable {minimum : QuittingTerminalSemanticPair ι}

/-- The simultaneous supplied-family limit lies in the enlarged orbit
carrier because the empty word is part of the raw orbit. -/
theorem limit_mem_prefixOrbitCarrier
    (passport : ConvergentPassport family minimum) :
    passport.limit ∈ family.prefixOrbitCarrier := by
  rw [prefixOrbitCarrier, mem_closure_iff_seq_limit]
  refine ⟨family.baseDecoration, ?_, passport.tendsto_base⟩
  intro rank
  exact ⟨rank, [], (family.rawDecoration_nil rank).symm⟩

/-- Strict density inequalities put the supplied limit in the normalized
slice. -/
theorem limit_mem_normalizedPassportSlice
    (passport : ConvergentPassport family minimum)
    (massDensity gainDensity : ℝ)
    (hmass : massDensity * passport.limit.wholeDebt <
      passport.limit.markedMass)
    (hgain : gainDensity * passport.limit.wholeDebt <
      passport.limit.actualGain) :
    passport.limit ∈
      family.normalizedPassportSlice minimum massDensity gainDensity := by
  exact ⟨passport.limit_mem_prefixOrbitCarrier,
    passport.tailDebt_eq, hmass.le, hgain.le⟩

end ConvergentPassport

/-- Whole debt attains a minimum on every nonempty normalized slice. -/
theorem exists_minimum_normalizedPassportSlice
    (minimum : QuittingTerminalSemanticPair ι) (massDensity gainDensity : ℝ)
    (hnonempty :
      (family.normalizedPassportSlice minimum massDensity gainDensity).Nonempty) :
    ∃ point ∈ family.normalizedPassportSlice minimum massDensity gainDensity,
      ∀ candidate ∈ family.normalizedPassportSlice minimum massDensity gainDensity,
        point.wholeDebt ≤ candidate.wholeDebt := by
  exact (family.normalizedPassportSlice_isCompact minimum massDensity gainDensity)
    |>.exists_isMinOn hnonempty
      QuittingMarkedPairDecoration.continuous_wholeDebt.continuousOn

/-- Exact arbitrary-root cap-debt account on the whole decorated coordinate. -/
theorem prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect
    (root : ι → PMF Bool) (point : QuittingMarkedPairDecoration ι) :
    (family.prefixMap root point).wholeDebt =
      quittingStationaryContinueMass root * point.wholeDebt +
        quittingRootTotalNashDefect reward point.whole.1.2 root := by
  unfold QuittingMarkedPairDecoration.wholeDebt
    QuittingMarkedPairDecoration.whole prefixMap
  rw [quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect]
  rfl

/-- Exact cap--Nash prefixing preserves the homogeneous normalized slice.
This statement is deliberately about the closed slice, not about finite raw
rows, whose positive finite-source defect can break the density inequalities. -/
theorem prefixMap_mem_normalizedPassportSlice_of_isZeroNash
    (minimum : QuittingTerminalSemanticPair ι) (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.whole.1.2 0 root) :
    family.prefixMap root point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity := by
  rcases hpoint with ⟨hcarrier, htail, hmass, hgain⟩
  have hdefect : quittingRootTotalNashDefect reward point.whole.1.2 root = 0 :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward point.whole.1.2 root).1 hnash
  have hdebt : (family.prefixMap root point).wholeDebt =
      quittingStationaryContinueMass root * point.wholeDebt := by
    rw [family.prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect,
      hdefect, add_zero]
  have hcontinue := quittingStationaryContinueMass_nonneg root
  refine ⟨family.prefixMap_mem_carrier root hcarrier, ?_, ?_, ?_⟩
  · simpa [QuittingMarkedPairDecoration.tailDebt, prefixMap] using htail
  · rw [hdebt]
    change massDensity *
        (quittingStationaryContinueMass root * point.wholeDebt) ≤
      quittingStationaryContinueMass root * point.markedMass
    calc
      massDensity *
          (quittingStationaryContinueMass root * point.wholeDebt) =
          quittingStationaryContinueMass root *
            (massDensity * point.wholeDebt) := by ring
      _ ≤ quittingStationaryContinueMass root * point.markedMass :=
        mul_le_mul_of_nonneg_left hmass hcontinue
  · rw [hdebt]
    change gainDensity *
        (quittingStationaryContinueMass root * point.wholeDebt) ≤
      quittingStationaryContinueMass root * point.actualGain
    calc
      gainDensity *
          (quittingStationaryContinueMass root * point.wholeDebt) =
          quittingStationaryContinueMass root *
            (gainDensity * point.wholeDebt) := by ring
      _ ≤ quittingStationaryContinueMass root * point.actualGain :=
        mul_le_mul_of_nonneg_left hgain hcontinue

/-- Positive global minimum debt forces every exact cap--Nash root at a
normalized-slice minimizer to have joint Continue mass one. -/
theorem minimum_normalizedPassportSlice_continueMass_eq_one
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hmin : ∀ candidate ∈
      family.normalizedPassportSlice minimum massDensity gainDensity,
      point.wholeDebt ≤ candidate.wholeDebt)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.whole.1.2 0 root) :
    quittingStationaryContinueMass root = 1 := by
  have hwholeCarrier := family.whole_semantic_mem_carrier hpoint.1
  have hpointPos : 0 < point.wholeDebt := by
    exact hminimum_pos.trans_le (hminimum point.whole.1 hwholeCarrier)
  have hprefixed := family.prefixMap_mem_normalizedPassportSlice_of_isZeroNash
    minimum massDensity gainDensity point hpoint root hnash
  have hminimal := hmin (family.prefixMap root point) hprefixed
  have hdefect : quittingRootTotalNashDefect reward point.whole.1.2 root = 0 :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward point.whole.1.2 root).1 hnash
  have hdebt : (family.prefixMap root point).wholeDebt =
      quittingStationaryContinueMass root * point.wholeDebt := by
    rw [family.prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect,
      hdefect, add_zero]
  rw [hdebt] at hminimal
  have hcontinueLe := quittingStationaryContinueMass_le_one root
  nlinarith

/-- Every exact cap--Nash root at the positive normalized minimizer is
literally the all-Continue product root. -/
theorem minimum_normalizedPassportSlice_exactRoot_eq_allContinue
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hmin : ∀ candidate ∈
      family.normalizedPassportSlice minimum massDensity gainDensity,
      point.wholeDebt ≤ candidate.wholeDebt)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.whole.1.2 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hcontinue := family.minimum_normalizedPassportSlice_continueMass_eq_one
    minimum hminimum hminimum_pos massDensity gainDensity point hpoint hmin
      root hnash
  funext player
  simpa only [quittingAllContinueRoot] using
    eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue player

/-- Exact correspondence form.  The reverse implication uses finite root-game
Nash existence plus the preceding universal rigidity; it does not assume that
carrier caps dominate singleton rewards. -/
theorem minimum_normalizedPassportSlice_isZeroNash_iff_allContinue
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (massDensity gainDensity : ℝ)
    (point : QuittingMarkedPairDecoration ι)
    (hpoint : point ∈
      family.normalizedPassportSlice minimum massDensity gainDensity)
    (hmin : ∀ candidate ∈
      family.normalizedPassportSlice minimum massDensity gainDensity,
      point.wholeDebt ≤ candidate.wholeDebt)
    (root : ι → PMF Bool) :
    IsεQuittingRootNash reward point.whole.1.2 0 root ↔
      root = (quittingAllContinueRoot : ι → PMF Bool) := by
  constructor
  · exact family.minimum_normalizedPassportSlice_exactRoot_eq_allContinue
      minimum hminimum hminimum_pos massDensity gainDensity point hpoint hmin root
  · intro hroot
    obtain ⟨selected, hselected⟩ :=
      exists_isZeroQuittingRootNash (reward := reward) point.whole.1.2
    have hselectedEq :=
      family.minimum_normalizedPassportSlice_exactRoot_eq_allContinue
        minimum hminimum hminimum_pos massDensity gainDensity point hpoint hmin
          selected hselected
    rw [hroot, ← hselectedEq]
    exact hselected

/-- A supplied convergent passport produces a normalized-slice minimizer with
the exact conjecture-facing split.  Its whole debt is either the displayed
global minimum, or it is strictly larger and its exact cap--Nash
correspondence consists only of the all-Continue root.

The selected point belongs to the enlarged arbitrary-prefix closure.  This
theorem does not place it in the original supplied-family cluster. -/
theorem exists_minimum_normalizedPassportSlice_eq_or_strict_inert
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (passport : ConvergentPassport family minimum)
    (massDensity gainDensity : ℝ)
    (hmass : massDensity * passport.limit.wholeDebt <
      passport.limit.markedMass)
    (hgain : gainDensity * passport.limit.wholeDebt <
      passport.limit.actualGain) :
    ∃ point ∈ family.normalizedPassportSlice minimum massDensity gainDensity,
      (∀ candidate ∈
          family.normalizedPassportSlice minimum massDensity gainDensity,
        point.wholeDebt ≤ candidate.wholeDebt) ∧
      quittingTerminalSemanticDebtSum minimum ≤ point.wholeDebt ∧
      (point.wholeDebt = quittingTerminalSemanticDebtSum minimum ∨
        quittingTerminalSemanticDebtSum minimum < point.wholeDebt ∧
          ∀ root : ι → PMF Bool,
            IsεQuittingRootNash reward point.whole.1.2 0 root ↔
              root = (quittingAllContinueRoot : ι → PMF Bool)) := by
  have hlimit := passport.limit_mem_normalizedPassportSlice
    massDensity gainDensity hmass hgain
  obtain ⟨point, hpoint, hmin⟩ :=
    family.exists_minimum_normalizedPassportSlice minimum massDensity
      gainDensity ⟨passport.limit, hlimit⟩
  have hwholeCarrier := family.whole_semantic_mem_carrier hpoint.1
  have hlower : quittingTerminalSemanticDebtSum minimum ≤ point.wholeDebt :=
    hminimum point.whole.1 hwholeCarrier
  refine ⟨point, hpoint, hmin, hlower, ?_⟩
  rcases hlower.eq_or_lt with heq | hlt
  · exact Or.inl heq.symm
  · exact Or.inr ⟨hlt, fun root ↦
      family.minimum_normalizedPassportSlice_isZeroNash_iff_allContinue
        minimum hminimum hminimum_pos massDensity gainDensity point hpoint hmin
          root⟩

end QuittingMarkedPairDecoratedFamily

end GameTheory
