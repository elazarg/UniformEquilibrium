import MathUE.Logic.SignFormulaFiniteFolds
import MathUE.RealQuantifierElimination.QuantifierElimination
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumInwardViolation
import UniformEquilibrium.Quitting.Root.RationalReward
import Mathlib.Data.Finset.Sort

/-! # Exact rational decision for product-low quitting premiums -/

namespace GameTheory

open Math.PolynomialSignCell
open Math.PolynomialSignCell.SignFormula
open MathUE.RealQuantifierElimination

variable {players : Nat}

private theorem product_map_sort_eq_finset_product
    {α : Type} [LinearOrder α] (set : Finset α) (value : α → ℝ) :
    ((set.sort (· ≤ ·)).map value).prod = ∏ item ∈ set, value item := by
  rw [Finset.prod_eq_multiset_prod]
  change (Multiset.map value ↑(set.sort (· ≤ ·))).prod = _
  rw [Finset.sort_eq]

/-- The product of hazard variables over a finite player set. -/
def hazardProductExpression (set : Finset (Fin players)) : RingExpression players :=
  RingExpression.product ((set.sort (· ≤ ·)).map RingExpression.var)

/-- The product of one-minus-hazard expressions over a finite player set. -/
def continueProductExpression (set : Finset (Fin players)) : RingExpression players :=
  RingExpression.product ((set.sort (· ≤ ·)).map fun player =>
    1 + -RingExpression.var player)

@[simp]
theorem evalReal_hazardProductExpression
    (set : Finset (Fin players)) (hazard : Fin players → ℝ) :
    (hazardProductExpression set).evalReal hazard =
      ∏ player ∈ set, hazard player := by
  rw [hazardProductExpression, RingExpression.evalReal_product,
    List.map_map, product_map_sort_eq_finset_product]
  rfl

@[simp]
theorem evalReal_continueProductExpression
    (set : Finset (Fin players)) (hazard : Fin players → ℝ) :
    (continueProductExpression set).evalReal hazard =
      ∏ player ∈ set, (1 - hazard player) := by
  rw [continueProductExpression, RingExpression.evalReal_product, List.map_map,
    product_map_sort_eq_finset_product]
  apply Finset.prod_congr rfl
  intro player _
  simp [Function.comp_apply, sub_eq_add_neg]

private def orderedSubsets (set : Finset (Fin players)) :
    List (Finset (Fin players)) :=
  (set.sort (· ≤ ·)).sublists.map List.toFinset

private theorem coe_map_sublists_toFinset_eq_powerset_toFinset
    (list : List (Fin players)) (hnodup : list.Nodup) :
    (↑(list.sublists.map List.toFinset) : Multiset (Finset (Fin players))) =
      list.toFinset.powerset.val := by
  unfold Finset.powerset
  simp only [List.toFinset_val, hnodup.dedup]
  simp only [Multiset.powerset_coe]
  change Multiset.map List.toFinset ↑list.sublists =
    Multiset.pmap Finset.mk
      (Multiset.map (fun sublist : List (Fin players) => Multiset.ofList sublist)
        ↑list.sublists) _
  change Multiset.map (Multiset.toFinset ∘ Multiset.ofList)
    (Multiset.ofList list.sublists) = _
  rw [← Multiset.map_map]
  have hall : ∀ sublist ∈
      Multiset.map Multiset.ofList (Multiset.ofList list.sublists), sublist.Nodup := by
    intro sublist hsublist
    obtain ⟨source, hsource, rfl⟩ := Multiset.mem_map.mp hsublist
    rw [Multiset.coe_nodup]
    exact List.Nodup.sublist (List.mem_sublists.mp (by simpa using hsource)) hnodup
  rw [← Multiset.pmap_eq_map (fun sublist : Multiset (Fin players) => sublist.Nodup)
    Multiset.toFinset _ hall]
  apply Multiset.pmap_congr
  intro sublist _ hleft _hright
  exact (Multiset.toFinset_eq hleft).symm

private theorem coe_orderedSubsets_eq_powerset
    (set : Finset (Fin players)) :
    (↑(orderedSubsets set) : Multiset (Finset (Fin players))) = set.powerset.val := by
  unfold orderedSubsets
  have hnodup : (set.sort (· ≤ ·)).Nodup := Finset.sort_nodup set (· ≤ ·)
  rw [coe_map_sublists_toFinset_eq_powerset_toFinset _ hnodup]
  congr 1
  ext player
  simp

private theorem sum_map_orderedSubsets_eq_finset_powerset_sum
    (set : Finset (Fin players)) (value : Finset (Fin players) → ℝ) :
    ((orderedSubsets set).map value).sum = ∑ coalition ∈ set.powerset, value coalition := by
  rw [Finset.sum_eq_multiset_sum]
  change (Multiset.map value ↑(orderedSubsets set)).sum = _
  rw [coe_orderedSubsets_eq_powerset]

/-- A coalition's contribution to one player's singleton-relative Quit premium. -/
def coalitionPremiumExpression (reward : RationalQuittingReward players)
    (player : Fin players) (coalition : Finset (Fin players)) :
    RingExpression players :=
  (hazardProductExpression coalition *
      continueProductExpression (Finset.univ.erase player \ coalition)) *
    (RingExpression.const
        (reward ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player) +
      -RingExpression.const
        (reward (quittingSingletonTerminal player) player))

/-- The singleton-relative Quit premium as an explicit rational expression. -/
def quittingHazardQuitPremiumExpression
    (reward : RationalQuittingReward players) (player : Fin players) :
    RingExpression players :=
  RingExpression.sum
    ((orderedSubsets (Finset.univ.erase player)).map fun coalition =>
      coalitionPremiumExpression reward player coalition)

@[simp]
theorem evalReal_coalitionPremiumExpression
    (reward : RationalQuittingReward players) (player : Fin players)
    (coalition : Finset (Fin players)) (hazard : Fin players → ℝ) :
    (coalitionPremiumExpression reward player coalition).evalReal hazard =
      ((∏ other ∈ coalition, hazard other) *
        ∏ other ∈ Finset.univ.erase player \ coalition, (1 - hazard other)) *
        (rationalQuittingRewardToReal reward
              ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player -
          rationalQuittingRewardToReal reward
            (quittingSingletonTerminal player) player) := by
  simp [coalitionPremiumExpression, rationalQuittingRewardToReal, sub_eq_add_neg]

@[simp]
theorem evalReal_quittingHazardQuitPremiumExpression
    (reward : RationalQuittingReward players) (player : Fin players)
    (hazard : Fin players → ℝ) :
    (quittingHazardQuitPremiumExpression reward player).evalReal hazard =
      quittingHazardQuitPremium (rationalQuittingRewardToReal reward) hazard player := by
  rw [quittingHazardQuitPremiumExpression, RingExpression.evalReal_sum, List.map_map,
    sum_map_orderedSubsets_eq_finset_powerset_sum]
  unfold quittingHazardQuitPremium
  apply Finset.sum_congr rfl
  intro coalition _
  simp

/-- The conjunction saying every hazard coordinate belongs to `[0,1]`. -/
def hazardCubeFormula (players : Nat) : QuantifierFreeFormula players :=
  conjunction
    ((List.ofFn fun player : Fin players =>
        QuantifierFreeFormula.nonnegative (RingExpression.var player)) ++
      (List.ofFn fun player : Fin players =>
        QuantifierFreeFormula.nonpositive
          (RingExpression.var player + -RingExpression.const 1)))

/-- Some hazard coordinate is positive. -/
def activeHazardFormula (players : Nat) : QuantifierFreeFormula players :=
  disjunction (List.ofFn fun player : Fin players =>
    QuantifierFreeFormula.positive (RingExpression.var player))

/-- Some active player has a nonpositive singleton-relative Quit premium. -/
def lowActivePremiumFormula (reward : RationalQuittingReward players) :
    QuantifierFreeFormula players :=
  disjunction (List.ofFn fun player : Fin players =>
    .and (QuantifierFreeFormula.positive (RingExpression.var player))
      (QuantifierFreeFormula.nonpositive
        (quittingHazardQuitPremiumExpression reward player)))

/-- The hazard-space sentence underlying the product-low condition. -/
def productLowHazardFormula (reward : RationalQuittingReward players) :
    QuantifierFreeFormula players :=
  .or (.not (.and (hazardCubeFormula players) (activeHazardFormula players)))
    (lowActivePremiumFormula reward)

@[simp]
theorem hazardCubeFormula_holdsAt_iff (hazard : Fin players → ℝ) :
    (hazardCubeFormula players).HoldsAt hazard ↔
      (∀ player, 0 ≤ hazard player) ∧ ∀ player, hazard player ≤ 1 := by
  rw [hazardCubeFormula, QuantifierFreeFormula.HoldsAt, holds_conjunction_iff]
  constructor
  · intro hall
    constructor
    · intro player
      apply (QuantifierFreeFormula.holdsAt_nonnegative_iff
        (RingExpression.var player) hazard).mp
      apply hall
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨player, rfl⟩)
    · intro player
      have hformula := hall
        (QuantifierFreeFormula.nonpositive
          (RingExpression.var player + -RingExpression.const 1))
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨player, rfl⟩))
      have heval := (QuantifierFreeFormula.holdsAt_nonpositive_iff
        (RingExpression.var player + -RingExpression.const 1) hazard).mp hformula
      simpa using heval
  · rintro ⟨hzero, hone⟩ formula hformula
    rw [List.mem_append, List.mem_ofFn, List.mem_ofFn] at hformula
    rcases hformula with ⟨player, rfl⟩ | ⟨player, rfl⟩
    · exact (QuantifierFreeFormula.holdsAt_nonnegative_iff _ hazard).mpr (hzero player)
    · apply (QuantifierFreeFormula.holdsAt_nonpositive_iff _ hazard).mpr
      simpa using hone player

@[simp]
theorem activeHazardFormula_holdsAt_iff (hazard : Fin players → ℝ) :
    (activeHazardFormula players).HoldsAt hazard ↔
      ∃ player, 0 < hazard player := by
  rw [activeHazardFormula, QuantifierFreeFormula.HoldsAt, holds_disjunction_iff]
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [List.mem_ofFn] at hformula
    obtain ⟨player, rfl⟩ := hformula
    exact ⟨player, (QuantifierFreeFormula.holdsAt_positive_iff _ hazard).mp hholds⟩
  · rintro ⟨player, hplayer⟩
    refine ⟨QuantifierFreeFormula.positive (RingExpression.var player),
      List.mem_ofFn.mpr ⟨player, rfl⟩, ?_⟩
    exact (QuantifierFreeFormula.holdsAt_positive_iff _ hazard).mpr hplayer

@[simp]
theorem lowActivePremiumFormula_holdsAt_iff
    (reward : RationalQuittingReward players) (hazard : Fin players → ℝ) :
    (lowActivePremiumFormula reward).HoldsAt hazard ↔
      ∃ player, 0 < hazard player ∧
        quittingHazardQuitPremium (rationalQuittingRewardToReal reward)
          hazard player ≤ 0 := by
  rw [lowActivePremiumFormula, QuantifierFreeFormula.HoldsAt,
    holds_disjunction_iff]
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [List.mem_ofFn] at hformula
    obtain ⟨player, rfl⟩ := hformula
    have hpremium :=
      (QuantifierFreeFormula.holdsAt_nonpositive_iff _ hazard).mp hholds.2
    rw [evalReal_quittingHazardQuitPremiumExpression] at hpremium
    exact ⟨player,
      (QuantifierFreeFormula.holdsAt_positive_iff _ hazard).mp hholds.1, hpremium⟩
  · rintro ⟨player, hactive, hpremium⟩
    refine ⟨.and (QuantifierFreeFormula.positive (RingExpression.var player))
        (QuantifierFreeFormula.nonpositive
          (quittingHazardQuitPremiumExpression reward player)),
      List.mem_ofFn.mpr ⟨player, rfl⟩, ?_, ?_⟩
    · exact (QuantifierFreeFormula.holdsAt_positive_iff _ hazard).mpr hactive
    · apply (QuantifierFreeFormula.holdsAt_nonpositive_iff _ hazard).mpr
      rw [evalReal_quittingHazardQuitPremiumExpression]
      exact hpremium

@[simp]
theorem productLowHazardFormula_holdsAt_iff
    (reward : RationalQuittingReward players) (hazard : Fin players → ℝ) :
    (productLowHazardFormula reward).HoldsAt hazard ↔
      (((∀ player, 0 ≤ hazard player) ∧ ∀ player, hazard player ≤ 1) ∧
          (∃ player, 0 < hazard player) →
        ∃ player, 0 < hazard player ∧
          quittingHazardQuitPremium (rationalQuittingRewardToReal reward)
            hazard player ≤ 0) := by
  change (¬((hazardCubeFormula players).HoldsAt hazard ∧
      (activeHazardFormula players).HoldsAt hazard) ∨
        (lowActivePremiumFormula reward).HoldsAt hazard) ↔ _
  rw [hazardCubeFormula_holdsAt_iff, activeHazardFormula_holdsAt_iff,
    lowActivePremiumFormula_holdsAt_iff]
  tauto

/-- The closed first-order sentence recognizing product-low rational tables. -/
def productLowQuittingPremiumFormula (reward : RationalQuittingReward players) :
    PolynomialFormula 0 :=
  (PolynomialFormula.ofQuantifierFree
    (productLowHazardFormula reward)).universallyClose

/-- The closed formula has exactly the existing product-low semantics. -/
theorem productLowQuittingPremiumFormula_holdsAt_iff
    (reward : RationalQuittingReward players) :
    (productLowQuittingPremiumFormula reward).HoldsAt Fin.elim0 ↔
      HasProductLowQuittingPremium (rationalQuittingRewardToReal reward) := by
  rw [productLowQuittingPremiumFormula,
    PolynomialFormula.holdsAt_universallyClose_iff]
  simp only [PolynomialFormula.holdsAt_ofQuantifierFree_iff]
  rw [hasProductLowQuittingPremium_iff_hazard]
  constructor
  · intro hformula hazard hzero hone hactive
    exact (productLowHazardFormula_holdsAt_iff reward hazard).mp
      (hformula hazard) ⟨⟨hzero, hone⟩, hactive⟩
  · intro hhazard hazard
    apply (productLowHazardFormula_holdsAt_iff reward hazard).mpr
    rintro ⟨⟨hzero, hone⟩, hactive⟩
    exact hhazard hazard hzero hone hactive

/-- Execute the checked real quantifier eliminator on a rational reward table. -/
def decideHasProductLowQuittingPremium
    (reward : RationalQuittingReward players) : Bool :=
  decideClosedFormula (productLowQuittingPremiumFormula reward)

/-- The executable Boolean result is true exactly for product-low tables. -/
theorem decideHasProductLowQuittingPremium_eq_true_iff
    (reward : RationalQuittingReward players) :
    decideHasProductLowQuittingPremium reward = true ↔
      HasProductLowQuittingPremium (rationalQuittingRewardToReal reward) := by
  rw [decideHasProductLowQuittingPremium, decideClosedFormula_eq_true_iff,
    productLowQuittingPremiumFormula_holdsAt_iff]

/-- With no players, the original product-low condition is vacuously true. -/
theorem decideHasProductLowQuittingPremium_zero_players
    (reward : RationalQuittingReward 0) :
    decideHasProductLowQuittingPremium reward = true := by
  rw [decideHasProductLowQuittingPremium_eq_true_iff]
  intro root habsorption
  obtain ⟨player, _⟩ :=
    (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp
      habsorption
  exact Fin.elim0 player

end GameTheory
