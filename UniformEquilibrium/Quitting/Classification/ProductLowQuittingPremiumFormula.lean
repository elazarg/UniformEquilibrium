import MathUE.Logic.SignFormulaFiniteFolds
import MathUE.RealQuantifierElimination.QuantifierFreeFormula
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumInwardViolation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

/-! # Expression frontend for product-low quitting premiums -/

namespace GameTheory

open Math.PolynomialSignCell.SignFormula
open MathUE.RealQuantifierElimination
open scoped BigOperators

variable {players arity : Nat}

private theorem product_map_sort_eq_finset_product
    {alpha : Type} [LinearOrder alpha] (set : Finset alpha) (value : alpha → ℝ) :
    ((set.sort (· ≤ ·)).map value).prod = ∏ item ∈ set, value item := by
  rw [Finset.prod_eq_multiset_prod]
  change (Multiset.map value ↑(set.sort (· ≤ ·))).prod = _
  rw [Finset.sort_eq]

/-- The product of supplied hazard expressions over a finite player set. -/
def hazardProductExpressionWithTerms
    (hazardTerm : Fin players → RingExpression arity)
    (set : Finset (Fin players)) : RingExpression arity :=
  RingExpression.product ((set.sort (· ≤ ·)).map hazardTerm)

/-- The product of one-minus-hazard expressions over a finite player set. -/
def continueProductExpressionWithTerms
    (hazardTerm : Fin players → RingExpression arity)
    (set : Finset (Fin players)) : RingExpression arity :=
  RingExpression.product ((set.sort (· ≤ ·)).map fun player =>
    1 + -hazardTerm player)

@[simp]
theorem evalReal_hazardProductExpressionWithTerms
    (hazardTerm : Fin players → RingExpression arity)
    (set : Finset (Fin players)) (environment : Fin arity → ℝ) :
    (hazardProductExpressionWithTerms hazardTerm set).evalReal environment =
      ∏ player ∈ set, (hazardTerm player).evalReal environment := by
  rw [hazardProductExpressionWithTerms, RingExpression.evalReal_product,
    List.map_map, product_map_sort_eq_finset_product]
  rfl

@[simp]
theorem evalReal_continueProductExpressionWithTerms
    (hazardTerm : Fin players → RingExpression arity)
    (set : Finset (Fin players)) (environment : Fin arity → ℝ) :
    (continueProductExpressionWithTerms hazardTerm set).evalReal environment =
      ∏ player ∈ set, (1 - (hazardTerm player).evalReal environment) := by
  rw [continueProductExpressionWithTerms, RingExpression.evalReal_product,
    List.map_map, product_map_sort_eq_finset_product]
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

/-- One coalition contribution with arbitrary reward and hazard expressions. -/
def coalitionPremiumExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (hazardTerm : Fin players → RingExpression arity)
    (player : Fin players) (coalition : Finset (Fin players)) :
    RingExpression arity :=
  (hazardProductExpressionWithTerms hazardTerm coalition *
      continueProductExpressionWithTerms hazardTerm
        (Finset.univ.erase player \ coalition)) *
    (rewardTerm ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player +
      -rewardTerm (quittingSingletonTerminal player) player)

/-- A singleton-relative Quit premium with arbitrary reward and hazard expressions. -/
def quittingHazardQuitPremiumExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (hazardTerm : Fin players → RingExpression arity)
    (player : Fin players) : RingExpression arity :=
  RingExpression.sum
    ((orderedSubsets (Finset.univ.erase player)).map fun coalition =>
      coalitionPremiumExpressionWithTerms rewardTerm hazardTerm player coalition)

@[simp]
theorem evalReal_coalitionPremiumExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (hazardTerm : Fin players → RingExpression arity)
    (player : Fin players) (coalition : Finset (Fin players))
    (environment : Fin arity → ℝ) :
    (coalitionPremiumExpressionWithTerms rewardTerm hazardTerm player coalition).evalReal
        environment =
      ((∏ other ∈ coalition, (hazardTerm other).evalReal environment) *
        ∏ other ∈ Finset.univ.erase player \ coalition,
          (1 - (hazardTerm other).evalReal environment)) *
        ((rewardTerm
              ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player).evalReal
            environment -
          (rewardTerm (quittingSingletonTerminal player) player).evalReal environment) := by
  simp [coalitionPremiumExpressionWithTerms, sub_eq_add_neg]

@[simp]
theorem evalReal_quittingHazardQuitPremiumExpressionWithTerms
    (rewardTerm : {S : Finset (Fin players) // S.Nonempty} →
      Fin players → RingExpression arity)
    (hazardTerm : Fin players → RingExpression arity)
    (player : Fin players) (environment : Fin arity → ℝ) :
    (quittingHazardQuitPremiumExpressionWithTerms rewardTerm hazardTerm player).evalReal
        environment =
      quittingHazardQuitPremium
        (fun terminal observer => (rewardTerm terminal observer).evalReal environment)
        (fun observer => (hazardTerm observer).evalReal environment) player := by
  rw [quittingHazardQuitPremiumExpressionWithTerms, RingExpression.evalReal_sum,
    List.map_map, sum_map_orderedSubsets_eq_finset_powerset_sum]
  unfold quittingHazardQuitPremium
  apply Finset.sum_congr rfl
  intro coalition _
  simp

/-- Every supplied hazard term evaluates in the unit interval. -/
def hazardCubeFormulaWithTerms
    (hazardTerm : Fin players → RingExpression arity) :
    QuantifierFreeFormula arity :=
  conjunction
    ((List.ofFn fun player : Fin players =>
        QuantifierFreeFormula.nonnegative (hazardTerm player)) ++
      (List.ofFn fun player : Fin players =>
        QuantifierFreeFormula.nonpositive (hazardTerm player + -1)))

/-- At least one supplied hazard term evaluates positively. -/
def activeHazardFormulaWithTerms
    (hazardTerm : Fin players → RingExpression arity) :
    QuantifierFreeFormula arity :=
  disjunction (List.ofFn fun player : Fin players =>
    QuantifierFreeFormula.positive (hazardTerm player))

/-- Some active hazard has a nonpositive supplied premium. -/
def lowActivePremiumFormulaWithTerms
    (hazardTerm premiumTerm : Fin players → RingExpression arity) :
    QuantifierFreeFormula arity :=
  disjunction (List.ofFn fun player : Fin players =>
    .and (QuantifierFreeFormula.positive (hazardTerm player))
      (QuantifierFreeFormula.nonpositive (premiumTerm player)))

/-- The product-low implication for supplied hazard and premium terms. -/
def productLowHazardFormulaWithTerms
    (hazardTerm premiumTerm : Fin players → RingExpression arity) :
    QuantifierFreeFormula arity :=
  .or (.not (.and (hazardCubeFormulaWithTerms hazardTerm)
    (activeHazardFormulaWithTerms hazardTerm)))
      (lowActivePremiumFormulaWithTerms hazardTerm premiumTerm)

@[simp]
theorem hazardCubeFormulaWithTerms_holdsAt_iff
    (hazardTerm : Fin players → RingExpression arity)
    (environment : Fin arity → ℝ) :
    (hazardCubeFormulaWithTerms hazardTerm).HoldsAt environment ↔
      (∀ player, 0 ≤ (hazardTerm player).evalReal environment) ∧
        ∀ player, (hazardTerm player).evalReal environment ≤ 1 := by
  rw [hazardCubeFormulaWithTerms, QuantifierFreeFormula.HoldsAt,
    holds_conjunction_iff]
  constructor
  · intro hall
    constructor
    · intro player
      apply (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mp
      apply hall
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨player, rfl⟩)
    · intro player
      have hformula := hall
        (QuantifierFreeFormula.nonpositive (hazardTerm player + -1))
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨player, rfl⟩))
      have heval :=
        (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mp hformula
      simpa using heval
  · rintro ⟨hzero, hone⟩ formula hformula
    rw [List.mem_append, List.mem_ofFn, List.mem_ofFn] at hformula
    rcases hformula with ⟨player, rfl⟩ | ⟨player, rfl⟩
    · exact (QuantifierFreeFormula.holdsAt_nonnegative_iff _ environment).mpr
        (hzero player)
    · apply (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mpr
      simpa using hone player

@[simp]
theorem activeHazardFormulaWithTerms_holdsAt_iff
    (hazardTerm : Fin players → RingExpression arity)
    (environment : Fin arity → ℝ) :
    (activeHazardFormulaWithTerms hazardTerm).HoldsAt environment ↔
      ∃ player, 0 < (hazardTerm player).evalReal environment := by
  rw [activeHazardFormulaWithTerms, QuantifierFreeFormula.HoldsAt,
    holds_disjunction_iff]
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [List.mem_ofFn] at hformula
    obtain ⟨player, rfl⟩ := hformula
    exact ⟨player, (QuantifierFreeFormula.holdsAt_positive_iff _ environment).mp hholds⟩
  · rintro ⟨player, hplayer⟩
    refine ⟨QuantifierFreeFormula.positive (hazardTerm player),
      List.mem_ofFn.mpr ⟨player, rfl⟩, ?_⟩
    exact (QuantifierFreeFormula.holdsAt_positive_iff _ environment).mpr hplayer

@[simp]
theorem lowActivePremiumFormulaWithTerms_holdsAt_iff
    (hazardTerm premiumTerm : Fin players → RingExpression arity)
    (environment : Fin arity → ℝ) :
    (lowActivePremiumFormulaWithTerms hazardTerm premiumTerm).HoldsAt environment ↔
      ∃ player, 0 < (hazardTerm player).evalReal environment ∧
        (premiumTerm player).evalReal environment ≤ 0 := by
  rw [lowActivePremiumFormulaWithTerms, QuantifierFreeFormula.HoldsAt,
    holds_disjunction_iff]
  constructor
  · rintro ⟨formula, hformula, hholds⟩
    rw [List.mem_ofFn] at hformula
    obtain ⟨player, rfl⟩ := hformula
    exact ⟨player,
      (QuantifierFreeFormula.holdsAt_positive_iff _ environment).mp hholds.1,
      (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mp hholds.2⟩
  · rintro ⟨player, hactive, hpremium⟩
    refine ⟨.and (QuantifierFreeFormula.positive (hazardTerm player))
        (QuantifierFreeFormula.nonpositive (premiumTerm player)),
      List.mem_ofFn.mpr ⟨player, rfl⟩, ?_, ?_⟩
    · exact (QuantifierFreeFormula.holdsAt_positive_iff _ environment).mpr hactive
    · exact (QuantifierFreeFormula.holdsAt_nonpositive_iff _ environment).mpr hpremium

@[simp]
theorem productLowHazardFormulaWithTerms_holdsAt_iff
    (hazardTerm premiumTerm : Fin players → RingExpression arity)
    (environment : Fin arity → ℝ) :
    (productLowHazardFormulaWithTerms hazardTerm premiumTerm).HoldsAt environment ↔
      (((∀ player, 0 ≤ (hazardTerm player).evalReal environment) ∧
          ∀ player, (hazardTerm player).evalReal environment ≤ 1) ∧
        (∃ player, 0 < (hazardTerm player).evalReal environment) →
          ∃ player, 0 < (hazardTerm player).evalReal environment ∧
            (premiumTerm player).evalReal environment ≤ 0) := by
  change (¬((hazardCubeFormulaWithTerms hazardTerm).HoldsAt environment ∧
      (activeHazardFormulaWithTerms hazardTerm).HoldsAt environment) ∨
        (lowActivePremiumFormulaWithTerms hazardTerm premiumTerm).HoldsAt environment) ↔ _
  rw [hazardCubeFormulaWithTerms_holdsAt_iff,
    activeHazardFormulaWithTerms_holdsAt_iff,
    lowActivePremiumFormulaWithTerms_holdsAt_iff]
  tauto

end GameTheory
