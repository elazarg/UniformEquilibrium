import MathUE.Interval.RationalPolynomialRationalEvaluation
import UniformEquilibrium.Quitting.Projective.ExcludedPolynomialRationalRejection
import UniformEquilibrium.Quitting.Projective.RobustChargedRelation
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi

/-! # Exhaustive finite-budget exact rational candidate rejection

Every rational source/probability pair has a finite canonical code. Testing
uses rational arithmetic only, actual source-based endpoint regret, and the
exact rational successor. Eventual success has no uniform cutoff or denominator bound.
-/

namespace GameTheory

open Math.Interval GameTheory.Finite
open scoped Topology

variable {players : ℕ}

abbrev RationalQuittingRejectionPair (players : ℕ) :=
  (Fin players → ℚ) × (Fin players → ℚ)

def rationalQuittingRejectionSuccessor (reward : RationalQuittingReward players)
    (pair : RationalQuittingRejectionPair players) : Fin players → ℚ :=
  fun who => rationalBooleanExpectedPayoff (rationalQuittingBooleanPayoff reward pair.1)
    pair.2 who

/-- Full exact rational test. Invalid raw probabilities are explicitly rejected. -/
def rationalQuittingPotentialRejects (reward : RationalQuittingReward players)
    (expression : RationalPolynomial players) (bound tolerance : ℚ)
    (pair : RationalQuittingRejectionPair players) : Bool :=
  decide ((∀ who, |pair.1 who| ≤ bound) ∧
    (∀ who, 0 ≤ pair.2 who) ∧ (∀ who, pair.2 who ≤ 1) ∧
    (∀ who, |rationalQuittingRejectionSuccessor reward pair who| ≤ bound) ∧
    0 < rationalQuittingAbsorption pair.2 ∧
    (∀ who, rationalBooleanNashRegret (rationalQuittingBooleanPayoff reward pair.1)
      pair.2 who ≤ tolerance * rationalQuittingAbsorption pair.2) ∧
    RationalPolynomial.evalRat pair.1 expression -
      RationalPolynomial.evalRat (rationalQuittingRejectionSuccessor reward pair) expression <
        rationalQuittingAbsorption pair.2)

/-- Enumerate every canonical code at most budget, omitting unsuccessful decodings. -/
def rationalQuittingRejectionCandidates (budget : ℕ) :
    List (RationalQuittingRejectionPair players) :=
  (List.range (budget + 1)).filterMap Encodable.decode

def rationalQuittingPotentialRejectionSearch? (reward : RationalQuittingReward players)
    (expression : RationalPolynomial players) (bound tolerance : ℚ) (budget : ℕ) :
    Option (RationalQuittingRejectionPair players) :=
  (rationalQuittingRejectionCandidates budget).find?
    (rationalQuittingPotentialRejects reward expression bound tolerance)

/-- Literal exhaustiveness over EVERY rational pair, not only a density subsequence. -/
theorem mem_rationalQuittingRejectionCandidates
    (pair : RationalQuittingRejectionPair players) (budget : ℕ)
    (hcode : Encodable.encode pair ≤ budget) :
    pair ∈ rationalQuittingRejectionCandidates budget := by
  apply List.mem_filterMap.mpr
  exact ⟨Encodable.encode pair, List.mem_range.mpr (Nat.lt_succ_of_le hcode),
    Encodable.encodek pair⟩

theorem rationalQuittingPotentialRejectionSearch_eventually_succeeds
    (reward : RationalQuittingReward players) (expression : RationalPolynomial players)
    (bound tolerance : ℚ)
    (hexists : ∃ pair, rationalQuittingPotentialRejects reward expression bound tolerance pair =
      true) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingPotentialRejectionSearch? reward expression bound tolerance budget).isSome =
        true := by
  obtain ⟨pair, hpair⟩ := hexists
  refine ⟨Encodable.encode pair, fun budget hbudget => ?_⟩
  apply List.find?_isSome.mpr
  exact ⟨pair, mem_rationalQuittingRejectionCandidates pair budget hbudget, hpair⟩

noncomputable section

/-- An accepted rational pair compiles to one literal actual robust rejecting
edge. No floating-point check, supplied root, or target realization is used. -/
theorem rationalQuittingPotentialRejects_sound
    (reward : RationalQuittingReward players) (expression : RationalPolynomial players)
    (bound tolerance : ℚ) (htolerance : 0 ≤ tolerance)
    (pair : RationalQuittingRejectionPair players)
    (haccepts : rationalQuittingPotentialRejects reward expression bound tolerance pair = true) :
    ∃ root : RationalQuittingRoot players,
      root.probability = pair.2 ∧
      ∃ source target : QuittingRobustChargedState (Fin players) (bound : ℝ),
        source.1 = (fun who => (pair.1 who : ℝ)) ∧
        target.1 = (fun who => (rationalQuittingRejectionSuccessor reward pair who : ℝ)) ∧
        target.1 = quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
          source.1 root.toPMF ∧
        IsQuittingFloorFreeRobustEdge (rationalQuittingRewardToReal reward)
          tolerance bound source (quittingSimplexOfRoot root.toPMF) target ∧
        0 < quittingRootAbsorptionMass root.toPMF ∧
        RationalPolynomial.evalReal source.1 expression -
          RationalPolynomial.evalReal target.1 expression < quittingRootAbsorptionMass root.toPMF :=
    by
  simp only [rationalQuittingPotentialRejects, decide_eq_true_eq] at haccepts
  obtain ⟨hsource, hzero, hone, htarget, hpositive, hregret, hdrop⟩ := haccepts
  let root : RationalQuittingRoot players := ⟨pair.2, hzero, hone⟩
  let source : QuittingRobustChargedState (Fin players) (bound : ℝ) :=
    ⟨fun who => (pair.1 who : ℝ), fun who => by
      change |(pair.1 who : ℝ)| ≤ (bound : ℝ)
      exact_mod_cast hsource who⟩
  let target : QuittingRobustChargedState (Fin players) (bound : ℝ) :=
    ⟨fun who => (rationalQuittingRejectionSuccessor reward pair who : ℝ),
      fun who => by
        change |(rationalQuittingRejectionSuccessor reward pair who : ℝ)| ≤ (bound : ℝ)
        exact_mod_cast htarget who⟩
  have hsuccessor : target.1 = quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
      source.1 root.toPMF :=
    (quittingRootSuccessorPayoff_rational_eq_cast reward pair.1 root).symm
  have hcharge : 0 < quittingRootAbsorptionMass root.toPMF := by
    rw [← rationalQuittingAbsorption_cast root]
    exact_mod_cast hpositive
  have hedge : IsQuittingFloorFreeRobustEdge (rationalQuittingRewardToReal reward)
      tolerance bound source (quittingSimplexOfRoot root.toPMF) target := by
    intro who
    constructor
    · simp only [quittingRobustChargedEdgeResidual,
        quittingRootOfSimplex_simplexOfRoot, hsuccessor, sub_self, abs_zero,
        quittingRobustChargedEdgeAbsorption]
      exact mul_nonneg (Rat.cast_nonneg.mpr htolerance) hcharge.le
    · simp only [quittingRobustChargedEdgeRegret, quittingRootOfSimplex_simplexOfRoot,
        quittingRobustChargedEdgeAbsorption]
      rw [quittingRootCoordinateNashDefect_rationalQuitting_eq_cast,
        ← rationalQuittingAbsorption_cast root]
      exact_mod_cast hregret who
  have hdropReal : RationalPolynomial.evalReal source.1 expression -
      RationalPolynomial.evalReal target.1 expression < quittingRootAbsorptionMass root.toPMF := by
    rw [← rationalQuittingAbsorption_cast root]
    change RationalPolynomial.evalReal (fun who => (pair.1 who : ℝ)) expression -
      RationalPolynomial.evalReal
        (fun who => (rationalQuittingRejectionSuccessor reward pair who : ℝ)) expression < _
    rw [← RationalPolynomial.ratCast_evalRat, ← RationalPolynomial.ratCast_evalRat]
    exact_mod_cast hdrop
  exact ⟨root, rfl, source, target, rfl, rfl, hsuccessor, hedge, hcharge, hdropReal⟩

/-- The actual result returned by the finite search has the same literal source,
root probabilities, exact successor and robust rejecting-edge interpretation.
The acceptance criterion remains the printed non-strict regret bound. -/
theorem rationalQuittingPotentialRejectionSearch_sound
    (reward : RationalQuittingReward players) (expression : RationalPolynomial players)
    (bound tolerance : ℚ) (htolerance : 0 ≤ tolerance) (budget : ℕ)
    (pair : RationalQuittingRejectionPair players)
    (hreturned : rationalQuittingPotentialRejectionSearch?
      reward expression bound tolerance budget = some pair) :
    ∃ root : RationalQuittingRoot players,
      root.probability = pair.2 ∧
      ∃ source target : QuittingRobustChargedState (Fin players) (bound : ℝ),
        source.1 = (fun who => (pair.1 who : ℝ)) ∧
        target.1 = (fun who => (rationalQuittingRejectionSuccessor reward pair who : ℝ)) ∧
        target.1 = quittingRootSuccessorPayoff (rationalQuittingRewardToReal reward)
          source.1 root.toPMF ∧
        IsQuittingFloorFreeRobustEdge (rationalQuittingRewardToReal reward)
          tolerance bound source (quittingSimplexOfRoot root.toPMF) target ∧
        0 < quittingRootAbsorptionMass root.toPMF ∧
        RationalPolynomial.evalReal source.1 expression -
          RationalPolynomial.evalReal target.1 expression <
            quittingRootAbsorptionMass root.toPMF := by
  apply rationalQuittingPotentialRejects_sound reward expression bound tolerance
    htolerance pair
  exact List.find?_some hreturned

/-- Source-facing termination: no supplied good pair or favorable strategy is
input. The actual exclusion produces one rational rejecting pair internally. -/
theorem rationalQuittingPotentialRejectionSearch_eventually_succeeds_of_excluded_polynomial
    [Nontrivial (Fin players)] (reward : RationalQuittingReward players)
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (expression : RationalPolynomial players)
    (hexcluded : expression.toMvPolynomial.totalDegree ≤ 2 ∨
      ∀ who, expression.toMvPolynomial.degreeOf who ≤ 1)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingPotentialRejectionSearch? reward expression 3 tolerance budget).isSome =
        true := by
  obtain ⟨source, root, hsource, htarget, hpositive, hregret, hdrop⟩ :=
    exists_rational_robust_rejection_of_excluded_polynomial
      reward hreward hsingleton expression hexcluded tolerance htolerance
  apply rationalQuittingPotentialRejectionSearch_eventually_succeeds
  refine ⟨(source, root.probability), ?_⟩
  simp only [rationalQuittingPotentialRejects, decide_eq_true_eq]
  refine ⟨hsource, root.nonnegative, root.le_one, htarget, ?_, ?_, ?_⟩
  · rw [← rationalQuittingAbsorption_cast root] at hpositive
    exact_mod_cast hpositive
  · intro who
    have h := (hregret who).le
    rw [quittingRootCoordinateNashDefect_rationalQuitting_eq_cast,
      ← rationalQuittingAbsorption_cast root] at h
    exact_mod_cast h
  · rw [← RationalPolynomial.ratCast_evalRat, ← RationalPolynomial.ratCast_evalRat,
      ← rationalQuittingAbsorption_cast root] at hdrop
    exact_mod_cast hdrop

end

end GameTheory
