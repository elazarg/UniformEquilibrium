/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FiniteClockPolynomialCertificate

/-!
# Polynomial lower queries for the escape-aware quantile-clock hierarchy

This file gives one finite polynomial system for a complete outer horizon.
It uses one common semantic point, one literal finite-clock center assignment
at each positive level through the horizon, coordinatewise radius constraints,
and an exact finite maximum graph for terminal exploitability.

For rational rewards and a rational query `gamma`, a supplied polynomial
infeasibility certificate for objective `< gamma` proves the checked lower
bound `gamma ≤ L_M`.  Strictness is encoded without a primitive strict
inequality: a nonnegative gap `gamma - objective` is required to have a
multiplicative inverse.

The verifier checks a supplied polynomial identity.  This file neither finds
certificates nor asserts Positivstellensatz completeness, CAD, quantifier
elimination, decidability, or a positive certificate for any reward table.
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
  Math.Topology
open QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

inductive QuantileClockOuterPointVar (ι : Type) : Type where
  | payoff (player : ι)
  | cap (player : ι)
  | objective
  | strictInverse
deriving DecidableEq

abbrev QuantileClockOuterVar (ι : Type) [Fintype ι]
    (horizon : ℕ) : Type :=
  QuantileClockOuterPointVar ι ⊕
    (Σ level : Fin horizon,
      FiniteClockCenterVar ι (quantileClockSupport ι (level.1 + 1)))

def quantileClockRadiusRat (ι : Type) [Fintype ι]
    (level : ℕ) : ℚ :=
  (Fintype.card ι * (Fintype.card ι - 1) : ℕ) / (level : ℚ)

omit [DecidableEq ι] in
theorem ratCast_quantileClockRadiusRat (level : ℕ) :
    (quantileClockRadiusRat ι level : ℝ) = quantileClockRadius ι level := by
  simp [quantileClockRadiusRat, quantileClockRadius]

def quantileClockOuterPointPair
    (horizon : ℕ) (assign : QuantileClockOuterVar ι horizon → ℝ) :
    QuittingTerminalSemanticPair ι :=
  (⟨fun player => assign (.inl (.payoff player)),
    fun player => assign (.inl (.cap player))⟩)

def quantileClockOuterObjective
    (horizon : ℕ) (assign : QuantileClockOuterVar ι horizon → ℝ) : ℝ :=
  assign (.inl .objective)

def quantileClockOuterCenterAssign
    {S : Type*} {horizon : ℕ} (level : Fin horizon)
    (assign : QuantileClockOuterVar ι horizon → S) :
    FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → S :=
  fun centerVariable => assign (.inr ⟨level, centerVariable⟩)

def quantileClockLiftCenterPolynomial
    {R : Type*} [CommRing R] {horizon : ℕ} (level : Fin horizon)
    (polynomial : MvPolynomial
      (FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1))) R) :
    MvPolynomial (QuantileClockOuterVar ι horizon) R :=
  MvPolynomial.rename
    (fun centerVariable => .inr ⟨level, centerVariable⟩) polynomial

omit [DecidableEq ι] in
theorem eval₂_quantileClockLiftCenterPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (coeff : R →+* S) {horizon : ℕ} (level : Fin horizon)
    (assign : QuantileClockOuterVar ι horizon → S)
    (polynomial : MvPolynomial
      (FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1))) R) :
    MvPolynomial.eval₂ coeff assign
        (quantileClockLiftCenterPolynomial level polynomial) =
      MvPolynomial.eval₂ coeff
        (quantileClockOuterCenterAssign level assign) polynomial := by
  rw [quantileClockLiftCenterPolynomial, MvPolynomial.eval₂_rename]
  rfl

def quantileClockOuterCandidatePoly
    {R : Type*} [CommRing R] (horizon : ℕ) :
    Option ι → MvPolynomial (QuantileClockOuterVar ι horizon) R
  | none => 0
  | some player =>
      MvPolynomial.X (.inl (.cap player)) -
        MvPolynomial.X (.inl (.payoff player))

def quantileClockOuterObjectiveUpperPoly
    {R : Type*} [CommRing R] (horizon : ℕ)
    (candidate : Option ι) :
    MvPolynomial (QuantileClockOuterVar ι horizon) R :=
  MvPolynomial.X (.inl .objective) -
    quantileClockOuterCandidatePoly horizon candidate

def quantileClockOuterObjectiveTightPoly
    {R : Type*} [CommRing R] (horizon : ℕ) :
    MvPolynomial (QuantileClockOuterVar ι horizon) R :=
  ∏ candidate : Option ι,
    quantileClockOuterObjectiveUpperPoly horizon candidate

structure QuantileClockOuterNeighborhoodIndex
    (ι : Type) (horizon : ℕ) where
  level : Fin horizon
  player : ι
  capCoordinate : Bool
  reverse : Bool
deriving DecidableEq, Fintype

def quantileClockOuterNeighborhoodPoly
    (horizon : ℕ) (index : QuantileClockOuterNeighborhoodIndex ι horizon) :
    MvPolynomial (QuantileClockOuterVar ι horizon) ℚ :=
  let pointVar := if index.capCoordinate then
    QuantileClockOuterPointVar.cap index.player
  else QuantileClockOuterPointVar.payoff index.player
  let centerVar := if index.capCoordinate then
    FiniteClockCenterVar.cap index.player
  else FiniteClockCenterVar.payoff index.player
  let difference :=
    MvPolynomial.X (.inl pointVar) -
      MvPolynomial.X (.inr ⟨index.level, centerVar⟩)
  MvPolynomial.C (quantileClockRadiusRat ι (index.level.1 + 1)) +
    if index.reverse then difference else -difference

abbrev QuantileClockOuterEqualityIndex (ι : Type) [Fintype ι]
    (horizon : ℕ) :=
  (Fin horizon × FiniteClockCenterEqualityIndex ι) ⊕ Unit

abbrev QuantileClockOuterInequalityIndex (ι : Type) [Fintype ι]
    (horizon : ℕ) :=
  (Σ level : Fin horizon,
      FiniteClockCenterInequalityIndex ι
        (quantileClockSupport ι (level.1 + 1))) ⊕
    (QuantileClockOuterNeighborhoodIndex ι horizon ⊕ Option ι)

def quantileClockOuterEqualityPolynomial
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) :
    QuantileClockOuterEqualityIndex ι horizon →
      MvPolynomial (QuantileClockOuterVar ι horizon) ℚ
  | .inl ⟨level, index⟩ =>
      quantileClockLiftCenterPolynomial level
        (finiteClockCenterEqualityPolynomial reward
          (quantileClockSupport ι (level.1 + 1)) index)
  | .inr _ => quantileClockOuterObjectiveTightPoly horizon

def quantileClockOuterInequalityPolynomial
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) :
    QuantileClockOuterInequalityIndex ι horizon →
      MvPolynomial (QuantileClockOuterVar ι horizon) ℚ
  | .inl ⟨level, index⟩ =>
      quantileClockLiftCenterPolynomial level
        (finiteClockCenterInequalityPolynomial reward
          (quantileClockSupport ι (level.1 + 1)) index)
  | .inr (.inl index) => quantileClockOuterNeighborhoodPoly horizon index
  | .inr (.inr candidate) =>
      quantileClockOuterObjectiveUpperPoly horizon candidate

def SatisfiesQuantileClockOuterPolynomials
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ)
    (assign : QuantileClockOuterVar ι horizon → ℝ) : Prop :=
  (∀ index, MvPolynomial.eval₂ (Rat.castHom ℝ) assign
      (quantileClockOuterEqualityPolynomial reward horizon index) = 0) ∧
    (∀ index, 0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ) assign
      (quantileClockOuterInequalityPolynomial reward horizon index))

theorem satisfiesQuantileClockOuter_center
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    {horizon : ℕ} (assign : QuantileClockOuterVar ι horizon → ℝ)
    (hsolution : SatisfiesQuantileClockOuterPolynomials
      reward horizon assign) (level : Fin horizon) :
    SatisfiesFiniteClockCenterPolynomials
      (Rat.castHom ℝ) reward
      (quantileClockSupport ι (level.1 + 1))
      (quantileClockOuterCenterAssign level assign) := by
  rw [satisfiesFiniteClockCenterPolynomials_iff_indexed]
  constructor
  · intro index
    have hrow := hsolution.1 (.inl ⟨level, index⟩)
    simpa [quantileClockOuterEqualityPolynomial,
      eval₂_quantileClockLiftCenterPolynomial] using hrow
  · intro index
    have hrow := hsolution.2 (.inl ⟨level, index⟩)
    simpa [quantileClockOuterInequalityPolynomial,
      eval₂_quantileClockLiftCenterPolynomial] using hrow

omit [DecidableEq ι] in
theorem eval₂_quantileClockOuterCandidatePoly
    {R S : Type*} [CommRing R] [CommRing S]
    (coeff : R →+* S) (horizon : ℕ)
    (assign : QuantileClockOuterVar ι horizon → S)
    (candidate : Option ι) :
    MvPolynomial.eval₂ coeff assign
        (quantileClockOuterCandidatePoly horizon candidate) =
      match candidate with
      | none => 0
      | some player =>
          assign (.inl (.cap player)) - assign (.inl (.payoff player)) := by
  cases candidate <;> simp [quantileClockOuterCandidatePoly]

omit [DecidableEq ι] in
theorem eval₂_quantileClockOuterObjectiveUpperPoly
    {R S : Type*} [CommRing R] [CommRing S]
    (coeff : R →+* S) (horizon : ℕ)
    (assign : QuantileClockOuterVar ι horizon → S)
    (candidate : Option ι) :
    MvPolynomial.eval₂ coeff assign
        (quantileClockOuterObjectiveUpperPoly horizon candidate) =
      assign (.inl .objective) -
        match candidate with
        | none => 0
        | some player =>
            assign (.inl (.cap player)) -
              assign (.inl (.payoff player)) := by
  simp [quantileClockOuterObjectiveUpperPoly,
    eval₂_quantileClockOuterCandidatePoly]

theorem quantileClockOuter_semanticPairWithin
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    {horizon : ℕ} (assign : QuantileClockOuterVar ι horizon → ℝ)
    (hsolution : SatisfiesQuantileClockOuterPolynomials
      reward horizon assign) (level : Fin horizon) :
    semanticPairWithin (quantileClockRadius ι (level.1 + 1))
      (quantileClockOuterPointPair horizon assign)
      (finiteClockCenterPair (quantileClockSupport ι (level.1 + 1))
        (quantileClockOuterCenterAssign level assign)) := by
  have row (player : ι) (capCoordinate reverse : Bool) :=
    hsolution.2 (.inr (.inl
      ⟨level, player, capCoordinate, reverse⟩))
  constructor
  · intro player
    have hforward := row player false false
    have hreverse := row player false true
    simp only [quantileClockOuterInequalityPolynomial,
      quantileClockOuterNeighborhoodPoly, Bool.false_eq_true, if_false,
      if_true, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_neg,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X] at hforward hreverse
    have hradius : (Rat.castHom ℝ)
        (quantileClockRadiusRat ι (level.1 + 1)) =
          quantileClockRadius ι (level.1 + 1) := by
      simpa using ratCast_quantileClockRadiusRat (ι := ι) (level.1 + 1)
    rw [hradius] at hforward hreverse
    rw [abs_le]
    constructor <;> dsimp [quantileClockOuterPointPair,
      finiteClockCenterPair, quantileClockOuterCenterAssign] at * <;> linarith
  · intro player
    have hforward := row player true false
    have hreverse := row player true true
    simp only [quantileClockOuterInequalityPolynomial,
      quantileClockOuterNeighborhoodPoly, Bool.false_eq_true, if_false,
      if_true, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_neg,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X] at hforward hreverse
    have hradius : (Rat.castHom ℝ)
        (quantileClockRadiusRat ι (level.1 + 1)) =
          quantileClockRadius ι (level.1 + 1) := by
      simpa using ratCast_quantileClockRadiusRat (ι := ι) (level.1 + 1)
    rw [hradius] at hforward hreverse
    rw [abs_le]
    constructor <;> dsimp [quantileClockOuterPointPair,
      finiteClockCenterPair, quantileClockOuterCenterAssign] at * <;> linarith

theorem quantileClockOuterObjective_eq_exploitability
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    {horizon : ℕ} (assign : QuantileClockOuterVar ι horizon → ℝ)
    (hsolution : SatisfiesQuantileClockOuterPolynomials
      reward horizon assign) :
    quantileClockOuterObjective horizon assign =
      quittingTerminalSemanticExploitability
        (quantileClockOuterPointPair horizon assign) := by
  let objective := quantileClockOuterObjective horizon assign
  let pair := quantileClockOuterPointPair horizon assign
  change objective = quittingTerminalSemanticExploitability pair
  have hupper (candidate : Option ι) :
      (match candidate with
        | none => 0
        | some player => pair.2 player - pair.1 player) ≤ objective := by
    have hrow := hsolution.2 (.inr (.inr candidate))
    rw [quantileClockOuterInequalityPolynomial,
      eval₂_quantileClockOuterObjectiveUpperPoly] at hrow
    dsimp [objective, pair, quantileClockOuterObjective,
      quantileClockOuterPointPair] at hrow ⊢
    linarith
  have hexplLe : quittingTerminalSemanticExploitability pair ≤ objective := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro player
    exact max_le (hupper none) (hupper (some player))
  have htight := hsolution.1 (.inr ())
  rw [quantileClockOuterEqualityPolynomial] at htight
  unfold quantileClockOuterObjectiveTightPoly at htight
  rw [MvPolynomial.eval₂_prod] at htight
  obtain ⟨candidate, -, hcand⟩ := Finset.prod_eq_zero_iff.mp htight
  rw [eval₂_quantileClockOuterObjectiveUpperPoly] at hcand
  cases candidate with
  | none =>
      have hobjective : objective = 0 := by
        dsimp [objective, quantileClockOuterObjective]
        linarith
      rw [hobjective]
      exact le_antisymm
        (quittingTerminalSemanticExploitability_nonneg pair)
        (hexplLe.trans hobjective.le)
  | some player =>
      have hobjective : objective = pair.2 player - pair.1 player := by
        dsimp [objective, pair, quantileClockOuterObjective,
          quantileClockOuterPointPair] at hcand ⊢
        linarith
      rw [hobjective]
      apply le_antisymm
      · exact (le_max_right 0 _).trans
          (le_finitePlayerMax
            (fun who => max 0 (pair.2 who - pair.1 who)) player)
      · simpa [hobjective] using hexplLe

def quantileClockOuterSemanticAssignment
    (horizon : ℕ) (pair : QuittingTerminalSemanticPair ι)
    (objective inverse : ℝ)
    (centerAssign : ∀ level : Fin horizon,
      FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ) :
    QuantileClockOuterVar ι horizon → ℝ
  | .inl (.payoff player) => pair.1 player
  | .inl (.cap player) => pair.2 player
  | .inl .objective => objective
  | .inl .strictInverse => inverse
  | .inr ⟨level, centerVariable⟩ => centerAssign level centerVariable

omit [DecidableEq ι] in
theorem quantileClockOuterPointPair_semanticAssignment
    (horizon : ℕ) (pair : QuittingTerminalSemanticPair ι)
    (objective inverse : ℝ)
    (centerAssign : ∀ level : Fin horizon,
      FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ) :
    quantileClockOuterPointPair horizon
      (quantileClockOuterSemanticAssignment horizon pair objective inverse
        centerAssign) = pair := by
  rfl

omit [DecidableEq ι] in
theorem quantileClockOuterObjective_semanticAssignment
    (horizon : ℕ) (pair : QuittingTerminalSemanticPair ι)
    (objective inverse : ℝ)
    (centerAssign : ∀ level : Fin horizon,
      FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ) :
    quantileClockOuterObjective horizon
      (quantileClockOuterSemanticAssignment horizon pair objective inverse
        centerAssign) = objective := by
  rfl

omit [DecidableEq ι] in
theorem quantileClockOuterCenterAssign_semanticAssignment
    (horizon : ℕ) (pair : QuittingTerminalSemanticPair ι)
    (objective inverse : ℝ)
    (centerAssign : ∀ level : Fin horizon,
      FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ)
    (level : Fin horizon) :
    quantileClockOuterCenterAssign level
      (quantileClockOuterSemanticAssignment horizon pair objective inverse
        centerAssign) = centerAssign level := by
  rfl

omit [DecidableEq ι] in
theorem quantileClockOuterObjectiveRows_semanticAssignment
    [Nonempty ι]
    (horizon : ℕ) (pair : QuittingTerminalSemanticPair ι)
    (inverse : ℝ)
    (centerAssign : ∀ level : Fin horizon,
      FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ) :
    (∀ candidate, 0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ)
      (quantileClockOuterSemanticAssignment horizon pair
        (quittingTerminalSemanticExploitability pair) inverse centerAssign)
      (quantileClockOuterObjectiveUpperPoly horizon candidate)) ∧
    MvPolynomial.eval₂ (Rat.castHom ℝ)
      (quantileClockOuterSemanticAssignment horizon pair
        (quittingTerminalSemanticExploitability pair) inverse centerAssign)
      (quantileClockOuterObjectiveTightPoly horizon) = 0 := by
  let objective := quittingTerminalSemanticExploitability pair
  let assign := quantileClockOuterSemanticAssignment horizon pair
    objective inverse centerAssign
  have hupper (candidate : Option ι) :
      0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ) assign
        (quantileClockOuterObjectiveUpperPoly horizon candidate) := by
    rw [eval₂_quantileClockOuterObjectiveUpperPoly]
    change 0 ≤ objective -
      match candidate with
      | none => 0
      | some player => pair.2 player - pair.1 player
    cases candidate with
    | none =>
        exact sub_nonneg.mpr (quittingTerminalSemanticExploitability_nonneg pair)
    | some player =>
        apply sub_nonneg.mpr
        exact (le_max_right 0 _).trans
          (le_finitePlayerMax
            (fun who => max 0 (pair.2 who - pair.1 who)) player)
  refine ⟨hupper, ?_⟩
  unfold quantileClockOuterObjectiveTightPoly
  rw [MvPolynomial.eval₂_prod]
  by_cases hzero : objective = 0
  · apply Finset.prod_eq_zero (Finset.mem_univ (none : Option ι))
    rw [eval₂_quantileClockOuterObjectiveUpperPoly]
    exact sub_eq_zero.mpr hzero
  · obtain ⟨player, -, hplayer⟩ := Finset.exists_mem_eq_sup'
        Finset.univ_nonempty
        (fun who => max 0 (pair.2 who - pair.1 who))
    apply Finset.prod_eq_zero (Finset.mem_univ (some player))
    rw [eval₂_quantileClockOuterObjectiveUpperPoly]
    apply sub_eq_zero.mpr
    have hobjectivePlayer :
        objective = max 0 (pair.2 player - pair.1 player) := by
      simpa [objective, quittingTerminalSemanticExploitability,
        quittingTerminalSemanticDebt, finitePlayerMax] using hplayer
    have hpositive : 0 < pair.2 player - pair.1 player := by
      have hmaxPositive : 0 < max 0 (pair.2 player - pair.1 player) := by
        rw [← hobjectivePlayer]
        exact lt_of_le_of_ne
          (quittingTerminalSemanticExploitability_nonneg pair)
          (Ne.symm hzero)
      by_contra hnot
      have hnonpos : pair.2 player - pair.1 player ≤ 0 := le_of_not_gt hnot
      rw [max_eq_left hnonpos] at hmaxPositive
      exact (lt_irrefl 0 hmaxPositive)
    change objective = pair.2 player - pair.1 player
    rw [← max_eq_right hpositive.le]
    exact hobjectivePlayer

theorem quantileClockOuterPointPair_mem_outer
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hcompression : HasEscapeAwareQuantileClockCompression
      (fun terminal player => (reward terminal player : ℝ)))
    {horizon : ℕ} (assign : QuantileClockOuterVar ι horizon → ℝ)
    (hsolution : SatisfiesQuantileClockOuterPolynomials
      reward horizon assign) :
    quantileClockOuterPointPair horizon assign ∈
      escapeAwareQuantileClockOuter
        (fun terminal player => (reward terminal player : ℝ))
        hcompression horizon := by
  intro level hlevel hle
  let index : Fin horizon := ⟨level - 1, by omega⟩
  have hindex : index.1 + 1 = level := by
    dsimp [index]
    omega
  let centerAssign := quantileClockOuterCenterAssign index assign
  let centerPair := finiteClockCenterPair
    (quantileClockSupport ι (index.1 + 1)) centerAssign
  have hcenterSolution : SatisfiesFiniteClockCenterPolynomials
      (Rat.castHom ℝ) reward
      (quantileClockSupport ι (index.1 + 1)) centerAssign :=
    satisfiesQuantileClockOuter_center reward assign hsolution index
  have hcenter : centerPair ∈ quittingFiniteClockSemanticCenter
      (fun terminal player => (reward terminal player : ℝ))
      (quantileClockSupport ι (index.1 + 1)) := by
    unfold quittingFiniteClockSemanticCenter
    rw [← rationalFiniteClockPolynomialSemanticImage_eq_reachable]
    exact ⟨centerAssign, hcenterSolution, rfl⟩
  have hwithin := quantileClockOuter_semanticPairWithin
    reward assign hsolution index
  have hdist : dist (quantileClockOuterPointPair horizon assign) centerPair ≤
      quantileClockRadius ι (index.1 + 1) :=
    dist_le_of_semanticPairWithin
      (quantileClockRadius_nonneg ι (index.1 + 1)) hwithin
  change Metric.infDist (quantileClockOuterPointPair horizon assign)
      (quittingFiniteClockSemanticCenter
        (fun terminal player => (reward terminal player : ℝ))
        (quantileClockSupport ι level)) ≤ quantileClockRadius ι level
  rw [← hindex]
  exact (Metric.infDist_le_dist_of_mem hcenter).trans hdist

theorem exists_quantileClockCenterAssignment_of_mem_outer
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hcompression : HasEscapeAwareQuantileClockCompression
      (fun terminal player => (reward terminal player : ℝ)))
    {horizon : ℕ} {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ escapeAwareQuantileClockOuter
      (fun terminal player => (reward terminal player : ℝ))
      hcompression horizon)
    (level : Fin horizon) :
    ∃ centerAssign : FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ,
      SatisfiesFiniteClockCenterPolynomials
        (Rat.castHom ℝ) reward
        (quantileClockSupport ι (level.1 + 1)) centerAssign ∧
      semanticPairWithin (quantileClockRadius ι (level.1 + 1)) pair
        (finiteClockCenterPair
          (quantileClockSupport ι (level.1 + 1)) centerAssign) := by
  let actualLevel := level.1 + 1
  let center := quittingFiniteClockSemanticCenter
    (fun terminal player => (reward terminal player : ℝ))
    (quantileClockSupport ι actualLevel)
  have houter := hpair actualLevel (by omega)
    (show actualLevel ≤ horizon by dsimp [actualLevel]; omega)
  obtain ⟨centerPair, hcenterPair, hnearest⟩ :=
    (quittingFiniteClockSemanticCenter_isCompact
      (fun terminal player => (reward terminal player : ℝ))
      (quantileClockSupport ι actualLevel)).exists_infDist_eq_dist
        (quittingFiniteClockSemanticCenter_nonempty
          (fun terminal player => (reward terminal player : ℝ))
          (quantileClockSupport ι actualLevel)) pair
  have hdist : dist pair centerPair ≤ quantileClockRadius ι actualLevel := by
    rw [← hnearest]
    exact houter
  have himage : centerPair ∈ finiteClockPolynomialSemanticImage
      (Rat.castHom ℝ) reward (quantileClockSupport ι actualLevel) := by
    rw [rationalFiniteClockPolynomialSemanticImage_eq_reachable]
    exact hcenterPair
  rcases himage with ⟨centerAssign, hcenterSolution, hcenterEq⟩
  refine ⟨centerAssign, hcenterSolution, ?_⟩
  rw [← hcenterEq]
  have hwithin := semanticPairWithin_dist pair centerPair
  exact ⟨fun player => (hwithin.1 player).trans hdist,
    fun player => (hwithin.2 player).trans hdist⟩

omit [DecidableEq ι] in
theorem eval₂_quantileClockOuterNeighborhoodPoly_semanticAssignment_nonneg
    {horizon : ℕ} (pair : QuittingTerminalSemanticPair ι)
    (objective inverse : ℝ)
    (centerAssign : ∀ level : Fin horizon,
      FiniteClockCenterVar ι
        (quantileClockSupport ι (level.1 + 1)) → ℝ)
    (index : QuantileClockOuterNeighborhoodIndex ι horizon)
    (hwithin : semanticPairWithin
      (quantileClockRadius ι (index.level.1 + 1)) pair
      (finiteClockCenterPair
        (quantileClockSupport ι (index.level.1 + 1))
        (centerAssign index.level))) :
    0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ)
      (quantileClockOuterSemanticAssignment horizon pair objective inverse
        centerAssign)
      (quantileClockOuterNeighborhoodPoly horizon index) := by
  have hradius : (Rat.castHom ℝ)
      (quantileClockRadiusRat ι (index.level.1 + 1)) =
        quantileClockRadius ι (index.level.1 + 1) := by
    simpa using ratCast_quantileClockRadiusRat
      (ι := ι) (index.level.1 + 1)
  rcases index with ⟨level, player, capCoordinate, reverse⟩
  cases capCoordinate <;> cases reverse
  all_goals
    simp only [quantileClockOuterNeighborhoodPoly, Bool.false_eq_true,
      if_false, if_true, MvPolynomial.eval₂_add, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_neg, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X]
    rw [hradius]
  · have hcoordinate := hwithin.1 player
    rw [abs_le] at hcoordinate
    dsimp [finiteClockCenterPair,
      quantileClockOuterSemanticAssignment] at hcoordinate ⊢
    linarith
  · have hcoordinate := hwithin.1 player
    rw [abs_le] at hcoordinate
    dsimp [finiteClockCenterPair,
      quantileClockOuterSemanticAssignment] at hcoordinate ⊢
    linarith
  · have hcoordinate := hwithin.2 player
    rw [abs_le] at hcoordinate
    dsimp [finiteClockCenterPair,
      quantileClockOuterSemanticAssignment] at hcoordinate ⊢
    linarith
  · have hcoordinate := hwithin.2 player
    rw [abs_le] at hcoordinate
    dsimp [finiteClockCenterPair,
      quantileClockOuterSemanticAssignment] at hcoordinate ⊢
    linarith

theorem exists_satisfiesQuantileClockOuterPolynomials_of_mem_outer
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hcompression : HasEscapeAwareQuantileClockCompression
      (fun terminal player => (reward terminal player : ℝ)))
    {horizon : ℕ} {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ escapeAwareQuantileClockOuter
      (fun terminal player => (reward terminal player : ℝ))
      hcompression horizon)
    (inverse : ℝ) :
    ∃ assign : QuantileClockOuterVar ι horizon → ℝ,
      SatisfiesQuantileClockOuterPolynomials reward horizon assign ∧
      quantileClockOuterPointPair horizon assign = pair ∧
      quantileClockOuterObjective horizon assign =
        quittingTerminalSemanticExploitability pair ∧
      assign (.inl .strictInverse) = inverse := by
  have hcenter (level : Fin horizon) :=
    exists_quantileClockCenterAssignment_of_mem_outer
      reward hcompression hpair level
  choose centerAssign hcenterSolution hcenterWithin using hcenter
  let objective := quittingTerminalSemanticExploitability pair
  let assign := quantileClockOuterSemanticAssignment horizon pair
    objective inverse centerAssign
  have hobjectiveRows := quantileClockOuterObjectiveRows_semanticAssignment
    horizon pair inverse centerAssign
  refine ⟨assign, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro index
      cases index with
      | inl row =>
          rcases row with ⟨level, centerIndex⟩
          have hindexed := hcenterSolution level
          rw [satisfiesFiniteClockCenterPolynomials_iff_indexed] at hindexed
          simpa [quantileClockOuterEqualityPolynomial,
            eval₂_quantileClockLiftCenterPolynomial, assign,
            quantileClockOuterCenterAssign_semanticAssignment] using
              hindexed.1 centerIndex
      | inr _ =>
          simpa [quantileClockOuterEqualityPolynomial, assign] using
            hobjectiveRows.2
    · intro index
      cases index with
      | inl row =>
          rcases row with ⟨level, centerIndex⟩
          have hindexed := hcenterSolution level
          rw [satisfiesFiniteClockCenterPolynomials_iff_indexed] at hindexed
          simpa [quantileClockOuterInequalityPolynomial,
            eval₂_quantileClockLiftCenterPolynomial, assign,
            quantileClockOuterCenterAssign_semanticAssignment] using
              hindexed.2 centerIndex
      | inr row =>
          cases row with
          | inl neighborhoodIndex =>
              simpa [quantileClockOuterInequalityPolynomial, assign] using
                eval₂_quantileClockOuterNeighborhoodPoly_semanticAssignment_nonneg
                  pair objective inverse centerAssign neighborhoodIndex
                  (hcenterWithin neighborhoodIndex.level)
          | inr candidate =>
              simpa [quantileClockOuterInequalityPolynomial, assign] using
                hobjectiveRows.1 candidate
  · exact quantileClockOuterPointPair_semanticAssignment
      horizon pair objective inverse centerAssign
  · exact quantileClockOuterObjective_semanticAssignment
      horizon pair objective inverse centerAssign
  · rfl

def quantileClockLowerStrictGapPoly
    (horizon : ℕ) (gamma : ℚ) :
    MvPolynomial (QuantileClockOuterVar ι horizon) ℚ :=
  MvPolynomial.C gamma - MvPolynomial.X (.inl .objective)

def quantileClockLowerStrictWitnessPoly
    (horizon : ℕ) (gamma : ℚ) :
    MvPolynomial (QuantileClockOuterVar ι horizon) ℚ :=
  quantileClockLowerStrictGapPoly horizon gamma *
      MvPolynomial.X (.inl .strictInverse) - 1

abbrev QuantileClockLowerQueryEqualityIndex (ι : Type) [Fintype ι]
    (horizon : ℕ) :=
  QuantileClockOuterEqualityIndex ι horizon ⊕ Unit

abbrev QuantileClockLowerQueryInequalityIndex (ι : Type) [Fintype ι]
    (horizon : ℕ) :=
  QuantileClockOuterInequalityIndex ι horizon ⊕ Unit

def quantileClockLowerQueryEqualityPolynomial
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) (gamma : ℚ) :
    QuantileClockLowerQueryEqualityIndex ι horizon →
      MvPolynomial (QuantileClockOuterVar ι horizon) ℚ
  | .inl index => quantileClockOuterEqualityPolynomial reward horizon index
  | .inr _ => quantileClockLowerStrictWitnessPoly horizon gamma

def quantileClockLowerQueryInequalityPolynomial
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) (gamma : ℚ) :
    QuantileClockLowerQueryInequalityIndex ι horizon →
      MvPolynomial (QuantileClockOuterVar ι horizon) ℚ
  | .inl index => quantileClockOuterInequalityPolynomial reward horizon index
  | .inr _ => quantileClockLowerStrictGapPoly horizon gamma

def QuantileClockLowerQueryFeasible
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) (gamma : ℚ) : Prop :=
  ∃ assign : QuantileClockOuterVar ι horizon → ℝ,
    (∀ index, MvPolynomial.eval₂ (Rat.castHom ℝ) assign
      (quantileClockLowerQueryEqualityPolynomial
        reward horizon gamma index) = 0) ∧
    (∀ index, 0 ≤ MvPolynomial.eval₂ (Rat.castHom ℝ) assign
      (quantileClockLowerQueryInequalityPolynomial
        reward horizon gamma index))

omit [DecidableEq ι] in
theorem eval₂_quantileClockLowerStrictGapPoly
    (horizon : ℕ) (gamma : ℚ)
    (assign : QuantileClockOuterVar ι horizon → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) assign
        (quantileClockLowerStrictGapPoly horizon gamma) =
      (gamma : ℝ) - quantileClockOuterObjective horizon assign := by
  simp [quantileClockLowerStrictGapPoly, quantileClockOuterObjective]

omit [DecidableEq ι] in
theorem eval₂_quantileClockLowerStrictWitnessPoly
    (horizon : ℕ) (gamma : ℚ)
    (assign : QuantileClockOuterVar ι horizon → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) assign
        (quantileClockLowerStrictWitnessPoly horizon gamma) =
      ((gamma : ℝ) - quantileClockOuterObjective horizon assign) *
        assign (.inl .strictInverse) - 1 := by
  simp [quantileClockLowerStrictWitnessPoly,
    eval₂_quantileClockLowerStrictGapPoly]

theorem quantileClockLowerQueryFeasible_iff
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hcompression : HasEscapeAwareQuantileClockCompression
      (fun terminal player => (reward terminal player : ℝ)))
    (horizon : ℕ) (gamma : ℚ) :
    QuantileClockLowerQueryFeasible reward horizon gamma ↔
      ∃ pair ∈ escapeAwareQuantileClockOuter
          (fun terminal player => (reward terminal player : ℝ))
          hcompression horizon,
        quittingTerminalSemanticExploitability pair < (gamma : ℝ) := by
  constructor
  · rintro ⟨assign, hequality, hinequality⟩
    have hbase : SatisfiesQuantileClockOuterPolynomials
        reward horizon assign := by
      constructor
      · intro index
        exact hequality (.inl index)
      · intro index
        exact hinequality (.inl index)
    let pair := quantileClockOuterPointPair horizon assign
    have hpair : pair ∈ escapeAwareQuantileClockOuter
        (fun terminal player => (reward terminal player : ℝ))
        hcompression horizon :=
      quantileClockOuterPointPair_mem_outer reward hcompression assign hbase
    have hobjective :=
      quantileClockOuterObjective_eq_exploitability reward assign hbase
    have hgap := hinequality (.inr ())
    have hwitness := hequality (.inr ())
    rw [quantileClockLowerQueryInequalityPolynomial,
      eval₂_quantileClockLowerStrictGapPoly] at hgap
    rw [quantileClockLowerQueryEqualityPolynomial,
      eval₂_quantileClockLowerStrictWitnessPoly] at hwitness
    have hgapNe :
        (gamma : ℝ) - quantileClockOuterObjective horizon assign ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul, zero_sub] at hwitness
      norm_num at hwitness
    have hgapPositive :
        0 < (gamma : ℝ) - quantileClockOuterObjective horizon assign :=
      lt_of_le_of_ne hgap (Ne.symm hgapNe)
    refine ⟨pair, hpair, ?_⟩
    rw [← hobjective]
    exact sub_pos.mp hgapPositive
  · rintro ⟨pair, hpair, hstrict⟩
    let gap : ℝ := (gamma : ℝ) -
      quittingTerminalSemanticExploitability pair
    have hgapPositive : 0 < gap := sub_pos.mpr hstrict
    obtain ⟨assign, hbase, hpairAssign, hobjective, hinverse⟩ :=
      exists_satisfiesQuantileClockOuterPolynomials_of_mem_outer
        reward hcompression hpair gap⁻¹
    refine ⟨assign, ?_, ?_⟩
    · intro index
      cases index with
      | inl index => exact hbase.1 index
      | inr _ =>
          rw [quantileClockLowerQueryEqualityPolynomial,
            eval₂_quantileClockLowerStrictWitnessPoly, hobjective, hinverse]
          change gap * gap⁻¹ - 1 = 0
          rw [mul_inv_cancel₀ hgapPositive.ne', sub_self]
    · intro index
      cases index with
      | inl index => exact hbase.2 index
      | inr _ =>
          rw [quantileClockLowerQueryInequalityPolynomial,
            eval₂_quantileClockLowerStrictGapPoly, hobjective]
          exact hgapPositive.le

abbrev RationalQuantileClockLowerInfeasibilityCertificate
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) (gamma : ℚ) :=
  Math.PolynomialInfeasibilityCertificate
    (QuantileClockLowerQueryEqualityIndex ι horizon)
    (QuantileClockLowerQueryInequalityIndex ι horizon)
    (quantileClockLowerQueryEqualityPolynomial reward horizon gamma)
    (quantileClockLowerQueryInequalityPolynomial reward horizon gamma)

theorem not_quantileClockLowerQueryFeasible_of_certificate
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (horizon : ℕ) (gamma : ℚ)
    (certificate : RationalQuantileClockLowerInfeasibilityCertificate
      reward horizon gamma) :
    ¬ QuantileClockLowerQueryFeasible reward horizon gamma := by
  exact Math.not_exists_of_polynomialInfeasibilityCertificate
    (Rat.castHom ℝ)
    (quantileClockLowerQueryEqualityPolynomial reward horizon gamma)
    (quantileClockLowerQueryInequalityPolynomial reward horizon gamma)
    certificate

theorem ratCast_le_escapeAwareQuantileClockLower_of_certificate
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hcompression : HasEscapeAwareQuantileClockCompression
      (fun terminal player => (reward terminal player : ℝ)))
    (horizon : ℕ) (gamma : ℚ)
    (certificate : RationalQuantileClockLowerInfeasibilityCertificate
      reward horizon gamma) :
    (gamma : ℝ) ≤ escapeAwareQuantileClockLower
      (fun terminal player => (reward terminal player : ℝ))
      hcompression horizon := by
  let realReward : {T : Finset ι // T.Nonempty} → Payoff ι :=
    fun terminal player => (reward terminal player : ℝ)
  let system := escapeAwareQuantileClockSystem realReward hcompression
  have hnotFeasible : ¬ QuantileClockLowerQueryFeasible
      reward horizon gamma :=
    not_quantileClockLowerQueryFeasible_of_certificate
      reward horizon gamma certificate
  change (gamma : ℝ) ≤ system.lowerValue
    quittingTerminalSemanticExploitability horizon
  unfold NestedOuterApproximation.lowerValue
  apply le_csInf
  · exact (system.attainable_nonempty.mono
      (system.attainable_subset_nestedOuter horizon)).image
        quittingTerminalSemanticExploitability
  · rintro value ⟨pair, hpair, rfl⟩
    by_contra hnot
    have hstrict :
        quittingTerminalSemanticExploitability pair < (gamma : ℝ) :=
      lt_of_not_ge hnot
    apply hnotFeasible
    rw [quantileClockLowerQueryFeasible_iff reward hcompression]
    exact ⟨pair, hpair, hstrict⟩

theorem ratCast_le_quittingTerminalExploitabilityInf_of_certificate
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hcompression : HasEscapeAwareQuantileClockCompression
      (fun terminal player => (reward terminal player : ℝ)))
    (horizon : ℕ) (gamma : ℚ)
    (certificate : RationalQuantileClockLowerInfeasibilityCertificate
      reward horizon gamma) :
    (gamma : ℝ) ≤ quittingTerminalExploitabilityInf
      (fun terminal player => (reward terminal player : ℝ)) := by
  exact (ratCast_le_escapeAwareQuantileClockLower_of_certificate
    reward hcompression horizon gamma certificate).trans
      (escapeAwareQuantileClockLower_le_exploitabilityInf
        (fun terminal player => (reward terminal player : ℝ))
        hcompression horizon)

theorem ratCast_le_escapeAwareQuantileClockLower_normalized_of_certificate
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (horizon : ℕ) (gamma : ℚ)
    (certificate : RationalQuantileClockLowerInfeasibilityCertificate
      reward horizon gamma) :
    (gamma : ℝ) ≤ escapeAwareQuantileClockLower
      (fun terminal player => (reward terminal player : ℝ))
      (hasEscapeAwareQuantileClockCompression_of_normalized
        (fun terminal player => (reward terminal player : ℝ)) hreward)
      horizon := by
  exact ratCast_le_escapeAwareQuantileClockLower_of_certificate
    reward
    (hasEscapeAwareQuantileClockCompression_of_normalized
      (fun terminal player => (reward terminal player : ℝ)) hreward)
    horizon gamma certificate

theorem ratCast_le_quittingTerminalExploitabilityInf_normalized_of_certificate
    [Nonempty ι]
    (reward : {T : Finset ι // T.Nonempty} → ι → ℚ)
    (hreward : ∀ terminal player, |(reward terminal player : ℝ)| ≤ 1)
    (horizon : ℕ) (gamma : ℚ)
    (certificate : RationalQuantileClockLowerInfeasibilityCertificate
      reward horizon gamma) :
    (gamma : ℝ) ≤ quittingTerminalExploitabilityInf
      (fun terminal player => (reward terminal player : ℝ)) := by
  exact ratCast_le_quittingTerminalExploitabilityInf_of_certificate
    reward
    (hasEscapeAwareQuantileClockCompression_of_normalized
      (fun terminal player => (reward terminal player : ℝ)) hreward)
    horizon gamma certificate

end GameTheory
