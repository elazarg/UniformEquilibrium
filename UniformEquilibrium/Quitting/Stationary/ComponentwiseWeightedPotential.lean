/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.SCC
import MathUE.FiniteBinaryWeightedPotential
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# Componentwise weighted potentials for quitting games

Affine membership gains admit a pure sure-exit coalition when their directed
influence graph is positively symmetrizable on each strongly connected
component.  Cross-component influences may be one-way and have arbitrary
sign.  The resulting pure stationary profile is an exact terminal Nash
profile against unrestricted behavioral deviations and its payoff is uniform.

This argument uses blockwise weighted potentials directly.  It does not pass
through the switched increasing-differences influence certificate, which does
not cover odd negative reciprocal cycles.
-/

noncomputable section

namespace GameTheory

open Math Math.CycleCoboundary Math.DirectedTransport MathUE
  QuittingSureSetOwnerRepair
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The own-membership gain of every player is affine in the background
coalition.  The coefficient is ordered as `coefficient affected influencer`.
-/
def IsAffineQuittingMembershipGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bias : ι → ℝ) (coefficient : ι → ι → ℝ) : Prop :=
  ∀ who S, who ∉ S →
    quittingSetReward reward (insert who S) who -
        quittingSetReward reward S who =
      bias who + ∑ other ∈ S, coefficient who other

/-- A nonzero affine influence edge.  Its source is the influencing player
and its target is the affected player. -/
def QuittingAffineInfluenceEdge (coefficient : ι → ι → ℝ) :=
  {pair : ι × ι // pair.1 ≠ pair.2 ∧ coefficient pair.2 pair.1 ≠ 0}

/-- Directed graph of nonzero off-diagonal affine membership influences. -/
def quittingAffineInfluenceGraph (coefficient : ι → ι → ℝ) :
    EdgeGraph ι (QuittingAffineInfluenceEdge coefficient) where
  source edge := edge.1.1
  target edge := edge.1.2

/-- Positive symmetrizing weights on every strongly connected component of
the affine influence graph.  A single global weight function records the
independently chosen weights on all components. -/
def IsComponentwisePositiveSymmetrizable
    (coefficient : ι → ι → ℝ) : Prop :=
  ∃ weight : ι → ℝ,
    (∀ who, 0 < weight who) ∧
      ∀ ⦃first second⦄, first ≠ second →
        LinkedTo (quittingAffineInfluenceGraph coefficient) first second →
          weight first * coefficient first second =
            weight second * coefficient second first

/-- Predecessors in the affine influence graph. -/
def quittingAffineInfluencePredecessors
    (coefficient : ι → ι → ℝ) (who : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun other =>
    Nonempty ((quittingAffineInfluenceGraph coefficient).Walk other who)

/-- A source-to-sink condensation level, represented by predecessor count. -/
def quittingAffineInfluenceLevel
    (coefficient : ι → ι → ℝ) (who : ι) : ℕ :=
  (quittingAffineInfluencePredecessors coefficient who).card

omit [DecidableEq ι] in
private theorem affineInfluenceEdge_level_le
    {coefficient : ι → ι → ℝ}
    (edge : QuittingAffineInfluenceEdge coefficient) :
    quittingAffineInfluenceLevel coefficient edge.1.1 ≤
      quittingAffineInfluenceLevel coefficient edge.1.2 := by
  classical
  apply Finset.card_le_card
  intro predecessor hpredecessor
  rw [quittingAffineInfluencePredecessors, Finset.mem_filter] at hpredecessor ⊢
  refine ⟨Finset.mem_univ predecessor, ?_⟩
  obtain ⟨walk⟩ := hpredecessor.2
  exact ⟨walk.append (EdgeGraph.Walk.singleton edge)⟩

omit [DecidableEq ι] in
private theorem affineInfluenceEdge_linked_of_level_eq
    {coefficient : ι → ι → ℝ}
    (edge : QuittingAffineInfluenceEdge coefficient)
    (hlevel : quittingAffineInfluenceLevel coefficient edge.1.1 =
      quittingAffineInfluenceLevel coefficient edge.1.2) :
    LinkedTo (quittingAffineInfluenceGraph coefficient)
      edge.1.1 edge.1.2 := by
  classical
  have hsubset : quittingAffineInfluencePredecessors coefficient edge.1.1 ⊆
      quittingAffineInfluencePredecessors coefficient edge.1.2 := by
    intro predecessor hpredecessor
    rw [quittingAffineInfluencePredecessors, Finset.mem_filter] at hpredecessor ⊢
    refine ⟨Finset.mem_univ predecessor, ?_⟩
    obtain ⟨walk⟩ := hpredecessor.2
    exact ⟨walk.append (EdgeGraph.Walk.singleton edge)⟩
  have heq : quittingAffineInfluencePredecessors coefficient edge.1.1 =
      quittingAffineInfluencePredecessors coefficient edge.1.2 := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [quittingAffineInfluenceLevel] using hlevel.ge
  constructor
  · exact ⟨EdgeGraph.Walk.singleton edge⟩
  · have htarget : edge.1.2 ∈
        quittingAffineInfluencePredecessors coefficient edge.1.2 := by
      rw [quittingAffineInfluencePredecessors, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨.nil⟩⟩
    rw [← heq, quittingAffineInfluencePredecessors,
      Finset.mem_filter] at htarget
    exact htarget.2

omit [DecidableEq ι] in
private theorem affineInfluence_future_zero
    {coefficient : ι → ι → ℝ} {who other : ι}
    (hlevel : quittingAffineInfluenceLevel coefficient who <
      quittingAffineInfluenceLevel coefficient other) :
    coefficient who other = 0 := by
  by_contra hnonzero
  have hne : other ≠ who := by
    intro heq
    subst other
    exact (lt_irrefl _ hlevel)
  let edge : QuittingAffineInfluenceEdge coefficient :=
    ⟨(other, who), hne, hnonzero⟩
  have hle := affineInfluenceEdge_level_le edge
  change quittingAffineInfluenceLevel coefficient other ≤
    quittingAffineInfluenceLevel coefficient who at hle
  omega

omit [DecidableEq ι] in
private theorem affineInfluence_within_symmetry
    {coefficient : ι → ι → ℝ} {weight : ι → ℝ}
    (hsymmetry : ∀ ⦃first second⦄, first ≠ second →
      LinkedTo (quittingAffineInfluenceGraph coefficient) first second →
        weight first * coefficient first second =
          weight second * coefficient second first)
    {who other : ι} (hne : who ≠ other)
    (hlevel : quittingAffineInfluenceLevel coefficient who =
      quittingAffineInfluenceLevel coefficient other) :
    weight who * coefficient who other =
      weight other * coefficient other who := by
  by_cases hforward : coefficient who other = 0
  · by_cases hbackward : coefficient other who = 0
    · simp [hforward, hbackward]
    · let edge : QuittingAffineInfluenceEdge coefficient :=
        ⟨(who, other), hne, hbackward⟩
      have hlinked := affineInfluenceEdge_linked_of_level_eq edge hlevel
      exact hsymmetry hne hlinked
  · let edge : QuittingAffineInfluenceEdge coefficient :=
      ⟨(other, who), Ne.symm hne, hforward⟩
    have hlinkedReverse := affineInfluenceEdge_linked_of_level_eq edge hlevel.symm
    exact hsymmetry hne ⟨hlinkedReverse.2, hlinkedReverse.1⟩

/-- Affine membership gains with positive SCC-wise symmetrizing weights
produce a stable pure exit coalition. -/
theorem exists_isQuittingSureExitSet_of_componentwiseWeightedPotential
    {bias : ι → ℝ} {coefficient : ι → ι → ℝ}
    (haffine : IsAffineQuittingMembershipGain reward bias coefficient)
    (hsymmetrizable : IsComponentwisePositiveSymmetrizable coefficient) :
    ∃ S, IsQuittingSureExitSet reward S := by
  classical
  obtain ⟨weight, hweightPositive, hsymmetry⟩ := hsymmetrizable
  let payoff : ι → Finset ι → ℝ := fun who S =>
    quittingSetReward reward S who
  let certificate : BinaryAffineBlockWeightedCertificate payoff :=
    { level := quittingAffineInfluenceLevel coefficient
      bias := bias
      coefficient := coefficient
      weight := weight
      weight_pos := hweightPositive
      joinGain_eq := by
        intro who S
        have hinsert : insert who (S.erase who) = insert who S := by
          ext player
          by_cases hplayer : player = who <;> simp [hplayer]
        have haffineAt := haffine who (S.erase who) (by simp)
        unfold payoff binaryJoinGain
        rwa [hinsert] at haffineAt
      future_coefficient_zero := fun hlevel =>
        affineInfluence_future_zero hlevel
      within_symmetry := by
        intro who other hne hlevel
        exact affineInfluence_within_symmetry hsymmetry hne hlevel }
  obtain ⟨S, hstable⟩ := certificate.exists_isBinaryGainStable
  refine ⟨S, ?_⟩
  constructor
  · intro who hwho
    have hgain := hstable who
    rw [if_pos hwho] at hgain
    unfold payoff binaryJoinGain at hgain
    rw [Finset.insert_eq_self.mpr hwho] at hgain
    linarith
  · intro who hwho
    have hgain := hstable who
    rw [if_neg hwho] at hgain
    unfold payoff binaryJoinGain at hgain
    rw [Finset.erase_eq_of_notMem hwho] at hgain
    linarith

/-- The pure stationary profile supported by the constructed exit coalition
is an exact terminal Nash profile against every unilateral behavioral
deviation. -/
theorem exists_pureStationary_exactTerminalNash_of_componentwiseWeightedPotential
    {bias : ι → ℝ} {coefficient : ι → ι → ℝ}
    (haffine : IsAffineQuittingMembershipGain reward bias coefficient)
    (hsymmetrizable : IsComponentwisePositiveSymmetrizable coefficient) :
    ∃ S,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot S)) := by
  obtain ⟨S, hS⟩ :=
    exists_isQuittingSureExitSet_of_componentwiseWeightedPotential
      haffine hsymmetrizable
  exact ⟨S,
    (isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet reward S).mpr hS⟩

/-- Componentwise positively symmetrizable affine quitting tables have a
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential
    {bias : ι → ℝ} {coefficient : ι → ι → ℝ}
    (haffine : IsAffineQuittingMembershipGain reward bias coefficient)
    (hsymmetrizable : IsComponentwisePositiveSymmetrizable coefficient) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨S, hS⟩ :=
    exists_isQuittingSureExitSet_of_componentwiseWeightedPotential
      haffine hsymmetrizable
  exact ⟨quittingSetReward reward S,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hS⟩

/-! ## Quadratic reward tables -/

/-- A quadratic coalition-payoff expression.  `linear owner member` is the
linear coefficient in `owner`'s reward and `pair owner first second` is the
coefficient of an unordered pair, represented symmetrically in its last two
arguments. -/
def quittingQuadraticSetExpression
    (linear : ι → ι → ℝ) (pair : ι → ι → ι → ℝ)
    (owner : ι) (S : Finset ι) : ℝ :=
  binaryAffineBlockPotential (linear owner) (pair owner) (fun _ => 1) ∅ S

/-- The complete extended quitting reward table has a linear-plus-quadratic
coalition representation.  Pair coefficients are symmetric in the two
coalition members; diagonal values are ignored by the expression. -/
def IsQuadraticQuittingReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (linear : ι → ι → ℝ) (pair : ι → ι → ι → ℝ) : Prop :=
  (∀ owner first second,
      pair owner first second = pair owner second first) ∧
    ∀ owner S,
      quittingSetReward reward S owner =
        quittingQuadraticSetExpression linear pair owner S

omit [Fintype ι] in
/-- Toggling a player's membership in a quadratic table adds its own linear
coefficient and exactly the pair coefficients involving that player. -/
theorem IsQuadraticQuittingReward.isAffineQuittingMembershipGain
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair) :
    IsAffineQuittingMembershipGain reward
      (fun who => linear who who) (fun who other => pair who who other) := by
  intro who S hwho
  rw [hquadratic.2 who (insert who S), hquadratic.2 who S]
  unfold quittingQuadraticSetExpression
  have hincrement := binaryAffineBlockPotential_insert
    (linear who) (pair who) (fun _ => (1 : ℝ))
    (outside := ∅) (selected := S) (who := who)
    (by simp) hwho (by simp)
    (fun other _ => by simpa using hquadratic.1 who who other)
  simpa using hincrement

omit [Fintype ι] in
/-- Equality of the two players' coefficients on every active unordered pair
makes the quadratic membership coefficients globally symmetrizable by unit
weights.  All passive coefficients remain unrestricted. -/
theorem IsQuadraticQuittingReward.componentwisePositiveSymmetrizable
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hactive : ∀ ⦃first second⦄, first ≠ second →
      pair first first second = pair second first second) :
    IsComponentwisePositiveSymmetrizable
      (fun who other => pair who who other) := by
  refine ⟨fun _ => 1, fun _ => zero_lt_one, ?_⟩
  intro first second hne _
  simp only [one_mul]
  calc
    pair first first second = pair second first second := hactive hne
    _ = pair second second first := hquadratic.1 second first second

/-- A quadratic table inherits the sure-exit theorem from positive SCC-wise
symmetrizability of its active pair coefficients. -/
theorem exists_isQuittingSureExitSet_of_quadratic_componentwiseWeightedPotential
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hsymmetrizable : IsComponentwisePositiveSymmetrizable
      (fun who other => pair who who other)) :
    ∃ S, IsQuittingSureExitSet reward S :=
  exists_isQuittingSureExitSet_of_componentwiseWeightedPotential
    hquadratic.isAffineQuittingMembershipGain hsymmetrizable

/-- The general weighted quadratic chamber has a pure stationary exact
terminal Nash profile against unrestricted behavioral deviations. -/
theorem exists_pureStationary_exactTerminalNash_of_quadratic_componentwiseWeightedPotential
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hsymmetrizable : IsComponentwisePositiveSymmetrizable
      (fun who other => pair who who other)) :
    ∃ S,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot S)) :=
  exists_pureStationary_exactTerminalNash_of_componentwiseWeightedPotential
    hquadratic.isAffineQuittingMembershipGain hsymmetrizable

/-- Positive SCC-wise symmetrizability of the active pair coefficients in a
quadratic table supplies a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_quadratic_componentwiseWeightedPotential
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hsymmetrizable : IsComponentwisePositiveSymmetrizable
      (fun who other => pair who who other)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential
    hquadratic.isAffineQuittingMembershipGain hsymmetrizable

/-- Quadratic quitting tables with equal active pair coefficients have a
literal sure-exit coalition. -/
theorem exists_isQuittingSureExitSet_of_quadratic_activePairSymmetry
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hactive : ∀ ⦃first second⦄, first ≠ second →
      pair first first second = pair second first second) :
    ∃ S, IsQuittingSureExitSet reward S :=
  exists_isQuittingSureExitSet_of_quadratic_componentwiseWeightedPotential
    hquadratic
    (hquadratic.componentwisePositiveSymmetrizable hactive)

/-- The quadratic corollary supplies a pure stationary exact terminal Nash
profile against unrestricted behavioral deviations. -/
theorem exists_pureStationary_exactTerminalNash_of_quadratic_activePairSymmetry
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hactive : ∀ ⦃first second⦄, first ≠ second →
      pair first first second = pair second first second) :
    ∃ S,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward (quittingPureSetRoot S)) :=
  exists_pureStationary_exactTerminalNash_of_quadratic_componentwiseWeightedPotential
    hquadratic
    (hquadratic.componentwisePositiveSymmetrizable hactive)

/-- Quadratic quitting tables with equal active pair coefficients have a
uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformPayoff_of_quadratic_activePairSymmetry
    {linear : ι → ι → ℝ} {pair : ι → ι → ι → ℝ}
    (hquadratic : IsQuadraticQuittingReward reward linear pair)
    (hactive : ∀ ⦃first second⦄, first ≠ second →
      pair first first second = pair second first second) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformPayoff_of_quadratic_componentwiseWeightedPotential
    hquadratic
    (hquadratic.componentwisePositiveSymmetrizable hactive)

end GameTheory
