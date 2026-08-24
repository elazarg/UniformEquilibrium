/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedPositiveLiveLimit
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.LowSurvivalScaleCompactness
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Compact limits of positive-rho low-survival landings

The positive side of the low-survival scale alternative supplies cofinally
many literal first-crossing rows.  This file compactifies those rows together
with their actual continuation vectors.  The purification radius and floor
slack vanish, so the original and purified roots have one common limit and
the clipped tails converge to the zero-slack punishment-floor clip of the
actual tail.

At finite scales the equations are two-ended: the predecessor value uses the
actual tail, while support optimality uses the clipped tail.  Source-family
coherence closes that first seam.  The crossing stage remains uniformly
reachable, so restarting the original approximate equilibrium there forces
the actual tail to the punishment floor in the limit.  Consequently the
actual and clipped limiting tails coincide.

The remaining alternatives are coupled.  If limiting absorption vanishes,
the root is all-Continue and the predecessor value does recur as the actual
tail, giving an exact finite-dimensional Nash--Bellman self-loop.  That loop
may still be a phantom annotation rather than the terminal payoff of the
repeated root.  Otherwise absorption is genuinely positive, but no argument
identifies predecessor and tail values.  Thus this compactification does not
by itself supply a semantic stationary Nash root or the positive-absorption
stationary splice interface.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical cofinal choice of positive-rho landing rows. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.selectedIndex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (cutoff : ℕ) : ℕ :=
  Classical.choose (landing.cofinally_landing cutoff)

theorem QuittingLowSurvivalPositiveRhoLandingFamily.le_selectedIndex
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (cutoff : ℕ) : cutoff ≤ landing.selectedIndex cutoff :=
  (Classical.choose_spec (landing.cofinally_landing cutoff)).1

theorem QuittingLowSurvivalPositiveRhoLandingFamily.selectedIndex_tendsto_atTop
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u) :
    Tendsto landing.selectedIndex atTop atTop := by
  rw [tendsto_atTop]
  intro cutoff
  exact Filter.eventually_atTop.2
    ⟨cutoff, fun n hn ↦ hn.trans (landing.le_selectedIndex n)⟩

/-- The original reached predecessor row selected at a scale. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.originalRoot
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) : ι → PMF Bool :=
  let source := landing.family.source n
  source.roots (source.crossingStage - 1)

/-- The actual continuation vector following the selected predecessor row. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.actualTail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) : Payoff ι :=
  let source := landing.family.source n
  quittingRootSequenceTailVector reward source.roots source.crossingStage

/-- The actual predecessor value before the selected crossing. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.predecessorValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) : Payoff ι :=
  let source := landing.family.source n
  quittingRootSequenceTailVector reward source.roots
    (source.crossingStage - 1)

/-- The literal root at the crossing stage, one row after the selected
predecessor. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.crossingRoot
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) : ι → PMF Bool :=
  let source := landing.family.source n
  source.roots source.crossingStage

/-- The actual continuation vector one row after the crossing root. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.futureTail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) : Payoff ι :=
  let source := landing.family.source n
  quittingRootSequenceTailVector reward source.roots
    (source.crossingStage + 1)

/-- The probability of reaching the literal crossing root from the start of
its source profile. -/
def QuittingLowSurvivalPositiveRhoLandingFamily.crossingSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) : ℝ :=
  let source := landing.family.source n
  quittingJointSurvivalWeight source.roots 0 source.crossingStage

theorem QuittingLowSurvivalPositiveRhoLandingFamily.predecessorValue_bellman
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) :
    landing.predecessorValue n =
      quittingRootSuccessorPayoff reward (landing.actualTail n)
        (landing.originalRoot n) := by
  funext who
  simpa [QuittingLowSurvivalPositiveRhoLandingFamily.predecessorValue,
    QuittingLowSurvivalPositiveRhoLandingFamily.actualTail,
    QuittingLowSurvivalPositiveRhoLandingFamily.originalRoot,
    quittingRootSequenceTailVector,
    Nat.sub_add_cancel (landing.family.source n).crossingStage_pos] using
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
        reward (landing.family.source n).roots who
          ((landing.family.source n).crossingStage - 1)

/-- The next literal source row gives a second, consecutive Bellman equation.
No recurrence of either root or value is asserted. -/
theorem QuittingLowSurvivalPositiveRhoLandingFamily.actualTail_bellman
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) :
    landing.actualTail n =
      quittingRootSuccessorPayoff reward (landing.futureTail n)
        (landing.crossingRoot n) := by
  funext who
  simpa [QuittingLowSurvivalPositiveRhoLandingFamily.actualTail,
    QuittingLowSurvivalPositiveRhoLandingFamily.futureTail,
    QuittingLowSurvivalPositiveRhoLandingFamily.crossingRoot,
    quittingRootSequenceTailVector] using
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
        reward (landing.family.source n).roots who
          (landing.family.source n).crossingStage

/-- The actual continuation vector is the terminal payoff of the retained
source continuation profile. -/
theorem QuittingLowSurvivalPositiveRhoLandingFamily.actualTail_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) :
    landing.actualTail n = fun who ↦ quittingTerminalPayoff reward
      (landing.family.source n).continuation who := by
  funext who
  rw [(landing.family.source n).continuation_eq]
  rfl

/-- Restarting an actual source at its crossing stage makes its actual tail
individually rational at the global Nash error divided by the probability of
reaching that stage. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.actualTail_rational
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (haccuracy : 0 ≤ accuracy)
    (hsurvival : 0 < quittingJointSurvivalWeight source.roots 0
      source.crossingStage) :
    QuittingSimonRationalPayoffAt reward
      (accuracy / quittingJointSurvivalWeight source.roots 0
        source.crossingStage)
      (quittingRootSequenceTailVector reward source.roots
        source.crossingStage) := by
  let survival := quittingJointSurvivalWeight source.roots 0
    source.crossingStage
  have hshift := isεQuittingRootSequenceNash_shift_of_survival_ge
    reward source.roots haccuracy hsurvival source.sourceNash
      source.crossingStage le_rfl
  have hbehavior :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
      (accuracy / survival)
      (fun offset ↦ source.roots (source.crossingStage + offset))).mp hshift
  have hprofile : quittingRootSequenceProfile reward
      (fun offset ↦ source.roots (source.crossingStage + offset)) 0 =
      source.continuation := by
    rw [source.continuation_eq,
      quittingRootSequenceProfile_eq_shift reward source.roots
        source.crossingStage]
  rw [hprofile] at hbehavior
  intro who
  have hpunishment := quittingPunishmentValue_le reward who source.continuation
  have hbest : quittingBestReplyValue reward source.continuation who ≤
      quittingTerminalPayoff reward source.continuation who +
        accuracy / survival := by
    apply quittingBestReplyValue_le
    intro deviation
    exact hbehavior who deviation
  have htail : quittingRootSequenceTailVector reward source.roots
      source.crossingStage who =
        quittingTerminalPayoff reward source.continuation who := by
    rw [source.continuation_eq]
    rfl
  rw [htail]
  linarith

/-- The crossing root itself is an approximate endpoint equilibrium against
its literal one-row-later tail, with the global error divided by the actual
probability of reaching that root. -/
theorem QuittingLowSurvivalPositiveRhoLandingFamily.crossingEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) (hsurvival : 0 < landing.crossingSurvival n) :
    IsεQuittingRootEndpointNash reward (landing.futureTail n)
      (landing.family.accuracy n / landing.crossingSurvival n)
      (landing.crossingRoot n) := by
  simpa [QuittingLowSurvivalPositiveRhoLandingFamily.futureTail,
    QuittingLowSurvivalPositiveRhoLandingFamily.crossingRoot,
    QuittingLowSurvivalPositiveRhoLandingFamily.crossingSurvival] using
    isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
      reward (landing.family.source n).roots
        (landing.family.source n).sourceNash
        (landing.family.source n).crossingStage hsurvival

/-- Compact carrier for one root and one actual terminal payoff vector. -/
def quittingLowSurvivalRootTailCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingRootSimplex ι × Payoff ι) :=
  (Set.univ : Set (QuittingRootSimplex ι)) ×ˢ
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)

omit [DecidableEq ι] in
theorem quittingLowSurvivalRootTailCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingLowSurvivalRootTailCarrier reward) := by
  exact isCompact_univ.prod isCompact_Icc

/-- The support budget already forces the purification threshold to vanish;
this need not be stored as an additional scale-family field. -/
theorem QuittingLowSurvivalScaleFamily.beta_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (family : QuittingLowSurvivalScaleFamily reward u) :
    Tendsto family.beta atTop (nhds 0) := by
  apply squeeze_zero' (g := family.tolerance)
  · exact Filter.Eventually.of_forall fun n ↦ (family.beta_pos n).le
  · apply Filter.Eventually.of_forall
    intro n
    have hnonneg : 0 ≤ 4 * quittingRewardBound reward *
        (Fintype.card ι : ℝ) * family.radius n := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num)
          (quittingRewardBound_nonneg reward)) (Nat.cast_nonneg _))
        (family.radius_pos n).le
    linarith [family.support_budget n]
  · exact family.tolerance_tendsto_zero

/-- The scale inequality and the vanishing threshold/radius force the actual
global approximate-equilibrium errors to vanish. -/
theorem QuittingLowSurvivalScaleFamily.accuracy_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (family : QuittingLowSurvivalScaleFamily reward u) :
    Tendsto family.accuracy atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n ↦ u * family.beta n * family.radius n) atTop (nhds 0) := by
    simpa using (family.beta_tendsto_zero.const_mul u).mul
      family.radius_tendsto_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ (family.accuracy_pos n).le
  · exact Filter.Eventually.of_forall fun n ↦ (family.scale n).le
  · exact hupper

/-- Each selected original root and actual tail lies in the compact carrier. -/
theorem QuittingLowSurvivalPositiveRhoLandingFamily.originalRoot_actualTail_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (n : ℕ) :
    (quittingSimplexOfRoot (landing.originalRoot n), landing.actualTail n) ∈
      quittingLowSurvivalRootTailCarrier reward := by
  refine ⟨Set.mem_univ _, ?_⟩
  rw [landing.actualTail_eq n]
  exact quittingTerminalPayoff_mem_rewardCube reward
    (landing.family.source n).continuation

/-- Exact support is sequentially closed when the support error tends to
zero jointly with the tail and simplex root. -/
theorem isQuittingSimplexRootSupportApproxNash_zero_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → Payoff ι) (root : ℕ → QuittingRootSimplex ι)
    (error : ℕ → ℝ) (limitTail : Payoff ι)
    (limitRoot : QuittingRootSimplex ι)
    (htail : Tendsto tail atTop (nhds limitTail))
    (hroot : Tendsto root atTop (nhds limitRoot))
    (herror : Tendsto error atTop (nhds 0))
    (hsupport : ∀ n,
      IsQuittingSimplexRootSupportApproxNash reward (tail n) (error n)
        (root n)) :
    IsQuittingSimplexRootSupportApproxNash reward limitTail 0 limitRoot := by
  have hpoint : Tendsto (fun n ↦ (tail n, root n)) atTop
      (nhds (limitTail, limitRoot)) := htail.prodMk_nhds hroot
  have hpositiveSupport : ∀ δ, 0 < δ →
      IsQuittingSimplexRootSupportApproxNash reward limitTail δ limitRoot := by
    intro δ hδ
    apply (isClosed_isQuittingSimplexRootSupportApproxNash reward δ).mem_of_tendsto
      hpoint
    have heventually : ∀ᶠ n in atTop, error n ≤ δ :=
      (tendsto_order.1 herror).2 δ hδ |>.mono fun _ hn ↦ hn.le
    filter_upwards [heventually] with n hn
    apply (isQuittingSimplexRootSupportApproxNash_iff reward
      (tail n) δ (root n)).2
    exact ((isQuittingSimplexRootSupportApproxNash_iff reward
      (tail n) (error n) (root n)).1 (hsupport n)).mono hn
  intro who
  constructor
  · by_cases hzero : limitRoot who true = 0
    · exact Or.inl hzero
    · right
      by_contra hnegative
      simp only [neg_zero] at hnegative
      have hgap : quittingRootEndpointDifference reward limitTail
          (quittingRootOfSimplex limitRoot) who < 0 := lt_of_not_ge hnegative
      let δ := -quittingRootEndpointDifference reward limitTail
        (quittingRootOfSimplex limitRoot) who / 2
      have hδ : 0 < δ := by dsimp [δ]; linarith
      have hsupportδ := hpositiveSupport δ hδ
      have hineq := (hsupportδ who).1.resolve_left hzero
      dsimp [δ] at hineq
      linarith
  · by_cases hzero : limitRoot who false = 0
    · exact Or.inl hzero
    · right
      by_contra hpositive
      have hgap : 0 < quittingRootEndpointDifference reward limitTail
          (quittingRootOfSimplex limitRoot) who := lt_of_not_ge hpositive
      let δ := quittingRootEndpointDifference reward limitTail
        (quittingRootOfSimplex limitRoot) who / 2
      have hδ : 0 < δ := by dsimp [δ]; linarith
      have hsupportδ := hpositiveSupport δ hδ
      have hineq := (hsupportδ who).2.resolve_left hzero
      dsimp [δ] at hineq
      linarith

omit [DecidableEq ι] in
/-- Coordinate convergence for the finite product of Boolean simplices. -/
theorem tendsto_quittingRootSimplex_apply
    {root : ℕ → QuittingRootSimplex ι} {limit : QuittingRootSimplex ι}
    (hroot : Tendsto root atTop (nhds limit)) (who : ι) (action : Bool) :
    Tendsto (fun n ↦ root n who action) atTop (nhds (limit who action)) := by
  exact ((continuous_apply action).comp
    (continuous_subtype_val.comp (continuous_apply who))).continuousAt
      |>.tendsto.comp hroot

omit [DecidableEq ι] in
/-- A Boolean simplex point is determined by its `true` coordinate. -/
theorem quittingRootSimplex_ext_true
    {left right : QuittingRootSimplex ι}
    (htrue : ∀ who, left who true = right who true) : left = right := by
  funext who
  apply Subtype.ext
  funext action
  cases action with
  | false =>
      have hleft := (left who).property.2
      have hright := (right who).property.2
      have htrue' : (left who).val true = (right who).val true := htrue who
      simp only [Fintype.sum_bool] at hleft hright
      rw [htrue'] at hleft
      linarith
  | true => exact htrue who

/-- The exact compact datum surviving from a positive-rho landing family. -/
structure QuittingLowSurvivalPositiveRhoCompactLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u) where
  index : ℕ → ℕ
  index_tendsto_atTop : Tendsto index atTop atTop
  landingAt : ∀ n,
    landing.rho ≤ landing.family.purifiedMass (index n) ∧
      landing.rho / 2 < quittingStationaryContinueMass
        (landing.originalRoot (index n)) ∧
      u * landing.rho / 2 < landing.crossingSurvival (index n) ∧
      landing.crossingSurvival (index n) ≤ u
  root : QuittingRootSimplex ι
  actualTail : Payoff ι
  clippedTail : Payoff ι
  predecessorValue : Payoff ι
  originalRoot_tendsto : Tendsto
    (fun n ↦ quittingSimplexOfRoot
      (landing.originalRoot (index n))) atTop (nhds root)
  purifiedRoot_tendsto : Tendsto
    (fun n ↦ quittingSimplexOfRoot
      (landing.family.purifiedRoot (index n))) atTop (nhds root)
  actualTail_tendsto : Tendsto
    (fun n ↦ landing.actualTail (index n)) atTop (nhds actualTail)
  clippedTail_tendsto : Tendsto
    (fun n ↦ (landing.family.source (index n)).clippedTail
      (landing.family.tolerance (index n))) atTop (nhds clippedTail)
  predecessorValue_tendsto : Tendsto
    (fun n ↦ landing.predecessorValue (index n)) atTop
      (nhds predecessorValue)
  clippedTail_eq : clippedTail =
    quittingPunishmentFloorClipAt reward 0 actualTail
  actualTail_rational : QuittingSimonRationalPayoffAt reward 0 actualTail
  clippedTail_eq_actual : clippedTail = actualTail
  predecessorValue_bellman : predecessorValue =
    quittingRootSuccessorPayoff reward actualTail
      (quittingRootOfSimplex root)
  exactSupport : IsQuittingRootSupportApproxNash reward clippedTail 0
    (quittingRootOfSimplex root)
  continueMass_lower : landing.rho ≤
    quittingStationaryContinueMass (quittingRootOfSimplex root)
  actualTail_mem : actualTail ∈
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)
  predecessorValue_mem : predecessorValue ∈
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)

/-- Conditional endpoint error at the next literal source row retained by a
positive-rho compact limit. -/
def QuittingLowSurvivalPositiveRhoCompactLimit.crossingError
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (n : ℕ) : ℝ :=
  landing.family.accuracy (limit.index n) /
    landing.crossingSurvival (limit.index n)

/-- Uniform reach of the crossing row makes its conditional endpoint error
vanish along the retained source indices. -/
theorem QuittingLowSurvivalPositiveRhoCompactLimit.crossingError_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    Tendsto limit.crossingError atTop (nhds 0) := by
  have hlower : 0 < u * landing.rho / 2 :=
    div_pos (mul_pos landing.family.u_pos landing.rho_pos) (by norm_num)
  have haccuracy : Tendsto
      (fun n ↦ landing.family.accuracy (limit.index n)) atTop (nhds 0) :=
    landing.family.accuracy_tendsto_zero.comp limit.index_tendsto_atTop
  have hupper : Tendsto (fun n ↦
      landing.family.accuracy (limit.index n) / (u * landing.rho / 2))
      atTop (nhds 0) := by
    simpa only [zero_div] using haccuracy.div_const (u * landing.rho / 2)
  apply squeeze_zero'
    (g := fun n ↦ landing.family.accuracy (limit.index n) /
      (u * landing.rho / 2))
  · apply Filter.Eventually.of_forall
    intro n
    exact div_nonneg (landing.family.accuracy_pos (limit.index n)).le
      (hlower.trans (limit.landingAt n).2.2.1).le
  · apply Filter.Eventually.of_forall
    intro n
    exact div_le_div_of_nonneg_left
      (landing.family.accuracy_pos (limit.index n)).le hlower
        (limit.landingAt n).2.2.1.le
  · exact hupper

theorem QuittingLowSurvivalPositiveRhoCompactLimit.clippedTail_rational
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    QuittingSimonRationalPayoffAt reward 0 limit.clippedTail := by
  rw [limit.clippedTail_eq_actual]
  exact limit.actualTail_rational

theorem QuittingLowSurvivalPositiveRhoCompactLimit.exactEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    IsεQuittingRootEndpointNash reward limit.clippedTail 0
      (quittingRootOfSimplex limit.root) := by
  exact isQuittingRootEndpointNash_of_supportApproxNash reward
    limit.clippedTail (quittingRootOfSimplex limit.root) le_rfl
      limit.exactSupport

/-- Positive `rho` keeps the limiting root away from every sure-quitter
face, but it does not keep it away from the all-Continue vertex. -/
theorem QuittingLowSurvivalPositiveRhoCompactLimit.noSureQuitter
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    ¬QuittingRootHasSureQuitter (quittingRootOfSimplex limit.root) := by
  rintro ⟨who, hwho⟩
  have hzero := quittingStationaryContinueMass_of_sureQuitter hwho
  have hpositive : 0 < quittingStationaryContinueMass
      (quittingRootOfSimplex limit.root) :=
    landing.rho_pos.trans_le limit.continueMass_lower
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

/-- Zero limiting absorption identifies the common limiting root exactly as
all-Continue. -/
theorem QuittingLowSurvivalPositiveRhoCompactLimit.root_eq_allContinue_of_absorption_eq_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex limit.root) = 0) :
    quittingRootOfSimplex limit.root =
      (quittingAllContinueRoot : ι → PMF Bool) := by
  have hmass : quittingStationaryContinueMass
      (quittingRootOfSimplex limit.root) = 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  funext who
  exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hmass who

/-- If absorption vanishes at the compact limit, the limiting root is
all-Continue and the predecessor Bellman value equals the actual tail. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.predecessorValue_eq_actualTail_of_absorption_eq_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex limit.root) = 0) :
    limit.predecessorValue = limit.actualTail := by
  have hroot := limit.root_eq_allContinue_of_absorption_eq_zero habsorption
  rw [limit.predecessorValue_bellman, hroot,
    quittingRootSuccessorPayoff_allContinueRoot_eq]

/-- Closing the temporal seam at any absorption level gives an exact
Nash--Bellman self-loop. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.selfEdge_of_valueRecurrence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (hrecurrence : limit.predecessorValue = limit.actualTail) :
    IsQuittingNashBellmanEdge reward
      (limit.actualTail, limit.root) (limit.actualTail, limit.root) := by
  constructor
  · calc
      limit.actualTail = limit.predecessorValue := hrecurrence.symm
      _ = quittingRootSuccessorPayoff reward limit.actualTail
          (quittingRootOfSimplex limit.root) :=
        limit.predecessorValue_bellman
  · rw [← limit.clippedTail_eq_actual]
    exact limit.exactEndpointNash

/-- The only surviving failure of predecessor/tail recurrence has genuinely
positive limiting absorption. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.positiveAbsorption_or_predecessorValue_eq_actualTail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    0 < quittingRootAbsorptionMass (quittingRootOfSimplex limit.root) ∨
      limit.predecessorValue = limit.actualTail := by
  rcases eq_or_lt_of_le
      (quittingRootAbsorptionMass_nonneg
        (quittingRootOfSimplex limit.root)) with hzero | hpositive
  · exact Or.inr
      (limit.predecessorValue_eq_actualTail_of_absorption_eq_zero hzero.symm)
  · exact Or.inl hpositive

/-- On the zero-absorption side the two source-family seams close to an exact
Nash--Bellman self-loop.  This is a finite-dimensional phantom self-loop, not
an identification with the terminal payoff of the repeated all-Continue
profile. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.selfEdge_of_zeroAbsorption
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex limit.root) = 0) :
    IsQuittingNashBellmanEdge reward
      (limit.actualTail, limit.root) (limit.actualTail, limit.root) := by
  exact limit.selfEdge_of_valueRecurrence
    (limit.predecessorValue_eq_actualTail_of_absorption_eq_zero habsorption)

/-- The honest unsolved all-Continue output: a nonzero bounded rational
phantom value with exact support at the all-Continue root.  The displayed
value is a finite-dimensional Bellman annotation; it is not asserted to be
the terminal payoff of the repeated root. -/
structure QuittingLowSurvivalAllContinuePhantom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  value : Payoff ι
  value_ne_zero : value ≠ 0
  notZeroSolo : ¬IsQuittingZeroSolo reward
  value_mem : value ∈ Set.Icc (fun _ ↦ -quittingRewardBound reward)
    (fun _ ↦ quittingRewardBound reward)
  rational : QuittingSimonRationalPayoffAt reward 0 value
  support : IsQuittingRootSupportApproxNash reward value 0
    (quittingAllContinueRoot : ι → PMF Bool)

/-- Exact all-Continue support says every solo quit payoff lies below the
phantom continuation annotation. -/
theorem QuittingLowSurvivalAllContinuePhantom.solo_le_value
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (phantom : QuittingLowSurvivalAllContinuePhantom reward) (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ phantom.value who := by
  have hendpoint : IsεQuittingRootEndpointNash reward phantom.value 0
      (quittingAllContinueRoot : ι → PMF Bool) :=
    isQuittingRootEndpointNash_of_supportApproxNash reward phantom.value
      quittingAllContinueRoot le_rfl phantom.support
  simpa [quittingAllContinueRoot] using (hendpoint who).1

/-- A residual phantom lies outside the zero-solo class, hence some player
has a strictly positive solo deviation payoff. -/
theorem QuittingLowSurvivalAllContinuePhantom.exists_positiveSolo
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (phantom : QuittingLowSurvivalAllContinuePhantom reward) :
    ∃ who, 0 < reward (quittingSingletonTerminal who) who := by
  simpa only [IsQuittingZeroSolo, not_forall, not_le] using
    phantom.notZeroSolo

/-- The phantom value is genuinely different from the terminal payoff of
the all-Continue profile.  This is the exact semantic obstruction to treating
the finite-dimensional self-loop as an equilibrium payoff. -/
theorem QuittingLowSurvivalAllContinuePhantom.exists_terminalPayoff_gap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (phantom : QuittingLowSurvivalAllContinuePhantom reward) :
    ∃ who, quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) who ≠ phantom.value who := by
  obtain ⟨who, hpositive⟩ := phantom.exists_positiveSolo
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_quittingAlwaysContinue]
  have hvalue : 0 < phantom.value who :=
    hpositive.trans_le (phantom.solo_le_value who)
  exact ne_of_lt hvalue

/-- On the zero-absorption side, zero phantom value is exactly the checked
zero-solo uniform branch.  The only residual is a nonzero rational
all-Continue phantom annotation. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.zeroPayoff_or_phantom_of_zeroAbsorption
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex limit.root) = 0) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι) ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom reward) := by
  have hroot := limit.root_eq_allContinue_of_absorption_eq_zero habsorption
  by_cases hzeroSolo : IsQuittingZeroSolo reward
  · left
    exact quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward
      hzeroSolo
  · right
    have hvalueNe : limit.actualTail ≠ 0 := by
      intro hzero
      apply hzeroSolo
      intro who
      have hendpoint := limit.exactEndpointNash who
      rw [limit.clippedTail_eq_actual, hzero, hroot] at hendpoint
      simpa [quittingAllContinueRoot] using hendpoint.1
    refine ⟨{
      value := limit.actualTail
      value_ne_zero := hvalueNe
      notZeroSolo := hzeroSolo
      value_mem := limit.actualTail_mem
      rational := limit.actualTail_rational
      support := ?_ }⟩
    rw [← limit.clippedTail_eq_actual, ← hroot]
    exact limit.exactSupport

/-- **Positive-rho compactification.**  Cofinal literal landing rows have a
subsequence on which the actual reached row/tail Bellman datum and the
floor-clipped support datum converge.  Vanishing purification identifies the
roots, while a source restart at the uniformly reached crossing identifies
the actual and clipped limiting tails. -/
theorem exists_quittingLowSurvivalPositiveRhoCompactLimit
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u) :
    Nonempty (QuittingLowSurvivalPositiveRhoCompactLimit landing) := by
  let firstData : ℕ → QuittingRootSimplex ι × Payoff ι := fun n ↦
    let index := landing.selectedIndex n
    (quittingSimplexOfRoot (landing.originalRoot index),
      landing.actualTail index)
  have hfirstData : ∀ n, firstData n ∈
      quittingLowSurvivalRootTailCarrier reward := by
    intro n
    exact landing.originalRoot_actualTail_mem (landing.selectedIndex n)
  obtain ⟨firstLimit, hfirstLimitMem, firstSubsequence,
      hfirstSubsequence, hfirstLimit⟩ :=
    (quittingLowSurvivalRootTailCarrier_isCompact reward).tendsto_subseq
      hfirstData
  let firstIndex : ℕ → ℕ := fun n ↦
    landing.selectedIndex (firstSubsequence n)
  have hfirstIndex : Tendsto firstIndex atTop atTop :=
    landing.selectedIndex_tendsto_atTop.comp hfirstSubsequence.tendsto_atTop
  have horiginalFirst : Tendsto
      (fun n ↦ quittingSimplexOfRoot (landing.originalRoot (firstIndex n)))
      atTop (nhds firstLimit.1) := by
    exact (continuous_fst.tendsto firstLimit).comp hfirstLimit
  have hactualFirst : Tendsto
      (fun n ↦ landing.actualTail (firstIndex n)) atTop
      (nhds firstLimit.2) := by
    exact (continuous_snd.tendsto firstLimit).comp hfirstLimit
  let secondData : ℕ → QuittingRootSimplex ι × Payoff ι := fun n ↦
    (quittingSimplexOfRoot (landing.family.purifiedRoot (firstIndex n)),
      (landing.family.source (firstIndex n)).clippedTail
        (landing.family.tolerance (firstIndex n)))
  have hsecondData : ∀ n, secondData n ∈
      quittingLowSurvivalRootTailCarrier reward := by
    intro n
    refine ⟨Set.mem_univ _, ?_⟩
    constructor
    · intro who
      exact neg_le_of_abs_le
        ((landing.family.core (firstIndex n)).tail_bound who)
    · intro who
      exact le_of_abs_le
        ((landing.family.core (firstIndex n)).tail_bound who)
  obtain ⟨secondLimit, _hsecondLimitMem, secondSubsequence,
      hsecondSubsequence, hsecondLimit⟩ :=
    (quittingLowSurvivalRootTailCarrier_isCompact reward).tendsto_subseq
      hsecondData
  let index : ℕ → ℕ := fun n ↦ firstIndex (secondSubsequence n)
  have hindex : Tendsto index atTop atTop :=
    hfirstIndex.comp hsecondSubsequence.tendsto_atTop
  have hlandingAt : ∀ n,
      landing.rho ≤ landing.family.purifiedMass (index n) ∧
        landing.rho / 2 < quittingStationaryContinueMass
          (landing.originalRoot (index n)) ∧
        u * landing.rho / 2 < landing.crossingSurvival (index n) ∧
        landing.crossingSurvival (index n) ≤ u := by
    intro n
    simpa [index, firstIndex,
      QuittingLowSurvivalPositiveRhoLandingFamily.selectedIndex,
      QuittingLowSurvivalPositiveRhoLandingFamily.originalRoot,
      QuittingLowSurvivalPositiveRhoLandingFamily.crossingSurvival] using
      (Classical.choose_spec
        (landing.cofinally_landing
          (firstSubsequence (secondSubsequence n)))).2
  have horiginal : Tendsto
      (fun n ↦ quittingSimplexOfRoot (landing.originalRoot (index n)))
      atTop (nhds firstLimit.1) :=
    horiginalFirst.comp hsecondSubsequence.tendsto_atTop
  have hactual : Tendsto (fun n ↦ landing.actualTail (index n)) atTop
      (nhds firstLimit.2) :=
    hactualFirst.comp hsecondSubsequence.tendsto_atTop
  have hpurified : Tendsto
      (fun n ↦ quittingSimplexOfRoot
        (landing.family.purifiedRoot (index n))) atTop
      (nhds secondLimit.1) := by
    exact (continuous_fst.tendsto secondLimit).comp hsecondLimit
  have hclipped : Tendsto
      (fun n ↦ (landing.family.source (index n)).clippedTail
        (landing.family.tolerance (index n))) atTop
      (nhds secondLimit.2) := by
    exact (continuous_snd.tendsto secondLimit).comp hsecondLimit
  have hradius : Tendsto (fun n ↦ landing.family.radius (index n)) atTop
      (nhds 0) := landing.family.radius_tendsto_zero.comp hindex
  have hrootEq : secondLimit.1 = firstLimit.1 := by
    apply quittingRootSimplex_ext_true
    intro who
    have hpurifiedWho := tendsto_quittingRootSimplex_apply hpurified who true
    have horiginalWho := tendsto_quittingRootSimplex_apply horiginal who true
    have habs : Tendsto (fun n ↦
        |(quittingSimplexOfRoot
              (landing.family.purifiedRoot (index n)) who true : ℝ) -
          (quittingSimplexOfRoot
              (landing.originalRoot (index n)) who true : ℝ)|) atTop
        (nhds |(secondLimit.1 who true : ℝ) -
          (firstLimit.1 who true : ℝ)|) :=
      hpurifiedWho.sub horiginalWho |>.abs
    have hclose : ∀ᶠ n in atTop,
        |(quittingSimplexOfRoot
              (landing.family.purifiedRoot (index n)) who true : ℝ) -
          (quittingSimplexOfRoot
              (landing.originalRoot (index n)) who true : ℝ)| ≤
            landing.family.radius (index n) := by
      apply Filter.Eventually.of_forall
      intro n
      have h := (landing.family.core (index n)).coordinateClose who
      simpa [QuittingLowSurvivalScaleFamily.purifiedRoot,
        QuittingLowSurvivalPositiveRhoLandingFamily.originalRoot,
        quittingSimplexOfRoot, Math.ProbabilityMassFunction.toVector]
        using h.le
    have hle : |(secondLimit.1 who true : ℝ) -
        (firstLimit.1 who true : ℝ)| ≤ 0 :=
      le_of_tendsto_of_tendsto habs hradius hclose
    have hreal : (secondLimit.1 who true : ℝ) =
        (firstLimit.1 who true : ℝ) := by
      exact sub_eq_zero.mp (abs_eq_zero.mp
        (le_antisymm hle (abs_nonneg _)))
    exact hreal
  have htolerance : Tendsto
      (fun n ↦ landing.family.tolerance (index n)) atTop (nhds 0) :=
    landing.family.tolerance_tendsto_zero.comp hindex
  let crossingSurvival : ℕ → ℝ := fun n ↦
    quittingJointSurvivalWeight (landing.family.source (index n)).roots 0
      (landing.family.source (index n)).crossingStage
  let conditionalError : ℕ → ℝ := fun n ↦
    landing.family.accuracy (index n) / crossingSurvival n
  have hlower : 0 < u * landing.rho / 2 := by
    exact div_pos (mul_pos landing.family.u_pos landing.rho_pos) (by norm_num)
  have hcrossingLower : ∀ n, u * landing.rho / 2 < crossingSurvival n := by
    intro n
    exact (Classical.choose_spec
      (landing.cofinally_landing
        (firstSubsequence (secondSubsequence n)))).2.2.2.1
  have haccuracy : Tendsto
      (fun n ↦ landing.family.accuracy (index n)) atTop (nhds 0) :=
    landing.family.accuracy_tendsto_zero.comp hindex
  have hconditionalError : Tendsto conditionalError atTop (nhds 0) := by
    have hupper : Tendsto (fun n ↦
        landing.family.accuracy (index n) / (u * landing.rho / 2)) atTop
        (nhds 0) := by
      simpa only [zero_div] using haccuracy.div_const (u * landing.rho / 2)
    apply squeeze_zero'
      (g := fun n ↦ landing.family.accuracy (index n) /
        (u * landing.rho / 2))
    · apply Filter.Eventually.of_forall
      intro n
      exact div_nonneg (landing.family.accuracy_pos (index n)).le
        (hlower.trans (hcrossingLower n)).le
    · apply Filter.Eventually.of_forall
      intro n
      exact div_le_div_of_nonneg_left
        (landing.family.accuracy_pos (index n)).le hlower
          (hcrossingLower n).le
    · exact hupper
  have hactualRationalAt : ∀ n,
      QuittingSimonRationalPayoffAt reward (conditionalError n)
        (landing.actualTail (index n)) := by
    intro n
    have hsource := (landing.family.source (index n)).actualTail_rational
      (landing.family.accuracy_pos (index n)).le
      (hlower.trans (hcrossingLower n))
    simpa [conditionalError, crossingSurvival,
      QuittingLowSurvivalPositiveRhoLandingFamily.actualTail] using hsource
  have hactualRational : QuittingSimonRationalPayoffAt reward 0
      firstLimit.2 := by
    intro who
    have hleft : Tendsto (fun n ↦ quittingPunishmentValue reward who -
        conditionalError n) atTop
        (nhds (quittingPunishmentValue reward who)) := by
      simpa using tendsto_const_nhds.sub hconditionalError
    have hright := tendsto_pi_nhds.1 hactual who
    have hle : quittingPunishmentValue reward who ≤ firstLimit.2 who :=
      le_of_tendsto_of_tendsto hleft hright
        (Filter.Eventually.of_forall fun n ↦ hactualRationalAt n who)
    simpa using hle
  have hclipExpected : Tendsto
      (fun n ↦ quittingPunishmentFloorClipAt reward
        (landing.family.tolerance (index n))
        (landing.actualTail (index n))) atTop
      (nhds (quittingPunishmentFloorClipAt reward 0 firstLimit.2)) := by
    rw [tendsto_pi_nhds]
    intro who
    simp only [quittingPunishmentFloorClipAt_apply]
    exact (tendsto_pi_nhds.1 hactual who).max
      (tendsto_const_nhds.sub htolerance)
  have hclippedAsClip : Tendsto
      (fun n ↦ (landing.family.source (index n)).clippedTail
        (landing.family.tolerance (index n))) atTop
      (nhds (quittingPunishmentFloorClipAt reward 0 firstLimit.2)) := by
    apply hclipExpected.congr'
    apply Filter.Eventually.of_forall
    intro n
    unfold QuittingLowSurvivalFirstCrossingSourceAt.clippedTail
    exact congrArg
      (quittingPunishmentFloorClipAt reward
        (landing.family.tolerance (index n)))
      (landing.actualTail_eq (index n))
  have hclippedEq : secondLimit.2 =
      quittingPunishmentFloorClipAt reward 0 firstLimit.2 :=
    tendsto_nhds_unique hclipped hclippedAsClip
  have hclippedEqActual : secondLimit.2 = firstLimit.2 := by
    calc
      secondLimit.2 = quittingPunishmentFloorClipAt reward 0 firstLimit.2 :=
        hclippedEq
      _ = firstLimit.2 :=
        quittingPunishmentFloorClipAt_eq_self_of_rational reward 0
          firstLimit.2 hactualRational
  have hpredecessor : Tendsto
      (fun n ↦ landing.predecessorValue (index n)) atTop
      (nhds (quittingRootSuccessorPayoff reward firstLimit.2
        (quittingRootOfSimplex firstLimit.1))) := by
    have hsuccessor : Tendsto
        (fun n ↦ quittingRootSuccessorPayoff reward
          (landing.actualTail (index n))
          (landing.originalRoot (index n))) atTop
        (nhds (quittingRootSuccessorPayoff reward firstLimit.2
          (quittingRootOfSimplex firstLimit.1))) := by
      have hpair : Tendsto (fun n ↦
          (landing.actualTail (index n),
            quittingSimplexOfRoot (landing.originalRoot (index n)))) atTop
          (nhds (firstLimit.2, firstLimit.1)) :=
        hactual.prodMk_nhds horiginal
      have h := (continuous_quittingRootSuccessorPayoff_simplex reward).tendsto
        (firstLimit.2, firstLimit.1) |>.comp hpair
      change Tendsto (fun n ↦ quittingRootSuccessorPayoff reward
        (landing.actualTail (index n))
        (quittingRootOfSimplex
          (quittingSimplexOfRoot (landing.originalRoot (index n))))) atTop
        (nhds (quittingRootSuccessorPayoff reward firstLimit.2
          (quittingRootOfSimplex firstLimit.1))) at h
      simpa only [quittingRootOfSimplex_simplexOfRoot] using h
    apply hsuccessor.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact (landing.predecessorValue_bellman (index n)).symm
  have hsupportSimplex : IsQuittingSimplexRootSupportApproxNash reward
      secondLimit.2 0 secondLimit.1 := by
    apply isQuittingSimplexRootSupportApproxNash_zero_of_tendsto reward
      (fun n ↦ (landing.family.source (index n)).clippedTail
        (landing.family.tolerance (index n)))
      (fun n ↦ quittingSimplexOfRoot
        (landing.family.purifiedRoot (index n)))
      (fun n ↦ landing.family.tolerance (index n))
      secondLimit.2 secondLimit.1 hclipped hpurified htolerance
    intro n
    apply (isQuittingSimplexRootSupportApproxNash_iff reward
      ((landing.family.source (index n)).clippedTail
        (landing.family.tolerance (index n)))
      (landing.family.tolerance (index n))
      (quittingSimplexOfRoot
        (landing.family.purifiedRoot (index n)))).2
    simpa only [QuittingLowSurvivalScaleFamily.purifiedRoot,
      quittingRootOfSimplex_simplexOfRoot] using
      (landing.family.core (index n)).support
  have hcontinueTendsto : Tendsto
      (fun n ↦ quittingStationaryContinueMass
        (landing.family.purifiedRoot (index n))) atTop
      (nhds (quittingStationaryContinueMass
        (quittingRootOfSimplex firstLimit.1))) := by
    have hcontinuous : Continuous (fun root : QuittingRootSimplex ι ↦
        quittingStationaryContinueMass (quittingRootOfSimplex root)) := by
      have h : Continuous (fun root : QuittingRootSimplex ι ↦
          (1 : ℝ) - quittingSimplexAbsorptionMass root) :=
        continuous_const.sub
          (continuous_quittingSimplexAbsorptionMass (ι := ι))
      convert h using 1
      funext root
      rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
      unfold quittingRootAbsorptionMass
      ring
    have h := (hcontinuous.tendsto firstLimit.1).comp
      (hrootEq ▸ hpurified)
    change Tendsto (fun n ↦ quittingStationaryContinueMass
      (quittingRootOfSimplex (quittingSimplexOfRoot
        (landing.family.purifiedRoot (index n))))) atTop
      (nhds (quittingStationaryContinueMass
        (quittingRootOfSimplex firstLimit.1))) at h
    simpa only [quittingRootOfSimplex_simplexOfRoot] using h
  have hcontinue : landing.rho ≤ quittingStationaryContinueMass
      (quittingRootOfSimplex firstLimit.1) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hcontinueTendsto
    apply Filter.Eventually.of_forall
    intro n
    exact (Classical.choose_spec
      (landing.cofinally_landing
        (firstSubsequence (secondSubsequence n)))).2.1
  have hpredecessorMem : quittingRootSuccessorPayoff reward firstLimit.2
      (quittingRootOfSimplex firstLimit.1) ∈
        Set.Icc (fun _ ↦ -quittingRewardBound reward)
          (fun _ ↦ quittingRewardBound reward) := by
    apply isClosed_Icc.mem_of_tendsto hpredecessor
    apply Filter.Eventually.of_forall
    intro n
    constructor
    · intro who
      exact neg_le_of_abs_le (abs_quittingRootSequenceTerminalValue_le reward
        (landing.family.source (index n)).roots who
        ((landing.family.source (index n)).crossingStage - 1)
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward))
    · intro who
      exact le_of_abs_le (abs_quittingRootSequenceTerminalValue_le reward
        (landing.family.source (index n)).roots who
        ((landing.family.source (index n)).crossingStage - 1)
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward))
  refine ⟨{
    index := index
    index_tendsto_atTop := hindex
    landingAt := hlandingAt
    root := firstLimit.1
    actualTail := firstLimit.2
    clippedTail := secondLimit.2
    predecessorValue := quittingRootSuccessorPayoff reward firstLimit.2
      (quittingRootOfSimplex firstLimit.1)
    originalRoot_tendsto := horiginal
    purifiedRoot_tendsto := hrootEq ▸ hpurified
    actualTail_tendsto := hactual
    clippedTail_tendsto := hclipped
    predecessorValue_tendsto := hpredecessor
    clippedTail_eq := hclippedEq
    actualTail_rational := hactualRational
    clippedTail_eq_actual := hclippedEqActual
    predecessorValue_bellman := rfl
    exactSupport := ?_
    continueMass_lower := hcontinue
    actualTail_mem := hfirstLimitMem.2
    predecessorValue_mem := hpredecessorMem }⟩
  rw [← hrootEq]
  exact (isQuittingSimplexRootSupportApproxNash_iff reward
    secondLimit.2 0 secondLimit.1).1 hsupportSimplex

/-- A compact limit of the literal row following a positive-rho landing.
Together with the base limit, this records two consecutive exact
Nash--Bellman edges from actual source data.  It asserts neither root nor
value recurrence. -/
structure QuittingLowSurvivalPositiveRhoConsecutiveLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (base : QuittingLowSurvivalPositiveRhoCompactLimit landing) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  crossingRoot : QuittingRootSimplex ι
  futureTail : Payoff ι
  crossingRoot_tendsto : Tendsto
    (fun n ↦ quittingSimplexOfRoot
      (landing.crossingRoot (base.index (subsequence n))))
    atTop (nhds crossingRoot)
  futureTail_tendsto : Tendsto
    (fun n ↦ landing.futureTail (base.index (subsequence n)))
    atTop (nhds futureTail)
  actualTail_bellman : base.actualTail =
    quittingRootSuccessorPayoff reward futureTail
      (quittingRootOfSimplex crossingRoot)
  exactEndpointNash : IsεQuittingRootEndpointNash reward futureTail 0
    (quittingRootOfSimplex crossingRoot)
  futureTail_mem : futureTail ∈
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)

/-- The base landing row and the retained crossing row form the first exact
source-matched Nash--Bellman edge. -/
theorem QuittingLowSurvivalPositiveRhoConsecutiveLimit.firstEdge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) :
    IsQuittingNashBellmanEdge reward
      (base.predecessorValue, base.root)
      (base.actualTail, limit.crossingRoot) := by
  constructor
  · exact base.predecessorValue_bellman
  · rw [← base.clippedTail_eq_actual]
    exact base.exactEndpointNash

/-- The retained crossing row and its literal future tail form the second
exact source-matched Nash--Bellman edge. -/
theorem QuittingLowSurvivalPositiveRhoConsecutiveLimit.secondEdge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) :
    IsQuittingNashBellmanEdge reward
      (base.actualTail, limit.crossingRoot)
      (limit.futureTail, limit.crossingRoot) :=
  ⟨limit.actualTail_bellman, limit.exactEndpointNash⟩

/-- Every positive-rho source-family limit retains a compact limit of the
next literal row.  This is the strongest unconditional temporal attachment
available from source coherence: two consecutive exact edges, not a
stationary self-loop. -/
theorem exists_quittingLowSurvivalPositiveRhoConsecutiveLimit
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (base : QuittingLowSurvivalPositiveRhoCompactLimit landing) :
    Nonempty (QuittingLowSurvivalPositiveRhoConsecutiveLimit base) := by
  let data : ℕ → QuittingRootSimplex ι × Payoff ι := fun n ↦
    (quittingSimplexOfRoot (landing.crossingRoot (base.index n)),
      landing.futureTail (base.index n))
  have hdata : ∀ n, data n ∈ quittingLowSurvivalRootTailCarrier reward := by
    intro n
    refine ⟨Set.mem_univ _, ?_⟩
    constructor
    · intro who
      exact neg_le_of_abs_le
        (abs_quittingRootSequenceTerminalValue_le reward
          (landing.family.source (base.index n)).roots who
          ((landing.family.source (base.index n)).crossingStage + 1)
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward))
    · intro who
      exact le_of_abs_le
        (abs_quittingRootSequenceTerminalValue_le reward
          (landing.family.source (base.index n)).roots who
          ((landing.family.source (base.index n)).crossingStage + 1)
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward))
  obtain ⟨point, hpoint, subsequence, hsubsequence, hlimit⟩ :=
    (quittingLowSurvivalRootTailCarrier_isCompact reward).tendsto_subseq hdata
  have hroot : Tendsto
      (fun n ↦ quittingSimplexOfRoot
        (landing.crossingRoot (base.index (subsequence n))))
      atTop (nhds point.1) := by
    exact (continuous_fst.tendsto point).comp hlimit
  have hfuture : Tendsto
      (fun n ↦ landing.futureTail (base.index (subsequence n)))
      atTop (nhds point.2) := by
    exact (continuous_snd.tendsto point).comp hlimit
  have hactual : Tendsto
      (fun n ↦ landing.actualTail (base.index (subsequence n)))
      atTop (nhds base.actualTail) :=
    base.actualTail_tendsto.comp hsubsequence.tendsto_atTop
  have hsuccessor : Tendsto (fun n ↦
      quittingRootSuccessorPayoff reward
        (landing.futureTail (base.index (subsequence n)))
        (landing.crossingRoot (base.index (subsequence n))))
      atTop (nhds (quittingRootSuccessorPayoff reward point.2
        (quittingRootOfSimplex point.1))) := by
    have hpair : Tendsto (fun n ↦
        (landing.futureTail (base.index (subsequence n)),
          quittingSimplexOfRoot
            (landing.crossingRoot (base.index (subsequence n)))))
        atTop (nhds (point.2, point.1)) := hfuture.prodMk_nhds hroot
    have h := (continuous_quittingRootSuccessorPayoff_simplex reward).tendsto
      (point.2, point.1) |>.comp hpair
    change Tendsto (fun n ↦ quittingRootSuccessorPayoff reward
      (landing.futureTail (base.index (subsequence n)))
      (quittingRootOfSimplex (quittingSimplexOfRoot
        (landing.crossingRoot (base.index (subsequence n)))))) atTop
      (nhds (quittingRootSuccessorPayoff reward point.2
        (quittingRootOfSimplex point.1))) at h
    simpa only [quittingRootOfSimplex_simplexOfRoot] using h
  have hsuccessorAsActual : Tendsto (fun n ↦
      quittingRootSuccessorPayoff reward
        (landing.futureTail (base.index (subsequence n)))
        (landing.crossingRoot (base.index (subsequence n))))
      atTop (nhds base.actualTail) := by
    apply hactual.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact landing.actualTail_bellman (base.index (subsequence n))
  have hbellman : base.actualTail =
      quittingRootSuccessorPayoff reward point.2
        (quittingRootOfSimplex point.1) :=
    tendsto_nhds_unique hsuccessorAsActual hsuccessor
  have herror : Tendsto
      (fun n ↦ base.crossingError (subsequence n)) atTop (nhds 0) :=
    base.crossingError_tendsto_zero.comp hsubsequence.tendsto_atTop
  have hendpoint : IsεQuittingRootEndpointNash reward point.2 0
      (quittingRootOfSimplex point.1) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward
      (fun n ↦ base.crossingError (subsequence n))
      (fun n ↦ landing.futureTail (base.index (subsequence n)))
      (fun n ↦ quittingSimplexOfRoot
        (landing.crossingRoot (base.index (subsequence n))))
      herror hfuture hroot
    apply Filter.Eventually.of_forall
    intro n
    have hpositive : 0 < landing.crossingSurvival
        (base.index (subsequence n)) :=
      (div_pos (mul_pos landing.family.u_pos landing.rho_pos) (by norm_num)).trans
        (base.landingAt (subsequence n)).2.2.1
    simpa [QuittingLowSurvivalPositiveRhoCompactLimit.crossingError] using
      landing.crossingEndpointNash (base.index (subsequence n)) hpositive
  exact ⟨{
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    crossingRoot := point.1
    futureTail := point.2
    crossingRoot_tendsto := hroot
    futureTail_tendsto := hfuture
    actualTail_bellman := hbellman
    exactEndpointNash := hendpoint
    futureTail_mem := hpoint.2 }⟩

/-- A finite source attachment ending at a literal sure-exit limiting row.
The two preceding edges remain the actual source-matched edges retained by
`QuittingLowSurvivalPositiveRhoConsecutiveLimit`; no stationary recurrence is
asserted. -/
structure QuittingLowSurvivalPositiveRhoSureExitAttachment
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) where
  sureExit : QuittingRootHasSureQuitter
    (quittingRootOfSimplex limit.crossingRoot)

/-- One further compactified row of the literal source sequence.  Its root
is the row immediately after `crossingRoot`, and its tail is that row's
actual source continuation.  Thus `futureTail_bellman` and
`exactEndpointNash` form a third source-matched Nash--Bellman edge. -/
structure QuittingLowSurvivalPositiveRhoNextRowLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  nextRoot : QuittingRootSimplex ι
  nextTail : Payoff ι
  nextRoot_tendsto : Tendsto
    (fun n ↦
      let sourceIndex := base.index (limit.subsequence (subsequence n))
      quittingSimplexOfRoot
        ((landing.family.source sourceIndex).roots
          ((landing.family.source sourceIndex).crossingStage + 1)))
    atTop (nhds nextRoot)
  nextTail_tendsto : Tendsto
    (fun n ↦
      let sourceIndex := base.index (limit.subsequence (subsequence n))
      quittingRootSequenceTailVector reward
        (landing.family.source sourceIndex).roots
        ((landing.family.source sourceIndex).crossingStage + 2))
    atTop (nhds nextTail)
  futureTail_bellman : limit.futureTail =
    quittingRootSuccessorPayoff reward nextTail
      (quittingRootOfSimplex nextRoot)
  exactEndpointNash : IsεQuittingRootEndpointNash reward nextTail 0
    (quittingRootOfSimplex nextRoot)
  nextTail_mem : nextTail ∈
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)

/-- The newly retained row supplies the third exact source-matched edge.
The simplex coordinate attached to the final payoff is irrelevant to this
edge and is reused only to keep the standard point type. -/
theorem QuittingLowSurvivalPositiveRhoNextRowLimit.thirdEdge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    {limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base}
    (next : QuittingLowSurvivalPositiveRhoNextRowLimit limit) :
    IsQuittingNashBellmanEdge reward
      (limit.futureTail, next.nextRoot) (next.nextTail, next.nextRoot) :=
  ⟨next.futureTail_bellman, next.exactEndpointNash⟩

/-- **One-row source extension.**  The limiting crossing row either has zero
Continue mass, hence is a literal sure-exit attachment, or its positive
Continue mass keeps the following source row uniformly reached.  In the
second case compactness retains that next row and its actual continuation,
and vanishing conditional Nash error gives one further exact edge.

No recurrence of roots or values is assumed in either branch. -/
theorem sureExitAttachment_or_exists_nextRowLimit
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) :
    Nonempty (QuittingLowSurvivalPositiveRhoSureExitAttachment limit) ∨
      Nonempty (QuittingLowSurvivalPositiveRhoNextRowLimit limit) := by
  let live := quittingStationaryContinueMass
    (quittingRootOfSimplex limit.crossingRoot)
  by_cases hlive : live = 0
  · exact Or.inl ⟨{
      sureExit := quittingRootHasSureQuitter_of_stationaryContinueMass_eq_zero
        (quittingRootOfSimplex limit.crossingRoot) hlive }⟩
  · right
    have hlivePos : 0 < live := lt_of_le_of_ne
      (quittingStationaryContinueMass_nonneg _) (Ne.symm hlive)
    have hliveTendsto : Tendsto (fun n ↦
        quittingStationaryContinueMass
          (landing.crossingRoot
            (base.index (limit.subsequence n))))
        atTop (nhds live) := by
      simpa only [Function.comp_def,
        quittingRootOfSimplex_simplexOfRoot] using
        (continuous_quittingStationaryContinueMass_simplex.tendsto
          limit.crossingRoot).comp limit.crossingRoot_tendsto
    have hliveEventually : ∀ᶠ n in atTop, live / 2 <
        quittingStationaryContinueMass
          (landing.crossingRoot
            (base.index (limit.subsequence n))) :=
      hliveTendsto.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨burnIn, hburnIn⟩ := Filter.eventually_atTop.1 hliveEventually
    let selected : ℕ → ℕ := fun n ↦ burnIn + n
    have hselected : StrictMono selected := by
      intro first second hlt
      dsimp only [selected]
      omega
    let sourceIndex : ℕ → ℕ := fun n ↦
      base.index (limit.subsequence (selected n))
    let nextRootAt : ℕ → QuittingRootSimplex ι := fun n ↦
      quittingSimplexOfRoot
        ((landing.family.source (sourceIndex n)).roots
          ((landing.family.source (sourceIndex n)).crossingStage + 1))
    let nextTailAt : ℕ → Payoff ι := fun n ↦
      quittingRootSequenceTailVector reward
        (landing.family.source (sourceIndex n)).roots
        ((landing.family.source (sourceIndex n)).crossingStage + 2)
    let data : ℕ → QuittingRootSimplex ι × Payoff ι := fun n ↦
      (nextRootAt n, nextTailAt n)
    have hdata : ∀ n, data n ∈ quittingLowSurvivalRootTailCarrier reward := by
      intro n
      refine ⟨Set.mem_univ _, ?_⟩
      constructor
      · intro who
        exact neg_le_of_abs_le
          (abs_quittingRootSequenceTerminalValue_le reward
            (landing.family.source (sourceIndex n)).roots who
            ((landing.family.source (sourceIndex n)).crossingStage + 2)
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward))
      · intro who
        exact le_of_abs_le
          (abs_quittingRootSequenceTerminalValue_le reward
            (landing.family.source (sourceIndex n)).roots who
            ((landing.family.source (sourceIndex n)).crossingStage + 2)
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward))
    obtain ⟨point, hpoint, subsequence, hsubsequence, hlimit⟩ :=
      (quittingLowSurvivalRootTailCarrier_isCompact reward).tendsto_subseq hdata
    have hroot : Tendsto (fun n ↦ nextRootAt (subsequence n))
        atTop (nhds point.1) := by
      simpa only [data, Function.comp_def, Prod.fst] using
        (continuous_fst.tendsto point).comp hlimit
    have htail : Tendsto (fun n ↦ nextTailAt (subsequence n))
        atTop (nhds point.2) := by
      simpa only [data, Function.comp_def, Prod.snd] using
        (continuous_snd.tendsto point).comp hlimit
    have hfuture : Tendsto (fun n ↦
        landing.futureTail (sourceIndex (subsequence n)))
        atTop (nhds limit.futureTail) := by
      exact limit.futureTail_tendsto.comp
        ((hselected.comp hsubsequence).tendsto_atTop)
    have hsuccessor : Tendsto (fun n ↦
        quittingRootSuccessorPayoff reward
          (nextTailAt (subsequence n))
          (quittingRootOfSimplex (nextRootAt (subsequence n))))
        atTop (nhds (quittingRootSuccessorPayoff reward point.2
          (quittingRootOfSimplex point.1))) := by
      have hpair : Tendsto (fun n ↦
          (nextTailAt (subsequence n), nextRootAt (subsequence n)))
          atTop (nhds (point.2, point.1)) := htail.prodMk_nhds hroot
      simpa only [Function.comp_def] using
        (continuous_quittingRootSuccessorPayoff_simplex reward).tendsto
          (point.2, point.1) |>.comp hpair
    have hsuccessorAsFuture : Tendsto (fun n ↦
        quittingRootSuccessorPayoff reward
          (nextTailAt (subsequence n))
          (quittingRootOfSimplex (nextRootAt (subsequence n))))
        atTop (nhds limit.futureTail) := by
      apply hfuture.congr'
      apply Filter.Eventually.of_forall
      intro n
      let source := landing.family.source (sourceIndex (subsequence n))
      have hbellman : quittingRootSequenceTailVector reward source.roots
          (source.crossingStage + 1) =
          quittingRootSuccessorPayoff reward
            (quittingRootSequenceTailVector reward source.roots
              (source.crossingStage + 2))
            (source.roots (source.crossingStage + 1)) := by
        funext who
        simpa only [quittingRootSequenceTailVector, Nat.add_assoc,
          Nat.reduceAdd] using
          quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
            reward source.roots who (source.crossingStage + 1)
      simpa [nextRootAt, nextTailAt, source, sourceIndex,
        QuittingLowSurvivalPositiveRhoLandingFamily.futureTail] using hbellman
    have hbellman : limit.futureTail =
        quittingRootSuccessorPayoff reward point.2
          (quittingRootOfSimplex point.1) :=
      tendsto_nhds_unique hsuccessorAsFuture hsuccessor
    let reachFloor :=
      (u * landing.rho / 2) * (live / 2)
    have hreachFloorPos : 0 < reachFloor := by
      dsimp only [reachFloor]
      exact mul_pos
        (div_pos (mul_pos landing.family.u_pos landing.rho_pos) (by norm_num))
        (div_pos hlivePos (by norm_num))
    have hreach : ∀ n, reachFloor <
        quittingJointSurvivalWeight
          (landing.family.source (sourceIndex n)).roots 0
          ((landing.family.source (sourceIndex n)).crossingStage + 1) := by
      intro n
      let source := landing.family.source (sourceIndex n)
      have hcrossing : u * landing.rho / 2 <
          landing.crossingSurvival (sourceIndex n) :=
        (base.landingAt (limit.subsequence (selected n))).2.2.1
      have hcontinue : live / 2 <
          quittingStationaryContinueMass
            (landing.crossingRoot (sourceIndex n)) := by
        exact hburnIn (selected n) (by simp [selected])
      have hrec := quittingJointSurvivalWeight_succ source.roots 0
        source.crossingStage
      change reachFloor < quittingJointSurvivalWeight source.roots 0
        (source.crossingStage + 1)
      rw [hrec]
      have hcontinue' : live / 2 ≤
          quittingStationaryContinueMass
            (source.roots source.crossingStage) := by
        simpa [source, sourceIndex,
          QuittingLowSurvivalPositiveRhoLandingFamily.crossingRoot] using
            hcontinue.le
      have hcrossing' : u * landing.rho / 2 <
          quittingJointSurvivalWeight source.roots 0
            source.crossingStage := by
        simpa [source, sourceIndex,
          QuittingLowSurvivalPositiveRhoLandingFamily.crossingSurvival] using
            hcrossing
      have hfirstProduct :
          (u * landing.rho / 2) * (live / 2) <
            quittingJointSurvivalWeight source.roots 0
              source.crossingStage * (live / 2) :=
        mul_lt_mul_of_pos_right hcrossing'
          (div_pos hlivePos (by norm_num))
      have hsecondProduct :
          quittingJointSurvivalWeight source.roots 0
                source.crossingStage * (live / 2) ≤
            quittingJointSurvivalWeight source.roots 0
                source.crossingStage *
              quittingStationaryContinueMass
                (source.roots source.crossingStage) :=
        mul_le_mul_of_nonneg_left hcontinue'
          (quittingJointSurvivalWeight_nonneg source.roots 0
            source.crossingStage)
      simpa only [zero_add] using hfirstProduct.trans_le hsecondProduct
    let error : ℕ → ℝ := fun n ↦
      landing.family.accuracy (sourceIndex (subsequence n)) /
        quittingJointSurvivalWeight
          (landing.family.source (sourceIndex (subsequence n))).roots 0
          ((landing.family.source (sourceIndex (subsequence n))).crossingStage + 1)
    have herror : Tendsto error atTop (nhds 0) := by
      have haccuracy : Tendsto (fun n ↦
          landing.family.accuracy (sourceIndex (subsequence n)))
          atTop (nhds 0) := by
        exact landing.family.accuracy_tendsto_zero.comp
          (base.index_tendsto_atTop.comp
            (limit.subsequence_strictMono.comp
              (hselected.comp hsubsequence)).tendsto_atTop)
      have hupper : Tendsto (fun n ↦
          landing.family.accuracy (sourceIndex (subsequence n)) /
            reachFloor) atTop (nhds 0) := by
        simpa only [zero_div] using haccuracy.div_const reachFloor
      apply squeeze_zero' (g := fun n ↦
        landing.family.accuracy (sourceIndex (subsequence n)) / reachFloor)
      · apply Filter.Eventually.of_forall
        intro n
        exact div_nonneg
          (landing.family.accuracy_pos (sourceIndex (subsequence n))).le
          (hreachFloorPos.trans
            (hreach (subsequence n))).le
      · apply Filter.Eventually.of_forall
        intro n
        exact div_le_div_of_nonneg_left
          (landing.family.accuracy_pos (sourceIndex (subsequence n))).le
          hreachFloorPos (hreach (subsequence n)).le
      · exact hupper
    have hendpoint : IsεQuittingRootEndpointNash reward point.2 0
        (quittingRootOfSimplex point.1) := by
      apply isεQuittingRootEndpointNash_of_tendsto reward error
        (fun n ↦ nextTailAt (subsequence n))
        (fun n ↦ nextRootAt (subsequence n))
        herror htail hroot
      apply Filter.Eventually.of_forall
      intro n
      let source := landing.family.source (sourceIndex (subsequence n))
      have hpositive : 0 < quittingJointSurvivalWeight source.roots 0
          (source.crossingStage + 1) :=
        hreachFloorPos.trans (hreach (subsequence n))
      simpa [error, nextRootAt, nextTailAt, source, sourceIndex] using
        isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
          reward source.roots source.sourceNash
          (source.crossingStage + 1) hpositive
    exact ⟨{
      subsequence := selected ∘ subsequence
      subsequence_strictMono := hselected.comp hsubsequence
      nextRoot := point.1
      nextTail := point.2
      nextRoot_tendsto := by
        simpa [nextRootAt, sourceIndex, Function.comp_def] using hroot
      nextTail_tendsto := by
        simpa [nextTailAt, sourceIndex, Function.comp_def] using htail
      futureTail_bellman := hbellman
      exactEndpointNash := hendpoint
      nextTail_mem := hpoint.2 }⟩

/-- A uniformly reached limiting row of the literal source sequence.  The
offset is measured from the first crossing row.  Both endpoint values and
the root come from one nested source subsequence, so `exactEdge` is a genuine
one-row temporal edge rather than a stationary recurrence assertion. -/
structure QuittingLowSurvivalPositiveRhoReachedRowLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (base : QuittingLowSurvivalPositiveRhoCompactLimit landing) where
  offset : ℕ
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  currentValue : Payoff ι
  root : QuittingRootSimplex ι
  nextValue : Payoff ι
  currentValue_tendsto : Tendsto
    (fun n ↦
      let sourceIndex := base.index (subsequence n)
      quittingRootSequenceTailVector reward
        (landing.family.source sourceIndex).roots
        ((landing.family.source sourceIndex).crossingStage + offset))
    atTop (nhds currentValue)
  root_tendsto : Tendsto
    (fun n ↦
      let sourceIndex := base.index (subsequence n)
      quittingSimplexOfRoot
        ((landing.family.source sourceIndex).roots
          ((landing.family.source sourceIndex).crossingStage + offset)))
    atTop (nhds root)
  nextValue_tendsto : Tendsto
    (fun n ↦
      let sourceIndex := base.index (subsequence n)
      quittingRootSequenceTailVector reward
        (landing.family.source sourceIndex).roots
        ((landing.family.source sourceIndex).crossingStage + offset + 1))
    atTop (nhds nextValue)
  reachFloor : ℝ
  reachFloor_pos : 0 < reachFloor
  reached : ∀ n, reachFloor < quittingJointSurvivalWeight
    (landing.family.source (base.index (subsequence n))).roots 0
    ((landing.family.source (base.index (subsequence n))).crossingStage + offset)
  exactEdge : IsQuittingNashBellmanEdge reward
    (currentValue, root) (nextValue, root)
  currentValue_mem : currentValue ∈
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)
  nextValue_mem : nextValue ∈
    Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)

/-- The first retained crossing row is a uniformly reached row in the
iterable source-limit interface. -/
def QuittingLowSurvivalPositiveRhoConsecutiveLimit.reachedRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) :
    QuittingLowSurvivalPositiveRhoReachedRowLimit base where
  offset := 0
  subsequence := limit.subsequence
  subsequence_strictMono := limit.subsequence_strictMono
  currentValue := base.actualTail
  root := limit.crossingRoot
  nextValue := limit.futureTail
  currentValue_tendsto := by
    simpa [QuittingLowSurvivalPositiveRhoLandingFamily.actualTail,
      Function.comp_def] using
      base.actualTail_tendsto.comp limit.subsequence_strictMono.tendsto_atTop
  root_tendsto := by
    simpa [QuittingLowSurvivalPositiveRhoLandingFamily.crossingRoot] using
      limit.crossingRoot_tendsto
  nextValue_tendsto := by
    simpa [QuittingLowSurvivalPositiveRhoLandingFamily.futureTail] using
      limit.futureTail_tendsto
  reachFloor := u * landing.rho / 2
  reachFloor_pos :=
    div_pos (mul_pos landing.family.u_pos landing.rho_pos) (by norm_num)
  reached := by
    intro n
    simpa [QuittingLowSurvivalPositiveRhoLandingFamily.crossingSurvival] using
      (base.landingAt (limit.subsequence n)).2.2.1
  exactEdge := limit.secondEdge
  currentValue_mem := base.actualTail_mem
  nextValue_mem := limit.futureTail_mem

/-- One reached row is a literal source successor of another when it is one
offset later and is obtained by a further cofinal subsequence. -/
def QuittingLowSurvivalPositiveRhoReachedRowLimit.IsSuccessor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (first second : QuittingLowSurvivalPositiveRhoReachedRowLimit base) : Prop :=
  second.offset = first.offset + 1 ∧
    second.currentValue = first.nextValue ∧
    ∃ refinement : ℕ → ℕ, StrictMono refinement ∧
      second.subsequence = first.subsequence ∘ refinement

/-- A sure-exit endpoint reached after finitely many literal source
extensions. -/
structure QuittingLowSurvivalPositiveRhoFiniteSureExitAttachment
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (seed : QuittingLowSurvivalPositiveRhoReachedRowLimit base) where
  terminal : QuittingLowSurvivalPositiveRhoReachedRowLimit base
  reachable : Relation.ReflTransGen
    QuittingLowSurvivalPositiveRhoReachedRowLimit.IsSuccessor seed terminal
  sureExit : QuittingRootHasSureQuitter
    (quittingRootOfSimplex terminal.root)

/-- An infinite sequence of exact one-row edges obtained from successively
nested subsequences of the same literal sources.  This is an exact temporal
spine; it does not assert recurrence or identify it with one executable
infinite profile. -/
structure QuittingLowSurvivalPositiveRhoInfiniteExactSpine
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (seed : QuittingLowSurvivalPositiveRhoReachedRowLimit base) where
  row : ℕ → QuittingLowSurvivalPositiveRhoReachedRowLimit base
  initial : row 0 = seed
  successor : ∀ n,
    QuittingLowSurvivalPositiveRhoReachedRowLimit.IsSuccessor
      (row n) (row (n + 1))

/-- Consecutive rows of an infinite exact spine compose into a standard
Nash--Bellman edge with the next row's actual root. -/
theorem QuittingLowSurvivalPositiveRhoInfiniteExactSpine.edge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    {seed : QuittingLowSurvivalPositiveRhoReachedRowLimit base}
    (spine : QuittingLowSurvivalPositiveRhoInfiniteExactSpine seed)
    (n : ℕ) :
    IsQuittingNashBellmanEdge reward
      ((spine.row n).currentValue, (spine.row n).root)
      ((spine.row (n + 1)).currentValue, (spine.row (n + 1)).root) := by
  have hvalue := (spine.successor n).2.1
  simpa [IsQuittingNashBellmanEdge, hvalue] using
    (spine.row n).exactEdge

/-- **Iterable one-row extension.**  A uniformly reached limiting source row
either has zero Continue mass and hence a sure quitter, or a nested cofinal
subsequence retains the next literal row with positive reach and an exact
Nash--Bellman edge. -/
theorem QuittingLowSurvivalPositiveRhoReachedRowLimit.sureExit_or_exists_successor
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (row : QuittingLowSurvivalPositiveRhoReachedRowLimit base) :
    QuittingRootHasSureQuitter (quittingRootOfSimplex row.root) ∨
      ∃ next : QuittingLowSurvivalPositiveRhoReachedRowLimit base,
        row.IsSuccessor next := by
  let live := quittingStationaryContinueMass
    (quittingRootOfSimplex row.root)
  by_cases hlive : live = 0
  · exact Or.inl
      (quittingRootHasSureQuitter_of_stationaryContinueMass_eq_zero
        (quittingRootOfSimplex row.root) hlive)
  · right
    have hlivePos : 0 < live := lt_of_le_of_ne
      (quittingStationaryContinueMass_nonneg _) (Ne.symm hlive)
    have hliveTendsto : Tendsto (fun n ↦
        let sourceIndex := base.index (row.subsequence n)
        quittingStationaryContinueMass
          ((landing.family.source sourceIndex).roots
            ((landing.family.source sourceIndex).crossingStage + row.offset)))
        atTop (nhds live) := by
      simpa only [Function.comp_def,
        quittingRootOfSimplex_simplexOfRoot] using
        (continuous_quittingStationaryContinueMass_simplex.tendsto row.root).comp
          row.root_tendsto
    have hliveEventually : ∀ᶠ n in atTop, live / 2 <
        let sourceIndex := base.index (row.subsequence n)
        quittingStationaryContinueMass
          ((landing.family.source sourceIndex).roots
            ((landing.family.source sourceIndex).crossingStage + row.offset)) :=
      hliveTendsto.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨burnIn, hburnIn⟩ := Filter.eventually_atTop.1 hliveEventually
    let selected : ℕ → ℕ := fun n ↦ burnIn + n
    have hselected : StrictMono selected := by
      intro first second hlt
      dsimp only [selected]
      omega
    let sourceIndex : ℕ → ℕ := fun n ↦
      base.index (row.subsequence (selected n))
    let nextRootAt : ℕ → QuittingRootSimplex ι := fun n ↦
      quittingSimplexOfRoot
        ((landing.family.source (sourceIndex n)).roots
          ((landing.family.source (sourceIndex n)).crossingStage +
            row.offset + 1))
    let nextTailAt : ℕ → Payoff ι := fun n ↦
      quittingRootSequenceTailVector reward
        (landing.family.source (sourceIndex n)).roots
        ((landing.family.source (sourceIndex n)).crossingStage +
          row.offset + 2)
    let data : ℕ → QuittingRootSimplex ι × Payoff ι := fun n ↦
      (nextRootAt n, nextTailAt n)
    have hdata : ∀ n, data n ∈
        quittingLowSurvivalRootTailCarrier reward := by
      intro n
      refine ⟨Set.mem_univ _, ?_⟩
      constructor
      · intro who
        exact neg_le_of_abs_le
          (abs_quittingRootSequenceTerminalValue_le reward
            (landing.family.source (sourceIndex n)).roots who
            ((landing.family.source (sourceIndex n)).crossingStage +
              row.offset + 2)
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward))
      · intro who
        exact le_of_abs_le
          (abs_quittingRootSequenceTerminalValue_le reward
            (landing.family.source (sourceIndex n)).roots who
            ((landing.family.source (sourceIndex n)).crossingStage +
              row.offset + 2)
            (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward))
    obtain ⟨point, hpoint, subsequence, hsubsequence, hlimit⟩ :=
      (quittingLowSurvivalRootTailCarrier_isCompact reward).tendsto_subseq hdata
    have hroot : Tendsto (fun n ↦ nextRootAt (subsequence n))
        atTop (nhds point.1) := by
      simpa only [data, Function.comp_def, Prod.fst] using
        (continuous_fst.tendsto point).comp hlimit
    have htail : Tendsto (fun n ↦ nextTailAt (subsequence n))
        atTop (nhds point.2) := by
      simpa only [data, Function.comp_def, Prod.snd] using
        (continuous_snd.tendsto point).comp hlimit
    have hcurrent : Tendsto (fun n ↦
        quittingRootSequenceTailVector reward
          (landing.family.source (sourceIndex (subsequence n))).roots
          ((landing.family.source (sourceIndex (subsequence n))).crossingStage +
            row.offset + 1)) atTop (nhds row.nextValue) := by
      simpa [sourceIndex, Function.comp_def, Nat.add_assoc] using
        row.nextValue_tendsto.comp
          ((hselected.comp hsubsequence).tendsto_atTop)
    have hsuccessor : Tendsto (fun n ↦
        quittingRootSuccessorPayoff reward
          (nextTailAt (subsequence n))
          (quittingRootOfSimplex (nextRootAt (subsequence n))))
        atTop (nhds (quittingRootSuccessorPayoff reward point.2
          (quittingRootOfSimplex point.1))) := by
      have hpair : Tendsto (fun n ↦
          (nextTailAt (subsequence n), nextRootAt (subsequence n)))
          atTop (nhds (point.2, point.1)) := htail.prodMk_nhds hroot
      simpa only [Function.comp_def] using
        (continuous_quittingRootSuccessorPayoff_simplex reward).tendsto
          (point.2, point.1) |>.comp hpair
    have hsuccessorAsCurrent : Tendsto (fun n ↦
        quittingRootSuccessorPayoff reward
          (nextTailAt (subsequence n))
          (quittingRootOfSimplex (nextRootAt (subsequence n))))
        atTop (nhds row.nextValue) := by
      apply hcurrent.congr'
      apply Filter.Eventually.of_forall
      intro n
      let source := landing.family.source (sourceIndex (subsequence n))
      have hbellman : quittingRootSequenceTailVector reward source.roots
          (source.crossingStage + row.offset + 1) =
          quittingRootSuccessorPayoff reward
            (quittingRootSequenceTailVector reward source.roots
              (source.crossingStage + row.offset + 2))
            (source.roots (source.crossingStage + row.offset + 1)) := by
        funext who
        simpa only [quittingRootSequenceTailVector, Nat.add_assoc,
          Nat.reduceAdd] using
          quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
            reward source.roots who (source.crossingStage + row.offset + 1)
      simpa [nextRootAt, nextTailAt, source] using hbellman
    have hbellman : row.nextValue =
        quittingRootSuccessorPayoff reward point.2
          (quittingRootOfSimplex point.1) :=
      tendsto_nhds_unique hsuccessorAsCurrent hsuccessor
    let reachFloor := row.reachFloor * (live / 2)
    have hreachFloorPos : 0 < reachFloor := by
      dsimp only [reachFloor]
      exact mul_pos row.reachFloor_pos (div_pos hlivePos (by norm_num))
    have hreach : ∀ n, reachFloor <
        quittingJointSurvivalWeight
          (landing.family.source (sourceIndex n)).roots 0
          ((landing.family.source (sourceIndex n)).crossingStage +
            row.offset + 1) := by
      intro n
      let source := landing.family.source (sourceIndex n)
      have hcurrentReach : row.reachFloor <
          quittingJointSurvivalWeight source.roots 0
            (source.crossingStage + row.offset) := by
        simpa [source, sourceIndex] using row.reached (selected n)
      have hcontinue : live / 2 <
          quittingStationaryContinueMass
            (source.roots (source.crossingStage + row.offset)) := by
        simpa [source, sourceIndex] using
          hburnIn (selected n) (by simp [selected])
      have hrec := quittingJointSurvivalWeight_succ source.roots 0
        (source.crossingStage + row.offset)
      change reachFloor < quittingJointSurvivalWeight source.roots 0
        (source.crossingStage + row.offset + 1)
      rw [hrec]
      have hfirstProduct : row.reachFloor * (live / 2) <
          quittingJointSurvivalWeight source.roots 0
              (source.crossingStage + row.offset) * (live / 2) :=
        mul_lt_mul_of_pos_right hcurrentReach
          (div_pos hlivePos (by norm_num))
      have hsecondProduct :
          quittingJointSurvivalWeight source.roots 0
                (source.crossingStage + row.offset) * (live / 2) ≤
            quittingJointSurvivalWeight source.roots 0
                (source.crossingStage + row.offset) *
              quittingStationaryContinueMass
                (source.roots (source.crossingStage + row.offset)) :=
        mul_le_mul_of_nonneg_left hcontinue.le
          (quittingJointSurvivalWeight_nonneg source.roots 0
            (source.crossingStage + row.offset))
      simpa only [zero_add] using hfirstProduct.trans_le hsecondProduct
    let error : ℕ → ℝ := fun n ↦
      landing.family.accuracy (sourceIndex (subsequence n)) /
        quittingJointSurvivalWeight
          (landing.family.source (sourceIndex (subsequence n))).roots 0
          ((landing.family.source (sourceIndex (subsequence n))).crossingStage +
            row.offset + 1)
    have herror : Tendsto error atTop (nhds 0) := by
      have haccuracy : Tendsto (fun n ↦
          landing.family.accuracy (sourceIndex (subsequence n)))
          atTop (nhds 0) := by
        exact landing.family.accuracy_tendsto_zero.comp
          (base.index_tendsto_atTop.comp
            (row.subsequence_strictMono.comp
              (hselected.comp hsubsequence)).tendsto_atTop)
      have hupper : Tendsto (fun n ↦
          landing.family.accuracy (sourceIndex (subsequence n)) /
            reachFloor) atTop (nhds 0) := by
        simpa only [zero_div] using haccuracy.div_const reachFloor
      apply squeeze_zero' (g := fun n ↦
        landing.family.accuracy (sourceIndex (subsequence n)) / reachFloor)
      · apply Filter.Eventually.of_forall
        intro n
        exact div_nonneg
          (landing.family.accuracy_pos (sourceIndex (subsequence n))).le
          (hreachFloorPos.trans (hreach (subsequence n))).le
      · apply Filter.Eventually.of_forall
        intro n
        exact div_le_div_of_nonneg_left
          (landing.family.accuracy_pos (sourceIndex (subsequence n))).le
          hreachFloorPos (hreach (subsequence n)).le
      · exact hupper
    have hendpoint : IsεQuittingRootEndpointNash reward point.2 0
        (quittingRootOfSimplex point.1) := by
      apply isεQuittingRootEndpointNash_of_tendsto reward error
        (fun n ↦ nextTailAt (subsequence n))
        (fun n ↦ nextRootAt (subsequence n))
        herror htail hroot
      apply Filter.Eventually.of_forall
      intro n
      let source := landing.family.source (sourceIndex (subsequence n))
      have hpositive : 0 < quittingJointSurvivalWeight source.roots 0
          (source.crossingStage + row.offset + 1) :=
        hreachFloorPos.trans (hreach (subsequence n))
      simpa [error, nextRootAt, nextTailAt, source, sourceIndex] using
        isεQuittingRootEndpointNash_tailVector_of_isεQuittingRootSequenceNash
          reward source.roots source.sourceNash
          (source.crossingStage + row.offset + 1) hpositive
    let refinement : ℕ → ℕ := selected ∘ subsequence
    let next : QuittingLowSurvivalPositiveRhoReachedRowLimit base := {
      offset := row.offset + 1
      subsequence := row.subsequence ∘ refinement
      subsequence_strictMono := row.subsequence_strictMono.comp
        (hselected.comp hsubsequence)
      currentValue := row.nextValue
      root := point.1
      nextValue := point.2
      currentValue_tendsto := by
        simpa [refinement, sourceIndex, Function.comp_def, Nat.add_assoc] using
          hcurrent
      root_tendsto := by
        simpa [refinement, sourceIndex, nextRootAt, Function.comp_def,
          Nat.add_assoc] using hroot
      nextValue_tendsto := by
        simpa [refinement, sourceIndex, nextTailAt, Function.comp_def,
          Nat.add_assoc] using htail
      reachFloor := reachFloor
      reachFloor_pos := hreachFloorPos
      reached := by
        intro n
        simpa [refinement, sourceIndex, Function.comp_def, Nat.add_assoc] using
          hreach (subsequence n)
      exactEdge := ⟨hbellman, hendpoint⟩
      currentValue_mem := row.nextValue_mem
      nextValue_mem := hpoint.2 }
    exact ⟨next, rfl, rfl, refinement,
      hselected.comp hsubsequence, rfl⟩

/-- **Finite attachment or infinite exact source spine.**  Iterating the
one-row extension produces either a reachable sure-exit limiting row after
finitely many extensions, or an infinite sequence of exact source-matched
Nash--Bellman edges.  The latter is a projective sequence of nested
subsequential limits, not an executable chronology or a recurrence theorem. -/
theorem
    QuittingLowSurvivalPositiveRhoReachedRowLimit.finiteSureExit_or_infiniteSpine
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (seed : QuittingLowSurvivalPositiveRhoReachedRowLimit base) :
    Nonempty (QuittingLowSurvivalPositiveRhoFiniteSureExitAttachment seed) ∨
      Nonempty (QuittingLowSurvivalPositiveRhoInfiniteExactSpine seed) := by
  let Step :=
    QuittingLowSurvivalPositiveRhoReachedRowLimit.IsSuccessor
      (base := base)
  by_cases hterminal : ∃ terminal,
      Relation.ReflTransGen Step seed terminal ∧
        QuittingRootHasSureQuitter
          (quittingRootOfSimplex terminal.root)
  · obtain ⟨terminal, hreach, hsure⟩ := hterminal
    exact Or.inl ⟨{
      terminal := terminal
      reachable := hreach
      sureExit := hsure }⟩
  · right
    let Reachable := {row : QuittingLowSurvivalPositiveRhoReachedRowLimit base //
      Relation.ReflTransGen Step seed row}
    have hstep : ∀ current : Reachable,
        ∃ next : QuittingLowSurvivalPositiveRhoReachedRowLimit base,
          Step current.1 next := by
      intro current
      rcases current.1.sureExit_or_exists_successor with hsure | hnext
      · exact False.elim (hterminal ⟨current.1, current.2, hsure⟩)
      · exact hnext
    let advance : Reachable → Reachable := fun current ↦
      ⟨Classical.choose (hstep current),
        Relation.ReflTransGen.tail current.2
          (Classical.choose_spec (hstep current))⟩
    have hadvance : ∀ current : Reachable,
        Step current.1 (advance current).1 := by
      intro current
      exact Classical.choose_spec (hstep current)
    let start : Reachable := ⟨seed, Relation.ReflTransGen.refl⟩
    let orbit : ℕ → Reachable := fun n ↦ advance^[n] start
    exact ⟨{
      row := fun n ↦ (orbit n).1
      initial := by simp [orbit, start]
      successor := by
        intro n
        change Step (orbit n).1 (orbit (n + 1)).1
        rw [show n + 1 = n.succ by omega]
        rw [show orbit n.succ = advance (orbit n) by
          exact Function.iterate_succ_apply' advance n start]
        exact hadvance (orbit n) }⟩

/-- The original positive-rho consecutive limit therefore has the exact
finite-attachment-or-infinite-spine alternative without any recurrence
hypothesis. -/
theorem finiteSureExitAttachment_or_exists_infiniteExactSpine
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    {base : QuittingLowSurvivalPositiveRhoCompactLimit landing}
    (limit : QuittingLowSurvivalPositiveRhoConsecutiveLimit base) :
    Nonempty (QuittingLowSurvivalPositiveRhoFiniteSureExitAttachment
      limit.reachedRow) ∨
      Nonempty (QuittingLowSurvivalPositiveRhoInfiniteExactSpine
        limit.reachedRow) :=
  limit.reachedRow.finiteSureExit_or_infiniteSpine

/-- If the temporal value recurs on the positive-absorption side and the
remaining saturated-opponent boundary inequalities hold, the actual compact
datum is a semantic stationary equilibrium and yields its named uniform
payoff. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.uniformPayoff_of_recurrence_boundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (base : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex base.root))
    (hrecurrence : base.predecessorValue = base.actualTail)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward
      (quittingRootOfSimplex base.root) base.actualTail) :
    (quittingGame reward).IsUniformEquilibriumPayoff none base.actualTail := by
  have hcontinue : quittingStationaryContinueMass
      (quittingRootOfSimplex base.root) < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hfixed : base.actualTail = quittingRootSuccessorPayoff reward
      base.actualTail (quittingRootOfSimplex base.root) := by
    rw [← base.predecessorValue_bellman]
    exact hrecurrence.symm
  have hendpoint : IsεQuittingRootEndpointNash reward base.actualTail 0
      (quittingRootOfSimplex base.root) := by
    rw [← base.clippedTail_eq_actual]
    exact base.exactEndpointNash
  exact isUniformEquilibriumPayoff_of_stationaryEndpointCertificate
    reward (quittingRootOfSimplex base.root) base.actualTail hcontinue
      hfixed hendpoint hboundary

/-- The exact unresolved positive-absorption output.  It retains two
consecutive source-matched Nash--Bellman edges.  The obstruction is either
failure of temporal value recurrence at the first edge or failure of the
finite saturated-opponent boundary packet after recurrence. -/
structure QuittingLowSurvivalPositiveAbsorptionAttachmentResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (u : ℝ) where
  landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u
  base : QuittingLowSurvivalPositiveRhoCompactLimit landing
  consecutive : QuittingLowSurvivalPositiveRhoConsecutiveLimit base
  absorption_pos : 0 < quittingRootAbsorptionMass
    (quittingRootOfSimplex base.root)
  obstruction : base.predecessorValue ≠ base.actualTail ∨
    ¬IsQuittingStationaryBoundaryAdmissible reward
      (quittingRootOfSimplex base.root) base.actualTail

/-- A literal positive-rho landing family either already supplies a uniform
payoff, leaves the exact all-Continue phantom, or supplies the concrete
positive-absorption two-edge attachment residual. -/
theorem uniformPayoff_or_phantom_or_positiveAbsorptionAttachmentResidual
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom reward) ∨
      Nonempty
        (QuittingLowSurvivalPositiveAbsorptionAttachmentResidual reward u) := by
  obtain ⟨base⟩ := exists_quittingLowSurvivalPositiveRhoCompactLimit landing
  obtain ⟨consecutive⟩ :=
    exists_quittingLowSurvivalPositiveRhoConsecutiveLimit base
  by_cases habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex base.root) = 0
  · rcases base.zeroPayoff_or_phantom_of_zeroAbsorption
        habsorption with hzero | hphantom
    · exact Or.inl ⟨0, hzero⟩
    · exact Or.inr (Or.inl hphantom)
  · have habsorptionPos : 0 < quittingRootAbsorptionMass
        (quittingRootOfSimplex base.root) :=
      lt_of_le_of_ne
        (quittingRootAbsorptionMass_nonneg
          (quittingRootOfSimplex base.root)) (Ne.symm habsorption)
    by_cases hrecurrence : base.predecessorValue = base.actualTail
    · by_cases hboundary : IsQuittingStationaryBoundaryAdmissible reward
          (quittingRootOfSimplex base.root) base.actualTail
      · exact Or.inl ⟨base.actualTail,
          base.uniformPayoff_of_recurrence_boundary
            habsorptionPos hrecurrence hboundary⟩
      · exact Or.inr (Or.inr ⟨{
          landing := landing
          base := base
          consecutive := consecutive
          absorption_pos := habsorptionPos
          obstruction := Or.inr hboundary }⟩)
    · exact Or.inr (Or.inr ⟨{
        landing := landing
        base := base
        consecutive := consecutive
        absorption_pos := habsorptionPos
        obstruction := Or.inl hrecurrence }⟩)

/-- **Actual-source low-survival boundary.**  Across compact scales, the
low-survival arm either feeds the checked instant-punishment producer, yields
a uniform payoff, leaves the positive-solo all-Continue phantom, or retains
the exact positive-absorption two-edge attachment residual. -/
theorem instantPunishment_or_uniformPayoff_or_phantom_or_attachmentResidual_of_lowSurvivalPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {u : ℝ} (hu : 0 < u) (huOne : u < 1)
    (hlow : HasLowSurvivalPrefixesAtCompactScales reward u) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      (∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom reward) ∨
      Nonempty
        (QuittingLowSurvivalPositiveAbsorptionAttachmentResidual reward u) := by
  rcases instantPunishmentExistence_or_positiveRhoLandingFamily_of_lowSurvivalPrefixes
      reward hu huOne hlow with hinstant | hlanding
  · exact Or.inl hinstant
  · obtain ⟨landing⟩ := hlanding
    exact Or.inr
      (uniformPayoff_or_phantom_or_positiveAbsorptionAttachmentResidual landing)

namespace PositiveRhoLandingCompactLimitRegression

open StationaryPrefixEndpointDecouplingRegression

/-- The local row-level Bellman/support/clip conditions do not force positive
absorption or identify the clipped tail with the actual tail.  The one-player
unit table realizes that local all-Continue seam: actual and predecessor
values are zero, while the zero-slack floor clip and support tail are one.
It is not an actual positive-rho source-family limit, because the checked
restart rationality above rules out its tail mismatch. -/
theorem exists_floorClippedBellmanData_with_zeroAbsorption_and_tailSeam :
    ∃ (root : PUnit → PMF Bool) (actual clipped predecessor : Payoff PUnit)
        (rho : ℝ),
      0 < rho ∧
      clipped = quittingPunishmentFloorClipAt reward 0 actual ∧
      predecessor = quittingRootSuccessorPayoff reward actual root ∧
      IsQuittingRootSupportApproxNash reward clipped 0 root ∧
      rho ≤ quittingStationaryContinueMass root ∧
      quittingRootAbsorptionMass root = 0 ∧
      clipped ≠ actual := by
  let root : PUnit → PMF Bool := quittingAllContinueRoot
  let actual : Payoff PUnit := fun _ ↦ 0
  let clipped : Payoff PUnit := fun _ ↦ 1
  let predecessor : Payoff PUnit := fun _ ↦ 0
  refine ⟨root, actual, clipped, predecessor, 1, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext who
    cases who
    simp [actual, clipped, punishmentValue_eq_one]
  · rw [quittingRootSuccessorPayoff_allContinueRoot_eq]
  · intro who
    constructor
    · intro hquit
      simp [root, quittingAllContinueRoot] at hquit
    · intro _
      have hendpoint : IsεQuittingRootEndpointNash reward
          (value 1) 0 quittingAllContinueRoot := by
        simpa [limit] using limit.endpointNash 0
      simpa [root, clipped, value, quittingAllContinueRoot] using
        (hendpoint who).1
  · simp [root, quittingStationaryContinueMass_eq_prod_continueProbability,
      quittingAllContinueRoot]
  · unfold quittingRootAbsorptionMass
    simp [root, quittingStationaryContinueMass_eq_prod_continueProbability,
      quittingAllContinueRoot]
  · intro heq
    have h := congrFun heq PUnit.unit
    norm_num [actual, clipped] at h

end PositiveRhoLandingCompactLimitRegression

end GameTheory
