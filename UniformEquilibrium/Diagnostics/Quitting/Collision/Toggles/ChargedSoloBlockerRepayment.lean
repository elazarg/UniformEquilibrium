/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Topology.Order.Lattice
import UniformEquilibrium.Diagnostics.Quitting.Capacity.InfiniteOrbitLimit
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PunishmentNormalAtomicCollisionHandoff
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SemanticCompactGap
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.TerminalGapExactRootMarginalCap
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Punishment.SoloCycleCompletion
import UniformEquilibrium.Quitting.Root.NashExistence

/-!
# Charged solo blockers: collision premium or coordinate repayment

On a literal four-player no-uniform branch, every positive solo rate in a
fixed compact interval has a strictly profitable outsider.  Compactness makes
this separation uniform over the four owners and the whole interval.

At a floor-safe exact solo seam, elementary algebra then gives a dichotomy.
Either the selected outsider's pair reward has a fixed premium over the
owner's singleton row, or every exact punishment-floor orbit anchored at that
literal seam eventually repays a fixed amount in the outsider coordinate.
The latter is coordinatewise only; it is not a payoff near-return.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction

private theorem finFour_outsiders_nonempty (owner : Fin 4) :
    (Finset.univ.erase owner).Nonempty := by
  obtain ⟨other, hne⟩ := exists_ne owner
  exact ⟨other, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ other⟩⟩

/-- The outsider's Quit-minus-Continue gain at the owner's singleton tail
for a scalar solo quit rate. -/
def finFourSoloBlockerGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner other : Fin 4) (rate : ℝ) : ℝ :=
  (1 - rate) * quittingSoloReward reward other other +
    rate * quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other

/-- Maximum outsider gain at one owner and one scalar solo rate. -/
def finFourSoloBlockerMax
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) (rate : ℝ) : ℝ :=
  (Finset.univ.erase owner).sup' (finFour_outsiders_nonempty owner)
    (fun other ↦ finFourSoloBlockerGain reward owner other rate)

theorem continuous_finFourSoloBlockerMax
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) :
    Continuous (finFourSoloBlockerMax reward owner) := by
  unfold finFourSoloBlockerMax finFourSoloBlockerGain
  apply Continuous.finset_sup'_apply (finFour_outsiders_nonempty owner)
  intro other _
  fun_prop

/-- On the same-table hard residual, failure of a uniform payoff makes the
maximum outsider gain strictly positive at every positive solo rate. -/
theorem FinFourQuantitativeFullSupportHardResidual.finFourSoloBlockerMax_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (owner : Fin 4) {rate : ℝ} (hrate0 : 0 < rate)
    (hrate1 : rate ≤ 1) :
    0 < finFourSoloBlockerMax reward owner rate := by
  by_contra hnotPos
  have hmax : finFourSoloBlockerMax reward owner rate ≤ 0 :=
    le_of_not_gt hnotPos
  let marginal := bernoulliBool rate hrate0.le hrate1
  have hspectator : ∀ other, other ≠ owner →
      (marginal true).toReal *
            reward ⟨{owner, other}, Finset.insert_nonempty owner {other}⟩ other +
          (marginal false).toReal *
            reward (quittingSingletonTerminal other) other ≤
        (marginal true).toReal *
            reward (quittingSingletonTerminal owner) other +
          (marginal false).toReal *
            quittingSoloReward reward owner other := by
    intro other hne
    have hmem : other ∈ Finset.univ.erase owner :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ other⟩
    have hle : finFourSoloBlockerGain reward owner other rate ≤
        finFourSoloBlockerMax reward owner rate := by
      unfold finFourSoloBlockerMax
      exact Finset.le_sup'
        (fun other ↦ finFourSoloBlockerGain reward owner other rate) hmem
    have hnonpos : finFourSoloBlockerGain reward owner other rate ≤ 0 :=
      hle.trans hmax
    simp only [marginal, bernoulliBool_true_toReal,
      bernoulliBool_false_toReal]
    change rate * quittingSingletonCollisionReward reward owner other +
        (1 - rate) * quittingSoloReward reward other other ≤
      rate * quittingSoloReward reward owner other +
        (1 - rate) * quittingSoloReward reward owner other
    calc
      _ = (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other := by ring
      _ ≤ quittingSoloReward reward owner other := by
        unfold finFourSoloBlockerGain at hnonpos
        linarith
      _ = _ := by ring
  have hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloMixedRoot owner marginal) :=
    isZeroQuittingRootEndpointNash_soloMixedRoot reward
      (quittingSoloReward reward owner) owner marginal rfl hspectator
  have huniform :=
    isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR
      reward owner marginal (by simp [marginal, hrate0]) (by
        have hroot : quittingSoloStationaryRoot owner marginal =
            quittingSoloMixedRoot owner marginal := by
          funext who
          by_cases hwho : who = owner
          · subst who
            simp [quittingSoloMixedRoot, quittingSoloStationaryRoot]
          · simp [quittingSoloMixedRoot, quittingSoloStationaryRoot,
              quittingAllContinueRoot, Function.update_of_ne hwho]
        rw [hroot]
        exact hnash) (by
        simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
          quittingSoloReward] using residual.all_punishmentNormal owner)
  exact hnot ⟨quittingSoloReward reward owner, huniform⟩

/-- Literal Fin4 adapter for the compact blocker gap.  The interval guard is
explicit: it is nonempty, starts at a positive rate, and stays below one. -/
theorem FinFourQuantitativeFullSupportHardResidual.exists_pos_uniformSoloBlockerGap
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound alpha beta : ℝ}
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (halpha : 0 < alpha) (hab : alpha ≤ beta) (hbeta : beta ≤ 1) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ owner rate,
      rate ∈ Set.Icc alpha beta →
        gap ≤ finFourSoloBlockerMax reward owner rate := by
  have howner : ∀ owner : Fin 4, ∃ ownerGap : ℝ,
      0 < ownerGap ∧ ∀ rate ∈ Set.Icc alpha beta,
        ownerGap ≤ finFourSoloBlockerMax reward owner rate := by
    intro owner
    apply exists_pos_compactGap_of_pos (Set.Icc alpha beta) isCompact_Icc
      ⟨alpha, le_rfl, hab⟩ (finFourSoloBlockerMax reward owner)
      (continuous_finFourSoloBlockerMax reward owner).continuousOn
    intro rate hrate
    exact residual.finFourSoloBlockerMax_pos hnot owner
      (halpha.trans_le hrate.1) (hrate.2.trans hbeta)
  choose ownerGap hownerGapPos hownerGap using howner
  let gapSet := Finset.univ.image ownerGap
  have hgapSet : gapSet.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let gap := gapSet.min' hgapSet
  have hgapMem : gap ∈ gapSet := Finset.min'_mem gapSet hgapSet
  obtain ⟨minOwner, _, hgapEq⟩ := Finset.mem_image.mp hgapMem
  refine ⟨gap, ?_, ?_⟩
  · rw [← hgapEq]
    exact hownerGapPos minOwner
  · intro owner rate hrate
    exact (Finset.min'_le gapSet (ownerGap owner)
      (Finset.mem_image.mpr ⟨owner, Finset.mem_univ owner, rfl⟩)).trans
        (hownerGap owner rate hrate)

/-- Choose an outsider attaining the finite maximum. -/
theorem exists_finFourSoloBlockerGain_eq_max
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) (rate : ℝ) :
    ∃ other, other ≠ owner ∧
      finFourSoloBlockerGain reward owner other rate =
        finFourSoloBlockerMax reward owner rate := by
  obtain ⟨other, hmem, heq⟩ := Finset.exists_mem_eq_sup'
    (finFour_outsiders_nonempty owner)
    (fun other ↦ finFourSoloBlockerGain reward owner other rate)
  exact ⟨other, (Finset.mem_erase.mp hmem).1, heq.symm⟩

/-- The terminal-gap marginal cap supplies the strict upper-rate hypothesis
used at a charged solo seam.  All bounds and the behavioral floor are kept
explicit, so this is applicable before any Fin4 specialization. -/
theorem QuittingTerminalExploitabilityWitness.exactFloorRoot_quitProbability_lt_one
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : Payoff iota) (root : iota → PMF Bool) (who : iota)
    {bound : ℝ} (hbound : 0 < bound)
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (htail : ∀ player, |tail player| ≤ bound)
    (hfloor : ∀ player, quittingPunishmentValue reward player ≤ tail player)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    (root who true).toReal < 1 := by
  have hcap := exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul
    reward tail root who witness.terminalGap_pos hreward htail hfloor
      witness.terminalExploitability hnash
  have hratio : 0 < witness.terminalGap / (4 * bound) :=
    div_pos witness.terminalGap_pos (mul_pos (by norm_num) hbound)
  linarith

/-! ## Anchored exact floor-orbit existence -/

private def selectedExactRoot
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail : Payoff iota) : iota → PMF Bool :=
  Classical.choose (exists_isZeroQuittingRootNash (reward := reward) tail)

private theorem selectedExactRoot_isZeroNash
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail : Payoff iota) :
    IsεQuittingRootNash reward tail 0 (selectedExactRoot reward tail) :=
  Classical.choose_spec (exists_isZeroQuittingRootNash (reward := reward) tail)

private def anchoredExactPoint
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (initial : Payoff iota) (initialRoot : iota → PMF Bool) :
    ℕ → Payoff iota × (iota → PMF Bool)
  | 0 => (initial, initialRoot)
  | time + 1 =>
      let nextValue := quittingRootSuccessorPayoff reward
        (anchoredExactPoint reward initial initialRoot time).1
        (anchoredExactPoint reward initial initialRoot time).2
      (nextValue, selectedExactRoot reward nextValue)

private theorem anchoredExactPoint_succ_value
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (initial : Payoff iota) (initialRoot : iota → PMF Bool) (time : ℕ) :
    (anchoredExactPoint reward initial initialRoot (time + 1)).1 =
      quittingRootSuccessorPayoff reward
        (anchoredExactPoint reward initial initialRoot time).1
        (anchoredExactPoint reward initial initialRoot time).2 := rfl

/-- Any exact root at a boxed floor tail extends to an infinite exact
punishment-floor orbit while preserving that literal root at time zero. -/
theorem exists_quittingPunishmentFloorInfiniteOrbit_anchored
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (initial : Payoff iota) (initialRoot : iota → PMF Bool)
    (hmem : initial ∈ quittingPunishmentFloorForwardCarrier reward)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ initial who)
    (hexact : IsεQuittingRootNash reward initial 0 initialRoot) :
    ∃ orbit : QuittingPunishmentFloorInfiniteOrbit reward,
      orbit.value 0 = initial ∧ orbit.roots 0 = initialRoot := by
  let point := anchoredExactPoint reward initial initialRoot
  have hpointMem : ∀ time,
      (point time).1 ∈ quittingPunishmentFloorForwardCarrier reward := by
    intro time
    induction time with
    | zero => exact hmem
    | succ time ih =>
        rw [show (point (time + 1)).1 =
          quittingRootSuccessorPayoff reward (point time).1
            (point time).2 from
          anchoredExactPoint_succ_value reward initial initialRoot time]
        constructor
        · intro who
          exact (abs_le.mp (abs_quittingRootExpectedPayoff_le_bound reward
            (point time).1 (point time).2 who
            (abs_reward_le_quittingRewardBound reward)
            (fun player => abs_le.mpr ⟨ih.1 player, ih.2 player⟩))).1
        · intro who
          exact (abs_le.mp (abs_quittingRootExpectedPayoff_le_bound reward
            (point time).1 (point time).2 who
            (abs_reward_le_quittingRewardBound reward)
            (fun player => abs_le.mpr ⟨ih.1 player, ih.2 player⟩))).2
  let orbit : QuittingPunishmentFloorInfiniteOrbit reward := {
    roots := fun time ↦ (point time).2
    value := fun time ↦ (point time).1
    value_mem := hpointMem
    anchor_floor := hfloor
    policy := fun time ↦
      anchoredExactPoint_succ_value reward initial initialRoot time
    exactNash := by
      intro time
      cases time with
      | zero => exact hexact
      | succ time =>
          exact selectedExactRoot_isZeroNash reward (point (time + 1)).1 }
  exact ⟨orbit, rfl, rfl⟩

/-! ## The universal repayment split -/

/-- Every anchored exact floor orbit has the packet's source-anchored
one-coordinate repayment, unless the selected pair row already has half the
blocker premium. -/
theorem chargedSoloBlocker_pairPremium_or_every_exactRepayment
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : Payoff (Fin 4)) (owner blocker : Fin 4)
    (_hne : blocker ≠ owner) (marginal : PMF Bool)
    {alpha gap : ℝ} (halpha : 0 < alpha) (hgap : 0 < gap)
    (halphaRate : alpha ≤ (marginal true).toReal)
    (hrateLtOne : (marginal true).toReal < 1)
    (hgain : gap ≤
      finFourSoloBlockerGain reward owner blocker
        (marginal true).toReal)
    (htail : tail blocker =
      (((1 - (marginal true).toReal) *
            quittingSoloReward reward blocker blocker +
          (marginal true).toReal *
            quittingSingletonCollisionReward reward owner blocker) -
        (marginal true).toReal * quittingSoloReward reward owner blocker) /
          (1 - (marginal true).toReal)) :
    quittingSingletonCollisionReward reward owner blocker -
          quittingSoloReward reward owner blocker ≥ gap / 2 ∨
      ∀ orbit : QuittingPunishmentFloorInfiniteOrbit reward,
        orbit.value 0 = tail →
        orbit.roots 0 = quittingSoloMixedRoot owner marginal →
        orbit.value 1 blocker =
            (1 - (marginal true).toReal) *
                quittingSoloReward reward blocker blocker +
              (marginal true).toReal *
                quittingSingletonCollisionReward reward owner blocker ∧
          ∃ limit : Payoff (Fin 4),
            (∀ who, Tendsto (fun time => orbit.value time who) atTop
              (nhds (limit who))) ∧
            alpha * gap / 2 ≤ limit blocker - orbit.value 1 blocker ∧
            ∃ time, 1 ≤ time ∧
              alpha * gap / 4 ≤
                orbit.value time blocker - orbit.value 1 blocker := by
  let p := (marginal true).toReal
  let s := quittingSoloReward reward blocker blocker
  let b := quittingSingletonCollisionReward reward owner blocker
  let R := quittingSoloReward reward owner blocker
  let Q := (1 - p) * s + p * b
  let g := Q - R
  by_cases hpremium : gap / 2 ≤ b - R
  · exact Or.inl hpremium
  · right
    intro orbit horbitValue horbitRoot
    have hp0 : 0 < p := halpha.trans_le halphaRate
    have hp1 : p < 1 := hrateLtOne
    have hden : 0 < 1 - p := sub_pos.mpr hp1
    have hg : gap ≤ g := by
      simpa only [finFourSoloBlockerGain, p, s, b, R, Q, g]
        using hgain
    have hfirst : orbit.value 1 blocker = Q := by
      rw [show orbit.value 1 = quittingRootSuccessorPayoff reward
          (orbit.value 0) (orbit.roots 0) by
        simpa using orbit.policy 0]
      rw [horbitValue, horbitRoot,
        quittingRootSuccessorPayoff_soloMixedRoot]
      have hsum : (marginal false).toReal = 1 - p := by
        have := quittingRoot_continueProbability_add_quitProbability
          (quittingSoloMixedRoot owner marginal) owner
        rw [quittingSoloMixedRoot_self] at this
        linarith
      have htail' : tail blocker = (Q - p * R) / (1 - p) := by
        simpa only [p, Q, R, s, b] using htail
      rw [hsum, htail']
      change p * R + (1 - p) * ((Q - p * R) / (1 - p)) = Q
      field_simp [ne_of_gt hden]
      ring
    obtain ⟨limit, hlimit, _, _, hsolo⟩ :=
      witness.infiniteOrbit_exists_value_limit orbit
    have hsoloDeficit : alpha * gap / 2 ≤ limit blocker - Q := by
      have hpremiumStrict : b - R < gap / 2 := lt_of_not_ge hpremium
      have hlimitSolo : s ≤ limit blocker := by
        simpa only [s] using hsolo blocker
      have hlimitQ : s - Q ≤ limit blocker - Q :=
        sub_le_sub_right hlimitSolo Q
      have hhalf : gap / 2 < g - (b - R) := by linarith
      have hrate : alpha * (gap / 2) ≤ p * (gap / 2) := by
        exact mul_le_mul_of_nonneg_right halphaRate (by positivity)
      have hscaled : p * (gap / 2) < p * (g - (b - R)) := by
        exact mul_lt_mul_of_pos_left hhalf hp0
      have hidentity : (1 - p) * (s - Q) = p * (g - (b - R)) := by
        dsimp only [s, Q, p, g, b, R]
        ring
      have hrepay : alpha * gap / 2 < s - Q := by
        apply lt_of_mul_lt_mul_left (a := 1 - p) (b := alpha * gap / 2)
          (c := s - Q) _ hden.le
        rw [hidentity]
        nlinarith [mul_pos halpha hgap]
      exact hrepay.le.trans hlimitQ
    have htargetLt : Q + alpha * gap / 4 < limit blocker := by
      nlinarith [mul_pos halpha hgap]
    have heventually : ∀ᶠ time in atTop,
        Q + alpha * gap / 4 < orbit.value time blocker :=
      (tendsto_order.1 (hlimit blocker)).1 _ htargetLt
    obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp heventually
    let time := max 1 threshold
    refine ⟨hfirst, limit, hlimit, ?_, time, le_max_left _ _, ?_⟩
    · rw [hfirst]
      exact hsoloDeficit
    · have hlate := hthreshold time (le_max_right _ _)
      rw [hfirst]
      linarith

end GameTheory
