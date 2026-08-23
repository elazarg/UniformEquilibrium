/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Capacity.InfiniteOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Debt.ViolationCollapse
import UniformEquilibrium.Quitting.Debt.Dynamic.PositiveDebtSelfLoopLimit

/-!
# The positive-debt self-loop limit of the counterexample tail

The terminal exploitability witness's optimized exact-debt tail converges
coordinatewise to a positive-debt all-Continue exact self-loop. The original
projective subsequence, exact-edge certificates, terminal-gap margin, and
summable absorption and opponent clocks are retained.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- The optimized tail converges coordinatewise in value and debt to a
positive-debt all-Continue exact dynamic-debt self-loop. -/
theorem exists_terminalGapDynamicDebtTail_selfLoopLimit
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ (tail : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
        (limit : QuittingPositiveDebtSelfLoopLimit reward),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ @quittingFiniteMinMaxDynamicDebtTail ι _ _
            witness.nonempty_players reward cutoff) ∘ subseq)
          atTop (nhds tail) ∧
      (∀ time, tail time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (tail time) (tail (time + 1))) ∧
      witness.terminalGap ≤ (tail 0).2 limit.owner ∧
      witness.terminalGap ≤ limit.debt limit.owner ∧
      (∀ who, Tendsto (fun time ↦ (tail time).1.1 who) atTop
        (nhds (limit.value who))) ∧
      (∀ who, Tendsto (fun time ↦ (tail time).2 who) atTop
        (nhds (limit.debt who))) ∧
      (∀ who, Tendsto (fun time ↦
          (quittingDynamicDebtTailRoots tail time who true).toReal)
        atTop (nhds 0)) ∧
      (∀ who, Tendsto (fun time ↦
          (quittingDynamicDebtTailRoots tail time who false).toReal)
        atTop (nhds 1)) ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots tail) limit.owner) ∧
      Summable (quittingDynamicDebtTailAbsorptionCharge tail) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨tail, subseq, owner, hsubseq, hprojective, hbox, hedge,
      hownerDebt, hownerClock, habsorption⟩ :=
    witness.exists_terminalGapDynamicDebtTail_summableAbsorption
  have hvalueConverge : ∀ who : ι, ∃ coordinateLimit : ℝ,
      Tendsto (fun time ↦ (tail time).1.1 who) atTop
        (nhds coordinateLimit) := by
    intro who
    have hdist : Summable (fun time ↦
        dist ((tail time).1.1 who) ((tail (time + 1)).1.1 who)) := by
      simpa [Real.dist_eq, abs_sub_comm] using
        QuittingDynamicDebtTail.summable_abs_value_succ_sub
          tail (fun time player ↦ abs_le.mpr
            ⟨(hbox time).1.1 player, (hbox time).1.2 player⟩)
          hedge habsorption who
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  choose valueLimit hvalueLimit using hvalueConverge
  let debtLimit : Payoff ι := fun who ↦ ⨆ time, (tail time).2 who
  have hdebtLimit : ∀ who,
      Tendsto (fun time ↦ (tail time).2 who) atTop
        (nhds (debtLimit who)) := by
    intro who
    exact tendsto_atTop_ciSup
      (QuittingDynamicDebtTail.monotone_debt tail
        (fun time ↦ (hbox time).2.1) hedge who)
      (QuittingDynamicDebtTail.bddAbove_range_debt tail
        (fun time ↦ (hbox time).2.2) who)
  have hvalueBox : valueLimit ∈ Set.Icc
      (fun _ : ι ↦ -quittingRewardBound reward)
      (fun _ : ι ↦ quittingRewardBound reward) := by
    constructor
    · intro who
      exact ge_of_tendsto' (hvalueLimit who)
        (fun time ↦ (hbox time).1.1 who)
    · intro who
      exact le_of_tendsto' (hvalueLimit who)
        (fun time ↦ (hbox time).1.2 who)
  have hdebtBox : debtLimit ∈ Set.Icc (0 : Payoff ι)
      (quittingPositiveSingletonDebtCap reward) := by
    constructor
    · intro who
      exact ge_of_tendsto' (hdebtLimit who)
        (fun time ↦ (hbox time).2.1 who)
    · intro who
      exact le_of_tendsto' (hdebtLimit who)
        (fun time ↦ (hbox time).2.2 who)
  have habsorptionZero : Tendsto
      (quittingDynamicDebtTailAbsorptionCharge tail) atTop (nhds 0) :=
    habsorption.tendsto_atTop_zero
  have hopponentZero : ∀ who, Tendsto (fun time ↦
      quittingRootOpponentAbsorptionMass
        (quittingDynamicDebtTailRoots tail time) who) atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun _ ↦ quittingOpponentClockCharge_nonneg
        (quittingDynamicDebtTailRoots tail) who _
    · exact fun time ↦ quittingRootOpponentAbsorptionMass_le_absorptionMass
        (quittingDynamicDebtTailRoots tail time) who
    · exact habsorptionZero
  have hsolo : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ valueLimit who := by
    intro who
    have hlower : Tendsto (fun time ↦
        quittingSoloReward reward who who -
          2 * quittingRewardBound reward *
            quittingRootOpponentAbsorptionMass
              (quittingDynamicDebtTailRoots tail time) who)
        atTop (nhds (quittingSoloReward reward who who)) := by
      have hscaled := (hopponentZero who).const_mul
        (2 * quittingRewardBound reward)
      simpa using tendsto_const_nhds.sub hscaled
    have hle := le_of_tendsto_of_tendsto' hlower (hvalueLimit who)
      (fun time ↦ QuittingDynamicDebtTail.soloReward_sub_opponentHazard_le_value
        tail hedge time who)
    exact hle
  have hownerZero_le_limit : (tail 0).2 owner ≤ debtLimit owner :=
    ge_of_tendsto' (hdebtLimit owner) fun time ↦
      QuittingDynamicDebtTail.monotone_debt tail
        (fun date ↦ (hbox date).2.1) hedge owner
        (Nat.zero_le time)
  have hownerLimit : witness.terminalGap ≤ debtLimit owner :=
    hownerDebt.trans hownerZero_le_limit
  have hselfNash : IsQuittingNashBellmanEdge reward
      (valueLimit, quittingAllContinueSimplexRoot)
      (valueLimit, quittingAllContinueSimplexRoot) := by
    constructor
    · change valueLimit = quittingRootSuccessorPayoff reward valueLimit
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        quittingRootSuccessorPayoff_allContinueRoot_eq]
    · change IsεQuittingRootEndpointNash reward valueLimit 0
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
      exact quittingAllContinueRoot_isZeroNash_of_singleton_le
        reward valueLimit hsolo
  have hopponentMass : ∀ who,
      quittingDebtOpponentContinueMass
          (((valueLimit, quittingAllContinueSimplexRoot), debtLimit) :
            QuittingDebtPoint ι) who = 1 := by
    intro who
    rw [quittingDebtOpponentContinueMass_eq_stationary,
      quittingRootOfSimplex_allContinueSimplexRoot]
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    apply Finset.prod_eq_one
    intro player _
    by_cases hplayer : player = who
    · subst player
      simp
    · rw [Function.update_of_ne hplayer]
      simp [quittingAllContinueRoot]
  have hselfDynamic : IsQuittingDynamicDebtEdge reward
      ((valueLimit, quittingAllContinueSimplexRoot), debtLimit)
      ((valueLimit, quittingAllContinueSimplexRoot), debtLimit) := by
    refine ⟨hselfNash, fun who ↦ ?_⟩
    unfold quittingDynamicDebtUpdate
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootQuitPayoff_allContinueRoot,
      quittingRootContinuePayoff_allContinueRoot,
      hopponentMass who]
    have hdebtNonneg := hdebtBox.1 who
    rw [max_eq_right]
    · dsimp
      ring
    · dsimp only
      rw [one_mul]
      exact (hsolo who).trans (le_add_of_nonneg_right hdebtNonneg)
  let limit : QuittingPositiveDebtSelfLoopLimit reward := {
    value := valueLimit
    debt := debtLimit
    owner := owner
    ownerDebt_pos := lt_of_lt_of_le witness.terminalGap_pos hownerLimit
    state_mem := ⟨hvalueBox, hdebtBox⟩
    exactSelfLoop := hselfDynamic }
  have hquitConverge : ∀ who, Tendsto (fun time ↦
      (quittingDynamicDebtTailRoots tail time who true).toReal)
      atTop (nhds 0) := fun who ↦
    quitProbability_tendsto_zero_of_summable_dynamicDebtTailAbsorptionCharge
      tail habsorption who
  have hcontinueConverge : ∀ who, Tendsto (fun time ↦
      (quittingDynamicDebtTailRoots tail time who false).toReal)
      atTop (nhds 1) := fun who ↦
    continueProbability_tendsto_one_of_summable_dynamicDebtTailAbsorptionCharge
      tail habsorption who
  exact ⟨tail, subseq, limit, hsubseq, hprojective, hbox, hedge,
    hownerDebt, hownerLimit, hvalueLimit, hdebtLimit, hquitConverge,
    hcontinueConverge, hownerClock, habsorption⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
