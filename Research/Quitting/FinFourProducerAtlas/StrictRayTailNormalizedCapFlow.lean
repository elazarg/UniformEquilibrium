/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ForwardExactCapTailFlow
import Research.Quitting.FinFourProducerAtlas.MaximalPrefixRayDichotomy
import UniformEquilibrium.Quitting.Classification.LCP.Normalization

/-!
# The strict Fin4 maximal ray as a tail-normalized forward cap flow

The source theorem below has an honest left branch.  A zero-absorption
selected maximal root is all Continue, is the unique exact root at that cap,
and fixes the autonomous semantic orbit literally.  Otherwise every selected
root has positive total marginal hazard and the strict ray gives an actual
`QuittingForwardExactCapTail`.

The packet's first-order solo/collision expansions are kept in the separate
`QuittingTailNormalizedCapFlow` certificate.  They are not consequences of
summability alone, and this module does not pretend that the current API has
already supplied them.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Set

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda)

private abbrev rayPair (time : ℕ) : QuittingTerminalSemanticPair (Fin 4) :=
  quittingMaximalCapSemanticPrefixOrbit reward packet.raySource time

private abbrev rayRoot (time : ℕ) : Fin 4 → PMF Bool :=
  quittingMaximalCapSemanticRoot reward (packet.rayPair time)

/-- The selected maximal root is all Continue at one date and the autonomous
semantic orbit is literally fixed from that date onward.  Maximality also
makes all Continue the unique exact root at the fixed cap. -/
structure FinFourMaximalRayEventualAllContinue where
  strict : MaximalPrefixRayStall packet
  cutoff : ℕ
  pair_eq : ∀ offset, packet.rayPair (cutoff + offset) = packet.rayPair cutoff
  root_eq : ∀ offset,
    packet.rayRoot (cutoff + offset) =
      (quittingAllContinueRoot : Fin 4 → PMF Bool)
  unique_exactRoot : ∀ candidate : Fin 4 → PMF Bool,
    IsεQuittingRootNash reward (packet.rayPair cutoff).2 0 candidate →
      candidate = (quittingAllContinueRoot : Fin 4 → PMF Bool)

/-- Actual nonstall branch of the strict ray.  The forward ray retains the
same minimum source, semantic source, selected maximal roots, and strict-stall
proof.  Its normalized current and tail hazards and exact renewal law are the
generic definitions on `forward`. -/
structure FinFourStrictRayForwardExactCapTail where
  strict : MaximalPrefixRayStall packet
  forward : QuittingForwardExactCapTail reward
  pair_eq : forward.pair = packet.rayPair
  root_eq : forward.root = packet.rayRoot

namespace FinFourStrictRayForwardExactCapTail

theorem pair_apply
    (flow : FinFourStrictRayForwardExactCapTail packet) (time : ℕ) :
    flow.forward.pair time = packet.rayPair time := by
  rw [flow.pair_eq]

theorem root_apply
    (flow : FinFourStrictRayForwardExactCapTail packet) (time : ℕ) :
    flow.forward.root time = packet.rayRoot time := by
  rw [flow.root_eq]

theorem source_eq
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    flow.forward.pair 0 = packet.raySource := by
  rw [flow.pair_apply]
  rfl

theorem currentHazard_sum
    (flow : FinFourStrictRayForwardExactCapTail packet) (time : ℕ) :
    ∑ who, flow.forward.currentHazard time who = 1 :=
  flow.forward.sum_currentHazard time

theorem tailAverage_renewal
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (time : ℕ) (who : Fin 4) :
    flow.forward.tailAverage time who =
      flow.forward.renewalRatio time * flow.forward.currentHazard time who +
        (1 - flow.forward.renewalRatio time) *
          flow.forward.tailAverage (time + 1) who :=
  flow.forward.tailAverage_renewal time who

theorem eventually_currentHazard_supported_binding
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    ∀ᶠ time in atTop, ∀ who,
      0 < flow.forward.currentHazard time who →
        who ∈ flow.forward.bindingFinset :=
  flow.forward.eventually_currentHazard_supported_binding

/-- Adding the two first-order product estimates upgrades the actual Fin4
ray to the selector-independent tail-normalized collision certificate. -/
structure Analysis (flow : FinFourStrictRayForwardExactCapTail packet) where
  normalized : QuittingTailNormalizedCapFlow reward flow.forward
  soloMatrix_eq : normalized.soloMatrix =
    QuittingLCPClassification.normalizedSoloMatrix reward
  collisionMatrix_eq : normalized.collisionMatrix = fun who owner ↦
    if h : who = owner then 0 else
      reward ⟨{who, owner}, by simp⟩ who -
        reward (quittingSingletonTerminal owner) who

end FinFourStrictRayForwardExactCapTail

private theorem root_eq_allContinue_of_absorption_eq_zero
    (root : Fin 4 → PMF Bool)
    (hzero : quittingRootAbsorptionMass root = 0) :
    root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at hzero
    linarith
  funext who
  simpa [quittingAllContinueRoot] using
    eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

private theorem pair_and_root_fixed_of_absorption_eq_zero
    (time : ℕ)
    (hzero : quittingRootAbsorptionMass (packet.rayRoot time) = 0) :
    (∀ offset, packet.rayPair (time + offset) = packet.rayPair time) ∧
      ∀ offset, packet.rayRoot (time + offset) =
        (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  have hroot := root_eq_allContinue_of_absorption_eq_zero
    (packet.rayRoot time) hzero
  have hnash := quittingMaximalCapSemanticRoot_exactNash reward
    (packet.rayPair time)
  have hfixed : quittingTerminalSemanticPrefix reward
      (quittingAllContinueRoot : Fin 4 → PMF Bool) (packet.rayPair time) =
        packet.rayPair time := by
    apply quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
    exact (isZeroQuittingRootNash_allContinue_iff_singleton_le reward
      (packet.rayPair time).2).1 (by simpa [hroot] using hnash)
  constructor
  · intro offset
    induction offset with
    | zero => simp
    | succ offset ih =>
        have ih' : quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
            (time + offset) = packet.rayPair time := ih
        change quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
          (time + offset + 1) = packet.rayPair time
        rw [quittingMaximalCapSemanticPrefixOrbit_succ]
        rw [ih']
        change quittingTerminalSemanticPrefix reward (packet.rayRoot time)
          (packet.rayPair time) = packet.rayPair time
        rw [hroot]
        exact hfixed
  · intro offset
    have hpairs : packet.rayPair (time + offset) = packet.rayPair time := by
      induction offset with
      | zero => simp
      | succ offset ih =>
          have ih' : quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
              (time + offset) = packet.rayPair time := ih
          change quittingMaximalCapSemanticPrefixOrbit reward packet.raySource
            (time + offset + 1) = packet.rayPair time
          rw [quittingMaximalCapSemanticPrefixOrbit_succ]
          rw [ih']
          change quittingTerminalSemanticPrefix reward (packet.rayRoot time)
            (packet.rayPair time) = packet.rayPair time
          rw [hroot]
          exact hfixed
    change quittingMaximalCapSemanticRoot reward
      (packet.rayPair (time + offset)) = _
    rw [hpairs]
    exact hroot

private theorem unique_exactRoot_of_absorption_eq_zero
    (time : ℕ)
    (hzero : quittingRootAbsorptionMass (packet.rayRoot time) = 0)
    (candidate : Fin 4 → PMF Bool)
    (hcandidate : IsεQuittingRootNash reward (packet.rayPair time).2 0 candidate) :
    candidate = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  have hmax := quittingMaximalCapSemanticRoot_maximal reward
    (packet.rayPair time) candidate hcandidate
  have hcandidateZero : quittingRootAbsorptionMass candidate = 0 :=
    le_antisymm (hmax.trans_eq hzero) (quittingRootAbsorptionMass_nonneg _)
  exact root_eq_allContinue_of_absorption_eq_zero candidate hcandidateZero

private theorem exists_capLimit_of_positive_hazard
    (strict : MaximalPrefixRayStall packet) :
    ∃ capLimit : Payoff (Fin 4),
      ∀ who, Tendsto (fun time ↦ (packet.rayPair time).2 who)
        atTop (nhds (capLimit who)) := by
  have habsorption : Summable (fun time ↦
      quittingRootAbsorptionMass (packet.rayRoot time)) := by
    change Summable
      (quittingMaximalCapSemanticPrefixAbsorption reward packet.raySource)
    exact strict.stall.summable_absorption
      (packet.rayBaseProfile 0) (packet.rayBaseProfile_semantic_eq 0)
  let total : ℕ → ℝ := fun time ↦
    ∑ who, quittingRootQuitRates (packet.rayRoot time) who
  have htotal : Summable total := by
    unfold total
    apply summable_sum
    intro who _
    exact habsorption.of_nonneg_of_le (fun time ↦ ENNReal.toReal_nonneg)
      (fun time ↦ quitProbability_le_quittingRootAbsorptionMass
        (packet.rayRoot time) who)
  have hcoordinate : ∀ who, ∃ limit : ℝ,
      Tendsto (fun time ↦ (packet.rayPair time).2 who)
        atTop (nhds limit) := by
    intro who
    apply Math.Viability.exists_tendsto_of_summable_step_bound
      (fun time ↦ (packet.rayPair time).2 who) total
        (2 * quittingRewardBound reward)
    · intro time
      have hcap : (packet.rayPair (time + 1)).2 =
          quittingRootSuccessorPayoff reward (packet.rayPair time).2
            (packet.rayRoot time) := by
        change (quittingMaximalCapSemanticPrefixOrbit reward
          packet.raySource (time + 1)).2 = _
        rw [quittingMaximalCapSemanticPrefixOrbit_succ]
        exact quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
          (packet.rayPair time) (packet.rayRoot time)
            (quittingMaximalCapSemanticRoot_exactNash reward _)
      have hbox := quittingTerminalSemanticCarrier_mem_box reward
        (packet.rayPair time) (abs_reward_le_quittingRewardBound reward)
        (quittingMaximalCapSemanticPrefixOrbit_mem_carrier reward
          packet.raySource packet.raySource_mem time)
      rw [Real.dist_eq, hcap]
      simpa only [total, abs_sub_comm] using
        (abs_quittingRootSuccessorPayoff_sub_tail_le_sum_quitRates
        reward (packet.rayPair time).2 (packet.rayRoot time) who
          (abs_reward_le_quittingRewardBound reward)
          (abs_le.mpr ⟨hbox.2.1 who, hbox.2.2 who⟩))
    · exact htotal
  choose capLimit hcapLimit using hcoordinate
  exact ⟨capLimit, hcapLimit⟩

private theorem singleton_le_capLimit
    (strict : MaximalPrefixRayStall packet)
    (capLimit : Payoff (Fin 4))
    (hcapLimit : ∀ who, Tendsto (fun time ↦ (packet.rayPair time).2 who)
      atTop (nhds (capLimit who))) (who : Fin 4) :
    reward (quittingSingletonTerminal who) who ≤ capLimit who := by
  have habsorption : Summable (fun time ↦
      quittingRootAbsorptionMass (packet.rayRoot time)) := by
    change Summable
      (quittingMaximalCapSemanticPrefixAbsorption reward packet.raySource)
    exact strict.stall.summable_absorption
      (packet.rayBaseProfile 0) (packet.rayBaseProfile_semantic_eq 0)
  have habsLimit := habsorption.tendsto_atTop_zero
  have hleft : Tendsto (fun time ↦
      reward (quittingSingletonTerminal who) who -
        2 * quittingRewardBound reward *
          quittingRootAbsorptionMass (packet.rayRoot time)) atTop
      (nhds (reward (quittingSingletonTerminal who) who)) := by
    simpa using tendsto_const_nhds.sub
      (habsLimit.const_mul (2 * quittingRewardBound reward))
  have hright := (hcapLimit who).comp (tendsto_add_atTop_nat 1)
  have hlower : ∀ time,
      reward (quittingSingletonTerminal who) who -
          2 * quittingRewardBound reward *
            quittingRootAbsorptionMass (packet.rayRoot time) ≤
        (packet.rayPair (time + 1)).2 who := by
    intro time
    have hnash := quittingMaximalCapSemanticRoot_exactNash reward
      (packet.rayPair time)
    have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash reward
      (packet.rayPair time).2 (packet.rayRoot time) who hnash
    have hcap : (packet.rayPair (time + 1)).2 who =
        quittingRootSuccessorPayoff reward (packet.rayPair time).2
          (packet.rayRoot time) who := by
      change (quittingMaximalCapSemanticPrefixOrbit reward
        packet.raySource (time + 1)).2 who = _
      rw [quittingMaximalCapSemanticPrefixOrbit_succ]
      exact congrFun
        (quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
          (packet.rayPair time) (packet.rayRoot time) hnash) who
    have hendpoint :=
      abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
        reward (packet.rayPair time).2 (packet.rayRoot time) who
          (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)
    have hopponent := quittingRootOpponentAbsorptionMass_le_absorptionMass
      (packet.rayRoot time) who
    have hfactor : 0 ≤ 2 * quittingRewardBound reward :=
      mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)
    rw [hcap]
    have herror := hendpoint.trans
      (mul_le_mul_of_nonneg_left hopponent hfactor)
    linarith [neg_le_of_abs_le herror, hquit]
  have hdiff := hright.sub hleft
  have hnonneg : 0 ≤ capLimit who -
      reward (quittingSingletonTerminal who) who :=
    ge_of_tendsto' hdiff fun time ↦ sub_nonneg.mpr (hlower time)
  linarith

private noncomputable def forwardExactCapTail
    (strict : MaximalPrefixRayStall packet)
    (hpositive : ∀ time, 0 < quittingRootAbsorptionMass (packet.rayRoot time)) :
    QuittingForwardExactCapTail reward := by
  let capLimit := Classical.choose
    (packet.exists_capLimit_of_positive_hazard strict)
  have hcapLimit := Classical.choose_spec
    (packet.exists_capLimit_of_positive_hazard strict)
  refine {
    pair := packet.rayPair
    root := packet.rayRoot
    pair_mem := quittingMaximalCapSemanticPrefixOrbit_mem_carrier reward
      packet.raySource packet.raySource_mem
    exactNash := fun time ↦ quittingMaximalCapSemanticRoot_exactNash reward
      (packet.rayPair time)
    forward := quittingMaximalCapSemanticPrefixOrbit_succ reward packet.raySource
    absorption_summable := ?_
    totalHazard_pos := ?_
    capLimit := capLimit
    cap_tendsto := hcapLimit
    singleton_le_capLimit := packet.singleton_le_capLimit strict capLimit hcapLimit
  }
  · change Summable
      (quittingMaximalCapSemanticPrefixAbsorption reward packet.raySource)
    exact strict.stall.summable_absorption
      (packet.rayBaseProfile 0) (packet.rayBaseProfile_semantic_eq 0)
  · intro time
    have hle := quittingRootAbsorptionMass_le_sum_quitRates
      (packet.rayRoot time)
    exact hpositive time |>.trans_le hle

/-- Honest source split for a strict Fin4 maximal ray.  The branches are not
advertised as logical negations: the right branch records the actual positive
hazard proof used to normalize every date. -/
theorem eventualAllContinue_or_nonempty_strictRayForwardExactCapTail
    (strict : MaximalPrefixRayStall packet) :
    Nonempty (FinFourMaximalRayEventualAllContinue packet) ∨
      Nonempty (FinFourStrictRayForwardExactCapTail packet) := by
  by_cases hzero : ∃ time,
      quittingRootAbsorptionMass (packet.rayRoot time) = 0
  · left
    obtain ⟨time, htime⟩ := hzero
    have hfixed := packet.pair_and_root_fixed_of_absorption_eq_zero time htime
    exact ⟨{
      strict := strict
      cutoff := time
      pair_eq := hfixed.1
      root_eq := hfixed.2
      unique_exactRoot := packet.unique_exactRoot_of_absorption_eq_zero time htime
    }⟩
  · right
    have hpositive : ∀ time,
        0 < quittingRootAbsorptionMass (packet.rayRoot time) := by
      intro time
      exact lt_of_le_of_ne (quittingRootAbsorptionMass_nonneg _)
        (fun heq ↦ hzero ⟨time, heq.symm⟩)
    let forward := packet.forwardExactCapTail strict hpositive
    exact ⟨{
      strict := strict
      forward := forward
      pair_eq := rfl
      root_eq := rfl
    }⟩

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
