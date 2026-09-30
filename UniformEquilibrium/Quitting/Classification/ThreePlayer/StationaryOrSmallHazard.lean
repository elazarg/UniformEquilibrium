/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.SingletonDispatch
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer
import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQProducer
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Normalized three-player stationary-or-small-hazard terminal equilibria

The strategy-class producer retains actual stationary roots or explicit
root sequences with every player's Quit hazard small at every live date.
The singleton alternative covers weak comparisons and degenerate supports.
When no feasible singleton mixture exists, the original-game analytic germ
has an absorbing endpoint that compiles to an exact stationary equilibrium.

Every own-singleton reward is exactly one. No all-sign, coordinate-scaling,
player-cardinality transport, or claim about a printed subdivision rate is made.
-/

noncomputable section

namespace GameTheory.QuittingThreePlayerStrategyClass

open StochasticGame QuittingLCPClassification

/-- A stationary terminal approximate equilibrium or a root-sequence terminal
approximate equilibrium with every date/player Quit hazard bounded by its accuracy. -/
def StationaryOrSmallHazardTerminalEquilibrium
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  (∃ root : ι → PMF Bool,
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
      (quittingStationaryProfile reward root)) ∨
  ∃ roots : ℕ → ι → PMF Bool,
    (∀ time who, (roots time who true).toReal ≤ ε) ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
      (quittingRootSequenceProfile reward roots 0)

/-- A normalized solo column with weak inactive-player comparisons supplies
stationary terminal approximate equilibria, including equality cases. -/
theorem of_normalizedSoloColumn
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (owner : Fin 3)
    (hcross : ∀ other, other ≠ owner →
      1 ≤ reward (quittingSingletonTerminal owner) other)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  let M := quittingRewardBound reward
  let p := ε / (2 * M + ε)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hden : 0 < 2 * M + ε := by positivity
  have hp : 0 < p := div_pos hε hden
  have hp1 : p ≤ 1 := (div_le_one hden).2 (by linarith)
  have herror : 2 * M * p < ε := by
    dsimp only [p]
    rw [show 2 * M * (ε / (2 * M + ε)) =
      (2 * M * ε) / (2 * M + ε) by ring, div_lt_iff₀ hden]
    nlinarith [mul_pos hε hε]
  let hazard := quittingHazardCoin p hp.le hp1
  have hpositive : 0 < (hazard true).toReal := by
    simpa [hazard, quittingHazardCoin_true_toReal] using hp
  have hself : 0 ≤ quittingSoloReward reward owner owner := by
    change 0 ≤ reward (quittingSingletonTerminal owner) owner
    rw [hsolo owner]
    norm_num
  left
  refine ⟨quittingSoloStationaryRoot owner hazard, ?_⟩
  intro who deviation
  rw [quittingTerminalPayoff_soloStationary reward owner who hazard hpositive]
  by_cases hwho : who = owner
  · subst who
    exact (quittingTerminalPayoff_update_solo_owner_le reward owner hazard deviation).trans
      ((max_le hself le_rfl).trans (le_add_of_nonneg_right hε.le))
  · refine (quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward (quittingSoloStationaryRoot owner hazard) who deviation
        (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
          hwho hazard hpositive)).trans ?_
    rw [quittingStationaryUnilateralCap_solo_other reward hwho hazard hpositive,
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward hwho hazard]
    apply max_le
    · have hbase : quittingSoloReward reward who who ≤
          quittingSoloReward reward owner who := by
        change reward (quittingSingletonTerminal who) who ≤
          reward (quittingSingletonTerminal owner) who
        rw [hsolo who]
        exact hcross who hwho
      have hcol : quittingSingletonCollisionReward reward owner who ≤ M :=
        (abs_le.mp (abs_reward_le_quittingRewardBound reward ⟨{owner, who}, by simp⟩ who)).2
      have hsoloLower : -M ≤ quittingSoloReward reward who who := by
        simpa [quittingSoloReward, quittingSingletonTerminal] using
          (abs_le.mp (abs_reward_le_quittingRewardBound reward
            (quittingSingletonTerminal who) who)).1
      have hproduct := mul_le_mul_of_nonneg_left
        (show quittingSingletonCollisionReward reward owner who -
          quittingSoloReward reward who who ≤ 2 * M by linarith) hp.le
      simp only [hazard, quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]
      nlinarith
    · exact le_add_of_nonneg_right hε.le

/-- The normalized complementary branch, including simplex vertices.
The nonvertex branch reuses the homogeneous stationary-root producer. -/
theorem of_normalizedHomogeneousWitness
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (weight : Convexity.StdSimplex ℝ (Fin 3))
    (hresidual : ∀ who, 0 ≤ _root_.Math.LinearProgramming.singletonLCPResidual
      (normalizedSoloMatrix reward) weight who)
    (hcomplementary : ∀ who, weight.weights who *
      _root_.Math.LinearProgramming.singletonLCPResidual
        (normalizedSoloMatrix reward) weight who = 0)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  by_cases hvertex : ∃ owner, weight.weights owner = 1
  · obtain ⟨owner, howner⟩ := hvertex
    apply of_normalizedSoloColumn reward hsolo owner _ hε
    intro other _
    have hcolumn :=
      QuittingLCPClassification.singletonLCPResidual_eq_column_of_weight_eq_one
        (QuittingLCPClassification.normalizedSoloMatrix reward) weight howner other
    have hnonnegative := hresidual other
    rw [hcolumn, normalizedSoloMatrix_eq_projectiveLCPMatrix] at hnonnegative
    change 0 ≤ reward (quittingSingletonTerminal owner) other -
      reward (quittingSingletonTerminal other) other at hnonnegative
    rw [hsolo other] at hnonnegative
    linarith
  · have hnonvertex (who : Fin 3) : weight.weights who < 1 := by
      have hle : weight.weights who ≤ 1 := by
        rw [← weight.total_of_fintype]
        exact Finset.single_le_sum
          (fun owner _ => weight.weights_nonneg owner) (Finset.mem_univ who)
      exact lt_of_le_of_ne hle (fun heq => hvertex ⟨who, heq⟩)
    have hstationary :=
      isQuittingStationaryUniformEquilibriumPayoff_of_nonvertexHomogeneousWitness
        reward weight hresidual hcomplementary hnonvertex
    obtain ⟨root, hnash, -⟩ := hstationary ε hε
    exact Or.inl ⟨root, hnash⟩

/-- A balanced normalized singleton mixture supplies stationary terminal
approximate equilibria, including simplex vertices. -/
theorem of_normalizedBalancedSingletonMixture
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3))
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (weight : Convexity.StdSimplex ℝ (Fin 3))
    (hbalance : ∀ who, quittingSingletonMixture reward weight.weights who = 1)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  have hresidual (who : Fin 3) : _root_.Math.LinearProgramming.singletonLCPResidual
      (normalizedSoloMatrix reward) weight who = 0 := by
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    unfold _root_.Math.LinearProgramming.singletonLCPResidual wsum dotProduct
      quittingProjectiveLCPMatrix
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    change quittingSingletonMixture reward weight.weights who -
      (∑ owner, weight.weights owner) * reward (quittingSingletonTerminal who) who = 0
    rw [weight.total_of_fintype, hbalance who, hsolo who]
    ring
  exact of_normalizedHomogeneousWitness reward hsolo weight
    (fun who => by rw [hresidual who]) (fun who => by rw [hresidual who]; ring) hε

/-- Exact coarse-arc subdivision simultaneously bounds terminal exploitability
and every date/player Quit hazard. The explicit rate is `1 - (1 - p)^(1/m)`. -/
theorem of_singletonArcCycle
    {ι : Type} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (initial : Fin L) {aStar D ε : ℝ}
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (ha : ∀ block, quittingMeshIntensity (p block) ≤ aStar)
    (hD : 0 ≤ D)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block)) (coarse (finRotate L block)))
    (hactive : ∀ block,
      coarse block (owner block) = quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who, quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hcoarseContracts : ∀ who,
      (∏ block : Fin L, if who = owner block then 1 else 1 - p block) < 1)
    (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  have haStar : 0 ≤ aStar :=
    (quittingMeshIntensity_nonneg (hp0 initial) (hp1 initial).le).trans (ha initial)
  obtain ⟨m, hmLarge⟩ := exists_nat_gt ((1 + D) * aStar / ε)
  have hmReal : 0 < (m : ℝ) :=
    (div_nonneg (mul_nonneg (by linarith) haStar) hε.le).trans_lt hmLarge
  have hm : 0 < m := by exact_mod_cast hmReal
  have hscaled : (1 + D) * aStar < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hmLarge
  have hhazard : aStar / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hmReal]
    nlinarith
  have herror : D * aStar / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hmReal]
    nlinarith
  let cycle := quittingSingletonArcCycleRoot owner p m hp0 hp1
  let phase := quittingSingletonMeshInitialPhase initial m hm
  right
  refine ⟨quittingCyclicRootSequence cycle phase, ?_, ?_⟩
  · intro time who
    let block := quittingSingletonMeshBlock (quittingCyclicOrbit phase time)
    change (quittingSoloStationaryRoot (owner block)
      (quittingMeshHazardCoin (p block) m (hp0 block) (hp1 block)) who true).toReal ≤ ε
    by_cases hwho : who = owner block
    · subst who
      rw [quittingSoloStationaryRoot_apply_owner, quittingMeshHazardCoin_true_toReal]
      exact (quittingMeshHazard_le_intensityBound_div p hp1 ha block).trans hhazard.le
    · rw [quittingSoloStationaryRoot_apply_other hwho]
      simpa using hε.le
  · obtain ⟨hnash, -⟩ := singletonArcCycle_isTerminalNash_and_hasValue
      reward owner p coarse initial m hm hp0 hp1 ha hD harc hactive
        hcoarseSolo hcollision hcoarseContracts
    exact hnash.mono herror.le

/-- The existing strict right-cycle certificate supplies actual coarse arcs
and a small-hazard terminal approximate equilibrium. -/
theorem of_rightSingletonCycle
    (reward : QuittingReward3) (d : RightSingletonCycle reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  have hp0 : ∀ block, 0 ≤
      ![rightAlpha reward, rightBeta reward, rightGamma reward] block := by
    have hpos := right_rates_pos d
    intro block
    fin_cases block
    · exact hpos.1.le
    · exact hpos.2.1.le
    · exact hpos.2.2.le
  have hp1 : ∀ block, (![rightAlpha reward, rightBeta reward,
      rightGamma reward] block) < 1 := by
    intro block
    fin_cases block <;> simp [right_rates_lt_one d]
  exact of_singletonArcCycle reward rightOwner
    (![rightAlpha reward, rightBeta reward, rightGamma reward]) (rightCoarse reward) 0
    hp0 hp1 threePlayerCycle_intensity_bound (threePlayerCycleD_nonneg reward)
    (right_coarse_arc d) (right_coarse_active d) (right_coarse_floor d)
    (fun block other hne =>
      threePlayerCycle_collision_bound reward (rightOwner block) other hne)
    (right_coarse_contracts d) hε

/-- The existing strict left-cycle certificate supplies the other oriented
small-hazard terminal approximate equilibrium. -/
theorem of_leftSingletonCycle
    (reward : QuittingReward3) (d : LeftSingletonCycle reward)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  have hp0 : ∀ block, 0 ≤
      ![leftAlpha reward, leftBeta reward, leftGamma reward] block := by
    have hpos := left_rates_pos d
    intro block
    fin_cases block
    · exact hpos.1.le
    · exact hpos.2.1.le
    · exact hpos.2.2.le
  have hp1 : ∀ block, (![leftAlpha reward, leftBeta reward,
      leftGamma reward] block) < 1 := by
    intro block
    fin_cases block <;> simp [left_rates_lt_one d]
  exact of_singletonArcCycle reward leftOwner
    (![leftAlpha reward, leftBeta reward, leftGamma reward]) (leftCoarse reward) 0
    hp0 hp1 threePlayerCycle_intensity_bound (threePlayerCycleD_nonneg reward)
    (left_coarse_arc d) (left_coarse_active d) (left_coarse_floor d)
    (fun block other hne =>
      threePlayerCycle_collision_bound reward (leftOwner block) other hne)
    (left_coarse_contracts d) hε

/-- Every feasible normalized singleton mixture gives the strategy
disjunction. The existing finite alternative retains degenerate supports;
its complementary branch is stationary and its strict cycles have small hazards. -/
theorem of_normalizedFeasibleSingletonMixture
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (weight : Convexity.StdSimplex ℝ (Fin 3))
    (hfeasible : ∀ who, 1 ≤ quittingSingletonMixture reward weight.weights who)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  classical
  let target : Payoff (Fin 3) := fun _ => 1
  let M := singletonExcess (threeSingletonTable reward) target
  have hprobability : ThreeProbability weight.weights :=
    ⟨weight.weights_nonneg, weight.total_of_fintype⟩
  have hfeas : ∀ who, 0 ≤ threeMixed M weight.weights who :=
    threeMixed_singletonExcess_nonneg reward target weight.weights hprobability hfeasible
  have hdiag : ∀ who, M who who = 0 := by
    intro who
    change reward (quittingSingletonTerminal who) who - 1 = 0
    rw [hsolo who]
    ring
  have hmatrix : M = normalizedSoloMatrix reward := by
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    funext who owner
    change reward (quittingSingletonTerminal owner) who - 1 =
      reward (quittingSingletonTerminal owner) who -
        reward (quittingSingletonTerminal who) who
    rw [hsolo who]
  cases three_singleton_source_alternative M weight.weights hprobability hfeas
      (fun who _ => hdiag who) with
  | complementary c =>
      let selected : Convexity.StdSimplex ℝ (Fin 3) :=
        { weights := Finsupp.equivFunOnFinite.symm c.mass
          nonneg := by
            intro who
            change 0 ≤ c.mass who
            exact c.probability.nonneg who
          total := by
            rw [Finsupp.equivFunOnFinite_symm_sum]
            exact c.probability.total }
      have hresidual (who : Fin 3) : _root_.Math.LinearProgramming.singletonLCPResidual
          (normalizedSoloMatrix reward) selected who = threeMixed M c.mass who := by
        conv_lhs => rw [← hmatrix]
        simp [selected, _root_.Math.LinearProgramming.singletonLCPResidual,
          wsum, dotProduct, threeMixed, mul_comm]
      exact of_normalizedHomogeneousWitness reward hsolo selected
        (fun who => by rw [hresidual who]; exact c.feasible who)
        (fun who => by
          rw [hresidual who]
          simpa [selected] using c.complementary who) hε
  | right c =>
      exact of_rightSingletonCycle reward (rightCycle_of_excess reward target c) hε
  | left c =>
      exact of_leftSingletonCycle reward (leftCycle_of_excess reward target c) hε

/-- Normalizing the positive singleton mass of an original-game projective
packet gives a feasible mixture when all own-singleton rewards are one. -/
private theorem feasibleSingletonMixture_of_normalizedProjectivePacket
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (packet : QuittingProjectiveSingletonPacket reward) :
    ∃ weight : Convexity.StdSimplex ℝ (Fin 3),
      ∀ who, 1 ≤ quittingSingletonMixture reward weight.weights who := by
  classical
  let s := ∑ who, packet.singleton who
  have hs : 0 < s := by
    by_contra hnot
    have hzero : ∀ who, packet.singleton who = 0 := by
      intro who
      have hle : packet.singleton who ≤ s :=
        Finset.single_le_sum (fun other _ => packet.singleton_nonneg other)
          (Finset.mem_univ who)
      exact le_antisymm (hle.trans (not_lt.mp hnot)) (packet.singleton_nonneg who)
    have hfloor := packet.solo_le_value 0
    rw [packet.value_eq_singleton_mix] at hfloor
    simp only [quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal,
      hsolo, hzero, zero_mul, Finset.sum_const_zero] at hfloor
    norm_num at hfloor
  have hs1 : s ≤ 1 := by
    have htotal := packet.total
    have hc := packet.cemetery_nonneg
    change packet.cemetery + s = 1 at htotal
    linarith
  let weight : Convexity.StdSimplex ℝ (Fin 3) :=
    { weights := Finsupp.equivFunOnFinite.symm (fun who => packet.singleton who / s)
      nonneg := by
        intro who
        simpa using div_nonneg (packet.singleton_nonneg who) hs.le
      total := by
        rw [Finsupp.equivFunOnFinite_symm_sum, ← Finset.sum_div]
        exact div_self hs.ne' }
  refine ⟨weight, ?_⟩
  intro who
  have hfloor : 1 ≤ packet.value who := by
    simpa only [quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal,
      hsolo] using packet.solo_le_value who
  have hmix : quittingSingletonMixture reward weight.weights who = packet.value who / s := by
    rw [packet.value_eq_singleton_mix]
    unfold quittingSingletonMixture
    simp only [weight, Finsupp.equivFunOnFinite_symm_apply_apply,
      quittingProjectiveSingletonTerminal_eq_quittingSingletonTerminal]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [hmix]
  exact (le_div_iff₀ hs).2 (by linarith)

/-- Infeasible normalized singleton mixtures force an exact stationary terminal
Nash root through the original-game analytic endpoint and its solo boundary. -/
theorem exists_exactStationaryTerminalNash_of_normalizedInfeasibleMixture
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    (hinfeasible : ¬ ∃ weight : Convexity.StdSimplex ℝ (Fin 3),
      ∀ who, 1 ≤ quittingSingletonMixture reward weight.weights who) :
    ∃ root : Fin 3 → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) := by
  classical
  obtain ⟨g⟩ := nonempty_analyticBellmanGerm_quittingGame reward
  have habsorbs : quittingStationaryContinueMass (g.endpointProfile none) < 1 := by
    by_contra hnot
    have hcontinue := le_antisymm
      (quittingStationaryContinueMass_le_one (g.endpointProfile none)) (not_lt.mp hnot)
    rcases quittingGerm_allContinue_zeroSolo_or_projectivePacket reward g hcontinue with
      hzero | hpacket
    · have hbad := hzero 0
      change reward (quittingSingletonTerminal 0) 0 ≤ 0 at hbad
      rw [hsolo 0] at hbad
      norm_num at hbad
    · exact hinfeasible
        (feasibleSingletonMixture_of_normalizedProjectivePacket reward hsolo hpacket.some)
  have hfixed := quittingGerm_endpoint_fixedPoint g
  have hnash := quittingGerm_endpoint_endpointNash g
  refine ⟨g.endpointProfile none,
    (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
      reward (g.endpointProfile none) (quittingGermValue g 0) habsorbs hfixed hnash).mpr ?_⟩
  intro who hmass
  have hroot := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (quittingGermValue g 0) (g.endpointProfile none)).mp hnash
  have hquit := (quittingStationaryEndpointBounds_of_fixedPoint_rootNash
    reward (g.endpointProfile none) (quittingGermValue g 0) hfixed hroot who).1
  rw [quittingStationaryFixedOpponentsQuitValue_eq_solo_of_mass_eq_one
    reward (g.endpointProfile none) who hmass, hsolo who] at hquit
  rw [hsolo who]
  exact max_le (by linarith) hquit

/-- The complete normalized positive-own-singleton three-player strategy
disjunction, assembled from existing stationary and cyclic root producers. -/
theorem of_normalizedThreePlayer
    (reward : QuittingReward3)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who = 1)
    {ε : ℝ} (hε : 0 < ε) : StationaryOrSmallHazardTerminalEquilibrium reward ε := by
  by_cases hfeasible : ∃ weight : Convexity.StdSimplex ℝ (Fin 3),
      ∀ who, 1 ≤ quittingSingletonMixture reward weight.weights who
  · obtain ⟨weight, hweight⟩ := hfeasible
    exact of_normalizedFeasibleSingletonMixture reward hsolo weight hweight hε
  · obtain ⟨root, hnash⟩ :=
      exists_exactStationaryTerminalNash_of_normalizedInfeasibleMixture reward hsolo hfeasible
    exact Or.inl ⟨root, hnash.mono hε.le⟩

end GameTheory.QuittingThreePlayerStrategyClass
