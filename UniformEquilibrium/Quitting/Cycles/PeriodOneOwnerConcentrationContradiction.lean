/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.NormalCorePunishmentNormal
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination
import UniformEquilibrium.Quitting.Cycles.DiffuseTailSoloStructure
import UniformEquilibrium.Quitting.Cycles.FixedPeriodInteriorCyclicLimit
import UniformEquilibrium.Quitting.Punishment.SoloCycleCompletion

/-!
# Vanishing-hazard sources from one-period interior cyclic blocks

For one-period blocks, the positive-owner alternative has a positive-rate
solo endpoint limit.  In a four-player counterexample every player is
punishment-normal, so the solo-cycle compiler rules out that alternative.
Thus the fixed-debtor escape retains the actual source profiles and has
vanishing total hazard.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingLCPClassification
open ThreeCoreAmbientCarrierElimination

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- A positive-owner concentration subsequence of one-period interior cyclic
blocks contradicts four-player nonexistence of a uniform-equilibrium payoff.
The proof retains the supplied actual blocks and uses their compact solo
endpoint limit; it does not replace them by unrelated stationary roots. -/
theorem false_of_periodOne_ownerConcentration_of_finFour_noUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (error : ℕ → ℝ) (herror : Tendsto error atTop (nhds 0))
    (block : ∀ n, InteriorApproximateNashCyclicBlock reward 0 (error n))
    (initial : ∀ _n, Fin 1) {owner : ι} {debtFloor : ℝ}
    (data : InteriorCyclicOwnerConcentrationSubsequence reward
      (fun _ ↦ 0) error block initial owner debtFloor) : False := by
  let selectedError : ℕ → ℝ := error ∘ data.select
  let selectedBlock : ∀ n,
      InteriorApproximateNashCyclicBlock reward 0 (selectedError n) :=
    fun n ↦ block (data.select n)
  let limit := Classical.choice
    (nonempty_fixedPeriodExactNashCyclicLimit reward selectedError
      selectedBlock owner
      (herror.comp data.select_strictMono.tendsto_atTop)
      data.opponentAbsorption_tendsto_zero)
  let root : ι → PMF Bool :=
    quittingRootOfSimplex (limit.point 0).2
  have hpointPhase : Tendsto
      (fun n ↦ (selectedBlock (limit.select n)).point 0) atTop
      (nhds (limit.point 0)) := by
    exact ((continuous_apply (0 : Fin 1)).tendsto limit.point).comp
      limit.sourcePoint_tendsto
  have hquit : Tendsto (fun n ↦
      ((selectedBlock (limit.select n)).cycle 0 owner true).toReal)
      atTop (nhds ((root owner true).toReal)) := by
    let quitCoordinate : QuittingNashBellmanPoint ι → ℝ :=
      fun point ↦ point.2 owner true
    have hcontinuous : Continuous quitCoordinate := by
      dsimp only [quitCoordinate]
      exact (continuous_apply true).comp
        (continuous_subtype_val.comp
          ((continuous_apply owner).comp continuous_snd))
    have hcoordinate := (hcontinuous.tendsto (limit.point 0)).comp hpointPhase
    change Tendsto (fun n ↦
      ((selectedBlock (limit.select n)).point 0).2 owner true)
      atTop (nhds ((limit.point 0).2 owner true)) at hcoordinate
    rw [quittingRootOfSimplex_apply_toReal]
    simpa only [InteriorApproximateNashCyclicBlock.point,
      quittingSimplexOfRoot,
      Math.ProbabilityMassFunction.coe_stdSimplexEquiv_apply,
      Math.ProbabilityMassFunction.toVector] using hcoordinate
  have hquitFloor : ∀ n, data.absorptionFloor ≤
      ((selectedBlock (limit.select n)).cycle 0 owner true).toReal := by
    intro n
    have hfloor := data.playerAbsorption_floor (limit.select n)
    unfold quittingCyclicPlayerAbsorptionMass at hfloor
    rw [Fin.prod_univ_one] at hfloor
    have hsum := quittingRoot_continueProbability_add_quitProbability
      ((selectedBlock (limit.select n)).cycle 0) owner
    dsimp only [selectedBlock] at hfloor ⊢
    linarith
  have hquitPositive : 0 < (root owner true).toReal := by
    exact data.absorptionFloor_pos.trans_le
      (ge_of_tendsto' hquit hquitFloor)
  have hvalueSource : Tendsto (fun n ↦
      (selectedBlock (limit.select n)).value 0) atTop
      (nhds (limit.point 0).1) := by
    have hvalue := (continuous_fst.tendsto (limit.point 0)).comp hpointPhase
    change Tendsto (fun n ↦
      (selectedBlock (limit.select n)).value 0) atTop
      (nhds (limit.point 0).1) at hvalue
    exact hvalue
  have hvalueSingleton : Tendsto (fun n ↦
      (selectedBlock (limit.select n)).value 0) atTop
      (nhds (quittingSoloReward reward owner)) := by
    have hterminal := data.terminalPayoff_tendsto_singleton.comp
      limit.select_strictMono.tendsto_atTop
    apply hterminal.congr'
    exact Eventually.of_forall fun n ↦ by
      dsimp only [selectedBlock, Function.comp_apply]
      rw [Subsingleton.elim (initial (data.select (limit.select n))) 0]
  have hpointValue : (limit.point 0).1 = quittingSoloReward reward owner :=
    tendsto_nhds_unique hvalueSource hvalueSingleton
  have hsolo : IsQuittingSoloRoot root owner := by
    intro other hne
    exact limit.opponents_continue_sure 0 other hne
  have hroot : root = quittingSoloStationaryRoot owner (root owner) :=
    hsolo.eq_soloStationaryRoot
  have hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner (root owner)) := by
    rw [← hpointValue, ← hroot]
    apply (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (limit.point 0).1 0 root).2
    simpa [root] using limit.rootNash 0
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward hplayers hno
  have hnormal :=
    all_punishmentNormal_of_normalCore_eq_univ reward hcore owner
  have hpunishment : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner := by
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSoloReward, quittingSingletonTerminal] using hnormal
  have huniform :=
    isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR
      reward owner (root owner) hquitPositive hnash hpunishment
  exact hno ⟨quittingSoloReward reward owner, huniform⟩

end GameTheory
