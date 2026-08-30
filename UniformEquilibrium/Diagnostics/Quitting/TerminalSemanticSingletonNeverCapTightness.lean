/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailProfileAdapter
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import MathUE.Probability.KakutaniProductDichotomy

/-!
# Singleton/Never terminal-law cap tightness

For an actual behavioral profile, the limiting joint live mass is the product
of its players' marginal Never masses.  The event that one player stops
finitely while every opponent Never stops is contained in that player's
terminal singleton event.  This gives the one-sided singleton cylinder used
below; equality is deliberately not claimed.

The resulting finite-stopping union bounds control immediate-Quit and Never
deviations quantitatively.  Applied to one common sequence realizing a joint
terminal semantic/law carrier point, these bounds show that positive support
on one singleton and Never, together with zero owner debt, makes the owner's
unrestricted cap equal to the singleton reward.

This module neither constructs such a carrier point nor supplies a strict
minimum classification, a Fin4 source, a behavioral realization of the
limit point, or a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Product of all opponents' marginal Never masses. -/
def quittingBehaviorOpponentNeverProduct
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) : ℝ :=
  ∏ other ∈ Finset.univ.erase owner,
    quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile other))

/-- Total finite-stopping mass of one behavioral hazard. -/
def quittingBehaviorFiniteStoppingMass
    (profile : (quittingGame reward).BehaviorProfile) (player : ι) : ℝ :=
  1 - quittingHazardNeverMass
    (quittingBehaviorLiveHazard reward (profile player))

omit [DecidableEq ι] in
/-- The limiting joint live mass is the product of the marginal Never masses. -/
theorem quittingLiveMassLimit_eq_prod_hazardNeverMass
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingLiveMassLimit reward profile =
      ∏ player, quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward (profile player)) := by
  let roots := quittingProfileLiveRoot reward profile
  have hfinite : ∀ cutoff,
      quittingLiveMass reward profile cutoff =
        ∏ player, quittingHazardSurvival
          (fun stage => roots stage player) cutoff := by
    intro cutoff
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
    rw [quittingJointSurvivalWeight_eq_prod]
    simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro player _
    rw [quittingHazardSurvival_eq_prod]
    simp [roots]
  have hlimit : Tendsto (fun cutoff =>
      ∏ player, quittingHazardSurvival
        (fun stage => roots stage player) cutoff) atTop
      (nhds (∏ player, quittingHazardNeverMass
        (fun stage => roots stage player))) :=
    tendsto_finsetProd Finset.univ fun player _ =>
      tendsto_quittingHazardSurvival_neverMass
        (fun stage => roots stage player)
  have hlive := tendsto_quittingLiveMass reward profile
  have hfiniteFunction : quittingLiveMass reward profile = fun cutoff =>
      ∏ player, quittingHazardSurvival
        (fun stage => roots stage player) cutoff := by
    funext cutoff
    exact hfinite cutoff
  rw [hfiniteFunction] at hlive
  have heq := tendsto_nhds_unique hlive hlimit
  refine heq.trans ?_
  apply Finset.prod_congr rfl
  intro player _
  congr 1

/-- The event that `owner` stops finitely and every opponent Never stops is
contained in the terminal singleton event. -/
theorem one_sub_neverMass_mul_opponentNeverProduct_le_singletonOutcomeMass
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) :
    (1 - quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward (profile owner))) *
        quittingBehaviorOpponentNeverProduct profile owner ≤
      quittingTerminalOutcomeMass reward profile
        (some (quittingSingletonTerminal owner)) := by
  let ownerHazard := quittingBehaviorLiveHazard reward (profile owner)
  let opponentNever := quittingBehaviorOpponentNeverProduct profile owner
  have hstage (time : ℕ) :
      quittingHazardStopMass ownerHazard time * opponentNever ≤
        quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal owner) := by
    have hfactor :=
      quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct
        profile time (quittingSingletonTerminal owner)
    have htail : opponentNever ≤
        ∏ other ∈ (quittingSingletonTerminal owner).valᶜ,
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward (profile other)) (time + 1) := by
      have hcompl : ({owner} : Finset ι)ᶜ =
          (Finset.univ : Finset ι).erase owner := by
        ext other
        simp
      simpa [opponentNever, quittingBehaviorOpponentNeverProduct,
        quittingSingletonTerminal, hcompl] using
        (Finset.prod_le_prod
          (s := (Finset.univ : Finset ι).erase owner)
          (fun other _ => quittingHazardNeverMass_nonneg
            (quittingBehaviorLiveHazard reward (profile other)))
          (fun other _ => quittingHazardNeverMass_le_survival
            (quittingBehaviorLiveHazard reward (profile other)) (time + 1)))
    have hstop : 0 ≤ quittingHazardStopMass ownerHazard time :=
      quittingHazardStopMass_nonneg ownerHazard time
    rw [hfactor]
    simpa [ownerHazard, opponentNever, quittingBehaviorOpponentNeverProduct,
      quittingSingletonTerminal] using
        (mul_le_mul_of_nonneg_left htail hstop)
  have hleft : HasSum
      (fun time => quittingHazardStopMass ownerHazard time * opponentNever)
      ((1 - quittingHazardNeverMass ownerHazard) * opponentNever) :=
    (hasSum_quittingHazardStopMass ownerHazard).mul_right opponentNever
  have hright := hasSum_quittingStageCoalitionMass reward profile
    (quittingSingletonTerminal owner)
  have hle : (∑' time,
      quittingHazardStopMass ownerHazard time * opponentNever) ≤
      ∑' time, quittingStageCoalitionMass reward profile time
        (quittingSingletonTerminal owner) := by
    exact hleft.summable.tsum_le_tsum hstage hright.summable
  rw [hleft.tsum_eq, hright.tsum_eq] at hle
  simpa [ownerHazard, opponentNever, quittingTerminalOutcomeMass] using hle

omit [Fintype ι] [DecidableEq ι] in
private theorem quittingHazardNeverMass_const_continue :
    quittingHazardNeverMass (fun _ : ℕ => (PMF.pure false : PMF Bool)) = 1 := by
  apply tendsto_nhds_unique
    (tendsto_quittingHazardSurvival_neverMass
      (fun _ : ℕ => (PMF.pure false : PMF Bool)))
  convert (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
  funext cutoff
  simp [quittingHazardSurvival_eq_prod]

/-- The opponents-only terminal live mass is exactly the product of their
marginal Never masses. -/
theorem quittingLiveMassLimit_opponentOnly_eq_opponentNeverProduct
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) :
    quittingLiveMassLimit reward
        (quittingOpponentOnlyProfile reward profile owner) =
      quittingBehaviorOpponentNeverProduct profile owner := by
  rw [quittingLiveMassLimit_eq_prod_hazardNeverMass]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun player => quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward
        (quittingOpponentOnlyProfile reward profile owner player)))
    (Finset.mem_univ owner)]
  have howner : quittingBehaviorLiveHazard reward
      (quittingOpponentOnlyProfile reward profile owner owner) =
        fun _ : ℕ => (PMF.pure false : PMF Bool) := by
    funext time
    simp [quittingOpponentOnlyProfile, quittingBehaviorLiveHazard,
      quittingAlwaysContinueStrategy]
    rfl
  rw [howner, quittingHazardNeverMass_const_continue, one_mul]
  unfold quittingBehaviorOpponentNeverProduct
  apply Finset.prod_congr rfl
  intro other hother
  congr 1
  funext time
  simp [quittingOpponentOnlyProfile, quittingBehaviorLiveHazard,
    Finset.ne_of_mem_erase hother]

omit [DecidableEq ι] in
theorem quittingBehaviorFiniteStoppingMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile) (player : ι) :
    0 ≤ quittingBehaviorFiniteStoppingMass profile player := by
  unfold quittingBehaviorFiniteStoppingMass
  have hle := quittingHazardNeverMass_le_survival
    (quittingBehaviorLiveHazard reward (profile player)) 0
  simp at hle
  linarith

omit [DecidableEq ι] in
theorem quittingBehaviorFiniteStoppingMass_le_one
    (profile : (quittingGame reward).BehaviorProfile) (player : ι) :
    quittingBehaviorFiniteStoppingMass profile player ≤ 1 := by
  unfold quittingBehaviorFiniteStoppingMass
  linarith [quittingHazardNeverMass_nonneg
    (quittingBehaviorLiveHazard reward (profile player))]

/-- The first-row opponent-absorption probability is bounded by the sum of
the opponents' total finite-stopping masses. -/
theorem quittingRootOpponentAbsorptionMass_profileLiveRoot_le_sum_finiteStoppingMass
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) :
    quittingRootOpponentAbsorptionMass
        (quittingProfileLiveRoot reward profile 0) owner ≤
      ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass profile other := by
  let opponents := (Finset.univ : Finset ι).erase owner
  let never := fun other => quittingHazardNeverMass
    (quittingBehaviorLiveHazard reward (profile other))
  have hneverContinue : ∀ other ∈ opponents,
      never other ≤
        (quittingProfileLiveRoot reward profile 0 other false).toReal := by
    intro other _
    have hle := quittingHazardNeverMass_le_survival
      (quittingBehaviorLiveHazard reward (profile other)) 1
    simpa [never, quittingHazardSurvival_eq_prod,
      quittingBehaviorLiveHazard, quittingProfileLiveRoot] using hle
  have hprod : (∏ other ∈ opponents, never other) ≤
      ∏ other ∈ opponents,
        (quittingProfileLiveRoot reward profile 0 other false).toReal := by
    exact Finset.prod_le_prod
      (fun other _ => quittingHazardNeverMass_nonneg _)
      hneverContinue
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  have hcontinueProduct :
      (∏ other ∈ opponents,
          (1 - (quittingProfileLiveRoot reward profile 0 other true).toReal)) =
        ∏ other ∈ opponents,
          (quittingProfileLiveRoot reward profile 0 other false).toReal := by
    apply Finset.prod_congr rfl
    intro other _
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (quittingProfileLiveRoot reward profile 0) other
    linarith
  rw [hcontinueProduct]
  calc
    1 - ∏ other ∈ opponents,
          (quittingProfileLiveRoot reward profile 0 other false).toReal ≤
        1 - ∏ other ∈ opponents, never other := by linarith
    _ ≤ ∑ other ∈ opponents, (1 - never other) := by
      exact Math.Probability.KakutaniProductDichotomy.one_sub_prod_le_sum_one_sub
        opponents never
        (fun other _ => quittingHazardNeverMass_nonneg _)
        (fun other _ => by
          have hle := quittingHazardNeverMass_le_survival
            (quittingBehaviorLiveHazard reward (profile other)) 0
          simpa [never] using hle)
    _ = ∑ other ∈ Finset.univ.erase owner,
          quittingBehaviorFiniteStoppingMass profile other := by
      apply Finset.sum_congr rfl
      intro other _
      rfl

/-- Immediate Quit differs from the owner's singleton reward by at most the
finite-stopping union bound of the opponents. -/
theorem abs_quittingTerminalPayoff_update_quitNow_sub_singleton_le
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) :
    |quittingTerminalPayoff reward
          (Function.update profile owner
            (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner -
        reward (quittingSingletonTerminal owner) owner| ≤
      2 * quittingRewardBound reward *
        ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass profile other := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
    ]
  exact (abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
      (quittingProfileLiveRoot reward profile 0) owner
      (abs_reward_le_quittingRewardBound reward)).trans
    (mul_le_mul_of_nonneg_left
      (quittingRootOpponentAbsorptionMass_profileLiveRoot_le_sum_finiteStoppingMass
        profile owner)
      (mul_nonneg (by norm_num) (quittingRewardBound_nonneg reward)))

/-- Never earns only on the opponents' finite-stopping union. -/
theorem abs_quittingTerminalPayoff_update_never_le_sum_finiteStoppingMass
    (profile : (quittingGame reward).BehaviorProfile) (owner : ι) :
    |quittingTerminalPayoff reward
        (Function.update profile owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner| ≤
      quittingRewardBound reward *
        ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass profile other := by
  have hbound := abs_quittingTerminalPayoff_update_never_le_opponentTail
    reward profile owner (abs_reward_le_quittingRewardBound reward)
  rw [quittingLiveMassLimit_opponentOnly_eq_opponentNeverProduct] at hbound
  have hunion : 1 - quittingBehaviorOpponentNeverProduct profile owner ≤
      ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass profile other := by
    exact Math.Probability.KakutaniProductDichotomy.one_sub_prod_le_sum_one_sub
      ((Finset.univ : Finset ι).erase owner)
      (fun other => quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward (profile other)))
      (fun other _ => quittingHazardNeverMass_nonneg _)
      (fun other _ => by
        have hle := quittingHazardNeverMass_le_survival
          (quittingBehaviorLiveHazard reward (profile other)) 0
        simpa using hle)
  exact hbound.trans
    (mul_le_mul_of_nonneg_left hunion (quittingRewardBound_nonneg reward))

/-- A singleton/Never outcome law has the displayed singleton reward moment. -/
theorem quittingTerminalRewardMoment_singletonNever
    (mass : QuittingTerminalOutcome ι → ℝ) (owner : ι) (p : ℝ)
    (hfinite : ∀ terminal : {S : Finset ι // S.Nonempty},
      mass (some terminal) = if terminal.val = {owner} then p else 0) :
    quittingTerminalRewardMoment reward mass =
      fun player => p * reward (quittingSingletonTerminal owner) player := by
  funext player
  unfold quittingTerminalRewardMoment
  rw [Fintype.sum_option]
  simp only [quittingTerminalOutcomeReward]
  simp_rw [hfinite]
  have hpredicate : ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal.val = {owner} ↔
        terminal = quittingSingletonTerminal owner := by
    intro terminal
    constructor
    · exact fun heq => Subtype.ext heq
    · exact fun heq => congrArg Subtype.val heq
  simp_rw [hpredicate]
  simp

/-- A joint carrier point supported on one singleton and Never, with positive
singleton mass and zero owner debt, has owner cap equal to the singleton
reward. -/
theorem terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (owner : ι) (p : ℝ) (hp : 0 < p)
    (hfinite : ∀ terminal : {S : Finset ι // S.Nonempty},
      point.2 (some terminal) =
        if terminal.val = {owner} then p else 0)
    (hnever : point.2 none = 1 - p)
    (hdebt : quittingTerminalSemanticDebt point.1 owner = 0) :
    point.1.2 owner = reward (quittingSingletonTerminal owner) owner := by
  letI : Nonempty ι := ⟨owner⟩
  rw [quittingTerminalSemanticLawCarrier, mem_closure_iff_seq_limit] at hpoint
  obtain ⟨points, hpoints, hpointsTendsto⟩ := hpoint
  choose profiles hprofiles using hpoints
  have hprofilesTendsto : Tendsto (fun n =>
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds point) := by
    simpa only [hprofiles] using hpointsTendsto
  have hsemantic : Tendsto (fun n =>
      quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    (continuous_fst.tendsto point).comp hprofilesTendsto
  have hmass : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward (profiles n))
      atTop (nhds point.2) :=
    (continuous_snd.tendsto point).comp hprofilesTendsto
  have hcap : Tendsto (fun n =>
      (quittingTerminalSemanticPair reward (profiles n)).2 owner)
      atTop (nhds (point.1.2 owner)) :=
    (((continuous_apply owner).comp continuous_snd).tendsto point.1).comp
      hsemantic
  have hmassCoordinate (outcome : QuittingTerminalOutcome ι) :
      Tendsto (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
        atTop (nhds (point.2 outcome)) :=
    ((continuous_apply outcome).tendsto point.2).comp hmass
  have hprodNever : Tendsto (fun n =>
      ∏ player, quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward (profiles n player)))
      atTop (nhds (1 - p)) := by
    have hnone := hmassCoordinate none
    rw [hnever] at hnone
    simpa [quittingTerminalOutcomeMass,
      quittingLiveMassLimit_eq_prod_hazardNeverMass] using hnone
  have hsingleton (other : ι) (hother : other ≠ owner) :
      Tendsto (fun n => quittingTerminalOutcomeMass reward (profiles n)
        (some (quittingSingletonTerminal other))) atTop (nhds 0) := by
    have hcoordinate := hmassCoordinate (some (quittingSingletonTerminal other))
    simpa [hfinite, quittingSingletonTerminal, hother] using hcoordinate
  have hsumFinite_of_ne (hpone : p ≠ 1) : Tendsto (fun n =>
      ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass (profiles n) other)
      atTop (nhds 0) := by
      have hpLt : p < 1 := by
        have hmassSimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
          (reward := reward) point
          (mem_terminalSemanticLawCarrier_of_joint_tendsto
            reward profiles point hprofilesTendsto)
        have := hmassSimplex.1 none
        rw [hnever] at this
        have hpLe : p ≤ 1 := by linarith
        exact lt_of_le_of_ne hpLe hpone
      let kappa := (1 - p) / 2
      have hkappa : 0 < kappa := by dsimp [kappa]; linarith
      have hopen : ∀ᶠ n in atTop, kappa <
          ∏ player, quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward (profiles n player)) :=
        hprodNever.eventually (Ioi_mem_nhds (by dsimp [kappa]; linarith))
      have hcoordinateZero (other : ι) (hother : other ≠ owner) :
          Tendsto (fun n =>
            quittingBehaviorFiniteStoppingMass (profiles n) other)
            atTop (nhds 0) := by
        have hsingle := hsingleton other hother
        have hupper : ∀ᶠ n in atTop,
            quittingBehaviorFiniteStoppingMass (profiles n) other ≤
              quittingTerminalOutcomeMass reward (profiles n)
                (some (quittingSingletonTerminal other)) / kappa := by
          filter_upwards [hopen] with n hn
          have hfactor :
              (∏ player, quittingHazardNeverMass
                (quittingBehaviorLiveHazard reward (profiles n player))) ≤
                quittingBehaviorOpponentNeverProduct (profiles n) other := by
            rw [← Finset.mul_prod_erase Finset.univ
              (fun player => quittingHazardNeverMass
                (quittingBehaviorLiveHazard reward (profiles n player)))
              (Finset.mem_univ other)]
            have hownerNever := quittingHazardNeverMass_le_survival
              (quittingBehaviorLiveHazard reward (profiles n other)) 0
            have hopponentNonneg : 0 ≤
                quittingBehaviorOpponentNeverProduct (profiles n) other := by
              unfold quittingBehaviorOpponentNeverProduct
              exact Finset.prod_nonneg fun player _ =>
                quittingHazardNeverMass_nonneg
                  (quittingBehaviorLiveHazard reward (profiles n player))
            simpa [quittingBehaviorOpponentNeverProduct] using
              (mul_le_of_le_one_left hopponentNonneg (by simpa using hownerNever))
          have hk : kappa <
              quittingBehaviorOpponentNeverProduct (profiles n) other :=
            hn.trans_le hfactor
          have hcylinder :=
            one_sub_neverMass_mul_opponentNeverProduct_le_singletonOutcomeMass
              (profiles n) other
          change quittingBehaviorFiniteStoppingMass (profiles n) other *
              quittingBehaviorOpponentNeverProduct (profiles n) other ≤ _
            at hcylinder
          apply (le_div_iff₀ hkappa).2
          calc
            quittingBehaviorFiniteStoppingMass (profiles n) other * kappa ≤
                quittingBehaviorFiniteStoppingMass (profiles n) other *
                  quittingBehaviorOpponentNeverProduct (profiles n) other := by
              exact mul_le_mul_of_nonneg_left hk.le
                (quittingBehaviorFiniteStoppingMass_nonneg (profiles n) other)
            _ ≤ _ := hcylinder
        exact squeeze_zero'
          (Eventually.of_forall fun n =>
            quittingBehaviorFiniteStoppingMass_nonneg (profiles n) other)
          hupper (by simpa using hsingle.div_const kappa)
      have hsum := tendsto_finsetSum (Finset.univ.erase owner)
        (fun other hother => hcoordinateZero other (Finset.ne_of_mem_erase hother))
      simpa using hsum
  have hcarrier : point ∈ quittingTerminalSemanticLawCarrier reward := by
    exact mem_terminalSemanticLawCarrier_of_joint_tendsto
      reward profiles point hprofilesTendsto
  have hmoment := terminalSemanticLawCarrier_rewardMoment reward point hcarrier
  rw [quittingTerminalRewardMoment_singletonNever point.2 owner p hfinite]
    at hmoment
  have hpayoff : point.1.1 owner =
      p * reward (quittingSingletonTerminal owner) owner := by
    exact (congrFun hmoment owner).symm
  have hcapFormula : point.1.2 owner =
      p * reward (quittingSingletonTerminal owner) owner := by
    unfold quittingTerminalSemanticDebt at hdebt
    linarith
  by_cases hpone : p = 1
  · rw [hpone, one_mul] at hcapFormula
    exact hcapFormula
  have hpLt : p < 1 := by
    have hmassSimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
      (reward := reward) point hcarrier
    have := hmassSimplex.1 none
    rw [hnever] at this
    have hpLe : p ≤ 1 := by linarith
    exact lt_of_le_of_ne hpLe hpone
  have hsumFinite := hsumFinite_of_ne hpone
  have hquitError : Tendsto (fun n =>
      quittingTerminalPayoff reward
          (Function.update (profiles n) owner
            (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner -
        reward (quittingSingletonTerminal owner) owner) atTop (nhds 0) := by
    apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _
      (fun n => 2 * quittingRewardBound reward *
        ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass (profiles n) other)
    · simpa using hsumFinite.const_mul (2 * quittingRewardBound reward)
    · exact Eventually.of_forall fun n =>
        abs_quittingTerminalPayoff_update_quitNow_sub_singleton_le
          (profiles n) owner
  have hneverPayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward
        (Function.update (profiles n) owner
          (quittingPureTimeBehaviorStrategy reward owner none)) owner)
      atTop (nhds 0) := by
    apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _
      (fun n => quittingRewardBound reward *
        ∑ other ∈ Finset.univ.erase owner,
        quittingBehaviorFiniteStoppingMass (profiles n) other)
    · simpa using hsumFinite.const_mul (quittingRewardBound reward)
    · exact Eventually.of_forall fun n =>
        abs_quittingTerminalPayoff_update_never_le_sum_finiteStoppingMass
          (profiles n) owner
  have hquitLimit : Tendsto (fun n => quittingTerminalPayoff reward
      (Function.update (profiles n) owner
        (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner)
      atTop (nhds (reward (quittingSingletonTerminal owner) owner)) := by
    convert hquitError.add_const
      (reward (quittingSingletonTerminal owner) owner) using 1 <;> simp
  have hquitLe : reward (quittingSingletonTerminal owner) owner ≤
      point.1.2 owner := by
    apply le_of_tendsto_of_tendsto hquitLimit hcap
    exact Eventually.of_forall fun n =>
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (profiles n) owner
        (quittingPureTimeBehaviorStrategy reward owner (some 0))
  have hneverLe : 0 ≤ point.1.2 owner := by
    apply le_of_tendsto_of_tendsto hneverPayoff hcap
    exact Eventually.of_forall fun n =>
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (profiles n) owner
        (quittingPureTimeBehaviorStrategy reward owner none)
  rw [hcapFormula] at hquitLe hneverLe
  have hrewardsNonpos : reward (quittingSingletonTerminal owner) owner ≤ 0 := by
    nlinarith
  have hrewardsNonneg : 0 ≤ reward (quittingSingletonTerminal owner) owner := by
    nlinarith
  have hrewardsZero : reward (quittingSingletonTerminal owner) owner = 0 :=
    le_antisymm hrewardsNonpos hrewardsNonneg
  rw [hcapFormula, hrewardsZero, mul_zero]

end GameTheory
