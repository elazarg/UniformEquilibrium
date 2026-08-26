/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.ChargedSoloBlockerRepayment
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.NormalizedCurvatureStrategicDispatch
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitChargeDichotomy
import MathUE.SummableChargeSurvival

/-!
# A paid row carried through one exact punishment-floor port

An attained paid profile whose prescribed payoff dominates the behavioral
punishment floor can be used as the literal suffix of one infinite exact
Nash--Bellman orbit.  The construction prefixes the selected roots to the same
profile before making the existing cumulative-charge versus summable-port
split.  Thus compactness never replaces the paid source.

The floor inequality is an explicit hypothesis.  A paid first-disagreement
row, including one obtained from normalized curvature, does not by itself
imply that inequality.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}

/-- An actual paid profile whose literal prescribed payoff is above the
behavioral punishment floor. -/
structure QuittingPaidRowFloorSafeSource
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota) where
  profile : (quittingGame reward).BehaviorProfile
  observer : iota
  gain : Real
  gain_pos : 0 < gain
  row : QuittingPaidFirstDisagreementRow reward profile observer gain
  punishment_le : forall who,
    quittingPunishmentValue reward who <=
      quittingTerminalPayoff reward profile who

namespace QuittingPaidRowFloorSafeSource

variable (source : QuittingPaidRowFloorSafeSource reward)

/-- The literal prescribed payoff of the paid source. -/
def prescribed : Payoff iota :=
  fun who => quittingTerminalPayoff reward source.profile who

/-- The paid source payoff lies in the canonical compact reward box. -/
theorem prescribed_mem :
    source.prescribed ∈ quittingPunishmentFloorForwardCarrier reward := by
  constructor <;> intro who
  · exact neg_le_of_abs_le
      (abs_quittingTerminalPayoff_le_quittingRewardBound
        reward source.profile who)
  · exact le_of_abs_le
      (abs_quittingTerminalPayoff_le_quittingRewardBound
        reward source.profile who)

end QuittingPaidRowFloorSafeSource

/-- One exact punishment-floor orbit together with literal behavioral
profiles obtained by repeatedly prefixing its displayed roots to the original
paid profile.  The source row remains available unchanged as `source.row`. -/
structure QuittingPaidRowMarkedExactOrbit
    (source : QuittingPaidRowFloorSafeSource reward) where
  orbit : QuittingPunishmentFloorInfiniteOrbit reward
  profiles : Nat -> (quittingGame reward).BehaviorProfile
  profiles_zero : profiles 0 = source.profile
  profiles_succ : forall time,
    profiles (time + 1) = quittingRootThenContinuationProfile reward
      (orbit.roots time) (profiles time)
  payoff_eq_value : forall time who,
    quittingTerminalPayoff reward (profiles time) who = orbit.value time who

namespace QuittingPaidRowMarkedExactOrbit

variable {source : QuittingPaidRowFloorSafeSource reward}

private def prefixedProfiles
    (source : QuittingPaidRowFloorSafeSource reward)
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward) :
    Nat -> (quittingGame reward).BehaviorProfile
  | 0 => source.profile
  | time + 1 => quittingRootThenContinuationProfile reward
      (orbit.roots time) (prefixedProfiles source orbit time)

/-- Construct one literal marked orbit before making any compactness or
summability choice. -/
theorem nonempty_of_floorSafe
    (source : QuittingPaidRowFloorSafeSource reward) :
    Nonempty (QuittingPaidRowMarkedExactOrbit source) := by
  obtain ⟨initialRoot, hinitialRoot⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) source.prescribed
  obtain ⟨orbit, horbitValue, _horbitRoot⟩ :=
    exists_quittingPunishmentFloorInfiniteOrbit_anchored
      source.prescribed initialRoot source.prescribed_mem
      source.punishment_le hinitialRoot
  let profiles := prefixedProfiles source orbit
  have hpayoff : forall time who,
      quittingTerminalPayoff reward (profiles time) who = orbit.value time who := by
    intro time
    induction time with
    | zero =>
        intro who
        simpa [profiles, prefixedProfiles, QuittingPaidRowFloorSafeSource.prescribed]
          using congrFun horbitValue.symm who
    | succ time ih =>
        intro who
        rw [show profiles (time + 1) =
          quittingRootThenContinuationProfile reward (orbit.roots time)
            (profiles time) by rfl]
        rw [quittingTerminalPayoff_rootThenContinuation_eq]
        have htail : (fun player =>
            quittingTerminalPayoff reward (profiles time) player) =
            orbit.value time := by
          funext player
          exact ih player
        rw [htail]
        exact congrFun (orbit.policy time).symm who
  exact ⟨{
    orbit := orbit
    profiles := profiles
    profiles_zero := rfl
    profiles_succ := fun _ => rfl
    payoff_eq_value := hpayoff }⟩

/-- Literal payoff-prefixing identifies the semantic pair of every successor
profile with the finite-dimensional prefix action. -/
theorem semanticPair_succ_eq (marked : QuittingPaidRowMarkedExactOrbit source)
    (time : Nat) :
    quittingTerminalSemanticPair reward (marked.profiles (time + 1)) =
      quittingTerminalSemanticPrefix reward (marked.orbit.roots time)
        (quittingTerminalSemanticPair reward (marked.profiles time)) := by
  rw [marked.profiles_succ]
  exact quittingTerminalSemanticPair_rootThenContinuation
    reward (marked.orbit.roots time) (marked.profiles time)

/-- Probability of surviving all roots prefixed before the original paid
suffix at a finite marked-orbit horizon. -/
def paidSuffixReach (marked : QuittingPaidRowMarkedExactOrbit source)
    (horizon : Nat) : Real :=
  ∏ time ∈ Finset.range horizon,
    quittingStationaryContinueMass (marked.orbit.roots time)

theorem paidSuffixReach_eq_prod_one_sub_absorption
    (marked : QuittingPaidRowMarkedExactOrbit source) (horizon : Nat) :
    marked.paidSuffixReach horizon =
      ∏ time ∈ Finset.range horizon,
        (1 - quittingRootAbsorptionMass (marked.orbit.roots time)) := by
  apply Finset.prod_congr rfl
  intro time _
  unfold quittingRootAbsorptionMass
  ring

/-- Every literal semantic debt coordinate decreases along the marked
prefixing orbit. -/
theorem debt_antitone (marked : QuittingPaidRowMarkedExactOrbit source)
    (who : iota) :
    Antitone (fun time => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (marked.profiles time)) who) := by
  apply antitone_nat_of_succ_le
  intro time
  rw [marked.semanticPair_succ_eq]
  apply quittingTerminalSemanticDebt_prefix_le
  · exact quittingTerminalDeviationDebt_nonneg
      reward (marked.profiles time) who
  · convert marked.orbit.exactNash time using 1
    funext player
    exact marked.payoff_eq_value time player

/-- On the nonsummable arm, arbitrary cumulative charge and arbitrary payoff
accuracy occur between two visits of this same literal marked orbit. -/
theorem exists_close_payoff_pair_of_not_summable_absorption
    (marked : QuittingPaidRowMarkedExactOrbit source)
    (hdiverges : ¬Summable (fun time =>
      quittingRootAbsorptionMass (marked.orbit.roots time)))
    {chargeTarget payoffError : Real}
    (hpayoffError : 0 < payoffError) :
    exists first second : Nat,
      first < second ∧
      chargeTarget <=
        (∑ time ∈ Finset.range second,
          quittingRootAbsorptionMass (marked.orbit.roots time)) -
        ∑ time ∈ Finset.range first,
          quittingRootAbsorptionMass (marked.orbit.roots time) ∧
      forall who,
        abs (marked.orbit.value second who - marked.orbit.value first who) <
          payoffError := by
  obtain ⟨first, second, hfirstSecond, hclose, hcharge⟩ :=
    Math.exists_close_pair_with_large_charge_gap_of_compact
      (quittingPunishmentFloorForwardCarrier reward)
      (quittingPunishmentFloorForwardCarrier_isCompact reward)
      marked.orbit.value marked.orbit.value_mem
      (fun time => quittingRootAbsorptionMass (marked.orbit.roots time))
      (fun time => marked.orbit.absorptionMass_nonneg time) hdiverges
      payoffError chargeTarget hpayoffError
  refine ⟨first, second, hfirstSecond, hcharge, ?_⟩
  intro who
  have hcoordinate := lt_of_le_of_lt
    (dist_le_pi_dist (marked.orbit.value first)
      (marked.orbit.value second) who) hclose
  simpa [Real.dist_eq, abs_sub_comm] using hcoordinate

/-- The semantic limit attached to a summable marked orbit.  Its prescribed
coordinate is the Bellman value limit; its envelope retains the monotone
limit of the literal all-behavior debt. -/
structure SummableSemanticPort (marked : QuittingPaidRowMarkedExactOrbit source)
    (port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
      marked.orbit) where
  limit : QuittingTerminalSemanticPair iota
  prescribed_eq : limit.1 = port.limit
  semantic_tendsto : Tendsto
    (fun time => quittingTerminalSemanticPair reward (marked.profiles time))
    atTop (nhds limit)
  limit_mem : limit ∈ quittingTerminalSemanticCarrier reward
  selfLoop : quittingTerminalSemanticPrefix reward quittingAllContinueRoot limit =
    limit

/-- Positive limiting probability of reaching the unchanged paid suffix
through every finite marked prefix. -/
structure PositivePaidSuffixReach
    (marked : QuittingPaidRowMarkedExactOrbit source) where
  limit : Real
  limit_pos : 0 < limit
  reach_tendsto : Tendsto marked.paidSuffixReach atTop (nhds limit)

/-- Summable charge gives a literal terminal-semantic all-Continue port for
the same marked profile sequence. -/
theorem nonempty_summableSemanticPort
    (marked : QuittingPaidRowMarkedExactOrbit source)
    (port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
      marked.orbit) :
    Nonempty (SummableSemanticPort marked port) := by
  let debt : Nat -> iota -> Real := fun time who =>
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (marked.profiles time)) who
  let debtLimit : iota -> Real := fun who => sInf (Set.range (fun time => debt time who))
  have hdebtNonneg : forall time who, 0 <= debt time who := by
    intro time who
    exact quittingTerminalDeviationDebt_nonneg reward (marked.profiles time) who
  have hdebtTendsto : forall who,
      Tendsto (fun time => debt time who) atTop (nhds (debtLimit who)) := by
    intro who
    apply tendsto_atTop_ciInf
    · exact marked.debt_antitone who
    · exact ⟨0, by
        rintro value ⟨time, rfl⟩
        exact hdebtNonneg time who⟩
  have hdebtLimitNonneg : forall who, 0 <= debtLimit who := by
    intro who
    exact ge_of_tendsto' (hdebtTendsto who) (fun time => hdebtNonneg time who)
  let semanticLimit : QuittingTerminalSemanticPair iota :=
    (port.limit, fun who => port.limit who + debtLimit who)
  have hsemantic : Tendsto
      (fun time => quittingTerminalSemanticPair reward (marked.profiles time))
      atTop (nhds semanticLimit) := by
    apply (Prod.tendsto_iff _ _).2
    constructor
    · apply tendsto_pi_nhds.2
      intro who
      apply (port.value_tendsto who).congr'
      filter_upwards [] with time
      exact (marked.payoff_eq_value time who).symm
    · apply tendsto_pi_nhds.2
      intro who
      have hadd := (port.value_tendsto who).add (hdebtTendsto who)
      apply hadd.congr'
      filter_upwards [] with time
      rw [← marked.payoff_eq_value time who]
      simp only [debt, quittingTerminalSemanticDebt,
        quittingTerminalSemanticPair]
      ring
  have hmem : semanticLimit ∈ quittingTerminalSemanticCarrier reward := by
    apply isClosed_closure.mem_of_tendsto hsemantic
    filter_upwards [] with time
    apply subset_closure
    exact ⟨marked.profiles time, rfl⟩
  have hfixed : quittingTerminalSemanticPrefix reward quittingAllContinueRoot
      semanticLimit = semanticLimit := by
    apply quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
    intro who
    exact (port.singleton_le who).trans
      (le_add_of_nonneg_right (hdebtLimitNonneg who))
  exact ⟨{
    limit := semanticLimit
    prescribed_eq := rfl
    semantic_tendsto := hsemantic
    limit_mem := hmem
    selfLoop := hfixed }⟩

/-- A terminal-gap witness makes every selected exact floor root strictly
surviving. -/
theorem absorptionMass_lt_one_of_terminalWitness
    (marked : QuittingPaidRowMarkedExactOrbit source)
    (witness : QuittingTerminalExploitabilityWitness reward) (time : Nat) :
    quittingRootAbsorptionMass (marked.orbit.roots time) < 1 := by
  letI : Nonempty iota := witness.nonempty_players
  have hboundPos : 0 < quittingRewardBound reward := by
    have hgapBound := terminalExploitabilityGap_le_two_mul_bound
      reward (abs_reward_le_quittingRewardBound reward)
        witness.terminalExploitability
    linarith [witness.terminalGap_pos]
  have hcontinueEach : forall who,
      0 < (marked.orbit.roots time who false).toReal := by
    intro who
    have hquitLt := witness.exactFloorRoot_quitProbability_lt_one
      (marked.orbit.value time) (marked.orbit.roots time) who hboundPos
      (abs_reward_le_quittingRewardBound reward)
      (marked.orbit.abs_value_le_quittingRewardBound time)
      (marked.orbit.punishmentValue_le_value time)
      (marked.orbit.exactNash time)
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (marked.orbit.roots time) who
    linarith
  have hcontinueMass :
      0 < quittingStationaryContinueMass (marked.orbit.roots time) := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    exact Finset.prod_pos fun who _ => hcontinueEach who
  unfold quittingRootAbsorptionMass
  linarith

/-- Under a terminal-gap witness, the unchanged paid suffix is reached with
positive probability through every finite prefix. -/
theorem paidSuffixReach_pos_of_terminalWitness
    (marked : QuittingPaidRowMarkedExactOrbit source)
    (witness : QuittingTerminalExploitabilityWitness reward) (horizon : Nat) :
    0 < marked.paidSuffixReach horizon := by
  rw [marked.paidSuffixReach_eq_prod_one_sub_absorption]
  exact Finset.prod_pos fun time _ =>
    sub_pos.mpr (marked.absorptionMass_lt_one_of_terminalWitness witness time)

/-- Under a terminal exploitability witness, all selected exact floor roots
have strict one-stage survival.  Summable absorption therefore leaves the
original paid suffix with positive limiting reach. -/
theorem nonempty_positivePaidSuffixReach_of_terminalWitness
    (marked : QuittingPaidRowMarkedExactOrbit source)
    (port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
      marked.orbit)
    (witness : QuittingTerminalExploitabilityWitness reward) :
    Nonempty (PositivePaidSuffixReach marked) := by
  have habsorptionLtOne : forall time,
      quittingRootAbsorptionMass (marked.orbit.roots time) < 1 := by
    exact fun time => marked.absorptionMass_lt_one_of_terminalWitness witness time
  obtain ⟨lower, hlowerPos, hlower⟩ :=
    Math.exists_pos_le_prod_one_sub_of_summable
      (fun time => quittingRootAbsorptionMass (marked.orbit.roots time))
      (fun time => marked.orbit.absorptionMass_nonneg time)
      habsorptionLtOne port.absorption_summable
  have hlowerReach : forall horizon,
      lower <= marked.paidSuffixReach horizon := by
    intro horizon
    rw [marked.paidSuffixReach_eq_prod_one_sub_absorption]
    exact hlower horizon
  have hreachAntitone : Antitone marked.paidSuffixReach := by
    apply antitone_nat_of_succ_le
    intro horizon
    rw [paidSuffixReach, Finset.prod_range_succ]
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun time _ =>
        quittingStationaryContinueMass_nonneg (marked.orbit.roots time))
      (quittingStationaryContinueMass_le_one (marked.orbit.roots horizon))
  let reachLimit := sInf (Set.range marked.paidSuffixReach)
  have hreachTendsto : Tendsto marked.paidSuffixReach atTop
      (nhds reachLimit) := by
    apply tendsto_atTop_ciInf hreachAntitone
    exact ⟨lower, by
      rintro value ⟨horizon, rfl⟩
      exact hlowerReach horizon⟩
  have hreachLimitPos : 0 < reachLimit := by
    have hlowerLimit : lower <= reachLimit :=
      ge_of_tendsto' hreachTendsto hlowerReach
    exact hlowerPos.trans_le hlowerLimit
  exact ⟨{
    limit := reachLimit
    limit_pos := hreachLimitPos
    reach_tendsto := hreachTendsto }⟩

/-- The existing exact charge dichotomy applies to the single marked orbit;
the left arm is already consumed into a uniform-equilibrium payoff. -/
theorem uniformPayoff_or_summableChargeAllContinuePort
    (marked : QuittingPaidRowMarkedExactOrbit source) :
    (exists payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty
        (QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
          marked.orbit) :=
  marked.orbit.uniformPayoff_or_summableChargeAllContinuePort

/-- Complete one-orbit alternative with the literal semantic port retained in
the summable arm. -/
theorem uniformPayoff_or_summableSemanticPort
    (marked : QuittingPaidRowMarkedExactOrbit source) :
    (exists payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      exists port :
          QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
            marked.orbit,
        Nonempty (SummableSemanticPort marked port) := by
  rcases marked.uniformPayoff_or_summableChargeAllContinuePort with
    huniform | hport
  · exact Or.inl huniform
  · rcases hport with ⟨port⟩
    exact Or.inr ⟨port, marked.nonempty_summableSemanticPort port⟩

end QuittingPaidRowMarkedExactOrbit

/-- Source-facing capstone: construct the literal paid suffix orbit and make
the exact cumulative-charge versus semantic-port split on that orbit. -/
theorem QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative
    (source : QuittingPaidRowFloorSafeSource reward) :
    exists marked : QuittingPaidRowMarkedExactOrbit source,
      (exists payoff : Payoff iota,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      exists port :
          QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
            marked.orbit,
        Nonempty
          (QuittingPaidRowMarkedExactOrbit.SummableSemanticPort marked port) := by
  obtain ⟨marked⟩ := QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe source
  exact ⟨marked, marked.uniformPayoff_or_summableSemanticPort⟩

/-- With a terminal-gap witness, the summable port additionally retains the
paid suffix with positive limiting reach through all selected roots. -/
theorem QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness
    (source : QuittingPaidRowFloorSafeSource reward)
    (witness : QuittingTerminalExploitabilityWitness reward) :
    exists marked : QuittingPaidRowMarkedExactOrbit source,
      (exists payoff : Payoff iota,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      exists port :
          QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
            marked.orbit,
        Nonempty
            (QuittingPaidRowMarkedExactOrbit.SummableSemanticPort marked port) ∧
          Nonempty
            (QuittingPaidRowMarkedExactOrbit.PositivePaidSuffixReach marked) := by
  obtain ⟨marked⟩ := QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe source
  rcases marked.uniformPayoff_or_summableChargeAllContinuePort with
    huniform | hport
  · exact ⟨marked, Or.inl huniform⟩
  · rcases hport with ⟨port⟩
    exact ⟨marked, Or.inr ⟨port,
      marked.nonempty_summableSemanticPort port,
      marked.nonempty_positivePaidSuffixReach_of_terminalWitness port witness⟩⟩

/-- A normalized-curvature paid witness enters the exact-port construction
once its attained receiving payoff is separately proved floor-safe. -/
theorem QuittingStoppingLawCurvaturePaidWitness.nonempty_markedExactOrbit_of_floor
    {profile : (quittingGame reward).BehaviorProfile}
    {mover observer : iota}
    {target : (quittingGame reward).BehaviorStrategy mover}
    {sourceError endpointError gain : Real}
    (carrier : QuittingStoppingLawCurvaturePaidWitness reward profile mover
      observer target sourceError endpointError gain)
    (hgain : 0 < gain)
    (hfloor : forall who,
      quittingPunishmentValue reward who <=
        quittingTerminalPayoff reward
          (Function.update profile mover target) who) :
    Nonempty (QuittingPaidRowMarkedExactOrbit
      ({ profile := Function.update profile mover target
         observer := observer
         gain := gain
         gain_pos := hgain
         row := carrier.row
         punishment_le := hfloor } : QuittingPaidRowFloorSafeSource reward)) :=
  QuittingPaidRowMarkedExactOrbit.nonempty_of_floorSafe _

end GameTheory
