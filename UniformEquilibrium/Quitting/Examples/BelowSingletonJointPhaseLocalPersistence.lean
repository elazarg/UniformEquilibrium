import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseJacobian
import UniformEquilibrium.Quitting.Root.RewardTableCoordinates
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! # Full reward-coordinate persistence below the singleton levels

Every nonempty-coalition/recipient entry is an independent parameter. The
actual four-odds equations select the nearby profile. Both phase singleton
gaps and all passive Quit gaps persist without imposing the original table's
family equalities or joining-cap hypotheses on nearby tables.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open PairedCycle Math.CrossedMatching Math.PairedAffine Filter
open scoped Topology ContDiff

abbrev RewardParameters :=
  Fin (Fintype.card (QuittingRewardTableVariable (Fin 4))) → ℝ

theorem rewardTableVariable_card :
    Fintype.card (QuittingRewardTableVariable (Fin 4)) = 60 := by
  have hrows : Fintype.card {S : Finset (Fin 4) // S.Nonempty} = 15 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr Math.Finset.finFourCoalitionRowEquiv.symm
  change Fintype.card ({S : Finset (Fin 4) // S.Nonempty} × Fin 4) = 60
  rw [Fintype.card_prod, hrows, Fintype.card_fin]

def baseParameters : RewardParameters := quittingRewardTableCoordinates reward

def jointOddsResponse (input : RewardParameters × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  oddsResponse (quittingRewardTableFromCoordinates input.1) input.2

def jointPhaseValue (input : RewardParameters × (Fin 4 → ℝ)) (phase : Fin 2) :
    Payoff (Fin 4) :=
  twoPairPhaseValue (quittingRewardTableFromCoordinates input.1) fin4Schedule
    (TwoPairOdds.hazard input.2) phase

def jointPostValue (input : RewardParameters × (Fin 4 → ℝ)) (player : Fin 4) : ℝ :=
  twoPairPostValue (quittingRewardTableFromCoordinates input.1) fin4Schedule
    (TwoPairOdds.hazard input.2) player

def jointPassiveQuit (input : RewardParameters × (Fin 4 → ℝ)) (player : Fin 4) : ℝ :=
  let table := quittingRewardTableFromCoordinates input.1
  bellman (table ⟨{player, favorite player}, by simp⟩ player)
    (table ⟨{player, other player}, by simp⟩ player)
    (table ⟨{player, favorite player, other player}, by simp⟩ player)
    (TwoPairOdds.hazard input.2 (favorite player))
    (TwoPairOdds.hazard input.2 (other player)) (PairedCycle.singleton table player)

theorem contDiffAt_jointOddsResponse :
    ContDiffAt ℝ 1 jointOddsResponse (baseParameters, baseOdds) := by
  apply contDiffAt_pi.mpr
  intro player
  unfold jointOddsResponse oddsResponse passiveEquation TwoPairOdds.premium
    TwoPairOdds.passive quittingProjectiveLCPMatrix
    PairedCycle.singleton quittingRewardTableFromCoordinates
  fun_prop (disch := norm_num [baseOdds])

private theorem contDiffAt_jointPostValue (player : Fin 4) :
    ContDiffAt ℝ 1 (fun input => jointPostValue input player) (baseParameters, baseOdds) := by
  unfold jointPostValue twoPairPostValue postValue partnerReward jointReward
    PairedCycle.singleton TwoPairOdds.hazard quittingRewardTableFromCoordinates
  fun_prop (disch := norm_num [baseOdds])

private theorem contDiffAt_jointPhaseValue (phase : Fin 2) (player : Fin 4) :
    ContDiffAt ℝ 1 (fun input => jointPhaseValue input phase player)
      (baseParameters, baseOdds) := by
  unfold jointPhaseValue twoPairPhaseValue
  split_ifs
  · unfold twoPairActiveValue activeValue jointReward PairedCycle.singleton
      TwoPairOdds.hazard quittingRewardTableFromCoordinates
    fun_prop (disch := norm_num [baseOdds])
  · exact contDiffAt_jointPostValue player

private theorem contDiffAt_jointPassiveQuit (player : Fin 4) :
    ContDiffAt ℝ 1 (fun input => jointPassiveQuit input player)
      (baseParameters, baseOdds) := by
  unfold jointPassiveQuit bellman contribution PairedCycle.singleton
    TwoPairOdds.hazard quittingRewardTableFromCoordinates
  fun_prop (disch := norm_num [baseOdds])

theorem jointOddsResponse_base : jointOddsResponse (baseParameters, baseOdds) = 0 := by
  unfold jointOddsResponse baseParameters
  rw [quittingRewardTableFromCoordinates_encode]
  exact baseOdds_response_zero

theorem jointOddsResponse_partial_invertible :
    (fderiv ℝ jointOddsResponse (baseParameters, baseOdds) ∘L
      ContinuousLinearMap.inr ℝ RewardParameters (Fin 4 → ℝ)).IsInvertible := by
  have hderivative := (contDiffAt_jointOddsResponse.hasStrictFDerivAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hchain := hderivative.comp baseOdds
    (hasFDerivAt_prodMk_right baseParameters baseOdds)
  simp only [Function.comp_def] at hchain
  have hfunction : (fun point => jointOddsResponse (baseParameters, point)) =
      oddsResponse reward := by
    funext point
    unfold jointOddsResponse baseParameters
    rw [quittingRewardTableFromCoordinates_encode]
  rw [hfunction] at hchain
  rw [← hchain.fderiv]
  exact baseOdds_derivative_invertible

private theorem jointPhaseValue_base (phase : Fin 2) :
    jointPhaseValue (baseParameters, baseOdds) phase = phaseValues phase := by
  unfold jointPhaseValue baseParameters
  rw [quittingRewardTableFromCoordinates_encode]
  have hh : TwoPairOdds.hazard baseOdds = fun _ => 1 - (2 / 3 : ℝ) := by
    funext player
    norm_num [TwoPairOdds.hazard, baseOdds]
  rw [hh, phaseValue_eq]

private theorem jointPostValue_base (player : Fin 4) :
    jointPostValue (baseParameters, baseOdds) player = 19 / 20 := by
  unfold jointPostValue baseParameters
  rw [quittingRewardTableFromCoordinates_encode, TwoPairOdds.postValue_eq]
  · rw [TwoPairOdds.matrix_entry, rawFamily.scheduled_singleton]
    unfold TwoPairOdds.premium
    rw [rawFamily.active_pair, singleton_eq]
    norm_num [baseOdds]
  · intro coordinate
    norm_num [baseOdds]

private theorem jointPassiveQuit_base (player : Fin 4) :
    jointPassiveQuit (baseParameters, baseOdds) player = 1 / 3 := by
  unfold jointPassiveQuit baseParameters
  rw [quittingRewardTableFromCoordinates_encode]
  fin_cases player <;>
    norm_num +decide [bellman, contribution, reward, TwoPairOdds.hazard,
      baseOdds, PairedCycle.singleton,
      Math.FiniteCoalition.binaryCode_finFour, favorite, other, quittingSingletonTerminal]

/-- The selected four-odds branch persists over all sixty independent reward coordinates. -/
theorem exists_local_odds_branch :
    ∃ branch : RewardParameters → (Fin 4 → ℝ), ∃ neighborhood : Set RewardParameters,
      IsOpen neighborhood ∧ baseParameters ∈ neighborhood ∧
      ContDiffOn ℝ 1 branch neighborhood ∧ branch baseParameters = baseOdds ∧
      ∀ parameters ∈ neighborhood,
        (∀ player, 0 < branch parameters player) ∧
        jointOddsResponse (parameters, branch parameters) = 0 ∧
        (∀ player, jointPassiveQuit (parameters, branch parameters) player <
          jointPostValue (parameters, branch parameters) player) ∧
        (∀ phase player, jointPhaseValue (parameters, branch parameters) phase player <
          PairedCycle.singleton (quittingRewardTableFromCoordinates parameters) player) := by
  have cdf := contDiffAt_jointOddsResponse
  let branch := cdf.implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0)
    jointOddsResponse_partial_invertible
  have hbase : branch baseParameters = baseOdds := cdf.implicitFunction_apply_self _ _
  have hbranch : ContDiffAt ℝ 1 branch baseParameters := cdf.contDiffAt_implicitFunction _ _
  have hzero : ∀ᶠ parameters in 𝓝 baseParameters,
      jointOddsResponse (parameters, branch parameters) = 0 := by
    simpa only [jointOddsResponse_base] using cdf.eventually_apply_implicitFunction
      (by norm_num : (1 : ℕ∞ω) ≠ 0) jointOddsResponse_partial_invertible
  have hpositive : ∀ᶠ input : RewardParameters × (Fin 4 → ℝ)
      in 𝓝 (baseParameters, baseOdds), ∀ player, 0 < input.2 player := by
    rw [eventually_all]
    intro player
    exact ((continuous_apply player).comp continuous_snd).continuousAt.tendsto.eventually
      (Ioi_mem_nhds (by norm_num [baseOdds]))
  have hgap : ∀ᶠ input in 𝓝 (baseParameters, baseOdds), ∀ player,
      jointPassiveQuit input player < jointPostValue input player := by
    rw [eventually_all]
    intro player
    have hdiff := (contDiffAt_jointPostValue player).continuousAt.sub
      (contDiffAt_jointPassiveQuit player).continuousAt
    have hstrict : 0 < jointPostValue (baseParameters, baseOdds) player -
        jointPassiveQuit (baseParameters, baseOdds) player := by
      rw [jointPostValue_base, jointPassiveQuit_base]
      norm_num
    filter_upwards [hdiff.tendsto.eventually (Ioi_mem_nhds hstrict)] with input hinput
    exact sub_pos.mp hinput
  have hbelow : ∀ᶠ input in 𝓝 (baseParameters, baseOdds), ∀ phase player,
      jointPhaseValue input phase player <
        PairedCycle.singleton (quittingRewardTableFromCoordinates input.1) player := by
    rw [eventually_all]
    intro phase
    rw [eventually_all]
    intro player
    have hs : ContinuousAt (fun input : RewardParameters × (Fin 4 → ℝ) =>
        PairedCycle.singleton (quittingRewardTableFromCoordinates input.1) player)
        (baseParameters, baseOdds) := by
      unfold PairedCycle.singleton quittingRewardTableFromCoordinates
      fun_prop
    have hdiff := hs.sub (contDiffAt_jointPhaseValue phase player).continuousAt
    have hstrict : 0 < PairedCycle.singleton
        (quittingRewardTableFromCoordinates baseParameters) player -
        jointPhaseValue (baseParameters, baseOdds) phase player := by
      rw [jointPhaseValue_base]
      rw [baseParameters, quittingRewardTableFromCoordinates_encode]
      exact sub_pos.mpr (phaseValues_lt_singleton phase player)
    filter_upwards [hdiff.tendsto.eventually (Ioi_mem_nhds hstrict)] with input hinput
    exact sub_pos.mp hinput
  have hpair : Tendsto (fun parameters => (parameters, branch parameters))
      (𝓝 baseParameters) (𝓝 (baseParameters, baseOdds)) := by
    simpa only [hbase, id_eq] using
      continuous_id.continuousAt.tendsto.prodMk_nhds hbranch.continuousAt.tendsto
  have hgood := (hpair.eventually (hpositive.and (hgap.and hbelow))).and
    (hzero.and (hbranch.eventually (by norm_num : (1 : ℕ∞ω) ≠ ∞)))
  obtain ⟨neighborhood, hsubset, hopen, hmem⟩ := mem_nhds_iff.mp hgood
  refine ⟨branch, neighborhood, hopen, hmem, ?_, hbase, ?_⟩
  · intro parameters hparameters
    exact (hsubset hparameters).2.2.contDiffWithinAt
  · intro parameters hparameters
    have h := hsubset hparameters
    exact ⟨h.1.1, h.2.1, h.1.2.1, h.1.2.2⟩

def nearbyProfile (parameters : RewardParameters) (point : Fin 4 → ℝ)
    (hpoint : ∀ player, 0 < point player) (initial : Fin 2) :
    (quittingGame (quittingRewardTableFromCoordinates parameters)).BehaviorProfile :=
  quittingCyclicBehaviorProfile (quittingRewardTableFromCoordinates parameters)
    (cycle fin4Schedule (TwoPairOdds.hazard point)
      (properUnitBounds _ (TwoPairOdds.hazard_proper hpoint))) initial

/-- Nearby unrestricted tables have actual exact profiles, below every own-singleton level.
For each table the displayed profile and target work at every accuracy. -/
theorem exists_open_below_singleton_uniform_profiles :
    ∃ neighborhood : Set RewardParameters,
      IsOpen neighborhood ∧ baseParameters ∈ neighborhood ∧
      ∀ parameters ∈ neighborhood, ∃ point : Fin 4 → ℝ,
        ∃ hpoint : ∀ player, 0 < point player,
        (∀ phase player, jointPhaseValue (parameters, point) phase player <
          PairedCycle.singleton (quittingRewardTableFromCoordinates parameters) player) ∧
        ∀ initial : Fin 2,
        quittingTerminalPayoff (quittingRewardTableFromCoordinates parameters)
            (nearbyProfile parameters point hpoint initial) =
          jointPhaseValue (parameters, point) initial ∧
        (quittingGame (quittingRewardTableFromCoordinates parameters)).IsεAsymptoticNash
          (quittingTerminalPayoff (quittingRewardTableFromCoordinates parameters)) 0
          (nearbyProfile parameters point hpoint initial) ∧
        (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
          (quittingGame (quittingRewardTableFromCoordinates parameters)).IsεHorizonNash
              none horizon ε (nearbyProfile parameters point hpoint initial) ∧
            ∀ player,
              |(quittingGame (quittingRewardTableFromCoordinates parameters)).finiteAveragePayoff
                  none horizon (nearbyProfile parameters point hpoint initial) player -
                jointPhaseValue (parameters, point) initial player| ≤ ε) ∧
        (quittingGame (quittingRewardTableFromCoordinates parameters)).IsUniformEquilibriumPayoff
          none (jointPhaseValue (parameters, point) initial) := by
  obtain ⟨branch, neighborhood, hopen, hbase, _hsmooth, _hbranchBase, hgood⟩ :=
    exists_local_odds_branch
  refine ⟨neighborhood, hopen, hbase, ?_⟩
  intro parameters hparameters
  obtain ⟨hpositive, hequation, hgap, hbelow⟩ := hgood parameters hparameters
  refine ⟨branch parameters, hpositive, hbelow, ?_⟩
  intro initial
  have hcontinue := TwoPairOdds.passive_continue
    (quittingRewardTableFromCoordinates parameters) hpositive
    (fun player => congrFun hequation player)
  have hquit (player : Fin 4) :
      quittingRootQuitPayoff (quittingRewardTableFromCoordinates parameters)
          (twoPairPhaseValue (quittingRewardTableFromCoordinates parameters) fin4Schedule
            (TwoPairOdds.hazard (branch parameters)) (fin4Schedule.phase player))
          (cycle fin4Schedule (TwoPairOdds.hazard (branch parameters))
            (properUnitBounds _ (TwoPairOdds.hazard_proper hpositive))
            (finRotate 2 (fin4Schedule.phase player))) player ≤
        twoPairPostValue (quittingRewardTableFromCoordinates parameters) fin4Schedule
          (TwoPairOdds.hazard (branch parameters)) player := by
    rw [fin4Schedule_passive_root, rootQuit_eq_bellman]
    · simp only [quittingHazardCoin_true_toReal]
      exact (hgap player).le
    · fin_cases player <;> decide
  have hresult := twoPair_exact_terminal_and_fixedProfile
    (quittingRewardTableFromCoordinates parameters) fin4Schedule
    (TwoPairOdds.hazard (branch parameters)) (TwoPairOdds.hazard_proper hpositive)
    hcontinue hquit initial
  simpa only [nearbyProfile, jointPhaseValue] using hresult

/-- An actual odds-selected profile, with a fixed target at every accuracy. -/
def HasBelowSingletonExactProfile (table : TwoPairOdds.Reward) : Prop :=
  ∃ point : Fin 4 → ℝ, ∃ hpoint : ∀ player, 0 < point player,
    let q := TwoPairOdds.hazard point
    (∀ phase player, twoPairPhaseValue table fin4Schedule q phase player <
      PairedCycle.singleton table player) ∧
    ∀ initial : Fin 2,
    let selectedProfile := quittingCyclicBehaviorProfile table
      (cycle fin4Schedule q (properUnitBounds _ (TwoPairOdds.hazard_proper hpoint))) initial
    let target := twoPairPhaseValue table fin4Schedule q initial
    quittingTerminalPayoff table selectedProfile = target ∧
    (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0 selectedProfile ∧
    (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      (quittingGame table).IsεHorizonNash none horizon ε selectedProfile ∧
        ∀ player, |(quittingGame table).finiteAveragePayoff none horizon selectedProfile player -
          target player| ≤ ε) ∧
    (quittingGame table).IsUniformEquilibriumPayoff none target

/-- A genuine uniform reward-entry radius; no nearby family or cap equations are inputs. -/
theorem exists_reward_supnorm_radius :
    ∃ δ : ℝ, 0 < δ ∧ ∀ table : TwoPairOdds.Reward,
      (∀ terminal player, |table terminal player - reward terminal player| ≤ δ) →
        HasBelowSingletonExactProfile table := by
  obtain ⟨neighborhood, hopen, hbase, hprofiles⟩ :=
    exists_open_below_singleton_uniform_profiles
  obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp hopen baseParameters hbase
  refine ⟨radius / 2, by linarith, ?_⟩
  intro table hclose
  have hparameters : quittingRewardTableCoordinates table ∈ neighborhood := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    apply (pi_norm_lt_iff hradius).mpr
    intro coordinate
    have hentry := hclose
      ((Fintype.equivFin (QuittingRewardTableVariable (Fin 4))).symm coordinate).1
      ((Fintype.equivFin (QuittingRewardTableVariable (Fin 4))).symm coordinate).2
    have hstrict : |table
        ((Fintype.equivFin (QuittingRewardTableVariable (Fin 4))).symm coordinate).1
        ((Fintype.equivFin (QuittingRewardTableVariable (Fin 4))).symm coordinate).2 -
      reward ((Fintype.equivFin (QuittingRewardTableVariable (Fin 4))).symm coordinate).1
        ((Fintype.equivFin (QuittingRewardTableVariable (Fin 4))).symm coordinate).2| <
        radius := by linarith
    simpa only [Pi.sub_apply, baseParameters, quittingRewardTableCoordinates,
      Real.norm_eq_abs] using hstrict
  obtain ⟨point, hpoint, hresult⟩ := hprofiles _ hparameters
  rw [← quittingRewardTableFromCoordinates_encode table]
  refine ⟨point, hpoint, ?_⟩
  simpa only [jointPhaseValue, nearbyProfile] using hresult

end GameTheory.BelowSingletonJointPhaseFixture
