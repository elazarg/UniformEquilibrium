/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.InteriorCyclicTerminalDebtRatio
import UniformEquilibrium.Quitting.Cycles.PeriodOneOwnerConcentrationContradiction
import UniformEquilibrium.Quitting.Circulation.DirectionBarycenter

/-!
# Actual one-period sources with vanishing total hazard

For any prescribed positive error sequence tending to zero, the interior
fixed-point producer gives one actual family of one-period stationary sources.
If a four-player quitting game has no uniform-equilibrium payoff, its positive
terminal exploitability gap selects one fixed debtor along one strict
subsequence. The owner-concentration alternative is impossible, so the same
selected source chronology has vanishing total hazard.

No limiting hazard direction, singleton first-order law, or cap asymptotic is
asserted in this module.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- One produced one-period block family together with one fixed debtor and a
strictly selected chronology on which the actual stationary sources have
vanishing total hazard. -/
structure PeriodOneVanishingHazardSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (error : ℕ → ℝ) where
  block : ∀ n, InteriorApproximateNashCyclicBlock reward 0 (error n)
  debtFloor : ℝ
  debtFloor_pos : 0 < debtFloor
  owner : ι
  vanishing : InteriorCyclicVanishingHazardSubsequence reward
    (fun _ ↦ 0) error block (fun _ ↦ 0) owner debtFloor

namespace PeriodOneVanishingHazardSource

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ}

/-- The literal stationary behavior profile at one selected source. -/
def profile (source : PeriodOneVanishingHazardSource reward error)
    (index : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (source.block (source.vanishing.select index)).cycle 0

/-- The displayed product root at one selected source. -/
def root (source : PeriodOneVanishingHazardSource reward error)
    (index : ℕ) : ι → PMF Bool :=
  (source.block (source.vanishing.select index)).cycle 0

/-- The exact-return value of one selected source. -/
def value (source : PeriodOneVanishingHazardSource reward error)
    (index : ℕ) : Payoff ι :=
  (source.block (source.vanishing.select index)).value 0

omit [Nontrivial ι] in
/-- The fixed debtor's terminal-debt floor holds on every selected actual
stationary source. -/
theorem debtFloor_le_terminalDeviationDebt
    (source : PeriodOneVanishingHazardSource reward error) (index : ℕ) :
    source.debtFloor ≤ quittingTerminalDeviationDebt reward
      (source.profile index) source.owner := by
  exact source.vanishing.ownerDebt_floor index

omit [Nontrivial ι] in
/-- The selected actual product roots have vanishing total Quit hazard. -/
theorem totalHazard_tendsto_zero
    (source : PeriodOneVanishingHazardSource reward error) :
    Tendsto (fun index ↦
      quittingStationaryTotalHazard (source.root index)) atTop (nhds 0) := by
  change Tendsto (fun index ↦ ∑ who,
    ((source.block (source.vanishing.select index)).cycle 0 who true).toReal)
    atTop (nhds 0)
  simpa [quittingCyclicTotalHazard] using
    source.vanishing.totalHazard_tendsto_zero

omit [Nontrivial ι] in
/-- Every displayed hazard is strictly positive at every finite source. -/
theorem quitProbability_pos
    (source : PeriodOneVanishingHazardSource reward error)
    (index : ℕ) (who : ι) :
    0 < (source.root index who true).toReal := by
  exact (source.block (source.vanishing.select index)).quitProbability_pos 0 who

/-- Strict interiority makes the total source hazard positive at every
finite index. -/
theorem totalHazard_pos
    (source : PeriodOneVanishingHazardSource reward error) (index : ℕ) :
    0 < quittingStationaryTotalHazard (source.root index) := by
  let who : ι := Classical.choice inferInstance
  have hsingle : (source.root index who true).toReal ≤
      quittingStationaryTotalHazard (source.root index) := by
    unfold quittingStationaryTotalHazard
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun other ↦ (source.root index other true).toReal)
      (fun other _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ who)
  exact (source.quitProbability_pos index who).trans_le hsingle

/-- The displayed value is the literal terminal payoff of its actual
stationary source. -/
theorem terminalPayoff_eq_value
    (source : PeriodOneVanishingHazardSource reward error) (index : ℕ) :
    quittingTerminalPayoff reward (source.profile index) = source.value index := by
  exact (congrFun
    (source.block (source.vanishing.select index)).value_eq_cyclicTerminalValue
      0).symm

end PeriodOneVanishingHazardSource

/-- One further strict compactness selection of the already selected source
chronology, carrying both its normalized hazard direction and exact-return
value. -/
structure PeriodOneNormalizedSourceLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℕ → ℝ}
    (source : PeriodOneVanishingHazardSource reward error) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  direction : stdSimplex ℝ ι
  limitValue : Payoff ι
  direction_tendsto : Tendsto (fun index ↦
    quittingStationaryHazardDirection (source.root (select index))
      (source.totalHazard_pos (select index))) atTop (nhds direction)
  value_tendsto : Tendsto (fun index ↦ source.value (select index))
    atTop (nhds limitValue)

namespace PeriodOneNormalizedSourceLimit

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {error : ℕ → ℝ}
  {source : PeriodOneVanishingHazardSource reward error}

/-- Original producer index of the refined source. Both selections are strict,
so this remains one cofinal subsequence of the single produced family. -/
def originalIndex (limit : PeriodOneNormalizedSourceLimit source)
    (index : ℕ) : ℕ :=
  source.vanishing.select (limit.select index)

/-- The composed selection of original produced blocks is strictly
increasing. -/
theorem originalIndex_strictMono
    (limit : PeriodOneNormalizedSourceLimit source) :
    StrictMono limit.originalIndex :=
  source.vanishing.select_strictMono.comp limit.select_strictMono

/-- The refined root is literally the corresponding root in the one produced
block family. -/
theorem selectedRoot_eq
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    source.root (limit.select index) =
      (source.block (limit.originalIndex index)).cycle 0 := rfl

/-- The refined profile is literally the corresponding stationary profile in
the one produced block family. -/
theorem selectedProfile_eq
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    source.profile (limit.select index) =
      quittingCyclicBehaviorProfile reward
        (source.block (limit.originalIndex index)).cycle 0 := rfl

/-- The refined value is literally the corresponding exact-return value in
the one produced block family. -/
theorem selectedValue_eq
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    source.value (limit.select index) =
      (source.block (limit.originalIndex index)).value 0 := rfl

/-- The selected displayed value is literally the terminal payoff of the
selected actual stationary profile. -/
theorem selectedTerminalPayoff_eq_value
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    quittingTerminalPayoff reward (source.profile (limit.select index)) =
      source.value (limit.select index) :=
  source.terminalPayoff_eq_value (limit.select index)

/-- The same fixed debtor and debt floor persist after compactification. -/
theorem debtFloor_le_selectedTerminalDeviationDebt
    (limit : PeriodOneNormalizedSourceLimit source) (index : ℕ) :
    source.debtFloor ≤ quittingTerminalDeviationDebt reward
      (source.profile (limit.select index)) source.owner :=
  source.debtFloor_le_terminalDeviationDebt (limit.select index)

/-- Any convergence along the original producer indices persists through the
composed cofinal selection. -/
theorem error_tendsto_zero
    (limit : PeriodOneNormalizedSourceLimit source)
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto (fun index ↦ error (limit.originalIndex index))
      atTop (nhds 0) :=
  herror.comp limit.originalIndex_strictMono.tendsto_atTop

/-- Vanishing total hazard persists on the common compactness refinement. -/
theorem totalHazard_tendsto_zero
    (limit : PeriodOneNormalizedSourceLimit source) :
    Tendsto (fun index ↦
      quittingStationaryTotalHazard (source.root (limit.select index)))
      atTop (nhds 0) :=
  source.totalHazard_tendsto_zero.comp limit.select_strictMono.tendsto_atTop

end PeriodOneNormalizedSourceLimit

/-- Compactness selects one normalized hazard direction and one exact-return
value along the same strict refinement of the supplied source chronology. -/
theorem nonempty_periodOneNormalizedSourceLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℕ → ℝ}
    (source : PeriodOneVanishingHazardSource reward error) :
    Nonempty (PeriodOneNormalizedSourceLimit source) := by
  let sourcePoint : ℕ →
      (stdSimplex ℝ ι) × Set.Icc
        (fun _ ↦ -quittingRewardBound reward)
        (fun _ ↦ quittingRewardBound reward) :=
    fun index ↦
      (quittingStationaryHazardDirection (source.root index)
          (source.totalHazard_pos index),
        ⟨source.value index,
          ⟨fun who ↦ (abs_le.mp
              ((source.block
                (source.vanishing.select index)).value_bound 0 who)).1,
            fun who ↦ (abs_le.mp
              ((source.block
                (source.vanishing.select index)).value_bound 0 who)).2⟩⟩)
  obtain ⟨point, select, hselect, hpoint⟩ :=
    CompactSpace.tendsto_subseq sourcePoint
  refine ⟨{
    select := select
    select_strictMono := hselect
    direction := point.1
    limitValue := point.2
    direction_tendsto := ?_
    value_tendsto := ?_
  }⟩
  · exact ((continuous_fst.tendsto point).comp hpoint)
  · have hvalue :=
      (((continuous_subtype_val.comp continuous_snd).tendsto point).comp hpoint)
    change Tendsto (fun index ↦ source.value (select index))
      atTop (nhds (point.2 : Payoff ι)) at hvalue
    exact hvalue

/-- In a four-player game without a uniform-equilibrium payoff, the
unconditional one-period interior producer yields one actual source chronology
with a fixed positive terminal-debt floor and vanishing total hazard. -/
theorem nonempty_periodOneVanishingHazardSource_of_fourPlayer_noUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (error : ℕ → ℝ) (herrorPos : ∀ n, 0 < error n)
    (herror : Tendsto error atTop (nhds 0)) :
    Nonempty (PeriodOneVanishingHazardSource reward error) := by
  let block := Classical.choice
    (nonempty_interiorApproximateNashCyclicBlockFamily reward
      (fun _ ↦ 0) error herrorPos)
  obtain ⟨gap, hgap, exploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hno
  have hperiodError : Tendsto (fun n ↦
      (((0 : ℕ) + 1 : ℕ) : ℝ) * error n) atTop (nhds 0) := by
    simpa using herror
  obtain ⟨fixed, hescape⟩ :=
    exists_interiorCyclicFixedDebtor_and_ownerEscape_of_terminalGap
      reward (fun _ ↦ 0) error (fun n ↦ (herrorPos n).le) block
      (fun _ ↦ 0) hgap exploit hperiodError
  let escape := Classical.choice hescape
  cases escape with
  | ownerConcentration data =>
      exact (false_of_periodOne_ownerConcentration_of_finFour_noUniformPayoff
        reward hplayers hno error herror block (fun _ ↦ 0) data).elim
  | vanishingHazard data =>
      exact ⟨{
        block := block
        debtFloor := gap
        debtFloor_pos := hgap
        owner := fixed.owner
        vanishing := data
      }⟩

/-- The source producer and compactness step compose without supplying a root,
debt floor, debtor, normalized direction, or payoff limit by hand. The output
still refers to one produced block family through one composed cofinal
selection. -/
theorem exists_periodOneNormalizedSourceLimit_of_fourPlayer_noUniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (error : ℕ → ℝ) (herrorPos : ∀ n, 0 < error n)
    (herror : Tendsto error atTop (nhds 0)) :
    ∃ source : PeriodOneVanishingHazardSource reward error,
      Nonempty (PeriodOneNormalizedSourceLimit source) := by
  let source := Classical.choice
    (nonempty_periodOneVanishingHazardSource_of_fourPlayer_noUniformPayoff
      reward hplayers hno error herrorPos herror)
  exact ⟨source, nonempty_periodOneNormalizedSourceLimit source⟩

end GameTheory
