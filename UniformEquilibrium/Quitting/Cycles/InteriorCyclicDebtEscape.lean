/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelSubsequence
import MathUE.Topology.NonnegativeSubsequenceDichotomy
import UniformEquilibrium.Quitting.Cycles.OwnerSingletonCyclicConcentration

/-!
# Fixed-debtor escape alternatives for interior cyclic profiles

A positive terminal-debt floor selects one fixed player along a strict
subsequence.  If period times local error vanishes, that player's opponent
absorption vanishes.  A second, purely scalar refinement either keeps the
player's own absorption uniformly positive, forcing singleton-payoff
concentration and vanishing outsider debt, or makes the whole displayed
hazard vanish.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A fixed debtor and strict subsequence extracted from a family of
interior cyclic profiles with a uniform terminal-debt floor. -/
structure InteriorCyclicFixedDebtorSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) (debtFloor : ℝ) where
  owner : ι
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  terminalDebt_floor : ∀ n, debtFloor ≤
    quittingTerminalDeviationDebt reward
      (quittingCyclicBehaviorProfile reward
        (block (select n)).cycle (initial (select n))) owner
  opponentAbsorption_le : ∀ n,
    quittingCyclicOpponentAbsorptionMass
        (block (select n)).cycle owner ≤
      (((period (select n) + 1 : ℕ) : ℝ) * error (select n)) /
        debtFloor
  opponentAbsorption_tendsto_zero : Tendsto (fun n =>
    quittingCyclicOpponentAbsorptionMass
      (block (select n)).cycle owner) atTop (nhds 0)

/-- A terminal-debt floor at some player of every cyclic profile, together
with vanishing period times local error, yields one fixed debtor whose
opponent absorption vanishes along a strict subsequence. -/
theorem nonempty_interiorCyclicFixedDebtorSubsequence
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (herror : ∀ n, 0 ≤ error n)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) {debtFloor : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hdebt : ∀ n, ∃ who, debtFloor ≤
      quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward
          (block n).cycle (initial n)) who)
    (hperiodError : Tendsto (fun n =>
      ((period n + 1 : ℕ) : ℝ) * error n) atTop (nhds 0)) :
    Nonempty (InteriorCyclicFixedDebtorSubsequence
      reward period error block initial debtFloor) := by
  let debtor : ℕ → ι := fun n => Classical.choose (hdebt n)
  have hdebtor : ∀ n, debtFloor ≤
      quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward
          (block n).cycle (initial n)) (debtor n) :=
    fun n => Classical.choose_spec (hdebt n)
  obtain ⟨owner, select, hselect, howner⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence debtor
  have hfloor : ∀ n, debtFloor ≤
      quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward
          (block (select n)).cycle (initial (select n))) owner := by
    intro n
    rw [← howner n]
    exact hdebtor (select n)
  have hopponentLe : ∀ n,
      quittingCyclicOpponentAbsorptionMass
          (block (select n)).cycle owner ≤
        (((period (select n) + 1 : ℕ) : ℝ) * error (select n)) /
          debtFloor := by
    intro n
    exact (block (select n)).opponentAbsorptionMass_le_of_debt_floor
      (herror (select n)) hdebtFloor (initial (select n)) owner (hfloor n)
  have hupper : Tendsto (fun n =>
      (((period (select n) + 1 : ℕ) : ℝ) * error (select n)) /
        debtFloor) atTop (nhds 0) := by
    have hcomp := hperiodError.comp hselect.tendsto_atTop
    simpa only [Function.comp_apply, zero_div] using hcomp.div_const debtFloor
  have hopponentNonneg : ∀ n, 0 ≤
      quittingCyclicOpponentAbsorptionMass
        (block (select n)).cycle owner := by
    intro n
    unfold quittingCyclicOpponentAbsorptionMass
    exact sub_nonneg.mpr <| Finset.prod_le_one
      (fun phase _ =>
        quittingStationaryFixedOpponentsContinueMass_nonneg _ _)
      (fun phase _ => by
        change quittingStationaryContinueMass
          (Function.update ((block (select n)).cycle phase) owner
            (PMF.pure false)) ≤ 1
        exact quittingStationaryContinueMass_le_one _)
  have hopponentZero : Tendsto (fun n =>
      quittingCyclicOpponentAbsorptionMass
        (block (select n)).cycle owner) atTop (nhds 0) :=
    squeeze_zero hopponentNonneg hopponentLe hupper
  exact ⟨{
    owner := owner
    select := select
    select_strictMono := hselect
    terminalDebt_floor := hfloor
    opponentAbsorption_le := hopponentLe
    opponentAbsorption_tendsto_zero := hopponentZero
  }⟩

/-- The positive-own-absorption refinement. The actual terminal law and
terminal payoff converge to the fixed owner's singleton, every outsider's
complete behavioral deviation debt tends to zero, and the owner's debt floor
and vanishing opponent absorption persist on the displayed subsequence. -/
structure InteriorCyclicOwnerConcentrationSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) (owner : ι)
    (debtFloor : ℝ) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  absorptionFloor : ℝ
  absorptionFloor_pos : 0 < absorptionFloor
  playerAbsorption_floor : ∀ n, absorptionFloor ≤
    quittingCyclicPlayerAbsorptionMass (block (select n)).cycle owner
  opponentAbsorption_tendsto_zero : Tendsto (fun n =>
    quittingCyclicOpponentAbsorptionMass
      (block (select n)).cycle owner) atTop (nhds 0)
  ownerDebt_floor : ∀ n, debtFloor ≤
    quittingTerminalDeviationDebt reward
      (quittingCyclicBehaviorProfile reward
        (block (select n)).cycle (initial (select n))) owner
  terminalPayoff_tendsto_singleton : Tendsto (fun n =>
    (block (select n)).value (initial (select n))) atTop
    (nhds (fun observer =>
      reward (quittingSingletonTerminal owner) observer))
  terminalOutcomeMass_tendsto_singleton : Tendsto (fun n =>
    quittingTerminalOutcomeMass reward
      (quittingCyclicBehaviorProfile reward
        (block (select n)).cycle (initial (select n)))) atTop
    (nhds (quittingSingletonTerminalOutcomeMass owner))
  outsiderDebt_tendsto_zero : ∀ outsider, owner ≠ outsider →
    Tendsto (fun n =>
      quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward
          (block (select n)).cycle (initial (select n))) outsider)
      atTop (nhds 0)

/-- The vanishing-own-absorption refinement. The sum of every Quit probability
displayed in the selected cyclic words tends to zero, while the owner's debt
floor and vanishing opponent absorption persist on the same subsequence. -/
structure InteriorCyclicVanishingHazardSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) (owner : ι)
    (debtFloor : ℝ) where
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  playerAbsorption_tendsto_zero : Tendsto (fun n =>
    quittingCyclicPlayerAbsorptionMass
      (block (select n)).cycle owner) atTop (nhds 0)
  opponentAbsorption_tendsto_zero : Tendsto (fun n =>
    quittingCyclicOpponentAbsorptionMass
      (block (select n)).cycle owner) atTop (nhds 0)
  ownerDebt_floor : ∀ n, debtFloor ≤
    quittingTerminalDeviationDebt reward
      (quittingCyclicBehaviorProfile reward
        (block (select n)).cycle (initial (select n))) owner
  totalHazard_tendsto_zero : Tendsto (fun n =>
    quittingCyclicTotalHazard (block (select n)).cycle) atTop (nhds 0)

/-- The two exact residual regimes after a fixed debtor's opponent
absorption has been shown to vanish. -/
inductive InteriorCyclicOwnerEscapeAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) (owner : ι)
    (debtFloor : ℝ) : Type
  | ownerConcentration
      (data : InteriorCyclicOwnerConcentrationSubsequence
        reward period error block initial owner debtFloor)
  | vanishingHazard
      (data : InteriorCyclicVanishingHazardSubsequence
        reward period error block initial owner debtFloor)

/-- A fixed debtor with vanishing opponent absorption has a strict
subsequence on which its debt floor and opponent-absorption limit persist and
either the owner remains active with terminal law concentrated on its
singleton, or every displayed hazard vanishes. -/
theorem InteriorCyclicFixedDebtorSubsequence.nonempty_ownerEscapeAlternative
    [Nontrivial ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {period : ℕ → ℕ} {error : ℕ → ℝ}
    {block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n)}
    {initial : ∀ n, Fin (period n + 1)} {debtFloor : ℝ}
    (fixed : InteriorCyclicFixedDebtorSubsequence
      reward period error block initial debtFloor)
    (herror : ∀ n, 0 ≤ error n)
    (hperiodError : Tendsto (fun n =>
      ((period n + 1 : ℕ) : ℝ) * error n) atTop (nhds 0)) :
    Nonempty (InteriorCyclicOwnerEscapeAlternative
      reward period error block initial fixed.owner debtFloor) := by
  let ownAbsorption : ℕ → ℝ := fun n =>
    quittingCyclicPlayerAbsorptionMass
      (block (fixed.select n)).cycle fixed.owner
  have hownNonneg : ∀ n, 0 ≤ ownAbsorption n := by
    intro n
    unfold ownAbsorption quittingCyclicPlayerAbsorptionMass
    exact sub_nonneg.mpr <| Finset.prod_le_one
      (fun phase _ => ENNReal.toReal_nonneg)
      (fun phase _ => ENNReal.toReal_mono ENNReal.one_ne_top
        (((block (fixed.select n)).cycle phase fixed.owner).coe_le_one false))
  let alternative := Classical.choice
    (Math.nonempty_nonnegativeSubsequenceAlternative
      ownAbsorption hownNonneg)
  cases alternative with
  | positiveFloor refine hRefine floor hFloorPos hFloor =>
      let select : ℕ → ℕ := fixed.select ∘ refine
      have hselect : StrictMono select :=
        fixed.select_strictMono.comp hRefine
      have hownerFloor : ∀ n, floor ≤
          quittingCyclicPlayerAbsorptionMass
            (block (select n)).cycle fixed.owner := by
        intro n
        exact hFloor n
      have hopponents : Tendsto (fun n =>
          quittingCyclicOpponentAbsorptionMass
            (block (select n)).cycle fixed.owner) atTop (nhds 0) := by
        exact fixed.opponentAbsorption_tendsto_zero.comp
          hRefine.tendsto_atTop
      have hterminalRaw :=
        tendsto_quittingCyclicTerminalValue_ownerSingleton_of_absorption
          (fun n => period (select n)) reward
          (fun n => (block (select n)).cycle)
          (fun n => initial (select n)) fixed.owner hFloorPos hownerFloor
          hopponents
      have hterminal : Tendsto (fun n =>
          (block (select n)).value (initial (select n))) atTop
          (nhds (fun observer =>
            reward (quittingSingletonTerminal fixed.owner) observer)) := by
        apply hterminalRaw.congr'
        exact Filter.Eventually.of_forall fun n =>
          (congrFun (block (select n)).value_eq_cyclicTerminalValue
            (initial (select n))).symm
      have houtcome :=
        tendsto_quittingTerminalOutcomeMass_cyclicBehaviorProfile_singleton_of_absorption
          (fun n => period (select n)) reward
          (fun n => (block (select n)).cycle)
          (fun n => initial (select n)) fixed.owner hFloorPos hownerFloor
          hopponents
      have hperiodErrorSelected : Tendsto (fun n =>
          (((period (select n) + 1 : ℕ) : ℝ) * error (select n)) /
            floor) atTop (nhds 0) := by
        have hcomp := hperiodError.comp hselect.tendsto_atTop
        simpa only [Function.comp_apply, zero_div] using
          hcomp.div_const floor
      have houtsider : ∀ outsider, fixed.owner ≠ outsider →
          Tendsto (fun n =>
            quittingTerminalDeviationDebt reward
              (quittingCyclicBehaviorProfile reward
                (block (select n)).cycle (initial (select n))) outsider)
            atTop (nhds 0) := by
        intro outsider hne
        apply squeeze_zero
        · intro n
          exact quittingTerminalDeviationDebt_nonneg reward _ outsider
        · intro n
          exact (block (select n)).outsiderTerminalDeviationDebt_le
            (herror (select n)) (initial (select n)) hne hFloorPos
              (hownerFloor n)
        · exact hperiodErrorSelected
      exact ⟨.ownerConcentration {
        select := select
        select_strictMono := hselect
        absorptionFloor := floor
        absorptionFloor_pos := hFloorPos
        playerAbsorption_floor := hownerFloor
        opponentAbsorption_tendsto_zero := hopponents
        ownerDebt_floor := fun n => fixed.terminalDebt_floor (refine n)
        terminalPayoff_tendsto_singleton := hterminal
        terminalOutcomeMass_tendsto_singleton := houtcome
        outsiderDebt_tendsto_zero := houtsider
      }⟩
  | vanishing refine hRefine hownZero =>
      let select : ℕ → ℕ := fixed.select ∘ refine
      have hselect : StrictMono select :=
        fixed.select_strictMono.comp hRefine
      have hopponents : Tendsto (fun n =>
          quittingCyclicOpponentAbsorptionMass
            (block (select n)).cycle fixed.owner) atTop (nhds 0) := by
        exact fixed.opponentAbsorption_tendsto_zero.comp
          hRefine.tendsto_atTop
      have howner : Tendsto (fun n =>
          quittingCyclicPlayerAbsorptionMass
            (block (select n)).cycle fixed.owner) atTop (nhds 0) := by
        exact hownZero
      have htotal :=
        tendsto_zero_quittingCyclicTotalHazard_of_player_and_opponents
          (fun n => period (select n))
          (fun n => (block (select n)).cycle) fixed.owner
          (fun n phase who =>
            (block (select n)).continueProbability_pos phase who)
          hopponents howner
      exact ⟨.vanishingHazard {
        select := select
        select_strictMono := hselect
        playerAbsorption_tendsto_zero := howner
        opponentAbsorption_tendsto_zero := hopponents
        ownerDebt_floor := fun n => fixed.terminalDebt_floor (refine n)
        totalHazard_tendsto_zero := htotal
      }⟩

end GameTheory
