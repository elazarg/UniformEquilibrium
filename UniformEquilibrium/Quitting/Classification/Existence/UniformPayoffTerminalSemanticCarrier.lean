/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ApproximateEquilibriumUniformPayoffEquivalence
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Uniform payoffs are exactly diagonal terminal-semantic carrier points

For a finite quitting game, a fixed payoff is a uniform-equilibrium payoff
exactly when its diagonal pair belongs to the closure of executable terminal
payoff/best-response pairs.  The forward direction selects terminal
approximate equilibria delivering the fixed target.  Their prescribed and
best-response coordinates converge to the target together.

Consequently the AKRS approximate-equilibrium premise is exactly the
existence of a diagonal point in this carrier.  This is a semantic
reformulation, not a stationary, instant-punishment, or sequentially-perfect
classification.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A diagonal point of the literal terminal-semantic carrier is an actual
uniform-equilibrium payoff target.  Carrier membership supplies executable
profiles; convergence of both semantic coordinates makes their terminal Nash
errors and prescribed-payoff errors vanish together. -/
theorem isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
    [Nonempty iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (target : Payoff iota)
    (hmem : (target, target) ∈ quittingTerminalSemanticCarrier reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair
      reward (target, target) hmem
  let error : ℕ → ℝ := fun n ↦ quittingTerminalSemanticExploitability
    (quittingTerminalSemanticPair reward (profiles n))
  have hzero : quittingTerminalSemanticExploitability
      (target, target) = 0 := by
    unfold quittingTerminalSemanticExploitability
      QuittingBoundaryHolonomy.finitePlayerMax
      quittingTerminalSemanticDebt
    simp
  have herror : Tendsto error atTop (nhds 0) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp
        hprofiles
    rw [hzero] at hcontinuous
    exact hcontinuous
  have hnash : ∀ n,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error n) (profiles n) := by
    intro n who deviation
    have hgain := quittingTerminalPayoff_update_sub_le_terminalSemanticDebt
      reward (profiles n) who deviation
    have hdebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) who ≤ error n := by
      dsimp only [error]
      unfold quittingTerminalSemanticExploitability
      exact (le_max_right 0 _).trans
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun player ↦ max 0 (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) player)) who)
    linarith
  have htarget : Tendsto
      (fun n ↦ quittingTerminalPayoff reward (profiles n)) atTop
      (nhds target) := by
    apply tendsto_pi_nhds.2
    intro who
    have hcoordinate :=
      (((continuous_apply who).comp continuous_fst).tendsto
        (target, target)).comp hprofiles
    exact hcoordinate
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto
    reward target error profiles herror (Frequently.of_forall hnash) htarget

/-- A uniform-equilibrium target belongs diagonally to the executable
terminal-semantic carrier. -/
theorem diagonal_mem_terminalSemanticCarrier_of_isUniformEquilibriumPayoff
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (target : Payoff iota)
    (huniform : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    (target, target) ∈ quittingTerminalSemanticCarrier reward := by
  let error : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have herrorPos : ∀ n, 0 < error n := by
    intro n
    dsimp only [error]
    positivity
  have hexists : ∀ n, ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) (error n) profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who - target who| ≤ error n :=
    fun n ↦ exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff
      reward target huniform (herrorPos n)
  choose profiles hnash htarget using hexists
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hprescribed : Tendsto
      (fun n ↦ (quittingTerminalSemanticPair reward (profiles n)).1)
      atTop (nhds target) := by
    apply tendsto_pi_nhds.2
    intro who
    rw [Metric.tendsto_atTop]
    intro tolerance htolerance
    have heventually : ∀ᶠ n in atTop, error n < tolerance :=
      (tendsto_order.1 herror).2 tolerance htolerance
    obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
    refine ⟨threshold, fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    exact (htarget n who).trans_lt (hthreshold n hn)
  have henvelope : Tendsto
      (fun n ↦ (quittingTerminalSemanticPair reward (profiles n)).2)
      atTop (nhds target) := by
    apply tendsto_pi_nhds.2
    intro who
    rw [Metric.tendsto_atTop]
    intro tolerance htolerance
    have heventually : ∀ᶠ n in atTop, 2 * error n < tolerance := by
      have htwo : Tendsto (fun n ↦ 2 * error n) atTop (nhds 0) := by
        simpa using herror.const_mul 2
      exact (tendsto_order.1 htwo).2 tolerance htolerance
    obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
    refine ⟨threshold, fun n hn ↦ ?_⟩
    let prescribed := quittingTerminalPayoff reward (profiles n) who
    let envelope := quittingContinuationBestResponseValue reward (profiles n) who
    have hlower : prescribed ≤ envelope := by
      have hdebt := quittingTerminalDeviationDebt_nonneg reward (profiles n) who
      dsimp only [quittingTerminalDeviationDebt] at hdebt
      exact sub_nonneg.mp hdebt
    letI : Nonempty ((quittingGame reward).BehaviorStrategy who) :=
      ⟨profiles n who⟩
    have hupper : envelope ≤ prescribed + error n := by
      dsimp only [envelope, prescribed]
      unfold quittingContinuationBestResponseValue
      apply csSup_le (Set.range_nonempty _)
      rintro payoff ⟨deviation, rfl⟩
      exact hnash n who deviation
    have hclose : |prescribed - target who| ≤ error n := by
      exact htarget n who
    rw [Real.dist_eq]
    calc
      |envelope - target who| =
          |(envelope - prescribed) + (prescribed - target who)| := by ring_nf
      _ ≤ |envelope - prescribed| + |prescribed - target who| :=
        abs_add_le _ _
      _ = envelope - prescribed + |prescribed - target who| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
      _ ≤ 2 * error n := by linarith
      _ < tolerance := hthreshold n hn
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun n ↦ quittingTerminalSemanticPair reward (profiles n), ?_, ?_⟩
  · intro n
    exact ⟨profiles n, rfl⟩
  · exact hprescribed.prodMk_nhds henvelope

/-- Fixed-target semantic characterization of uniform-equilibrium payoffs. -/
theorem isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (target : Payoff iota) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target ↔
      (target, target) ∈ quittingTerminalSemanticCarrier reward := by
  constructor
  · exact diagonal_mem_terminalSemanticCarrier_of_isUniformEquilibriumPayoff
      reward target
  · exact isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
      target

/-- Target-free approximate-equilibrium existence is exactly existence of a
diagonal terminal-semantic carrier point. -/
theorem quittingApproximateEquilibriumExistence_iff_exists_diagonal_mem_terminalSemanticCarrier
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota) :
    QuittingApproximateEquilibriumExistence reward ↔
      ∃ target : Payoff iota,
        (target, target) ∈ quittingTerminalSemanticCarrier reward := by
  rw [quittingApproximateEquilibriumExistence_iff_exists_uniformEquilibriumPayoff]
  apply exists_congr
  intro target
  exact isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier
    reward target

namespace QuittingLCPClassification

/-- The arbitrary-never AKRS premise is exactly diagonal-carrier
nonemptiness for the normalized zero-never table. -/
theorem
    QuittingPayoffTable.approximateEquilibriumExistence_iff_exists_diagonalCarrierPoint
    [Nonempty iota]
    (table : QuittingPayoffTable iota) :
    table.ApproximateEquilibriumExistence ↔
      ∃ target : Payoff iota,
        (target, target) ∈
          quittingTerminalSemanticCarrier table.zeroNeverReward := by
  rw [table.approximateEquilibriumExistence_iff_zeroNever,
    quittingApproximateEquilibriumExistence_iff_exists_diagonal_mem_terminalSemanticCarrier]

end QuittingLCPClassification
end GameTheory
