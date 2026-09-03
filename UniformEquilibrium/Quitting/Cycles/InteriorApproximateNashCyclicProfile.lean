/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.EndogenousInteriorCyclicBlock
import UniformEquilibrium.Quitting.Cycles.PeriodicApproximateNashDeviationCap
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Terminal profiles from interior approximate-Nash cyclic blocks

Strict interiority makes every nonempty-player block jointly absorbing.  With
at least two players it also makes each player-deleted cycle contracting, so
the local root error feeds the unrestricted behavioral deviation cap.  The
last theorem consumes any fixed-payoff limit whose exact playerwise cyclic
caps vanish.

For a singleton player type, joint absorption and the realized-payoff theorem
remain true, but player-deleted survival is one.  The playerwise cap theorem
is therefore intentionally stated under `Nontrivial ι`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Set StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [DecidableEq ι] in
/-- Positive Quit probability at one coordinate makes a product root absorb
with positive probability. -/
theorem quittingRootAbsorptionMass_pos_of_positive_quitProbability
    (root : ι → PMF Bool) (who : ι)
    (hquit : 0 < (root who true).toReal) :
    0 < quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

/-- Positive Quit probability of an opponent makes the corresponding
player-deleted root absorb with positive probability. -/
theorem quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
    (root : ι → PMF Bool) {who other : ι} (hne : other ≠ who)
    (hquit : 0 < (root other true).toReal) :
    quittingStationaryFixedOpponentsContinueMass root who < 1 := by
  have hcontinue := quittingStationaryContinueMass_le_ownContinueProbability
    (Function.update root who (PMF.pure false)) other
  rw [Function.update_of_ne hne] at hcontinue
  have hsum := quittingRoot_continueProbability_add_quitProbability root other
  change quittingStationaryContinueMass
    (Function.update root who (PMF.pure false)) < 1
  linarith

/-- Every interior cyclic block is jointly absorbing over one turn. -/
theorem InteriorApproximateNashCyclicBlock.prod_continueMass_lt_one
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error) :
    (∏ phase : Fin (m + 1),
      quittingStationaryContinueMass (block.cycle phase)) < 1 := by
  let who : ι := Classical.choice inferInstance
  exact prod_quittingStationaryContinueMass_univ_lt_one_of_absorbing
    block.cycle 0
      (quittingRootAbsorptionMass_pos_of_positive_quitProbability
        (block.cycle 0) who (block.quitProbability_pos 0 who))

/-- Exact Bellman return in an interior block is the actual terminal payoff
of its repeated cyclic profile. -/
theorem InteriorApproximateNashCyclicBlock.value_eq_cyclicTerminalValue
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error) :
    block.value = quittingCyclicTerminalValue reward block.cycle :=
  eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing
    reward block.cycle block.value block.bellman block.prod_continueMass_lt_one

/-- Local approximate Nash in an interior block is literally against the
actual next-phase terminal value. -/
theorem InteriorApproximateNashCyclicBlock.rootNash_cyclicTerminalValue
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (phase : Fin (m + 1)) :
    IsεQuittingRootNash reward
      (quittingCyclicTerminalValue reward block.cycle
        (finRotate (m + 1) phase)) error (block.cycle phase) := by
  rw [← block.value_eq_cyclicTerminalValue]
  exact block.rootNash phase

/-- With at least two players, strict interiority contracts every player's
opponent-only survival product over a turn. -/
theorem InteriorApproximateNashCyclicBlock.prod_fixedOpponentsContinueMass_lt_one
    [Nontrivial ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error) (who : ι) :
    (∏ phase : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (block.cycle phase) who) < 1 := by
  obtain ⟨other, hother⟩ := exists_ne who
  apply Math.Finset.prod_lt_one_of_mem Finset.univ
    (fun phase : Fin (m + 1) ↦
      quittingStationaryFixedOpponentsContinueMass
        (block.cycle phase) who) 0
  · exact Finset.mem_univ 0
  · intro phase _ _
    exact quittingStationaryFixedOpponentsContinueMass_nonneg
      (block.cycle phase) who
  · intro phase _ _
    change quittingStationaryContinueMass
      (Function.update (block.cycle phase) who (PMF.pure false)) ≤ 1
    exact quittingStationaryContinueMass_le_one _
  · exact
      quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
        (block.cycle 0) hother (block.quitProbability_pos 0 other)

/-- Probability that at least one opponent of `who` quits during one turn of
a cyclic product profile. -/
def quittingCyclicOpponentAbsorptionMass
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) (who : ι) : ℝ :=
  1 - ∏ phase : Fin K,
    quittingStationaryFixedOpponentsContinueMass (cycle phase) who

/-- Probability that `who` quits at least once during one turn of a cyclic
product profile. -/
def quittingCyclicPlayerAbsorptionMass
    {K : ℕ} (cycle : Fin K → ι → PMF Bool) (who : ι) : ℝ :=
  1 - ∏ phase : Fin K, (cycle phase who false).toReal

/-- Player-deleted absorption is positive for every player of an interior
cyclic block with at least two players. -/
theorem InteriorApproximateNashCyclicBlock.opponentAbsorptionMass_pos
    [Nontrivial ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error) (who : ι) :
    0 < quittingCyclicOpponentAbsorptionMass block.cycle who := by
  unfold quittingCyclicOpponentAbsorptionMass
  exact sub_pos.mpr (block.prod_fixedOpponentsContinueMass_lt_one who)

/-- The unrestricted terminal deviation debt of the cyclic profile has the
exact period-error over player-deleted absorption bound. -/
theorem InteriorApproximateNashCyclicBlock.terminalDeviationDebt_le
    [Nontrivial ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error : ℝ} (herror : 0 ≤ error)
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (initial : Fin (m + 1)) (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingCyclicBehaviorProfile reward block.cycle initial) who ≤
      ((m + 1 : ℕ) : ℝ) * error /
        (1 - ∏ phase : Fin (m + 1),
          quittingStationaryFixedOpponentsContinueMass
            (block.cycle phase) who) := by
  exact
    quittingTerminalDeviationDebt_cyclicBehaviorProfile_le_card_mul_error_div_opponentAbsorption
      reward block.cycle herror block.rootNash_cyclicTerminalValue initial who
        (block.prod_fixedOpponentsContinueMass_lt_one who)

/-- A positive terminal-debt floor forces the exact player-deleted absorption
denominator of an interior cyclic block below period times local error divided
by that floor. -/
theorem InteriorApproximateNashCyclicBlock.opponentAbsorptionMass_le_of_debt_floor
    [Nontrivial ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {error debtFloor : ℝ} (herror : 0 ≤ error) (hdebtFloor : 0 < debtFloor)
    (block : InteriorApproximateNashCyclicBlock reward m error)
    (initial : Fin (m + 1)) (who : ι)
    (hdebt : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingCyclicBehaviorProfile reward block.cycle initial) who) :
    quittingCyclicOpponentAbsorptionMass block.cycle who ≤
      ((m + 1 : ℕ) : ℝ) * error / debtFloor := by
  have habsorption := block.opponentAbsorptionMass_pos who
  have hcap := block.terminalDeviationDebt_le herror initial who
  have hquotient : debtFloor ≤
      ((m + 1 : ℕ) : ℝ) * error /
        quittingCyclicOpponentAbsorptionMass block.cycle who := by
    unfold quittingCyclicOpponentAbsorptionMass
    exact hdebt.trans hcap
  apply (le_div_iff₀ hdebtFloor).2
  have hmul := (le_div_iff₀ habsorption).1 hquotient
  nlinarith

/-- On a singleton player type, deleting the only player leaves the
all-Continue root, so the player-deleted survival product is exactly one.
This records explicitly why the preceding deviation-cap denominator needs
at least two players. -/
theorem prod_fixedOpponentsContinueMass_eq_one_of_subsingleton
    [Subsingleton ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {error : ℝ}
    (block : InteriorApproximateNashCyclicBlock reward m error) (who : ι) :
    (∏ phase : Fin (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (block.cycle phase) who) = 1 := by
  apply Finset.prod_eq_one
  intro phase _
  apply le_antisymm
  · change quittingStationaryContinueMass
      (Function.update (block.cycle phase) who (PMF.pure false)) ≤ 1
    exact quittingStationaryContinueMass_le_one _
  · have hall : Function.update (block.cycle phase) who (PMF.pure false) =
        (fun _ : ι ↦ PMF.pure false) := by
      funext player
      rw [Subsingleton.elim player who, Function.update_self]
    change 1 ≤ quittingStationaryContinueMass
      (Function.update (block.cycle phase) who (PMF.pure false))
    rw [hall, quittingStationaryContinueMass_eq_prod_continueProbability]
    simp

/-- Vanishing exact cyclic cap ratios and convergence of the actual phase
values select one fixed uniform-equilibrium payoff.  Periods may vary with
the sequence. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_interiorCyclicBlocks
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (period : ℕ → ℕ) (error : ℕ → ℝ) (herror : ∀ n, 0 ≤ error n)
    (block : ∀ n, InteriorApproximateNashCyclicBlock
      reward (period n) (error n))
    (initial : ∀ n, Fin (period n + 1)) (target : Payoff ι)
    (hcap : Tendsto (fun n who ↦
      (((period n + 1 : ℕ) : ℝ) * error n /
        (1 - ∏ phase : Fin (period n + 1),
          quittingStationaryFixedOpponentsContinueMass
            ((block n).cycle phase) who))) atTop (nhds 0))
    (htarget : Tendsto (fun n ↦ (block n).value (initial n))
      atTop (nhds target)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance
  intro requested hrequested
  have heventuallyCap : ∀ᶠ n in atTop, ∀ who,
      (((period n + 1 : ℕ) : ℝ) * error n /
        (1 - ∏ phase : Fin (period n + 1),
          quittingStationaryFixedOpponentsContinueMass
            ((block n).cycle phase) who)) < requested := by
    apply Filter.eventually_all.mpr
    intro who
    have hcoordinate := (continuous_apply who).tendsto 0 |>.comp hcap
    exact (tendsto_order.1 hcoordinate).2 requested hrequested
  have heventuallyTarget : ∀ᶠ n in atTop, ∀ who,
      |(block n).value (initial n) who - target who| < requested := by
    apply Filter.eventually_all.mpr
    intro who
    have hcoordinate : Tendsto
        (fun n ↦ (block n).value (initial n) who)
        atTop (nhds (target who)) :=
      (continuous_apply who).tendsto target |>.comp htarget
    have hball := hcoordinate.eventually
      (Metric.ball_mem_nhds (target who) hrequested)
    filter_upwards [hball] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  obtain ⟨n, hnCap, hnTarget⟩ :=
    (heventuallyCap.and heventuallyTarget).exists
  let profile := quittingCyclicBehaviorProfile reward
    (block n).cycle (initial n)
  refine ⟨profile, ?_, ?_⟩
  · intro who deviation
    have hdeviation :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who deviation
    have hdebt := (block n).terminalDeviationDebt_le
      (herror n) (initial n) who
    unfold quittingTerminalDeviationDebt at hdebt
    exact hdeviation.trans (by linarith [hnCap who])
  · intro who
    rw [quittingTerminalPayoff_cyclicBehaviorProfile,
      ← congrFun (block n).value_eq_cyclicTerminalValue (initial n)]
    exact (hnTarget who).le

end GameTheory
