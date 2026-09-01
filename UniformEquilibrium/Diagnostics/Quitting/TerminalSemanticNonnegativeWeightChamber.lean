/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-!
# Nonnegative-weight chamber at an ordinary terminal-debt minimum

This file aggregates the ordinary positive-minimum singleton margin against
one nonnegative player weight.  The minimum objective remains unweighted.
The closing theorem selects the ordinary compact-carrier minimum and invokes
the unrestricted-behavior zero-minimum consumer.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Total mass of one player weight. -/
def quittingPlayerWeightTotal (weight : ι → ℝ) : ℝ :=
  ∑ who, weight who

/-- Largest coordinate of one player weight. -/
def quittingPlayerWeightMaximum (weight : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty weight

/-- Mass outside the largest coordinate. -/
def quittingPlayerWeightOffMaximum (weight : ι → ℝ) : ℝ :=
  quittingPlayerWeightTotal weight - quittingPlayerWeightMaximum weight

/-- Weighted prescribed payoff of one terminal-semantic pair. -/
def quittingTerminalSemanticWeightedPrescribed
    (weight : ι → ℝ) (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  ∑ who, weight who * pair.1 who

/-- Weighted own-singleton reward. -/
def quittingWeightedSingletonReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) : ℝ :=
  ∑ who, weight who * reward (quittingSingletonTerminal who) who

/-- Weighted value of a terminal outcome, with Never valued at zero. -/
def quittingWeightedTerminalOutcomeReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) (outcome : QuittingTerminalOutcome ι) : ℝ :=
  ∑ who, weight who * quittingTerminalOutcomeReward reward outcome who

/-- Largest weighted value of a terminal outcome, including Never. -/
def quittingWeightedTerminalOutcomeMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingWeightedTerminalOutcomeReward reward weight)

omit [DecidableEq ι] in
theorem quittingPlayerWeight_le_maximum
    (weight : ι → ℝ) (who : ι) :
    weight who ≤ quittingPlayerWeightMaximum weight := by
  exact Finset.le_sup' weight (Finset.mem_univ who)

/-- Two distinct positive coordinates make the off-maximum weight positive. -/
theorem quittingPlayerWeightOffMaximum_pos_of_two_positive
    (weight : ι → ℝ) (first second : ι) (hne : first ≠ second)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second) :
    0 < quittingPlayerWeightOffMaximum weight := by
  obtain ⟨largest, -, hlargest⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty weight
  let other := if largest = first then second else first
  have hother_ne : other ≠ largest := by
    dsimp [other]
    split_ifs with heq
    · simpa [heq] using hne.symm
    · exact Ne.symm heq
  have hother_pos : 0 < weight other := by
    dsimp [other]
    split_ifs <;> assumption
  have hsubset : ({largest, other} : Finset ι) ⊆ Finset.univ :=
    Finset.subset_univ _
  have htwo : weight largest + weight other ≤ ∑ who, weight who := by
    calc
      weight largest + weight other =
          ∑ who ∈ ({largest, other} : Finset ι), weight who := by
            simp [Ne.symm hother_ne]
      _ ≤ ∑ who ∈ (Finset.univ : Finset ι), weight who :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun who _ _ => hweight who)
      _ = ∑ who, weight who := rfl
  rw [quittingPlayerWeightOffMaximum, quittingPlayerWeightTotal,
    quittingPlayerWeightMaximum, hlargest]
  linarith

/-- The sharp nonnegative-weight lower chamber at a positive ordinary
minimum of total terminal debt. -/
theorem minimumTerminalSemantic_nonnegativeWeight_lowerBound
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hweight : ∀ who, 0 ≤ weight who) :
    quittingWeightedSingletonReward reward weight +
        quittingPlayerWeightOffMaximum weight *
          quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticWeightedPrescribed weight pair := by
  let debt : ι → ℝ := fun who => quittingTerminalSemanticDebt pair who
  have hmargin : ∀ who,
      quittingTerminalSemanticDebtSum pair ≤ pair.2 who -
        reward (quittingSingletonTerminal who) who :=
    minimumTerminalSemantic_singletonMargin pair hpair hminimum hpositive
  have hweightedMargin :
      quittingPlayerWeightTotal weight *
          quittingTerminalSemanticDebtSum pair ≤
        ∑ who, weight who *
          (pair.2 who - reward (quittingSingletonTerminal who) who) := by
    rw [quittingPlayerWeightTotal, Finset.sum_mul]
    exact Finset.sum_le_sum fun who _ =>
      mul_le_mul_of_nonneg_left (hmargin who) (hweight who)
  have hdebtNonneg : ∀ who, 0 ≤ debt who := fun who =>
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  have hweightedDebt :
      (∑ who, weight who * debt who) ≤
        quittingPlayerWeightMaximum weight *
          quittingTerminalSemanticDebtSum pair := by
    calc
      (∑ who, weight who * debt who) ≤
          ∑ who, quittingPlayerWeightMaximum weight * debt who := by
            exact Finset.sum_le_sum fun who _ =>
              mul_le_mul_of_nonneg_right
                (quittingPlayerWeight_le_maximum weight who)
                (hdebtNonneg who)
      _ = quittingPlayerWeightMaximum weight *
          quittingTerminalSemanticDebtSum pair := by
            unfold quittingTerminalSemanticDebtSum
            rw [Finset.mul_sum]
  have hcap : ∀ who, pair.2 who = pair.1 who + debt who := by
    intro who
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  simp_rw [hcap, mul_sub, mul_add] at hweightedMargin
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hweightedMargin
  unfold quittingWeightedSingletonReward
    quittingTerminalSemanticWeightedPrescribed
    quittingPlayerWeightOffMaximum
  linarith

omit [Nonempty ι] in
/-- Every terminal-semantic carrier point has weighted prescribed value at
most the largest weighted terminal outcome, including Never. -/
theorem terminalSemantic_weightedPrescribed_le_outcomeMaximum
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticWeightedPrescribed weight pair ≤
      quittingWeightedTerminalOutcomeMaximum reward weight := by
  obtain ⟨mass, hmass, hmoment⟩ :=
    quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      reward pair hpair
  have houtcome : ∀ outcome,
      quittingWeightedTerminalOutcomeReward reward weight outcome ≤
        quittingWeightedTerminalOutcomeMaximum reward weight := fun outcome =>
    Finset.le_sup' _ (Finset.mem_univ outcome)
  have haverage :
      (∑ outcome, mass outcome *
          quittingWeightedTerminalOutcomeReward reward weight outcome) ≤
        ∑ outcome, mass outcome *
          quittingWeightedTerminalOutcomeMaximum reward weight := by
    exact Finset.sum_le_sum fun outcome _ =>
      mul_le_mul_of_nonneg_left (houtcome outcome) (hmass.1 outcome)
  have hleft :
      (∑ outcome, mass outcome *
          quittingWeightedTerminalOutcomeReward reward weight outcome) =
        quittingTerminalSemanticWeightedPrescribed weight pair := by
    unfold quittingWeightedTerminalOutcomeReward
      quittingTerminalSemanticWeightedPrescribed
    calc
      (∑ outcome, mass outcome *
          ∑ who, weight who *
            quittingTerminalOutcomeReward reward outcome who) =
          ∑ who, weight who *
            (∑ outcome, mass outcome *
              quittingTerminalOutcomeReward reward outcome who) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro who _
        apply Finset.sum_congr rfl
        intro outcome _
        ring
      _ = ∑ who, weight who * pair.1 who := by
        apply Finset.sum_congr rfl
        intro who _
        have hcoordinate := congrFun hmoment who
        unfold quittingTerminalRewardMoment at hcoordinate
        rw [hcoordinate]
  have hright :
      (∑ outcome, mass outcome *
          quittingWeightedTerminalOutcomeMaximum reward weight) =
        quittingWeightedTerminalOutcomeMaximum reward weight := by
    rw [← Finset.sum_mul, hmass.2, one_mul]
  rwa [hleft, hright] at haverage

/-- The complete sharp chamber at a positive ordinary total-debt minimum:
the nonnegative-weight singleton margin gives the lower face, and the reward
moment gives the upper face in the same theorem. -/
theorem minimumTerminalSemantic_nonnegativeWeight_chamber
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hweight : ∀ who, 0 ≤ weight who) :
    quittingWeightedSingletonReward reward weight +
          quittingPlayerWeightOffMaximum weight *
            quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticWeightedPrescribed weight pair ∧
      quittingTerminalSemanticWeightedPrescribed weight pair ≤
        quittingWeightedTerminalOutcomeMaximum reward weight := by
  exact ⟨minimumTerminalSemantic_nonnegativeWeight_lowerBound
      pair weight hpair hminimum hpositive hweight,
    terminalSemantic_weightedPrescribed_le_outcomeMaximum pair weight hpair⟩

/-- Unconditional upper bound for the debt of an ordinary global minimum.
The positive-debt proof uses the sharp chamber; the zero-debt case is
immediate. -/
theorem minimumTerminalSemantic_debtSum_le_nonnegativeWeightBound
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hweight : ∀ who, 0 ≤ weight who)
    (hgap : 0 < quittingPlayerWeightOffMaximum weight) :
    quittingTerminalSemanticDebtSum pair ≤
      max 0
        ((quittingWeightedTerminalOutcomeMaximum reward weight -
            quittingWeightedSingletonReward reward weight) /
          quittingPlayerWeightOffMaximum weight) := by
  have hdebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  by_cases hzero : quittingTerminalSemanticDebtSum pair = 0
  · rw [hzero]
    exact le_max_left _ _
  · have hpositive : 0 < quittingTerminalSemanticDebtSum pair :=
      lt_of_le_of_ne hdebtNonneg (Ne.symm hzero)
    have hlower := minimumTerminalSemantic_nonnegativeWeight_lowerBound
      pair weight hpair hminimum hpositive hweight
    have hupper := terminalSemantic_weightedPrescribed_le_outcomeMaximum
      pair weight hpair
    have hproduct : quittingPlayerWeightOffMaximum weight *
          quittingTerminalSemanticDebtSum pair ≤
        quittingWeightedTerminalOutcomeMaximum reward weight -
          quittingWeightedSingletonReward reward weight := by
      linarith
    have hdiv : quittingTerminalSemanticDebtSum pair ≤
        (quittingWeightedTerminalOutcomeMaximum reward weight -
            quittingWeightedSingletonReward reward weight) /
          quittingPlayerWeightOffMaximum weight :=
      (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hproduct)
    exact hdiv.trans (le_max_right _ _)

/-- Two distinct positive weight coordinates discharge the strict
off-maximum denominator in the unconditional debt bound. -/
theorem minimumTerminalSemantic_debtSum_le_nonnegativeWeightBound_of_two_positive
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    (first second : ι) (hne : first ≠ second)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second) :
    quittingTerminalSemanticDebtSum pair ≤
      max 0
        ((quittingWeightedTerminalOutcomeMaximum reward weight -
            quittingWeightedSingletonReward reward weight) /
          quittingPlayerWeightOffMaximum weight) := by
  exact minimumTerminalSemantic_debtSum_le_nonnegativeWeightBound
    pair weight hpair hminimum hweight
      (quittingPlayerWeightOffMaximum_pos_of_two_positive
        weight first second hne hweight hfirst hsecond)

omit [DecidableEq ι] [Nonempty ι] in
/-- The displayed reward-table inequalities bound every weighted terminal
outcome by the weighted singleton value, including Never. -/
theorem weightedTerminalOutcomeMaximum_le_singleton_of_table
    (weight : ι → ℝ)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight)
    (hterminal : ∀ terminal : {S : Finset ι // S.Nonempty},
      quittingWeightedTerminalOutcomeReward reward weight (some terminal) ≤
        quittingWeightedSingletonReward reward weight) :
    quittingWeightedTerminalOutcomeMaximum reward weight ≤
      quittingWeightedSingletonReward reward weight := by
  unfold quittingWeightedTerminalOutcomeMaximum
  apply Finset.sup'_le
  intro outcome _
  cases outcome with
  | none =>
      simpa [quittingWeightedTerminalOutcomeReward,
        quittingTerminalOutcomeReward] using hsingleton
  | some terminal => exact hterminal terminal

/-- A nonnegative weight with two positive coordinates and the literal
reward-table chamber forces the ordinary minimum debt to be zero. -/
theorem hasZeroMinimumTerminalSemanticDebt_of_nonnegativeWeightChamber
    (weight : ι → ℝ) (first second : ι) (hne : first ≠ second)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight)
    (hterminal : ∀ terminal : {S : Finset ι // S.Nonempty},
      quittingWeightedTerminalOutcomeReward reward weight (some terminal) ≤
        quittingWeightedSingletonReward reward weight) :
    HasZeroMinimumTerminalSemanticDebt reward := by
  obtain ⟨pair, hpair, hminimum⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  have hdebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  have hgap := quittingPlayerWeightOffMaximum_pos_of_two_positive
    weight first second hne hweight hfirst hsecond
  have houtcome := weightedTerminalOutcomeMaximum_le_singleton_of_table
    weight hsingleton hterminal
  have hzero : quittingTerminalSemanticDebtSum pair = 0 := by
    by_contra hneZero
    have hpositive : 0 < quittingTerminalSemanticDebtSum pair :=
      lt_of_le_of_ne hdebtNonneg (Ne.symm hneZero)
    have hlower := minimumTerminalSemantic_nonnegativeWeight_lowerBound
      pair weight hpair hminimum hpositive hweight
    have hupper := terminalSemantic_weightedPrescribed_le_outcomeMaximum
      pair weight hpair
    have : 0 < quittingPlayerWeightOffMaximum weight *
        quittingTerminalSemanticDebtSum pair := mul_pos hgap hpositive
    linarith
  exact ⟨pair, hpair, hminimum, hzero⟩

/-- The nonnegative-weight reward-table chamber has a uniform-equilibrium
payoff against unrestricted unilateral behavioral deviations. -/
theorem exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber
    (weight : ι → ℝ) (first second : ι) (hne : first ≠ second)
    (hweight : ∀ who, 0 ≤ weight who)
    (hfirst : 0 < weight first) (hsecond : 0 < weight second)
    (hsingleton : 0 ≤ quittingWeightedSingletonReward reward weight)
    (hterminal : ∀ terminal : {S : Finset ι // S.Nonempty},
      quittingWeightedTerminalOutcomeReward reward weight (some terminal) ≤
        quittingWeightedSingletonReward reward weight) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt reward
    (hasZeroMinimumTerminalSemanticDebt_of_nonnegativeWeightChamber
      weight first second hne hweight hfirst hsecond hsingleton hterminal)

end GameTheory
