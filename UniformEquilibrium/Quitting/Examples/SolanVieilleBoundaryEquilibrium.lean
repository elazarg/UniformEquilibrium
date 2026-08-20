/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Solan–Vieille boundary table has a uniform-equilibrium payoff

The four-player table of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Section 3, is fixed in
`GameTheory.SolanVieilleBoundary.boundaryReward`.  This module exposes, under
that table's own name, the exact period-two cross-pair equilibrium built in
`GameTheory.FourPlayerPairedSingleton`.

The profile alternates two simultaneous quitters per stage: players `0` and
`2` mix at one phase and players `1` and `3` mix at the other, with
continuation probabilities `FourPlayerPairedSingleton.periodTwoParameter` and
`FourPlayerPairedSingleton.periodTwoSecondary`.  Its payoff is
`crossBlockPayoff`.

The module also records the elimination of the primary continuation
probability between the two active-phase identities
`FourPlayerPairedSingleton.periodTwo_active_identity_first` and
`FourPlayerPairedSingleton.periodTwo_active_identity_second`.  That
elimination exposes `crossBlockQuartic` as the polynomial selecting the
secondary continuation probability, isolated by an exact sign change on
`[73/100, 74/100]`, and it sharpens the rational isolation of both
continuation probabilities enough to localize every payoff coordinate.

The localizations separate the two off-phase coordinates
(`crossBlockPayoff_three_lt_crossBlockPayoff_one`): the equilibrium pays the
two off-phase players different amounts, and its payoff vector is not constant
across players.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open StochasticGame
open FourPlayerPairedSingleton (periodTwoParameter periodTwoSecondary
  periodTwoPolynomial oddValue)

/-! ## The selecting quartic for the secondary continuation probability -/

/-- The quartic obtained by eliminating the primary continuation probability
between the two active-phase identities. -/
def crossBlockQuartic (x : ℝ) : ℝ :=
  27 * x ^ 4 + 13 * x ^ 3 - 22 * x ^ 2 - 7 * x + 4

theorem crossBlockQuartic_seventyThree_hundredths :
    crossBlockQuartic ((73 : ℝ) / 100) = -10905393 / 100000000 := by
  norm_num [crossBlockQuartic]

theorem crossBlockQuartic_seventyFour_hundredths :
    crossBlockQuartic ((74 : ℝ) / 100) = 856797 / 6250000 := by
  norm_num [crossBlockQuartic]

/-- Eliminating the primary continuation probability between the two
active-phase identities leaves the selecting quartic together with the
extraneous all-Continue factor `1 - x`. -/
theorem crossBlockQuartic_elimination (x : ℝ) :
    (3 * x ^ 2 + x - 1) ^ 2 * (4 - 3 * x) - (2 * x ^ 2 + x) ^ 2 =
      (1 - x) * crossBlockQuartic x := by
  unfold crossBlockQuartic
  ring

/-- The selecting quartic has a root in the explicit rational isolation
interval `(73/100, 74/100)`. -/
theorem exists_crossBlockQuartic_root_mem_isolatingInterval :
    ∃ x : ℝ, x ∈ Set.Ioo ((73 : ℝ) / 100) (74 / 100) ∧ crossBlockQuartic x = 0 := by
  have hleft : crossBlockQuartic ((73 : ℝ) / 100) < 0 := by
    rw [crossBlockQuartic_seventyThree_hundredths]
    norm_num
  have hright : 0 < crossBlockQuartic ((74 : ℝ) / 100) := by
    rw [crossBlockQuartic_seventyFour_hundredths]
    norm_num
  have hcontinuous : ContinuousOn crossBlockQuartic
      (Set.Icc ((73 : ℝ) / 100) (74 / 100)) := by
    unfold crossBlockQuartic
    fun_prop
  obtain ⟨x, hxIcc, hxroot⟩ :=
    intermediate_value_Icc
      (by norm_num : (73 : ℝ) / 100 ≤ 74 / 100)
      hcontinuous ⟨hleft.le, hright.le⟩
  refine ⟨x, ⟨?_, ?_⟩, hxroot⟩
  · exact lt_of_le_of_ne hxIcc.1 fun h ↦ by
      subst x
      linarith
  · exact lt_of_le_of_ne hxIcc.2 fun h ↦ by
      subst x
      linarith

/-- The secondary continuation probability is a root of the selecting
quartic. -/
theorem crossBlockQuartic_periodTwoSecondary :
    crossBlockQuartic periodTwoSecondary = 0 := by
  have hfirst := FourPlayerPairedSingleton.periodTwo_active_identity_first
  have hsecond := FourPlayerPairedSingleton.periodTwo_active_identity_second
  have hlinear :
      3 * periodTwoSecondary ^ 2 + periodTwoSecondary - 1 =
        periodTwoParameter * (2 * periodTwoSecondary ^ 2 + periodTwoSecondary) := by
    linear_combination hfirst
  have hkey :
      (3 * periodTwoSecondary ^ 2 + periodTwoSecondary - 1) ^ 2 *
          (4 - 3 * periodTwoSecondary) -
        (2 * periodTwoSecondary ^ 2 + periodTwoSecondary) ^ 2 = 0 := by
    rw [hlinear]
    linear_combination
      (2 * periodTwoSecondary ^ 2 + periodTwoSecondary) ^ 2 * hsecond
  rw [crossBlockQuartic_elimination] at hkey
  have hne : (1 : ℝ) - periodTwoSecondary ≠ 0 := by
    have h := FourPlayerPairedSingleton.periodTwoSecondary_lt_one
    linarith
  exact (mul_eq_zero.mp hkey).resolve_left hne

/-! ## Sharpened rational isolation of both continuation probabilities -/

theorem periodTwoPolynomial_threeSeventyThree_fiveHundredths :
    periodTwoPolynomial ((373 : ℝ) / 500) = -8984331 / 3906250000 := by
  norm_num [FourPlayerPairedSingleton.periodTwoPolynomial]

theorem periodTwoPolynomial_sevenFortySeven_thousandths :
    periodTwoPolynomial ((747 : ℝ) / 1000) = 5348719641 / 250000000000 := by
  norm_num [FourPlayerPairedSingleton.periodTwoPolynomial]

/-- The primary continuation probability lies in the sharpened rational
interval `(373/500, 747/1000)`. -/
theorem periodTwoParameter_mem_sharpInterval :
    periodTwoParameter ∈ Set.Ioo ((373 : ℝ) / 500) (747 / 1000) := by
  have hcoarse := FourPlayerPairedSingleton.periodTwoParameter_mem_isolatingInterval
  have hroot := FourPlayerPairedSingleton.periodTwoParameter_root
  have hmem : periodTwoParameter ∈ Set.Icc ((7 : ℝ) / 10) 1 := by
    constructor
    · have := hcoarse.1
      norm_num at this ⊢
      linarith
    · have := hcoarse.2
      norm_num at this ⊢
      linarith
  have hlow : ((373 : ℝ) / 500) ∈ Set.Icc ((7 : ℝ) / 10) 1 := by norm_num
  have hhigh : ((747 : ℝ) / 1000) ∈ Set.Icc ((7 : ℝ) / 10) 1 := by norm_num
  constructor
  · refine (FourPlayerPairedSingleton.periodTwoPolynomial_strictMonoOn.lt_iff_lt
      hlow hmem).mp ?_
    rw [periodTwoPolynomial_threeSeventyThree_fiveHundredths, hroot]
    norm_num
  · refine (FourPlayerPairedSingleton.periodTwoPolynomial_strictMonoOn.lt_iff_lt
      hmem hhigh).mp ?_
    rw [periodTwoPolynomial_sevenFortySeven_thousandths, hroot]
    norm_num

/-- The secondary continuation probability lies in the rational isolation
interval of the selecting quartic. -/
theorem periodTwoSecondary_mem_isolatingInterval :
    periodTwoSecondary ∈ Set.Ioo ((73 : ℝ) / 100) (74 / 100) := by
  have hsharp := periodTwoParameter_mem_sharpInterval
  have hpos := FourPlayerPairedSingleton.periodTwoParameter_pos
  have hden : 0 < 3 * periodTwoParameter ^ 2 := by positivity
  have hlowSq : ((373 : ℝ) / 500) ^ 2 < periodTwoParameter ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self (by norm_num) hsharp.1
  have hhighSq : periodTwoParameter ^ 2 < ((747 : ℝ) / 1000) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self hpos.le hsharp.2
  constructor
  · rw [show periodTwoSecondary =
        (4 * periodTwoParameter ^ 2 - 1) / (3 * periodTwoParameter ^ 2) from rfl,
      lt_div_iff₀ hden]
    norm_num at hlowSq ⊢
    linarith
  · rw [show periodTwoSecondary =
        (4 * periodTwoParameter ^ 2 - 1) / (3 * periodTwoParameter ^ 2) from rfl,
      div_lt_iff₀ hden]
    norm_num at hhighSq ⊢
    linarith

/-- The two continuation probabilities are distinct: the isolation intervals
`(73/100, 74/100)` and `(373/500, 747/1000)` are disjoint, and the secondary
one is the smaller. -/
theorem periodTwoSecondary_lt_periodTwoParameter :
    periodTwoSecondary < periodTwoParameter := by
  have hsecondary := periodTwoSecondary_mem_isolatingInterval
  have hprimary := periodTwoParameter_mem_sharpInterval
  have h2 := hsecondary.2
  have h1 := hprimary.1
  norm_num at h1 h2
  linarith

/-! ## The uniform-equilibrium payoff -/

/-- The payoff of the period-two cross-pair profile.  Players `0` and `2`
receive their common solo exit value `1`; the two off-phase players receive
the reciprocals of the continuation probabilities. -/
def crossBlockPayoff : Payoff Player :=
  ![1, 1 / periodTwoSecondary, 1, 1 / periodTwoParameter]

theorem crossBlockPayoff_eq_oddValue : crossBlockPayoff = oddValue := rfl

@[simp] theorem crossBlockPayoff_zero : crossBlockPayoff 0 = 1 := rfl

@[simp] theorem crossBlockPayoff_two : crossBlockPayoff 2 = 1 := rfl

/-- The two off-phase coordinates strictly exceed the common solo exit value
`1`: the players scheduled to mix at the other phase do strictly better by
continuing than by taking their own solo exit. -/
theorem one_lt_crossBlockPayoff_one : 1 < crossBlockPayoff 1 := by
  have hpos := FourPlayerPairedSingleton.periodTwoSecondary_pos
  have hlt := FourPlayerPairedSingleton.periodTwoSecondary_lt_one
  show (1 : ℝ) < 1 / periodTwoSecondary
  rw [lt_div_iff₀ hpos]
  linarith

theorem one_lt_crossBlockPayoff_three : 1 < crossBlockPayoff 3 := by
  have hpos := FourPlayerPairedSingleton.periodTwoParameter_pos
  have hlt := FourPlayerPairedSingleton.periodTwoParameter_lt_one
  show (1 : ℝ) < 1 / periodTwoParameter
  rw [lt_div_iff₀ hpos]
  linarith

/-- Rational localization of the second payoff coordinate. -/
theorem crossBlockPayoff_one_mem :
    crossBlockPayoff 1 ∈ Set.Ioo ((135 : ℝ) / 100) (137 / 100) := by
  have hmem := periodTwoSecondary_mem_isolatingInterval
  have hpos := FourPlayerPairedSingleton.periodTwoSecondary_pos
  show (1 : ℝ) / periodTwoSecondary ∈ _
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith [hmem.2]
  · rw [div_lt_iff₀ hpos]
    nlinarith [hmem.1]

/-- Rational localization of the fourth payoff coordinate. -/
theorem crossBlockPayoff_three_mem :
    crossBlockPayoff 3 ∈ Set.Ioo ((133 : ℝ) / 100) (135 / 100) := by
  have hmem := periodTwoParameter_mem_sharpInterval
  have hpos := FourPlayerPairedSingleton.periodTwoParameter_pos
  show (1 : ℝ) / periodTwoParameter ∈ _
  constructor
  · rw [lt_div_iff₀ hpos]
    nlinarith [hmem.2]
  · rw [div_lt_iff₀ hpos]
    nlinarith [hmem.1]

/-- **The two off-phase players are paid differently.**  The localizations of
the two off-phase coordinates abut exactly at `135/100`, so the coordinate
carrying the secondary continuation probability is strictly the larger.  The
period-two cross-pair profile therefore treats the players scheduled to mix at
the two phases asymmetrically even though the schedule is symmetric between
the phases. -/
theorem crossBlockPayoff_three_lt_crossBlockPayoff_one :
    crossBlockPayoff 3 < crossBlockPayoff 1 := by
  have hone := crossBlockPayoff_one_mem
  have hthree := crossBlockPayoff_three_mem
  have h1 := hone.1
  have h3 := hthree.2
  linarith

/-- **The equilibrium payoff is not constant across players.**  Coordinates
`0` and `2` receive the common solo exit value `1` while the other two receive
strictly more, so no single number is the payoff of every player.  This is a
statement about this equilibrium payoff, not about the table: it does not by
itself decide whether `boundaryReward` is symmetric. -/
theorem not_exists_forall_crossBlockPayoff_eq :
    ¬ ∃ c : ℝ, ∀ who : Player, crossBlockPayoff who = c := by
  rintro ⟨c, hc⟩
  have hzero := hc 0
  have hone := hc 1
  have hlt := one_lt_crossBlockPayoff_one
  rw [crossBlockPayoff_zero] at hzero
  rw [hone] at hlt
  linarith

/-- **The Solan–Vieille boundary table has a uniform-equilibrium payoff.** -/
theorem boundaryReward_isUniformEquilibriumPayoff :
    (quittingGame boundaryReward).IsUniformEquilibriumPayoff none crossBlockPayoff :=
  FourPlayerPairedSingleton.periodTwo_isUniformEquilibriumPayoff

theorem boundaryReward_exists_uniformEquilibriumPayoff :
    ∃ payoff : Payoff Player,
      (quittingGame boundaryReward).IsUniformEquilibriumPayoff none payoff :=
  ⟨crossBlockPayoff, boundaryReward_isUniformEquilibriumPayoff⟩

/-- The table has no positive terminal exploitability gap. -/
theorem boundaryReward_not_hasTerminalExploitabilityGap {gap : ℝ} (hgap : 0 < gap) :
    ¬ HasTerminalExploitabilityGap boundaryReward gap := fun hexploit ↦
  quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    boundaryReward hgap hexploit boundaryReward_exists_uniformEquilibriumPayoff

/-- The table has zero canonical semantic min-max terminal exploitability. -/
theorem boundaryReward_terminalExploitabilityInf_eq_zero :
    quittingTerminalExploitabilityInf boundaryReward = 0 :=
  FourPlayerPairedSingleton.periodTwo_terminalExploitabilityInf_eq_zero

end SolanVieilleBoundary

end GameTheory
