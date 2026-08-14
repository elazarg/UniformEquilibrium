/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticWeightedAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import MathUE.BonferroniProductBounds
import UniformEquilibrium.Quitting.RewardBound

/-!
# Singular weighted-debt limits and a source-matched singleton insertion experiment

The positive-costate moat can be sent to a boundary costate.  Giving one
player weight tending to zero and every other player weight one produces a
carrier point whose debt is supported on that one coordinate.  This is a
compactness consequence of the existing weighted singleton-margin theorem,
not a new case split.

For a quitting counterexample, applying this construction to a player with
positive singleton reward and then using the unavoidable singleton-insertion
toggle gives one source-matched row: the insertion gain and the singleton
incidence are evaluated at the same root and against the same axis source.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The singular positive costate used to isolate the debt of `owner`. -/
def quittingDebtAxisCostate (owner : ι) (index : ℕ) : Payoff ι :=
  fun who => if who = owner then 1 / ((index : ℝ) + 1) else 1

omit [Fintype ι] in
theorem quittingDebtAxisCostate_pos (owner : ι) (index : ℕ) (who : ι) :
    0 < quittingDebtAxisCostate owner index who := by
  by_cases hwho : who = owner
  · rw [quittingDebtAxisCostate, if_pos hwho]
    positivity
  · rw [quittingDebtAxisCostate, if_neg hwho]
    norm_num

omit [Fintype ι] in
theorem quittingDebtAxisCostate_owner (owner : ι) (index : ℕ) :
    quittingDebtAxisCostate owner index owner = 1 / ((index : ℝ) + 1) := by
  simp [quittingDebtAxisCostate]

omit [DecidableEq ι] in
theorem continuous_quittingTerminalSemanticWeightedDebtSum
    (theta : Payoff ι) :
    Continuous (quittingTerminalSemanticWeightedDebtSum theta :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticWeightedDebtSum
  exact continuous_finsetSum (s := (Finset.univ : Finset ι)) fun who _ =>
    continuous_const.mul (continuous_quittingTerminalSemanticDebt who)

/-! ## Exact row accounting used by the critical-pair audit -/

/-- If the envelope endpoint selects Continue, one coordinate of prefixed
debt is exactly transported tail debt plus the displayed probability of Quit
times the Continue-minus-Quit endpoint difference at the prescribed tail.
This is the semantic version of the one-row identity used in the weighted
argument. -/
theorem quittingTerminalSemanticDebt_prefix_eq_of_capContinue
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool) (who : ι)
    (hcapContinue :
      quittingRootQuitPayoff reward pair.1 root who ≤
        quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who +
        (root who true).toReal *
          (quittingRootContinuePayoff reward pair.1 root who -
            quittingRootQuitPayoff reward pair.1 root who) := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinueEnvelope :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueValue + quittingRootOpponentContinueMass root who * debt := by
    rw [henvelope, quittingRootContinuePayoff_update_add]
  have hprob := quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [max_eq_right hcapContinue,
    quittingRootSuccessorPayoff_eq_endpointMix, hcontinueEnvelope]
  change continueValue + quittingRootOpponentContinueMass root who * debt -
      ((root who true).toReal * quitValue +
        (root who false).toReal * continueValue) =
    quittingRootOpponentContinueMass root who * debt +
      (root who true).toReal * (continueValue - quitValue)
  have hfalse : (root who false).toReal = 1 - (root who true).toReal := by
    linarith
  rw [hfalse]
  ring

/-- The alleged critical-pair second-order term is algebraically exact once
the cap-Continue coordinate formulas have been established.  In particular,
there is no omitted first-order term: the two critical singleton margins
cancel it. -/
theorem criticalPair_secondOrder_accounting
    (minimumDebt firstHazard secondHazard firstDebt secondDebt
      firstRefusal secondRefusal : ℝ) :
    (1 - firstHazard) * (1 - secondHazard) *
          (minimumDebt - firstDebt - secondDebt) +
        ((1 - firstHazard) * (1 - secondHazard) * firstDebt +
          firstHazard * (1 - secondHazard) * minimumDebt +
          firstHazard * secondHazard * firstRefusal) +
        ((1 - firstHazard) * (1 - secondHazard) * secondDebt +
          secondHazard * (1 - firstHazard) * minimumDebt +
          firstHazard * secondHazard * secondRefusal) -
        minimumDebt =
      firstHazard * secondHazard *
        (firstRefusal + secondRefusal - minimumDebt) := by
  ring

/-- Therefore global minimality along one positive critical-pair square
forces the aggregate refusal coefficient to be at least the minimum debt.
-/
theorem criticalPair_refusal_ge_minimumDebt
    {minimumDebt firstHazard secondHazard firstRefusal secondRefusal : ℝ}
    (hfirst : 0 < firstHazard) (hsecond : 0 < secondHazard)
    (hminimal : 0 ≤ firstHazard * secondHazard *
      (firstRefusal + secondRefusal - minimumDebt)) :
    minimumDebt ≤ firstRefusal + secondRefusal := by
  have hproduct : 0 < firstHazard * secondHazard := mul_pos hfirst hsecond
  nlinarith

/-! ## The open cap-Continue neighborhood -/

/-- Continue-minus-Quit at the envelope coordinate. -/
def quittingTerminalSemanticCapContinueGap
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (who : ι) : ℝ :=
  quittingRootContinuePayoff reward pair.2 root who -
    quittingRootQuitPayoff reward pair.2 root who

/-- The envelope cap gap changes by at most four reward bounds times the
probability that an opponent quits. -/
theorem abs_quittingTerminalSemanticCapContinueGap_sub_singletonMargin_le
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbox : pair ∈ quittingTerminalSemanticBox ι M) :
    |quittingTerminalSemanticCapContinueGap (reward := reward) pair root who -
        (pair.2 who - reward (quittingSingletonTerminal who) who)| ≤
      4 * M * quittingRootOpponentAbsorptionMass root who := by
  let mass := quittingRootOpponentAbsorptionMass root who
  let margin := pair.2 who - reward (quittingSingletonTerminal who) who
  let joining := quittingOutsiderJoiningContribution reward root who
  have hmassNonneg : 0 ≤ mass :=
    quittingRootOpponentAbsorptionMass_nonneg root who
  have hmarginAbs : |margin| ≤ 2 * M := by
    dsimp only [margin]
    calc
      |pair.2 who - reward (quittingSingletonTerminal who) who| ≤
          |pair.2 who| +
            |reward (quittingSingletonTerminal who) who| := abs_sub _ _
      _ ≤ M + M := add_le_add (abs_le.mpr ⟨(hbox.2.1 who), hbox.2.2 who⟩)
        (hreward (quittingSingletonTerminal who) who)
      _ = 2 * M := by ring
  have hscaled : |mass * margin| ≤ 2 * M * mass := by
    rw [abs_mul, abs_of_nonneg hmassNonneg]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hmarginAbs hmassNonneg)
  have hjoining : |joining| ≤ 2 * M * mass := by
    simpa [joining, mass] using
      abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
        reward root who hreward
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever reward pair.2 root who
  have hmassEq : quittingRootAbsorptionMass
      (Function.update root who (PMF.pure false)) = mass := rfl
  rw [hmassEq] at hdecomposition
  have hdecomposition' :
      quittingRootEndpointDifference reward pair.2 root who =
        -(1 - mass) * margin + joining := by
    dsimp only [mass, margin, joining]
    rw [hdecomposition]
    ring
  dsimp only [quittingTerminalSemanticCapContinueGap]
  have hgap :
      quittingRootContinuePayoff reward pair.2 root who -
          quittingRootQuitPayoff reward pair.2 root who - margin =
        -(quittingRootEndpointDifference reward pair.2 root who) - margin := by
    unfold quittingRootEndpointDifference
    ring
  rw [hgap]
  rw [hdecomposition']
  have hidentity : -(-(1 - mass) * margin + joining) - margin =
      -(mass * margin) - joining := by ring
  rw [hidentity]
  calc
    |-(mass * margin) - joining| ≤ |mass * margin| + |joining| :=
      (abs_sub _ _).trans_eq (by rw [abs_neg])
    _ ≤ 2 * M * mass + 2 * M * mass := add_le_add hscaled hjoining
    _ = 4 * M * mass := by ring

/-- Opponent absorption is bounded by the sum of all displayed quit
probabilities. -/
theorem quittingRootOpponentAbsorptionMass_le_sum_quitProbability
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentAbsorptionMass root who ≤
      ∑ player, (root player true).toReal := by
  have hle := quittingRootOpponentAbsorptionMass_le_absorptionMass root who
  have habsorption : quittingRootAbsorptionMass root ≤
      ∑ player, (root player true).toReal := by
    rw [quittingRootAbsorptionMass,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    have hfalse : ∀ player,
        (root player false).toReal = 1 - (root player true).toReal := by
      intro player
      have hprob := quittingRoot_continueProbability_add_quitProbability
        root player
      linarith
    simp_rw [hfalse]
    exact Math.one_sub_prod_one_sub_le_sum
      (fun player => (root player true).toReal) Finset.univ
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun player _ => ENNReal.toReal_mono ENNReal.one_ne_top
        ((root player).coe_le_one true))
  exact hle.trans habsorption

/-- A strict positive singleton margin gives a uniform cap-Continue
neighborhood.  The `M = 0` case is automatically excluded by the positive
margin and the semantic box. -/
theorem half_minimumDebt_le_capContinueGap_of_small_root
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (who : ι) {minimumDebt M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbox : pair ∈ quittingTerminalSemanticBox ι M)
    (hminimumDebt : 0 < minimumDebt)
    (hmargin : minimumDebt ≤
      pair.2 who - reward (quittingSingletonTerminal who) who)
    (hsmall : (∑ player, (root player true).toReal) ≤
      minimumDebt / (8 * M)) :
    minimumDebt / 2 ≤
      quittingTerminalSemanticCapContinueGap (reward := reward) pair root who := by
  have hMpos : 0 < M := by
    by_contra hnot
    have hMzero : M = 0 := le_antisymm (le_of_not_gt hnot) hM
    have hcapZero : pair.2 who = 0 := by
      have := abs_le.mpr ⟨hbox.2.1 who, hbox.2.2 who⟩
      rw [hMzero] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    have hreZero : reward (quittingSingletonTerminal who) who = 0 := by
      have := hreward (quittingSingletonTerminal who) who
      rw [hMzero] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    rw [hcapZero, hreZero, sub_zero] at hmargin
    linarith
  have hmass := quittingRootOpponentAbsorptionMass_le_sum_quitProbability
    root who
  have hmassSmall : quittingRootOpponentAbsorptionMass root who ≤
      minimumDebt / (8 * M) := hmass.trans hsmall
  have hden : 0 < 8 * M := by positivity
  have hcharge : 4 * M * quittingRootOpponentAbsorptionMass root who ≤
      minimumDebt / 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hmassSmall (by positivity : 0 ≤ 4 * M)
    calc
      4 * M * quittingRootOpponentAbsorptionMass root who ≤
          4 * M * (minimumDebt / (8 * M)) := hscaled
      _ = minimumDebt / 2 := by field_simp; ring
  have hvariation :=
    abs_quittingTerminalSemanticCapContinueGap_sub_singletonMargin_le
      (reward := reward) pair root who hreward hbox
  have hlower := neg_le_of_abs_le hvariation
  linarith

/-- Every carrier point of a counterexample has total debt at least the
stored terminal gap. -/
theorem QuittingCounterexampleRegime.terminalGap_le_semanticDebtSum
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    regime.terminalGap ≤ quittingTerminalSemanticDebtSum pair := by
  have hfloor : regime.terminalGap ≤
      quittingTerminalSemanticExploitability pair :=
    (terminalExploitabilityGap_le_quittingTerminalExploitabilityInf
      reward regime.terminalExploitability).trans
      (quittingTerminalExploitabilityInf_le_semanticCarrier reward hpair)
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  have hexploitLe : quittingTerminalSemanticExploitability pair ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    rw [max_eq_right (hdebtNonneg who)]
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  exact hfloor.trans hexploitLe

/-- A positive costate has a positive weighted minimum throughout a
counterexample carrier. -/
theorem QuittingCounterexampleRegime.weightedDebtSum_pos
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    (theta : Payoff ι) (htheta : ∀ who, 0 < theta who)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    0 < quittingTerminalSemanticWeightedDebtSum theta pair := by
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  have hsumPositive : 0 < quittingTerminalSemanticDebtSum pair :=
    regime.terminalGap_pos.trans_le
      (regime.terminalGap_le_semanticDebtSum pair hpair)
  obtain ⟨who, _, hwho⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun player _ => hdebtNonneg player)).mp hsumPositive
  unfold quittingTerminalSemanticWeightedDebtSum
  exact Finset.sum_pos' (fun player _ =>
    mul_nonneg (htheta player).le (hdebtNonneg player))
    ⟨who, Finset.mem_univ who, mul_pos (htheta who) hwho⟩

/-- Singular-weight compactness forces a carrier point whose debt is
supported on any prescribed coordinate.  The surviving debt remains at
least the counterexample's terminal gap, and the point is an exact
all-Continue plateau. -/
theorem QuittingCounterexampleRegime.exists_terminalSemanticDebtAxis
    (regime : QuittingCounterexampleRegime reward) (owner : ι) :
    ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      regime.terminalGap ≤ quittingTerminalSemanticDebt pair owner ∧
      (∀ other, other ≠ owner →
        quittingTerminalSemanticDebt pair other = 0) ∧
      IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool) := by
  obtain ⟨M, -, hreward⟩ :=
    exists_quittingRewardBound reward
  letI : Nonempty ι := regime.nonempty_players
  let theta : ℕ → Payoff ι := quittingDebtAxisCostate owner
  have hcompact := quittingTerminalSemanticCarrier_isCompact reward
  have hnonempty := quittingTerminalSemanticCarrier_nonempty reward
  have hmin : ∀ index, ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticWeightedDebtSum (theta index) pair ≤
          quittingTerminalSemanticWeightedDebtSum (theta index) candidate := by
    intro index
    obtain ⟨pair, hpair, hpairMin⟩ := hcompact.exists_isMinOn hnonempty
      (continuous_quittingTerminalSemanticWeightedDebtSum
        (theta index)).continuousOn
    exact ⟨pair, hpair, fun candidate hcandidate => hpairMin hcandidate⟩
  choose pair hpair hminimum using hmin
  have hpositive : ∀ index,
      0 < quittingTerminalSemanticWeightedDebtSum (theta index) (pair index) :=
    fun index => regime.weightedDebtSum_pos (theta index)
      (quittingDebtAxisCostate_pos owner index) (pair index)
      (hpair index)
  have hplateau : ∀ index,
      IsεQuittingRootNash reward (pair index).1 0
        (quittingAllContinueRoot : ι → PMF Bool) := by
    intro index
    exact (minimumTerminalSemantic_weightedIs_allContinuePlateau
      (reward := reward) (theta index) (pair index)
      (hpair index) (hminimum index) (hpositive index)
      (quittingDebtAxisCostate_pos owner index)).1
  have hbox : ∀ index,
      pair index ∈ quittingTerminalSemanticBox ι M := fun index =>
    quittingTerminalSemanticCarrier_mem_box
      (reward := reward) (pair index) hreward (hpair index)
  let rate : ℕ → ℝ := fun index => 1 / ((index : ℝ) + 1)
  have hrateNonneg : ∀ index, 0 ≤ rate index := by
    intro index
    dsimp [rate]
    positivity
  have hotherSumBound : ∀ index,
      (∑ other ∈ Finset.univ.erase owner,
        quittingTerminalSemanticDebt (pair index) other) ≤
          2 * M * rate index := by
    intro index
    have hmargin := minimumTerminalSemantic_weightedSingletonMargin
      (reward := reward) (theta index) (pair index)
      (hpair index) (hminimum index) (hpositive index)
      (quittingDebtAxisCostate_pos owner index) owner
    have hownerDebtNonneg : 0 ≤
        quittingTerminalSemanticDebt (pair index) owner :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward (hpair index) owner
    have hgapUpper :
        (pair index).2 owner -
            reward (quittingSingletonTerminal owner) owner ≤ 2 * M := by
      have henvelopeUpper := (hbox index).2.2 owner
      have hrewardLower := neg_le_of_abs_le
        (hreward (quittingSingletonTerminal owner) owner)
      linarith
    have hweightedIdentity :
        quittingTerminalSemanticWeightedDebtSum (theta index) (pair index) =
          rate index * quittingTerminalSemanticDebt (pair index) owner +
            ∑ other ∈ Finset.univ.erase owner,
              quittingTerminalSemanticDebt (pair index) other := by
      unfold quittingTerminalSemanticWeightedDebtSum
      rw [← Finset.sum_erase_add Finset.univ
        (fun who => theta index who *
          quittingTerminalSemanticDebt (pair index) who)
        (Finset.mem_univ owner)]
      rw [show theta index owner = rate index by
        simp [theta, rate, quittingDebtAxisCostate]]
      have herase :
          (∑ other ∈ Finset.univ.erase owner,
            theta index other * quittingTerminalSemanticDebt (pair index) other) =
          ∑ other ∈ Finset.univ.erase owner,
            quittingTerminalSemanticDebt (pair index) other := by
        apply Finset.sum_congr rfl
        intro other hother
        have hne : other ≠ owner := (Finset.mem_erase.mp hother).1
        simp [theta, quittingDebtAxisCostate, hne]
      rw [herase]
      ring
    rw [hweightedIdentity] at hmargin
    have hscaledMargin :
        rate index * quittingTerminalSemanticDebt (pair index) owner +
            ∑ other ∈ Finset.univ.erase owner,
              quittingTerminalSemanticDebt (pair index) other ≤
          rate index *
            ((pair index).2 owner -
              reward (quittingSingletonTerminal owner) owner) := by
      simpa [theta, rate, quittingDebtAxisCostate] using hmargin
    have hotherSumNonneg : 0 ≤
        ∑ other ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebt (pair index) other := by
      exact Finset.sum_nonneg fun other _ =>
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward (hpair index) other
    have hscaledUpper := mul_le_mul_of_nonneg_left hgapUpper
      (hrateNonneg index)
    have hownerTermNonneg : 0 ≤ rate index *
        quittingTerminalSemanticDebt (pair index) owner :=
      mul_nonneg (hrateNonneg index) hownerDebtNonneg
    linarith
  obtain ⟨limit, hlimitCarrier, subseq, hsubseq, hlimit⟩ :=
    hcompact.tendsto_subseq hpair
  have hrate : Tendsto rate atTop (𝓝 0) := by
    simpa [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrateSubseq : Tendsto (fun index => rate (subseq index)) atTop (𝓝 0) :=
    hrate.comp hsubseq.tendsto_atTop
  have hotherZero : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt limit other = 0 := by
    intro other hother
    have hdebtLimit : Tendsto
        (fun index => quittingTerminalSemanticDebt (pair (subseq index)) other)
        atTop (𝓝 (quittingTerminalSemanticDebt limit other)) :=
      (continuous_quittingTerminalSemanticDebt other).tendsto limit |>.comp hlimit
    have hdebtZero : Tendsto
        (fun index => quittingTerminalSemanticDebt (pair (subseq index)) other)
        atTop (𝓝 0) := by
      apply squeeze_zero
      · intro index
        exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward (hpair (subseq index)) other
      · intro index
        have hmem : other ∈ Finset.univ.erase owner :=
          Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
        have hsingle := Finset.single_le_sum
          (s := Finset.univ.erase owner)
          (fun player _ => quittingTerminalSemanticDebt_nonneg_of_mem_carrier
            reward (hpair (subseq index)) player)
          hmem
        exact hsingle.trans (hotherSumBound (subseq index))
      · simpa using hrateSubseq.const_mul (2 * M)
    exact tendsto_nhds_unique hdebtLimit hdebtZero
  have hgapLimit : regime.terminalGap ≤
      quittingTerminalSemanticDebt limit owner := by
    have hgapSum := regime.terminalGap_le_semanticDebtSum
      limit hlimitCarrier
    have hsumOwner : quittingTerminalSemanticDebtSum limit =
        quittingTerminalSemanticDebt limit owner := by
      unfold quittingTerminalSemanticDebtSum
      rw [← Finset.sum_erase_add Finset.univ
        (fun who => quittingTerminalSemanticDebt limit who)
        (Finset.mem_univ owner)]
      have hzero : (∑ other ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebt limit other) = 0 := by
        apply Finset.sum_eq_zero
        intro other hmem
        exact hotherZero other (by simpa using (Finset.mem_erase.mp hmem).1)
      rw [hzero, zero_add]
    rwa [hsumOwner] at hgapSum
  have hnashLimit : IsεQuittingRootNash reward limit.1 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    apply (isZeroQuittingRootNash_allContinue_iff_singleton_le reward limit.1).2
    intro who
    have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
        reward (quittingSingletonTerminal who) who ≤ candidate.1 who} := by
      exact isClosed_le continuous_const (by fun_prop)
    apply hclosed.mem_of_tendsto hlimit
    filter_upwards [] with index
    exact (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward (pair (subseq index)).1).1 (hplateau (subseq index)) who
  exact ⟨limit, hlimitCarrier, hgapLimit, hotherZero, hnashLimit⟩

/-- **Universal debt-axis and source-matched insertion certificate.**  Every
player has a carrier state with debt supported on that player.  Moreover one
positive-solo owner has such a state at which a fixed-rate solo prefix carries
singleton incidence at least one half and a distinct player's exact endpoint
gain equals half of its positive singleton-insertion gain. -/
theorem QuittingCounterexampleRegime.exists_debtAxes_and_sourceMatchedInsertion
    (regime : QuittingCounterexampleRegime reward) :
    (∀ owner, ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      regime.terminalGap ≤ quittingTerminalSemanticDebt pair owner ∧
      (∀ other, other ≠ owner →
        quittingTerminalSemanticDebt pair other = 0)) ∧
    ∃ (owner other : ι) (pair : QuittingTerminalSemanticPair ι)
        (rate gain : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      other ≠ owner ∧
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      regime.terminalGap ≤ quittingTerminalSemanticDebt pair owner ∧
      (∀ player, player ≠ owner →
        quittingTerminalSemanticDebt pair player = 0) ∧
      quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0 hrate1)) pair ∈
        quittingTerminalSemanticCarrier reward ∧
      1 / 2 ≤ rate ∧
      regime.terminalGap ≤ gain ∧
      gain = quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other ∧
      quittingRootEndpointDifference reward pair.1
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0 hrate1)) other = gain / 2 := by
  letI : Nonempty ι := regime.nonempty_players
  have haxes : ∀ owner, ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      regime.terminalGap ≤ quittingTerminalSemanticDebt pair owner ∧
      (∀ other, other ≠ owner →
        quittingTerminalSemanticDebt pair other = 0) := by
    intro owner
    obtain ⟨pair, hpair, hdebt, hother, _hnash⟩ :=
      regime.exists_terminalSemanticDebtAxis owner
    exact ⟨pair, hpair, hdebt, hother⟩
  refine ⟨haxes, ?_⟩
  obtain ⟨owner, hownerSolo⟩ := regime.exists_terminalGap_le_soloReward
  obtain ⟨pair, hpair, hownerDebt, hotherDebt, hnashAll⟩ :=
    regime.exists_terminalSemanticDebtAxis owner
  obtain ⟨other, hne, hinsertion⟩ := regime.exists_collision_gain
    (owner := owner) (by linarith [regime.terminalGap_pos])
  let gain := quittingSingletonCollisionReward reward owner other -
    quittingSoloReward reward owner other
  let slack := pair.1 other - quittingSoloReward reward other other
  have hgain : regime.terminalGap ≤ gain := by
    dsimp only [gain]
    linarith
  have hgainPos : 0 < gain := regime.terminalGap_pos.trans_le hgain
  have hslackNonneg : 0 ≤ slack := by
    dsimp only [slack]
    have hsingleton := (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward pair.1).1 hnashAll other
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      sub_nonneg.mpr hsingleton
  let rate := (slack + gain / 2) / (slack + gain)
  have hden : 0 < slack + gain := add_pos_of_nonneg_of_pos hslackNonneg hgainPos
  have hrate0 : 0 ≤ rate := by
    dsimp only [rate]
    positivity
  have hrate1 : rate ≤ 1 := by
    dsimp only [rate]
    apply (div_le_one hden).2
    linarith
  have hrateHalf : 1 / 2 ≤ rate := by
    dsimp only [rate]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hprefix := quittingTerminalSemanticPrefix_mem_carrier reward
    (quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate0 hrate1)) pair hpair
  refine ⟨owner, other, pair, rate, gain, hrate0, hrate1, hne,
    hpair, hownerDebt, hotherDebt, hprefix, hrateHalf, hgain, rfl, ?_⟩
  rw [quittingRootEndpointDifference_conditionedSolo_other reward hne]
  have hslackEq : quittingSoloReward reward other other - pair.1 other =
      -slack := by
    dsimp only [slack]
    ring
  have hgainEq : quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other = gain := rfl
  rw [hslackEq, hgainEq]
  dsimp only [rate]
  field_simp [hden.ne']
  ring

end GameTheory
