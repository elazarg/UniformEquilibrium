/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Topology.Algebra.Order.LiminfLimsup
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticDebtRatioResponse

/-!
# Carrier responses in the debt-ratio chamber

This module selects a fixed maximum-debt payer along a realizing sequence for
one terminal-semantic carrier point, and then uses literal approximate best
responses.  It contains no paid-port attachment or downstream consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Topology QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- An executable realizing sequence for a carrier point, restricted to one
cofinal subsequence on which a fixed player maximizes literal terminal debt. -/
structure QuittingDebtRatioCarrierSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticPair ι) where
  payer : ι
  profile : ℕ → (quittingGame reward).BehaviorProfile
  tendsto_point : Tendsto
    (fun n => quittingTerminalSemanticPair reward (profile n)) atTop (𝓝 point)
  payer_maximum : ∀ n other,
    quittingTerminalDeviationDebt reward (profile n) other ≤
      quittingTerminalDeviationDebt reward (profile n) payer

/-- Every carrier point has an actual realizing sequence with one fixed
maximum-debt payer.  This is the literal carrier source used below. -/
theorem nonempty_quittingDebtRatioCarrierSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticPair ι)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward) :
    Nonempty (QuittingDebtRatioCarrierSource reward point) := by
  obtain ⟨rawProfile, hrawTendsto⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward point hpoint
  let payerAt : ℕ → ι := fun n => Classical.choose
    (Finset.exists_mem_eq_sup' Finset.univ_nonempty fun who : ι =>
      quittingTerminalDeviationDebt reward (rawProfile n) who)
  have hpayerAt : ∀ n other,
      quittingTerminalDeviationDebt reward (rawProfile n) other ≤
        quittingTerminalDeviationDebt reward (rawProfile n) (payerAt n) := by
    intro n other
    have hspec := Classical.choose_spec
      (Finset.exists_mem_eq_sup' Finset.univ_nonempty fun who : ι =>
        quittingTerminalDeviationDebt reward (rawProfile n) who)
    rw [← hspec.2]
    exact Finset.le_sup' (f := fun who : ι =>
      quittingTerminalDeviationDebt reward (rawProfile n) who)
      (Finset.mem_univ other)
  obtain ⟨payer, hpayerInfinite⟩ := Finite.exists_infinite_fiber payerAt
  have hpayerFrequent : ∃ᶠ n in atTop, payerAt n = payer := by
    rw [Nat.frequently_atTop_iff_infinite]
    have hinfinite : (payerAt ⁻¹' ({payer} : Set ι)).Infinite :=
      Set.infinite_coe_iff.mp hpayerInfinite
    convert hinfinite using 1
    ext n
    simp
  obtain ⟨subsequence, hsubsequence, hpayer⟩ :=
    extraction_of_frequently_atTop hpayerFrequent
  refine ⟨{
    payer := payer
    profile := fun n => rawProfile (subsequence n)
    tendsto_point := hrawTendsto.comp hsubsequence.tendsto_atTop
    payer_maximum := ?_ }⟩
  intro n other
  simpa only [hpayer n] using hpayerAt (subsequence n) other

/-- The fixed-payer source together with a literal positive decreasing error
sequence and actual approximate best responses.  The target is definitionally
the one-player replacement, so every opponent strategy is retained literally. -/
structure QuittingDebtRatioApproximateResponseSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticPair ι) where
  carrier : QuittingDebtRatioCarrierSource reward point
  error : ℕ → ℝ
  error_pos : ∀ n, 0 < error n
  error_strictAnti : StrictAnti error
  error_tendsto_zero : Tendsto error atTop (𝓝 0)
  response : ∀ _ : ℕ, (quittingGame reward).BehaviorStrategy carrier.payer
  response_payoff : ∀ n,
    quittingContinuationBestResponseValue reward (carrier.profile n) carrier.payer -
        error n ≤
      quittingTerminalPayoff reward
        (Function.update (carrier.profile n) carrier.payer (response n))
        carrier.payer

namespace QuittingDebtRatioApproximateResponseSource

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {point : QuittingTerminalSemanticPair ι}

omit [Nonempty ι] in
private theorem quittingTerminalDebtSum_le_card_mul_two_mul_bound
    (profile : (quittingGame reward).BehaviorProfile) (bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalDebtSum reward profile ≤ Fintype.card ι * (2 * bound) := by
  unfold quittingTerminalDebtSum
  calc
    ∑ who, quittingTerminalDeviationDebt reward profile who ≤
        ∑ _who : ι, 2 * bound := by
      apply Finset.sum_le_sum
      intro who _
      have hcap := abs_quittingContinuationBestResponseValue_le
        reward profile who hreward
      have hpayoff := abs_quittingTerminalPayoff_le reward profile who hreward
      unfold quittingTerminalDeviationDebt
      linarith [le_of_abs_le hcap, neg_le_of_abs_le hpayoff]
    _ = Fintype.card ι * (2 * bound) := by simp

/-- The literal approximate-response target. -/
def target (source : QuittingDebtRatioApproximateResponseSource reward point)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (source.carrier.profile n) source.carrier.payer (source.response n)

omit [Nonempty ι] in
/-- Every opponent's strategy is unchanged literally at the response target. -/
@[simp] theorem target_apply_of_ne
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (n : ℕ) {other : ι} (hne : other ≠ source.carrier.payer) :
    source.target n other = source.carrier.profile n other := by
  simpa only [target] using
    Function.update_of_ne hne (source.response n) (source.carrier.profile n)

omit [Nonempty ι] in
/-- The approximate response gains at least source debt minus its displayed
error. -/
theorem gain_ge_debt_sub_error
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (n : ℕ) :
    quittingTerminalDeviationDebt reward (source.carrier.profile n)
          source.carrier.payer - source.error n ≤
      quittingTerminalPayoff reward (source.target n) source.carrier.payer -
        quittingTerminalPayoff reward (source.carrier.profile n)
          source.carrier.payer := by
  dsimp only [target]
  unfold quittingTerminalDeviationDebt
  linarith [source.response_payoff n]

omit [Nonempty ι] in
/-- Approximate best response leaves at most the displayed error of mover
debt at the literal response target. -/
theorem target_payer_debt_le_error
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (n : ℕ) :
    quittingTerminalDeviationDebt reward (source.target n) source.carrier.payer ≤
      source.error n := by
  dsimp only [target]
  unfold quittingTerminalDeviationDebt
  rw [quittingContinuationBestResponseValue_update_self]
  linarith [source.response_payoff n]

omit [Nonempty ι] in
/-- Literal payer debt along the selected source tends to its carrier debt. -/
theorem tendsto_source_payer_debt
    (source : QuittingDebtRatioApproximateResponseSource reward point) :
    Tendsto
      (fun n => quittingTerminalDeviationDebt reward (source.carrier.profile n)
        source.carrier.payer)
      atTop (𝓝 (quittingTerminalSemanticDebt point source.carrier.payer)) := by
  change Tendsto
    ((fun pair => quittingTerminalSemanticDebt pair source.carrier.payer) ∘
      fun n => quittingTerminalSemanticPair reward (source.carrier.profile n))
    atTop (𝓝 (quittingTerminalSemanticDebt point source.carrier.payer))
  exact ((continuous_quittingTerminalSemanticDebt source.carrier.payer).tendsto point).comp
    source.carrier.tendsto_point

omit [Nonempty ι] in
/-- Literal source total debt tends to the carrier total debt. -/
theorem tendsto_source_debtSum
    (source : QuittingDebtRatioApproximateResponseSource reward point) :
    Tendsto (fun n => quittingTerminalDebtSum reward (source.carrier.profile n))
      atTop (𝓝 (quittingTerminalSemanticDebtSum point)) := by
  change Tendsto
    (quittingTerminalSemanticDebtSum ∘
      fun n => quittingTerminalSemanticPair reward (source.carrier.profile n))
    atTop (𝓝 (quittingTerminalSemanticDebtSum point))
  exact (continuous_quittingTerminalSemanticDebtSum.tendsto point).comp
    source.carrier.tendsto_point

omit [Nonempty ι] in
/-- The fixed source payer still maximizes debt at the limiting carrier
point. -/
theorem point_debt_le_payer_debt
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (other : ι) :
    quittingTerminalSemanticDebt point other ≤
      quittingTerminalSemanticDebt point source.carrier.payer := by
  have hother : Tendsto
      (fun n => quittingTerminalDeviationDebt reward (source.carrier.profile n) other)
      atTop (𝓝 (quittingTerminalSemanticDebt point other)) := by
    change Tendsto
      ((fun pair => quittingTerminalSemanticDebt pair other) ∘
        fun n => quittingTerminalSemanticPair reward (source.carrier.profile n))
      atTop (𝓝 (quittingTerminalSemanticDebt point other))
    exact ((continuous_quittingTerminalSemanticDebt other).tendsto point).comp
      source.carrier.tendsto_point
  have hdiff := hother.sub source.tendsto_source_payer_debt
  have hle : quittingTerminalSemanticDebt point other -
      quittingTerminalSemanticDebt point source.carrier.payer ≤ 0 := by
    apply le_of_tendsto hdiff
    exact Filter.Eventually.of_forall fun n => by
      linarith [source.carrier.payer_maximum n other]
  linarith

/-- The global terminal exploitability infimum is no larger than the fixed
payer's debt at the limiting carrier point. -/
theorem exploitabilityInf_le_point_payer_debt
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalExploitabilityInf reward ≤
      quittingTerminalSemanticDebt point source.carrier.payer := by
  apply (quittingTerminalExploitabilityInf_le_semanticCarrier reward hpoint).trans
  unfold quittingTerminalSemanticExploitability
  apply finitePlayerMax_le
  intro other
  rw [max_eq_right
    (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpoint other)]
  exact source.point_debt_le_payer_debt other

/-- In the strict ratio chamber the fixed carrier payer has debt strictly
above the global exploitability floor.  The proof uses actual approximate
responses and a fixed positive stopping-law mixture scale; no response is
selected at the carrier point. -/
theorem exploitabilityInf_lt_point_payer_debt_of_debtSum_lt_two_mul
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward)
    (hupper : quittingTerminalSemanticDebtSum point <
      2 * quittingTerminalExploitabilityInf reward)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalExploitabilityInf reward <
      quittingTerminalSemanticDebt point source.carrier.payer := by
  let eta := quittingTerminalExploitabilityInf reward
  let payerDebt := quittingTerminalSemanticDebt point source.carrier.payer
  let pointTotal := quittingTerminalSemanticDebtSum point
  let targetBound := Fintype.card ι * (2 * bound)
  have hetaLe : eta ≤ payerDebt := source.exploitabilityInf_le_point_payer_debt hpoint
  by_contra hnot
  have hpayerEq : payerDebt = eta := le_antisymm (not_lt.mp hnot) hetaLe
  have hright : ∀ theta : ℝ, 0 < theta → theta < 1 →
      eta + (1 - theta) * payerDebt ≤
        (1 - theta) * pointTotal + theta * targetBound := by
    intro theta hthetaPos hthetaLt
    have hthetaNonneg : 0 ≤ theta := hthetaPos.le
    have hthetaLe : theta ≤ 1 := hthetaLt.le
    let mixed : ℕ → (quittingGame reward).BehaviorProfile := fun n ↦
      Function.update (source.carrier.profile n) source.carrier.payer
        (quittingStoppingLawMixtureBehaviorStrategy reward source.carrier.payer
          (source.carrier.profile n source.carrier.payer) (source.response n)
          theta hthetaNonneg hthetaLe)
    let mixedPayerDebt : ℕ → ℝ := fun n ↦
      (1 - theta) *
          quittingTerminalDeviationDebt reward (source.carrier.profile n)
            source.carrier.payer +
        theta * quittingTerminalDeviationDebt reward (source.target n)
          source.carrier.payer
    have htargetPayerTendsto : Tendsto
        (fun n ↦ quittingTerminalDeviationDebt reward (source.target n)
          source.carrier.payer) atTop (𝓝 0) := by
      apply squeeze_zero
      · intro n
        exact quittingTerminalDeviationDebt_nonneg reward _ _
      · exact source.target_payer_debt_le_error
      · exact source.error_tendsto_zero
    have hmixedPayerTendsto : Tendsto mixedPayerDebt atTop
        (𝓝 ((1 - theta) * payerDebt + theta * 0)) := by
      exact (source.tendsto_source_payer_debt.const_mul (1 - theta)).add
        (htargetPayerTendsto.const_mul theta)
    have hmixedPayerLimitLt : (1 - theta) * payerDebt + theta * 0 < eta := by
      rw [hpayerEq]
      nlinarith
    have hmixedPayerLt : ∀ᶠ n in atTop, mixedPayerDebt n < eta :=
      hmixedPayerTendsto.eventually_lt_const hmixedPayerLimitLt
    have hcrossing : ∀ᶠ n in atTop,
        eta + mixedPayerDebt n ≤
          (1 - theta) * quittingTerminalDebtSum reward (source.carrier.profile n) +
            theta * targetBound := by
      filter_upwards [hmixedPayerLt] with n hn
      have hmoverChord :=
        quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
          reward (source.carrier.profile n) source.carrier.payer
            (source.carrier.profile n source.carrier.payer) (source.response n)
            theta hthetaNonneg hthetaLe
      rw [Function.update_eq_self] at hmoverChord
      change quittingTerminalDeviationDebt reward (mixed n) source.carrier.payer =
        mixedPayerDebt n at hmoverChord
      have hlower :=
        quittingTerminalExploitabilityInf_add_debt_le_debtSum_of_debt_lt
          reward (mixed n) source.carrier.payer (hmoverChord.symm ▸ hn)
      have hconvex := quittingTerminalDebtSum_stoppingLawMixture_le
        reward (source.carrier.profile n) source.carrier.payer
          (source.carrier.profile n source.carrier.payer) (source.response n)
          theta hthetaNonneg hthetaLe
      rw [Function.update_eq_self] at hconvex
      change quittingTerminalDebtSum reward (mixed n) ≤
        (1 - theta) * quittingTerminalDebtSum reward (source.carrier.profile n) +
          theta * quittingTerminalDebtSum reward (source.target n) at hconvex
      have htargetBound : quittingTerminalDebtSum reward (source.target n) ≤
          targetBound :=
        quittingTerminalDebtSum_le_card_mul_two_mul_bound
          (source.target n) bound hreward
      have hscaled := mul_le_mul_of_nonneg_left htargetBound hthetaNonneg
      rw [hmoverChord] at hlower
      exact hlower.trans (hconvex.trans (add_le_add (le_refl _) hscaled))
    have hleft : Tendsto (fun n ↦ eta + mixedPayerDebt n) atTop
        (𝓝 (eta + ((1 - theta) * payerDebt + theta * 0))) :=
      hmixedPayerTendsto.const_add eta
    have hrightLimit : Tendsto
        (fun n ↦
          (1 - theta) * quittingTerminalDebtSum reward (source.carrier.profile n) +
            theta * targetBound) atTop
        (𝓝 ((1 - theta) * pointTotal + theta * targetBound)) := by
      exact (source.tendsto_source_debtSum.const_mul (1 - theta)).add tendsto_const_nhds
    have hdiff := hleft.sub hrightLimit
    have hlimitLe :
        (eta + ((1 - theta) * payerDebt + theta * 0)) -
            ((1 - theta) * pointTotal + theta * targetBound) ≤ 0 := by
      apply le_of_tendsto hdiff
      filter_upwards [hcrossing] with n hn
      linarith
    linarith
  have hboundary := affine_le_of_forall_right
    0 eta payerDebt pointTotal targetBound (by norm_num) hright
  dsimp only [eta, payerDebt, pointTotal] at hpayerEq hboundary hupper
  rw [hpayerEq] at hboundary
  norm_num at hboundary
  linarith

omit [Nonempty ι] in
/-- The response target's mover debt vanishes with the approximation error. -/
theorem tendsto_target_payer_debt_zero
    (source : QuittingDebtRatioApproximateResponseSource reward point) :
    Tendsto
      (fun n => quittingTerminalDeviationDebt reward (source.target n)
        source.carrier.payer) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro n
    exact quittingTerminalDeviationDebt_nonneg reward _ _
  · exact source.target_payer_debt_le_error
  · exact source.error_tendsto_zero

omit [Nonempty ι] in
/-- The literal incoming response gain converges to the fixed payer's carrier
debt. -/
theorem tendsto_response_gain
    (source : QuittingDebtRatioApproximateResponseSource reward point) :
    Tendsto
      (fun n => quittingTerminalPayoff reward (source.target n) source.carrier.payer -
        quittingTerminalPayoff reward (source.carrier.profile n)
          source.carrier.payer)
      atTop (𝓝 (quittingTerminalSemanticDebt point source.carrier.payer)) := by
  have hlower : Tendsto
      (fun n => quittingTerminalDeviationDebt reward (source.carrier.profile n)
          source.carrier.payer - source.error n)
      atTop (𝓝 (quittingTerminalSemanticDebt point source.carrier.payer)) := by
    simpa only [sub_zero] using
      source.tendsto_source_payer_debt.sub source.error_tendsto_zero
  have hupper := source.tendsto_source_payer_debt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper
  · exact source.gain_ge_debt_sub_error
  · intro n
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (source.carrier.profile n) source.carrier.payer (source.response n)
    dsimp only [target]
    unfold quittingTerminalDeviationDebt
    linarith

/-- The literal approximate-response targets have the debt-ratio chamber's
quantitative off-minimum liminf.  The statement retains the actual source,
fixed payer, full response, and definitionally updated target. -/
theorem ratioCrossing_le_liminf_target_debtExcess
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward)
    (hlower : quittingTerminalExploitabilityInf reward <
      quittingTerminalSemanticDebtSum point)
    (hupper : quittingTerminalSemanticDebtSum point <
      2 * quittingTerminalExploitabilityInf reward)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalSemanticDebtSum point *
          (2 * quittingTerminalExploitabilityInf reward -
            quittingTerminalSemanticDebtSum point) /
          (quittingTerminalSemanticDebtSum point -
            quittingTerminalExploitabilityInf reward) ≤
      liminf
        (fun n => quittingTerminalDebtSum reward (source.target n) -
          quittingTerminalSemanticDebtSum point) atTop := by
  let eta := quittingTerminalExploitabilityInf reward
  let payerDebt := quittingTerminalSemanticDebt point source.carrier.payer
  let pointTotal := quittingTerminalSemanticDebtSum point
  let sourcePayerDebt : ℕ → ℝ := fun n ↦
    quittingTerminalDeviationDebt reward (source.carrier.profile n)
      source.carrier.payer
  let targetPayerDebt : ℕ → ℝ := fun n ↦
    quittingTerminalDeviationDebt reward (source.target n) source.carrier.payer
  let sourceTotal : ℕ → ℝ := fun n ↦
    quittingTerminalDebtSum reward (source.carrier.profile n)
  let targetTotal : ℕ → ℝ := fun n ↦
    quittingTerminalDebtSum reward (source.target n)
  let theta : ℕ → ℝ := fun n ↦
    (sourcePayerDebt n - eta) / (sourcePayerDebt n - targetPayerDebt n)
  let thetaAbove : ℕ → ℝ := fun n ↦
    theta n + (1 - theta n) * source.error n
  let targetBound := Fintype.card ι * (2 * bound)
  have hpayerStrict : eta < payerDebt :=
    source.exploitabilityInf_lt_point_payer_debt_of_debtSum_lt_two_mul
      hpoint hpositive hupper bound hreward
  have hpayerPos : 0 < payerDebt := hpositive.trans hpayerStrict
  have hsourcePayerTendsto : Tendsto sourcePayerDebt atTop (𝓝 payerDebt) :=
    source.tendsto_source_payer_debt
  have htargetPayerTendsto : Tendsto targetPayerDebt atTop (𝓝 0) :=
    source.tendsto_target_payer_debt_zero
  have hsourceTotalTendsto : Tendsto sourceTotal atTop (𝓝 pointTotal) :=
    source.tendsto_source_debtSum
  have hetaConst : Tendsto (fun _ : ℕ ↦ eta) atTop (𝓝 eta) := tendsto_const_nhds
  have honeConst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hthetaTendsto : Tendsto theta atTop (𝓝 ((payerDebt - eta) / payerDebt)) := by
    have hnumerator := hsourcePayerTendsto.sub hetaConst
    have hdenominator := hsourcePayerTendsto.sub htargetPayerTendsto
    have hdenominatorNe : payerDebt - 0 ≠ 0 := by linarith
    change Tendsto
      ((fun n ↦ sourcePayerDebt n - eta) /
        fun n ↦ sourcePayerDebt n - targetPayerDebt n)
      atTop (𝓝 ((payerDebt - eta) / payerDebt))
    simpa only [sub_zero] using hnumerator.div hdenominator hdenominatorNe
  have hthetaAboveTendsto : Tendsto thetaAbove atTop
      (𝓝 ((payerDebt - eta) / payerDebt)) := by
    have honeSub := honeConst.sub hthetaTendsto
    have hcorrection := honeSub.mul source.error_tendsto_zero
    simpa only [mul_zero, add_zero] using hthetaTendsto.add hcorrection
  have hsourcePayerAbove : ∀ᶠ n in atTop, eta < sourcePayerDebt n :=
    hsourcePayerTendsto.eventually_const_lt hpayerStrict
  have htargetPayerBelow : ∀ᶠ n in atTop, targetPayerDebt n < eta :=
    htargetPayerTendsto.eventually_lt_const hpositive
  have herrorBelowOne : ∀ᶠ n in atTop, source.error n < 1 :=
    source.error_tendsto_zero.eventually_lt_const (by norm_num)
  have hparameters : ∀ᶠ n in atTop,
      0 < theta n ∧ theta n < thetaAbove n ∧ thetaAbove n < 1 ∧
        (1 - theta n) * sourcePayerDebt n + theta n * targetPayerDebt n = eta := by
    filter_upwards [hsourcePayerAbove, htargetPayerBelow, herrorBelowOne]
      with n hsourceAbove htargetBelow herrorBelow
    have hdenomPos : 0 < sourcePayerDebt n - targetPayerDebt n := by linarith
    have hthetaPos : 0 < theta n := by
      dsimp only [theta]
      positivity
    have hthetaLtOne : theta n < 1 := by
      dsimp only [theta]
      rw [div_lt_one hdenomPos]
      linarith
    have hthetaLtAbove : theta n < thetaAbove n := by
      dsimp only [thetaAbove]
      have : 0 < (1 - theta n) * source.error n :=
        mul_pos (sub_pos.mpr hthetaLtOne) (source.error_pos n)
      linarith
    have haboveLtOne : thetaAbove n < 1 := by
      dsimp only [thetaAbove]
      nlinarith [mul_pos (sub_pos.mpr hthetaLtOne)
        (sub_pos.mpr herrorBelow)]
    have hthetaIdentity :
        (1 - theta n) * sourcePayerDebt n + theta n * targetPayerDebt n = eta := by
      dsimp only [theta]
      field_simp
      ring
    exact ⟨hthetaPos, hthetaLtAbove, haboveLtOne, hthetaIdentity⟩
  have hcrossing : ∀ᶠ n in atTop,
      eta +
          ((1 - thetaAbove n) * sourcePayerDebt n +
            thetaAbove n * targetPayerDebt n) ≤
        (1 - thetaAbove n) * sourceTotal n + thetaAbove n * targetTotal n := by
    filter_upwards [hparameters, hsourcePayerAbove, htargetPayerBelow]
      with n hn hsourceAbove htargetBelow
    have habovePos : 0 < thetaAbove n := hn.1.trans hn.2.1
    let mixed := Function.update (source.carrier.profile n) source.carrier.payer
      (quittingStoppingLawMixtureBehaviorStrategy reward source.carrier.payer
        (source.carrier.profile n source.carrier.payer) (source.response n)
        (thetaAbove n) habovePos.le hn.2.2.1.le)
    have hmoverChord := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward (source.carrier.profile n) source.carrier.payer
        (source.carrier.profile n source.carrier.payer) (source.response n)
        (thetaAbove n) habovePos.le hn.2.2.1.le
    rw [Function.update_eq_self] at hmoverChord
    change quittingTerminalDeviationDebt reward mixed source.carrier.payer =
      (1 - thetaAbove n) * sourcePayerDebt n +
        thetaAbove n * targetPayerDebt n at hmoverChord
    have hmoverLt : quittingTerminalDeviationDebt reward mixed source.carrier.payer <
        eta := by
      rw [hmoverChord]
      rw [← hn.2.2.2]
      nlinarith [hn.2.1, sub_pos.mpr (lt_trans htargetBelow hsourceAbove)]
    have hlowerMixed :=
      quittingTerminalExploitabilityInf_add_debt_le_debtSum_of_debt_lt
        reward mixed source.carrier.payer hmoverLt
    have hupperMixed := quittingTerminalDebtSum_stoppingLawMixture_le
      reward (source.carrier.profile n) source.carrier.payer
        (source.carrier.profile n source.carrier.payer) (source.response n)
        (thetaAbove n) habovePos.le hn.2.2.1.le
    rw [Function.update_eq_self] at hupperMixed
    change quittingTerminalDebtSum reward mixed ≤
      (1 - thetaAbove n) * sourceTotal n + thetaAbove n * targetTotal n
      at hupperMixed
    rw [hmoverChord] at hlowerMixed
    exact hlowerMixed.trans hupperMixed
  let lowerTarget : ℕ → ℝ := fun n ↦
    (eta + (1 - thetaAbove n) * sourcePayerDebt n +
          thetaAbove n * targetPayerDebt n -
        (1 - thetaAbove n) * sourceTotal n) / thetaAbove n
  have hlowerTarget : ∀ᶠ n in atTop, lowerTarget n ≤ targetTotal n := by
    filter_upwards [hparameters, hcrossing] with n hn hcross
    dsimp only [lowerTarget]
    rw [div_le_iff₀ (hn.1.trans hn.2.1)]
    nlinarith
  have hthetaLimitPos : 0 < (payerDebt - eta) / payerDebt := by positivity
  have hlowerTargetTendsto : Tendsto lowerTarget atTop
      (𝓝 (eta * (2 * payerDebt - pointTotal) / (payerDebt - eta))) := by
    have honeSub := honeConst.sub hthetaAboveTendsto
    have hnumerator' :=
      (((hetaConst.add (honeSub.mul hsourcePayerTendsto)).add
        (hthetaAboveTendsto.mul htargetPayerTendsto)).sub
          (honeSub.mul hsourceTotalTendsto))
    have hquotient := hnumerator'.div hthetaAboveTendsto hthetaLimitPos.ne'
    change Tendsto lowerTarget atTop _ at hquotient
    convert hquotient using 1
    field_simp
    ring_nf
  have htargetUpper : ∀ n, targetTotal n ≤ targetBound := by
    intro n
    exact quittingTerminalDebtSum_le_card_mul_two_mul_bound
      (source.target n) bound hreward
  have hliminfRaw :
      eta * (2 * payerDebt - pointTotal) / (payerDebt - eta) - pointTotal ≤
        liminf (fun n ↦ targetTotal n - pointTotal) atTop := by
    have hpointTotalConst : Tendsto (fun _ : ℕ ↦ pointTotal) atTop
        (𝓝 pointTotal) := tendsto_const_nhds
    have hlowerExcessTendsto := hlowerTargetTendsto.sub hpointTotalConst
    rw [← hlowerExcessTendsto.liminf_eq]
    apply liminf_le_liminf
    · filter_upwards [hlowerTarget] with n hn
      linarith
    · exact hlowerExcessTendsto.isBoundedUnder_ge
    · apply isCoboundedUnder_ge_of_le atTop
      intro n
      exact sub_le_sub_right (htargetUpper n) pointTotal
  have hpayerLeTotal : payerDebt ≤ pointTotal := by
    dsimp only [payerDebt, pointTotal]
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun other _ =>
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpoint other)
      (Finset.mem_univ source.carrier.payer)
  have hpointDenom : 0 < pointTotal - eta := sub_pos.mpr hlower
  have hpayerDenom : 0 < payerDebt - eta := sub_pos.mpr hpayerStrict
  have hfactor : 0 < 2 * eta - pointTotal := sub_pos.mpr hupper
  have hratio : pointTotal / (pointTotal - eta) ≤
      payerDebt / (payerDebt - eta) := by
    rw [div_le_div_iff₀ hpointDenom hpayerDenom]
    nlinarith
  have hmonotone : pointTotal * (2 * eta - pointTotal) / (pointTotal - eta) ≤
      payerDebt * (2 * eta - pointTotal) / (payerDebt - eta) := by
    calc
      pointTotal * (2 * eta - pointTotal) / (pointTotal - eta) =
          (2 * eta - pointTotal) * (pointTotal / (pointTotal - eta)) := by ring
      _ ≤ (2 * eta - pointTotal) * (payerDebt / (payerDebt - eta)) :=
        mul_le_mul_of_nonneg_left hratio hfactor.le
      _ = payerDebt * (2 * eta - pointTotal) / (payerDebt - eta) := by ring
  have hrawRewrite :
      eta * (2 * payerDebt - pointTotal) / (payerDebt - eta) - pointTotal =
        payerDebt * (2 * eta - pointTotal) / (payerDebt - eta) := by
    field_simp
    ring
  dsimp only [eta, payerDebt, pointTotal, targetTotal] at hliminfRaw hmonotone ⊢
  rw [hrawRewrite] at hliminfRaw
  exact hmonotone.trans hliminfRaw

/-- After discarding finitely many indices, every literal response target has
half the chamber's quantitative off-minimum excess. -/
theorem eventually_half_ratioCrossing_le_target_debtExcess
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward)
    (hlower : quittingTerminalExploitabilityInf reward <
      quittingTerminalSemanticDebtSum point)
    (hupper : quittingTerminalSemanticDebtSum point <
      2 * quittingTerminalExploitabilityInf reward)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∀ᶠ n in atTop,
      (quittingTerminalSemanticDebtSum point *
          (2 * quittingTerminalExploitabilityInf reward -
            quittingTerminalSemanticDebtSum point) /
          (quittingTerminalSemanticDebtSum point -
            quittingTerminalExploitabilityInf reward)) / 2 ≤
        quittingTerminalDebtSum reward (source.target n) -
          quittingTerminalSemanticDebtSum point := by
  let delta := quittingTerminalSemanticDebtSum point *
    (2 * quittingTerminalExploitabilityInf reward -
      quittingTerminalSemanticDebtSum point) /
    (quittingTerminalSemanticDebtSum point -
      quittingTerminalExploitabilityInf reward)
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    have htotalPos : 0 < quittingTerminalSemanticDebtSum point :=
      hpositive.trans hlower
    positivity
  have hliminf := source.ratioCrossing_le_liminf_target_debtExcess
    hpoint hpositive hlower hupper bound hreward
  have hhalfLt : delta / 2 < liminf
      (fun n => quittingTerminalDebtSum reward (source.target n) -
        quittingTerminalSemanticDebtSum point) atTop :=
    (half_lt_self hdeltaPos).trans_le hliminf
  have hbounded : IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop
      (fun n => quittingTerminalDebtSum reward (source.target n) -
        quittingTerminalSemanticDebtSum point) := by
    apply isBoundedUnder_of_eventually_ge
      (a := -quittingTerminalSemanticDebtSum point)
    exact Filter.Eventually.of_forall fun n => by
      have htotalNonneg : 0 ≤ quittingTerminalDebtSum reward (source.target n) := by
        unfold quittingTerminalDebtSum
        exact Finset.sum_nonneg fun who _ =>
          quittingTerminalDeviationDebt_nonneg reward (source.target n) who
      linarith
  exact (eventually_lt_of_lt_liminf hhalfLt hbounded).mono fun _ hn => hn.le

/-- Some strict subsequence of literal response targets converges to a carrier
point retaining the full debt-ratio excess.  Compactness is used only after
all actual response targets have been constructed. -/
theorem exists_targetCarrierCluster_debtSum_ge_ratioCrossing
    (source : QuittingDebtRatioApproximateResponseSource reward point)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalExploitabilityInf reward)
    (hlower : quittingTerminalExploitabilityInf reward <
      quittingTerminalSemanticDebtSum point)
    (hupper : quittingTerminalSemanticDebtSum point <
      2 * quittingTerminalExploitabilityInf reward)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ cluster ∈ quittingTerminalSemanticCarrier reward,
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto
          ((fun n => quittingTerminalSemanticPair reward (source.target n)) ∘
            subsequence) atTop (𝓝 cluster) ∧
        quittingTerminalSemanticDebtSum point +
            quittingTerminalSemanticDebtSum point *
              (2 * quittingTerminalExploitabilityInf reward -
                quittingTerminalSemanticDebtSum point) /
              (quittingTerminalSemanticDebtSum point -
                quittingTerminalExploitabilityInf reward) ≤
          quittingTerminalSemanticDebtSum cluster := by
  let targetPair : ℕ → QuittingTerminalSemanticPair ι := fun n ↦
    quittingTerminalSemanticPair reward (source.target n)
  have htargetMem : ∀ n, targetPair n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact subset_closure ⟨source.target n, rfl⟩
  obtain ⟨cluster, hcluster, subsequence, hsubsequence, hclusterTendsto⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq htargetMem
  refine ⟨cluster, hcluster, subsequence, hsubsequence, hclusterTendsto, ?_⟩
  let delta := quittingTerminalSemanticDebtSum point *
    (2 * quittingTerminalExploitabilityInf reward -
      quittingTerminalSemanticDebtSum point) /
    (quittingTerminalSemanticDebtSum point -
      quittingTerminalExploitabilityInf reward)
  have hliminf := source.ratioCrossing_le_liminf_target_debtExcess
    hpoint hpositive hlower hupper bound hreward
  by_contra hnot
  have hclusterLt : quittingTerminalSemanticDebtSum cluster -
      quittingTerminalSemanticDebtSum point < delta := by
    dsimp only [delta] at hnot ⊢
    linarith
  let midpoint :=
    ((quittingTerminalSemanticDebtSum cluster -
        quittingTerminalSemanticDebtSum point) + delta) / 2
  have hclusterBelowMidpoint : quittingTerminalSemanticDebtSum cluster -
      quittingTerminalSemanticDebtSum point < midpoint := by
    dsimp only [midpoint]
    linarith
  have hmidpointBelowDelta : midpoint < delta := by
    dsimp only [midpoint]
    linarith
  have hbounded : IsBoundedUnder (fun x₁ x₂ : ℝ => x₁ ≥ x₂) atTop
      (fun n => quittingTerminalDebtSum reward (source.target n) -
        quittingTerminalSemanticDebtSum point) := by
    apply isBoundedUnder_of_eventually_ge
      (a := -quittingTerminalSemanticDebtSum point)
    exact Filter.Eventually.of_forall fun n => by
      have htotalNonneg : 0 ≤ quittingTerminalDebtSum reward (source.target n) := by
        unfold quittingTerminalDebtSum
        exact Finset.sum_nonneg fun who _ =>
          quittingTerminalDeviationDebt_nonneg reward (source.target n) who
      linarith
  have hmidpointBelowLiminf : midpoint < liminf
      (fun n => quittingTerminalDebtSum reward (source.target n) -
        quittingTerminalSemanticDebtSum point) atTop :=
    hmidpointBelowDelta.trans_le hliminf
  have haboveMidpoint : ∀ᶠ n in atTop, midpoint <
      quittingTerminalDebtSum reward (source.target n) -
        quittingTerminalSemanticDebtSum point :=
    eventually_lt_of_lt_liminf hmidpointBelowLiminf hbounded
  have haboveMidpointSubsequence : ∀ᶠ n in atTop, midpoint <
      quittingTerminalDebtSum reward (source.target (subsequence n)) -
        quittingTerminalSemanticDebtSum point :=
    hsubsequence.tendsto_atTop.eventually haboveMidpoint
  have hclusterDebtTendsto : Tendsto
      (fun n => quittingTerminalDebtSum reward (source.target (subsequence n)))
      atTop (𝓝 (quittingTerminalSemanticDebtSum cluster)) := by
    change Tendsto
      (quittingTerminalSemanticDebtSum ∘ targetPair ∘ subsequence)
      atTop (𝓝 (quittingTerminalSemanticDebtSum cluster))
    exact (continuous_quittingTerminalSemanticDebtSum.tendsto cluster).comp
      hclusterTendsto
  have hpointTotalConst : Tendsto
      (fun _ : ℕ ↦ quittingTerminalSemanticDebtSum point) atTop
      (𝓝 (quittingTerminalSemanticDebtSum point)) := tendsto_const_nhds
  have hclusterExcessTendsto := hclusterDebtTendsto.sub hpointTotalConst
  have hbelowMidpoint : ∀ᶠ n in atTop,
      quittingTerminalDebtSum reward (source.target (subsequence n)) -
          quittingTerminalSemanticDebtSum point < midpoint :=
    hclusterExcessTendsto.eventually_lt_const hclusterBelowMidpoint
  have hfalse : ∀ᶠ _n : ℕ in atTop, False :=
    (haboveMidpointSubsequence.and hbelowMidpoint).mono fun _ hn => by
      linarith [hn.1, hn.2]
  exact (Filter.Eventually.exists hfalse).choose_spec

end QuittingDebtRatioApproximateResponseSource

/-- A carrier source always admits explicit `1 / (n + 1)` approximate best
responses.  No compactness or attainment of the strategy space is used. -/
theorem nonempty_quittingDebtRatioApproximateResponseSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticPair ι)
    (hpoint : point ∈ quittingTerminalSemanticCarrier reward) :
    Nonempty (QuittingDebtRatioApproximateResponseSource reward point) := by
  obtain ⟨carrier⟩ := nonempty_quittingDebtRatioCarrierSource
    reward point hpoint
  let error : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have herrorPos : ∀ n, 0 < error n := by
    intro n
    dsimp only [error]
    positivity
  have herrorStrictAnti : StrictAnti error := by
    apply strictAnti_nat_of_succ_lt
    intro n
    dsimp only [error]
    apply one_div_lt_one_div_of_lt (by positivity)
    norm_num
  have herrorTendsto : Tendsto error atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let response : ∀ n,
      (quittingGame reward).BehaviorStrategy carrier.payer := fun n ↦
    Classical.choose (exists_quittingContinuation_deviation_ge_sub
      reward (carrier.profile n) carrier.payer (herrorPos n))
  have hresponse : ∀ n,
      quittingContinuationBestResponseValue reward (carrier.profile n) carrier.payer -
          error n ≤
        quittingTerminalPayoff reward
          (Function.update (carrier.profile n) carrier.payer (response n))
          carrier.payer := by
    intro n
    exact Classical.choose_spec (exists_quittingContinuation_deviation_ge_sub
      reward (carrier.profile n) carrier.payer (herrorPos n))
  exact ⟨{
    carrier := carrier
    error := error
    error_pos := herrorPos
    error_strictAnti := herrorStrictAnti
    error_tendsto_zero := herrorTendsto
    response := response
    response_payoff := hresponse }⟩

end GameTheory
