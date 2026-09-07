import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDynamicCostate
import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloCapThreshold
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# All-player ties and the strict-half bound at positive maximum-debt minima

The objective is maximum debt, not total debt. The solo prefix uses the
existing complete-response cap formula, and the all-Never comparison retains
signed singleton rewards. Actual-profile minima extend to the semantic carrier
by continuity before the carrier-level statements are applied.
-/

noncomputable section

namespace GameTheory

open QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every debt coordinate ties at a positive global maximum-debt minimum in the unit cube. -/
theorem minimumTerminalSemantic_maximumDebt_allPlayersTie
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability pair) (owner : ι) :
    quittingTerminalSemanticDebt pair owner = quittingTerminalSemanticExploitability pair := by
  let minimum := quittingTerminalSemanticExploitability pair
  have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hdebtLe : ∀ who, quittingTerminalSemanticDebt pair who ≤ minimum :=
    fun who => quittingTerminalSemanticDebt_le_exploitability pair who (hnonneg who)
  apply le_antisymm (hdebtLe owner)
  by_contra hnot
  have hgap : 0 < minimum - quittingTerminalSemanticDebt pair owner := by
    exact sub_pos.mpr (lt_of_not_ge hnot)
  have hsmall : 0 < min 1 (min (minimum / 4)
      ((minimum - quittingTerminalSemanticDebt pair owner) / 2)) := by
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  obtain ⟨hazard, hzero, hbound⟩ := exists_between hsmall
  have hone : hazard < 1 := hbound.trans_le (min_le_left _ _)
  have hmargin : 4 * hazard < minimum := by
    have h := hbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hslack : 2 * hazard < minimum - quittingTerminalSemanticDebt pair owner := by
    have h := hbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hbox := quittingTerminalSemanticCarrier_mem_box reward pair hreward hpair
  let root := quittingSoloStationaryRoot owner (quittingHazardCoin hazard hzero.le hone.le)
  have haffine := quittingTerminalSemanticPrefix_solo_eq_of_above_threshold
    reward pair owner hreward hbox hzero hone (fun who => by
      have hmoat := minimumTerminalSemantic_exploitabilitySingletonMargin
        reward pair hpair hminimum hpositive who
      change minimum ≤ _ at hmoat
      change 4 * 1 * hazard < pair.2 who - reward (quittingSingletonTerminal who) who
      linarith)
  have hprefixMinimum := hminimum (quittingTerminalSemanticPrefix reward root pair)
    (quittingTerminalSemanticPrefix_mem_carrier reward root pair hpair)
  have hprefixStrict : quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPrefix reward root pair) < minimum := by
    unfold quittingTerminalSemanticExploitability finitePlayerMax
    rw [Finset.sup'_lt_iff]
    intro who _
    apply max_lt hpositive
    unfold quittingTerminalSemanticDebt
    rw [haffine]
    dsimp only
    by_cases hwho : who = owner
    · subst who
      rw [if_pos rfl]
      have hpayoffUpper : pair.1 owner ≤ 1 := hbox.1.2 owner
      have hsingletonLower : -1 ≤ reward (quittingSingletonTerminal owner) owner :=
        neg_le_of_abs_le (hreward _ _)
      have hincrease : hazard *
          (pair.1 owner - reward (quittingSingletonTerminal owner) owner) ≤ 2 * hazard := by
        have hgapUpper : pair.1 owner - reward (quittingSingletonTerminal owner) owner ≤ 2 := by
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hgapUpper hzero.le]
      unfold quittingTerminalSemanticDebt at hslack
      nlinarith
    · rw [if_neg hwho]
      have hcontract := mul_le_mul_of_nonneg_left (hdebtLe who)
        (show 0 ≤ 1 - hazard by linarith)
      have hstrictProduct : 0 < hazard * minimum := mul_pos hzero hpositive
      unfold quittingTerminalSemanticDebt at hcontract
      nlinarith
  exact (not_lt_of_ge hprefixMinimum) hprefixStrict

/-- All-Never cannot attain a positive minimum of maximum complete-response debt. -/
theorem not_allNever_positiveMinimumTerminalSemanticExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward)) ≤
          quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward))) : False := by
  let pair := quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward)
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := subset_closure ⟨_, rfl⟩
  by_cases hexists : ∃ who, 0 ≤ reward (quittingSingletonTerminal who) who
  · obtain ⟨who, hsingleton⟩ := hexists
    have hmoat := minimumTerminalSemantic_exploitabilitySingletonMargin
      reward pair hpair hminimum hpositive who
    have hcap : pair.2 who = max 0 (reward (quittingSingletonTerminal who) who) :=
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile reward who
    rw [hcap, max_eq_right hsingleton, sub_self] at hmoat
    exact (not_le_of_gt hpositive) hmoat
  · push Not at hexists
    have hnonpositive : quittingTerminalSemanticExploitability pair ≤ 0 := by
      unfold quittingTerminalSemanticExploitability
      apply finitePlayerMax_le
      intro who
      change max 0 (quittingContinuationBestResponseValue reward
        (quittingAlwaysContinueProfile reward) who -
          quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who) ≤ 0
      rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
        quittingTerminalPayoff_quittingAlwaysContinue, max_eq_left (hexists who).le]
      norm_num
    exact (not_le_of_gt hpositive) hnonpositive

/-- A positive global maximum-debt minimum in the unit cube is strictly below one half. -/
theorem minimumTerminalSemantic_maximumDebt_lt_half
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability pair ≤
        quittingTerminalSemanticExploitability candidate)
    (hpositive : 0 < quittingTerminalSemanticExploitability pair) :
    quittingTerminalSemanticExploitability pair < (1 : ℝ) / 2 := by
  let minimum := quittingTerminalSemanticExploitability pair
  let neverPair := quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward)
  have hnever : neverPair ∈ quittingTerminalSemanticCarrier reward := subset_closure ⟨_, rfl⟩
  have hneverDebt : ∀ who, quittingTerminalSemanticDebt neverPair who =
      max 0 (reward (quittingSingletonTerminal who) who) := by
    intro who
    change quittingContinuationBestResponseValue reward (quittingAlwaysContinueProfile reward)
      who - quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who = _
    rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      quittingTerminalPayoff_quittingAlwaysContinue, sub_zero]
  have hstrict : minimum < quittingTerminalSemanticExploitability neverPair := by
    have hle := hminimum neverPair hnever
    by_contra hnot
    have heq : quittingTerminalSemanticExploitability neverPair = minimum :=
      le_antisymm (le_of_not_gt hnot) hle
    apply not_allNever_positiveMinimumTerminalSemanticExploitability reward
    · intro candidate hcandidate
      change quittingTerminalSemanticExploitability neverPair ≤ _
      rw [heq]
      exact hminimum candidate hcandidate
    · change 0 < quittingTerminalSemanticExploitability neverPair
      rwa [heq]
  have hneverLeOne : quittingTerminalSemanticExploitability neverPair ≤ 1 := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    rw [hneverDebt]
    exact max_le (by norm_num) (max_le (by norm_num) (le_of_abs_le (hreward _ _)))
  have hminimumLeOne : minimum ≤ 1 := hstrict.le.trans hneverLeOne
  have hbox := quittingTerminalSemanticCarrier_mem_box reward pair hreward hpair
  have hsingleton : ∀ who, reward (quittingSingletonTerminal who) who ≤ 1 - minimum := by
    intro who
    have hmoat := minimumTerminalSemantic_exploitabilitySingletonMargin
      reward pair hpair hminimum hpositive who
    have hcap : pair.2 who ≤ 1 := hbox.2.2 who
    change minimum ≤ _ at hmoat
    linarith
  have hneverUpper : quittingTerminalSemanticExploitability neverPair ≤ 1 - minimum := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    rw [hneverDebt]
    exact max_le (by linarith) (max_le (by linarith) (hsingleton who))
  change minimum < 1 / 2
  linarith

/-- An attained minimum against all actual profiles is also a minimum against
their full prescribed-payoff/complete-cap carrier. -/
theorem terminalSemantic_minimum_of_actualMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate : (quittingGame reward).BehaviorProfile,
      quittingTerminalExploitability reward profile ≤
        quittingTerminalExploitability reward candidate) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticExploitability (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticExploitability candidate := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      quittingTerminalSemanticExploitability (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticExploitability candidate} :=
    isClosed_le continuous_const continuous_quittingTerminalSemanticExploitability
  intro candidate hcandidate
  apply (closure_minimal ?_ hclosed) hcandidate
  rintro pair ⟨actual, rfl⟩
  exact hminimum actual

/-- Actual attained positive minima tie every player's unrestricted terminal debt. -/
theorem quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hminimum : ∀ candidate : (quittingGame reward).BehaviorProfile,
      quittingTerminalExploitability reward profile ≤
        quittingTerminalExploitability reward candidate)
    (hpositive : 0 < quittingTerminalExploitability reward profile) (who : ι) :
    quittingTerminalDeviationDebt reward profile who =
      quittingTerminalExploitability reward profile :=
  minimumTerminalSemantic_maximumDebt_allPlayersTie reward _ hreward
    (subset_closure ⟨profile, rfl⟩)
    (terminalSemantic_minimum_of_actualMinimum reward profile hminimum) hpositive who

/-- Every attained positive minimum for a finite nonempty player set is below one half. -/
theorem quittingTerminalExploitability_lt_half_of_attained_positive_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hminimum : ∀ candidate : (quittingGame reward).BehaviorProfile,
      quittingTerminalExploitability reward profile ≤
        quittingTerminalExploitability reward candidate)
    (hpositive : 0 < quittingTerminalExploitability reward profile) :
    quittingTerminalExploitability reward profile < (1 : ℝ) / 2 :=
  minimumTerminalSemantic_maximumDebt_lt_half reward _ hreward
    (subset_closure ⟨profile, rfl⟩)
    (terminalSemantic_minimum_of_actualMinimum reward profile hminimum) hpositive

end GameTheory
