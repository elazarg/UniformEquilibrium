/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Players.SmallPlayers
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality

/-!
# The random deviation audit game

This file gives a direct game-theoretic characterization of the fixed-table
uniform-equilibrium-payoff question for a finite quitting game.

The Coordinator chooses an actual behavioral profile.  Nature then selects a
player according to a public audit law.  After learning that player, the
Auditor replaces only that player's strategy by a deterministic quitting time
or by `Never`.  The Auditor is paid the selected player's improvement in
terminal payoff.

Behavioral pure-time extremality proves, rather than assumes, that the value
of the audit after a profile and player have been selected is exactly that
player's all-behavior terminal debt.  Under the uniform audit law, the expected
score is therefore total terminal debt divided by the number of players.  The
main fixed-table reduction is

```
  uniform random-deviation audit value = 0
    ↔ the quitting game has a uniform-equilibrium payoff.
```

Equivalently, positive audit value is exactly nonexistence of a UE payoff.  It
therefore produces the landed canonical positive minimum-total-debt
all-Continue semantic plateau.  The small-player existence theorems imply
that positive audit value requires at least four players; four is only the
first open cardinality, and no reduction of larger games to four players is
claimed.

The semantic formulation minimizes the same score over
`quittingTerminalSemanticCarrier`.  This carrier is irreducible provenance:
it is the closure of pairs co-realized by executable profiles.  Static reward
geometry, a free debt simplex, or independently chosen payoff and cap vectors
cannot replace it.
-/

noncomputable section

namespace GameTheory
namespace RandomDeviationAudit

open Filter StochasticGame QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Nature's public distribution over audited players, represented by its
finite probability weights. -/
structure Law (ι : Type) [Fintype ι] where
  weight : ι → ℝ
  weight_nonneg : ∀ who, 0 ≤ weight who
  sum_weight : ∑ who, weight who = 1

namespace Law

/-- Every player can be audited.  This is not symmetry of rewards or play. -/
def HasFullSupport (law : Law ι) : Prop :=
  ∀ who, 0 < law.weight who

/-- Canonical ex-ante symmetry: Nature audits each player uniformly. -/
def uniform [Nonempty ι] : Law ι where
  weight := fun _ => 1 / (Fintype.card ι : ℝ)
  weight_nonneg := fun _ => by positivity
  sum_weight := by
    rw [Finset.sum_const, Finset.card_univ]
    rw [nsmul_eq_mul]
    field_simp

omit [DecidableEq ι] in
theorem uniform_hasFullSupport [Nonempty ι] :
    (uniform : Law ι).HasFullSupport := by
  intro who
  dsimp [uniform]
  positivity

end Law

variable
  (reward : {S : Finset ι // S.Nonempty} → Payoff ι)

/-- The Coordinator's move: an executable, possibly history-dependent
behavioral profile in the original quitting game. -/
abbrev CoordinatorMove := (quittingGame reward).BehaviorProfile

/-- The Auditor's response after Nature reveals the audited player.  `some t`
means Quit deterministically at time `t`; `none` means Never Quit. -/
abbrev PureAuditResponse (_who : ι) := Option ℕ

/-- A contingent audit policy, chosen after the Coordinator's profile is
public: one pure-time response for every possible player selected by Nature.
-/
abbrev AuditorPolicy (ι : Type) := ι → Option ℕ

/-- Terminal improvement produced by one deterministic quit time or Never. -/
def pureTimeGain
    (profile : CoordinatorMove reward) (who : ι)
    (response : PureAuditResponse who) : ℝ :=
  quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who response)) who -
    quittingTerminalPayoff reward profile who

/-- The post-audit value for one selected player.  The constant prescribed
payoff is subtracted after taking the supremum over deterministic quit times
and Never. -/
def individualValue
    (profile : CoordinatorMove reward) (who : ι) : ℝ :=
  sSup (Set.range fun response : Option ℕ =>
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who response)) who) -
    quittingTerminalPayoff reward profile who

/-- Exact operational reduction: after a profile and player are selected,
the pure-time/ Never audit has value equal to the all-behavior unilateral
terminal debt. -/
theorem individualValue_eq_terminalDebt
    (profile : CoordinatorMove reward) (who : ι) :
    individualValue reward profile who =
      quittingTerminalDeviationDebt reward profile who := by
  unfold individualValue quittingTerminalDeviationDebt
    quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime reward profile who]

/-- Every concrete pure-time response pays at most the post-audit value. -/
theorem pureTimeGain_le_individualValue
    (profile : CoordinatorMove reward) (who : ι)
    (response : PureAuditResponse who) :
    pureTimeGain reward profile who response ≤
      individualValue reward profile who := by
  let values : Set ℝ := Set.range fun choice : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hbounded : BddAbove values := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) who
        (abs_reward_le_quittingRewardBound reward))
  have hmember : quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who response)) who ∈
      values := ⟨response, rfl⟩
  have hle := le_csSup hbounded hmember
  unfold pureTimeGain individualValue
  exact sub_le_sub_right hle _

/-- The post-audit value can be approached arbitrarily closely by one
deterministic quitting time or Never. -/
theorem exists_pureTimeGain_gt_individualValue_sub
    (profile : CoordinatorMove reward) (who : ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ response : PureAuditResponse who,
      individualValue reward profile who - ε <
        pureTimeGain reward profile who response := by
  let values : Set ℝ := Set.range fun choice : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hnonempty : values.Nonempty := Set.range_nonempty _
  have hbounded : BddAbove values := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) who
        (abs_reward_le_quittingRewardBound reward))
  have hlt : sSup values - ε < sSup values := sub_lt_self _ hε
  obtain ⟨payoff, ⟨response, rfl⟩, hpayoff⟩ :=
    (lt_csSup_iff hbounded hnonempty).mp hlt
  refine ⟨response, ?_⟩
  unfold individualValue pureTimeGain
  change sSup values - _ - ε < _ - _
  linarith

/-- The displayed individual audit value is the least upper bound of the
actual pure-time improvement payments. -/
theorem individualValue_isLUB_pureTimeGain
    (profile : CoordinatorMove reward) (who : ι) :
    IsLUB (Set.range fun response : PureAuditResponse who =>
      pureTimeGain reward profile who response)
      (individualValue reward profile who) := by
  constructor
  · rintro gain ⟨response, rfl⟩
    exact pureTimeGain_le_individualValue reward profile who response
  · intro bound hbound
    by_contra hnot
    have hlt : bound < individualValue reward profile who :=
      lt_of_not_ge hnot
    let ε := (individualValue reward profile who - bound) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨response, hresponse⟩ :=
      exists_pureTimeGain_gt_individualValue_sub
        reward profile who hε
    have hupper := hbound ⟨response, rfl⟩
    dsimp [ε] at hresponse
    linarith

/-- Exact supremal-payment form of the operational reduction. -/
theorem sSup_range_pureTimeGain_eq_terminalDebt
    (profile : CoordinatorMove reward) (who : ι) :
    sSup (Set.range fun response : PureAuditResponse who =>
      pureTimeGain reward profile who response) =
        quittingTerminalDeviationDebt reward profile who := by
  rw [(individualValue_isLUB_pureTimeGain reward profile who).csSup_eq
    (Set.range_nonempty _)]
  exact individualValue_eq_terminalDebt reward profile who

/-- Every selected player has nonnegative audit value: keeping the
Coordinator's own strategy is among the all-behavior deviations. -/
theorem individualValue_nonneg
    (profile : CoordinatorMove reward) (who : ι) :
    0 ≤ individualValue reward profile who := by
  rw [individualValue_eq_terminalDebt]
  exact quittingTerminalDeviationDebt_nonneg reward profile who

/-- Expected realized payment of a contingent pure-time audit policy. -/
def policyPayoff
    (law : Law ι) (profile : CoordinatorMove reward)
    (policy : AuditorPolicy ι) : ℝ :=
  ∑ who, law.weight who * pureTimeGain reward profile who (policy who)

/-- The random-audit score after the Coordinator fixes a profile and the
Auditor optimizes separately after observing Nature's selected player. -/
def score (law : Law ι) (profile : CoordinatorMove reward) : ℝ :=
  ∑ who, law.weight who * individualValue reward profile who

/-- A concrete contingent audit policy never beats the optimized score. -/
theorem policyPayoff_le_score
    (law : Law ι) (profile : CoordinatorMove reward)
    (policy : AuditorPolicy ι) :
    policyPayoff reward law profile policy ≤ score reward law profile := by
  unfold policyPayoff score
  apply Finset.sum_le_sum
  intro who _
  exact mul_le_mul_of_nonneg_left
    (pureTimeGain_le_individualValue reward profile who (policy who))
    (law.weight_nonneg who)

/-- Because the player set is finite, one contingent pure-time policy
approaches the optimized expected score at every positive accuracy. -/
theorem exists_policyPayoff_ge_score_sub
    (law : Law ι) (profile : CoordinatorMove reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ policy : AuditorPolicy ι,
      score reward law profile - ε ≤
        policyPayoff reward law profile policy := by
  choose response hresponse using fun who =>
    exists_pureTimeGain_gt_individualValue_sub reward profile who hε
  let policy : AuditorPolicy ι := fun who => response who
  refine ⟨policy, ?_⟩
  have hsum :
      ∑ who, law.weight who *
          (individualValue reward profile who - ε) ≤
        ∑ who, law.weight who *
          pureTimeGain reward profile who (policy who) := by
    apply Finset.sum_le_sum
    intro who _
    apply mul_le_mul_of_nonneg_left _ (law.weight_nonneg who)
    exact (hresponse who).le
  have hleft :
      ∑ who, law.weight who *
          (individualValue reward profile who - ε) =
        score reward law profile - ε := by
    unfold score
    calc
      ∑ who, law.weight who *
            (individualValue reward profile who - ε) =
          ∑ who, (law.weight who *
            individualValue reward profile who - law.weight who * ε) := by
              apply Finset.sum_congr rfl
              intro who _
              ring
      _ = (∑ who, law.weight who *
            individualValue reward profile who) -
          ∑ who, law.weight who * ε := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ who, law.weight who *
            individualValue reward profile who) - ε := by
              rw [← Finset.sum_mul, law.sum_weight, one_mul]
  rw [← hleft]
  exact hsum

/-- The optimized expected score is exactly the least upper bound of the
payoffs of contingent pure-time audit policies. -/
theorem score_isLUB_policyPayoff
    (law : Law ι) (profile : CoordinatorMove reward) :
    IsLUB (Set.range fun policy : AuditorPolicy ι =>
      policyPayoff reward law profile policy) (score reward law profile) := by
  constructor
  · rintro payoff ⟨policy, rfl⟩
    exact policyPayoff_le_score reward law profile policy
  · intro bound hbound
    by_contra hnot
    have hlt : bound < score reward law profile := lt_of_not_ge hnot
    let ε := (score reward law profile - bound) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨policy, hpolicy⟩ :=
      exists_policyPayoff_ge_score_sub reward law profile hε
    have hupper := hbound ⟨policy, rfl⟩
    dsimp [ε] at hpolicy
    linarith

theorem sSup_range_policyPayoff_eq_score
    (law : Law ι) (profile : CoordinatorMove reward) :
    sSup (Set.range fun policy : AuditorPolicy ι =>
      policyPayoff reward law profile policy) = score reward law profile :=
  (score_isLUB_policyPayoff reward law profile).csSup_eq
    (Set.range_nonempty _)

/-- The score is the weighted sum of literal all-behavior debts. -/
theorem score_eq_weightedTerminalDebt
    (law : Law ι) (profile : CoordinatorMove reward) :
    score reward law profile =
      ∑ who, law.weight who *
        quittingTerminalDeviationDebt reward profile who := by
  unfold score
  apply Finset.sum_congr rfl
  intro who _
  rw [individualValue_eq_terminalDebt]

theorem score_nonneg
    (law : Law ι) (profile : CoordinatorMove reward) :
    0 ≤ score reward law profile := by
  rw [score_eq_weightedTerminalDebt]
  exact Finset.sum_nonneg fun who _ =>
    mul_nonneg (law.weight_nonneg who)
      (quittingTerminalDeviationDebt_nonneg reward profile who)

/-! ## Weighted and uniform zero sets -/

/-- With strictly positive audit weights, score zero means every player's
terminal debt is zero, and conversely. -/
theorem score_eq_zero_iff_forall_terminalDebt_eq_zero
    (law : Law ι) (hfull : law.HasFullSupport)
    (profile : CoordinatorMove reward) :
    score reward law profile = 0 ↔
      ∀ who, quittingTerminalDeviationDebt reward profile who = 0 := by
  rw [score_eq_weightedTerminalDebt]
  have hterm : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ law.weight who *
        quittingTerminalDeviationDebt reward profile who := by
    intro who _
    exact mul_nonneg (law.weight_nonneg who)
      (quittingTerminalDeviationDebt_nonneg reward profile who)
  constructor
  · intro hzero who
    have hproduct :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero who
        (Finset.mem_univ who)
    exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt (hfull who))
  · intro hzero
    apply Finset.sum_eq_zero
    intro who _
    rw [hzero who, mul_zero]

/-- Positive weighted audit and maximum terminal exploitability have exactly
the same fixed-profile zero set. -/
theorem score_eq_zero_iff_terminalExploitability_eq_zero
    [Nonempty ι]
    (law : Law ι) (hfull : law.HasFullSupport)
    (profile : CoordinatorMove reward) :
    score reward law profile = 0 ↔
      quittingTerminalExploitability reward profile = 0 := by
  rw [score_eq_zero_iff_forall_terminalDebt_eq_zero reward law hfull profile]
  constructor
  · intro hzero
    apply le_antisymm
    · unfold quittingTerminalExploitability
      apply finitePlayerMax_le
      intro who
      change max 0 (quittingTerminalDeviationDebt reward profile who) ≤ 0
      rw [hzero who]
      simp
    · exact quittingTerminalExploitability_nonneg reward profile
  · intro hmax who
    have hdebtNonneg := quittingTerminalDeviationDebt_nonneg
      reward profile who
    have hcoordinate : quittingTerminalDeviationDebt reward profile who ≤
        quittingTerminalExploitability reward profile := by
      exact (le_max_right 0 _).trans
        (le_finitePlayerMax (fun player =>
          max 0 (quittingTerminalDeviationDebt reward profile player)) who)
    rw [hmax] at hcoordinate
    exact le_antisymm hcoordinate hdebtNonneg

/-- Uniform auditing recovers total debt divided by the player count. -/
theorem uniform_score_eq_totalDebt_div_card [Nonempty ι]
    (profile : CoordinatorMove reward) :
    score reward (Law.uniform : Law ι) profile =
      quittingTerminalDebtSum reward profile / (Fintype.card ι : ℝ) := by
  rw [score_eq_weightedTerminalDebt]
  change (∑ who, (1 / (Fintype.card ι : ℝ)) *
      quittingTerminalDeviationDebt reward profile who) = _
  unfold quittingTerminalDebtSum
  rw [← Finset.mul_sum]
  ring

/-! ## The Coordinator's value and the exact UE reduction -/

/-- The Coordinator minimizes the optimized random-audit score over actual
behavioral profiles. -/
def value (law : Law ι) : ℝ :=
  sInf (Set.range fun profile : CoordinatorMove reward =>
    score reward law profile)

theorem bddBelow_range_score (law : Law ι) :
    BddBelow (Set.range fun profile : CoordinatorMove reward =>
      score reward law profile) := by
  refine ⟨0, ?_⟩
  rintro scoreValue ⟨profile, rfl⟩
  exact score_nonneg reward law profile

theorem value_nonneg (law : Law ι) :
    0 ≤ value reward law := by
  unfold value
  apply le_csInf (Set.range_nonempty _)
  rintro scoreValue ⟨profile, rfl⟩
  exact score_nonneg reward law profile

/-- A terminal approximate Nash profile has audit score at most its Nash
error, for every probability law. -/
theorem score_le_of_isεAsymptoticNash
    (law : Law ι) (profile : CoordinatorMove reward) {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    score reward law profile ≤ ε := by
  rw [score_eq_weightedTerminalDebt]
  calc
    ∑ who, law.weight who *
          quittingTerminalDeviationDebt reward profile who ≤
        ∑ who, law.weight who * ε := by
          apply Finset.sum_le_sum
          intro who _
          apply mul_le_mul_of_nonneg_left _ (law.weight_nonneg who)
          unfold quittingTerminalDeviationDebt
            quittingContinuationBestResponseValue
          have hnonempty : (Set.range fun deviation :
              (quittingGame reward).BehaviorStrategy who =>
              quittingTerminalPayoff reward
                (Function.update profile who deviation) who).Nonempty :=
            Set.range_nonempty _
          have hcap : sSup (Set.range fun deviation :
              (quittingGame reward).BehaviorStrategy who =>
              quittingTerminalPayoff reward
                (Function.update profile who deviation) who) ≤
              quittingTerminalPayoff reward profile who + ε := by
            apply csSup_le hnonempty
            rintro payoff ⟨deviation, rfl⟩
            exact hnash who deviation
          linarith
    _ = ε := by
      rw [← Finset.sum_mul, law.sum_weight, one_mul]

/-- A UE payoff forces zero value for every audit law. -/
theorem value_eq_zero_of_exists_uniformEquilibriumPayoff
    (law : Law ι)
    (hpayoff : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    value reward law = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpositive : 0 < value reward law :=
      lt_of_not_ge hnot
    have hhalf : 0 < value reward law / 2 := by linarith
    obtain ⟨profile, hnash⟩ :=
      (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
        reward).mp hpayoff (value reward law / 2) hhalf
    have hvalueLeProfile : value reward law ≤ score reward law profile :=
      csInf_le (bddBelow_range_score reward law) ⟨profile, rfl⟩
    have hprofileLe := score_le_of_isεAsymptoticNash
      reward law profile hnash
    linarith
  · exact value_nonneg reward law

/-- With full-support weights, failure of UE existence forces positive audit
value even though the identity of the debtor may vary with the profile. -/
theorem value_pos_of_no_uniformEquilibriumPayoff
    [Nonempty ι]
    (law : Law ι) (hfull : law.HasFullSupport)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    0 < value reward law := by
  obtain ⟨least, _, hleast⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) law.weight
      Finset.univ_nonempty
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hno
  have hlower : law.weight least * gap ≤ value reward law := by
    unfold value
    apply le_csInf (Set.range_nonempty _)
    rintro scoreValue ⟨profile, rfl⟩
    change law.weight least * gap ≤ score reward law profile
    rw [score_eq_weightedTerminalDebt]
    obtain ⟨who, deviation, hgain⟩ := hexploit profile
    have hbest :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who deviation
    have hdebt : gap ≤
        quittingTerminalDeviationDebt reward profile who := by
      unfold quittingTerminalDeviationDebt
      linarith
    have hproduct : law.weight least * gap ≤
        law.weight who * quittingTerminalDeviationDebt reward profile who := by
      exact mul_le_mul (hleast who (Finset.mem_univ who)) hdebt hgap.le
        (law.weight_nonneg who)
    exact hproduct.trans (Finset.single_le_sum
      (fun player _ => mul_nonneg (law.weight_nonneg player)
        (quittingTerminalDeviationDebt_nonneg reward profile player))
      (Finset.mem_univ who))
  exact (mul_pos (hfull least) hgap).trans_le hlower

/-- Every full-support weighted audit gives the same exact fixed-table
zero-value characterization. -/
theorem value_eq_zero_iff_exists_uniformEquilibriumPayoff
    [Nonempty ι]
    (law : Law ι) (hfull : law.HasFullSupport) :
    value reward law = 0 ↔
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · intro hzero
    by_contra hno
    have hpositive := value_pos_of_no_uniformEquilibriumPayoff
      reward law hfull hno
    linarith
  · exact value_eq_zero_of_exists_uniformEquilibriumPayoff reward law

theorem value_pos_iff_no_uniformEquilibriumPayoff
    [Nonempty ι]
    (law : Law ι) (hfull : law.HasFullSupport) :
    0 < value reward law ↔
      ¬ ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · intro hpositive hpayoff
    have hzero := value_eq_zero_of_exists_uniformEquilibriumPayoff
      reward law hpayoff
    linarith
  · exact value_pos_of_no_uniformEquilibriumPayoff reward law hfull

/-- Failure of UE existence gives a positive uniform-audit value.  The player
exposing the positive terminal gap may vary with the Coordinator's profile;
uniform Nature prevents that debt from escaping the audit. -/
theorem uniform_value_pos_of_no_uniformEquilibriumPayoff
    [Nonempty ι]
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    0 < value reward (Law.uniform : Law ι) := by
  obtain ⟨gap, hgap, hexploit⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
      reward).mp hno
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hlower : gap / (Fintype.card ι : ℝ) ≤
      value reward (Law.uniform : Law ι) := by
    unfold value
    apply le_csInf (Set.range_nonempty _)
    rintro scoreValue ⟨profile, rfl⟩
    change gap / (Fintype.card ι : ℝ) ≤
      score reward (Law.uniform : Law ι) profile
    rw [uniform_score_eq_totalDebt_div_card]
    apply div_le_div_of_nonneg_right _ hcard.le
    obtain ⟨who, deviation, hgain⟩ := hexploit profile
    have hbest :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile who deviation
    have hdebt : gap ≤
        quittingTerminalDeviationDebt reward profile who := by
      unfold quittingTerminalDeviationDebt
      linarith
    exact hdebt.trans (Finset.single_le_sum
      (fun player _ => quittingTerminalDeviationDebt_nonneg
        reward profile player)
      (Finset.mem_univ who))
  exact (div_pos hgap hcard).trans_le hlower

/-- **Exact fixed-table reduction.**  The uniform random-deviation audit has
value zero exactly when the quitting game has a uniform-equilibrium payoff.
This is payoff existence, not existence of one exact terminal Nash profile. -/
theorem uniform_value_eq_zero_iff_exists_uniformEquilibriumPayoff
    [Nonempty ι] :
    value reward (Law.uniform : Law ι) = 0 ↔
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · intro hzero
    by_contra hno
    have hpositive := uniform_value_pos_of_no_uniformEquilibriumPayoff
      reward hno
    linarith
  · exact value_eq_zero_of_exists_uniformEquilibriumPayoff reward _

/-- Equivalent terminal formulation: uniform audit value vanishes exactly
when terminal approximate Nash profiles exist at every positive error. -/
theorem uniform_value_eq_zero_iff_terminalNash_all_errors
    [Nonempty ι] :
    value reward (Law.uniform : Law ι) = 0 ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile :=
  (uniform_value_eq_zero_iff_exists_uniformEquilibriumPayoff reward).trans
    (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
      reward)

/-- Positive uniform audit value is exactly failure of UE-payoff existence. -/
theorem uniform_value_pos_iff_no_uniformEquilibriumPayoff
    [Nonempty ι] :
    0 < value reward (Law.uniform : Law ι) ↔
      ¬ ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · intro hpositive hpayoff
    have hzero := value_eq_zero_of_exists_uniformEquilibriumPayoff
      reward (Law.uniform : Law ι) hpayoff
    linarith
  · exact uniform_value_pos_of_no_uniformEquilibriumPayoff reward

/-! ## Compact semantic audit game -/

/-- Uniform expected audit score of a point in the attainable semantic
carrier. -/
def semanticUniformScore [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  quittingTerminalSemanticDebtSum pair / (Fintype.card ι : ℝ)

/-- Compact semantic audit value.  The image is restricted to the actual
profile-generated semantic carrier. -/
def semanticUniformValue [Nonempty ι] : ℝ :=
  sInf (semanticUniformScore (ι := ι) ''
    quittingTerminalSemanticCarrier reward)

theorem semanticUniformScore_nonneg_of_mem_carrier [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    0 ≤ semanticUniformScore (ι := ι) pair := by
  apply div_nonneg
  · unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  · positivity

theorem bddBelow_semanticUniformScores [Nonempty ι] :
    BddBelow (semanticUniformScore (ι := ι) ''
      quittingTerminalSemanticCarrier reward) := by
  refine ⟨0, ?_⟩
  rintro scoreValue ⟨pair, hpair, rfl⟩
  exact semanticUniformScore_nonneg_of_mem_carrier reward pair hpair

/-- A minimum-total-debt carrier point realizes the compact semantic audit
value. -/
theorem semanticUniformValue_eq_of_minimum [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    semanticUniformValue reward = semanticUniformScore (ι := ι) pair := by
  apply le_antisymm
  · unfold semanticUniformValue
    exact csInf_le (bddBelow_semanticUniformScores reward)
      ⟨pair, hpair, rfl⟩
  · unfold semanticUniformValue
    apply le_csInf
    · obtain ⟨candidate, hcandidate⟩ :=
        quittingTerminalSemanticCarrier_nonempty reward
      exact ⟨semanticUniformScore (ι := ι) candidate,
        candidate, hcandidate, rfl⟩
    · rintro scoreValue ⟨candidate, hcandidate, rfl⟩
      exact div_le_div_of_nonneg_right
        (hminimum candidate hcandidate) (by positivity)

/-- The operational profile value equals the compact semantic-carrier value.
Thus compactification adds minimizers but no fictitious lower audit score. -/
theorem uniform_value_eq_semanticUniformValue [Nonempty ι] :
    value reward (Law.uniform : Law ι) = semanticUniformValue reward := by
  obtain ⟨pair, hpair, hminimum⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  rw [semanticUniformValue_eq_of_minimum reward pair hpair hminimum]
  apply le_antisymm
  · obtain ⟨profiles, hprofiles⟩ :=
      exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
    have hsum : Tendsto
        (fun n => quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n))) atTop
        (nhds (quittingTerminalSemanticDebtSum pair)) :=
      continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
        hprofiles
    have hscore : Tendsto
        (fun n => score reward (Law.uniform : Law ι) (profiles n)) atTop
        (nhds (semanticUniformScore (ι := ι) pair)) := by
      have hliteralSum : Tendsto
          (fun n => quittingTerminalDebtSum reward (profiles n)) atTop
          (nhds (quittingTerminalSemanticDebtSum pair)) := by
        simpa only [quittingTerminalDebtSum,
          quittingTerminalSemanticDebtSum, quittingTerminalSemanticPair,
          quittingTerminalSemanticDebt, quittingTerminalDeviationDebt] using hsum
      simpa only [uniform_score_eq_totalDebt_div_card,
        semanticUniformScore] using
          hliteralSum.div_const (Fintype.card ι : ℝ)
    apply ge_of_tendsto hscore
    exact Filter.Eventually.of_forall fun n =>
      csInf_le (bddBelow_range_score reward (Law.uniform : Law ι))
        ⟨profiles n, rfl⟩
  · unfold value
    apply le_csInf (Set.range_nonempty _)
    rintro scoreValue ⟨profile, rfl⟩
    change semanticUniformScore (ι := ι) pair ≤
      score reward (Law.uniform : Law ι) profile
    rw [uniform_score_eq_totalDebt_div_card]
    unfold semanticUniformScore
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hminProfile := hminimum
      (quittingTerminalSemanticPair reward profile)
      (subset_closure ⟨profile, rfl⟩)
    simpa only [quittingTerminalDebtSum,
      quittingTerminalSemanticDebtSum, quittingTerminalSemanticPair,
      quittingTerminalSemanticDebt, quittingTerminalDeviationDebt] using
        hminProfile

/-! ## Canonical positive plateau and the first open cardinality -/

/-- Positive audit value produces the landed canonical positive
minimum-total-debt all-Continue semantic plateau. -/
theorem positive_uniform_value_implies_minimum_allContinue_plateau
    [Nonempty ι]
    (hpositive : 0 < value reward (Law.uniform : Law ι)) :
    HasPositiveMinimumTerminalSemanticPlateau reward := by
  have hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
    (uniform_value_pos_iff_no_uniformEquilibriumPayoff reward).mp hpositive
  let witness : QuittingTerminalExploitabilityWitness reward :=
    quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hno
  exact noUniformPayoff_implies_positiveMinimumSemanticPlateau
    witness

/-- Fewer than four players cannot have positive uniform audit value. -/
theorem not_positive_uniform_value_of_card_lt_four
    [Nonempty ι] (hcard : Fintype.card ι < 4) :
    ¬ 0 < value reward (Law.uniform : Law ι) := by
  intro hpositive
  have hno :=
    (uniform_value_pos_iff_no_uniformEquilibriumPayoff reward).mp hpositive
  let witness : QuittingTerminalExploitabilityWitness reward :=
    quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hno
  have hfour := witness.three_lt_card
  omega

/-- Hence every game with fewer than four players has zero uniform audit
value.  Four is the first open cardinality; this makes no statement reducing
larger games to four players. -/
theorem uniform_value_eq_zero_of_card_lt_four
    [Nonempty ι] (hcard : Fintype.card ι < 4) :
    value reward (Law.uniform : Law ι) = 0 := by
  rw [uniform_value_eq_zero_iff_exists_uniformEquilibriumPayoff]
  by_contra hno
  let witness : QuittingTerminalExploitabilityWitness reward :=
    quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hno
  exact (not_lt_of_ge witness.three_lt_card) hcard

/-! ## Why the audited player cannot be fixed ex ante -/

/-- A four-coordinate abstract debt family in which the zero coordinate
rotates with the Coordinator's move. -/
def rotatingDebt (schedule who : Fin 4) : ℝ :=
  if schedule = who then 0 else 1

@[simp] theorem rotatingDebt_self (who : Fin 4) :
    rotatingDebt who who = 0 := by
  simp [rotatingDebt]

theorem rotatingDebt_nonneg (schedule who : Fin 4) :
    0 ≤ rotatingDebt schedule who := by
  simp [rotatingDebt]
  split <;> norm_num

/-- Every fixed audited coordinate can be driven to zero. -/
theorem sInf_rotatingDebt_coordinate_eq_zero (who : Fin 4) :
    sInf (Set.range fun schedule : Fin 4 => rotatingDebt schedule who) = 0 := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun value hvalue => by
      obtain ⟨schedule, rfl⟩ := hvalue
      exact rotatingDebt_nonneg schedule who⟩ ⟨who, rotatingDebt_self who⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro value ⟨schedule, rfl⟩
    exact rotatingDebt_nonneg schedule who

/-- Yet total debt is always three. -/
theorem sum_rotatingDebt_eq_three (schedule : Fin 4) :
    ∑ who, rotatingDebt schedule who = 3 := by
  fin_cases schedule <;>
    norm_num [rotatingDebt, Fin.sum_univ_four, Fin.ext_iff]

/-- The abstract aggregate-debt infimum stays positive although every fixed
coordinate has infimum zero. -/
theorem sInf_sum_rotatingDebt_eq_three :
    sInf (Set.range fun schedule : Fin 4 =>
      ∑ who, rotatingDebt schedule who) = 3 := by
  rw [show (Set.range fun schedule : Fin 4 =>
      ∑ who, rotatingDebt schedule who) = {3} by
    ext value
    simp [sum_rotatingDebt_eq_three]]
  simp

/-- The maximum debt also stays one. -/
theorem finitePlayerMax_rotatingDebt_eq_one (schedule : Fin 4) :
    finitePlayerMax (rotatingDebt schedule) = 1 := by
  apply le_antisymm
  · apply finitePlayerMax_le
    intro who
    simp [rotatingDebt]
    split <;> norm_num
  · obtain ⟨who, hne⟩ := exists_ne schedule
    have hle := le_finitePlayerMax (rotatingDebt schedule) who
    simpa [rotatingDebt, Ne.symm hne] using hle

theorem sInf_finitePlayerMax_rotatingDebt_eq_one :
    sInf (Set.range fun schedule : Fin 4 =>
      finitePlayerMax (rotatingDebt schedule)) = 1 := by
  rw [show (Set.range fun schedule : Fin 4 =>
      finitePlayerMax (rotatingDebt schedule)) = {1} by
    ext value
    simp [finitePlayerMax_rotatingDebt_eq_one]]
  simp

/-! ## Four players: symmetric before the draw, `1 + 3` afterward -/

/-- Once Nature selects the audited player, the opponents are its complement.
No symmetry of the reward table or strategy profile is imposed. -/
abbrev AuditedOpponents (who : Fin 4) := {other : Fin 4 // other ≠ who}

theorem card_auditedOpponents (who : Fin 4) :
    Fintype.card (AuditedOpponents who) = 3 := by
  simp [AuditedOpponents]

end RandomDeviationAudit
end GameTheory
