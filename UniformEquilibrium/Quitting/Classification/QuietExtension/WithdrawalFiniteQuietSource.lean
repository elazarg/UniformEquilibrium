import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinFixedTarget
import UniformEquilibrium.Quitting.Classification.QuietExtension.QuietLiftFiniteCensor
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Finite quiet sources selected from original withdrawal certificates

A nonnegative low-player singleton suffices, including zero. Certificate
constants precede the accuracy; child marginals are selected internally.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open _root_.Math.Probability
open Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Original five-kind finite reward data produce actual finite independent
child menus and literal quiet parent lifts, with both quantitative bounds. -/
theorem exists_finiteQuietProfiles_of_withdrawalFutureJoinFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (kind : {who : ι // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : ι // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (hcard : Fintype.card (QuittingChildPlayer deleted) ≤ 3)
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 ≤ reward (quittingSingletonTerminal pivot.1) pivot.1)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    let : Nonempty ι := ⟨pivot.1⟩
    ∃ factor residual : ℝ, 1 ≤ factor ∧ 0 ≤ residual ∧
      (∀ outside, (∑ who, (certificate outside).debtWeight who) ≤ factor) ∧
      (∀ outside, (certificate outside).neverExcess ≤ residual) ∧
      ∀ delta : ℝ, 0 < delta → ∃ deadline : ℕ, 0 < deadline ∧
        ∃ mixed : QuittingChildPlayer deleted →
            PMF (QuittingFiniteDeadlineTimingAction deadline),
          quittingTerminalExploitability reward
              (quittingLiftDeletedProfile reward deleted
                (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
                  deadline mixed)) ≤
            (factor + residual) * delta + (factor + 4 * bound) * delta ^ 2 ∧
          (∏ who, (quittingBehaviorStoppingLaw (quittingDeleteReward reward deleted)
            (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
              deadline mixed who) none).toReal) ≤ delta + delta ^ 2 := by
  let : Nonempty ι := ⟨pivot.1⟩
  let : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  obtain ⟨factor, residual, hfactor, hresidual, hweight, hexcess, hfamily⟩ :=
    exists_quietProfiles_smallExploitability_smallNever_of_withdrawalFutureJoinFamily
      deleted reward kind certificate hcard pivot hpivot
  refine ⟨factor, residual, hfactor, hresidual, hweight, hexcess, ?_⟩
  intro delta hdelta
  obtain ⟨profile, hexploit, hnever⟩ := hfamily delta hdelta
  obtain ⟨deadline, hdeadline, mixed, hfinite, hfiniteNever⟩ :=
    exists_finiteQuietLift_of_profile reward deleted profile
      (by positivity : 0 < delta ^ 2 / 2) hbound hreward
  refine ⟨deadline, hdeadline, mixed, ?_, ?_⟩
  · have h := hfinite.trans (add_le_add hexploit le_rfl)
    nlinarith [mul_nonneg hbound (sq_nonneg delta)]
  · linarith

/-- One target is selected from one internally produced indexed family of
finite quiet lifts. Every accuracy retains a member of that same family. -/
theorem exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (kind : {who : ι // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : ι // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (hcard : Fintype.card (QuittingChildPlayer deleted) ≤ 3)
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 ≤ reward (quittingSingletonTerminal pivot.1) pivot.1) :
    let : Nonempty ι := ⟨pivot.1⟩
    ∃ deadlines : ℕ → ℕ,
      ∃ mixed : ∀ n, QuittingChildPlayer deleted →
          PMF (QuittingFiniteDeadlineTimingAction (deadlines n)),
        ∃ payoff : Payoff ι,
          (∀ n, 0 < deadlines n) ∧
          Tendsto (fun n => quittingTerminalExploitability reward
            (quittingLiftDeletedProfile reward deleted
              (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
                (deadlines n) (mixed n)))) atTop (nhds 0) ∧
          Tendsto (fun n => ∏ who, (quittingBehaviorStoppingLaw
            (quittingDeleteReward reward deleted)
            (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
              (deadlines n) (mixed n) who) none).toReal) atTop (nhds 0) ∧
          ∀ error : ℝ, 0 < error → ∃ n threshold : ℕ,
            ∀ horizon, threshold ≤ horizon →
              (quittingGame reward).IsεHorizonNash none horizon error
                (quittingLiftDeletedProfile reward deleted
                  (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
                    (deadlines n) (mixed n))) ∧
              ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
                (quittingLiftDeletedProfile reward deleted
                  (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
                    (deadlines n) (mixed n))) who - payoff who| ≤ error := by
  let : Nonempty ι := ⟨pivot.1⟩
  obtain ⟨factor, residual, _, _, _, _, hfamily⟩ :=
    exists_finiteQuietProfiles_of_withdrawalFutureJoinFamily deleted reward kind certificate
      hcard pivot hpivot (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  let delta := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hpositive : ∀ n, 0 < delta n := by intro n; dsimp [delta]; positivity
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simpa [delta] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  choose deadlines hdeadlines mixed hexploit hnever using fun n => hfamily (delta n) (hpositive n)
  let profiles := fun n => quittingLiftDeletedProfile reward deleted
    (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
      (deadlines n) (mixed n))
  let errors := fun n => (factor + residual) * delta n +
    (factor + 4 * quittingRewardBound reward) * delta n ^ 2
  have herrors : Tendsto errors atTop (nhds 0) := by
    simpa only [errors, mul_zero, zero_pow (by omega : 2 ≠ 0), zero_add] using
      (tendsto_const_nhds.mul hdelta).add (tendsto_const_nhds.mul (hdelta.pow 2))
  have hnash : ∀ n, (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (errors n) (profiles n) :=
    fun n => isεAsymptoticNash_of_quittingTerminalExploitability_le (profiles n) (hexploit n)
  obtain ⟨payoff, _, hwitnesses⟩ :=
    quittingGame_exists_uniformPayoffWitnesses_of_terminalNash_family
      reward errors profiles herrors hnash
  refine ⟨deadlines, mixed, payoff, hdeadlines, ?_, ?_, hwitnesses⟩
  · exact squeeze_zero
      (fun n => quittingTerminalExploitability_nonneg reward (profiles n)) hexploit herrors
  · apply squeeze_zero (fun n => Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg) hnever
    simpa only [zero_pow (by omega : 2 ≠ 0), zero_add] using hdelta.add (hdelta.pow 2)

/-- The retained finite quiet family yields a parent uniform-equilibrium payoff
without prescribing the child's target. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_nonnegativeSingleton_withdrawalFamily
    (deleted : ι → Prop) [DecidablePred deleted]
    [Nonempty {who : ι // deleted who}]
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (kind : {who : ι // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : ι // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (hcard : Fintype.card (QuittingChildPlayer deleted) ≤ 3)
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 ≤ reward (quittingSingletonTerminal pivot.1) pivot.1) :
    ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨deadlines, mixed, payoff, _, _, _, hwitnesses⟩ :=
    exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily
      deleted reward kind certificate hcard pivot hpivot
  refine ⟨payoff, fun error herror => ?_⟩
  obtain ⟨n, threshold, hwitness⟩ := hwitnesses error herror
  exact ⟨quittingLiftDeletedProfile reward deleted
    (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
      (deadlines n) (mixed n)), threshold, hwitness⟩

/-- The Fin4 existence boundary includes a zero child singleton. The proper
child cardinality bound is supplied internally, not assumed. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finFour_nonnegativeWithdrawalFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {A : Finset (Fin 4) // A.Nonempty} → Payoff (Fin 4))
    (kind : {who : Fin 4 // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 ≤ reward (quittingSingletonTerminal pivot.1) pivot.1) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨⟨outside, houtside⟩⟩ :=
    (inferInstance : Nonempty {who : Fin 4 // deleted who})
  have hlt : Fintype.card (QuittingChildPlayer deleted) < 4 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := fun who : Fin 4 => ¬ deleted who)
        (x := outside) (not_not.mpr houtside))
  exact quittingGame_exists_uniformEquilibriumPayoff_of_nonnegativeSingleton_withdrawalFamily
    deleted reward kind certificate (Nat.le_of_lt_succ hlt) pivot hpivot

end GameTheory
