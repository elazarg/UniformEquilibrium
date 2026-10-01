import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan
import UniformEquilibrium.Quitting.Root.RationalPayoffDebtThresholdScan
import UniformEquilibrium.Quitting.Root.RationalFiniteWordSearch
import UniformEquilibrium.Quitting.Root.RationalQuittingRootGridSelector
import UniformEquilibrium.Quitting.Paths.ExecutableRationalCapThresholdBlock
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Shared literal data and checked semantic bridges for threshold regressions -/

namespace GameTheory.CapThresholdRegression

open QuittingSureSetOwnerRepair

def pureRoot {n : ℕ} (coalition : Finset (Fin n)) : RationalQuittingRoot n where
  probability := fun who => if who ∈ coalition then 1 else 0
  nonnegative := by intro who; split <;> norm_num
  le_one := by intro who; split <;> norm_num

theorem pureRoot_toPMF {n : ℕ} (coalition : Finset (Fin n)) :
    (pureRoot coalition).toPMF = quittingPureSetRoot coalition := by
  funext who
  apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro action
  cases action <;> by_cases hmem : who ∈ coalition <;>
    simp [pureRoot, quittingPureSetRoot, quittingSetAction, hmem, PMF.pure_apply]

noncomputable def profile {n : ℕ} (reward : RationalQuittingReward n)
    (word : List (RationalQuittingRoot n)) :=
  quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    (word.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))

theorem actual_pair {n : ℕ} (reward : RationalQuittingReward n)
    (word : List (RationalQuittingRoot n)) (pair : RationalQuittingSemanticPair n)
    (heval : rationalQuittingFiniteWordSemanticPair reward word = pair) :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
      (profile reward word) = pair.toReal := by
  unfold profile
  simpa only [heval, RationalQuittingSemanticPair.toReal] using
    quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word

theorem actual_debt {n : ℕ} (reward : RationalQuittingReward n)
    (word : List (RationalQuittingRoot n)) (debt : ℚ)
    (heval : rationalFiniteSourceDebt reward word = debt) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (profile reward word)) = (debt : ℝ) := by
  rw [profile, quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast]
  exact congrArg (fun q : ℚ => (q : ℝ)) heval

/-- The same literal word has independent finite-date/Never laws with its full cap. -/
theorem finite_laws {n : ℕ} (reward : RationalQuittingReward n)
    (word : List (RationalQuittingRoot n)) :
    ∃ mixed : Fin n → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (profile reward word) := by
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  refine ⟨mixed, hmass, ?_⟩
  exact hpair.trans (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word).symm

theorem actual_solo_word_pair {n : ℕ} (reward : RationalQuittingReward n)
    (source : List (RationalQuittingRoot n)) (owner : Fin n) (hazard : ℚ)
    (hhazard : hazard ∈ Set.Icc 0 1) (steps : ℕ) :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (profile reward (List.replicate steps (rationalQuittingSoloRoot owner hazard) ++
          source)) =
      quittingSoloSemanticIterate (rationalQuittingRewardToReal reward) owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hhazard.1) (by exact_mod_cast hhazard.2))
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (profile reward source)) steps := by
  unfold profile
  rw [quittingTerminalSemanticPair_rationalSoloPrefix_eq_iterate reward source owner hhazard,
    quittingTerminalSemanticPair_rationalFiniteWord_eq_cast]
  exact (quittingSoloSemanticIterate_rational_eq_cast reward owner hhazard _ steps).symm

/-- Feed explicitly verified model inequalities into the canonical first-hit
affine ledger. No new cap recurrence or stopping-time theorem is proved here. -/
theorem solo_affine_up_to {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι) (owner : ι) {M θ : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (cutoff : ℕ)
    (hmodel : ∀ k < cutoff, ∀ who,
      4 * M * θ <
        (if who = owner then source.2 owner else
          reward (quittingSingletonTerminal owner) who + (1 - θ) ^ k *
            (source.2 who - reward (quittingSingletonTerminal owner) who)) -
          reward (quittingSingletonTerminal who) who) :
    ∀ k ≤ cutoff,
      quittingSoloSemanticIterate reward owner
          (quittingHazardCoin θ hθ0.le hθ1.le) source k =
        (fun who => reward (quittingSingletonTerminal owner) who + (1 - θ) ^ k *
            (source.1 who - reward (quittingSingletonTerminal owner) who),
         fun who => if who = owner then source.2 owner else
          reward (quittingSingletonTerminal owner) who + (1 - θ) ^ k *
            (source.2 who - reward (quittingSingletonTerminal owner) who)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      apply quittingSoloSemanticIterate_eq_affine_of_before_threshold
        reward source owner hreward hsource hθ0 hθ1 k
      intro earlier hearlier who
      rw [ih earlier hearlier (Nat.le_trans hearlier.le hk)]
      exact hmodel earlier (Nat.lt_of_lt_of_le hearlier hk) who

end GameTheory.CapThresholdRegression
