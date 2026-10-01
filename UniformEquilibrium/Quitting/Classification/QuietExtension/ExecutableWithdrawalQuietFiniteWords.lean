import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalSourceAmplification
import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalQuietFiniteWordAssembly

/-! # Executable raw-table quiet finite-word search

Full raw certificates or F/J certificates plus an actual positive singleton
supply erased termination proofs. The actual source weights and K are computed
BEFORE accuracy. The output is the canonical child word at accuracy/K, with the
same calendar and literal Never outsiders; no fixed target is computed.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {players childPlayers : ℕ}

section Full

variable (reward : RationalQuittingReward players)
  (deleted : Fin players → Prop) [DecidablePred deleted]
  [Nonempty (QuittingChildPlayer deleted)] [Nonempty {who : Fin players // deleted who}]
  (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind)
  (hsource : FullSource reward deleted kind)

theorem fullSource_quietLift
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame
      (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).BehaviorProfile)
    (hnash : (quittingGame
      (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)) error profile) :
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
      ((fullAmplification reward deleted kind hsource : ℝ) * error)
      (quittingLiftDeletedProfile (rationalQuittingRewardToReal reward) deleted profile) := by
  let : Nonempty (Fin players) := Nonempty.map Subtype.val
    (inferInstance : Nonempty (QuittingChildPlayer deleted))
  refine isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds deleted
    (rationalQuittingRewardToReal reward)
    (fun outside => (fullSourceCertificate reward deleted kind hsource outside).debtWeight)
    (fun outside i =>
      (fullSourceCertificate reward deleted kind hsource outside).debtWeight_nonneg i)
    (fullAmplification reward deleted kind hsource)
    (by exact_mod_cast fullAmplification_ge_one reward deleted kind hsource)
    ?_ herror profile ?_ hnash
  · intro outside
    rw [fullAmplification_cast]
    exact (Finset.le_sup' (f := fun outside =>
      ∑ i, (fullSourceCertificate reward deleted kind hsource outside).debtWeight i)
      (Finset.mem_univ outside)).trans (le_max_right _ _)
  · intro outside
    apply quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound
      deleted (rationalQuittingRewardToReal reward) outside
      (fullSourceCertificate reward deleted kind hsource outside).debtWeight
    dsimp only
    intro childProfile
    have h := withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess
      (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside)
      (fullSourceCertificate reward deleted kind hsource outside) childProfile
    simpa only [fullSourceCertificate_excess_eq_zero, zero_mul, add_zero] using h

/-- Executable source-to-word map. All source coefficients are independent of accuracy. -/
def fullWord (label : QuittingChildPlayer deleted ≃ Fin childPlayers)
    (hchild : childPlayers ≤ 3) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot childPlayers) :=
  rationalQuittingDeletedChildWord reward deleted label hchild
    (accuracy / fullAmplification reward deleted kind hsource)
    (div_pos haccuracy (lt_of_lt_of_le (by norm_num)
      (fullAmplification_ge_one reward deleted kind hsource)))

/-- Same computed child word, same exact rational atoms, and full behavioral terminal regret. -/
theorem fullWord_finiteLaws (label : QuittingChildPlayer deleted ≃ Fin childPlayers)
    (hchild : childPlayers ≤ 3) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := fullWord reward deleted kind hsource label hchild accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ outside, deleted outside → mixed outside = PMF.pure none) ∧
      (∀ child : QuittingChildPlayer deleted, ∀ choice, (mixed child.1 choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length (label child) choice : ℝ)) ∧
      ∀ who, quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) who < (accuracy : ℝ) := by
  dsimp only [fullWord]
  exact rationalQuittingQuietFiniteWordLaws_of_terminalNashLift reward deleted label hchild
      (fullAmplification reward deleted kind hsource)
      (fullAmplification_ge_one reward deleted kind hsource)
      (fun _ herror profile hnash =>
        fullSource_quietLift reward deleted kind hsource herror profile hnash)
      accuracy haccuracy

end Full

section FutureJoin

variable (reward : RationalQuittingReward players)
  (deleted : Fin players → Prop) [DecidablePred deleted]
  [Nonempty {who : Fin players // deleted who}]
  (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind)
  (hsource : FutureJoinSource reward deleted kind)
  (pivot : QuittingChildPlayer deleted)

/-- The actual positive-singleton hypothesis is not an input to coefficient computation. -/
def futureJoinWord (label : QuittingChildPlayer deleted ≃ Fin childPlayers)
    (hchild : childPlayers ≤ 3) (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot childPlayers) :=
  rationalQuittingDeletedChildWord reward deleted label hchild
    (accuracy / futureJoinAmplification reward deleted kind hsource pivot)
    (div_pos haccuracy (lt_of_lt_of_le (by norm_num)
      (futureJoinAmplification_ge_one reward deleted kind hsource pivot)))

/-- The computed omitted-Never correction is paid by the actual original child singleton.
The acceptance conclusion is TERMINAL-only and covers all five outsider-dependent kinds. -/
theorem futureJoinWord_finiteLaws
    (hpivot : 0 < rationalQuittingRewardToReal reward (quittingSingletonTerminal pivot.1) pivot.1)
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := futureJoinWord reward deleted kind hsource pivot label hchild accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ outside, deleted outside → mixed outside = PMF.pure none) ∧
      (∀ child : QuittingChildPlayer deleted, ∀ choice, (mixed child.1 choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length (label child) choice : ℝ)) ∧
      ∀ who, quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) who < (accuracy : ℝ) := by
  let : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  have hlift : ∀ error : ℝ, 0 ≤ error →
      ∀ profile : (quittingGame
        (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).BehaviorProfile,
      (quittingGame
        (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)) error profile →
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
        ((futureJoinAmplification reward deleted kind hsource pivot : ℝ) * error)
        (quittingLiftDeletedProfile (rationalQuittingRewardToReal reward) deleted profile) := by
    intro error herror profile hnash
    rw [futureJoinAmplification_cast]
    exact isεAsymptoticNash_quietLift_of_withdrawalFutureJoinFamily
      deleted (rationalQuittingRewardToReal reward) kind
      (futureJoinSourceCertificate reward deleted kind hsource) pivot hpivot herror profile hnash
  dsimp only [futureJoinWord]
  exact rationalQuittingQuietFiniteWordLaws_of_terminalNashLift reward deleted label hchild
      (futureJoinAmplification reward deleted kind hsource pivot)
      (futureJoinAmplification_ge_one reward deleted kind hsource pivot)
      hlift accuracy haccuracy

end FutureJoin

end GameTheory.ExecutableWithdrawal
