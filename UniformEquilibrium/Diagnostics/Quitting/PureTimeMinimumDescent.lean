import UniformEquilibrium.Diagnostics.Quitting.PureTimeCapAttainment
import UniformEquilibrium.Diagnostics.Quitting.PureTimePositiveMinimumAllNever
import UniformEquilibrium.Diagnostics.Quitting.PureTimeSingletonMinimumResponse

/-!
# Canonical positive-minimum deadline descent

Anchored `Never` erasures reduce the first quitting coalition to one owner.
An exact screened response then either leaves the global minimum or strictly
decreases finite deadline rank.  The all-`Never` endpoint cannot remain at a
positive global minimum.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total terminal semantic debt of a canonical pure-time profile. -/
def quittingPureTimeTerminalSemanticDebtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) : ℝ :=
  quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingPureTimeProfileBehavior reward times))

omit [DecidableEq ι] in
private theorem quittingPureTimeProfileBehavior_eq_allContinue_of_support_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι)
    (hsupport : quittingPureTimeDeadlineSupport times = ∅) :
    quittingPureTimeProfileBehavior reward times =
      quittingAlwaysContinueProfile reward := by
  have hallNever : ∀ who, times who = none := by
    intro who
    cases htime : times who with
    | none => rfl
    | some time =>
        have hmem : time ∈ quittingPureTimeDeadlineSupport times :=
          (mem_quittingPureTimeDeadlineSupport_iff times time).2 ⟨who, htime⟩
        rw [hsupport] at hmem
        simp at hmem
  funext who
  rw [quittingPureTimeProfileBehavior_apply, hallNever who,
    quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
  rfl

private theorem pureTimeMinimum_oneRound_exit_or_rank_descent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ)
    (hlower : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < minimumDebt)
    (times : QuittingPureTimeProfile ι)
    (hminimum : quittingPureTimeTerminalSemanticDebtSum reward times = minimumDebt) :
    (∃ target,
      IsQuittingPureTimeReplacementAncestry times target ∧
      minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward target) ∨
    ∃ next,
      IsQuittingPureTimeReplacementAncestry times next ∧
      quittingPureTimeTerminalSemanticDebtSum reward next = minimumDebt ∧
      quittingPureTimeDeadlineRank next <
        quittingPureTimeDeadlineRank times := by
  have hsupport : (quittingPureTimeDeadlineSupport times).Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    have hbehavior :=
      quittingPureTimeProfileBehavior_eq_allContinue_of_support_empty
        reward times hnot
    have hminimumAll : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAlwaysContinueProfile reward)) ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [← hbehavior]
      change quittingPureTimeTerminalSemanticDebtSum reward times ≤ _
      rw [hminimum]
      exact hlower candidate hcandidate
    have hpositiveAll : 0 < quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAlwaysContinueProfile reward)) := by
      rw [← hbehavior]
      change 0 < quittingPureTimeTerminalSemanticDebtSum reward times
      rw [hminimum]
      exact hpositive
    exact not_allNever_positiveMinimumTerminalSemanticDebt
      reward hminimumAll hpositiveAll
  obtain ⟨deadline, hcoalition, hfirst⟩ :=
    exists_quittingPureTime_firstDeadline times hsupport
  obtain ⟨owner, hownerMem⟩ := hcoalition
  let erasedPlayers := (quittingPureTimeCoalitionAt times deadline).erase owner
  let singletonTimes := quittingPureTimeErasePlayers times erasedPlayers
  have herased : IsQuittingPureTimeReplacementAncestry times singletonTimes :=
    isQuittingPureTimeReplacementAncestry_erasePlayers times erasedPlayers
  have hsingleton :
      quittingPureTimeCoalitionAt singletonTimes deadline = {owner} := by
    change quittingPureTimeCoalitionAt
      (quittingPureTimeErasePlayers times erasedPlayers) deadline = {owner}
    rw [quittingPureTimeCoalitionAt_erasePlayers]
    ext who
    simp only [erasedPlayers, Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hmem, hnot⟩
      by_contra hne
      exact hnot ⟨hne, hmem⟩
    · rintro rfl
      exact ⟨hownerMem, by simp⟩
  have hfirstSingleton : ∀ time < deadline,
      quittingPureTimeCoalitionAt singletonTimes time = ∅ := by
    intro time htime
    rw [quittingPureTimeCoalitionAt_erasePlayers, hfirst time htime]
    simp
  have hrankErase : quittingPureTimeDeadlineRank singletonTimes ≤
      quittingPureTimeDeadlineRank times :=
    quittingPureTimeDeadlineRank_erasePlayers_le times erasedPlayers
  let singletonPair := quittingTerminalSemanticPair reward
    (quittingPureTimeProfileBehavior reward singletonTimes)
  have hsingletonCarrier : singletonPair ∈
      quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨_, rfl⟩
  have hsingletonLower : minimumDebt ≤
      quittingPureTimeTerminalSemanticDebtSum reward singletonTimes := by
    exact hlower singletonPair hsingletonCarrier
  rcases lt_or_eq_of_le hsingletonLower with hstrict | hequal
  · exact Or.inl ⟨singletonTimes, herased, hstrict⟩
  · have hsingletonMinimum :
        quittingPureTimeTerminalSemanticDebtSum reward singletonTimes = minimumDebt :=
      hequal.symm
    by_cases hopponentSupport :
        (quittingPureTimeOpponentDeadlineSupport singletonTimes owner).Nonempty
    · obtain ⟨opponentDeadline, hopponentsAt, hopponentsBefore⟩ :=
        exists_quittingPureTime_firstOpponentDeadline
          singletonTimes owner hopponentSupport
      have hdeadlineLt : deadline < opponentDeadline := by
        by_contra hnot
        have hle := le_of_not_gt hnot
        rcases lt_or_eq_of_le hle with hlt | heq
        · have hempty := hfirstSingleton opponentDeadline hlt
          have hsubset : quittingPureTimeOpponentCoalitionAt
              singletonTimes owner opponentDeadline = ∅ := by
            rw [quittingPureTimeOpponentCoalitionAt, hempty]
            simp
          rw [hsubset] at hopponentsAt
          exact Finset.not_nonempty_empty hopponentsAt
        · subst opponentDeadline
          rw [quittingPureTimeOpponentCoalitionAt, hsingleton] at hopponentsAt
          simp at hopponentsAt
      have howner : singletonTimes owner = some deadline := by
        have : owner ∈ quittingPureTimeCoalitionAt singletonTimes deadline := by
          rw [hsingleton]
          simp
        simpa [quittingPureTimeCoalitionAt] using this
      obtain ⟨replacement, _, honeStep, _, _, houtcome⟩ :=
        pureTimeSingletonMinimum_response_or_deadlineRank_strict
          reward singletonTimes owner deadline opponentDeadline howner
          hfirstSingleton hsingleton hdeadlineLt hopponentsBefore hopponentsAt
          (by
            intro candidate hcandidate
            change quittingPureTimeTerminalSemanticDebtSum reward singletonTimes ≤ _
            rw [hsingletonMinimum]
            exact hlower candidate hcandidate)
          (by
            change 0 < quittingPureTimeTerminalSemanticDebtSum reward singletonTimes
            rw [hsingletonMinimum]
            exact hpositive)
      let next := Function.update singletonTimes owner replacement
      have hancestry : IsQuittingPureTimeReplacementAncestry times next :=
        herased.trans (Relation.ReflTransGen.single honeStep)
      rcases houtcome with hnextStrict | ⟨hnextEqual, hrankStrict⟩
      · exact Or.inl ⟨next, hancestry, by
          rw [← hsingletonMinimum]
          simpa only [quittingPureTimeTerminalSemanticDebtSum, next] using hnextStrict⟩
      · exact Or.inr ⟨next, hancestry, by
          rw [← hsingletonMinimum]
          simpa only [quittingPureTimeTerminalSemanticDebtSum, next] using hnextEqual,
          hrankStrict.trans_le hrankErase⟩
    · let allNever := Function.update singletonTimes owner none
      have hallNever : allNever = fun _ : ι => none := by
        funext who
        by_cases heq : who = owner
        · subst who
          simp [allNever]
        · have hotherNone : singletonTimes who = none := by
            cases htime : singletonTimes who with
            | none => rfl
            | some time =>
                exfalso
                apply hopponentSupport
                exact ⟨time,
                  (mem_quittingPureTimeOpponentDeadlineSupport_iff
                    singletonTimes owner time).2 ⟨who, heq, htime⟩⟩
          simp [allNever, Function.update_of_ne heq, hotherNone]
      have hallNeverBehavior : quittingPureTimeProfileBehavior reward allNever =
          quittingAlwaysContinueProfile reward := by
        rw [hallNever]
        apply quittingPureTimeProfileBehavior_eq_allContinue_of_support_empty
        simp
      let allNeverPair := quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward allNever)
      have hallNeverCarrier : allNeverPair ∈
          quittingTerminalSemanticCarrier reward := by
        apply subset_closure
        exact ⟨_, rfl⟩
      have hallNeverLower : minimumDebt ≤
          quittingPureTimeTerminalSemanticDebtSum reward allNever :=
        hlower allNeverPair hallNeverCarrier
      have hallNeverNe :
          quittingPureTimeTerminalSemanticDebtSum reward allNever ≠ minimumDebt := by
        intro heq
        have hminimumAll : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
            quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (quittingAlwaysContinueProfile reward)) ≤
              quittingTerminalSemanticDebtSum candidate := by
          intro candidate hcandidate
          rw [← hallNeverBehavior]
          change quittingPureTimeTerminalSemanticDebtSum reward allNever ≤ _
          rw [heq]
          exact hlower candidate hcandidate
        have hpositiveAll : 0 < quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAlwaysContinueProfile reward)) := by
          rw [← hallNeverBehavior]
          change 0 < quittingPureTimeTerminalSemanticDebtSum reward allNever
          rw [heq]
          exact hpositive
        exact not_allNever_positiveMinimumTerminalSemanticDebt
          reward hminimumAll hpositiveAll
      exact Or.inl ⟨allNever,
        herased.trans (isQuittingPureTimeReplacementAncestry_update
          singletonTimes owner none),
        lt_of_le_of_ne hallNeverLower (Ne.symm hallNeverNe)⟩

/-- Every canonical pure-time realization of a positive global minimum has a
finite literal unilateral-replacement descendant strictly above that
minimum. -/
theorem pureTimeMinimum_exists_offMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ)
    (hlower : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < minimumDebt)
    (times : QuittingPureTimeProfile ι)
    (hminimum : quittingPureTimeTerminalSemanticDebtSum reward times = minimumDebt) :
    ∃ target,
      IsQuittingPureTimeReplacementAncestry times target ∧
      minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward target := by
  let Minimum := fun current : QuittingPureTimeProfile ι =>
    quittingPureTimeTerminalSemanticDebtSum reward current = minimumDebt
  let Exit := fun current : QuittingPureTimeProfile ι =>
    ∃ target,
      IsQuittingPureTimeReplacementAncestry current target ∧
      minimumDebt < quittingPureTimeTerminalSemanticDebtSum reward target
  have hstep : ∀ current, Minimum current →
      Exit current ∨
        ∃ next,
          IsQuittingPureTimeReplacementAncestry current next ∧
          Minimum next ∧
          quittingPureTimeDeadlineRank next <
            quittingPureTimeDeadlineRank current := by
    intro current hcurrent
    exact pureTimeMinimum_oneRound_exit_or_rank_descent
      reward minimumDebt hlower hpositive current hcurrent
  obtain ⟨source, hsource, target, htarget, hoff⟩ :=
    exists_pureTimeReplacementAncestry_of_ancestry_deadlineRank_descent
      Minimum Exit hstep times hminimum
  exact ⟨target, hsource.trans htarget, hoff⟩

end GameTheory
