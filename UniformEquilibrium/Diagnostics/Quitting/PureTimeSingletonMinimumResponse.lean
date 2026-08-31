import UniformEquilibrium.Diagnostics.Quitting.PureTimeScreenedMenu
import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineRank

/-!
# Exact screened response from a singleton pure-time minimum

The first opponent deadline gives the two screened response endpoints.  At a
positive global semantic-debt minimum, the singleton margin forces one of
those endpoints to attain the unrestricted cap.  Replacing the singleton
owner by that endpoint either leaves the minimum fibre with paid gain or
returns to it with strictly smaller deadline rank.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One exact cap response from a canonical singleton minimum either exits
the minimum fibre or returns to it after strictly deleting the owner's old
deadline. -/
theorem pureTimeSingletonMinimum_response_or_deadlineRank_strict
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (owner : ι)
    (ownerDeadline opponentDeadline : ℕ)
    (howner : times owner = some ownerDeadline)
    (hfirst : ∀ time < ownerDeadline,
      quittingPureTimeCoalitionAt times time = ∅)
    (hsingleton : quittingPureTimeCoalitionAt times ownerDeadline = {owner})
    (hdeadline : ownerDeadline < opponentDeadline)
    (hopponentsBefore : ∀ time < opponentDeadline,
      quittingPureTimeOpponentCoalitionAt times owner time = ∅)
    (hopponentsAt :
      (quittingPureTimeOpponentCoalitionAt times owner opponentDeadline).Nonempty)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward times))) :
    ∃ replacement : Option ℕ,
      (replacement = some opponentDeadline ∨ replacement = none) ∧
      IsQuittingPureTimeUnilateralReplacement times
        (Function.update times owner replacement) ∧
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times owner replacement)) owner =
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward times)).2 owner ∧
      quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward
              (Function.update times owner replacement)) owner -
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)).1 owner =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)) ∧
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingPureTimeProfileBehavior reward
                (Function.update times owner replacement))) ∨
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingPureTimeProfileBehavior reward
                (Function.update times owner replacement))) =
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward times)) ∧
          quittingPureTimeDeadlineRank
              (Function.update times owner replacement) <
            quittingPureTimeDeadlineRank times)) := by
  let profile := quittingPureTimeProfileBehavior reward times
  let pair := quittingTerminalSemanticPair reward profile
  let debt := quittingTerminalSemanticDebtSum pair
  let opponentCoalition :=
    quittingPureTimeOpponentCoalitionAt times owner opponentDeadline
  let joinValue := reward
    ⟨insert owner opponentCoalition, Finset.insert_nonempty owner _⟩ owner
  let passValue := reward ⟨opponentCoalition, by
    simpa only [opponentCoalition] using hopponentsAt⟩ owner
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨profile, rfl⟩
  have hnonnegative : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hownerDebtLe : quittingTerminalSemanticDebt pair owner ≤ debt := by
    dsimp only [debt]
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun who _ => hnonnegative who) (Finset.mem_univ owner)
  have hprescribed : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner := by
    have hpayoff := quittingTerminalPayoff_pureTimeProfileBehavior_eq
      reward times ownerDeadline hfirst (by rw [hsingleton]; simp)
    dsimp only [pair, profile, quittingTerminalSemanticPair]
    simpa [hsingleton, quittingSingletonTerminal] using congrFun hpayoff owner
  have hcap : pair.2 owner =
      max (reward (quittingSingletonTerminal owner) owner)
        (max joinValue passValue) := by
    change quittingContinuationBestResponseValue reward profile owner = _
    simpa only [profile, opponentCoalition, joinValue, passValue] using
      quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
        reward times owner opponentDeadline (by omega)
          hopponentsBefore hopponentsAt
  have hmargin : debt ≤ pair.2 owner -
      reward (quittingSingletonTerminal owner) owner := by
    simpa only [pair, debt] using
      minimumTerminalSemantic_singletonMargin pair hpair hminimum hpositive owner
  have hownerDebt : quittingTerminalSemanticDebt pair owner = debt := by
    apply le_antisymm hownerDebtLe
    unfold quittingTerminalSemanticDebt
    rw [hprescribed]
    exact hmargin
  have hcapSub : pair.2 owner - pair.1 owner = debt := by
    simpa only [quittingTerminalSemanticDebt] using hownerDebt
  have hsingleLtCap :
      reward (quittingSingletonTerminal owner) owner < pair.2 owner := by
    rw [hprescribed] at hcapSub
    linarith
  have hsingleLtEndpoints :
      reward (quittingSingletonTerminal owner) owner < max joinValue passValue := by
    by_contra hnot
    have hle : max joinValue passValue ≤
        reward (quittingSingletonTerminal owner) owner := le_of_not_gt hnot
    rw [hcap, max_eq_left hle] at hsingleLtCap
    exact (lt_irrefl _ hsingleLtCap)
  have hendpoints : max joinValue passValue = pair.2 owner := by
    rw [hcap, max_eq_right hsingleLtEndpoints.le]
  obtain ⟨other, hotherAt⟩ := hopponentsAt
  have hopponentsAt' :
      (quittingPureTimeOpponentCoalitionAt times owner opponentDeadline).Nonempty :=
    ⟨other, hotherAt⟩
  have hotherNe : other ≠ owner := by
    exact (Finset.mem_erase.mp hotherAt).1
  have hotherTime : times other = some opponentDeadline := by
    have hmem := (Finset.mem_erase.mp hotherAt).2
    simpa [quittingPureTimeCoalitionAt] using hmem
  have hunique : ∀ other, times other = some ownerDeadline → other = owner := by
    intro other hother
    have hmem : other ∈ quittingPureTimeCoalitionAt times ownerDeadline := by
      simp [quittingPureTimeCoalitionAt, hother]
    rw [hsingleton] at hmem
    simpa using hmem
  have hrankSome : quittingPureTimeDeadlineRank
      (Function.update times owner (some opponentDeadline)) <
        quittingPureTimeDeadlineRank times := by
    apply quittingPureTimeDeadlineRank_update_lt
      times owner ownerDeadline (some opponentDeadline) howner hunique
    right
    exact ⟨other, hotherNe, hotherTime.symm, by
      intro heq
      have := Option.some.inj heq
      omega⟩
  have hrankNone : quittingPureTimeDeadlineRank
      (Function.update times owner none) < quittingPureTimeDeadlineRank times := by
    apply quittingPureTimeDeadlineRank_update_lt
      times owner ownerDeadline none howner hunique
    exact Or.inl rfl
  by_cases hjoin : passValue ≤ joinValue
  · refine ⟨some opponentDeadline, Or.inl rfl,
      isQuittingPureTimeUnilateralReplacement_update _ _ _, ?_, ?_, ?_⟩
    · rw [quittingPureTimeProfileBehavior_update,
        quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
        reward times owner opponentDeadline hopponentsBefore]
      change joinValue = pair.2 owner
      rw [← max_eq_left hjoin, hendpoints]
    · rw [quittingPureTimeProfileBehavior_update,
        quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
        reward times owner opponentDeadline hopponentsBefore]
      change joinValue - pair.1 owner = debt
      rw [← max_eq_left hjoin, hendpoints]
      exact hcapSub
    · let targetPair := quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times owner (some opponentDeadline)))
      have htarget : targetPair ∈ quittingTerminalSemanticCarrier reward := by
        apply subset_closure
        exact ⟨_, rfl⟩
      have hle : debt ≤ quittingTerminalSemanticDebtSum targetPair :=
        hminimum targetPair htarget
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨by
          simpa only [targetPair, debt, pair, profile] using heq.symm,
          hrankSome⟩
  · have hpass : joinValue ≤ passValue := le_of_not_ge hjoin
    refine ⟨none, Or.inr rfl,
      isQuittingPureTimeUnilateralReplacement_update _ _ _, ?_, ?_, ?_⟩
    · rw [quittingPureTimeProfileBehavior_update,
        quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
          reward times owner opponentDeadline hopponentsBefore hopponentsAt']
      change passValue = pair.2 owner
      rw [← max_eq_right hpass, hendpoints]
    · rw [quittingPureTimeProfileBehavior_update,
        quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
          reward times owner opponentDeadline hopponentsBefore hopponentsAt']
      change passValue - pair.1 owner = debt
      rw [← max_eq_right hpass, hendpoints]
      exact hcapSub
    · let targetPair := quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times owner none))
      have htarget : targetPair ∈ quittingTerminalSemanticCarrier reward := by
        apply subset_closure
        exact ⟨_, rfl⟩
      have hle : debt ≤ quittingTerminalSemanticDebtSum targetPair :=
        hminimum targetPair htarget
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨by
          simpa only [targetPair, debt, pair, profile] using heq.symm,
          hrankNone⟩

end GameTheory
