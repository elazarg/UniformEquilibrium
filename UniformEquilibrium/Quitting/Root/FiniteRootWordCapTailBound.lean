import UniformEquilibrium.Quitting.Root.FiniteDeadlineCapRecursion

/-! # Finite root-word caps with an arbitrary signed suffix cap -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem affine_finiteRootWordCap_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) (tailCap offset weight bound : ℝ)
    (hweight : 0 ≤ weight)
    (hfinite : ∀ time, time < fuel →
      offset + weight * quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + time)) start ≤ bound) :
    offset + weight * quittingFiniteRootWordCap reward
        (List.ofFn fun time : Fin fuel => roots (start + time.val)) who tailCap ≤
      max bound (offset + weight *
        (quittingLiveLedgerAccum reward roots who start fuel +
          quittingOpponentSurvivalWeight roots who start fuel * tailCap)) := by
  induction fuel generalizing start offset weight with
  | zero =>
      rw [List.ofFn_zero]
      simp only [quittingFiniteRootWordCap, List.foldr_nil,
        quittingLiveLedgerAccum_zero, quittingOpponentSurvivalWeight]
      simp
  | succ fuel ih =>
      rw [List.ofFn_succ]
      simp only [quittingFiniteRootWordCap, List.foldr_cons]
      change offset + weight * max
        (quittingRootQuitPayoff reward 0 (roots start) who)
        (quittingRootContinuePayoff reward
          (Function.update 0 who
            (quittingFiniteRootWordCap reward
              (List.ofFn fun time : Fin fuel => roots (start + (time.val + 1)))
              who tailCap)) (roots start) who) ≤ _
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        quittingRootContinuePayoff_eq_fixedOpponents]
      simp only [Function.update_self]
      let quitValue := quittingFixedOpponentsQuitValue reward roots who start
      let continueReward := quittingFixedOpponentsContinueReward reward roots who start
      let continueMass := quittingFixedOpponentsContinueMass roots who start
      let suffix := quittingFiniteRootWordCap reward
        (List.ofFn fun time : Fin fuel => roots (start + 1 + time.val)) who tailCap
      have hmass : 0 ≤ continueMass :=
        quittingFixedOpponentsContinueMass_nonneg roots who start
      have hquit : offset + weight * quitValue ≤ bound := by
        simpa [quitValue, quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
          using hfinite 0 (by omega)
      have hsuffix := ih (start := start + 1)
        (offset := offset + weight * continueReward)
        (weight := weight * continueMass) (mul_nonneg hweight hmass)
        (fun time htime => by
          have h := hfinite (time + 1) (by omega)
          rw [show start + (time + 1) = start + time + 1 by omega] at h
          rw [quittingRootSequencePureTimeTerminalValue_some_succ] at h
          dsimp [continueReward, continueMass]
          convert h using 1
          ring_nf)
      rw [mul_max_of_nonneg _ _ hweight]
      rw [← max_add_add_left]
      apply max_le
      · exact hquit.trans (le_max_left _ _)
      · have hlist : (List.ofFn fun time : Fin fuel => roots (start + (time.val + 1))) =
            List.ofFn fun time : Fin fuel => roots (start + 1 + time.val) := by
          congr 1
          funext time
          congr 1
          omega
        rw [hlist]
        rw [quittingLiveLedgerAccum_shift,
          quittingOpponentSurvivalWeight_shift]
        dsimp [continueReward, continueMass] at hsuffix
        convert hsuffix using 1
        all_goals first | rfl | ring_nf

/-- If every pure response inside a finite prefix is bounded by `bound`, its
root-word cap with any signed suffix cap is bounded by the larger of `bound`
and the literal ledger-plus-surviving-tail value. -/
theorem quittingFiniteRootWordCap_le_max_pureTime_and_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ)
    (tailCap bound : ℝ)
    (hfinite : ∀ time, time < cutoff →
      quittingRootSequencePureTimeTerminalValue reward roots who (some time) 0 ≤ bound) :
    quittingFiniteRootWordCap reward
        (List.ofFn fun time : Fin cutoff => roots time.val) who tailCap ≤
      max bound (quittingLiveLedgerAccum reward roots who 0 cutoff +
        quittingOpponentSurvivalWeight roots who 0 cutoff * tailCap) := by
  simpa using affine_finiteRootWordCap_le_max reward roots who 0 cutoff tailCap
    0 1 bound (by norm_num) (by simpa using hfinite)

end GameTheory
