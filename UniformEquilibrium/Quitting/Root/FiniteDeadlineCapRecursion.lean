import MathUE.Finset.FiniteMenuSupremum
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineReplyCap
import UniformEquilibrium.Quitting.Terminal.TargetTail.FiniteChainTerminalCompiler

/-! # Root algebra for finite deadline reply caps -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A deterministic quit strictly after the current date first receives the
fixed-opponent Continue contribution and then its shifted terminal value. -/
theorem quittingRootSequencePureTimeTerminalValue_some_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who
        (some (start + fuel + 1)) start =
      quittingFixedOpponentsContinueReward reward roots who start +
        quittingFixedOpponentsContinueMass roots who start *
          quittingRootSequencePureTimeTerminalValue reward roots who
            (some (start + fuel + 1)) (start + 1) := by
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  have hne : start ≠ start + fuel + 1 := by omega
  rw [quittingPureTimeHazard_some_of_ne hne]
  simp

private def finitePureTimeMenuCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start deadline : ℕ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (Option (Fin deadline))).Nonempty)
    (fun action => quittingRootSequencePureTimeTerminalValue reward roots who
      (action.map fun time => start + time.val) start)

private theorem finitePureTimeMenuCap_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start deadline : ℕ) :
    finitePureTimeMenuCap reward roots who start (deadline + 1) =
      max (quittingFixedOpponentsQuitValue reward roots who start)
        (quittingFixedOpponentsContinueReward reward roots who start +
          quittingFixedOpponentsContinueMass roots who start *
            finitePureTimeMenuCap reward roots who (start + 1) deadline) := by
  unfold finitePureTimeMenuCap
  rw [Math.sup'_option_fin_succ_eq_max]
  simp only [Option.map_some, Fin.val_zero, Nat.add_zero]
  rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  let offset := quittingFixedOpponentsContinueReward reward roots who start
  let scale := quittingFixedOpponentsContinueMass roots who start
  let suffixValue := fun action : Option (Fin deadline) =>
    quittingRootSequencePureTimeTerminalValue reward roots who
      (action.map fun time => start + 1 + time.val) (start + 1)
  have hpoint : (fun action : Option (Fin deadline) =>
      quittingRootSequencePureTimeTerminalValue reward roots who
        ((action.map Fin.succ).map fun time => start + time.val) start) =
      fun action => offset + scale * suffixValue action := by
    funext action
    cases action with
    | none =>
        exact quittingRootSequencePureTimeTerminalValue_none_succ_eq_fixedOpponents
          reward roots who start
    | some time =>
        simpa [offset, scale, suffixValue, Nat.add_assoc,
          Nat.add_comm time.val 1] using
            quittingRootSequencePureTimeTerminalValue_some_succ
              reward roots who start time.val
  rw [hpoint, Math.sup'_affine_of_nonneg suffixValue offset scale
    (quittingFixedOpponentsContinueMass_nonneg roots who start)]

theorem finitePureTimeMenuCap_eq_finiteRootWordCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start deadline : ℕ) :
    finitePureTimeMenuCap reward roots who start deadline =
      quittingFiniteRootWordCap reward
        (List.ofFn fun time : Fin deadline => roots (start + time.val)) who
        (quittingRootSequencePureTimeTerminalValue reward roots who none
          (start + deadline)) := by
  induction deadline generalizing start with
  | zero =>
      unfold finitePureTimeMenuCap quittingFiniteRootWordCap
      have hdefault : (default : Option (Fin 0)) = none := by
        cases (default : Option (Fin 0)) with
        | none => rfl
        | some time => exact Fin.elim0 time
      simp only [List.ofFn_zero, List.foldr_nil]
      apply le_antisymm
      · apply Finset.sup'_le
        intro action _
        have : action = none := Subsingleton.elim _ _
        subst action
        simp
      · simpa using Finset.le_sup'
          (fun action : Option (Fin 0) =>
            quittingRootSequencePureTimeTerminalValue reward roots who
              (action.map fun time => start + time.val) start)
          (Finset.mem_univ (none : Option (Fin 0)))
  | succ deadline ih =>
      rw [finitePureTimeMenuCap_succ, show deadline + 1 = Nat.succ deadline by omega]
      simp only [List.ofFn_succ, quittingFiniteRootWordCap, List.foldr_cons]
      rw [ih (start + 1)]
      simp only [Fin.val_zero, Nat.add_zero]
      change max (quittingFixedOpponentsQuitValue reward roots who start)
          (quittingFixedOpponentsContinueReward reward roots who start +
            quittingFixedOpponentsContinueMass roots who start * _) =
        max (quittingRootQuitPayoff reward 0 (roots start) who)
          (quittingRootContinuePayoff reward
            (Function.update 0 who _) (roots start) who)
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue,
        quittingRootContinuePayoff_eq_fixedOpponents]
      simp only [Function.update_self]
      unfold quittingFiniteRootWordCap
      congr 2
      apply congrArg (fun value =>
        quittingFixedOpponentsContinueMass roots who start * value)
      congr 2
      · omega
      · funext time
        congr 1
        change start + 1 + time.val = start + (time.val + 1)
        omega

theorem quittingFiniteDeadlineReplyCap_eq_finiteRootWordCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingFiniteDeadlineReplyCap reward deadline mixed who =
      quittingFiniteRootWordCap reward
        (List.ofFn fun time : Fin deadline =>
          quittingProfileLiveRoot reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) time.val)
        who 0 := by
  let roots := quittingProfileLiveRoot reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed)
  rw [quittingFiniteDeadlineReplyCap_eq_sup_pureTimeTerminalValue]
  rw [show (Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (QuittingFiniteDeadlineTimingAction deadline)).Nonempty)
      (fun action => quittingRootSequencePureTimeTerminalValue reward roots who
        (quittingFiniteDeadlineTimingActionTime action) 0)) =
      finitePureTimeMenuCap reward roots who 0 deadline by
    unfold finitePureTimeMenuCap
    congr 1
    funext action
    cases action with
    | none =>
        change quittingRootSequencePureTimeTerminalValue reward roots who none = _
        rfl
    | some time =>
        change quittingRootSequencePureTimeTerminalValue reward roots who
          (some time.val) = _
        simp]
  rw [finitePureTimeMenuCap_eq_finiteRootWordCap]
  have hall : ∀ time, deadline ≤ time → roots time = quittingAllContinueRoot := by
    intro time htime
    exact quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
      reward deadline mixed htime
  have htail : quittingRootSequencePureTimeTerminalValue reward roots who none deadline = 0 := by
    unfold quittingRootSequencePureTimeTerminalValue
    change quittingRootSequenceTerminalValue reward
      (quittingRootSequenceUpdate roots who (quittingPureTimeHazard none)) who deadline = 0
    apply quittingRootSequenceTerminalValue_eq_zero_of_allContinue_from
    intro time htime
    funext player
    by_cases hplayer : player = who
    · subst player
      simp only [quittingRootSequenceUpdate, Function.update_self,
        quittingPureTimeHazard]
      change PMF.pure false = PMF.pure false
      rfl
    · simp only [quittingRootSequenceUpdate, Function.update_of_ne hplayer]
      rw [hall time htime]
  simp [roots, htail]

end GameTheory
