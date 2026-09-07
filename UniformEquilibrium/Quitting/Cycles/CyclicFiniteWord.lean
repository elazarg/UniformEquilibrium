import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler
import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-! # Literal finite cyclic words and exact boundary evaluation -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

/-- The first `fuel` roots of a cycle, in chronological order. -/
def quittingCyclicRootWord (roots : Fin period → ι → PMF Bool)
    (phase : Fin period) : ℕ → List (ι → PMF Bool)
  | 0 => []
  | fuel + 1 => roots phase :: quittingCyclicRootWord roots (finRotate period phase) fuel

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingCyclicRootWord_length (roots : Fin period → ι → PMF Bool)
    (phase : Fin period) (fuel : ℕ) :
    (quittingCyclicRootWord roots phase fuel).length = fuel := by
  induction fuel generalizing phase with
  | zero => rfl
  | succ fuel ih => simp [quittingCyclicRootWord, ih]

omit [DecidableEq ι] in
theorem quittingCyclicRootWord_jointSurvival (roots : Fin period → ι → PMF Bool)
    (phase : Fin period) (fuel : ℕ) :
    quittingLiteralRootStackJointSurvival (quittingCyclicRootWord roots phase fuel) =
      quittingCyclicPrefixWeight (fun phase => quittingStationaryContinueMass (roots phase))
        phase fuel := by
  induction fuel generalizing phase with
  | zero => simp [quittingCyclicRootWord, quittingLiteralRootStackJointSurvival]
  | succ fuel ih =>
      rw [quittingCyclicRootWord]
      change quittingStationaryContinueMass (roots phase) *
        quittingLiteralRootStackJointSurvival
          (quittingCyclicRootWord roots (finRotate period phase) fuel) = _
      rw [ih, show fuel + 1 = 1 + fuel by omega, quittingCyclicPrefixWeight_add]
      simp [quittingCyclicPrefixWeight_succ, quittingCyclicOrbit_succ]

omit [DecidableEq ι] in
theorem quittingFiniteRootWordPayoff_cyclic_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) :
    quittingFiniteRootWordPayoff reward (quittingCyclicRootWord roots phase fuel)
        (quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase fuel)) =
      quittingCyclicTerminalValue reward roots phase := by
  induction fuel generalizing phase with
  | zero => simp [quittingCyclicRootWord, quittingFiniteRootWordPayoff]
  | succ fuel ih =>
      have horbit : quittingCyclicOrbit phase (fuel + 1) =
          quittingCyclicOrbit (finRotate period phase) fuel := by
        rw [show fuel + 1 = 1 + fuel by omega, quittingCyclicOrbit_add]
        simp [quittingCyclicOrbit_succ]
      simp only [quittingCyclicRootWord, quittingFiniteRootWordPayoff, List.foldr_cons]
      change quittingRootSuccessorPayoff reward
        (quittingFiniteRootWordPayoff reward _ _) (roots phase) = _
      rw [horbit, ih, ← quittingCyclicTerminalValue_eq_rootSuccessorPayoff]

/-- A finite cyclic calendar followed by literal perpetual Continue. -/
def quittingCyclicFiniteProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (quittingCyclicRootWord roots phase fuel)
    (quittingAlwaysContinueProfile reward)

omit [DecidableEq ι] in
/-- Exact finite-cut payoff identity, without any equilibrium hypothesis. -/
theorem quittingTerminalPayoff_cyclicFiniteProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ) (who : ι) :
    quittingTerminalPayoff reward (quittingCyclicFiniteProfile reward roots phase fuel) who =
      quittingCyclicTerminalValue reward roots phase who -
        quittingCyclicPrefixWeight (fun phase => quittingStationaryContinueMass (roots phase))
          phase fuel *
            quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase fuel) who := by
  have hdiff := quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul reward
    (quittingCyclicRootWord roots phase fuel)
    (quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase fuel)) 0 who
  rw [quittingFiniteRootWordPayoff_cyclic_value, quittingCyclicRootWord_jointSurvival] at hdiff
  have hnever : quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) = 0 := by
    funext player
    exact quittingTerminalPayoff_quittingAlwaysContinue reward player
  rw [quittingCyclicFiniteProfile, quittingTerminalPayoff_literalRootStack_eq_wordPayoff, hnever]
  change _ - _ = _ * (_ - 0) at hdiff
  linarith

omit [DecidableEq ι] in
/-- Complete turns multiply every prescribed payoff by the same exact factor. -/
theorem quittingTerminalPayoff_cyclicFiniteProfile_mul_card
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (turns : ℕ) (who : ι) :
    quittingTerminalPayoff reward
        (quittingCyclicFiniteProfile reward roots phase (turns * period)) who =
      (1 - (∏ phase, quittingStationaryContinueMass (roots phase)) ^ turns) *
        quittingCyclicTerminalValue reward roots phase who := by
  rw [quittingTerminalPayoff_cyclicFiniteProfile, quittingCyclicOrbit_mul_card,
    quittingCyclicPrefixWeight_mul_card]
  ring

/-- The cap fold with the periodic exact-Nash boundary returns its reference value. -/
theorem quittingFiniteRootWordCap_cyclic_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool)
    (hnash : ∀ phase, IsεQuittingRootNash reward
      (quittingCyclicTerminalValue reward roots (finRotate period phase)) 0 (roots phase))
    (phase : Fin period) (fuel : ℕ) (who : ι) :
    quittingFiniteRootWordCap reward (quittingCyclicRootWord roots phase fuel) who
        (quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase fuel) who) =
      quittingCyclicTerminalValue reward roots phase who := by
  induction fuel generalizing phase with
  | zero => simp [quittingCyclicRootWord, quittingFiniteRootWordCap]
  | succ fuel ih =>
      have horbit : quittingCyclicOrbit phase (fuel + 1) =
          quittingCyclicOrbit (finRotate period phase) fuel := by
        rw [show fuel + 1 = 1 + fuel by omega, quittingCyclicOrbit_add]
        simp [quittingCyclicOrbit_succ]
      change max (quittingRootQuitPayoff reward 0 (roots phase) who)
        (quittingRootContinuePayoff reward (Function.update 0 who
          (quittingFiniteRootWordCap reward
            (quittingCyclicRootWord roots (finRotate period phase) fuel) who
            (quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase (fuel + 1))
              who))) (roots phase) who) = _
      rw [horbit, ih, quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward roots phase,
        quittingRootSuccessorPayoff_eq_max_of_isZeroNash reward _ _ who (hnash phase)]
      congr 1
      · exact quittingRootQuitPayoff_continuation_invariant reward _ _ _ who
      · apply quittingRootExpectedPayoff_continuation_congr
        simp

/-- A dominated Never boundary gives an upper bound for all behavioral replacements. -/
theorem quittingContinuationBestResponseValue_cyclicFiniteProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool)
    (hnash : ∀ phase, IsεQuittingRootNash reward
      (quittingCyclicTerminalValue reward roots (finRotate period phase)) 0 (roots phase))
    (phase : Fin period) (fuel : ℕ) (who : ι)
    (htail : max 0 (reward (quittingSingletonTerminal who) who) ≤
      quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase fuel) who) :
    quittingContinuationBestResponseValue reward
        (quittingCyclicFiniteProfile reward roots phase fuel) who ≤
      quittingCyclicTerminalValue reward roots phase who := by
  rw [quittingCyclicFiniteProfile,
    quittingContinuationBestResponseValue_literalRootStack_eq_capFold,
    quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  have hbound := quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart reward
    (quittingCyclicRootWord roots phase fuel) who
    (max 0 (reward (quittingSingletonTerminal who) who))
    (quittingCyclicTerminalValue reward roots (quittingCyclicOrbit phase fuel) who)
  rw [quittingFiniteRootWordCap_cyclic_value reward roots hnash] at hbound
  rw [max_eq_left (sub_nonpos.mpr htail), mul_zero] at hbound
  linarith

/-- A finite pure date attains a reference value if earlier Continue endpoints and
the final Quit endpoint agree with that reference. The post-date tail is arbitrary. -/
theorem quittingTerminalPayoff_cyclicWord_pureTime_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (reference : Fin period → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile) (phase : Fin period) (fuel time : ℕ)
    (who : ι) (htime : time < fuel)
    (hcontinue : ∀ offset < time,
      quittingRootContinuePayoff reward
          (reference (finRotate period (quittingCyclicOrbit phase offset)))
          (roots (quittingCyclicOrbit phase offset)) who =
        reference (quittingCyclicOrbit phase offset) who)
    (hquit : quittingRootQuitPayoff reward 0 (roots (quittingCyclicOrbit phase time)) who =
      reference (quittingCyclicOrbit phase time) who) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingLiteralRootStackProfile reward (quittingCyclicRootWord roots phase fuel) tail)
          who (quittingPureTimeBehaviorStrategy reward who (some time))) who =
      reference phase who := by
  induction time generalizing phase fuel with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [quittingCyclicRootWord, quittingLiteralRootStackProfile_cons,
            quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff,
            quittingRootQuitPayoff_continuation_invariant reward _ 0]
          simpa using hquit
  | succ time ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have horbit (offset : ℕ) : quittingCyclicOrbit (finRotate period phase) offset =
              quittingCyclicOrbit phase (offset + 1) := by
            rw [show offset + 1 = 1 + offset by omega, quittingCyclicOrbit_add]
            simp [quittingCyclicOrbit_succ]
          have hchild := ih (finRotate period phase) fuel (by omega)
            (fun offset hoff => by simpa only [horbit] using hcontinue (offset + 1) (by omega))
            (by simpa only [horbit] using hquit)
          rw [quittingCyclicRootWord, quittingLiteralRootStackProfile_cons]
          change quittingTerminalPayoff reward (Function.update _ who
            (quittingPureTimeBehaviorStrategy reward who ((some time).map Nat.succ))) who = _
          rw [quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff]
          calc
            _ = quittingRootContinuePayoff reward
                (reference (finRotate period phase)) (roots phase) who := by
                  apply quittingRootExpectedPayoff_continuation_congr
                  simpa using hchild
            _ = reference phase who := by simpa using hcontinue 0 (by omega)

omit [DecidableEq ι] in
/-- The literal finite stack uses exactly the cyclic roots before the cut and
all-Continue afterwards, at every history including histories of probability zero. -/
theorem quittingCyclicFiniteProfile_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (phase : Fin period) (fuel : ℕ)
    (who : ι) (time : ℕ) (history : (quittingGame reward).Hist time) :
    quittingCyclicFiniteProfile reward roots phase fuel who time history =
      if time < fuel then roots (quittingCyclicOrbit phase time) who else PMF.pure false := by
  induction fuel generalizing phase time with
  | zero => rfl
  | succ fuel ih =>
      cases time with
      | zero => simp [quittingCyclicFiniteProfile, quittingCyclicRootWord]
      | succ time =>
          change quittingCyclicFiniteProfile reward roots (finRotate period phase) fuel who time
            (Fin.tail history.1, history.2) = _
          rw [ih]
          have horbit : quittingCyclicOrbit (finRotate period phase) time =
              quittingCyclicOrbit phase (time + 1) := by
            rw [show time + 1 = 1 + time by omega, quittingCyclicOrbit_add]
            simp [quittingCyclicOrbit_succ]
          simp only [Nat.succ_lt_succ_iff, horbit]

end GameTheory
