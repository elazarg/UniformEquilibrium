import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality

/-! # Literal stationary-tail splicing of arbitrary behavioral profiles -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Keep every history row of the source before the cutoff; thereafter use
one preselected independent stationary root. -/
def quittingStationaryTailSpliceProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) : (quittingGame reward).BehaviorProfile :=
  fun who time history ↦ if time < cutoff then source who time history else root who

omit [DecidableEq ι] in
theorem quittingStationaryTailSpliceProfile_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) {time : ℕ} (htime : time < cutoff)
    (who : ι) (history : (quittingGame reward).Hist time) :
    quittingStationaryTailSpliceProfile reward source cutoff root who time history =
      source who time history := by
  simp [quittingStationaryTailSpliceProfile, htime]

omit [DecidableEq ι] in
theorem quittingStationaryTailSpliceProfile_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) {time : ℕ} (htime : cutoff ≤ time)
    (who : ι) (history : (quittingGame reward).Hist time) :
    quittingStationaryTailSpliceProfile reward source cutoff root who time history = root who := by
  simp [quittingStationaryTailSpliceProfile, not_lt.mpr htime]

omit [DecidableEq ι] in
theorem quittingProfileLiveRoot_stationaryTailSplice
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) (time : ℕ) :
    quittingProfileLiveRoot reward (quittingStationaryTailSpliceProfile reward source cutoff root)
        time = if time < cutoff then quittingProfileLiveRoot reward source time else root := by
  funext who
  by_cases htime : time < cutoff <;>
    simp [quittingProfileLiveRoot, quittingStationaryTailSpliceProfile, htime]

omit [DecidableEq ι] in
theorem quittingTerminalPayoff_congr_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (hroots : quittingProfileLiveRoot reward first = quittingProfileLiveRoot reward second)
    (who : ι) :
    quittingTerminalPayoff reward first who = quittingTerminalPayoff reward second who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingTerminalPayoff_eq_rootSequence_profileLiveRoot, hroots]

theorem quittingContinuationBestResponseValue_congr_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (hroots : quittingProfileLiveRoot reward first = quittingProfileLiveRoot reward second)
    (who : ι) :
    quittingContinuationBestResponseValue reward first who =
      quittingContinuationBestResponseValue reward second who := by
  change sSup (Set.range fun deviation ↦ quittingTerminalPayoff reward
      (Function.update first who deviation) who) =
    sSup (Set.range fun deviation ↦ quittingTerminalPayoff reward
      (Function.update second who deviation) who)
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  simp_rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy, hroots]

omit [DecidableEq ι] in
/-- The full source-preserving splice has the same live rows as the literal
finite root word followed by the selected stationary root. -/
theorem quittingProfileLiveRoot_stationaryTailSplice_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) :
    quittingProfileLiveRoot reward (quittingStationaryTailSpliceProfile reward source cutoff root) =
      quittingProfileLiveRoot reward (quittingLiteralRootStackProfile reward
        (List.ofFn fun time : Fin cutoff ↦ quittingProfileLiveRoot reward source time.val)
        (quittingStationaryProfile reward root)) := by
  let roots := fun time ↦ if time < cutoff then quittingProfileLiveRoot reward source time else root
  have htail : quittingRootSequenceProfile reward roots cutoff =
      quittingStationaryProfile reward root := by
    funext who time history
    simp [quittingRootSequenceProfile, roots, quittingStationaryProfile,
      show ¬ cutoff + time < cutoff by omega]
    rfl
  have hword : (List.ofFn fun time : Fin cutoff ↦ roots (0 + time.val)) =
      List.ofFn fun time : Fin cutoff ↦ quittingProfileLiveRoot reward source time.val := by
    congr 1
    funext time
    simp [roots, time.isLt]
  have h := quittingRootSequenceProfile_eq_literalRootStack reward roots 0 cutoff
  simp only [Nat.zero_add] at h
  rw [show (List.ofFn fun time : Fin cutoff ↦ roots time.val) =
    List.ofFn fun time : Fin cutoff ↦ quittingProfileLiveRoot reward source time.val by
      simpa only [Nat.zero_add] using hword, htail] at h
  rw [← h, quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  funext time
  exact quittingProfileLiveRoot_stationaryTailSplice reward source cutoff root time

/-- Both prescribed payoff and unrestricted behavioral caps of the literal
history-preserving splice equal the existing finite root-word semantics. -/
theorem quittingTerminalSemanticPair_stationaryTailSplice_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (root : ι → PMF Bool) :
    quittingTerminalSemanticPair reward
        (quittingStationaryTailSpliceProfile reward source cutoff root) =
      quittingTerminalSemanticPair reward (quittingLiteralRootStackProfile reward
        (List.ofFn fun time : Fin cutoff ↦ quittingProfileLiveRoot reward source time.val)
        (quittingStationaryProfile reward root)) := by
  have hroots := quittingProfileLiveRoot_stationaryTailSplice_eq_literalRootStack
    reward source cutoff root
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_congr_profileLiveRoot reward _ _ hroots who
  · funext who
    exact quittingContinuationBestResponseValue_congr_profileLiveRoot reward _ _ hroots who

end GameTheory
