import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice
import UniformEquilibrium.Quitting.Boundary.Exceptional.InfiniteLTG

/-! # Finite root words as literal prefixes of root sequences -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingFiniteRootWordCap_append
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : List (ι → PMF Bool)) (who : ι) (value : ℝ) :
    quittingFiniteRootWordCap reward (first ++ second) who value =
      quittingFiniteRootWordCap reward first who
        (quittingFiniteRootWordCap reward second who value) := by
  simp only [quittingFiniteRootWordCap, List.foldr_append]

omit [DecidableEq ι] in
theorem quittingFiniteRootWordPayoff_append
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : List (ι → PMF Bool)) (value : Payoff ι) :
    quittingFiniteRootWordPayoff reward (first ++ second) value =
      quittingFiniteRootWordPayoff reward first
        (quittingFiniteRootWordPayoff reward second value) := by
  simp only [quittingFiniteRootWordPayoff, List.foldr_append]

omit [DecidableEq ι] in
/-- The original sequence, its literal finite prefix, and its actual shifted
tail are the same behavioral profile, not merely equal payoff vectors. -/
theorem quittingRootSequenceProfile_eq_literalRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) :
    quittingRootSequenceProfile reward roots start =
      quittingLiteralRootStackProfile reward
        (List.ofFn fun time : Fin length ↦ roots (start + time.val))
        (quittingRootSequenceProfile reward roots (start + length)) := by
  induction length generalizing start with
  | zero => simp
  | succ length ih =>
      rw [List.ofFn_succ, quittingLiteralRootStackProfile_cons]
      conv_lhs => rw [quittingRootSequenceProfile_eq_rootThenContinuation]
      simp only [Fin.val_zero, Nat.add_zero]
      congr 1
      convert ih (start + 1) using 1
      simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

omit [DecidableEq ι] in
theorem quittingLiteralRootStackJointSurvival_ofFn
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) :
    quittingLiteralRootStackJointSurvival
      (List.ofFn fun time : Fin length ↦ roots (start + time.val)) =
        quittingJointSurvivalWeight roots start length := by
  simp only [quittingLiteralRootStackJointSurvival, List.map_ofFn, List.prod_ofFn,
    Function.comp_def]
  rw [Fin.prod_univ_eq_prod_range
    (fun time ↦ quittingStationaryContinueMass (roots (start + time))) length,
    quittingJointSurvivalWeight_eq_prod]

theorem quittingLiteralRootStackOpponentSurvival_ofFn
    (roots : ℕ → ι → PMF Bool) (who : ι) (start length : ℕ) :
    quittingLiteralRootStackOpponentSurvival
      (List.ofFn fun time : Fin length ↦ roots (start + time.val)) who =
        quittingOpponentSurvivalWeight roots who start length := by
  simp only [quittingLiteralRootStackOpponentSurvival, List.map_ofFn, List.prod_ofFn,
    Function.comp_def]
  rw [Fin.prod_univ_eq_prod_range
    (fun time ↦ quittingRootOpponentContinueMass (roots (start + time)) who) length]
  rfl

omit [DecidableEq ι] in
/-- A literal root-word splice keeps every prescribed prefix row at every
history, independently of the continuation installed after the word. -/
theorem quittingLiteralRootStackProfile_ofFn_apply_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start length : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) (player : ι)
    (time : ℕ) (history : (quittingGame reward).Hist time) (htime : time < length) :
    quittingLiteralRootStackProfile reward
      (List.ofFn fun offset : Fin length ↦ roots (start + offset.val))
      tail player time history = roots (start + time) player := by
  induction length generalizing start time with
  | zero => omega
  | succ length ih =>
      rw [List.ofFn_succ, quittingLiteralRootStackProfile_cons]
      cases time with
      | zero => rfl
      | succ time =>
          change quittingLiteralRootStackProfile reward
            (List.ofFn fun offset : Fin length ↦ roots (start + offset.succ.val))
            tail player time (Fin.tail history.1, history.2) = _
          have h := ih (start + 1) time (Fin.tail history.1, history.2) (by omega)
          convert h using 1 <;> simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

omit [DecidableEq ι] in
theorem quittingProfileLiveRoot_literalRootStack_ofFn_of_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start length : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) {time : ℕ} (htime : time < length) :
    quittingProfileLiveRoot reward (quittingLiteralRootStackProfile reward
      (List.ofFn fun offset : Fin length ↦ roots (start + offset.val)) tail) time =
        roots (start + time) := by
  funext player
  exact quittingLiteralRootStackProfile_ofFn_apply_of_lt reward roots start length tail
    player time _ htime

end GameTheory
