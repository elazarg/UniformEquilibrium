import UniformEquilibrium.Quitting.Root.SequentialSerialization
import UniformEquilibrium.Quitting.Root.FiniteRootWordSequenceBridge

/-!
# Finite-prefix and terminal payoff estimates for sequential serialization

Every prefix is evaluated by the canonical finite root-word fold. The error
is charged to absorbed mass, rather than to the number of original stages.
-/

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability

/-- The literal chronological word of four singleton substages. -/
def quittingSerializedBlockWord (root : Fin 4 → PMF Bool) : List (Fin 4 → PMF Bool) :=
  [quittingSerializedStage root 0, quittingSerializedStage root 1,
    quittingSerializedStage root 2, quittingSerializedStage root 3]

/-- Concatenation of the serialized blocks in a finite original-clock window. -/
def quittingSerializedWindowWord (roots : ℕ → Fin 4 → PMF Bool) (start fuel : ℕ) :
    List (Fin 4 → PMF Bool) :=
  List.flatten (List.ofFn fun offset : Fin fuel =>
    quittingSerializedBlockWord (roots (start + offset.val)))

/-- The literal four-root word uses the already established block evaluator. -/
theorem quittingFiniteRootWordPayoff_serializedBlock
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (tail : Payoff (Fin 4)) :
    quittingFiniteRootWordPayoff reward (quittingSerializedBlockWord root) tail =
      quittingSerializedBlockPayoff reward root tail := by
  rfl

/-- Opening a window removes exactly its first serialized block. -/
theorem quittingSerializedWindowWord_succ
    (roots : ℕ → Fin 4 → PMF Bool) (start fuel : ℕ) :
    quittingSerializedWindowWord roots start (fuel + 1) =
      quittingSerializedBlockWord (roots start) ++
        quittingSerializedWindowWord roots (start + 1) fuel := by
  simp only [quittingSerializedWindowWord, List.ofFn_succ, Fin.val_zero, Nat.add_zero,
    List.flatten_cons]
  congr 1
  congr 1
  apply congrArg List.ofFn
  funext offset
  simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

/-- Canonical zero-boundary finite recursion equals the canonical literal prefix fold. -/
theorem quittingFiniteRootWordPayoff_ofFn_zero_eq_finiteRootPayoff
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ) :
    quittingFiniteRootWordPayoff reward
        (List.ofFn fun offset : Fin fuel => roots (start + offset.val)) 0 who =
      quittingFiniteRootPayoff reward roots who (fun time => roots time who) start fuel := by
  induction fuel generalizing start with
  | zero => simp [quittingFiniteRootWordPayoff, quittingFiniteRootPayoff]
  | succ fuel ih =>
      rw [List.ofFn_succ]
      simp only [Fin.val_zero, Nat.add_zero, quittingFiniteRootWordPayoff, List.foldr_cons,
        quittingFiniteRootPayoff, Function.update_eq_self]
      change quittingRootSuccessorPayoff reward _ _ who =
        quittingRootSuccessorPayoff reward _ _ who
      apply quittingRootExpectedPayoff_continuation_congr
      convert ih (start + 1) using 1
      simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
      rfl

/-- At zero boundary the serialized window fold is the actual microclock recursion. -/
theorem quittingFiniteRootWordPayoff_serializedWindow_zero_eq_finiteRootPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool) (who : Fin 4) (start fuel : ℕ) :
    quittingFiniteRootWordPayoff reward (quittingSerializedWindowWord roots start fuel)
        0 who =
      quittingFiniteRootPayoff reward (quittingSerializedRoots roots) who
        (fun time => quittingSerializedRoots roots time who) (4 * start) (4 * fuel) := by
  induction fuel generalizing start with
  | zero => simp [quittingSerializedWindowWord, quittingFiniteRootWordPayoff,
      quittingFiniteRootPayoff]
  | succ fuel ih =>
      rw [quittingSerializedWindowWord_succ, quittingFiniteRootWordPayoff_append,
        quittingFiniteRootWordPayoff_serializedBlock]
      rw [show 4 * (fuel + 1) = 4 * fuel + 4 by omega,
        quittingFiniteRootPayoff_serialized_four_step]
      rw [quittingSerializedBlockPayoff_eq_orderedSingletonExpectation,
        quittingSerializedBlockPayoff_eq_orderedSingletonExpectation]
      congr 1
      exact ih (start + 1)

/-- The source comparison for any finite prefix and any two terminal boundaries.
The collision error telescopes to absorption, while the boundary discrepancy
is multiplied by exact joint survival. -/
theorem abs_quittingSerializedWindowPayoff_sub_original_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool) (who : Fin 4)
    {M ε : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ ε)
    (first second : Payoff (Fin 4)) (start fuel : ℕ) :
    |quittingFiniteRootWordPayoff reward (quittingSerializedWindowWord roots start fuel)
          first who -
        quittingFiniteRootWordPayoff reward
          (List.ofFn fun offset : Fin fuel => roots (start + offset.val)) second who| ≤
      8 * M * ε * (1 - quittingJointSurvivalWeight roots start fuel) +
        quittingJointSurvivalWeight roots start fuel * |first who - second who| := by
  induction fuel generalizing start with
  | zero => simp [quittingSerializedWindowWord, quittingFiniteRootWordPayoff,
      quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ fuel ih =>
      let serialTail := quittingFiniteRootWordPayoff reward
        (quittingSerializedWindowWord roots (start + 1) fuel) first
      let originalTail := quittingFiniteRootWordPayoff reward
        (List.ofFn fun offset : Fin fuel => roots (start + 1 + offset.val)) second
      have hsource : (List.ofFn fun offset : Fin (fuel + 1) =>
          roots (start + offset.val)) = roots start ::
            (List.ofFn fun offset : Fin fuel => roots (start + 1 + offset.val)) := by
        rw [List.ofFn_succ]
        simp only [Fin.val_zero, Nat.add_zero]
        congr 1
        apply congrArg List.ofFn
        funext offset
        simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
      rw [quittingSerializedWindowWord_succ, quittingFiniteRootWordPayoff_append,
        quittingFiniteRootWordPayoff_serializedBlock, hsource]
      change |quittingSerializedBlockPayoff reward (roots start) serialTail who -
        quittingRootSuccessorPayoff reward originalTail (roots start) who| ≤ _
      have hsplit : quittingSerializedBlockPayoff reward (roots start) serialTail who -
          quittingRootSuccessorPayoff reward originalTail (roots start) who =
          (quittingSerializedBlockPayoff reward (roots start) serialTail who -
            quittingSerializedBlockPayoff reward (roots start) originalTail who) +
          (quittingSerializedBlockPayoff reward (roots start) originalTail who -
            quittingRootSuccessorPayoff reward originalTail (roots start) who) := by ring
      rw [hsplit]
      have hrow := abs_quittingSerializedBlockPayoff_sub_rootPayoff_le
        reward (roots start) originalTail who hreward (hsmall start)
      have htransport : |quittingSerializedBlockPayoff reward (roots start) serialTail who -
          quittingSerializedBlockPayoff reward (roots start) originalTail who| ≤
          quittingStationaryContinueMass (roots start) *
            (8 * M * ε * (1 - quittingJointSurvivalWeight roots (start + 1) fuel) +
              quittingJointSurvivalWeight roots (start + 1) fuel *
                |first who - second who|) := by
        rw [quittingSerializedBlockPayoff_sub_eq_continueMass_mul, abs_mul,
          abs_of_nonneg (quittingStationaryContinueMass_nonneg _)]
        exact mul_le_mul_of_nonneg_left (ih (start + 1))
          (quittingStationaryContinueMass_nonneg _)
      have hsurvival : quittingJointSurvivalWeight roots start (fuel + 1) =
          quittingStationaryContinueMass (roots start) *
            quittingJointSurvivalWeight roots (start + 1) fuel := by
        simp only [quittingJointSurvivalWeight_eq_survivalProduct,
          Math.survivalProduct_succ_left]
      refine (abs_add_le _ _).trans ((add_le_add htransport hrow).trans_eq ?_)
      rw [hsurvival]
      ring

/-- Uniform whole-profile payoff comparison, including possible nonabsorption. -/
theorem abs_quittingSerializedTerminalValue_sub_original_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool) (who : Fin 4)
    {M ε : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ ε) (start : ℕ) :
    |quittingRootSequenceTerminalValue reward (quittingSerializedRoots roots) who (4 * start) -
        quittingRootSequenceTerminalValue reward roots who start| ≤ 8 * M * ε := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who))
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hsmall start who)
  have hbound : ∀ fuel,
      |quittingFiniteRootPayoff reward (quittingSerializedRoots roots) who
          (fun time => quittingSerializedRoots roots time who) (4 * start) (4 * fuel) -
        quittingFiniteRootPayoff reward roots who
          (fun time => roots time who) start fuel| ≤ 8 * M * ε := by
    intro fuel
    rw [← quittingFiniteRootWordPayoff_serializedWindow_zero_eq_finiteRootPayoff,
      ← quittingFiniteRootWordPayoff_ofFn_zero_eq_finiteRootPayoff]
    have h := abs_quittingSerializedWindowPayoff_sub_original_le
      reward roots who hreward hsmall 0 0 start fuel
    simp only [Pi.zero_apply, sub_self, abs_zero, mul_zero, add_zero] at h
    exact h.trans (mul_le_of_le_one_right
      (mul_nonneg (mul_nonneg (by norm_num) hM) hε)
      (by linarith [quittingJointSurvivalWeight_nonneg roots start fuel]))
  have hserial := (tendsto_quittingFiniteRootPayoff_self_terminalValue
    reward (quittingSerializedRoots roots) who (4 * start)).comp
      (show Tendsto (fun fuel : ℕ => 4 * fuel) atTop atTop from
        (strictMono_nat_of_lt_succ (fun fuel => by omega)).tendsto_atTop)
  have hsource := tendsto_quittingFiniteRootPayoff_self_terminalValue reward roots who start
  exact le_of_tendsto ((hserial.sub hsource).abs) (Filter.Eventually.of_forall hbound)

end GameTheory
