import UniformEquilibrium.Quitting.Root.SequentialSerializationPayoff
import UniformEquilibrium.Quitting.Classification.Existence.PureTimeDeviationLedger
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Pure-deadline comparison for small-hazard serialization

The comparison uses actual finite prefixes with the deviator forced to Continue.
At the stopping block both conditional rewards are close to the unit solo exit.
Never is handled by the whole-profile comparison on the deleted roots.
-/

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability QuittingAbsorptionPath

/-- Forcing one player to Continue commutes with chronological serialization. -/
theorem quittingSerializedRoots_update_continue {n : ℕ} [NeZero n]
    (roots : ℕ → Fin n → PMF Bool) (who : Fin n) :
    quittingSerializedRoots (quittingRootSequenceUpdate roots who (fun _ => PMF.pure false)) =
      quittingRootSequenceUpdate (quittingSerializedRoots roots) who
        (fun _ => PMF.pure false) := by
  funext time player
  let phase : Fin n := ⟨time % n, Nat.mod_lt _ (NeZero.pos n)⟩
  by_cases hp : player = who
  · subst player
    by_cases hphase : who = phase <;>
      simp [quittingSerializedRoots, quittingSerializedStage, quittingSoloMixedRoot,
        quittingAllContinueRoot, quittingRootSequenceUpdate, phase, hphase]
  · by_cases hphase : player = phase
    · have hphaseWho : phase ≠ who := fun heq => hp (hphase.trans heq)
      simp [quittingSerializedRoots, quittingSerializedStage, quittingSoloMixedRoot,
        quittingRootSequenceUpdate, phase, hphase, hphaseWho]
    · simp [quittingSerializedRoots, quittingSerializedStage, quittingSoloMixedRoot,
        quittingAllContinueRoot, quittingRootSequenceUpdate, phase, hp, hphase]

/-- The finite chronological block word is exactly the corresponding actual microclock word. -/
theorem quittingSerializedWindowWord_eq_ofFn
    (roots : ℕ → Fin 4 → PMF Bool) (start fuel : ℕ) :
    quittingSerializedWindowWord roots start fuel =
      List.ofFn (fun offset : Fin (4 * fuel) =>
        quittingSerializedRoots roots (4 * start + offset.val)) := by
  induction fuel generalizing start with
  | zero => simp [quittingSerializedWindowWord]
  | succ fuel ih =>
      rw [quittingSerializedWindowWord_succ,
        show 4 * (fuel + 1) = 4 + 4 * fuel by omega, List.ofFn_add]
      apply congrArg₂ List.append
      · have hblock : List.ofFn (fun phase : Fin 4 =>
            quittingSerializedRoots roots (4 * start + phase.val)) =
            quittingSerializedBlockWord (roots start) := by
          simp only [List.ofFn_succ, List.ofFn_zero]
          have hclock0 : quittingSerializedRoots roots (4 * start) =
              quittingSerializedStage (roots start) 0 := by
            simpa using quittingSerializedRoots_at roots start 0
          have hclock1 : quittingSerializedRoots roots (4 * start + 1) =
              quittingSerializedStage (roots start) 1 := by
            simpa using quittingSerializedRoots_at roots start 1
          have hclock2 : quittingSerializedRoots roots (4 * start + 2) =
              quittingSerializedStage (roots start) 2 := by
            simpa using quittingSerializedRoots_at roots start 2
          have hclock3 : quittingSerializedRoots roots (4 * start + 3) =
              quittingSerializedStage (roots start) 3 := by
            simpa using quittingSerializedRoots_at roots start 3
          simp only [Fin.val_succ, Fin.val_zero, Nat.add_zero]
          norm_num only
          rw [hclock0, hclock1, hclock2, hclock3]
          rfl
        simpa only [Fin.val_castLE] using hblock.symm
      · rw [ih]
        apply congrArg List.ofFn
        funext offset
        congr 1
        simp only [Fin.val_natAdd]
        omega

/-- A finite pure deadline is evaluated by the literal all-Continue prefix
followed by its actual conditional deadline value. -/
theorem quittingPureTimeTerminalValue_eq_continueWord
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (target start fuel : ℕ)
    (hbefore : start + fuel ≤ target) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some target) start =
      quittingFiniteRootWordPayoff reward
        (List.ofFn fun offset : Fin fuel =>
          Function.update (roots (start + offset.val)) who (PMF.pure false))
        (fun _ => quittingRootSequencePureTimeTerminalValue reward roots who
          (some target) (start + fuel)) who := by
  induction fuel generalizing start with
  | zero => simp [quittingFiniteRootWordPayoff]
  | succ fuel ih =>
      rw [quittingRootSequencePureTimeTerminalValue_continue_step reward roots who
        (some target) start (by intro h; injection h with h; omega), List.ofFn_succ]
      simp only [Fin.val_zero, Nat.add_zero, quittingFiniteRootWordPayoff, List.foldr_cons]
      rw [show quittingRootSuccessorPayoff reward _ _ who =
        quittingRootExpectedPayoff reward _ _ who by rfl,
        quittingRootExpectedPayoff_eq_absorbingContribution_add]
      unfold quittingFixedOpponentsContinueReward quittingFixedOpponentsContinueMass
      congr 1
      congr 1
      convert ih (start + 1) (by omega) using 1
      simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]
      rfl

/-- A row with small individual hazards has small total absorption. -/
private theorem absorption_le_four_mul
    (root : Fin 4 → PMF Bool) {ε : ℝ}
    (hsmall : ∀ owner, (root owner true).toReal ≤ ε) :
    quittingRootAbsorptionMass root ≤ 4 * ε := by
  refine (quittingRootAbsorptionMass_le_sum_quitProbability root).trans ?_
  calc
    (∑ owner, (root owner true).toReal) ≤ ∑ _owner : Fin 4, ε :=
      Finset.sum_le_sum (fun owner _ => hsmall owner)
    _ = 4 * ε := by simp

/-- Quitting at the original stopping block pays almost the unit solo reward. -/
theorem abs_quittingOriginalDeadlineValue_sub_one_le
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hunit : QuittingUnitSoloExit reward) (roots : ℕ → Fin 4 → PMF Bool)
    (who : Fin 4) (stage : ℕ) {M ε : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ ε) :
    |quittingRootSequencePureTimeTerminalValue reward roots who (some stage) stage - 1| ≤
      8 * M * ε := by
  rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who) who)
  refine (abs_quittingFixedOpponentsQuitValue_sub_one_le
    hunit roots who stage hreward).trans ?_
  have hmass := (quittingRootOpponentAbsorptionMass_le_absorptionMass (roots stage) who).trans
    (absorption_le_four_mul (roots stage) (hsmall stage))
  have h : 2 * M * quittingRootOpponentAbsorptionMass (roots stage) who ≤
      2 * M * (4 * ε) :=
    mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) hM)
  nlinarith

/-- From block entry to any of its four deadline substages, the payoff is
within `8Mε` of the unit solo exit. -/
theorem abs_quittingSerializedDeadlineValue_sub_one_le
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hunit : QuittingUnitSoloExit reward) (roots : ℕ → Fin 4 → PMF Bool)
    (who : Fin 4) (stage : ℕ) (phase : Fin 4) {M ε : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ ε) :
    |quittingRootSequencePureTimeTerminalValue reward (quittingSerializedRoots roots) who
        (some (4 * stage + phase.val)) (4 * stage) - 1| ≤ 8 * M * ε := by
  let serial := quittingSerializedRoots roots
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who) who)
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hsmall stage who)
  have hmass : ∀ offset : Fin 4,
      quittingRootOpponentAbsorptionMass (serial (4 * stage + offset.val)) who ≤ ε := by
    intro offset
    refine (quittingRootOpponentAbsorptionMass_le_absorptionMass _ _).trans ?_
    dsimp only [serial]
    rw [quittingSerializedRoots_at, quittingSerializedStage,
      quittingRootAbsorptionMass_soloMixedRoot]
    exact hsmall stage offset
  have hbounded : ∀ time,
      |quittingRootSequencePureTimeTerminalValue reward serial who
        (some (4 * stage + phase.val)) time| ≤ M := by
    intro time
    exact abs_quittingTerminalPayoff_le reward
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate serial who
          (quittingPureTimeHazard (some (4 * stage + phase.val)))) time) who hreward
  have hremaining : ∀ (remaining : ℕ) (offset : Fin 4),
      offset.val + remaining = phase.val →
      |quittingRootSequencePureTimeTerminalValue reward serial who
          (some (4 * stage + phase.val)) (4 * stage + offset.val) - 1| ≤
        2 * M * ε * (remaining + 1 : ℕ) := by
    intro remaining
    induction remaining with
    | zero =>
        intro offset heq
        have hoffset : offset = phase := Fin.ext (by omega)
        subst offset
        rw [quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
        have hscaled :
            2 * M * quittingRootOpponentAbsorptionMass (serial (4 * stage + phase.val)) who ≤
              2 * M * ε :=
          mul_le_mul_of_nonneg_left (hmass phase) (mul_nonneg (by norm_num) hM)
        simpa using (abs_quittingFixedOpponentsQuitValue_sub_one_le
          hunit serial who _ hreward).trans hscaled
    | succ remaining ih =>
        intro offset heq
        let next : Fin 4 := ⟨offset.val + 1, by omega⟩
        have htail := ih next (by dsimp [next]; omega)
        have hstep :=
          abs_quittingRootContinuePayoff_sub_tail_le_two_mul_opponentAbsorptionMass
            reward
            (fun _ => quittingRootSequencePureTimeTerminalValue reward serial who
              (some (4 * stage + phase.val)) (4 * stage + offset.val + 1))
            (serial (4 * stage + offset.val)) who M hreward
            (hbounded (4 * stage + offset.val + 1))
        have hcontinue := quittingRootSequencePureTimeTerminalValue_continue_step
          reward serial who (some (4 * stage + phase.val)) (4 * stage + offset.val)
          (by intro h; injection h with h; omega)
        have hroot : quittingRootContinuePayoff reward
            (fun _ => quittingRootSequencePureTimeTerminalValue reward serial who
              (some (4 * stage + phase.val)) (4 * stage + offset.val + 1))
            (serial (4 * stage + offset.val)) who =
          quittingRootSequencePureTimeTerminalValue reward serial who
            (some (4 * stage + phase.val)) (4 * stage + offset.val) := by
          rw [hcontinue]
          exact quittingRootContinuePayoff_eq_fixedOpponents reward serial who _ _
        rw [hroot] at hstep
        have hscaled :
            2 * M * quittingRootOpponentAbsorptionMass (serial (4 * stage + offset.val)) who ≤
              2 * M * ε :=
          mul_le_mul_of_nonneg_left (hmass offset) (mul_nonneg (by norm_num) hM)
        have hstep' := hstep.trans hscaled
        have htail' : |quittingRootSequencePureTimeTerminalValue reward serial who
            (some (4 * stage + phase.val)) (4 * stage + offset.val + 1) - 1| ≤
            2 * M * ε * (remaining + 1 : ℕ) := by
          simpa [next, Nat.add_assoc] using htail
        have htriangle := abs_sub_le
          (quittingRootSequencePureTimeTerminalValue reward serial who
            (some (4 * stage + phase.val)) (4 * stage + offset.val))
          (quittingRootSequencePureTimeTerminalValue reward serial who
            (some (4 * stage + phase.val)) (4 * stage + offset.val + 1)) 1
        push_cast
        push_cast at htail'
        nlinarith
  have h := hremaining phase.val 0 (by simp)
  simp only [Fin.val_zero, Nat.add_zero] at h
  dsimp only [serial] at h
  have hphase : (phase.val + 1 : ℝ) ≤ 4 := by exact_mod_cast (by omega : phase.val + 1 ≤ 4)
  push_cast at h
  have hfactor : 0 ≤ 2 * M * ε := mul_nonneg (mul_nonneg (by norm_num) hM) hε
  exact h.trans (by nlinarith)

/-- Every finite substage deadline is close to its original-clock deadline.
This is the source's prefix-plus-stopping-block comparison, on actual values. -/
theorem abs_quittingSerializedPureDeadline_sub_original_le
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hunit : QuittingUnitSoloExit reward) (roots : ℕ → Fin 4 → PMF Bool)
    (who : Fin 4) (stage : ℕ) (phase : Fin 4) {M ε : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ ε) :
    |quittingRootSequencePureTimeTerminalValue reward (quittingSerializedRoots roots) who
          (some (4 * stage + phase.val)) 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who (some stage) 0| ≤
      24 * M * ε := by
  let deleted := quittingRootSequenceUpdate roots who (fun _ => PMF.pure false)
  let first : Payoff (Fin 4) := fun _ =>
    quittingRootSequencePureTimeTerminalValue reward (quittingSerializedRoots roots) who
      (some (4 * stage + phase.val)) (4 * stage)
  let second : Payoff (Fin 4) := fun _ =>
    quittingRootSequencePureTimeTerminalValue reward roots who (some stage) stage
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who) who)
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hsmall stage who)
  have hdeleted : ∀ time owner, (deleted time owner true).toReal ≤ ε := by
    intro time owner
    by_cases howner : owner = who
    · simpa [deleted, quittingRootSequenceUpdate, howner] using hε
    · simpa [deleted, quittingRootSequenceUpdate, Function.update_of_ne howner] using
        hsmall time owner
  have hboundary : |first who - second who| ≤ 16 * M * ε := by
    have hy := abs_quittingSerializedDeadlineValue_sub_one_le
      hunit roots who stage phase hreward hsmall
    have hx := abs_quittingOriginalDeadlineValue_sub_one_le
      hunit roots who stage hreward hsmall
    calc
      |first who - second who| ≤ |first who - 1| + |1 - second who| := abs_sub_le _ _ _
      _ ≤ 16 * M * ε := by dsimp [first, second]; rw [abs_sub_comm 1]; linarith
  have hprefix := abs_quittingSerializedWindowPayoff_sub_original_le
    reward deleted who (fun terminal => hreward terminal who) hdeleted first second 0 stage
  have hy := quittingPureTimeTerminalValue_eq_continueWord reward
    (quittingSerializedRoots roots) who (4 * stage + phase.val) 0 (4 * stage) (by omega)
  have hx := quittingPureTimeTerminalValue_eq_continueWord reward
    roots who stage 0 stage (by omega)
  rw [quittingSerializedWindowWord_eq_ofFn,
    quittingSerializedRoots_update_continue] at hprefix
  dsimp only [deleted, quittingRootSequenceUpdate] at hprefix
  simp only [Nat.zero_add, Nat.mul_zero] at hy hx hprefix
  change |quittingFiniteRootWordPayoff reward _ first who -
    quittingFiniteRootWordPayoff reward _ second who| ≤ _ at hprefix
  rw [← hy, ← hx] at hprefix
  have hweight0 := quittingJointSurvivalWeight_nonneg deleted 0 stage
  have hweight1 := quittingJointSurvivalWeight_le_one deleted 0 stage
  have hfactor : 0 ≤ 8 * M * ε := mul_nonneg (mul_nonneg (by norm_num) hM) hε
  have hfirst := mul_le_of_le_one_right hfactor (by linarith :
    1 - quittingJointSurvivalWeight deleted 0 stage ≤ 1)
  have hsecond := (mul_le_mul_of_nonneg_left hboundary hweight0).trans
    (mul_le_of_le_one_left (by nlinarith : 0 ≤ 16 * M * ε) hweight1)
  exact hprefix.trans (by linarith)

/-- Never comparison is the whole-profile estimate on the actual deleted roots. -/
theorem abs_quittingSerializedNever_sub_original_le
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool) (who : Fin 4) {M ε : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hsmall : ∀ time owner, (roots time owner true).toReal ≤ ε) :
    |quittingRootSequencePureTimeTerminalValue reward (quittingSerializedRoots roots) who none 0 -
        quittingRootSequencePureTimeTerminalValue reward roots who none 0| ≤ 8 * M * ε := by
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hsmall 0 who)
  have hdeleted : ∀ time owner,
      (quittingRootSequenceUpdate roots who (fun _ => PMF.pure false) time owner true).toReal ≤
        ε := by
    intro time owner
    by_cases howner : owner = who
    · simpa [quittingRootSequenceUpdate, howner] using hε
    · simpa [quittingRootSequenceUpdate, Function.update_of_ne howner] using hsmall time owner
  have h := abs_quittingSerializedTerminalValue_sub_original_le reward
    (quittingRootSequenceUpdate roots who (fun _ => PMF.pure false)) who hreward hdeleted 0
  rw [quittingSerializedRoots_update_continue] at h
  have hnever : quittingPureTimeHazard none = (fun _ => PMF.pure false) := by
    funext time
    rfl
  simpa only [quittingRootSequencePureTimeTerminalValue,
    quittingRootSequenceHazardTerminalValue, hnever, Nat.mul_zero] using h

end GameTheory
