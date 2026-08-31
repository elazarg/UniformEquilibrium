import UniformEquilibrium.Diagnostics.Quitting.PureTimeMinimumPaidPort
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.DeadlineBoundedPureTimeCap

/-!
# Bounded exact-cap purification chains

This file retains the quantitative fuel hidden by the simpler purification
eliminator: at most one exact pure-time cap replacement per player is needed
before either a strict off-minimum target is reached or every coordinate is
canonical pure-time/`Never`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One literal pure-time replacement which attains the mover's unrestricted
behavioral cap against the source opponents. -/
def IsQuittingPureTimeCapReplacement
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (first second : (quittingGame reward).BehaviorProfile) : Prop :=
  ∃ (who : ι) (choice : Option ℕ),
    second = Function.update first who
      (quittingPureTimeBehaviorStrategy reward who choice) ∧
    quittingPureTimeDeviationPayoff reward first who choice =
      quittingContinuationBestResponseValue reward first who

/-- Exactly `steps` successive pure-time exact-cap replacements, with every
source of a nontrivial step on the displayed total-debt fibre.  The final
endpoint need not lie on that fibre. -/
inductive QuittingPureTimeCapReplacementStepsOnDebtFiber
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (minimumDebt : ℝ) :
    ℕ → (quittingGame reward).BehaviorProfile →
      (quittingGame reward).BehaviorProfile → Prop
  | refl (profile) :
      QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt 0
        profile profile
  | cons {steps first middle last} :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward first) = minimumDebt →
      IsQuittingPureTimeCapReplacement first middle →
      QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt steps
        middle last →
      QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt (steps + 1)
        first last

private theorem mem_of_sdiff_card_zero
    {players : Finset ι}
    (hcard : ((Finset.univ : Finset ι) \ players).card = 0) :
    ∀ who : ι, who ∈ players := by
  intro who
  by_contra hnot
  have hmem : who ∈ (Finset.univ : Finset ι) \ players :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ who, hnot⟩
  rw [Finset.card_eq_zero.mp hcard] at hmem
  simp at hmem

private theorem exists_pureTimeCapPurificationSteps_aux
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ) :
    ∀ (fuel : ℕ) (purified : Finset ι)
      (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ),
      ((Finset.univ : Finset ι) \ purified).card ≤ fuel →
      (∀ who ∈ purified, ∃ choice : Option ℕ,
        profile who = quittingPureTimeBehaviorStrategy reward who choice) →
      QuittingDeadlineBounded reward profile deadline →
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) = minimumDebt →
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ≤
          quittingTerminalSemanticDebtSum candidate) →
      0 < quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) →
      (∃ (times : QuittingPureTimeProfile ι) (steps : ℕ),
          steps ≤ fuel ∧
          QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt steps profile
            (quittingPureTimeProfileBehavior reward times) ∧
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward times)) =
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) ∧
          ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
            quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (quittingPureTimeProfileBehavior reward times)) ≤
              quittingTerminalSemanticDebtSum candidate) ∨
        ∃ (target : (quittingGame reward).BehaviorProfile)
          (targetBound steps : ℕ),
          steps ≤ fuel ∧
          QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt steps
            profile target ∧
          QuittingDeadlineBounded reward target targetBound ∧
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) <
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward target) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro purified profile _ hcard hpure _ hdebtEq hminimum _
      have hall : ∀ who, ∃ choice : Option ℕ,
          profile who = quittingPureTimeBehaviorStrategy reward who choice :=
        fun who => hpure who
          (mem_of_sdiff_card_zero (Nat.le_zero.mp hcard) who)
      let times : QuittingPureTimeProfile ι := fun who =>
        Classical.choose (hall who)
      have heq : quittingPureTimeProfileBehavior reward times = profile := by
        funext who
        exact (Classical.choose_spec (hall who)).symm
      exact Or.inl ⟨times, 0, le_rfl, by
        rw [heq]
        exact QuittingPureTimeCapReplacementStepsOnDebtFiber.refl profile,
        by rw [heq], by simpa only [heq] using hminimum⟩
  | succ fuel ih =>
      intro purified profile deadline hcard hpure hbound hdebtEq hminimum hpositive
      by_cases hremaining :
          ((Finset.univ : Finset ι) \ purified).Nonempty
      · obtain ⟨who, hwho⟩ := hremaining
        obtain ⟨choice, hcap, hshape⟩ :=
          exists_quittingDeadlineBounded_pureTime_eq_cap
            reward profile who hbound
        let target := Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)
        have hstep : IsQuittingPureTimeCapReplacement profile target :=
          ⟨who, choice, rfl, hcap⟩
        have htargetBound : QuittingDeadlineBounded reward target (deadline + 1) :=
          quittingDeadlineBounded_update_pureTime
            reward profile hbound who hshape
        have htargetLower : quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) ≤
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward target) :=
          hminimum _ (quittingTerminalSemanticPair_mem_carrier reward target)
        rcases lt_or_eq_of_le htargetLower with hstrict | hequal
        · exact Or.inr ⟨target, deadline + 1, 1, by omega,
            QuittingPureTimeCapReplacementStepsOnDebtFiber.cons hdebtEq hstep
              (QuittingPureTimeCapReplacementStepsOnDebtFiber.refl target),
            htargetBound, hstrict⟩
        · have hcard' :
              ((Finset.univ : Finset ι) \ insert who purified).card ≤ fuel := by
            rw [Finset.sdiff_insert, Finset.card_erase_of_mem hwho]
            omega
          have hpure' : ∀ player ∈ insert who purified,
              ∃ response : Option ℕ,
                target player =
                  quittingPureTimeBehaviorStrategy reward player response := by
            intro player hplayer
            by_cases heqPlayer : player = who
            · subst player
              exact ⟨choice, Function.update_self _ _ _⟩
            · obtain ⟨response, hresponse⟩ := hpure player
                ((Finset.mem_insert.mp hplayer).resolve_left heqPlayer)
              exact ⟨response, by
                dsimp [target]
                rw [Function.update_of_ne heqPlayer]
                exact hresponse⟩
          have hminimum' : ∀ candidate ∈
              quittingTerminalSemanticCarrier reward,
              quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward target) ≤
                quittingTerminalSemanticDebtSum candidate := by
            intro candidate hcandidate
            rw [← hequal]
            exact hminimum candidate hcandidate
          have hpositive' : 0 < quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward target) := by
            rw [← hequal]
            exact hpositive
          have hdebtEq' : quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward target) = minimumDebt := by
            rw [← hequal, hdebtEq]
          rcases ih (insert who purified) target (deadline + 1) hcard' hpure'
              htargetBound hdebtEq' hminimum' hpositive' with
            ⟨times, steps, hsteps, hchain, hdebt, hminimumTimes⟩ |
              ⟨last, lastBound, steps, hsteps, hchain, hlastBound, hlast⟩
          · exact Or.inl ⟨times, steps + 1, by omega,
              QuittingPureTimeCapReplacementStepsOnDebtFiber.cons hdebtEq
                hstep hchain,
              hdebt.trans hequal.symm, hminimumTimes⟩
          · exact Or.inr ⟨last, lastBound, steps + 1, by omega,
              QuittingPureTimeCapReplacementStepsOnDebtFiber.cons hdebtEq
                hstep hchain,
              hlastBound, hequal.trans_lt hlast⟩
      · have hcardZero :
            ((Finset.univ : Finset ι) \ purified).card = 0 :=
          Finset.card_eq_zero.mpr
            (Finset.not_nonempty_iff_eq_empty.mp hremaining)
        have hall : ∀ who, ∃ choice : Option ℕ,
            profile who = quittingPureTimeBehaviorStrategy reward who choice :=
          fun who => hpure who (mem_of_sdiff_card_zero hcardZero who)
        let times : QuittingPureTimeProfile ι := fun who =>
          Classical.choose (hall who)
        have heq : quittingPureTimeProfileBehavior reward times = profile := by
          funext who
          exact (Classical.choose_spec (hall who)).symm
        exact Or.inl ⟨times, 0, Nat.zero_le _, by
          rw [heq]
          exact QuittingPureTimeCapReplacementStepsOnDebtFiber.refl profile,
          by rw [heq], by simpa only [heq] using hminimum⟩

/-- A deadline-bounded positive global minimum either reaches a canonical
minimum or leaves the minimum in at most one exact-cap purification per
player. -/
theorem deadlineBoundedMinimum_purify_or_offMinimum_with_step_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ)
    (hbound : QuittingDeadlineBounded reward profile deadline)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    (∃ (times : QuittingPureTimeProfile ι) (steps : ℕ),
        steps ≤ Fintype.card ι ∧
        QuittingPureTimeCapReplacementStepsOnDebtFiber
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) steps profile
          (quittingPureTimeProfileBehavior reward times) ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingPureTimeProfileBehavior reward times)) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ∧
        ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward times)) ≤
            quittingTerminalSemanticDebtSum candidate) ∨
      ∃ (target : (quittingGame reward).BehaviorProfile)
        (targetBound steps : ℕ),
        steps ≤ Fintype.card ι ∧
        QuittingPureTimeCapReplacementStepsOnDebtFiber
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) steps profile target ∧
        QuittingDeadlineBounded reward target targetBound ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward target) := by
  simpa only [Finset.card_sdiff, Finset.card_univ, Finset.card_empty,
    Nat.sub_zero] using
    exists_pureTimeCapPurificationSteps_aux reward
      (quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile))
      (Fintype.card ι) ∅ profile deadline (by simp) (by simp) hbound rfl
      hminimum hpositive

/-- Fin4 specialization of bounded exact-cap purification: at most four
coordinate replacements are needed. -/
theorem finFourDeadlineBoundedMinimum_purify_or_offMinimum_with_four_steps
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ)
    (hbound : QuittingDeadlineBounded reward profile deadline)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    (∃ (times : QuittingPureTimeProfile (Fin 4)) (steps : ℕ),
        steps ≤ 4 ∧
        QuittingPureTimeCapReplacementStepsOnDebtFiber
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) steps profile
          (quittingPureTimeProfileBehavior reward times) ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingPureTimeProfileBehavior reward times)) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ∧
        ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward times)) ≤
            quittingTerminalSemanticDebtSum candidate) ∨
      ∃ (target : (quittingGame reward).BehaviorProfile)
        (targetBound steps : ℕ),
        steps ≤ 4 ∧
        QuittingPureTimeCapReplacementStepsOnDebtFiber
          (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) steps profile target ∧
        QuittingDeadlineBounded reward target targetBound ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward target) := by
  simpa using
    deadlineBoundedMinimum_purify_or_offMinimum_with_step_bound
      reward profile deadline hbound hminimum hpositive

end GameTheory
