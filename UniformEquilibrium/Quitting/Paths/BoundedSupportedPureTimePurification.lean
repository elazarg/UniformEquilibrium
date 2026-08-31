import UniformEquilibrium.Quitting.Paths.BehaviorSupportedPureTimeReplacement

/-!
# Bounded supported purification to pure stopping times

An arbitrary behavioral profile can be made pure-clock coordinate by
coordinate.  Each replacement clock belongs to the current coordinate's
actual stopping-law support and does not lower that mover's current payoff.
The construction records at most `card ι` replacements.  It makes no claim
about other players' payoffs, caps, or debts.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One supported pure-time replacement which does not lower the mover's
payoff at its source profile. -/
def IsQuittingBehaviorSupportedPureTimeReplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) : Prop :=
  ∃ (mover : ι) (clock : Option ℕ),
    clock ∈ (quittingBehaviorStoppingLaw reward (source mover)).support ∧
    quittingTerminalPayoff reward source mover ≤
      quittingTerminalPayoff reward target mover ∧
    target = Function.update source mover
      (quittingPureTimeBehaviorStrategy reward mover clock)

/-- A finite supported-purification path with its replacement count exposed. -/
inductive QuittingBehaviorSupportedPureTimeReplacementPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ℕ → (quittingGame reward).BehaviorProfile →
      (quittingGame reward).BehaviorProfile → Prop
  | nil (profile) : QuittingBehaviorSupportedPureTimeReplacementPath
      reward 0 profile profile
  | cons {count source middle target}
      (step : IsQuittingBehaviorSupportedPureTimeReplacement
        reward source middle)
      (rest : QuittingBehaviorSupportedPureTimeReplacementPath
        reward count middle target) :
      QuittingBehaviorSupportedPureTimeReplacementPath
        reward (count + 1) source target

namespace QuittingBehaviorSupportedPureTimeReplacementPath

/-- Forgetting support and payoff annotations leaves literal behavioral
replacement ancestry. -/
theorem ancestry
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {count : ℕ}
    {source target : (quittingGame reward).BehaviorProfile}
    (path : QuittingBehaviorSupportedPureTimeReplacementPath
      reward count source target) :
    IsQuittingBehaviorReplacementAncestry source target := by
  induction path with
  | nil => exact Relation.ReflTransGen.refl
  | @cons count source middle target step rest ih =>
      obtain ⟨mover, clock, _hsupport, _hpayoff, hmiddle⟩ := step
      subst middle
      exact (isQuittingBehaviorReplacementAncestry_update source mover _).trans ih

end QuittingBehaviorSupportedPureTimeReplacementPath

/-- A pure-clock descendant obtained through at most `card ι` supported
non-payoff-lowering replacements. -/
structure QuittingBehaviorSupportedPureTimePurification
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) where
  targetTimes : QuittingPureTimeProfile ι
  replacementCount : ℕ
  replacementCount_le_card : replacementCount ≤ Fintype.card ι
  path : QuittingBehaviorSupportedPureTimeReplacementPath reward
    replacementCount source
      (quittingPureTimeProfileBehavior reward targetTimes)

/-- Every behavioral profile admits a bounded supported pure-time
purification. -/
theorem nonempty_quittingBehaviorSupportedPureTimePurification
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) :
    Nonempty (QuittingBehaviorSupportedPureTimePurification reward source) := by
  classical
  let PureAt := fun (profile : (quittingGame reward).BehaviorProfile)
      (who : ι) => ∃ clock : Option ℕ,
        profile who = quittingPureTimeBehaviorStrategy reward who clock
  have aux : ∀ (fuel : ℕ) (purified : Finset ι)
      (profile : (quittingGame reward).BehaviorProfile),
      ((Finset.univ : Finset ι) \ purified).card ≤ fuel →
      (∀ who, who ∈ purified → PureAt profile who) →
      ∃ (count : ℕ) (times : QuittingPureTimeProfile ι),
        count ≤ fuel ∧
        QuittingBehaviorSupportedPureTimeReplacementPath reward count profile
          (quittingPureTimeProfileBehavior reward times) := by
    intro fuel
    induction fuel with
    | zero =>
        intro purified profile hcard hpure
        have hremaining : ((Finset.univ : Finset ι) \ purified) = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
        have hallPure : ∀ who, PureAt profile who := by
          intro who
          apply hpure who
          by_contra hnot
          have hmem : who ∈ (Finset.univ : Finset ι) \ purified :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ who, hnot⟩
          rw [hremaining] at hmem
          simp at hmem
        let times : QuittingPureTimeProfile ι := fun who =>
          Classical.choose (hallPure who)
        have hprofile : quittingPureTimeProfileBehavior reward times = profile := by
          funext who
          rw [quittingPureTimeProfileBehavior_apply]
          exact (Classical.choose_spec (hallPure who)).symm
        refine ⟨0, times, by simp, ?_⟩
        rw [hprofile]
        exact QuittingBehaviorSupportedPureTimeReplacementPath.nil profile
    | succ fuel ih =>
        intro purified profile hcard hpure
        by_cases hremaining :
            ((Finset.univ : Finset ι) \ purified).Nonempty
        · obtain ⟨mover, hmover⟩ := hremaining
          have hmoverNot : mover ∉ purified := (Finset.mem_sdiff.mp hmover).2
          obtain ⟨clock, hsupport, hpayoff⟩ :=
            exists_support_pureTime_payoff_ge_prescribed reward profile mover
          let target := Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover clock)
          have hcard' :
              ((Finset.univ : Finset ι) \ insert mover purified).card ≤ fuel := by
            rw [Finset.sdiff_insert, Finset.card_erase_of_mem hmover]
            omega
          have hpure' : ∀ who, who ∈ insert mover purified →
              PureAt target who := by
            intro who hwho
            by_cases heq : who = mover
            · subst who
              exact ⟨clock, Function.update_self _ _ _⟩
            · obtain ⟨oldClock, holdClock⟩ :=
                hpure who ((Finset.mem_insert.mp hwho).resolve_left heq)
              refine ⟨oldClock, ?_⟩
              dsimp only [target]
              rw [Function.update_of_ne heq]
              exact holdClock
          obtain ⟨count, times, hcount, path⟩ :=
            ih (insert mover purified) target hcard' hpure'
          refine ⟨count + 1, times, by omega, ?_⟩
          apply QuittingBehaviorSupportedPureTimeReplacementPath.cons
            (middle := target)
          · exact ⟨mover, clock, hsupport, hpayoff, rfl⟩
          · exact path
        · have hcardZero :
              ((Finset.univ : Finset ι) \ purified).card = 0 :=
            Finset.card_eq_zero.mpr
              (Finset.not_nonempty_iff_eq_empty.mp hremaining)
          obtain ⟨count, times, hcount, path⟩ :=
            ih purified profile (by rw [hcardZero]; exact Nat.zero_le _) hpure
          exact ⟨count, times, hcount.trans (Nat.le_succ fuel), path⟩
  obtain ⟨count, times, hcount, path⟩ :=
    aux (Fintype.card ι) ∅ source (by simp) (by simp)
  exact ⟨{
    targetTimes := times
    replacementCount := count
    replacementCount_le_card := hcount
    path := path }⟩

end GameTheory
