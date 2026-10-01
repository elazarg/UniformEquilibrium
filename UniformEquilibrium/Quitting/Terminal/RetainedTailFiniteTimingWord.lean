import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingRecursion
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack
import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival

/-! # Exact finite timing-law root words

The pure and mixed timing laws determine the actual chronological roots, their
joint and player-deleted Never masses, and the retained-tail finite evaluators.
These are table-independent semantic identities; Nash, debt, and punishment
consumers remain in their existing diagnostic modules.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The behavioral realization of a finite timing word followed by a literal
retained tail. -/
def quittingRetainedTailFiniteTimingGraft
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward roots tail

/-! ## Retained-tail timing games and root words -/

/-- Pure root word represented by one finite timing-action profile.  A player
Quits at exactly its selected finite date and Continues at every displayed
date when it selects `Never`. -/
def quittingRetainedTailPureTimingRootStack
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    List (ι → PMF Bool) :=
  List.ofFn fun date who => PMF.pure (decide (choices who = some date))

/-- The finite normal-form timing game whose `Never` action resumes one fixed
actual behavioral tail.  This differs from the hard zero-tail timing game. -/
abbrev quittingRetainedTailFiniteTimingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => QuittingFiniteDeadlineTimingAction deadline)
    (fun choices who => quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward
        (quittingRetainedTailPureTimingRootStack deadline choices) tail) who)

/-- The retained-tail timing game has the finite timing-profile outcome
carrier. -/
instance quittingRetainedTailFiniteTimingGame_finiteOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (tail : (quittingGame reward).BehaviorProfile) :
    Finite (quittingRetainedTailFiniteTimingGame reward deadline tail).Outcome := by
  unfold quittingRetainedTailFiniteTimingGame KernelGame.ofPureEU
  infer_instance

/-- The finite hazard word carried by independent mixed timing laws. -/
def quittingRetainedTailMixedTimingRootStack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    List (ι → PMF Bool) :=
  List.ofFn fun date : Fin deadline => quittingProfileLiveRoot reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) date.val

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingRetainedTailPureTimingRootStack_length
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    (quittingRetainedTailPureTimingRootStack deadline choices).length =
      deadline := by
  simp [quittingRetainedTailPureTimingRootStack]

omit [DecidableEq ι] in
@[simp] theorem quittingRetainedTailMixedTimingRootStack_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingRetainedTailMixedTimingRootStack reward deadline mixed).length =
      deadline := by
  simp [quittingRetainedTailMixedTimingRootStack]

/-- A finite root word followed by the all-Continue tail is its hard
zero-tail realization. -/
def quittingRetainedTailFiniteTimingHardGraft
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingGraft reward roots
    (quittingAlwaysContinueProfile reward)

/-- The actual behavioral profile which executes the mixed-law finite root
word and resumes the prescribed tail on joint `Never`. -/
def quittingRetainedTailMixedTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (tail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingGraft reward
    (quittingRetainedTailMixedTimingRootStack reward deadline mixed) tail

omit [DecidableEq ι] in
private theorem quittingLiteralRootStackProfile_apply_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (tail : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) (history : (quittingGame reward).Hist time)
    (htime : time < roots.length) :
    quittingLiteralRootStackProfile reward roots tail who time history =
      roots.get ⟨time, htime⟩ who := by
  induction roots generalizing time with
  | nil => simp at htime
  | cons root roots ih =>
      cases time with
      | zero => rfl
      | succ time =>
          change quittingLiteralRootStackProfile reward roots tail who time
              (Fin.tail history.1, history.2) =
            roots.get ⟨time, by simpa using htime⟩ who
          exact ih time (Fin.tail history.1, history.2) (by simpa using htime)

omit [DecidableEq ι] in
private theorem quittingLiteralRootStackProfile_allContinue_of_length_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (who : ι) (time : ℕ) (history : (quittingGame reward).Hist time)
    (htime : roots.length ≤ time) :
    quittingLiteralRootStackProfile reward roots
        (quittingAlwaysContinueProfile reward) who time history =
      PMF.pure false := by
  induction roots generalizing time with
  | nil =>
      rfl
  | cons root roots ih =>
      cases time with
      | zero => simp at htime
      | succ time =>
          change quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward) who time
                (Fin.tail history.1, history.2) = PMF.pure false
          exact ih time (Fin.tail history.1, history.2) (by simpa using htime)

omit [DecidableEq ι] in
/-- The hard graft of the mixed-law hazard word is literally the canonical
behavioral realization of those independent finite timing laws.  This holds
also when a current survival probability is zero. -/
theorem quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingRetainedTailFiniteTimingHardGraft reward
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) =
      quittingFiniteDeadlineTimingProfile reward deadline mixed := by
  funext who time history
  by_cases htime : time < deadline
  · rw [quittingRetainedTailFiniteTimingHardGraft,
      quittingRetainedTailFiniteTimingGraft,
      quittingLiteralRootStackProfile_apply_lt]
    · simp only [quittingRetainedTailMixedTimingRootStack, List.get_ofFn]
      unfold quittingProfileLiveRoot quittingFiniteDeadlineTimingProfile
        quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
      rfl
    · simpa using htime
  · rw [quittingRetainedTailFiniteTimingHardGraft,
      quittingRetainedTailFiniteTimingGraft,
      quittingLiteralRootStackProfile_allContinue_of_length_le]
    · have hroot := congrFun
          (quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
            reward deadline mixed (Nat.le_of_not_gt htime)) who
      unfold quittingProfileLiveRoot quittingFiniteDeadlineTimingProfile
        quittingCompactStoppingLawProfile quittingStoppingLawBehaviorStrategy
        quittingAllContinueRoot at hroot
      exact hroot.symm
    · simpa using Nat.le_of_not_gt htime

omit [DecidableEq ι] in
/-- Playerwise survival through the mixed timing root word is the declared
`Never` mass of that player's finite timing law. -/
theorem quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingLiteralRootStackOwnSurvival
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) who =
      (mixed who none).toReal := by
  let law : PMF (Option ℕ) :=
    (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
  unfold quittingLiteralRootStackOwnSurvival
    quittingRetainedTailMixedTimingRootStack quittingProfileLiveRoot
    quittingFiniteDeadlineTimingProfile quittingCompactStoppingLawProfile
    quittingStoppingLawBehaviorStrategy
  rw [List.map_ofFn]
  change (List.ofFn fun date : Fin deadline =>
      (((Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard law).toBoolean
        date.val false).toReal)).prod = (mixed who none).toReal
  rw [List.prod_ofFn]
  simp only [Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.booleanCoin_false_toReal]
  let continuationMass : ℕ → ℝ := fun time =>
    1 - (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard law).stop time
  change (∏ date : Fin deadline, continuationMass date.val) =
    (mixed who none).toReal
  rw [Fin.prod_univ_eq_prod_range]
  have hproduct : Math.survivalProduct continuationMass 0 deadline =
      ∏ time ∈ Finset.range deadline, continuationMass time := by
    simp [Math.survivalProduct]
  rw [← hproduct]
  change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard law).survival
      0 deadline = (mixed who none).toReal
  rw [Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard_survival]
  have htail : ∀ time, deadline ≤ time →
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass law time = 0 := by
    intro time htime
    have hzero := quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le
      (mixed who) htime
    dsimp only [law,
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass]
    exact congrArg ENNReal.toReal hzero
  have hsum : (∑' time,
      Math.Probability.DiscreteHazard.StoppingLaw.finiteMass law time) =
      ∑ time ∈ Finset.range deadline,
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass law time := by
    rw [tsum_eq_sum (s := Finset.range deadline)]
    intro time htime
    exact htail time (Nat.le_of_not_gt (by simpa using htime))
  have htotal :=
    Math.Probability.DiscreteHazard.StoppingLaw.none_add_tsum_finiteMass law
  rw [hsum] at htotal
  have hnone : (law none).toReal = (mixed who none).toReal := by
    have hmass : (mixed who).map quittingFiniteDeadlineTimingActionTime
        (⊤ : Math.Probability.CompactStoppingTime) = mixed who none := by
      rw [PMF.map_apply]
      rw [tsum_eq_single none]
      · simp [quittingFiniteDeadlineTimingActionTime]
      · intro action haction
        cases action with
        | none => exact (haction rfl).elim
        | some time => simp [quittingFiniteDeadlineTimingActionTime]
    dsimp only [law, quittingFiniteDeadlineTimingLaw]
    rw [Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    exact congrArg ENNReal.toReal hmass
  unfold Math.Probability.DiscreteHazard.StoppingLaw.survival
  linarith

omit [DecidableEq ι] in
/-- Joint finite-word survival is the product of the playerwise survival
coefficients. -/
theorem quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival
    (roots : List (ι → PMF Bool)) :
    quittingLiteralRootStackJointSurvival roots =
      ∏ player, quittingLiteralRootStackOwnSurvival roots player := by
  induction roots with
  | nil =>
      simp [quittingLiteralRootStackJointSurvival,
        quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      change quittingStationaryContinueMass root *
          quittingLiteralRootStackJointSurvival roots =
        ∏ player, (root player false).toReal *
          quittingLiteralRootStackOwnSurvival roots player
      rw [quittingStationaryContinueMass_eq_prod_continueProbability, ih,
        Finset.prod_mul_distrib]

private theorem quittingRootOpponentContinueMass_eq_prod_erase
    (root : ι → PMF Bool) (player : ι) :
    quittingRootOpponentContinueMass root player =
      ∏ other ∈ Finset.univ.erase player, (root other false).toReal := by
  classical
  rw [quittingRootOpponentContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  have hfunction :
      (fun other =>
        ((Function.update root player (PMF.pure false)) other false).toReal) =
        Function.update (fun other => (root other false).toReal) player 1 := by
    funext other
    by_cases hother : other = player
    · subst other
      simp
    · simp [Function.update_of_ne hother]
  rw [hfunction, Finset.prod_update_of_mem (Finset.mem_univ player)]
  simp only [one_mul, Finset.sdiff_singleton_eq_erase]

/-- Player-deleted finite-word survival is the product of every other
player's own survival coefficient. -/
theorem quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase
    (roots : List (ι → PMF Bool)) (player : ι) :
    quittingLiteralRootStackOpponentSurvival roots player =
      ∏ other ∈ Finset.univ.erase player,
        quittingLiteralRootStackOwnSurvival roots other := by
  induction roots with
  | nil =>
      simp [quittingLiteralRootStackOpponentSurvival,
        quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      change quittingRootOpponentContinueMass root player *
          quittingLiteralRootStackOpponentSurvival roots player =
        ∏ other ∈ Finset.univ.erase player,
          (root other false).toReal *
            quittingLiteralRootStackOwnSurvival roots other
      rw [quittingRootOpponentContinueMass_eq_prod_erase, ih,
        Finset.prod_mul_distrib]

omit [Fintype ι] [DecidableEq ι] in
/-- A deterministic player's finite timing word survives exactly when that
player selected `Never`. -/
theorem quittingRetainedTailPureTimingRootStack_ownSurvival_eq_indicator
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) :
    quittingLiteralRootStackOwnSurvival
        (quittingRetainedTailPureTimingRootStack deadline choices) who =
      if choices who = none then 1 else 0 := by
  unfold quittingLiteralRootStackOwnSurvival
    quittingRetainedTailPureTimingRootStack
  rw [List.map_ofFn, List.prod_ofFn]
  cases hchoice : choices who with
  | none => simp [hchoice]
  | some chosen =>
      rw [ite_eq_right (by simp)]
      apply Finset.prod_eq_zero (Finset.mem_univ chosen)
      simp [hchoice]

omit [DecidableEq ι] in
/-- A deterministic finite timing word jointly survives exactly on the
all-`Never` pure timing profile. -/
theorem quittingRetainedTailPureTimingRootStack_jointSurvival_eq_indicator
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline) :
    quittingLiteralRootStackJointSurvival
        (quittingRetainedTailPureTimingRootStack deadline choices) =
      if choices = fun _ ↦ none then 1 else 0 := by
  rw [quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
  simp_rw [quittingRetainedTailPureTimingRootStack_ownSurvival_eq_indicator]
  by_cases hall : choices = fun _ ↦ none
  · subst choices
    simp
  · rw [ite_eq_right hall]
    have hexists : ∃ who, choices who ≠ none := by
      by_contra hnone
      push Not at hnone
      exact hall (funext hnone)
    obtain ⟨who, hwho⟩ := hexists
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    simp [hwho]

omit [DecidableEq ι] in
/-- Joint survival of the mixed-law root word is the product of all declared
`Never` masses. -/
theorem quittingRetainedTailMixedTimingRootStack_jointSurvival_eq_prod_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingLiteralRootStackJointSurvival
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) =
      ∏ player, (mixed player none).toReal := by
  rw [quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
  exact Finset.prod_congr rfl fun player _ =>
    quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
      reward deadline mixed player

/-- Player-deleted survival of the mixed-law root word is the product of the
opponents' declared `Never` masses. -/
theorem quittingRetainedTailMixedTimingRootStack_opponentSurvival_eq_prod_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingLiteralRootStackOpponentSurvival
        (quittingRetainedTailMixedTimingRootStack reward deadline mixed) who =
      ∏ other ∈ Finset.univ.erase who, (mixed other none).toReal := by
  rw [quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase]
  exact Finset.prod_congr rfl fun other _ =>
    quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
      reward deadline mixed other

/-- Literal pure payoff of one retained-tail finite timing declaration. -/
def quittingRetainedTailTimingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (quittingRetainedTailFiniteTimingGraft reward
      (quittingRetainedTailPureTimingRootStack deadline choices) tail) who

/-- Expected retained-tail payoff under independent mixed timing laws. -/
def quittingRetainedTailTimingMixedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) : ℝ :=
  Math.Probability.expect (pmfPi mixed) fun choices =>
    quittingRetainedTailTimingPurePayoff reward tail deadline choices who

omit [DecidableEq ι] in
/-- The retained-tail normal-form mixed EU is exactly the expectation of the
literal behavioral graft, with no semantic replacement of the terminal tail. -/
theorem quittingRetainedTailFiniteTimingGame_mixedEU_eq_mixedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension.eu
        mixed who =
      quittingRetainedTailTimingMixedPayoff reward tail deadline mixed who := by
  let : Finite
      (quittingRetainedTailFiniteTimingGame reward deadline tail).Outcome :=
    quittingRetainedTailFiniteTimingGame_finiteOutcome reward deadline tail
  rw [(quittingRetainedTailFiniteTimingGame reward deadline tail).mixedExtension_eu]
  unfold quittingRetainedTailTimingMixedPayoff
    quittingRetainedTailTimingPurePayoff quittingRetainedTailFiniteTimingGame
  simp only [KernelGame.eu_ofPureEU]

omit [Fintype ι] [DecidableEq ι] in
/-- The current root and shifted choices split the literal pure root word. -/
theorem quittingRetainedTailPureTimingRootStack_succ
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (deadline + 1)) :
    quittingRetainedTailPureTimingRootStack (deadline + 1) choices =
      timingChoicesRoot choices ::
        quittingRetainedTailPureTimingRootStack deadline
          (timingChoicesTail choices) := by
  unfold quittingRetainedTailPureTimingRootStack
  rw [List.ofFn_succ]
  congr 1
  · funext who
    unfold timingChoicesRoot
    cases hchoice : choices who with
    | none => rfl
    | some time =>
        cases time using Fin.cases with
        | zero => rfl
        | succ later => rfl
  · apply congrArg List.ofFn
    funext date
    funext who
    apply congrArg PMF.pure
    cases hchoice : choices who with
    | none => simp [hchoice, timingChoicesTail, timingActionTail]
    | some time =>
        cases time using Fin.cases with
        | zero =>
            have htail : timingChoicesTail choices who = none := by
              unfold timingChoicesTail
              rw [hchoice]
              rfl
            rw [htail]
            have hleft : (0 : Fin (deadline + 1)) ≠ date.succ := by
              intro heq
              have := congrArg Fin.val heq
              simp at this
            have hright : (none : Option (Fin deadline)) ≠ some date := by
              intro heq
              cases heq
            simp [hleft, hright]
        | succ later => simp [hchoice, timingChoicesTail, timingActionTail]

omit [DecidableEq ι] in
/-- At deadline zero the retained timing payoff is the prescribed payoff of
the actual retained tail. -/
theorem quittingRetainedTailTimingMixedPayoff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction 0))
    (who : ι) :
    quittingRetainedTailTimingMixedPayoff reward tail 0 mixed who =
      quittingTerminalPayoff reward tail who := by
  have hmixed : mixed = fun _ => PMF.pure none := by
    funext player
    exact Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
  rw [hmixed]
  unfold quittingRetainedTailTimingMixedPayoff
  rw [pmfPi_pure]
  simp [quittingRetainedTailTimingPurePayoff,
    quittingRetainedTailPureTimingRootStack,
    quittingRetainedTailFiniteTimingGraft]

omit [DecidableEq ι] in
/-- Bellman peeling for a deterministic retained-tail timing declaration. -/
theorem quittingRetainedTailTimingPurePayoff_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ)
    (choices : ι → QuittingFiniteDeadlineTimingAction (deadline + 1))
    (who : ι) :
    quittingRetainedTailTimingPurePayoff reward tail (deadline + 1) choices who =
      quittingRootPayoff reward
        (fun player => quittingRetainedTailTimingPurePayoff reward tail deadline
          (timingChoicesTail choices) player)
        (fun player => timingActionCurrent (choices player)) who := by
  unfold quittingRetainedTailTimingPurePayoff
    quittingRetainedTailFiniteTimingGraft
  rw [quittingRetainedTailPureTimingRootStack_succ,
    quittingLiteralRootStackProfile_cons,
    quittingTerminalPayoff_rootThenContinuation_eq]
  unfold quittingRootExpectedPayoff timingChoicesRoot
  rw [pmfPi_pure]
  simp only [Math.Probability.expect_pure]

omit [DecidableEq ι] in
/-- Replacing the retained tail by all-Continue recovers the ordinary hard
finite-timing pure payoff. -/
theorem quittingRetainedTailTimingPurePayoff_alwaysContinue_eq_timingPurePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ (deadline : ℕ)
      (choices : ι → QuittingFiniteDeadlineTimingAction deadline)
      (who : ι),
      quittingRetainedTailTimingPurePayoff reward
          (quittingAlwaysContinueProfile reward) deadline choices who =
        timingPurePayoff reward deadline choices who := by
  intro deadline
  induction deadline with
  | zero =>
      intro choices who
      unfold quittingRetainedTailTimingPurePayoff
        quittingRetainedTailPureTimingRootStack
        quittingRetainedTailFiniteTimingGraft
      rw [timingPurePayoff_zero]
      simp
  | succ deadline ih =>
      intro choices who
      rw [quittingRetainedTailTimingPurePayoff_succ,
        timingPurePayoff_succ]
      congr 1
      funext player
      exact ih (timingChoicesTail choices) player


end GameTheory
