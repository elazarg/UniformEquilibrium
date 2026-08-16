/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteCapApproximation

/-!
# All-player finite-cap bootstrap

This module composes one-coordinate cap approximations.  Two zero-Never seeds
suffice to create permanent finite sentinels, after which every remaining
coordinate can be capped while preserving a requested prefix.  The resulting
semantic control transports terminal approximate-Nash certificates.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-! ## Terminal-semantic transport -/

/-- Uniform coordinatewise control of the complete terminal semantics: the
prescribed payoff, the full behavioral best-response envelope, and debt. -/
def QuittingTerminalSemanticsWithin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (left right : (quittingGame reward).BehaviorProfile)
    (error : ℝ) : Prop :=
  ∀ observer,
    |(quittingTerminalSemanticPair reward left).1 observer -
        (quittingTerminalSemanticPair reward right).1 observer| ≤ error ∧
    |(quittingTerminalSemanticPair reward left).2 observer -
        (quittingTerminalSemanticPair reward right).2 observer| ≤ error ∧
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward left) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward right) observer| ≤ error

omit [Nontrivial ι] in
/-- Terminal-semantic error budgets compose additively. -/
theorem QuittingTerminalSemanticsWithin.trans
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first middle last : (quittingGame reward).BehaviorProfile}
    {firstError secondError : ℝ}
    (hfirst : QuittingTerminalSemanticsWithin reward first middle firstError)
    (hsecond : QuittingTerminalSemanticsWithin reward middle last secondError) :
    QuittingTerminalSemanticsWithin reward first last
      (firstError + secondError) := by
  intro observer
  have h₁ := hfirst observer
  have h₂ := hsecond observer
  constructor
  · calc
      |(quittingTerminalSemanticPair reward first).1 observer -
          (quittingTerminalSemanticPair reward last).1 observer| =
          |((quittingTerminalSemanticPair reward first).1 observer -
              (quittingTerminalSemanticPair reward middle).1 observer) +
            ((quittingTerminalSemanticPair reward middle).1 observer -
              (quittingTerminalSemanticPair reward last).1 observer)| := by
            congr 1
            ring
      _ ≤ |(quittingTerminalSemanticPair reward first).1 observer -
              (quittingTerminalSemanticPair reward middle).1 observer| +
            |(quittingTerminalSemanticPair reward middle).1 observer -
              (quittingTerminalSemanticPair reward last).1 observer| :=
          abs_add_le _ _
      _ ≤ firstError + secondError := add_le_add h₁.1 h₂.1
  · constructor
    · calc
        |(quittingTerminalSemanticPair reward first).2 observer -
            (quittingTerminalSemanticPair reward last).2 observer| =
            |((quittingTerminalSemanticPair reward first).2 observer -
                (quittingTerminalSemanticPair reward middle).2 observer) +
              ((quittingTerminalSemanticPair reward middle).2 observer -
                (quittingTerminalSemanticPair reward last).2 observer)| := by
              congr 1
              ring
        _ ≤ |(quittingTerminalSemanticPair reward first).2 observer -
                (quittingTerminalSemanticPair reward middle).2 observer| +
              |(quittingTerminalSemanticPair reward middle).2 observer -
                (quittingTerminalSemanticPair reward last).2 observer| :=
            abs_add_le _ _
        _ ≤ firstError + secondError := add_le_add h₁.2.1 h₂.2.1
    · calc
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward first) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward last) observer| =
            |(quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward first) observer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward middle) observer) +
              (quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward middle) observer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward last) observer)| := by
              congr 1
              ring
        _ ≤ |quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward first) observer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward middle) observer| +
            |quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward middle) observer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward last) observer| :=
          abs_add_le _ _
        _ ≤ firstError + secondError := add_le_add h₁.2.2 h₂.2.2

omit [Nontrivial ι] in
/-- Uniform payoff and best-response control transports a terminal
approximate-Nash certificate. -/
theorem isεAsymptoticNash_of_payoff_and_bestResponse_within
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    {ε error : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε source)
    (hpayoff : ∀ observer,
      |quittingTerminalPayoff reward source observer -
        quittingTerminalPayoff reward target observer| ≤ error)
    (hbest : ∀ observer,
      |quittingContinuationBestResponseValue reward source observer -
        quittingContinuationBestResponseValue reward target observer| ≤ error) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (ε + 2 * error) target := by
  have hsourceBest : ∀ observer,
      quittingContinuationBestResponseValue reward source observer ≤
        quittingTerminalPayoff reward source observer + ε := by
    intro observer
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, ⟨source observer, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact hnash observer deviation
  intro observer deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target observer deviation
  have hbestUpper :
      quittingContinuationBestResponseValue reward target observer ≤
        quittingContinuationBestResponseValue reward source observer + error := by
    linarith [neg_le_abs
      (quittingContinuationBestResponseValue reward source observer -
        quittingContinuationBestResponseValue reward target observer),
      hbest observer]
  have hpayoffUpper :
      quittingTerminalPayoff reward source observer ≤
        quittingTerminalPayoff reward target observer + error := by
    linarith [le_abs_self
      (quittingTerminalPayoff reward source observer -
        quittingTerminalPayoff reward target observer), hpayoff observer]
  linarith [hsourceBest observer]

omit [Nontrivial ι] in
/-- If every original live-path stopping law has zero `Never` mass, all
players can be capped at finite dates while keeping the complete terminal
semantic pair and every debt coordinate uniformly close.  Every resulting
strategy is literally a finite cap of its corresponding original strategy,
at a date no earlier than the requested lower bound. -/
theorem exists_allPlayersFiniteCap_terminalSemantics_close_of_neverMass_zero_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hnever : ∀ mover, quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile mover)) = 0)
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        lowerBound ≤ cutoff ∧ capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward capped).1 observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward capped).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward capped) observer| < δ) := by
  classical
  let η : ℝ := δ / ((Fintype.card ι : ℝ) + 1)
  have hdenom : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hδ hdenom
  have hfinite : ∀ players : Finset ι,
      ∃ current : (quittingGame reward).BehaviorProfile,
        (∀ mover ∈ players, ∃ cutoff,
          lowerBound ≤ cutoff ∧ current mover =
            quittingStoppingLawFiniteCapBehaviorStrategy reward mover
              (profile mover) cutoff) ∧
        (∀ mover ∉ players, current mover = profile mover) ∧
        QuittingTerminalSemanticsWithin reward profile current
          ((players.card : ℝ) * η) := by
    intro players
    induction players using Finset.induction_on with
    | empty =>
        refine ⟨profile, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro observer
          simp
    | @insert mover players hmover ih =>
        obtain ⟨current, hprocessed, hunprocessed, hcurrent⟩ := ih
        have hmoverCurrent : current mover = profile mover :=
          hunprocessed mover hmover
        have hmoverNever : quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward (current mover)) = 0 := by
          rw [hmoverCurrent]
          exact hnever mover
        obtain ⟨cutoff, hcutoffLower, hstep⟩ :=
          exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
            reward current mover hmoverNever lowerBound hη
        let next := quittingFiniteCapProfileAt reward current mover cutoff
        refine ⟨next, ?_, ?_, ?_⟩
        · intro player hplayer
          rcases Finset.mem_insert.mp hplayer with rfl | hplayerOld
          · refine ⟨cutoff, hcutoffLower, ?_⟩
            simp [next, quittingFiniteCapProfileAt, hmoverCurrent]
          · obtain ⟨oldCutoff, holdLower, hold⟩ :=
              hprocessed player hplayerOld
            refine ⟨oldCutoff, holdLower, ?_⟩
            have hne : player ≠ mover := by
              intro heq
              subst player
              exact hmover hplayerOld
            simp [next, quittingFiniteCapProfileAt,
              Function.update_of_ne hne, hold]
        · intro player hplayer
          have hnotOld : player ∉ players := by
            exact fun hmem => hplayer (Finset.mem_insert_of_mem hmem)
          have hne : player ≠ mover := by
            intro heq
            subst player
            exact hplayer (Finset.mem_insert_self mover players)
          simp [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hne, hunprocessed player hnotOld]
        · have hstepWithin :
              QuittingTerminalSemanticsWithin reward current next η := by
            intro observer
            have h := hstep observer
            simpa [next] using
              ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
          have hcombined :=
            QuittingTerminalSemanticsWithin.trans reward hcurrent hstepWithin
          have hcard : (insert mover players).card = players.card + 1 :=
            Finset.card_insert_of_notMem hmover
          convert hcombined using 1
          rw [hcard]
          push_cast
          ring
  obtain ⟨capped, hcapped, _hunprocessed, hclose⟩ :=
    hfinite Finset.univ
  have htotal : (Fintype.card ι : ℝ) * η < δ := by
    calc
      (Fintype.card ι : ℝ) * η <
          ((Fintype.card ι : ℝ) + 1) * η := by
        exact mul_lt_mul_of_pos_right (by linarith) hη
      _ = δ := by
        dsimp [η]
        field_simp
  refine ⟨capped, ?_, ?_⟩
  · intro mover
    exact hcapped mover (Finset.mem_univ mover)
  · intro observer
    have h := hclose observer
    simpa using ⟨lt_of_le_of_lt h.1 htotal,
      lt_of_le_of_lt h.2.1 htotal,
      lt_of_le_of_lt h.2.2 htotal⟩

/-- Once every player is finitely capped, every unilateral deviator faces a
distinct opponent who quits surely at one finite live date.  Thus the tail
after that date is behaviorally invisible to that deviation. -/
theorem quittingAllPlayersFiniteCap_deviation_has_finite_sureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source capped : (quittingGame reward).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover =
        quittingStoppingLawFiniteCapBehaviorStrategy reward mover
          (source mover) cutoff)
    (observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy observer) :
    ∃ cutoff, QuittingRootHasSureQuitter
      (quittingProfileLiveRoot reward
        (Function.update capped observer deviation) cutoff) := by
  obtain ⟨opponent, hopponent⟩ : ∃ opponent : ι, opponent ≠ observer :=
    exists_ne observer
  obtain ⟨cutoff, hcap⟩ := hcapped opponent
  refine ⟨cutoff, opponent, ?_⟩
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  unfold quittingRootSequenceUpdate
  rw [Function.update_of_ne hopponent]
  change quittingBehaviorLiveHazard reward (capped opponent) cutoff =
    PMF.pure true
  rw [hcap, quittingBehaviorLiveHazard_finiteCap]
  exact quittingHazardCapAt_self _ cutoff

/-- All of the deviation problems share one finite iteration bound.  Before
that horizon, every unilateral deviation encounters a prescribed opponent
who quits surely.  The horizon depends on the capped profile, but not on the
observer or its arbitrary behavioral deviation. -/
theorem quittingAllPlayersFiniteCap_deviation_has_uniform_horizon
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source capped : (quittingGame reward).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover =
        quittingStoppingLawFiniteCapBehaviorStrategy reward mover
          (source mover) cutoff) :
    ∃ horizon, ∀ observer
        (deviation : (quittingGame reward).BehaviorStrategy observer),
      ∃ cutoff, cutoff < horizon ∧ QuittingRootHasSureQuitter
        (quittingProfileLiveRoot reward
          (Function.update capped observer deviation) cutoff) := by
  classical
  let capTime : ι → ℕ := fun player => Classical.choose (hcapped player)
  have hcapTime : ∀ player, capped player =
      quittingStoppingLawFiniteCapBehaviorStrategy reward player
        (source player) (capTime player) := by
    intro player
    exact Classical.choose_spec (hcapped player)
  let horizon := Finset.univ.sup capTime + 1
  refine ⟨horizon, ?_⟩
  intro observer deviation
  obtain ⟨opponent, hopponent⟩ : ∃ opponent : ι,
      opponent ≠ observer := exists_ne observer
  refine ⟨capTime opponent, ?_, opponent, ?_⟩
  · dsimp [horizon]
    have hle : capTime opponent ≤ Finset.univ.sup capTime :=
      Finset.le_sup (Finset.mem_univ opponent)
    omega
  · rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
    unfold quittingRootSequenceUpdate
    rw [Function.update_of_ne hopponent]
    change quittingBehaviorLiveHazard reward (capped opponent)
        (capTime opponent) = PMF.pure true
    rw [hcapTime opponent, quittingBehaviorLiveHazard_finiteCap]
    exact quittingHazardCapAt_self _ (capTime opponent)

omit [DecidableEq ι] [Nontrivial ι] in
/-- If every selected cap date lies after `prefix`, the entire prescribed live
root word is preserved literally before `prefix`.  In particular, choosing a
positive lower bound fixes the time-zero entry root exactly. -/
theorem quittingAllPlayersFiniteCap_liveRoot_eq_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source capped : (quittingGame reward).BehaviorProfile)
    (prefixLength : ℕ)
    (hcapped : ∀ mover, ∃ cutoff, prefixLength ≤ cutoff ∧
      capped mover =
        quittingStoppingLawFiniteCapBehaviorStrategy reward mover
          (source mover) cutoff)
    {time : ℕ} (htime : time < prefixLength) :
    quittingProfileLiveRoot reward capped time =
      quittingProfileLiveRoot reward source time := by
  funext player
  obtain ⟨cutoff, hprefixCutoff, hcap⟩ := hcapped player
  change quittingBehaviorLiveHazard reward (capped player) time =
    quittingBehaviorLiveHazard reward (source player) time
  rw [hcap, quittingBehaviorLiveHazard_finiteCap,
    quittingHazardCapAt_of_lt]
  omega

/-! ## Two zero-Never seeds unlock arbitrary later buttons -/

/-- After two distinct players have been finitely capped, every third
player's maximal pair-deleted clock dies. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_cappedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source current : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirstCap : current first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (source first) firstTime)
    (hsecondCap : current second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (source second) secondTime) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward current) mover 0 fuel)
      atTop (nhds 0) := by
  have hfirstSure : quittingProfileLiveRoot reward current firstTime first =
      PMF.pure true := by
    change quittingBehaviorLiveHazard reward (current first) firstTime = _
    rw [hfirstCap, quittingBehaviorLiveHazard_finiteCap]
    exact quittingHazardCapAt_self _ firstTime
  have hsecondSure : quittingProfileLiveRoot reward current secondTime second =
      PMF.pure true := by
    change quittingBehaviorLiveHazard reward (current second) secondTime = _
    rw [hsecondCap, quittingBehaviorLiveHazard_finiteCap]
    exact quittingHazardCapAt_self _ secondTime
  exact tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_sentinels
    (quittingProfileLiveRoot reward current) mover first second
      hfirstSecond hfirstMover hsecondMover firstTime secondTime
      hfirstSure hsecondSure

omit [Nontrivial ι] in
/-- **Two-sentinel extension step.**  Once two distinct capped players are
present, an arbitrary third player's button can be capped at any requested
terminal-semantic accuracy.  No condition on that third button's Never mass
is needed. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_two_cappedPlayers_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source current : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirstCap : current first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (source first) firstTime)
    (hsecondCap : current second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (source second) secondTime)
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |(quittingTerminalSemanticPair reward current).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward current mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward current).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward current mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward current) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward current mover cutoff))
              observer| < δ := by
  letI : Nontrivial ι := nontrivial_of_ne first second hfirstSecond
  obtain ⟨cutoff, hlower, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_pairDeleted_after
      reward current mover (current mover)
      (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_cappedPlayers
        reward source current mover first second hfirstSecond hfirstMover
          hsecondMover firstTime secondTime hfirstCap hsecondCap)
      lowerBound hδ
  refine ⟨cutoff, hlower, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

omit [Nontrivial ι] in
/-- **Two-seed global finite reduction.**  It is enough that two distinct
original players have zero `Never` mass.  Cap those two first.  They then act
as permanent sentinels, so every remaining player can be capped in turn even
when that player's original law has positive `Never` mass.

The final profile is coordinatewise a literal finite cap of the original
profile, while prescribed payoff, the full behavioral best-response envelope,
and every debt coordinate are uniformly as close as requested. -/
theorem exists_allPlayersFiniteCap_terminalSemantics_close_of_two_zeroNever_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hfirstSecond : first ≠ second)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        lowerBound ≤ cutoff ∧ capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward capped).1 observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward capped).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward capped) observer| < δ) := by
  letI : Nontrivial ι := nontrivial_of_ne first second hfirstSecond
  classical
  let η : ℝ := δ / ((Fintype.card ι : ℝ) + 1)
  have hdenom : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hδ hdenom

  obtain ⟨firstTime, hfirstLate, hfirstStep⟩ :=
    exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
      reward profile first hneverFirst lowerBound hη
  let afterFirst :=
    quittingFiniteCapProfileAt reward profile first firstTime
  have hsecondAfterFirst : afterFirst second = profile second := by
    simp [afterFirst, quittingFiniteCapProfileAt,
      Function.update_of_ne hfirstSecond.symm]
  have hneverSecondAfterFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (afterFirst second)) = 0 := by
    rw [hsecondAfterFirst]
    exact hneverSecond
  obtain ⟨secondTime, hsecondLate, hsecondStep⟩ :=
    exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
      reward afterFirst second hneverSecondAfterFirst lowerBound hη
  let seeded :=
    quittingFiniteCapProfileAt reward afterFirst second secondTime

  have hfirstSeeded : seeded first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (profile first) firstTime := by
    simp [seeded, afterFirst, quittingFiniteCapProfileAt,
      Function.update_of_ne hfirstSecond]
  have hsecondSeeded : seeded second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (profile second) secondTime := by
    simp [seeded, quittingFiniteCapProfileAt, hsecondAfterFirst]
  have hunseeded : ∀ mover, mover ≠ first → mover ≠ second →
      seeded mover = profile mover := by
    intro mover hmoverFirst hmoverSecond
    simp [seeded, afterFirst, quittingFiniteCapProfileAt,
      Function.update_of_ne hmoverSecond,
      Function.update_of_ne hmoverFirst]

  have hwithinFirst :
      QuittingTerminalSemanticsWithin reward profile afterFirst η := by
    intro observer
    have h := hfirstStep observer
    simpa [afterFirst] using
      ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
  have hwithinSecond :
      QuittingTerminalSemanticsWithin reward afterFirst seeded η := by
    intro observer
    have h := hsecondStep observer
    simpa [seeded] using
      ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
  have hseededClose :
      QuittingTerminalSemanticsWithin reward profile seeded (2 * η) := by
    simpa [two_mul] using
      QuittingTerminalSemanticsWithin.trans reward hwithinFirst hwithinSecond

  have hfinite : ∀ players : Finset ι,
      first ∉ players → second ∉ players →
      ∃ current : (quittingGame reward).BehaviorProfile,
        current first =
            quittingStoppingLawFiniteCapBehaviorStrategy reward first
              (profile first) firstTime ∧
        current second =
            quittingStoppingLawFiniteCapBehaviorStrategy reward second
              (profile second) secondTime ∧
        (∀ mover ∈ players, ∃ cutoff,
          lowerBound ≤ cutoff ∧ current mover =
            quittingStoppingLawFiniteCapBehaviorStrategy reward mover
              (profile mover) cutoff) ∧
        (∀ mover ∉ players, mover ≠ first → mover ≠ second →
          current mover = profile mover) ∧
        QuittingTerminalSemanticsWithin reward profile current
          (((players.card : ℝ) + 2) * η) := by
    intro players
    induction players using Finset.induction_on with
    | empty =>
        intro _ _
        refine ⟨seeded, hfirstSeeded, hsecondSeeded, ?_, ?_, ?_⟩
        · simp
        · simpa using hunseeded
        · simpa using hseededClose
    | @insert mover players hmover ih =>
        intro hfirstInsert hsecondInsert
        have hfirstOld : first ∉ players := by
          exact fun hmem => hfirstInsert (Finset.mem_insert_of_mem hmem)
        have hsecondOld : second ∉ players := by
          exact fun hmem => hsecondInsert (Finset.mem_insert_of_mem hmem)
        have hfirstMover : first ≠ mover := by
          intro heq
          subst mover
          exact hfirstInsert (Finset.mem_insert_self first players)
        have hsecondMover : second ≠ mover := by
          intro heq
          subst mover
          exact hsecondInsert (Finset.mem_insert_self second players)
        obtain ⟨current, hfirstCurrent, hsecondCurrent,
            hprocessed, hunprocessed, hcurrent⟩ :=
          ih hfirstOld hsecondOld
        have hmoverCurrent : current mover = profile mover :=
          hunprocessed mover hmover hfirstMover.symm hsecondMover.symm
        obtain ⟨cutoff, hcutoffLate, hstep⟩ :=
          exists_quittingFiniteCapProfileAt_semantics_close_of_two_cappedPlayers_after
            reward profile current mover first second hfirstSecond
              hfirstMover hsecondMover firstTime secondTime
              hfirstCurrent hsecondCurrent lowerBound hη
        let next :=
          quittingFiniteCapProfileAt reward current mover cutoff
        refine ⟨next, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hfirstMover] using hfirstCurrent
        · simpa [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hsecondMover] using hsecondCurrent
        · intro player hplayer
          rcases Finset.mem_insert.mp hplayer with rfl | hplayerOld
          · refine ⟨cutoff, hcutoffLate, ?_⟩
            simp [next, quittingFiniteCapProfileAt, hmoverCurrent]
          · obtain ⟨oldCutoff, holdLate, hold⟩ :=
              hprocessed player hplayerOld
            refine ⟨oldCutoff, holdLate, ?_⟩
            have hplayerMover : player ≠ mover := by
              intro heq
              subst player
              exact hmover hplayerOld
            simpa [next, quittingFiniteCapProfileAt,
              Function.update_of_ne hplayerMover] using hold
        · intro player hplayer hplayerFirst hplayerSecond
          have hplayerOld : player ∉ players := by
            exact fun hmem => hplayer (Finset.mem_insert_of_mem hmem)
          have hplayerMover : player ≠ mover := by
            intro heq
            subst player
            exact hplayer (Finset.mem_insert_self mover players)
          simpa [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hplayerMover] using
              hunprocessed player hplayerOld hplayerFirst hplayerSecond
        · have hstepWithin :
              QuittingTerminalSemanticsWithin reward current next η := by
            intro observer
            have h := hstep observer
            simpa [next] using
              ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
          have hcombined :=
            QuittingTerminalSemanticsWithin.trans reward hcurrent hstepWithin
          have hcard : (insert mover players).card = players.card + 1 :=
            Finset.card_insert_of_notMem hmover
          convert hcombined using 1
          rw [hcard]
          push_cast
          ring

  let remaining : Finset ι := (Finset.univ.erase first).erase second
  have hfirstRemaining : first ∉ remaining := by
    simp [remaining]
  have hsecondRemaining : second ∉ remaining := by
    simp [remaining]
  obtain ⟨capped, hfirstCapped, hsecondCapped,
      hprocessed, _hunprocessed, hclose⟩ :=
    hfinite remaining hfirstRemaining hsecondRemaining
  have hsecondMemAfterFirstErase : second ∈ Finset.univ.erase first :=
    Finset.mem_erase.mpr ⟨hfirstSecond.symm, Finset.mem_univ second⟩
  have hremainingCard : remaining.card + 2 = Fintype.card ι := by
    have hsecondErase :=
      Finset.card_erase_add_one hsecondMemAfterFirstErase
    have hfirstErase :=
      Finset.card_erase_add_one (Finset.mem_univ first)
    rw [Finset.card_univ] at hfirstErase
    dsimp [remaining]
    omega
  have htotal : ((remaining.card : ℝ) + 2) * η < δ := by
    have hremainingCardReal : (remaining.card : ℝ) + 2 =
        (Fintype.card ι : ℝ) := by
      exact_mod_cast hremainingCard
    rw [hremainingCardReal]
    calc
      (Fintype.card ι : ℝ) * η <
          ((Fintype.card ι : ℝ) + 1) * η := by
        exact mul_lt_mul_of_pos_right (by linarith) hη
      _ = δ := by
        dsimp [η]
        field_simp
  refine ⟨capped, ?_, ?_⟩
  · intro mover
    by_cases hmoverFirst : mover = first
    · subst mover
      exact ⟨firstTime, hfirstLate, hfirstCapped⟩
    by_cases hmoverSecond : mover = second
    · subst mover
      exact ⟨secondTime, hsecondLate, hsecondCapped⟩
    · exact hprocessed mover (by
        simp [remaining, hmoverFirst, hmoverSecond])
  · intro observer
    have h := hclose observer
    exact ⟨lt_of_le_of_lt h.1 htotal,
      lt_of_le_of_lt h.2.1 htotal,
      lt_of_le_of_lt h.2.2 htotal⟩

omit [Nontrivial ι] in
/-- **Finite-horizon approximate-Nash reduction from two seeds.**  Under the
same two-zero-Never hypothesis, every terminal `ε`-Nash profile has a literal
all-player finite cap which is terminal `(epsilon + 2 * δ)`-Nash.  The full
terminal semantics, including debt, remains within `δ`. -/
theorem exists_allPlayersFiniteCap_isεAsymptoticNash_of_two_zeroNever_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hfirstSecond : first ≠ second)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        lowerBound ≤ cutoff ∧ capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward capped).1 observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward capped).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward capped) observer| < δ) ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + 2 * δ) capped := by
  obtain ⟨capped, hcapped, hclose⟩ :=
    exists_allPlayersFiniteCap_terminalSemantics_close_of_two_zeroNever_after
      reward profile first second hfirstSecond hneverFirst hneverSecond
        lowerBound hδ
  refine ⟨capped, hcapped, hclose, ?_⟩
  apply isεAsymptoticNash_of_payoff_and_bestResponse_within
      reward profile capped hnash
  · intro observer
    exact le_of_lt (hclose observer).1
  · intro observer
    exact le_of_lt (hclose observer).2.1

end GameTheory
