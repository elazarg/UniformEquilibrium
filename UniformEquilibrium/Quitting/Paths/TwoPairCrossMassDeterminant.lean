import MathUE.PMFProduct.Conditioning
import UniformEquilibrium.Quitting.Paths.CommonStoppingCalendarRetiming
import UniformEquilibrium.Quitting.Paths.BehaviorFirstStoppingPairLaw
import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

/-!
# Cross-mass determinant for four independent stopping laws

The four clocks are regrouped into the independent pairs `(0,2)` and
`(1,3)`.  The four strict-order rectangles have an exact product identity;
their inclusions into the six relevant first-stopping atoms give the
determinant inequality.
-/

noncomputable section

namespace GameTheory

open Math Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

private def regroupedStoppingTimes
    (sample : Fin 2 → Option ℕ × Option ℕ) : Fin 4 → Option ℕ :=
  ![sample 0 |>.1, sample 1 |>.1, sample 0 |>.2, sample 1 |>.2]

private def regroupedStoppingTimesEquiv :
    (Fin 2 → Option ℕ × Option ℕ) ≃ (Fin 4 → Option ℕ) where
  toFun := regroupedStoppingTimes
  invFun := fun times ↦ ![(times 0, times 2), (times 1, times 3)]
  left_inv sample := by
    funext pair
    fin_cases pair <;> rfl
  right_inv times := by
    funext player
    fin_cases player <;> rfl

private def pairedStoppingLaw
    (first second : PMF (Option ℕ)) : PMF (Option ℕ × Option ℕ) :=
  (pmfPi ![first, second]).map (finTwoArrowEquiv (Option ℕ))

private theorem pairedStoppingLaw_apply
    (first second : PMF (Option ℕ)) (pair : Option ℕ × Option ℕ) :
    pairedStoppingLaw first second pair = first pair.1 * second pair.2 := by
  rw [pairedStoppingLaw, map_equiv_apply, pmfPi_apply]
  simp [Fin.prod_univ_two]

private def regroupedPairLaws
    (laws : Fin 4 → PMF (Option ℕ)) : Fin 2 → PMF (Option ℕ × Option ℕ) :=
  ![pairedStoppingLaw (laws 0) (laws 2), pairedStoppingLaw (laws 1) (laws 3)]

private theorem map_regroupedPairLaws_eq_pmfPi
    (laws : Fin 4 → PMF (Option ℕ)) :
    (pmfPi (regroupedPairLaws laws)).map regroupedStoppingTimesEquiv = pmfPi laws := by
  ext times
  rw [map_equiv_apply, pmfPi_apply, pmfPi_apply]
  simp [regroupedPairLaws, pairedStoppingLaw_apply,
    regroupedStoppingTimesEquiv, Fin.prod_univ_two, Fin.prod_univ_four]
  ac_rfl

private theorem crossOrders_outcome
    {players : Type} [Fintype players] [DecidableEq players] [Nonempty players]
    (times : players → Option ℕ)
    (firstEarly firstLate secondLate secondEarly : players)
    (hcover : ∀ player,
      player = firstEarly ∨ player = firstLate ∨
        player = secondLate ∨ player = secondEarly)
    (hfirst : quittingStoppingTimeValue (times firstEarly) <
      quittingStoppingTimeValue (times firstLate))
    (hsecond : quittingStoppingTimeValue (times secondEarly) <
      quittingStoppingTimeValue (times secondLate)) :
    quittingFirstStoppingOutcome times = some ⟨{firstEarly}, by simp⟩ ∨
      quittingFirstStoppingOutcome times = some ⟨{secondEarly}, by simp⟩ ∨
      quittingFirstStoppingOutcome times =
        some ⟨{firstEarly, secondEarly}, by simp⟩ := by
  cases hfirstValue : times firstEarly with
  | none => simp [hfirstValue, quittingStoppingTimeValue] at hfirst
  | some firstTime =>
    cases hsecondValue : times secondEarly with
    | none => simp [hsecondValue, quittingStoppingTimeValue] at hsecond
    | some secondTime =>
      have hfirstInside : times firstEarly = some firstTime := hfirstValue
      have hsecondInside : times secondEarly = some secondTime := hsecondValue
      have hfirstOrder : quittingStoppingTimeValue (some firstTime) <
          quittingStoppingTimeValue (times firstLate) := by
        simpa [hfirstValue] using hfirst
      have hsecondOrder : quittingStoppingTimeValue (some secondTime) <
          quittingStoppingTimeValue (times secondLate) := by
        simpa [hsecondValue] using hsecond
      rcases lt_trichotomy firstTime secondTime with hbefore | heq | hafter
      · left
        apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
          times {firstEarly} (by simp) firstTime
        · intro player hplayer
          simp only [Finset.mem_singleton] at hplayer
          subst player
          exact hfirstInside
        · intro player hplayer
          rcases hcover player with rfl | rfl | rfl | rfl
          · simp at hplayer
          · exact hfirstOrder
          · have hbefore' : quittingStoppingTimeValue (some firstTime) <
                quittingStoppingTimeValue (some secondTime) := by
              simpa [quittingStoppingTimeValue] using hbefore
            exact hbefore'.trans hsecondOrder
          · simpa [hsecondValue, quittingStoppingTimeValue] using hbefore
      · subst secondTime
        exact Or.inr (Or.inr (by
          apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
            times {firstEarly, secondEarly} (by simp) firstTime
          · intro player hplayer
            simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
            rcases hplayer with rfl | rfl
            · exact hfirstInside
            · exact hsecondInside
          · intro player hplayer
            rcases hcover player with rfl | rfl | rfl | rfl
            · simp at hplayer
            · exact hfirstOrder
            · exact hsecondOrder
            · simp at hplayer))

      · exact Or.inr (Or.inl (by
          apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
            times {secondEarly} (by simp) secondTime
          · intro player hplayer
            simp only [Finset.mem_singleton] at hplayer
            subst player
            exact hsecondInside
          · intro player hplayer
            rcases hcover player with rfl | rfl | rfl | rfl
            · simpa [hfirstValue, quittingStoppingTimeValue] using hafter
            · have hafter' : quittingStoppingTimeValue (some secondTime) <
                  quittingStoppingTimeValue (some firstTime) := by
                simpa [quittingStoppingTimeValue] using hafter
              exact hafter'.trans hfirstOrder
            · exact hsecondOrder
            · simp at hplayer))

private theorem outcome_pair_implies_strict_orders
    {players : Type} [Fintype players] [DecidableEq players] [Nonempty players]
    (times : players → Option ℕ) (first second firstLater secondLater : players)
    (hfirstLater : firstLater ∉ ({first, second} : Finset players))
    (hsecondLater : secondLater ∉ ({first, second} : Finset players))
    (houtcome : quittingFirstStoppingOutcome times =
      some ⟨{first, second}, by simp⟩) :
    quittingStoppingTimeValue (times first) <
        quittingStoppingTimeValue (times firstLater) ∧
      quittingStoppingTimeValue (times second) <
        quittingStoppingTimeValue (times secondLater) := by
  have hcoalition : quittingEarliestStoppingCoalition times = {first, second} := by
    unfold quittingFirstStoppingOutcome at houtcome
    split at houtcome
    · simp at houtcome
    · exact congrArg Subtype.val (Option.some.inj houtcome)
  have strict_of_mem_not_mem
      (early late : players)
      (hearly : early ∈ ({first, second} : Finset players))
      (hlate : late ∉ ({first, second} : Finset players)) :
      quittingStoppingTimeValue (times early) <
        quittingStoppingTimeValue (times late) := by
    have hearlyMin : early ∈ quittingEarliestStoppingCoalition times := by
      rw [hcoalition]
      exact hearly
    have hlateNot : late ∉ quittingEarliestStoppingCoalition times := by
      rw [hcoalition]
      exact hlate
    have hle :=
      (mem_quittingEarliestStoppingCoalition_iff times early).mp hearlyMin late
    apply lt_of_le_of_ne hle
    intro heq
    apply hlateNot
    apply (mem_quittingEarliestStoppingCoalition_iff times late).mpr
    intro other
    rw [← heq]
    exact (mem_quittingEarliestStoppingCoalition_iff times early).mp
      hearlyMin other
  exact ⟨strict_of_mem_not_mem first firstLater (by simp) hfirstLater,
    strict_of_mem_not_mem second secondLater (by simp) hsecondLater⟩

private theorem crossForwardBackward_outcome
    (sample : Fin 2 → Option ℕ × Option ℕ)
    (hfirst : quittingStoppingTimeValue (sample 0).1 <
      quittingStoppingTimeValue (sample 0).2)
    (hsecond : quittingStoppingTimeValue (sample 1).2 <
      quittingStoppingTimeValue (sample 1).1) :
    quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
        some ⟨{0}, by simp⟩ ∨
      quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
        some ⟨{3}, by simp⟩ ∨
      quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
        some ⟨{0, 3}, by simp⟩ := by
  apply crossOrders_outcome (regroupedStoppingTimes sample) 0 2 1 3
  · intro player
    fin_cases player <;> simp
  · exact hfirst
  · exact hsecond

private theorem crossBackwardForward_outcome
    (sample : Fin 2 → Option ℕ × Option ℕ)
    (hfirst : quittingStoppingTimeValue (sample 0).2 <
      quittingStoppingTimeValue (sample 0).1)
    (hsecond : quittingStoppingTimeValue (sample 1).1 <
      quittingStoppingTimeValue (sample 1).2) :
    quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
        some ⟨{1}, by simp⟩ ∨
      quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
        some ⟨{2}, by simp⟩ ∨
      quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
        some ⟨{1, 2}, by simp⟩ := by
  apply crossOrders_outcome (regroupedStoppingTimes sample) 1 3 0 2
  · intro player
    fin_cases player <;> simp
  · exact hsecond
  · exact hfirst

private def pairForward (pair : Option ℕ × Option ℕ) : Prop :=
  quittingStoppingTimeValue pair.1 < quittingStoppingTimeValue pair.2

private def pairBackward (pair : Option ℕ × Option ℕ) : Prop :=
  quittingStoppingTimeValue pair.2 < quittingStoppingTimeValue pair.1

private theorem regroupedRectangleMass_eq
    (laws : Fin 4 → PMF (Option ℕ))
    (firstEvent secondEvent : Option ℕ × Option ℕ → Prop) :
    pmfMass (pmfPi (regroupedPairLaws laws))
        (fun sample ↦ firstEvent (sample 0) ∧ secondEvent (sample 1)) =
      pmfMass (regroupedPairLaws laws 0) firstEvent *
        pmfMass (regroupedPairLaws laws 1) secondEvent := by
  rw [show (fun sample : Fin 2 → Option ℕ × Option ℕ ↦
      firstEvent (sample 0) ∧ secondEvent (sample 1)) =
      (fun sample ↦ ∀ index,
        ![firstEvent, secondEvent] index (sample index)) by
    funext sample
    apply propext
    simp [Fin.forall_fin_two]]
  rw [pmfMass_pmfPi_forall, Fin.prod_univ_two]
  rfl

private theorem regroupedRectangleMass_determinant
    (laws : Fin 4 → PMF (Option ℕ)) :
    pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairForward (sample 0) ∧ pairForward (sample 1)) *
        pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairBackward (sample 0) ∧ pairBackward (sample 1)) =
      pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairForward (sample 0) ∧ pairBackward (sample 1)) *
        pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairBackward (sample 0) ∧ pairForward (sample 1)) := by
  rw [regroupedRectangleMass_eq, regroupedRectangleMass_eq,
    regroupedRectangleMass_eq, regroupedRectangleMass_eq]
  ac_rfl

private theorem quittingIndependentTerminalOutcomeLaw_eq_regrouped
    (laws : Fin 4 → PMF (Option ℕ)) :
    quittingIndependentTerminalOutcomeLaw laws =
      (pmfPi (regroupedPairLaws laws)).map
        (fun sample ↦ quittingFirstStoppingOutcome (regroupedStoppingTimes sample)) := by
  unfold quittingIndependentTerminalOutcomeLaw
  rw [← map_regroupedPairLaws_eq_pmfPi laws, PMF.map_comp]
  rfl

private theorem firstPair_outcome_implies_forwardForward
    (sample : Fin 2 → Option ℕ × Option ℕ)
    (houtcome : quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
      some ⟨{0, 1}, by simp⟩) :
    pairForward (sample 0) ∧ pairForward (sample 1) := by
  have horders := outcome_pair_implies_strict_orders
    (regroupedStoppingTimes sample) 0 1 2 3 (by simp) (by simp) houtcome
  exact horders

private theorem secondPair_outcome_implies_backwardBackward
    (sample : Fin 2 → Option ℕ × Option ℕ)
    (houtcome : quittingFirstStoppingOutcome (regroupedStoppingTimes sample) =
      some ⟨{2, 3}, by simp⟩) :
    pairBackward (sample 0) ∧ pairBackward (sample 1) := by
  have horders := outcome_pair_implies_strict_orders
    (regroupedStoppingTimes sample) 2 3 0 1 (by simp) (by simp) houtcome
  exact horders

private theorem groupedOutcomeFiberMass_eq
    (laws : Fin 4 → PMF (Option ℕ)) (outcome : QuittingTerminalOutcome (Fin 4)) :
    pmfMass (pmfPi (regroupedPairLaws laws))
        (fun sample ↦ quittingFirstStoppingOutcome
          (regroupedStoppingTimes sample) = outcome) =
      quittingIndependentTerminalOutcomeLaw laws outcome := by
  rw [quittingIndependentTerminalOutcomeLaw_eq_regrouped]
  exact (pushforward_apply_eq_pmfMass
    (pmfPi (regroupedPairLaws laws))
    (fun sample ↦ quittingFirstStoppingOutcome (regroupedStoppingTimes sample))
    outcome).symm

private theorem firstPairMass_le_forwardForwardMass
    (laws : Fin 4 → PMF (Option ℕ)) :
    quittingIndependentTerminalOutcomeLaw laws (some ⟨{0, 1}, by simp⟩) ≤
      pmfMass (pmfPi (regroupedPairLaws laws))
        (fun sample ↦ pairForward (sample 0) ∧ pairForward (sample 1)) := by
  rw [← groupedOutcomeFiberMass_eq]
  exact pmfMass_mono _ fun sample ↦ firstPair_outcome_implies_forwardForward sample

private theorem secondPairMass_le_backwardBackwardMass
    (laws : Fin 4 → PMF (Option ℕ)) :
    quittingIndependentTerminalOutcomeLaw laws (some ⟨{2, 3}, by simp⟩) ≤
      pmfMass (pmfPi (regroupedPairLaws laws))
        (fun sample ↦ pairBackward (sample 0) ∧ pairBackward (sample 1)) := by
  rw [← groupedOutcomeFiberMass_eq]
  exact pmfMass_mono _ fun sample ↦ secondPair_outcome_implies_backwardBackward sample

private theorem pmfMass_or_le_add
    {sample : Type} (law : PMF sample) (first second : sample → Prop) :
    pmfMass law (fun value ↦ first value ∨ second value) ≤
      pmfMass law first + pmfMass law second := by
  rw [pmfMass_eq_toOuterMeasure, pmfMass_eq_toOuterMeasure,
    pmfMass_eq_toOuterMeasure]
  exact MeasureTheory.measure_union_le _ _

private theorem forwardBackwardMass_le_crossPlusMass
    (laws : Fin 4 → PMF (Option ℕ)) :
    pmfMass (pmfPi (regroupedPairLaws laws))
        (fun sample ↦ pairForward (sample 0) ∧ pairBackward (sample 1)) ≤
      quittingIndependentTerminalOutcomeLaw laws (some ⟨{0}, by simp⟩) +
        quittingIndependentTerminalOutcomeLaw laws (some ⟨{3}, by simp⟩) +
        quittingIndependentTerminalOutcomeLaw laws (some ⟨{0, 3}, by simp⟩) := by
  let law := pmfPi (regroupedPairLaws laws)
  let outcome := fun sample ↦
    quittingFirstStoppingOutcome (regroupedStoppingTimes sample)
  calc
    pmfMass law
        (fun sample ↦ pairForward (sample 0) ∧ pairBackward (sample 1)) ≤
        pmfMass law (fun sample ↦
          outcome sample = some ⟨{0}, by simp⟩ ∨
          outcome sample = some ⟨{3}, by simp⟩ ∨
          outcome sample = some ⟨{0, 3}, by simp⟩) := by
      apply pmfMass_mono
      intro sample hsample
      exact crossForwardBackward_outcome sample hsample.1 hsample.2
    _ ≤ pmfMass law (fun sample ↦ outcome sample = some ⟨{0}, by simp⟩) +
          (pmfMass law (fun sample ↦ outcome sample = some ⟨{3}, by simp⟩) +
            pmfMass law (fun sample ↦
              outcome sample = some ⟨{0, 3}, by simp⟩)) := by
      have htail := pmfMass_or_le_add law
        (fun sample ↦ outcome sample = some ⟨{3}, by simp⟩)
        (fun sample ↦ outcome sample = some ⟨{0, 3}, by simp⟩)
      exact (pmfMass_or_le_add law _ _).trans (add_le_add_right htail _)
    _ = _ := by
      rw [groupedOutcomeFiberMass_eq, groupedOutcomeFiberMass_eq,
        groupedOutcomeFiberMass_eq]
      ac_rfl

private theorem backwardForwardMass_le_crossMinusMass
    (laws : Fin 4 → PMF (Option ℕ)) :
    pmfMass (pmfPi (regroupedPairLaws laws))
        (fun sample ↦ pairBackward (sample 0) ∧ pairForward (sample 1)) ≤
      quittingIndependentTerminalOutcomeLaw laws (some ⟨{1}, by simp⟩) +
        quittingIndependentTerminalOutcomeLaw laws (some ⟨{2}, by simp⟩) +
        quittingIndependentTerminalOutcomeLaw laws (some ⟨{1, 2}, by simp⟩) := by
  let law := pmfPi (regroupedPairLaws laws)
  let outcome := fun sample ↦
    quittingFirstStoppingOutcome (regroupedStoppingTimes sample)
  calc
    pmfMass law
        (fun sample ↦ pairBackward (sample 0) ∧ pairForward (sample 1)) ≤
        pmfMass law (fun sample ↦
          outcome sample = some ⟨{1}, by simp⟩ ∨
          outcome sample = some ⟨{2}, by simp⟩ ∨
          outcome sample = some ⟨{1, 2}, by simp⟩) := by
      apply pmfMass_mono
      intro sample hsample
      exact crossBackwardForward_outcome sample hsample.1 hsample.2
    _ ≤ pmfMass law (fun sample ↦ outcome sample = some ⟨{1}, by simp⟩) +
          (pmfMass law (fun sample ↦ outcome sample = some ⟨{2}, by simp⟩) +
            pmfMass law (fun sample ↦
              outcome sample = some ⟨{1, 2}, by simp⟩)) := by
      have htail := pmfMass_or_le_add law
        (fun sample ↦ outcome sample = some ⟨{2}, by simp⟩)
        (fun sample ↦ outcome sample = some ⟨{1, 2}, by simp⟩)
      exact (pmfMass_or_le_add law _ _).trans (add_le_add_right htail _)
    _ = _ := by
      rw [groupedOutcomeFiberMass_eq, groupedOutcomeFiberMass_eq,
        groupedOutcomeFiberMass_eq]
      ac_rfl

/-- For four independent stopping laws, the two complementary pair atoms
obey the cross-mass determinant inequality.  Never and all tie events remain
in the source law; no absorption or finite-support premise is used. -/
theorem quittingIndependentTerminalOutcomeLaw_twoPair_crossMassDeterminant
    (laws : Fin 4 → PMF (Option ℕ)) :
    quittingIndependentTerminalOutcomeLaw laws (some ⟨{0, 1}, by simp⟩) *
        quittingIndependentTerminalOutcomeLaw laws (some ⟨{2, 3}, by simp⟩) ≤
      (quittingIndependentTerminalOutcomeLaw laws (some ⟨{0}, by simp⟩) +
          quittingIndependentTerminalOutcomeLaw laws (some ⟨{3}, by simp⟩) +
          quittingIndependentTerminalOutcomeLaw laws (some ⟨{0, 3}, by simp⟩)) *
        (quittingIndependentTerminalOutcomeLaw laws (some ⟨{1}, by simp⟩) +
          quittingIndependentTerminalOutcomeLaw laws (some ⟨{2}, by simp⟩) +
          quittingIndependentTerminalOutcomeLaw laws (some ⟨{1, 2}, by simp⟩)) := by
  calc
    _ ≤ pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairForward (sample 0) ∧ pairForward (sample 1)) *
        pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairBackward (sample 0) ∧ pairBackward (sample 1)) :=
      mul_le_mul (firstPairMass_le_forwardForwardMass laws)
        (secondPairMass_le_backwardBackwardMass laws) bot_le bot_le
    _ = pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairForward (sample 0) ∧ pairBackward (sample 1)) *
        pmfMass (pmfPi (regroupedPairLaws laws))
          (fun sample ↦ pairBackward (sample 0) ∧ pairForward (sample 1)) :=
      regroupedRectangleMass_determinant laws
    _ ≤ _ := mul_le_mul (forwardBackwardMass_le_crossPlusMass laws)
      (backwardForwardMass_le_crossMinusMass laws) bot_le bot_le

/-- The exact finite coalition mass is the corresponding independent outcome-law atom. -/
theorem exactFiniteFirstStoppingCoalitionMass_eq_outcomeLaw_toReal
    {players : Type} [Fintype players] [DecidableEq players] [Nonempty players]
    (laws : players → PMF (Option ℕ))
    (coalition : {S : Finset players // S.Nonempty}) :
    Math.Probability.DiscreteHazard.StoppingLaw.exactFiniteFirstStoppingCoalitionMass
        laws coalition =
      (quittingIndependentTerminalOutcomeLaw laws (some coalition)).toReal := by
  let indicator : {S : Finset players // S.Nonempty} → Payoff players :=
    fun terminal _ ↦ if terminal = coalition then 1 else 0
  let profile := quittingStoppingLawProfile indicator laws
  let observer : players := coalition.2.choose
  have hpayoff := quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff
    indicator laws observer
  have hmoment := congrFun
    (quittingTerminalRewardMoment_outcomeMass indicator profile) observer
  have hterminalMass : quittingTerminalPayoff indicator profile observer =
      quittingTerminalOutcomeMass indicator profile (some coalition) := by
    rw [← hmoment]
    unfold quittingTerminalRewardMoment quittingTerminalOutcomeReward
    rw [Fintype.sum_option]
    simp only [Pi.zero_apply, mul_zero, zero_add, indicator]
    simp_rw [mul_ite, mul_one, mul_zero]
    simp
  have hexpected : quittingStoppingLawExpectedPayoff indicator laws observer =
      (quittingIndependentTerminalOutcomeLaw laws (some coalition)).toReal := by
    unfold quittingStoppingLawExpectedPayoff
    rw [Math.Probability.expect_eq_sum]
    rw [Fintype.sum_eq_single (some coalition)]
    · simp [indicator, quittingTerminalOutcomeReward]
    · intro outcome houtcome
      cases outcome with
      | none => simp [quittingTerminalOutcomeReward]
      | some terminal =>
        have hterminal : terminal ≠ coalition := by
          intro heq
          apply houtcome
          simp [heq]
        simp [quittingTerminalOutcomeReward, indicator, hterminal]
  rw [← hexpected, ← hpayoff, hterminalMass,
    ← quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass]
  unfold quittingBehaviorExactFiniteFirstCoalitionMass
    quittingBehaviorStoppingLaws profile
  simp_rw [quittingBehaviorStoppingLaw_stoppingLawProfile]

/-- The literal exact first-quitter masses of every actual behavioral
four-player quitting profile satisfy the separate-cross determinant. -/
theorem quittingBehaviorTwoPair_crossMassDeterminant
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{0, 1}, by simp⟩ *
        quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{2, 3}, by simp⟩ ≤
      (quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{0}, by simp⟩ +
          quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{3}, by simp⟩ +
          quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{0, 3}, by simp⟩) *
        (quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{1}, by simp⟩ +
          quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{2}, by simp⟩ +
          quittingBehaviorExactFiniteFirstCoalitionMass profile ⟨{1, 2}, by simp⟩) := by
  let laws := quittingBehaviorStoppingLaws reward profile
  let terminalLaw := quittingIndependentTerminalOutcomeLaw laws
  have hsource :=
    quittingIndependentTerminalOutcomeLaw_twoPair_crossMassDeterminant laws
  have hfinite (outcome : QuittingTerminalOutcome (Fin 4)) :
      terminalLaw outcome ≠ ⊤ := PMF.apply_ne_top terminalLaw outcome
  have hthree (first second third : QuittingTerminalOutcome (Fin 4)) :
      (terminalLaw first + terminalLaw second + terminalLaw third).toReal =
        (terminalLaw first).toReal + (terminalLaw second).toReal +
          (terminalLaw third).toReal := by
    have hfirstSecond : terminalLaw first + terminalLaw second ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfinite first, hfinite second⟩
    rw [ENNReal.toReal_add hfirstSecond (hfinite third),
      ENNReal.toReal_add (hfinite first) (hfinite second)]
  have hrightFinite :
      (terminalLaw (some ⟨{0}, by simp⟩) + terminalLaw (some ⟨{3}, by simp⟩) +
          terminalLaw (some ⟨{0, 3}, by simp⟩)) *
        (terminalLaw (some ⟨{1}, by simp⟩) + terminalLaw (some ⟨{2}, by simp⟩) +
          terminalLaw (some ⟨{1, 2}, by simp⟩)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hfinite _, hfinite _⟩, hfinite _⟩
    · exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨hfinite _, hfinite _⟩, hfinite _⟩
  change terminalLaw (some ⟨{0, 1}, by simp⟩) *
      terminalLaw (some ⟨{2, 3}, by simp⟩) ≤ _ at hsource
  have hreal := ENNReal.toReal_mono hrightFinite hsource
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hthree, hthree] at hreal
  have hmass (coalition : {S : Finset (Fin 4) // S.Nonempty}) :
      quittingBehaviorExactFiniteFirstCoalitionMass profile coalition =
        (quittingIndependentTerminalOutcomeLaw laws (some coalition)).toReal := by
    unfold quittingBehaviorExactFiniteFirstCoalitionMass laws
      quittingBehaviorStoppingLaws
    exact exactFiniteFirstStoppingCoalitionMass_eq_outcomeLaw_toReal _ _
  dsimp only [terminalLaw] at hreal
  simpa only [← hmass] using hreal

end GameTheory
