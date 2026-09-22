import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality
import UniformEquilibrium.Quitting.Terminal.FiniteOpponentLateResponse

/-!
# A missed reply between two supported calendar dates

One player stays at Never while the other has a fair stopping law on dates
zero and two.  The first player's best pure reply lies at the unsupported
intervening date one.
-/

noncomputable section

namespace GameTheory
namespace SparseCalendarReplyGap

open _root_.Math.Probability Math.PMFProduct

abbrev Player := Bool

/-- Player `false` receives `1` when quitting alone, `0` when player `true`
quits alone, and `-1` when they quit together.  Player `true` receives zero. -/
def reward (coalition : {S : Finset Player // S.Nonempty})
    (who : Player) : ℝ :=
  if who = false then
    if false ∈ coalition.1 then
      if true ∈ coalition.1 then -1 else 1
    else 0
  else 0

/-- The fair law supported on dates zero and two. -/
def sparseLaw : PMF (Option ℕ) :=
  (PMF.uniformOfFintype Bool).map fun coin =>
    if coin then some 2 else some 0

/-- Player `false` stays at Never and player `true` uses `sparseLaw`. -/
def laws : Player → PMF (Option ℕ)
  | false => PMF.pure none
  | true => sparseLaw

/-- The actual behavioral reconstruction of the sparse stopping laws. -/
def profile : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward laws

/-- Terminal payoff to player `false` after one deterministic reply. -/
def replyValue (choice : Option ℕ) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update profile false
      (quittingPureTimeBehaviorStrategy reward false choice)) false

/-- The complete deterministic reply menu, including every unsupported date
and Never. -/
theorem replyValue_eq (choice : Option ℕ) :
    replyValue choice =
      if choice = some 1 then 1 / 2
      else if choice = some 2 then -1 / 2
      else 0 := by
  unfold replyValue profile
  rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
  rw [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  unfold quittingStoppingLawExpectedPayoff
    quittingIndependentTerminalOutcomeLaw
  rw [expect_map]
  let sigma := Function.update laws false (PMF.pure choice)
  change expect (pmfPi sigma) _ = _
  have hsigma : sigma = Function.update
      (fun _ : Player => PMF.pure choice) true sparseLaw := by
    funext player
    cases player <;> simp [sigma, laws]
  have hlaw : pmfPi sigma =
      (sigma true).map (fun clock player => if player then clock else choice) := by
    rw [hsigma, pmfPi_update_pure_family]
    change sparseLaw.bind (PMF.pure ∘ fun clock =>
        Function.update (fun _ : Player => choice) true clock) =
      sparseLaw.map (fun clock player => if player then clock else choice)
    rw [PMF.bind_pure_comp]
    congr 1
    funext clock player
    cases player <;> rfl
  rw [hlaw, expect_map]
  change expect sparseLaw _ = _
  unfold sparseLaw
  rw [expect_map]
  cases choice with
  | none =>
      simp [reward, expect_eq_sum,
        PMF.uniformOfFintype_apply, quittingTerminalOutcomeReward,
        quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
        quittingEarliestStoppingCoalition, quittingStoppingTimeValue]
  | some time =>
      rcases time with _ | time
      · simp [reward, expect_eq_sum,
          PMF.uniformOfFintype_apply, quittingTerminalOutcomeReward,
          quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
          quittingEarliestStoppingCoalition, quittingStoppingTimeValue]
      · rcases time with _ | time
        · simp [reward, expect_eq_sum,
            PMF.uniformOfFintype_apply, quittingTerminalOutcomeReward,
            quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
            quittingEarliestStoppingCoalition, quittingStoppingTimeValue]
        · rcases time with _ | time
          · simp [reward, expect_eq_sum,
              PMF.uniformOfFintype_apply, quittingTerminalOutcomeReward,
              quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
              quittingEarliestStoppingCoalition, quittingStoppingTimeValue]
            norm_num
          · simp [reward, expect_eq_sum,
              PMF.uniformOfFintype_apply, quittingTerminalOutcomeReward,
              quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
              quittingEarliestStoppingCoalition, quittingStoppingTimeValue]
            intro himpossible
            norm_cast at himpossible

/-- The five source-displayed replies are respectively
`0, 1/2, -1/2, 0, 0`. -/
theorem displayed_replyValues :
    (replyValue (some 0), replyValue (some 1), replyValue (some 2),
      replyValue (some 3), replyValue none) =
      (0, 1 / 2, -1 / 2, 0, 0) := by
  simp [replyValue_eq]

/-- Player `false` receives zero under the prescribed sparse profile. -/
theorem profile_payoff_false_eq_zero :
    quittingTerminalPayoff reward profile false = 0 := by
  have hnone : replyValue none = 0 := by
    simpa using replyValue_eq none
  rw [← hnone]
  unfold replyValue profile
  rw [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq]
  congr 2
  funext player
  cases player <;> simp [laws]

private theorem replyValue_le_half (choice : Option ℕ) :
    replyValue choice ≤ 1 / 2 := by
  rw [replyValue_eq]
  split_ifs <;> norm_num

/-- Pure-time extremality turns the literal reply menu into the exact
unrestricted behavioral cap. -/
theorem behaviorDeviationPayoffCap_false_eq_half :
    quittingBehaviorDeviationPayoffCap reward profile false = 1 / 2 := by
  rw [quittingBehaviorDeviationPayoffCap_eq_pureTime]
  unfold quittingBehaviorPureTimePayoffCap quittingBehaviorPureTimePayoff
  change sSup (Set.range replyValue) = 1 / 2
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty replyValue)
    rintro _ ⟨choice, rfl⟩
    exact replyValue_le_half choice
  · apply le_csSup
    · exact ⟨1 / 2, by
        rintro _ ⟨choice, rfl⟩
        exact replyValue_le_half choice⟩
    · refine ⟨some 1, ?_⟩
      simp [replyValue_eq]

/-- The defective sparse test checks only the two atoms, one post-calendar
date, and Never. -/
def sparseTestedReplyCap : ℝ :=
  ({none, some 0, some 2, some 3} : Finset (Option ℕ)).sup'
    (by simp) replyValue

/-- The defective sparse menu reports cap zero. -/
theorem sparseTestedReplyCap_eq_zero : sparseTestedReplyCap = 0 := by
  simp [sparseTestedReplyCap, replyValue_eq]
  norm_num

/-- The omitted intervening date creates an exact one-half cap gap. -/
theorem behaviorCap_sub_sparseTestedReplyCap_eq_half :
    quittingBehaviorDeviationPayoffCap reward profile false -
        sparseTestedReplyCap = 1 / 2 := by
  rw [behaviorDeviationPayoffCap_false_eq_half,
    sparseTestedReplyCap_eq_zero, sub_zero]

/-! ## Adding one actual always-Never player -/

abbrev ExtendedPlayer := Option Player

/-- Remove `none` from a parent coalition and forget the `some` tags. -/
def childCoalition (coalition : Finset ExtendedPlayer) : Finset Player :=
  coalition.biUnion fun who => who.elim ∅ singleton

/-- Extend the sparse table by a third player.  The fresh player's payoff is
zero; a child payoff is the old payoff whenever a child quits. -/
def extendedReward
    (coalition : {S : Finset ExtendedPlayer // S.Nonempty})
    (who : ExtendedPlayer) : ℝ :=
  match who with
  | none => 0
  | some child =>
      if h : (childCoalition coalition.1).Nonempty then
        reward ⟨childCoalition coalition.1, h⟩ child
      else 0

/-- The canonical equivalence between old players and non-fresh parent
players, assembled from Mathlib's `Option.isSome` equivalence. -/
def childEquiv : Player ≃ {who : ExtendedPlayer // who ≠ none} :=
  (Equiv.optionIsSomeEquiv Player).symm |>.trans
    (Equiv.subtypeEquivRight fun _ => Option.isSome_iff_ne_none)

@[simp] theorem childEquiv_apply (child : Player) :
    (childEquiv child).1 = some child :=
  rfl

/-- Deleting the fresh player recovers the old reward table under the
canonical child relabeling. -/
theorem delete_extendedReward_eq_reindex :
    quittingDeleteReward extendedReward (· = none) =
      quittingRewardReindex childEquiv reward := by
  funext coalition who
  obtain ⟨child, hchild⟩ := Option.ne_none_iff_exists.mp who.2
  have hwho : who = childEquiv child := by
    apply Subtype.ext
    exact hchild.symm
  subst who
  unfold quittingDeleteReward quittingRewardReindex extendedReward
  simp only [childEquiv_apply, Equiv.symm_apply_apply]
  split_ifs with hnonempty
  · congr 2
    ext child
    simp [childCoalition, quittingExtendDeletedCoalition, childEquiv]
    constructor
    · rintro ⟨a, ⟨ha, hmem⟩, hchild⟩
      cases a with
      | none => exact (ha rfl).elim
      | some old =>
          refine ⟨some old, Option.some_ne_none old, hmem, ?_⟩
          have heq : child = old := by simpa using hchild
          exact heq.symm
    · rintro ⟨a, ha, hmem, hget⟩
      refine ⟨a, ⟨ha, hmem⟩, ?_⟩
      cases a with
      | none => exact (ha rfl).elim
      | some old =>
          have heq : old = child := by simpa using hget
          simpa only [Option.elim_some, Finset.mem_singleton] using heq.symm
  · exfalso
    apply hnonempty
    obtain ⟨member, hmember⟩ := coalition.2
    obtain ⟨memberChild, hmemberChild⟩ :=
      Option.ne_none_iff_exists.mp member.2
    refine ⟨memberChild, ?_⟩
    unfold childCoalition quittingExtendDeletedCoalition
    rw [Finset.mem_biUnion]
    refine ⟨member.1, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨member, hmember, rfl⟩
    · rw [← hmemberChild]
      simp

/-- The old sparse profile, relabeled as the deletion of the fresh player. -/
def extendedChildProfile :
    (quittingGame (quittingDeleteReward extendedReward (· = none))).BehaviorProfile :=
  quittingProfileOfRewardEq delete_extendedReward_eq_reindex
    (quittingProfilePushforward childEquiv reward profile)

/-- The actual parent profile obtained by prescribing Never to the fresh
player. -/
def extendedProfile : (quittingGame extendedReward).BehaviorProfile :=
  quittingLiftDeletedProfile extendedReward (· = none) extendedChildProfile

/-- Adding the third always-Never player preserves every old player's exact
unrestricted behavioral cap. -/
theorem extendedProfile_child_behaviorCap (child : Player) :
    quittingBehaviorDeviationPayoffCap extendedReward extendedProfile (some child) =
      quittingBehaviorDeviationPayoffCap reward profile child := by
  have hlift := quittingBehaviorDeviationPayoffCap_liftDeletedProfile
    extendedReward (· = none) extendedChildProfile (childEquiv child)
  unfold extendedChildProfile at hlift
  rw [quittingBehaviorDeviationPayoffCap_profileOfRewardEq] at hlift
  rw [quittingBehaviorDeviationPayoffCap_profilePushforward] at hlift
  exact hlift

/-- In particular the missed one-half response survives the actual
three-player always-Never extension. -/
theorem extendedProfile_false_behaviorCap_eq_half :
    quittingBehaviorDeviationPayoffCap extendedReward extendedProfile (some false) =
      1 / 2 := by
  rw [extendedProfile_child_behaviorCap,
    behaviorDeviationPayoffCap_false_eq_half]

/-- Every deterministic reply payoff of the old player is literally
preserved by the actual always-Never extension. -/
def extendedReplyValue (choice : Option ℕ) : ℝ :=
  quittingTerminalPayoff extendedReward
    (Function.update extendedProfile (some false)
      (quittingPureTimeBehaviorStrategy extendedReward (some false) choice))
    (some false)

theorem extendedReplyValue_eq_replyValue (choice : Option ℕ) :
    extendedReplyValue choice = replyValue choice := by
  unfold extendedReplyValue extendedProfile
  have hlift := quittingTerminalPayoff_update_pureTime_liftDeletedProfile
    extendedReward (· = none) extendedChildProfile (childEquiv false) choice
  simp only [childEquiv_apply] at hlift
  unfold extendedChildProfile at hlift ⊢
  rw [quittingTerminalPayoff_update_pureTime_profileOfRewardEq] at hlift
  rw [hlift]
  have hstrategy :
      quittingPureTimeBehaviorStrategy
          (quittingRewardReindex childEquiv reward) (childEquiv false) choice =
        quittingStrategyPushforward childEquiv reward false
          (quittingPureTimeBehaviorStrategy reward false choice) := by
    funext time history
    rfl
  rw [hstrategy, ← quittingProfilePushforward_update,
    quittingTerminalPayoff_profilePushforward]
  rfl

/-- Hence the extended deterministic reply menu has the same complete
piecewise formula. -/
theorem extendedReplyValue_eq (choice : Option ℕ) :
    extendedReplyValue choice =
      if choice = some 1 then 1 / 2
      else if choice = some 2 then -1 / 2
      else 0 := by
  rw [extendedReplyValue_eq_replyValue, replyValue_eq]

/-- The same defective sparse test, now applied to the actual three-player
profile. -/
def extendedSparseTestedReplyCap : ℝ :=
  ({none, some 0, some 2, some 3} : Finset (Option ℕ)).sup'
    (by simp) extendedReplyValue

theorem extendedSparseTestedReplyCap_eq_zero :
    extendedSparseTestedReplyCap = 0 := by
  simp [extendedSparseTestedReplyCap, extendedReplyValue_eq]
  norm_num

/-- The sparse test still misses the exact half-unit behavioral cap after
adding the third always-Never player. -/
theorem extendedBehaviorCap_sub_sparseTestedReplyCap_eq_half :
    quittingBehaviorDeviationPayoffCap extendedReward extendedProfile (some false) -
        extendedSparseTestedReplyCap = 1 / 2 := by
  rw [extendedProfile_false_behaviorCap_eq_half,
    extendedSparseTestedReplyCap_eq_zero, sub_zero]

/-- The fresh player's actual stopping law is the point mass at Never. -/
theorem extendedProfile_fresh_stoppingLaw :
    quittingBehaviorStoppingLaw extendedReward (extendedProfile none) =
      PMF.pure none := by
  exact quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
    extendedReward (· = none) extendedChildProfile rfl

end SparseCalendarReplyGap
end GameTheory
