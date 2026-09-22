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

end SparseCalendarReplyGap
end GameTheory
