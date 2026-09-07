import UniformEquilibrium.Quitting.Examples.PureCoalitionLowProductFailure

/-!
# A four-player inactive-coordinate embedding of pure-coalition low failure

The cyclic three-player pair-premium example is embedded literally into four
players.  The fourth player has zero participant premium and is inactive at
the witnessing product root.  Thus every pure coalition has a low participant,
while one actual absorbing independent root has strictly positive pure-Quit
premium at every active coordinate.
-/

noncomputable section

namespace GameTheory.PureCoalitionLowProductFailureFinFour

open Math.Probability Math.PMFProduct

/-- The three cyclic pair-premium rows, with a zero fourth coordinate. -/
def premium (terminal : Finset (Fin 4)) : Payoff (Fin 4) :=
  if terminal = {0, 1} then ![2, -1, 0, 0]
  else if terminal = {1, 2} then ![0, 2, -1, 0]
  else if terminal = {0, 2} then ![-1, 0, 2, 0]
  else 0

/-- The embedded reward table, with arbitrary passive coordinates. -/
def reward
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  rewardOfOwnPremium 0 premium passive

@[simp] theorem premium_singleton (player : Fin 4) :
    premium {player} player = 0 := by
  fin_cases player <;> simp +decide [premium]

@[simp] theorem reward_singleton
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (player : Fin 4) :
    reward passive (quittingSingletonTerminal player) player = 0 := by
  unfold reward rewardOfOwnPremium
  simp [quittingSingletonTerminal]

/-- Every nonempty pure coalition in the four-player embedding contains a
participant with nonpositive premium. -/
theorem everyPureCoalition_has_low_participant
    (terminal : Finset (Fin 4)) (hterminal : terminal.Nonempty) :
    ∃ player ∈ terminal, premium terminal player ≤ 0 := by
  by_cases h01 : terminal = {0, 1}
  · subst terminal
    exact ⟨1, by simp, by norm_num [premium]⟩
  by_cases h12 : terminal = {1, 2}
  · subst terminal
    refine ⟨2, by simp, ?_⟩
    change (-1 : ℝ) ≤ 0
    norm_num
  by_cases h02 : terminal = {0, 2}
  · subst terminal
    exact ⟨0, by simp, by norm_num [premium, h01, h12]⟩
  obtain ⟨player, hplayer⟩ := hterminal
  exact ⟨player, hplayer, by simp [premium, h01, h12, h02]⟩

/-- The pure-coalition property is stated on the actual embedded reward
table: every terminal coalition has a participant whose reward is at most
that participant's own singleton reward. -/
theorem everyPureCoalition_reward_has_low_participant
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    ∃ player ∈ terminal.1,
      reward passive terminal player ≤
        reward passive (quittingSingletonTerminal player) player := by
  obtain ⟨player, hplayer, hpremium⟩ :=
    everyPureCoalition_has_low_participant terminal.1 terminal.2
  refine ⟨player, hplayer, ?_⟩
  apply sub_nonpos.mp
  unfold reward
  rw [rewardOfOwnPremium_sub_singleton 0 premium passive terminal player
    hplayer (premium_singleton player)]
  exact hpremium

/-- Players zero, one, and two quit independently with probability one half;
player three continues surely. -/
def inactiveFourthHalfRoot : Fin 4 → PMF Bool := fun player =>
  if player = 3 then PMF.pure false
  else quittingHazardCoin (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem inactiveFourthHalfRoot_quitProbability
    (player : Fin 4) :
    (inactiveFourthHalfRoot player true).toReal =
      if player = 3 then 0 else 1 / 2 := by
  by_cases hplayer : player = 3
  · simp [inactiveFourthHalfRoot, hplayer]
  · simp [inactiveFourthHalfRoot, hplayer, quittingHazardCoin]

@[simp] theorem inactiveFourthHalfRoot_continueProbability
    (player : Fin 4) :
    (inactiveFourthHalfRoot player false).toReal =
      if player = 3 then 1 else 1 / 2 := by
  rw [pmfBool_false_toReal, inactiveFourthHalfRoot_quitProbability]
  split <;> norm_num

@[simp] theorem inactiveFourthHalfRoot_absorptionMass :
    quittingRootAbsorptionMass inactiveFourthHalfRoot = 7 / 8 := by
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_four]
  norm_num +decide

/-- At the embedded half-hazard root, every active player's actual pure-Quit
premium is one quarter. -/
theorem inactiveFourthHalfRoot_quitPremium
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (player : Fin 4) (hplayer : player ≠ 3) :
    quittingRootQuitPayoff (reward passive) 0 inactiveFourthHalfRoot player -
      reward passive (quittingSingletonTerminal player) player = 1 / 4 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases player <;>
    simp +decide [reward, rewardOfOwnPremium, premium, quittingRootPayoff,
      quittingQuitters, inactiveFourthHalfRoot, quittingHazardCoin,
      Math.Probability.expect_eq_sum] <;>
    norm_num
  exact (hplayer rfl).elim

/-- The inactive fourth coordinate is literally absent from the support of
the witnessing actual product root. -/
theorem inactiveFourthHalfRoot_fourth_inactive :
    (inactiveFourthHalfRoot 3 true).toReal = 0 := by
  simp

/-- The Fin4 embedded table fails product-low premiums, witnessed by the
actual absorbing root with inactive fourth player. -/
theorem not_hasProductLowQuittingPremium
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬HasProductLowQuittingPremium (reward passive) := by
  intro hlow
  obtain ⟨player, hactive, hquit⟩ :=
    hlow inactiveFourthHalfRoot (by norm_num)
  have hplayer : player ≠ 3 := by
    intro hequal
    subst player
    rw [inactiveFourthHalfRoot_fourth_inactive] at hactive
    linarith
  have hpremium := inactiveFourthHalfRoot_quitPremium passive player hplayer
  linarith

end GameTheory.PureCoalitionLowProductFailureFinFour
