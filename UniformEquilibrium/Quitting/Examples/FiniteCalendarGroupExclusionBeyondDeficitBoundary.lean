import UniformEquilibrium.Quitting.Paths.TwoPairGroupExclusion
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# A four-player group-exclusion boundary beyond strict deficit

Two disjoint pairs receive elevated rewards when they quit together.  The
generic two-pair entrance theorem gives group exclusion with cap `1 / 2`,
while the pure first-pair exit refutes every positive strict singleton deficit.
-/

noncomputable section

namespace GameTheory.FiniteCalendarGroupExclusionBeyondDeficitBoundary

open QuittingSureSetOwnerRepair

def pairA : Finset (Fin 4) := {0, 1}

def pairB : Finset (Fin 4) := {2, 3}

def partner : Fin 4 → Fin 4 := ![1, 0, 3, 2]

def pairATerminal : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨pairA, by simp [pairA]⟩

def pairBTerminal : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨pairB, by simp [pairB]⟩

/-- Own singletons pay one; the owner's partner receives zero and the two
outsiders receive one half.  Pair `A` pays `(2,2,1,1)`, pair `B` pays
`(1,1,2,2)`, and every remaining coalition pays one half throughout. -/
def reward
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if terminal.1 = pairA then if who ∈ pairA then 2 else 1
  else if terminal.1 = pairB then if who ∈ pairB then 2 else 1
  else if terminal.1 = {who} then 1
  else if terminal.1 = {partner who} then 0
  else 1 / 2

@[simp] theorem reward_singleton (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = 1 := by
  fin_cases who <;>
    norm_num +decide [reward, quittingSingletonTerminal, pairA, pairB, partner]

@[simp] theorem reward_pairA (who : Fin 4) :
    reward pairATerminal who = if who ∈ pairA then 2 else 1 := by
  fin_cases who <;> norm_num +decide [reward, pairATerminal, pairA, pairB]

@[simp] theorem reward_pairB (who : Fin 4) :
    reward pairBTerminal who = if who ∈ pairB then 2 else 1 := by
  fin_cases who <;> norm_num +decide [reward, pairBTerminal, pairA, pairB]

private theorem reward_pairA_group_sum
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    reward terminal 0 + reward terminal 1 =
      if terminal.1 = pairA then 4 else if terminal.1 = pairB then 2 else 1 := by
  by_cases hA : terminal.1 = pairA
  · simp [reward, hA, pairA]
    norm_num
  by_cases hB : terminal.1 = pairB
  · simp [reward, hB, pairA, pairB]
    norm_num +decide
  by_cases hzero : terminal.1 = {0}
  · simp [reward, hzero, pairA, pairB, partner]
    norm_num +decide
  by_cases hone : terminal.1 = {1}
  · simp [reward, hone, pairA, pairB, partner]
    norm_num +decide
  simp [reward, hA, hB, hzero, hone, partner]
  norm_num

private theorem reward_pairB_group_sum
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) :
    reward terminal 2 + reward terminal 3 =
      if terminal.1 = pairA then 2 else if terminal.1 = pairB then 4 else 1 := by
  by_cases hA : terminal.1 = pairA
  · simp [reward, hA, pairA]
    norm_num
  by_cases hB : terminal.1 = pairB
  · simp [reward, hB, pairA, pairB]
    norm_num +decide
  by_cases htwo : terminal.1 = {2}
  · simp [reward, htwo, pairA, pairB, partner]
    norm_num +decide
  by_cases hthree : terminal.1 = {3}
  · simp [reward, hthree, pairA, pairB, partner]
    norm_num +decide
  simp [reward, hA, hB, htwo, hthree, partner]
  norm_num

/-- Every actual behavioral profile admits a half-capped group-exclusion
weight.  The selected pair may depend on the profile, but the cap does not. -/
theorem hasQuittingActualNonconcentratedGroupExclusion_half :
    HasQuittingActualNonconcentratedGroupExclusion reward ((1 : ℝ) / 2) := by
  apply hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds
    (a := 1) (b := 0) (L := 1 / 2)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [reward_singleton]
  · norm_num [reward_singleton]
  · rw [quittingTwoCoordinateAverageSurplus]
    have hsum := reward_pairA_group_sum pairATerminal
    norm_num [pairATerminal, pairA, pairB] at hsum
    simp only [reward_singleton]
    linarith
  · rw [quittingTwoCoordinateAverageSurplus]
    have hsum := reward_pairB_group_sum pairATerminal
    norm_num [pairATerminal, pairA, pairB] at hsum
    simp only [reward_singleton]
    linarith
  · rw [quittingTwoCoordinateAverageSurplus]
    have hsum := reward_pairA_group_sum pairBTerminal
    norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB] at hsum
    simp only [reward_singleton]
    linarith
  · rw [quittingTwoCoordinateAverageSurplus]
    have hsum := reward_pairB_group_sum pairBTerminal
    have hne : ({2, 3} : Finset (Fin 4)) ≠ {0, 1} := by decide
    simp [pairBTerminal, pairA, pairB, hne] at hsum
    simp only [reward_singleton]
    linarith
  · intro terminal hA hB
    have hAval : terminal.1 ≠ pairA := fun heq ↦ hA (Subtype.ext heq)
    have hBval : terminal.1 ≠ pairB := fun heq ↦ hB (Subtype.ext heq)
    constructor
    · rw [quittingTwoCoordinateAverageSurplus]
      have hsum := reward_pairA_group_sum terminal
      simp [hAval, hBval] at hsum
      simp only [reward_singleton]
      linarith
    · rw [quittingTwoCoordinateAverageSurplus]
      have hsum := reward_pairB_group_sum terminal
      simp [hAval, hBval] at hsum
      simp only [reward_singleton]
      linarith

/-- The actual pure profile in which precisely pair `A` quits immediately. -/
def purePairAProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot pairA)

theorem purePairAProfile_terminalPayoff :
    quittingTerminalPayoff reward purePairAProfile = ![2, 2, 1, 1] := by
  funext who
  unfold purePairAProfile
  rw [quittingTerminalPayoff_pureSetRoot]
  fin_cases who <;>
    norm_num +decide [quittingSetReward, reward, pairA, pairB, partner]

/-- No positive strict singleton-deficit parameter is valid: the pure `A`
profile has surplus `(1,1,0,0)`. -/
theorem not_hasQuittingActualStrictSingletonDeficit
    (gap : ℝ) (hgap : 0 < gap) :
    ¬ HasQuittingActualStrictSingletonDeficit reward gap := by
  intro hdeficit
  obtain ⟨who, hwho⟩ := hdeficit purePairAProfile
  have hpayoff := congrFun purePairAProfile_terminalPayoff who
  fin_cases who <;> norm_num [reward_singleton] at hpayoff hwho ⊢ <;> linarith

theorem not_exists_positive_actualStrictSingletonDeficit :
    ¬ ∃ gap : ℝ, 0 < gap ∧
      HasQuittingActualStrictSingletonDeficit reward gap := by
  rintro ⟨gap, hgap, hdeficit⟩
  exact not_hasQuittingActualStrictSingletonDeficit gap hgap hdeficit

/-- Pair `A` itself is a sure exit set, so this boundary table still has an
easy exact terminal Nash equilibrium. -/
theorem purePairAProfile_isExactTerminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 purePairAProfile := by
  unfold purePairAProfile
  apply (isεAsymptoticNash_pureSetRoot_iff reward pairA 0).mpr
  intro who
  fin_cases who <;>
    norm_num +decide [quittingSetReward, reward, pairA, pairB, partner]

/-- At the pure `A` root, each active player's own-singleton Quit premium is
exactly one. -/
theorem purePairA_active_quitPremium
    (who : Fin 4) (hwho : who ∈ pairA) :
    quittingRootQuitPayoff reward 0 (quittingPureSetRoot pairA) who -
        reward (quittingSingletonTerminal who) who = 1 := by
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases who <;>
    simp_all +decide [quittingSetReward, reward] <;> norm_num

/-- The correlated half-`A`, half-`B` reward lottery has surplus one half in
every coordinate.  This is a convex-hull point, not an actual-profile claim. -/
theorem correlatedPairReward_surplus (who : Fin 4) :
    (reward pairATerminal who + reward pairBTerminal who) / 2 -
        reward (quittingSingletonTerminal who) who = 1 / 2 := by
  fin_cases who <;> norm_num +decide [reward, pairATerminal, pairBTerminal,
    pairA, pairB, partner, quittingSingletonTerminal]

/-- No nonzero nonnegative fixed weight can put both pair rows below the
weighted own-singleton benchmark. -/
theorem no_nonzero_nonnegativeWeight_bounds_all_terminalRows
    (weight : Fin 4 → ℝ) (hnonnegative : ∀ who, 0 ≤ weight who)
    (hpositive : ∃ who, 0 < weight who) :
    ¬ ∀ terminal : {S : Finset (Fin 4) // S.Nonempty},
      ∑ who, weight who * reward terminal who ≤
        ∑ who, weight who *
          reward (quittingSingletonTerminal who) who := by
  intro hbound
  have hA := hbound pairATerminal
  have hB := hbound pairBTerminal
  simp_rw [reward_singleton, mul_one] at hA hB
  obtain ⟨positiveWho, hpositiveWho⟩ := hpositive
  have hsumPositive : 0 < ∑ who, weight who := by
    apply Finset.sum_pos'
    · intro who _
      exact hnonnegative who
    · exact ⟨positiveWho, Finset.mem_univ positiveWho, hpositiveWho⟩
  simp only [Fin.sum_univ_four] at hA hB hsumPositive
  norm_num +decide [reward, pairATerminal, pairBTerminal, pairA, pairB] at hA hB
  linarith

/-- The actual pure-`A` product root refutes the product-low quitting-premium
condition. -/
theorem not_hasProductLowQuittingPremium :
    ¬ HasProductLowQuittingPremium reward := by
  intro hproductLow
  have habsorption : 0 < quittingRootAbsorptionMass (quittingPureSetRoot pairA) := by
    rw [quittingRootAbsorptionMass_pureSetRoot_of_nonempty (by simp [pairA])]
    norm_num
  obtain ⟨who, hactive, hlow⟩ :=
    hproductLow (quittingPureSetRoot pairA) habsorption
  have hwho : who ∈ pairA := by
    by_contra hnotMem
    simp [quittingPureSetRoot, quittingSetAction, hnotMem] at hactive
  have hpremium := purePairA_active_quitPremium who hwho
  linarith

end GameTheory.FiniteCalendarGroupExclusionBeyondDeficitBoundary
