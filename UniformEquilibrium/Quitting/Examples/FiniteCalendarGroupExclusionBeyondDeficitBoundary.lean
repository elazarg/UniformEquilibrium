import UniformEquilibrium.Quitting.Paths.BehaviorFirstStoppingPairLaw
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# A four-player group-exclusion boundary beyond strict deficit

Two disjoint pairs receive elevated rewards when they quit together.  The
actual first-stopping pair square-root law selects, profile by profile, one
of the two pair-average surplus inequalities.  This gives group exclusion
with cap `1 / 2`, while the pure first-pair exit refutes every positive
strict singleton deficit.
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

/-- Actual mass of pair `A` as the finite first-quitter coalition. -/
def pairAMass (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  quittingBehaviorExactFiniteFirstCoalitionMass profile pairATerminal

/-- Actual mass of pair `B` as the finite first-quitter coalition. -/
def pairBMass (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  quittingBehaviorExactFiniteFirstCoalitionMass profile pairBTerminal

/-- Actual probability of Never. -/
def neverMass (profile : (quittingGame reward).BehaviorProfile) : ℝ :=
  quittingTerminalOutcomeMass reward profile none

theorem pairAMass_nonneg (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ pairAMass profile :=
  quittingBehaviorExactFiniteFirstCoalitionMass_nonneg profile pairATerminal

theorem pairBMass_nonneg (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ pairBMass profile :=
  quittingBehaviorExactFiniteFirstCoalitionMass_nonneg profile pairBTerminal

theorem neverMass_nonneg (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ neverMass profile :=
  (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 none

/-- The existing actual-profile pair law, specialized to the two disjoint
pairs of the example. -/
theorem sqrt_pairAMass_add_sqrt_pairBMass_le_one
    (profile : (quittingGame reward).BehaviorProfile) :
    Real.sqrt (pairAMass profile) + Real.sqrt (pairBMass profile) ≤ 1 := by
  exact quittingBehaviorFirstStoppingPairMass_sqrt_add_sqrt_le_one
    profile pairATerminal pairBTerminal (by norm_num [pairATerminal, pairA])
      (by norm_num +decide [pairBTerminal, pairB])
      (by norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB])

private theorem pairATerminal_ne_pairBTerminal : pairATerminal ≠ pairBTerminal := by
  norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB]

private theorem pairA_outcome_reward_sum (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeReward reward outcome 0 +
        quittingTerminalOutcomeReward reward outcome 1 =
      if outcome = some pairATerminal then 4
      else if outcome = some pairBTerminal then 2
      else if outcome = none then 0 else 1 := by
  cases outcome with
  | none => simp [quittingTerminalOutcomeReward]
  | some terminal =>
    simp only [quittingTerminalOutcomeReward]
    rw [reward_pairA_group_sum]
    by_cases hA : terminal = pairATerminal
    · subst terminal
      norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB]
    by_cases hB : terminal = pairBTerminal
    · subst terminal
      norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB]
    have hAval : terminal.1 ≠ pairA := by
      intro h
      apply hA
      exact Subtype.ext h
    have hBval : terminal.1 ≠ pairB := by
      intro h
      apply hB
      exact Subtype.ext h
    simp [hA, hB, hAval, hBval]

private theorem pairB_outcome_reward_sum (outcome : QuittingTerminalOutcome (Fin 4)) :
    quittingTerminalOutcomeReward reward outcome 2 +
        quittingTerminalOutcomeReward reward outcome 3 =
      if outcome = some pairATerminal then 2
      else if outcome = some pairBTerminal then 4
      else if outcome = none then 0 else 1 := by
  cases outcome with
  | none => simp [quittingTerminalOutcomeReward]
  | some terminal =>
    simp only [quittingTerminalOutcomeReward]
    rw [reward_pairB_group_sum]
    by_cases hA : terminal = pairATerminal
    · subst terminal
      norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB]
    by_cases hB : terminal = pairBTerminal
    · subst terminal
      norm_num +decide [pairATerminal, pairBTerminal, pairA, pairB]
    have hAval : terminal.1 ≠ pairA := by
      intro h
      apply hA
      exact Subtype.ext h
    have hBval : terminal.1 ≠ pairB := by
      intro h
      apply hB
      exact Subtype.ext h
    simp [hA, hB, hAval, hBval]

private theorem payoff_sum_of_outcome_reward_sum
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : Fin 4)
    (primary secondary : {S : Finset (Fin 4) // S.Nonempty})
    (hne : primary ≠ secondary)
    (hreward : ∀ outcome : QuittingTerminalOutcome (Fin 4),
      quittingTerminalOutcomeReward reward outcome first +
          quittingTerminalOutcomeReward reward outcome second =
        if outcome = some primary then 4
        else if outcome = some secondary then 2
        else if outcome = none then 0 else 1) :
    quittingTerminalPayoff reward profile first +
        quittingTerminalPayoff reward profile second =
      1 + 3 * quittingTerminalOutcomeMass reward profile (some primary) +
        quittingTerminalOutcomeMass reward profile (some secondary) -
          quittingTerminalOutcomeMass reward profile none := by
  let mass := quittingTerminalOutcomeMass reward profile
  have hmoment := quittingTerminalRewardMoment_outcomeMass reward profile
  have htotal := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
  have hcoordinateFirst := congrFun hmoment first
  have hcoordinateSecond := congrFun hmoment second
  rw [← hcoordinateFirst, ← hcoordinateSecond]
  simp only [quittingTerminalRewardMoment, ← Finset.sum_add_distrib, ← mul_add]
  simp_rw [hreward]
  change (∑ outcome, mass outcome *
      (if outcome = some primary then 4
       else if outcome = some secondary then 2
       else if outcome = none then 0 else 1)) = _
  change (∑ outcome, mass outcome) = 1 at htotal
  dsimp only [mass] at htotal ⊢
  classical
  calc
    _ = ∑ outcome, (quittingTerminalOutcomeMass reward profile outcome +
          (if outcome = some primary then
            3 * quittingTerminalOutcomeMass reward profile outcome else 0) +
          (if outcome = some secondary then
            quittingTerminalOutcomeMass reward profile outcome else 0) -
          (if outcome = none then
            quittingTerminalOutcomeMass reward profile outcome else 0)) := by
      apply Finset.sum_congr rfl
      intro outcome _
      split_ifs with hA hB hnone
      all_goals try { subst outcome; simp_all }
      all_goals ring
    _ = 1 + 3 * quittingTerminalOutcomeMass reward profile (some primary) +
          quittingTerminalOutcomeMass reward profile (some secondary) -
            quittingTerminalOutcomeMass reward profile none := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [htotal]

private theorem pairA_payoff_sum
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile 0 +
        quittingTerminalPayoff reward profile 1 =
      1 + 3 * pairAMass profile + pairBMass profile - neverMass profile := by
  rw [pairAMass, pairBMass, neverMass,
    quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass,
    quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass]
  exact payoff_sum_of_outcome_reward_sum profile 0 1 pairATerminal pairBTerminal
    pairATerminal_ne_pairBTerminal pairA_outcome_reward_sum

private theorem pairB_payoff_sum
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile 2 +
        quittingTerminalPayoff reward profile 3 =
      1 + 3 * pairBMass profile + pairAMass profile - neverMass profile := by
  rw [pairAMass, pairBMass, neverMass,
    quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass,
    quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass]
  apply payoff_sum_of_outcome_reward_sum profile 2 3 pairBTerminal pairATerminal
    pairATerminal_ne_pairBTerminal.symm
  intro outcome
  rw [pairB_outcome_reward_sum]
  by_cases hB : outcome = some pairBTerminal
  · subst outcome
    have hne : pairBTerminal ≠ pairATerminal := pairATerminal_ne_pairBTerminal.symm
    simp [hne]
  by_cases hA : outcome = some pairATerminal
  · subst outcome
    simp [pairATerminal_ne_pairBTerminal]
  simp [hA, hB]

private theorem three_mul_add_le_one_of_sqrt_add_sqrt_le_one
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsqrt : Real.sqrt x + Real.sqrt y ≤ 1) (hxy : x ≤ y) :
    3 * x + y ≤ 1 := by
  have hsqrtX0 := Real.sqrt_nonneg x
  have hsqrtY0 := Real.sqrt_nonneg y
  have hsqrtXsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsqrtYsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hsqrtXY : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hsqrtXhalf : Real.sqrt x ≤ (1 : ℝ) / 2 := by
    linarith
  have hcomplement : Real.sqrt y ≤ 1 - Real.sqrt x := by
    linarith
  have hcomplement0 : 0 ≤ 1 - Real.sqrt x := by
    linarith
  have hproduct := mul_nonneg (sub_nonneg.mpr hcomplement)
    (add_nonneg hcomplement0 hsqrtY0)
  have hquadratic := mul_nonneg hsqrtX0 (sub_nonneg.mpr (by linarith :
    2 * Real.sqrt x ≤ 1))
  nlinarith

def pairAWeight : Fin 4 → ℝ := ![1 / 2, 1 / 2, 0, 0]

def pairBWeight : Fin 4 → ℝ := ![0, 0, 1 / 2, 1 / 2]

private theorem pairAWeight_nonneg (who : Fin 4) : 0 ≤ pairAWeight who := by
  fin_cases who <;> norm_num [pairAWeight]

private theorem pairBWeight_nonneg (who : Fin 4) : 0 ≤ pairBWeight who := by
  fin_cases who <;> norm_num [pairBWeight]

private theorem sum_pairAWeight : ∑ who, pairAWeight who = 1 := by
  norm_num [pairAWeight, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three]

private theorem sum_pairBWeight : ∑ who, pairBWeight who = 1 := by
  norm_num [pairBWeight, Fin.sum_univ_four, Matrix.cons_val_two,
    Matrix.cons_val_three]

private theorem pairAWeight_le_half (who : Fin 4) :
    pairAWeight who ≤ (1 : ℝ) / 2 := by
  fin_cases who <;> norm_num [pairAWeight]

private theorem pairBWeight_le_half (who : Fin 4) :
    pairBWeight who ≤ (1 : ℝ) / 2 := by
  fin_cases who <;> norm_num [pairBWeight]

private theorem pairA_weightedSurplus
    (profile : (quittingGame reward).BehaviorProfile) :
    ∑ who, pairAWeight who *
      (quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who) =
      (3 * pairAMass profile + pairBMass profile - 1 - neverMass profile) / 2 := by
  rw [show (∑ who, pairAWeight who *
      (quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who)) =
      ((quittingTerminalPayoff reward profile 0 - 1) +
        (quittingTerminalPayoff reward profile 1 - 1)) / 2 by
      simp [pairAWeight, Fin.sum_univ_four]
      ring]
  rw [show ((quittingTerminalPayoff reward profile 0 - 1) +
      (quittingTerminalPayoff reward profile 1 - 1)) / 2 =
      ((quittingTerminalPayoff reward profile 0 +
        quittingTerminalPayoff reward profile 1) - 2) / 2 by ring]
  rw [pairA_payoff_sum]
  ring

private theorem pairB_weightedSurplus
    (profile : (quittingGame reward).BehaviorProfile) :
    ∑ who, pairBWeight who *
      (quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who) =
      (3 * pairBMass profile + pairAMass profile - 1 - neverMass profile) / 2 := by
  rw [show (∑ who, pairBWeight who *
      (quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who)) =
      ((quittingTerminalPayoff reward profile 2 - 1) +
        (quittingTerminalPayoff reward profile 3 - 1)) / 2 by
      simp [pairBWeight, Fin.sum_univ_four]
      ring]
  rw [show ((quittingTerminalPayoff reward profile 2 - 1) +
      (quittingTerminalPayoff reward profile 3 - 1)) / 2 =
      ((quittingTerminalPayoff reward profile 2 +
        quittingTerminalPayoff reward profile 3) - 2) / 2 by ring]
  rw [pairB_payoff_sum]
  ring

/-- Every actual behavioral profile admits a half-capped group-exclusion
weight.  The selected pair may depend on the profile, but the cap does not. -/
theorem hasQuittingActualNonconcentratedGroupExclusion_half :
    HasQuittingActualNonconcentratedGroupExclusion reward ((1 : ℝ) / 2) := by
  intro profile
  have hsqrt := sqrt_pairAMass_add_sqrt_pairBMass_le_one profile
  by_cases horder : pairAMass profile ≤ pairBMass profile
  · refine ⟨pairAWeight, pairAWeight_nonneg, sum_pairAWeight,
      pairAWeight_le_half, ?_⟩
    rw [pairA_weightedSurplus]
    have hbound := three_mul_add_le_one_of_sqrt_add_sqrt_le_one
      (pairAMass_nonneg profile) (pairBMass_nonneg profile) hsqrt horder
    have hnever := neverMass_nonneg profile
    linarith
  · refine ⟨pairBWeight, pairBWeight_nonneg, sum_pairBWeight,
      pairBWeight_le_half, ?_⟩
    rw [pairB_weightedSurplus]
    have hbound := three_mul_add_le_one_of_sqrt_add_sqrt_le_one
      (pairBMass_nonneg profile) (pairAMass_nonneg profile) (by linarith)
        (le_of_not_ge horder)
    have hnever := neverMass_nonneg profile
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
exactly one.  Thus this root does not pass the own-singleton product-low
endpoint test. -/
theorem purePairA_active_quitPremium
    (who : Fin 4) (hwho : who ∈ pairA) :
    quittingRootQuitPayoff reward 0 (quittingPureSetRoot pairA) who -
        reward (quittingSingletonTerminal who) who = 1 := by
  rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
  fin_cases who <;>
    simp_all +decide [quittingSetReward, reward] <;> norm_num

/-- The correlated half-`A`, half-`B` reward lottery has surplus one half in
every coordinate.  This is a convex-hull point, not a claim that the lottery
is generated by an actual behavioral profile. -/
theorem correlatedPairReward_surplus (who : Fin 4) :
    (reward pairATerminal who + reward pairBTerminal who) / 2 -
        reward (quittingSingletonTerminal who) who = 1 / 2 := by
  fin_cases who <;> norm_num +decide [reward, pairATerminal, pairBTerminal,
    pairA, pairB, partner, quittingSingletonTerminal]

/-- Consequently no nonzero nonnegative fixed weight can put both pair rows
below the weighted own-singleton benchmark.  This is the literal failure of
the fixed nonnegative-weight reward-convex-hull criterion. -/
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
condition: it absorbs surely and every active coordinate has premium one. -/
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
