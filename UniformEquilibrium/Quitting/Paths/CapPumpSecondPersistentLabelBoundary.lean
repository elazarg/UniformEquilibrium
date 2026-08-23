/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.CapPumpSecondPersistentLabel

/-!
# Sharp finite cap-pump boundary regressions

These are the exact rational `Fin 2` and `Fin 3` tests for the cap-pump
account.  They use literal quitting roots and zero terminal rewards.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped BigOperators Topology

namespace CapPumpSecondPersistentLabelBoundary

/-- The zero quitting reward used in both finite regressions. -/
def zeroReward {ι : Type} :
    {S : Finset ι // S.Nonempty} → Payoff ι := fun _ _ => 0

@[simp] theorem quittingRootAbsorbingContribution_zeroReward
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution zeroReward root who = 0 := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  rw [expect_eq_sum]
  apply Finset.sum_eq_zero
  intro action _
  by_cases hquit : (quittingQuitters action).Nonempty
  · simp [quittingRootPayoff, zeroReward, hquit]
  · simp [quittingRootPayoff, hquit]

@[simp] theorem quittingFixedOpponentsQuitValue_zeroReward
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingFixedOpponentsQuitValue zeroReward roots who time = 0 := by
  simp [quittingFixedOpponentsQuitValue]

@[simp] theorem quittingFixedOpponentsContinueReward_zeroReward
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingFixedOpponentsContinueReward zeroReward roots who time = 0 := by
  simp [quittingFixedOpponentsContinueReward]

/-- The exact fair Quit coin. -/
def halfCoin : PMF Bool :=
  quittingHazardCoin (1 / 2 : ℝ) (by norm_num) (by norm_num)

/-! ## Sharp `Fin 2` one-label obstruction -/

/-- Player `0` uses the fair Quit coin and player `1` always Continues. -/
def finTwoOneLabelRoots (_time : ℕ) (who : Fin 2) : PMF Bool :=
  if who = 0 then halfCoin else PMF.pure false

@[simp] theorem finTwo_marginal_zero (time : ℕ) :
    quittingMarginalQuitHazard finTwoOneLabelRoots (0 : Fin 2) time = 1 / 2 := by
  simp [quittingMarginalQuitHazard, finTwoOneLabelRoots, halfCoin]

@[simp] theorem finTwo_marginal_one (time : ℕ) :
    quittingMarginalQuitHazard finTwoOneLabelRoots (1 : Fin 2) time = 0 := by
  simp [quittingMarginalQuitHazard, finTwoOneLabelRoots]

@[simp] theorem finTwo_opponentMass_owner (time : ℕ) :
    quittingFixedOpponentsContinueMass finTwoOneLabelRoots (1 : Fin 2) time =
      1 / 2 := by
  rw [quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [finTwoOneLabelRoots, halfCoin, Fin.prod_univ_two]
  norm_num

@[simp] theorem finTwo_opponentMass_mover (time : ℕ) :
    quittingFixedOpponentsContinueMass finTwoOneLabelRoots (0 : Fin 2) time =
      1 := by
  rw [quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [finTwoOneLabelRoots, Fin.prod_univ_two]

/-- The one-row cap table with source `1/2` and donated endpoint `1`. -/
def finTwoPump : QuittingBoundedCapPump
    (zeroReward (ι := Fin 2)) finTwoOneLabelRoots (1 : Fin 2) 1 0 where
  length := fun _ => 1
  length_pos := by simp
  cap := fun _ offset => if offset = 0 then 1 / 2 else 1
  K_nonneg := by norm_num
  M_nonneg := by norm_num
  cap_bound := by
    intro block offset hoffset
    interval_cases offset <;> norm_num
  reward_bound := by simp [zeroReward]
  cap_recursion := by
    intro block offset hoffset
    have hoffsetZero : offset = 0 := by omega
    subst offset
    simp

@[simp] theorem finTwo_favorableDrop (block : ℕ) :
    finTwoPump.favorableDrop block = 1 / 2 := by
  simp [QuittingBoundedCapPump.favorableDrop, finTwoPump]
  norm_num

@[simp] theorem finTwo_reverseRise (block : ℕ) :
    finTwoPump.reverseRise block = 0 := by
  simp [QuittingBoundedCapPump.reverseRise, finTwoPump]
  norm_num

@[simp] theorem finTwo_knownMoverAccount (blocks : ℕ) :
    finTwoPump.knownMoverAccount (0 : Fin 2) blocks = blocks / 2 := by
  simp [QuittingBoundedCapPump.knownMoverAccount, consecutiveBlockSum,
    finTwoPump]
  ring

/-- With the minimal bounds, subtracting the sole mover leaves exactly the
constant boundary term `-2`; it is not positive excess. -/
@[simp] theorem finTwo_knownMoverExcess (blocks : ℕ) :
    finTwoPump.knownMoverExcess (0 : Fin 2) blocks = -2 := by
  simp [QuittingBoundedCapPump.knownMoverExcess]
  ring

theorem finTwo_favorable_not_summable :
    ¬Summable finTwoPump.favorableDrop := by
  rw [show finTwoPump.favorableDrop = fun _ => (1 / 2 : ℝ) from
    funext finTwo_favorableDrop]
  exact (not_congr (summable_const_iff (β := ℕ) (1 / 2 : ℝ))).mpr
    (by norm_num)

theorem finTwo_reverse_summable :
    Summable finTwoPump.reverseRise := by
  rw [show finTwoPump.reverseRise = fun _ => (0 : ℝ) from
    funext finTwo_reverseRise]
  exact summable_zero

theorem finTwo_mover_persistent :
    ¬Summable
      (quittingMarginalQuitHazard finTwoOneLabelRoots (0 : Fin 2)) := by
  rw [show quittingMarginalQuitHazard finTwoOneLabelRoots (0 : Fin 2) =
      fun _ => (1 / 2 : ℝ) from funext finTwo_marginal_zero]
  exact (not_congr (summable_const_iff (β := ℕ) (1 / 2 : ℝ))).mpr
    (by norm_num)

theorem finTwo_knownMoverExcess_bddAbove :
    BddAbove (Set.range (finTwoPump.knownMoverExcess (0 : Fin 2))) := by
  rw [bddAbove_def]
  refine ⟨-2, ?_⟩
  rintro value ⟨blocks, rfl⟩
  rw [finTwo_knownMoverExcess]

/-- The fair mover is the only persistent label in the two-player test. -/
theorem finTwo_not_twoPersistent :
    ¬HasTwoPersistentQuittingMarginals finTwoOneLabelRoots := by
  have hone : Summable
      (quittingMarginalQuitHazard finTwoOneLabelRoots (1 : Fin 2)) := by
    rw [show quittingMarginalQuitHazard finTwoOneLabelRoots (1 : Fin 2) =
      fun _ => (0 : ℝ) from funext finTwo_marginal_one]
    exact summable_zero
  rintro ⟨first, second, hne, hfirst, hsecond⟩
  fin_cases first <;> fin_cases second
  · exact hne rfl
  · exact hsecond hone
  · exact hfirst hone
  · exact hne rfl

/-- After deleting the sole mover, survival stays identically one. -/
@[simp] theorem finTwo_moverDeletedSurvival (start fuel : ℕ) :
    quittingOpponentSurvivalWeight finTwoOneLabelRoots (0 : Fin 2) start fuel =
      1 := by
  simp [quittingOpponentSurvivalWeight]

/-! ## `Fin 3` positive-excess test -/

/-- Players `0` and `2` use fair Quit coins; owner `1` always Continues. -/
def finThreeTwoLabelRoots (_time : ℕ) (who : Fin 3) : PMF Bool :=
  if who = 1 then PMF.pure false else halfCoin

@[simp] theorem finThree_marginal_zero (time : ℕ) :
    quittingMarginalQuitHazard finThreeTwoLabelRoots (0 : Fin 3) time =
      1 / 2 := by
  simp [quittingMarginalQuitHazard, finThreeTwoLabelRoots, halfCoin]

@[simp] theorem finThree_marginal_two (time : ℕ) :
    quittingMarginalQuitHazard finThreeTwoLabelRoots (2 : Fin 3) time =
      1 / 2 := by
  simp [quittingMarginalQuitHazard, finThreeTwoLabelRoots, halfCoin]

@[simp] theorem finThree_opponentMass_owner (time : ℕ) :
    quittingFixedOpponentsContinueMass finThreeTwoLabelRoots (1 : Fin 3) time =
      1 / 4 := by
  rw [quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [finThreeTwoLabelRoots, halfCoin, Fin.prod_univ_succ]
  norm_num

/-- The one-row cap table with source `1/4` and donated endpoint `1`. -/
def finThreePump : QuittingBoundedCapPump
    (zeroReward (ι := Fin 3)) finThreeTwoLabelRoots (1 : Fin 3) 1 0 where
  length := fun _ => 1
  length_pos := by simp
  cap := fun _ offset => if offset = 0 then 1 / 4 else 1
  K_nonneg := by norm_num
  M_nonneg := by norm_num
  cap_bound := by
    intro block offset hoffset
    interval_cases offset <;> norm_num
  reward_bound := by simp [zeroReward]
  cap_recursion := by
    intro block offset hoffset
    have hoffsetZero : offset = 0 := by omega
    subst offset
    simp

@[simp] theorem finThree_favorableDrop (block : ℕ) :
    finThreePump.favorableDrop block = 3 / 4 := by
  simp [QuittingBoundedCapPump.favorableDrop, finThreePump]
  norm_num

@[simp] theorem finThree_reverseRise (block : ℕ) :
    finThreePump.reverseRise block = 0 := by
  simp [QuittingBoundedCapPump.reverseRise, finThreePump]
  norm_num

@[simp] theorem finThree_knownMoverAccount (blocks : ℕ) :
    finThreePump.knownMoverAccount (0 : Fin 3) blocks = blocks / 2 := by
  simp [QuittingBoundedCapPump.knownMoverAccount, consecutiveBlockSum,
    finThreePump]
  ring

/-- The mover-subtracted excess grows by the positive amount `1/4` per
block, apart from the fixed endpoint charge. -/
@[simp] theorem finThree_knownMoverExcess (blocks : ℕ) :
    finThreePump.knownMoverExcess (0 : Fin 3) blocks = blocks / 4 - 2 := by
  simp [QuittingBoundedCapPump.knownMoverExcess]
  ring

theorem finThree_mover_persistent :
    ¬Summable
      (quittingMarginalQuitHazard finThreeTwoLabelRoots (0 : Fin 3)) := by
  rw [show quittingMarginalQuitHazard finThreeTwoLabelRoots (0 : Fin 3) =
      fun _ => (1 / 2 : ℝ) from funext finThree_marginal_zero]
  exact (not_congr (summable_const_iff (β := ℕ) (1 / 2 : ℝ))).mpr
    (by norm_num)

theorem finThree_favorable_not_summable :
    ¬Summable finThreePump.favorableDrop := by
  rw [show finThreePump.favorableDrop = fun _ => (3 / 4 : ℝ) from
    funext finThree_favorableDrop]
  exact (not_congr (summable_const_iff (β := ℕ) (3 / 4 : ℝ))).mpr
    (by norm_num)

theorem finThree_reverse_summable :
    Summable finThreePump.reverseRise := by
  rw [show finThreePump.reverseRise = fun _ => (0 : ℝ) from
    funext finThree_reverseRise]
  exact summable_zero

theorem finThree_knownMoverExcess_not_bddAbove :
    ¬BddAbove (Set.range (finThreePump.knownMoverExcess (0 : Fin 3))) := by
  rw [not_bddAbove_iff]
  intro bound
  obtain ⟨blocks, hblocks⟩ := exists_nat_gt (4 * (bound + 2))
  refine ⟨blocks / 4 - 2, ⟨blocks, finThree_knownMoverExcess blocks⟩, ?_⟩
  linarith

/-- The positive-excess regression invokes the general extraction theorem on
the literal `Fin 3` roots. -/
theorem finThree_hasTwoPersistent :
    HasTwoPersistentQuittingMarginals finThreeTwoLabelRoots :=
  finThreePump.hasTwoPersistent_of_knownMoverExcess (by decide)
    finThree_mover_persistent finThree_knownMoverExcess_not_bddAbove

/-- Hence the exact three-player regression fills all joint and deleted
suffix-survival conclusions. -/
theorem finThree_survival :
    (∀ who start, Tendsto
      (quittingOpponentSurvivalWeight finThreeTwoLabelRoots who start)
        atTop (nhds 0)) ∧
    (∀ start, Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass
          (finThreeTwoLabelRoots time)) start) atTop (nhds 0)) :=
  finThree_hasTwoPersistent.survival (by decide)

end CapPumpSecondPersistentLabelBoundary

end GameTheory
