/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.BonferroniProductBounds
import MathUE.SurvivalProductComparison
import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalDebtShadowing
import UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy

/-!
# Persistent deleted clocks and two labelled marginal streams

For a finite player set with at least two elements, every one-player-deleted
clock diverges exactly when two distinct marginal Quit-hazard streams diverge.
This file also transports the conclusion through consecutive finite blocks
under summable absolute marginal error or fixed positive-fraction retention.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The displayed Quit probability of one player in one product root. -/
def quittingMarginalQuitHazard
    (roots : ℕ → ι → PMF Bool) (owner : ι) (time : ℕ) : ℝ :=
  (roots time owner true).toReal

omit [Fintype ι] [DecidableEq ι] in
theorem quittingMarginalQuitHazard_nonneg
    (roots : ℕ → ι → PMF Bool) (owner : ι) (time : ℕ) :
    0 ≤ quittingMarginalQuitHazard roots owner time :=
  ENNReal.toReal_nonneg

omit [Fintype ι] [DecidableEq ι] in
theorem quittingMarginalQuitHazard_le_one
    (roots : ℕ → ι → PMF Bool) (owner : ι) (time : ℕ) :
    quittingMarginalQuitHazard roots owner time ≤ 1 := by
  unfold quittingMarginalQuitHazard
  rw [← ENNReal.toReal_one,
    ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by simp)]
  exact (roots time owner).coe_le_one true

/-- Event inclusion: an opponent's marginal Quit event is contained in the
deleted player's opponent-absorption event. -/
theorem quittingMarginalQuitHazard_le_opponentClockCharge
    (roots : ℕ → ι → PMF Bool) {who owner : ι} (hne : owner ≠ who)
    (time : ℕ) :
    quittingMarginalQuitHazard roots owner time ≤
      quittingOpponentClockCharge roots who time := by
  rw [quittingOpponentClockCharge_eq_one_sub]
  have hcontinue := quittingRootOpponentContinueMass_le_continueProbability_of_ne
    (roots time) hne
  change quittingFixedOpponentsContinueMass roots who time ≤
    (roots time owner false).toReal at hcontinue
  have hsum := pmf_toReal_sum_one (roots time owner)
  rw [Fintype.sum_bool] at hsum
  unfold quittingMarginalQuitHazard
  linarith

/-- Finite union bound for the deleted opponent charge. -/
theorem quittingOpponentClockCharge_le_sum_marginalQuitHazard
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingOpponentClockCharge roots who time ≤
      ∑ owner ∈ Finset.univ.erase who,
        quittingMarginalQuitHazard roots owner time := by
  rw [quittingOpponentClockCharge,
    quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  exact Math.one_sub_prod_one_sub_le_sum
    (fun owner => quittingMarginalQuitHazard roots owner time)
    (Finset.univ.erase who)
    (fun owner _ => quittingMarginalQuitHazard_nonneg roots owner time)
    (fun owner _ => quittingMarginalQuitHazard_le_one roots owner time)

/-- A deleted opponent charge is summable exactly when every non-deleted
marginal Quit stream is summable. -/
theorem summable_quittingOpponentClockCharge_iff
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    Summable (quittingOpponentClockCharge roots who) ↔
      ∀ owner, owner ≠ who →
        Summable (quittingMarginalQuitHazard roots owner) := by
  constructor
  · intro hcharge owner hne
    exact hcharge.of_nonneg_of_le
      (quittingMarginalQuitHazard_nonneg roots owner)
      (quittingMarginalQuitHazard_le_opponentClockCharge roots hne)
  · intro hmarginal
    have hsum : Summable (fun time =>
        ∑ owner ∈ Finset.univ.erase who,
          quittingMarginalQuitHazard roots owner time) := by
      exact summable_sum fun owner howner =>
        hmarginal owner (Finset.ne_of_mem_erase howner)
    exact hsum.of_nonneg_of_le
      (quittingOpponentClockCharge_nonneg roots who)
      (quittingOpponentClockCharge_le_sum_marginalQuitHazard roots who)

/-- Two distinct labels carry divergent marginal Quit-hazard streams. -/
def HasTwoPersistentQuittingMarginals
    (roots : ℕ → ι → PMF Bool) : Prop :=
  ∃ first second, first ≠ second ∧
    ¬Summable (quittingMarginalQuitHazard roots first) ∧
    ¬Summable (quittingMarginalQuitHazard roots second)

/-- Exact finite-player additive-clock reduction. -/
theorem hasTwoPersistentQuittingMarginals_iff_all_opponentClocks
    (roots : ℕ → ι → PMF Bool) (hcard : 2 ≤ Fintype.card ι) :
    HasTwoPersistentQuittingMarginals roots ↔
      ∀ who, ¬Summable (quittingOpponentClockCharge roots who) := by
  classical
  constructor
  · rintro ⟨first, second, hne, hfirst, hsecond⟩ who hcharge
    have hall := (summable_quittingOpponentClockCharge_iff roots who).mp hcharge
    by_cases hwho : first = who
    · exact hsecond (hall second (by simpa [hwho] using hne.symm))
    · exact hfirst (hall first hwho)
  · intro hall
    letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    let first : ι := Classical.choice inferInstance
    have hexistsSecond : ∃ second, second ≠ first ∧
        ¬Summable (quittingMarginalQuitHazard roots second) := by
      by_contra hnot
      push Not at hnot
      exact hall first ((summable_quittingOpponentClockCharge_iff roots first).mpr
        fun owner howner => hnot owner howner)
    obtain ⟨second, hsecondFirst, hsecond⟩ := hexistsSecond
    have hexistsThird : ∃ third, third ≠ second ∧
        ¬Summable (quittingMarginalQuitHazard roots third) := by
      by_contra hnot
      push Not at hnot
      exact hall second ((summable_quittingOpponentClockCharge_iff roots second).mpr
        fun owner howner => hnot owner howner)
    obtain ⟨third, hthirdSecond, hthird⟩ := hexistsThird
    exact ⟨second, third, hthirdSecond.symm, hsecond, hthird⟩

private theorem not_summable_nat_add_of_not_summable
    (f : ℕ → ℝ) (start : ℕ) (hdiverges : ¬Summable f) :
    ¬Summable (fun offset => f (start + offset)) := by
  intro hsuffix
  have hshift : Summable (fun offset => f (offset + start)) := by
    simpa [Nat.add_comm] using hsuffix
  exact hdiverges ((summable_nat_add_iff start).1 hshift)

/-- Exact additive/multiplicative deleted-clock equivalence, including every
suffix and isolated zero Continue factors. -/
theorem all_opponentClocks_iff_all_suffix_survival_zero
    (roots : ℕ → ι → PMF Bool) :
    (∀ who, ¬Summable (quittingOpponentClockCharge roots who)) ↔
      ∀ who start, Tendsto
        (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0) := by
  constructor
  · intro hall who start
    exact tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge
      roots who start
      (not_summable_nat_add_of_not_summable
        (quittingOpponentClockCharge roots who) start (hall who))
  · intro hsurvival who hsummable
    obtain ⟨start, hhalf⟩ :=
      exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable
        roots who hsummable
    have hlimit : (1 / 2 : ℝ) ≤ 0 :=
      ge_of_tendsto' (hsurvival who start) hhalf
    norm_num at hlimit

/-- The exact two-label characterization in its suffix-survival form. -/
theorem hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero
    (roots : ℕ → ι → PMF Bool) (hcard : 2 ≤ Fintype.card ι) :
    HasTwoPersistentQuittingMarginals roots ↔
      ∀ who start, Tendsto
        (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0) :=
  (hasTwoPersistentQuittingMarginals_iff_all_opponentClocks roots hcard).trans
    (all_opponentClocks_iff_all_suffix_survival_zero roots)

/-- Any vanishing deleted-player survival bounds the joint survival from
above, so the full family of deleted limits makes joint survival redundant. -/
theorem tendsto_jointSurvival_zero_of_opponentSurvival_zero
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (hopponent : Tendsto
      (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)) :
    Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start)
      atTop (nhds 0) := by
  have hopponent' : Tendsto
      (Math.survivalProduct
        (quittingFixedOpponentsContinueMass roots who) start)
      atTop (nhds 0) := by
    have hfun : Math.survivalProduct
        (quittingFixedOpponentsContinueMass roots who) start =
        quittingOpponentSurvivalWeight roots who start := by
      funext fuel
      rfl
    rw [hfun]
    exact hopponent
  exact squeeze_zero
    (fun fuel => Math.survivalProduct_nonneg _
      (fun time => quittingStationaryContinueMass_nonneg (roots time)) start fuel)
    (fun fuel => Math.survivalProduct_le_survivalProduct _ _
      (fun time => quittingStationaryContinueMass_nonneg (roots time))
      (fun time => quittingStationaryContinueMass_le_update_pure_false
        (roots time) who) start fuel)
    hopponent'

/-- Two persistent labels imply both every deleted-player survival limit and
the joint-survival limit on every suffix. -/
theorem HasTwoPersistentQuittingMarginals.survival
    {roots : ℕ → ι → PMF Bool} (hcard : 2 ≤ Fintype.card ι)
    (hpersistent : HasTwoPersistentQuittingMarginals roots) :
    (∀ who start, Tendsto
      (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)) ∧
    (∀ start, Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start)
      atTop (nhds 0)) := by
  have hopponent :=
    (hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero
      roots hcard).mp hpersistent
  refine ⟨hopponent, ?_⟩
  intro start
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let who : ι := Classical.choice inferInstance
  exact tendsto_jointSurvival_zero_of_opponentSurvival_zero
    roots who start (hopponent who start)

/-- Exactly the two survival fields of the chronological debt-shadowing
certificate, split out without asserting any forcing or discrepancy field. -/
structure QuittingChronologicalDebtShadowingSurvivalFields
    (data : QuittingChronologicalDebtData ι) : Prop where
  joint_survival : ∀ start,
    Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (data.root time)) start)
      atTop (nhds 0)
  opponent_survival : ∀ who start,
    Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (data.root time) who)
        start) atTop (nhds 0)

/-- Direct chronological-data adapter for the two survival hypotheses only. -/
theorem QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent
    (data : QuittingChronologicalDebtData ι) (hcard : 2 ≤ Fintype.card ι)
    (hpersistent : HasTwoPersistentQuittingMarginals data.root) :
    QuittingChronologicalDebtShadowingSurvivalFields data := by
  obtain ⟨hopponent, hjoint⟩ := hpersistent.survival hcard
  refine ⟨hjoint, ?_⟩
  intro who start
  have hfun : Math.survivalProduct
      (fun time => quittingRootOpponentContinueMass (data.root time) who) start =
      quittingOpponentSurvivalWeight data.root who start := by
    funext fuel
    rfl
  rw [hfun]
  exact hopponent who start

/-! ## Consecutive finite-block transport -/

/-- Left endpoint of block `block` for a sequence of consecutive block
lengths. -/
def consecutiveBlockStart (length : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | block + 1 => consecutiveBlockStart length block + length block

/-- Sum of a scalar stream over one consecutive finite block. -/
def consecutiveBlockSum
    (length : ℕ → ℕ) (stream : ℕ → ℝ) (block : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range (length block),
    stream (consecutiveBlockStart length block + offset)

/-- The first `blocks` consecutive blocks are exactly the time prefix ending
at the next block boundary. -/
theorem sum_consecutiveBlockSum_eq_sum_range
    (length : ℕ → ℕ) (stream : ℕ → ℝ) (blocks : ℕ) :
    ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length stream block =
      ∑ time ∈ Finset.range (consecutiveBlockStart length blocks),
        stream time := by
  induction blocks with
  | zero => simp [consecutiveBlockStart]
  | succ blocks ih =>
      rw [Finset.sum_range_succ, ih]
      unfold consecutiveBlockSum
      rw [consecutiveBlockStart, Finset.sum_range_add]

private theorem consecutiveBlockSum_nonneg
    (length : ℕ → ℕ) (stream : ℕ → ℝ)
    (hstream : ∀ time, 0 ≤ stream time) (block : ℕ) :
    0 ≤ consecutiveBlockSum length stream block := by
  exact Finset.sum_nonneg fun offset _ =>
    hstream (consecutiveBlockStart length block + offset)

private theorem consecutiveBlockSum_nominal_le_actual_add_error
    (length : ℕ → ℕ) (actual nominal : ℕ → ℝ) (block : ℕ) :
    consecutiveBlockSum length nominal block ≤
      consecutiveBlockSum length actual block +
        consecutiveBlockSum length
          (fun time => |actual time - nominal time|) block := by
  unfold consecutiveBlockSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro offset _
  have habs : nominal (consecutiveBlockStart length block + offset) -
      actual (consecutiveBlockStart length block + offset) ≤
      |actual (consecutiveBlockStart length block + offset) -
        nominal (consecutiveBlockStart length block + offset)| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

/-- Divergence of nominal consecutive block mass survives a summable total
absolute marginal error. -/
theorem not_summable_of_consecutiveBlock_summable_absolute_error
    (length : ℕ → ℕ) (actual nominal : ℕ → ℝ)
    (hactual : ∀ time, 0 ≤ actual time)
    (hnominal : ∀ time, 0 ≤ nominal time)
    (hnominalBlocks : ¬Summable (consecutiveBlockSum length nominal))
    (herrorBlocks : Summable (consecutiveBlockSum length
      (fun time => |actual time - nominal time|))) :
    ¬Summable actual := by
  intro hactualSummable
  have hnominalTop : Tendsto (fun blocks =>
      ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length nominal block) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (consecutiveBlockSum_nonneg length nominal hnominal)).mp hnominalBlocks
  let bound : ℝ := (∑' time, actual time) +
    (∑' block, consecutiveBlockSum length
      (fun time => |actual time - nominal time|) block)
  have heventually : ∀ᶠ blocks : ℕ in atTop, bound <
      ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length nominal block :=
    hnominalTop.eventually (eventually_gt_atTop bound)
  obtain ⟨blocks, hlarge⟩ := heventually.exists
  have hcompare := Finset.sum_le_sum fun block (_ : block ∈ Finset.range blocks) =>
    consecutiveBlockSum_nominal_le_actual_add_error
      length actual nominal block
  rw [Finset.sum_add_distrib,
    sum_consecutiveBlockSum_eq_sum_range length actual blocks] at hcompare
  have hactualBound :
      (∑ time ∈ Finset.range (consecutiveBlockStart length blocks), actual time) ≤
        ∑' time, actual time :=
    hactualSummable.sum_le_tsum _ (fun time _ => hactual time)
  have herrorBound :
      (∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length
          (fun time => |actual time - nominal time|) block) ≤
        ∑' block, consecutiveBlockSum length
          (fun time => |actual time - nominal time|) block :=
    herrorBlocks.sum_le_tsum _ (fun block _ =>
      consecutiveBlockSum_nonneg length _ (fun time => abs_nonneg _) block)
  dsimp only [bound] at hlarge
  linarith

/-- Fixed positive-fraction retention also transports divergent nominal
block mass to the actual marginal stream. -/
theorem not_summable_of_consecutiveBlock_fixedFraction
    (length : ℕ → ℕ) (actual nominal : ℕ → ℝ) {theta : ℝ}
    (htheta : 0 < theta)
    (hactual : ∀ time, 0 ≤ actual time)
    (hnominal : ∀ time, 0 ≤ nominal time)
    (hretain : ∀ time, theta * nominal time ≤ actual time)
    (hnominalBlocks : ¬Summable (consecutiveBlockSum length nominal)) :
    ¬Summable actual := by
  intro hactualSummable
  have hnominalTop : Tendsto (fun blocks =>
      ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length nominal block) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (consecutiveBlockSum_nonneg length nominal hnominal)).mp hnominalBlocks
  let bound : ℝ := (∑' time, actual time) / theta
  have heventually : ∀ᶠ blocks : ℕ in atTop, bound <
      ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length nominal block :=
    hnominalTop.eventually (eventually_gt_atTop bound)
  obtain ⟨blocks, hlarge⟩ := heventually.exists
  have hcompare : theta *
      (∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length nominal block) ≤
      ∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length actual block := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro block _
    unfold consecutiveBlockSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun offset _ =>
      hretain (consecutiveBlockStart length block + offset)
  rw [sum_consecutiveBlockSum_eq_sum_range length actual blocks] at hcompare
  have hactualBound :
      (∑ time ∈ Finset.range (consecutiveBlockStart length blocks), actual time) ≤
        ∑' time, actual time :=
    hactualSummable.sum_le_tsum _ (fun time _ => hactual time)
  dsimp only [bound] at hlarge
  have hscaled : ∑' time, actual time < theta *
      (∑ block ∈ Finset.range blocks,
        consecutiveBlockSum length nominal block) := by
    simpa only [mul_comm] using (div_lt_iff₀ htheta).mp hlarge
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Two nominal divergent block streams remain two persistent actual root
marginals under summable absolute block errors. -/
theorem hasTwoPersistentQuittingMarginals_of_consecutiveBlock_summableError
    (roots : ℕ → ι → PMF Bool) (length : ℕ → ℕ)
    (nominal : ℕ → ι → ℝ) {first second : ι} (hne : first ≠ second)
    (hnominal : ∀ time owner, 0 ≤ nominal time owner)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second)))
    (hfirstError : Summable (consecutiveBlockSum length (fun time =>
      |quittingMarginalQuitHazard roots first time - nominal time first|)))
    (hsecondError : Summable (consecutiveBlockSum length (fun time =>
      |quittingMarginalQuitHazard roots second time - nominal time second|))) :
    HasTwoPersistentQuittingMarginals roots := by
  refine ⟨first, second, hne, ?_, ?_⟩
  · exact not_summable_of_consecutiveBlock_summable_absolute_error
      length (quittingMarginalQuitHazard roots first)
      (fun time => nominal time first)
      (quittingMarginalQuitHazard_nonneg roots first)
      (fun time => hnominal time first) hfirst hfirstError
  · exact not_summable_of_consecutiveBlock_summable_absolute_error
      length (quittingMarginalQuitHazard roots second)
      (fun time => nominal time second)
      (quittingMarginalQuitHazard_nonneg roots second)
      (fun time => hnominal time second) hsecond hsecondError

omit [Fintype ι] [DecidableEq ι] in
/-- Fixed positive-fraction retention of two divergent nominal block streams
also makes both actual root marginals persistent. -/
theorem hasTwoPersistentQuittingMarginals_of_consecutiveBlock_fixedFraction
    (roots : ℕ → ι → PMF Bool) (length : ℕ → ℕ)
    (nominal : ℕ → ι → ℝ) {first second : ι} (hne : first ≠ second)
    {theta : ℝ} (htheta : 0 < theta)
    (hnominal : ∀ time owner, 0 ≤ nominal time owner)
    (hfirstRetain : ∀ time,
      theta * nominal time first ≤ quittingMarginalQuitHazard roots first time)
    (hsecondRetain : ∀ time,
      theta * nominal time second ≤ quittingMarginalQuitHazard roots second time)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second))) :
    HasTwoPersistentQuittingMarginals roots := by
  refine ⟨first, second, hne, ?_, ?_⟩
  · exact not_summable_of_consecutiveBlock_fixedFraction
      length (quittingMarginalQuitHazard roots first)
      (fun time => nominal time first) htheta
      (quittingMarginalQuitHazard_nonneg roots first)
      (fun time => hnominal time first) hfirstRetain hfirst
  · exact not_summable_of_consecutiveBlock_fixedFraction
      length (quittingMarginalQuitHazard roots second)
      (fun time => nominal time second) htheta
      (quittingMarginalQuitHazard_nonneg roots second)
      (fun time => hnominal time second) hsecondRetain hsecond

/-- Robust consecutive-block transport all the way to every deleted and joint
suffix survival limit. -/
theorem survival_of_consecutiveBlock_summableError
    (roots : ℕ → ι → PMF Bool) (hcard : 2 ≤ Fintype.card ι)
    (length : ℕ → ℕ) (nominal : ℕ → ι → ℝ)
    {first second : ι} (hne : first ≠ second)
    (hnominal : ∀ time owner, 0 ≤ nominal time owner)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second)))
    (hfirstError : Summable (consecutiveBlockSum length (fun time =>
      |quittingMarginalQuitHazard roots first time - nominal time first|)))
    (hsecondError : Summable (consecutiveBlockSum length (fun time =>
      |quittingMarginalQuitHazard roots second time - nominal time second|))) :
    (∀ who start, Tendsto
      (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)) ∧
    (∀ start, Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start)
      atTop (nhds 0)) :=
  (hasTwoPersistentQuittingMarginals_of_consecutiveBlock_summableError
    roots length nominal hne hnominal hfirst hsecond hfirstError hsecondError)
    |>.survival hcard

/-- Fixed-fraction consecutive-block transport to every deleted and joint
suffix survival limit. -/
theorem survival_of_consecutiveBlock_fixedFraction
    (roots : ℕ → ι → PMF Bool) (hcard : 2 ≤ Fintype.card ι)
    (length : ℕ → ℕ) (nominal : ℕ → ι → ℝ)
    {first second : ι} (hne : first ≠ second) {theta : ℝ}
    (htheta : 0 < theta)
    (hnominal : ∀ time owner, 0 ≤ nominal time owner)
    (hfirstRetain : ∀ time,
      theta * nominal time first ≤ quittingMarginalQuitHazard roots first time)
    (hsecondRetain : ∀ time,
      theta * nominal time second ≤ quittingMarginalQuitHazard roots second time)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second))) :
    (∀ who start, Tendsto
      (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)) ∧
    (∀ start, Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start)
      atTop (nhds 0)) :=
  (hasTwoPersistentQuittingMarginals_of_consecutiveBlock_fixedFraction
    roots length nominal hne htheta hnominal hfirstRetain hsecondRetain
      hfirst hsecond)
    |>.survival hcard

/-- Summable-error block data fill exactly the chronological survival fields. -/
theorem QuittingChronologicalDebtShadowingSurvivalFields.of_consecutiveBlock_summableError
    (data : QuittingChronologicalDebtData ι) (hcard : 2 ≤ Fintype.card ι)
    (length : ℕ → ℕ) (nominal : ℕ → ι → ℝ)
    {first second : ι} (hne : first ≠ second)
    (hnominal : ∀ time owner, 0 ≤ nominal time owner)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second)))
    (hfirstError : Summable (consecutiveBlockSum length (fun time =>
      |quittingMarginalQuitHazard data.root first time - nominal time first|)))
    (hsecondError : Summable (consecutiveBlockSum length (fun time =>
      |quittingMarginalQuitHazard data.root second time - nominal time second|))) :
    QuittingChronologicalDebtShadowingSurvivalFields data :=
  QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent data hcard
    (hasTwoPersistentQuittingMarginals_of_consecutiveBlock_summableError
      data.root length nominal hne hnominal hfirst hsecond
      hfirstError hsecondError)

/-- Fixed-fraction block data fill exactly the chronological survival fields. -/
theorem QuittingChronologicalDebtShadowingSurvivalFields.of_consecutiveBlock_fixedFraction
    (data : QuittingChronologicalDebtData ι) (hcard : 2 ≤ Fintype.card ι)
    (length : ℕ → ℕ) (nominal : ℕ → ι → ℝ)
    {first second : ι} (hne : first ≠ second) {theta : ℝ}
    (htheta : 0 < theta)
    (hnominal : ∀ time owner, 0 ≤ nominal time owner)
    (hfirstRetain : ∀ time,
      theta * nominal time first ≤
        quittingMarginalQuitHazard data.root first time)
    (hsecondRetain : ∀ time,
      theta * nominal time second ≤
        quittingMarginalQuitHazard data.root second time)
    (hfirst : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time first)))
    (hsecond : ¬Summable
      (consecutiveBlockSum length (fun time => nominal time second))) :
    QuittingChronologicalDebtShadowingSurvivalFields data :=
  QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent data hcard
    (hasTwoPersistentQuittingMarginals_of_consecutiveBlock_fixedFraction
      data.root length nominal hne htheta hnominal
      hfirstRetain hsecondRetain hfirst hsecond)

/-! ## Boundary witness -/

/-- A two-player path with one perpetual sure quitter and one perpetual
continuer. -/
def onePersistentBoolRoots (_time : ℕ) (owner : Bool) : PMF Bool :=
  if owner = false then PMF.pure true else PMF.pure false

@[simp] theorem quittingStationaryContinueMass_onePersistentBoolRoots
    (time : ℕ) :
    quittingStationaryContinueMass (onePersistentBoolRoots time) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fintype.prod_bool]
  simp [onePersistentBoolRoots]

@[simp] theorem quittingFixedOpponentsContinueMass_onePersistentBoolRoots_false
    (time : ℕ) :
    quittingFixedOpponentsContinueMass onePersistentBoolRoots false time = 1 := by
  unfold quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fintype.prod_bool]
  simp [onePersistentBoolRoots]

/-- Joint survival alone does not imply the full deleted-player family: this
path has vanishing joint survival on every suffix, while deletion of the only
persistent owner leaves survival identically one. -/
theorem exists_jointSurvival_zero_not_all_opponentSurvival_zero :
    (∀ start, Tendsto
      (Math.survivalProduct (fun time =>
        quittingStationaryContinueMass (onePersistentBoolRoots time)) start)
      atTop (nhds 0)) ∧
    ¬(∀ who start, Tendsto
      (quittingOpponentSurvivalWeight onePersistentBoolRoots who start)
      atTop (nhds 0)) := by
  constructor
  · intro start
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop 1] with fuel hfuel
    rcases fuel with _ | fuel
    · omega
    · simp [Math.survivalProduct]
  · intro hall
    have hone : Tendsto
        (quittingOpponentSurvivalWeight onePersistentBoolRoots false 0)
        atTop (nhds 1) := by
      convert tendsto_const_nhds using 1
      funext fuel
      unfold quittingOpponentSurvivalWeight
      simp
    have hzero := hall false 0
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at this

end GameTheory
