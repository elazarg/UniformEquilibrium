import MathUE.FiniteContinuousIntervalSelection
import UniformEquilibrium.Quitting.Classification.CommonSupportHazardPolynomials
import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowSupportPeelingConverse
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.ExactRootContinuationConstruction

/-!
# Exact-root boundary characterization for nonnegative quitting premiums

Weak support peeling is equivalent to every absorbing exact root in a padded
payoff box having its successor on the singleton lower boundary. When peeling
fails, a common small hazard constructs an exact root with strictly interior
successor; the continuation is selected coordinatewise by indifference.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem quittingHazardQuitPremium_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    quittingHazardQuitPremium reward 0 player = 0 := by
  unfold quittingHazardQuitPremium
  apply Finset.sum_eq_zero
  intro coalition _
  by_cases hcoalition : coalition.Nonempty
  · rw [Finset.prod_eq_zero (s := coalition) hcoalition.choose_spec (by simp)]
    simp
  · have hempty : coalition = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcoalition
    subst coalition
    simp [quittingSingletonTerminal]

omit [Fintype ι] [DecidableEq ι] in
private theorem exists_support_all_strict_of_not_weakPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ HasWeakQuittingPremiumSupportPeeling reward) :
    ∃ active : Finset ι, active.Nonempty ∧
      ∀ player, player ∈ active →
        ∃ terminal : {S : Finset ι // S.Nonempty}, terminal.val ⊆ active ∧
          player ∈ terminal.val ∧
          reward (quittingSingletonTerminal player) player <
            reward terminal player := by
  rw [hasWeakQuittingPremiumSupportPeeling_iff] at hnot
  push Not at hnot
  obtain ⟨active, hactive, hfailure⟩ := hnot
  refine ⟨active, hactive, ?_⟩
  intro player hplayer
  obtain ⟨terminal, hterminal, hsubset, hmem, hstrict⟩ :=
    hfailure player hplayer
  exact ⟨⟨terminal, hterminal⟩, hsubset, hmem, hstrict⟩

private theorem commonSupport_quitPremium_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (active : Finset ι)
    (hwitness : ∀ player, player ∈ active →
      ∃ terminal : {S : Finset ι // S.Nonempty}, terminal.val ⊆ active ∧
        player ∈ terminal.val ∧
        reward (quittingSingletonTerminal player) player <
          reward terminal player)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (player : ι) (hplayer : player ∈ active) :
    0 < quittingHazardQuitPremium reward
      (commonSupportHazard active t) player := by
  obtain ⟨terminal, hsubset, hmem, hstrict⟩ := hwitness player hplayer
  let coalition := terminal.val.erase player
  have hcoalitionPowerset : coalition ∈
      (Finset.univ.erase player).powerset := by
    apply Finset.mem_powerset.mpr
    intro other hother
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hother).1, Finset.mem_univ other⟩
  unfold quittingHazardQuitPremium
  apply Finset.sum_pos'
  · intro other _
    apply mul_nonneg
    · apply mul_nonneg
      · apply Finset.prod_nonneg
        intro who _
        simp only [commonSupportHazard]
        split <;> linarith
      · apply Finset.prod_nonneg
        intro who _
        simp only [commonSupportHazard]
        split <;> linarith
    · exact sub_nonneg.mpr (hnonnegative
        ⟨insert player other, Finset.insert_nonempty player other⟩ player
        (Finset.mem_insert_self player other))
  · refine ⟨coalition, hcoalitionPowerset, ?_⟩
    have hinsert : insert player coalition = terminal.val :=
      Finset.insert_erase hmem
    have hfirst : 0 < ∏ other ∈ coalition,
        commonSupportHazard active t other := by
      apply Finset.prod_pos
      intro other hother
      have hotherActive : other ∈ active := hsubset (by
        rw [← hinsert]
        exact Finset.mem_insert_of_mem hother)
      simp [commonSupportHazard, hotherActive, ht0]
    have hsecond : 0 < ∏ other ∈ Finset.univ.erase player \ coalition,
        (1 - commonSupportHazard active t other) := by
      apply Finset.prod_pos
      intro other _
      by_cases hotherActive : other ∈ active
      · simp [commonSupportHazard, hotherActive, ht1]
      · simp [commonSupportHazard, hotherActive]
    have hpremium : 0 <
        reward ⟨insert player coalition,
            Finset.insert_nonempty player coalition⟩ player -
          reward (quittingSingletonTerminal player) player := by
      rw [show (⟨insert player coalition,
        Finset.insert_nonempty player coalition⟩ :
          {S : Finset ι // S.Nonempty}) = terminal by
            exact Subtype.ext hinsert]
      exact sub_pos.mpr hstrict
    exact mul_pos (mul_pos hfirst hsecond) hpremium

omit [DecidableEq ι] in
private theorem quittingRootSuccessorPayoff_lt_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι)
    {M B : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (htail : tail player ≤ B) (hMB : M < B)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingRootSuccessorPayoff reward tail root player < B := by
  have habsorbing :=
    abs_quittingRootAbsorbingContribution_le reward root player M hreward
  have habsorbingUpper :
      quittingRootAbsorbingContribution reward root player ≤
        M * quittingRootAbsorptionMass root :=
    (le_abs_self _).trans habsorbing
  have hcontinueNonnegative : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  have htailTerm : quittingStationaryContinueMass root * tail player ≤
      quittingStationaryContinueMass root * B :=
    mul_le_mul_of_nonneg_left htail hcontinueNonnegative
  have hmass : quittingRootAbsorptionMass root =
      1 - quittingStationaryContinueMass root := rfl
  have hnegative : quittingRootAbsorptionMass root * (M - B) < 0 :=
    mul_neg_of_pos_of_neg habsorption (sub_neg.mpr hMB)
  rw [quittingRootSuccessorPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [hmass] at habsorbingUpper hnegative
  nlinarith

/-- Failure of weak peeling under nonnegative own premiums produces an
absorbing exact root whose continuation is in the padded reward box and whose
entire successor is strictly between the singleton vector and the upper cap. -/
theorem exists_exactRoot_strictSingletonInterior_of_not_weakPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    {M B : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hMB : M < B)
    (hnot : ¬ HasWeakQuittingPremiumSupportPeeling reward) :
    ∃ (tail : Payoff ι) (root : ι → PMF Bool),
      (∀ player, tail player ∈ Set.Icc (-B) B) ∧
      IsεQuittingRootNash reward tail 0 root ∧
      0 < quittingRootAbsorptionMass root ∧
      ∀ player,
        reward (quittingSingletonTerminal player) player <
            quittingRootSuccessorPayoff reward tail root player ∧
          quittingRootSuccessorPayoff reward tail root player < B := by
  obtain ⟨active, hactive, hwitness⟩ :=
    exists_support_all_strict_of_not_weakPeeling reward hnot
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal hactive.choose) hactive.choose)
  let hazard : ℝ → ι → ℝ := commonSupportHazard active
  let emptyMass : ι → ℝ → ℝ := fun player t =>
    hazardOpponentContinueMass (hazard t) player
  let quitValue : ι → ℝ → ℝ := fun player t =>
    reward (quittingSingletonTerminal player) player +
      quittingHazardQuitPremium reward (hazard t) player
  let continueZero : ι → ℝ → ℝ := fun player t =>
    hazardContinueZeroPayoff reward (hazard t) player
  let activeTail : ι → ℝ → ℝ := fun player t =>
    (quitValue player t - continueZero player t) / emptyMass player t
  let outsiderSlack : ι → ℝ → ℝ := fun player t =>
    continueZero player t + emptyMass player t * B - quitValue player t
  let test : ι → ℝ → ℝ := fun player t =>
    if player ∈ active then activeTail player t else outsiderSlack player t
  let lower : ι → ℝ := fun player => if player ∈ active then -B else 0
  let upper : ι → ℝ := fun player =>
    if player ∈ active then B else outsiderSlack player 0 + 1
  have hhazard : Continuous hazard := by
    rw [continuous_pi_iff]
    exact fun player => continuous_commonSupportHazard active player
  have hemptyContinuous : ∀ player, Continuous (emptyMass player) := by
    intro player
    exact (continuous_hazardOpponentContinueMass player).comp hhazard
  have hquitContinuous : ∀ player, Continuous (quitValue player) := by
    intro player
    exact continuous_const.add
      ((continuous_quittingHazardQuitPremium reward player).comp hhazard)
  have hcontinueContinuous : ∀ player, Continuous (continueZero player) := by
    intro player
    exact (continuous_hazardContinueZeroPayoff reward player).comp hhazard
  have hemptyZero : ∀ player, emptyMass player 0 = 1 := by
    intro player
    simp [emptyMass, hazard]
  have hquitZero : ∀ player, quitValue player 0 =
      reward (quittingSingletonTerminal player) player := by
    intro player
    simp [quitValue, hazard, quittingHazardQuitPremium_zero]
  have hcontinueZero : ∀ player, continueZero player 0 = 0 := by
    intro player
    simp [continueZero, hazard]
  have hactiveTailZero : ∀ player, activeTail player 0 =
      reward (quittingSingletonTerminal player) player := by
    intro player
    simp [activeTail, hquitZero, hcontinueZero, hemptyZero]
  have houtsideSlackZero : ∀ player, outsiderSlack player 0 =
      B - reward (quittingSingletonTerminal player) player := by
    intro player
    simp [outsiderSlack, hquitZero, hcontinueZero, hemptyZero]
  have htestContinuous : ∀ player, ContinuousAt (test player) 0 := by
    intro player
    by_cases hplayer : player ∈ active
    · simp only [test, hplayer, if_true]
      apply ContinuousAt.div
      · exact (hquitContinuous player).continuousAt.sub
          (hcontinueContinuous player).continuousAt
      · exact (hemptyContinuous player).continuousAt
      · rw [hemptyZero player]
        norm_num
    · simp only [test, hplayer, if_false]
      exact ((hcontinueContinuous player).add
        ((hemptyContinuous player).mul continuous_const)).sub
          (hquitContinuous player) |>.continuousAt
  have htestZero : ∀ player, test player 0 ∈ Set.Ioo (lower player) (upper player) := by
    intro player
    by_cases hplayer : player ∈ active
    · have hsingletonBound := hreward (quittingSingletonTerminal player) player
      have hsingletonSides := abs_le.mp hsingletonBound
      simp only [test, lower, upper, hplayer, if_true, hactiveTailZero]
      constructor <;> linarith
    · have hsingletonBound := hreward (quittingSingletonTerminal player) player
      have hsingletonSides := abs_le.mp hsingletonBound
      simp only [test, lower, upper, hplayer, if_false, houtsideSlackZero]
      constructor <;> linarith
  obtain ⟨t, ht0, ht1, htest⟩ :=
    Math.exists_pos_lt_one_forall_mem_Ioo_of_continuousAt
      test lower upper htestContinuous htestZero
  have hhazard0 : ∀ player, 0 ≤ hazard t player := by
    intro player
    simp only [hazard, commonSupportHazard]
    split <;> linarith
  have hhazard1 : ∀ player, hazard t player ≤ 1 := by
    intro player
    simp only [hazard, commonSupportHazard]
    split <;> linarith
  let root : ι → PMF Bool := rootOfHazard (hazard t) hhazard0 hhazard1
  have hrates : ∀ player, (root player true).toReal = hazard t player := by
    intro player
    change hazardOfRoot root player = hazard t player
    rw [show hazardOfRoot root = hazard t from
      hazardOfRoot_rootOfHazard (hazard t) hhazard0 hhazard1]
  have hquitValue : ∀ player, quitValue player t =
      quittingRootQuitPayoff reward 0 root player := by
    intro player
    dsimp only [quitValue]
    rw [quittingHazardQuitPremium_eq_rootQuitPremium
      reward (hazard t) hhazard0 hhazard1]
    dsimp only [root]
    ring
  have hcontinueValue : ∀ player, continueZero player t =
      quittingRootContinuePayoff reward 0 root player := by
    intro player
    exact hazardContinueZeroPayoff_eq_rootContinuePayoff
      reward (hazard t) hhazard0 hhazard1 player
  have hemptyValue : ∀ player, emptyMass player t =
      quittingOpponentCoalitionMass root player ∅ := by
    intro player
    exact hazardOpponentContinueMass_eq_root_emptyMass
      (hazard t) hhazard0 hhazard1 player
  let cap : Payoff ι := fun _ => B
  let tail : Payoff ι := fun player =>
    if player ∈ active then
      (quittingRootQuitPayoff reward 0 root player -
        quittingRootContinuePayoff reward 0 root player) /
          quittingOpponentCoalitionMass root player ∅
    else cap player
  have houtsideZero : ∀ player, player ∉ active →
      (root player true).toReal = 0 := by
    intro player hplayer
    rw [hrates player]
    simp [hazard, commonSupportHazard, hplayer]
  have hemptyPositive : ∀ player, player ∈ active →
      0 < quittingOpponentCoalitionMass root player ∅ := by
    intro player _
    rw [← hemptyValue player]
    unfold emptyMass hazardOpponentContinueMass
    apply Finset.prod_pos
    intro other _
    by_cases hother : other ∈ active
    · simp [hazard, commonSupportHazard, hother, ht1]
    · simp [hazard, commonSupportHazard, hother]
  have houtsideDominance : ∀ player, player ∉ active →
      quittingRootQuitPayoff reward 0 root player ≤
        quittingRootContinuePayoff reward cap root player := by
    intro player hplayer
    have hpositive : 0 < outsiderSlack player t := by
      have := (htest player).1
      simpa [test, lower, hplayer] using this
    dsimp only [outsiderSlack] at hpositive
    rw [hquitValue player, hcontinueValue player,
      hemptyValue player] at hpositive
    have hcontinueCap := quittingRootContinuePayoff_eq_zero_add_emptyMass_mul
      reward cap root player
    dsimp only [cap] at hcontinueCap
    linarith
  have hnash : IsεQuittingRootNash reward tail 0 root := by
    exact exactRootNash_of_indifferenceContinuation reward root active cap
      houtsideZero hemptyPositive houtsideDominance
  have htailBox : ∀ player, tail player ∈ Set.Icc (-B) B := by
    intro player
    by_cases hplayer : player ∈ active
    · have hinside := htest player
      simp only [test, lower, upper, hplayer, if_true] at hinside
      dsimp only [activeTail] at hinside
      rw [hquitValue player, hcontinueValue player,
        hemptyValue player] at hinside
      simp only [tail, hplayer, if_true]
      exact ⟨le_of_lt hinside.1, le_of_lt hinside.2⟩
    · have hBnonnegative : 0 ≤ B := lt_of_le_of_lt hM hMB |>.le
      simp [tail, cap, hplayer, hBnonnegative]
  obtain ⟨marked, hmarked⟩ := hactive
  have habsorption : 0 < quittingRootAbsorptionMass root := by
    have hcontinue :=
      quittingStationaryContinueMass_le_ownContinueProbability root marked
    have hsum :=
      quittingRoot_continueProbability_add_quitProbability root marked
    have hrate : (root marked true).toReal = t := by
      rw [hrates marked]
      simp [hazard, commonSupportHazard, hmarked]
    unfold quittingRootAbsorptionMass
    rw [hrate] at hsum
    linarith
  refine ⟨tail, root, htailBox, hnash, habsorption, ?_⟩
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  intro player
  constructor
  · by_cases hplayer : player ∈ active
    · have hrate : 0 < (root player true).toReal := by
        rw [hrates player]
        simp [hazard, commonSupportHazard, hplayer, ht0]
      have hrootNe : root player true ≠ 0 := by
        intro hzero
        rw [hzero] at hrate
        norm_num at hrate
      rw [quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
        hendpoint player hrootNe,
        quittingRootQuitPayoff_continuation_invariant reward tail 0 root player]
      rw [← hquitValue player]
      dsimp only [quitValue]
      linarith [commonSupport_quitPremium_pos reward hnonnegative active hwitness
        ht0 ht1 player hplayer]
    · have hcontinueNe : root player false ≠ 0 := by
        intro hzero
        have hsum := quittingRoot_continueProbability_add_quitProbability root player
        rw [hzero, houtsideZero player hplayer] at hsum
        norm_num at hsum
      rw [quittingRootSuccessorPayoff_eq_continuePayoff_of_isZeroEndpointNash
        hendpoint player hcontinueNe]
      exact lt_of_le_of_lt
        (quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
          hnonnegative tail root player)
        (lt_of_not_ge (not_le_of_gt (by
          have hstrict := (htest player).1
          simp only [test, lower, hplayer, if_false] at hstrict
          dsimp only [outsiderSlack] at hstrict
          rw [hquitValue player, hcontinueValue player,
            hemptyValue player] at hstrict
          have htailCap : tail player = cap player := by simp [tail, hplayer]
          rw [quittingRootQuitPayoff_continuation_invariant reward tail 0 root player,
            quittingRootContinuePayoff_eq_zero_add_emptyMass_mul, htailCap]
          dsimp only [cap]
          linarith)))
  · exact quittingRootSuccessorPayoff_lt_cap reward tail root player hreward
      (htailBox player).2 hMB habsorption

/-- Under nonnegative own premiums, weak support peeling is equivalent to the
claim that every absorbing exact root over the padded reward box has its
successor on the singleton lower boundary of that box. -/
theorem weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    {M B : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hMB : M < B) :
    HasWeakQuittingPremiumSupportPeeling reward ↔
      ∀ (tail : Payoff ι) (root : ι → PMF Bool),
        (∀ player, tail player ∈ Set.Icc (-B) B) →
        IsεQuittingRootNash reward tail 0 root →
        0 < quittingRootAbsorptionMass root →
        (∀ player,
          quittingRootSuccessorPayoff reward tail root player ∈
            Set.Icc
              (reward (quittingSingletonTerminal player) player) B) ∧
        ∃ player,
          quittingRootSuccessorPayoff reward tail root player =
            reward (quittingSingletonTerminal player) player := by
  constructor
  · intro hpeel tail root htail hnash habsorption
    have hlow : HasProductLowQuittingPremium reward :=
      (hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative
        reward hnonnegative).mpr hpeel
    obtain ⟨hlower, player, _hactive, hequal⟩ :=
      exactRootSuccessor_mem_singletonLowerBoundary
        hnonnegative hlow tail root hnash habsorption
    constructor
    · intro who
      exact ⟨hlower who, le_of_lt
        (quittingRootSuccessorPayoff_lt_cap reward tail root who hreward
          (htail who).2 hMB habsorption)⟩
    · exact ⟨player, hequal⟩
  · intro hboundary
    by_contra hnot
    obtain ⟨tail, root, htail, hnash, habsorption, hinterior⟩ :=
      exists_exactRoot_strictSingletonInterior_of_not_weakPeeling
        reward hnonnegative hreward hMB hnot
    obtain ⟨_hbox, player, hequal⟩ :=
      hboundary tail root htail hnash habsorption
    exact (ne_of_gt (hinterior player).1) hequal

end GameTheory
