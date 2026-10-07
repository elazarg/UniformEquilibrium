import MathUE.Finset.FinFourNonemptyCoalitions
import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtures
import UniformEquilibrium.Quitting.Punishment.ContinueFloor
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import Mathlib.Order.Iterate

/-! # Actual punishment and full-cube roots of the negative-premium fixture

The punishment calculation uses an actual legal immediate-Quit replacement
against every behavioral opponent plan and an adverse pure-row cap. The literal
endpoint polynomials and canonical complementarity classify the entire closed
hazard cube: exact roots at punishment have all four hazards equal to `1/10`.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

open QuittingSureSetOwnerRepair
open scoped BigOperators

theorem participantReward_ge_lower
    (coalition : {S : Finset Player // S.Nonempty}) (who : Player)
    (hwho : who ∈ coalition.val) : lower ≤ survivorReward coalition who := by
  obtain ⟨row, hrow⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective coalition
  have heq : Math.Finset.finFourCoalitionOfRow row = coalition.val :=
    congrArg Subtype.val hrow
  have hmember : who ∈ Math.Finset.finFourCoalitionOfRow row := heq.symm ▸ hwho
  have hcoalition : coalition =
      ⟨Math.Finset.finFourCoalitionOfRow row,
        Math.Finset.finFourCoalitionOfRow_nonempty row⟩ := Subtype.ext heq.symm
  rw [hcoalition]
  fin_cases row <;> fin_cases who
  all_goals
    norm_num [Math.Finset.finFourCoalitionOfRow] at hmember
  all_goals
    norm_num [Math.Finset.finFourCoalitionOfRow, survivorReward, lower, upper,
      Finset.ext_iff, Fin.forall_fin_succ]

/-- Every actual opponent coalition gives the participant the same lower bound. -/
theorem rootQuitPayoff_ge_lower (root : Player → PMF Bool) (who : Player) :
    lower ≤ quittingRootQuitPayoff survivorReward 0 root who := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  calc
    lower = ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition * lower := by
      rw [← Finset.sum_mul, quittingOpponentCoalitionMass_sum_powerset, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro coalition _
      apply mul_le_mul_of_nonneg_left _
        (quittingOpponentCoalitionMass_nonneg root who coalition)
      simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, ↓reduceDIte]
      exact participantReward_ge_lower _ who (Finset.mem_insert_self _ _)

/-- Quit at date zero guarantees the literal floor against all behavioral opponents. -/
theorem immediateQuit_payoff_ge_lower
    (profile : (quittingGame survivorReward).BehaviorProfile) (who : Player) :
    lower ≤ quittingTerminalPayoff survivorReward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy survivorReward who (some 0))) who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
    ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue survivorReward
      (quittingProfileLiveRoot survivorReward profile) who 0 0]
  exact rootQuitPayoff_ge_lower _ who

def adverseQuitter : Player → Player := ![3, 0, 0, 0]

theorem punishmentValue_le_lower (who : Player) :
    quittingPunishmentValue survivorReward who ≤ lower := by
  have hcap := quittingPunishmentValue_le_pureRowCap survivorReward who {adverseQuitter who}
  fin_cases who
  all_goals
    norm_num [adverseQuitter, quittingSetReward, survivorReward, lower, upper,
      Finset.ext_iff, Fin.forall_fin_succ] at hcap ⊢
  all_goals exact hcap

/-- The original sixty-coordinate table has punishment value `629/729` for every player. -/
theorem punishmentValue_eq_lower (who : Player) :
    quittingPunishmentValue survivorReward who = lower := by
  refine le_antisymm (punishmentValue_le_lower who) ?_
  let : Nonempty ((quittingGame survivorReward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile survivorReward⟩
  exact le_ciInf fun profile =>
    (immediateQuit_payoff_ge_lower profile who).trans
      (le_quittingBestReplyValue survivorReward profile who
        (quittingPureTimeBehaviorStrategy survivorReward who (some 0)))

def childEndpointGap (h next previous : ℝ) : ℝ :=
  loss * (1 - h) * (1 - next) * (1 - previous) + (1 - loss) * h + next -
    (3 - loss) * previous

def pivotEndpointGap (first second third : ℝ) : ℝ :=
  -(1 - loss) * first - second + (1 - loss) * third +
    loss * (1 - first) * (1 - second) * (1 - third)

/-- The packet's four endpoint polynomials are the actual annotated-root gaps. -/
theorem rootEndpointGap_eq (root : Player → PMF Bool) :
    quittingRootEndpointDifference survivorReward (fun _ => lower) root =
      ![pivotEndpointGap (hazardOfRoot root 1) (hazardOfRoot root 2) (hazardOfRoot root 3),
        childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 2) (hazardOfRoot root 3),
        childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 3) (hazardOfRoot root 1),
        childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 1) (hazardOfRoot root 2)] := by
  funext who
  rw [quittingRootEndpointDifference_eq_gainValue]
  fin_cases who
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (0 : Player) lower =
      pivotEndpointGap (hazardOfRoot root 1) (hazardOfRoot root 2) (hazardOfRoot root 3)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
    rw [show ({1, 2, 3} : Finset Player).powerset =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [weightOfReward, survivorReward, pivotEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (1 : Player) lower =
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 2) (hazardOfRoot root 3)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
    rw [show ({0, 2, 3} : Finset Player).powerset =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [weightOfReward, survivorReward, childEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (2 : Player) lower =
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 3) (hazardOfRoot root 1)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
    rw [show ({0, 1, 3} : Finset Player).powerset =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [weightOfReward, survivorReward, childEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (3 : Player) lower =
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 1) (hazardOfRoot root 2)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
    rw [show ({0, 1, 2} : Finset Player).powerset =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    simp +decide [weightOfReward, survivorReward, childEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring

private theorem child_positive {h x y z : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hfirst : x < 1 → childEndpointGap h y z ≤ 0)
    (hsecond : y < 1 → childEndpointGap h z x ≤ 0)
    (hthird : 0 < z → 0 ≤ childEndpointGap h x y) : 0 < x := by
  by_contra hnot
  have hxzero : x = 0 := le_antisymm (not_lt.mp hnot) hx.1
  have hgfirst := hfirst (by rw [hxzero]; norm_num)
  have hzpositive : 0 < z := by
    by_contra hznot
    have hzzero : z = 0 := le_antisymm (not_lt.mp hznot) hz.1
    rw [hzzero] at hgfirst
    norm_num [childEndpointGap, loss] at hgfirst
    nlinarith [hh.1, hy.1]
  have hgthird := hthird hzpositive
  rw [hxzero] at hgthird
  have hc : 0 ≤ loss * (1 - h) :=
    mul_nonneg (by norm_num [loss]) (sub_nonneg.mpr hh.2)
  have hcy : 0 ≤ loss * (1 - h) * y := mul_nonneg hc hy.1
  have hybelow : y < 1 := by
    norm_num [childEndpointGap, loss] at hgthird
    norm_num [loss] at hcy
    nlinarith [hh.2]
  have hgsecond := hsecond hybelow
  rw [hxzero] at hgsecond
  have hcz : 0 ≤ loss * (1 - h) * (1 - z) :=
    mul_nonneg hc (sub_nonneg.mpr hz.2)
  have hah : 0 ≤ (1 - loss) * h := mul_nonneg (by norm_num [loss]) hh.1
  simp only [childEndpointGap, sub_zero, mul_one, mul_zero] at hgsecond
  linarith

private theorem child_lt_one {h x y z : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hypositive : 0 < y)
    (hsecond : 0 < y → 0 ≤ childEndpointGap h z x) : x < 1 := by
  by_contra hnot
  have hxone : x = 1 := le_antisymm hx.2 (not_lt.mp hnot)
  have hgsecond := hsecond hypositive
  rw [hxone] at hgsecond
  norm_num [childEndpointGap, loss] at hgsecond
  nlinarith [hh.2, hz.2]

private theorem rootNash_endpoint_complementary (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash survivorReward (fun _ => lower) 0 root) :
    IsExactRowComplementary (hazardOfRoot root)
      (quittingRootEndpointDifference survivorReward (fun _ => lower) root) := by
  have hcompl := (isExactRowComplementary_hazardOfRoot_iff survivorReward
    (fun _ => lower) root).mpr
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        survivorReward (fun _ => lower) root).mpr hnash)
  simpa only [IsExactRowComplementary, quittingRootEndpointDifference_eq_gainValue] using hcompl

/-- Every exact root has three child hazards in `(0,1)`. -/
theorem rootNash_children_proper (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash survivorReward (fun _ => lower) 0 root) :
    hazardOfRoot root 1 ∈ Set.Ioo (0 : ℝ) 1 ∧
      hazardOfRoot root 2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      hazardOfRoot root 3 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hcompl := rootNash_endpoint_complementary root hnash
  have hfirst := hcompl 1
  have hsecond := hcompl 2
  have hthird := hcompl 3
  rw [rootEndpointGap_eq] at hfirst hsecond hthird
  change (0 < hazardOfRoot root 1 → 0 ≤ childEndpointGap (hazardOfRoot root 0)
      (hazardOfRoot root 2) (hazardOfRoot root 3)) ∧
    (hazardOfRoot root 1 < 1 → childEndpointGap (hazardOfRoot root 0)
      (hazardOfRoot root 2) (hazardOfRoot root 3) ≤ 0) at hfirst
  change (0 < hazardOfRoot root 2 → 0 ≤ childEndpointGap (hazardOfRoot root 0)
      (hazardOfRoot root 3) (hazardOfRoot root 1)) ∧
    (hazardOfRoot root 2 < 1 → childEndpointGap (hazardOfRoot root 0)
      (hazardOfRoot root 3) (hazardOfRoot root 1) ≤ 0) at hsecond
  change (0 < hazardOfRoot root 3 → 0 ≤ childEndpointGap (hazardOfRoot root 0)
      (hazardOfRoot root 1) (hazardOfRoot root 2)) ∧
    (hazardOfRoot root 3 < 1 → childEndpointGap (hazardOfRoot root 0)
      (hazardOfRoot root 1) (hazardOfRoot root 2) ≤ 0) at hthird
  have hmem (who : Player) : hazardOfRoot root who ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot_nonneg root who, hazardOfRoot_le_one root who⟩
  have hpos1 := child_positive (hmem 0) (hmem 1) (hmem 2) (hmem 3)
    hfirst.2 hsecond.2 hthird.1
  have hpos2 := child_positive (hmem 0) (hmem 2) (hmem 3) (hmem 1)
    hsecond.2 hthird.2 hfirst.1
  have hpos3 := child_positive (hmem 0) (hmem 3) (hmem 1) (hmem 2)
    hthird.2 hfirst.2 hsecond.1
  exact ⟨⟨hpos1, child_lt_one (hmem 0) (hmem 1) (hmem 3) hpos2 hsecond.1⟩,
    ⟨hpos2, child_lt_one (hmem 0) (hmem 2) (hmem 1) hpos3 hthird.1⟩,
    ⟨hpos3, child_lt_one (hmem 0) (hmem 3) (hmem 2) hpos1 hfirst.1⟩⟩

private def childMapNumerator (h r : ℝ) : ℝ :=
  loss * (1 - h) * (1 - r) + (1 - loss) * h + r

private def childMapDenominator (h r : ℝ) : ℝ :=
  3 - loss + loss * (1 - h) * (1 - r)

private theorem childMapDenominator_pos {h r : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    0 < childMapDenominator h r := by
  have hterm := mul_nonneg
    (mul_nonneg (show 0 ≤ loss by norm_num [loss]) (sub_nonneg.mpr hh.2))
    (sub_nonneg.mpr hr.2)
  unfold childMapDenominator
  linarith [show 0 < 3 - loss by norm_num [loss]]

private theorem childMap_mem {h r : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    childMapNumerator h r / childMapDenominator h r ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := childMapDenominator_pos hh hr
  have hterm := mul_nonneg
    (mul_nonneg (show 0 ≤ loss by norm_num [loss]) (sub_nonneg.mpr hh.2))
    (sub_nonneg.mpr hr.2)
  have hah := mul_nonneg (show 0 ≤ 1 - loss by norm_num [loss]) hh.1
  have hn : 0 ≤ childMapNumerator h r := by
    unfold childMapNumerator
    linarith [hr.1]
  refine ⟨div_nonneg hn hd.le, (div_le_iff₀ hd).mpr ?_⟩
  norm_num [childMapNumerator, childMapDenominator, loss]
  nlinarith [hh.2, hr.2]

private def childMap (h : Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := fun r =>
  ⟨childMapNumerator h r / childMapDenominator h r, childMap_mem h.property r.property⟩

private theorem childMap_monotone (h : Set.Icc (0 : ℝ) 1) : Monotone (childMap h) := by
  intro a b hab
  change childMapNumerator h a / childMapDenominator h a ≤
    childMapNumerator h b / childMapDenominator h b
  apply (div_le_div_iff₀ (childMapDenominator_pos h.property a.property)
    (childMapDenominator_pos h.property b.property)).mpr
  have hc : 0 ≤ loss * (1 - (h : ℝ)) :=
    mul_nonneg (by norm_num [loss]) (sub_nonneg.mpr h.property.2)
  have hc_one : loss * (1 - (h : ℝ)) ≤ 1 := by
    norm_num [loss]
    nlinarith [h.property.1]
  have hah : 0 ≤ (1 - loss) * (h : ℝ) :=
    mul_nonneg (by norm_num [loss]) h.property.1
  have hcoefficient : 0 ≤ (3 - loss) * (1 - loss * (1 - (h : ℝ))) +
      loss * (1 - (h : ℝ)) + loss * (1 - (h : ℝ)) * ((1 - loss) * (h : ℝ)) := by
    exact add_nonneg (add_nonneg
      (mul_nonneg (by norm_num [loss]) (sub_nonneg.mpr hc_one)) hc) (mul_nonneg hc hah)
  have hcross : childMapNumerator h b * childMapDenominator h a -
      childMapNumerator h a * childMapDenominator h b =
      ((b : ℝ) - (a : ℝ)) * ((3 - loss) * (1 - loss * (1 - (h : ℝ))) +
        loss * (1 - (h : ℝ)) + loss * (1 - (h : ℝ)) * ((1 - loss) * (h : ℝ))) := by
    unfold childMapNumerator childMapDenominator
    ring
  have hproduct := mul_nonneg
    (sub_nonneg.mpr (show (a : ℝ) ≤ (b : ℝ) from hab)) hcoefficient
  linarith

private theorem childMap_eq_of_gap_zero (h r : Set.Icc (0 : ℝ) 1) (previous : ℝ)
    (hgap : childEndpointGap h r previous = 0) : (childMap h r : ℝ) = previous := by
  change childMapNumerator h r / childMapDenominator h r = previous
  apply (div_eq_iff (childMapDenominator_pos h.property r.property).ne').mpr
  unfold childMapNumerator childMapDenominator
  unfold childEndpointGap at hgap
  nlinarith only [hgap]

private theorem rootNash_child_gaps_zero (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash survivorReward (fun _ => lower) 0 root) :
    childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 2)
        (hazardOfRoot root 3) = 0 ∧
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 3)
        (hazardOfRoot root 1) = 0 ∧
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 1)
        (hazardOfRoot root 2) = 0 := by
  obtain ⟨hfirst, hsecond, hthird⟩ := rootNash_children_proper root hnash
  have hcompl := rootNash_endpoint_complementary root hnash
  have hzero (who : Player) (hproper : hazardOfRoot root who ∈ Set.Ioo (0 : ℝ) 1) :
      quittingRootEndpointDifference survivorReward (fun _ => lower) root who = 0 :=
    le_antisymm ((hcompl who).2 hproper.2) ((hcompl who).1 hproper.1)
  have hzero1 := hzero 1 hfirst
  have hzero2 := hzero 2 hsecond
  have hzero3 := hzero 3 hthird
  rw [rootEndpointGap_eq] at hzero1 hzero2 hzero3
  exact ⟨hzero1, hzero2, hzero3⟩

/-- All exact annotated roots have equal child hazards. -/
theorem rootNash_children_equal (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash survivorReward (fun _ => lower) 0 root) :
    hazardOfRoot root 1 = hazardOfRoot root 2 ∧
      hazardOfRoot root 2 = hazardOfRoot root 3 := by
  obtain ⟨hg1, hg2, hg3⟩ := rootNash_child_gaps_zero root hnash
  let h : Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot root 0, hazardOfRoot_nonneg root 0, hazardOfRoot_le_one root 0⟩
  let x : Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot root 1, hazardOfRoot_nonneg root 1, hazardOfRoot_le_one root 1⟩
  let y : Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot root 2, hazardOfRoot_nonneg root 2, hazardOfRoot_le_one root 2⟩
  let z : Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot root 3, hazardOfRoot_nonneg root 3, hazardOfRoot_le_one root 3⟩
  have hxy : childMap h x = y := Subtype.ext (childMap_eq_of_gap_zero h x y hg3)
  have hyz : childMap h y = z := Subtype.ext (childMap_eq_of_gap_zero h y z hg1)
  have hzx : childMap h z = x := Subtype.ext (childMap_eq_of_gap_zero h z x hg2)
  have hthree : (childMap h)^[3] x = id^[3] x := by
    calc
      (childMap h)^[3] x = childMap h (childMap h (childMap h x)) := rfl
      _ = x := by rw [hxy, hyz, hzx]
      _ = id^[3] x := rfl
  have hcommute : Function.Commute (childMap h) id := fun _ => rfl
  have hfixed := (hcommute.iterate_pos_eq_iff_map_eq (childMap_monotone h)
    strictMono_id (show 0 < (3 : ℕ) by decide)).mp hthree
  have hxeqy : x = y := hfixed.symm.trans hxy
  have hyeqz : y = z :=
    hxy.symm.trans ((congrArg (childMap h) hxeqy).trans hyz)
  exact ⟨congrArg (fun r : Set.Icc (0 : ℝ) 1 => (r : ℝ)) hxeqy,
    congrArg (fun r : Set.Icc (0 : ℝ) 1 => (r : ℝ)) hyeqz⟩

/-- Exact factorization of the common-child pivot gap. -/
theorem pivotEndpointGap_common_factor (r : ℝ) :
    pivotEndpointGap r r r = (1 / 10 - r) *
      (1 + loss * ((1 - r) ^ 2 + (1 - r) * (9 / 10) + (9 / 10) ^ 2)) := by
  norm_num [pivotEndpointGap, loss]
  ring

private theorem pivot_factor_pos {r : ℝ} (hr : r ≤ 1) :
    0 < 1 + loss * ((1 - r) ^ 2 + (1 - r) * (9 / 10) + (9 / 10) ^ 2) := by
  have hsum : 0 ≤ (1 - r) ^ 2 + (1 - r) * (9 / 10) + (9 / 10) ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hr) (by norm_num)))
      (sq_nonneg _)
  have hterm := mul_nonneg (show 0 ≤ loss by norm_num [loss]) hsum
  linarith

/-- The full closed cube has only the all-tenth hazard vector at actual punishment. -/
theorem rootNash_hazard_eq_tenth (root : Player → PMF Bool)
    (hnash : IsεQuittingRootNash survivorReward (fun _ => lower) 0 root) :
    ∀ who, hazardOfRoot root who = 1 / 10 := by
  obtain ⟨h12, h23⟩ := rootNash_children_equal root hnash
  have h21 := h12.symm
  have h31 := (h12.trans h23).symm
  let h := hazardOfRoot root 0
  let r := hazardOfRoot root 1
  have hh : h ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot_nonneg root 0, hazardOfRoot_le_one root 0⟩
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hazardOfRoot_nonneg root 1, hazardOfRoot_le_one root 1⟩
  have hchild := (rootNash_child_gaps_zero root hnash).1
  rw [h21, h31] at hchild
  change childEndpointGap h r r = 0 at hchild
  have hpivot := rootNash_endpoint_complementary root hnash 0
  rw [rootEndpointGap_eq] at hpivot
  change (0 < h → 0 ≤ pivotEndpointGap (hazardOfRoot root 1)
      (hazardOfRoot root 2) (hazardOfRoot root 3)) ∧
    (h < 1 → pivotEndpointGap (hazardOfRoot root 1)
      (hazardOfRoot root 2) (hazardOfRoot root 3) ≤ 0) at hpivot
  rw [h21, h31] at hpivot
  change (0 < h → 0 ≤ pivotEndpointGap r r r) ∧
    (h < 1 → pivotEndpointGap r r r ≤ 0) at hpivot
  have hfactor := pivot_factor_pos hr.2
  have hreq : r = 1 / 10 := by
    rcases lt_trichotomy r (1 / 10) with hsmall | heq | hlarge
    · have hpositive : 0 < pivotEndpointGap r r r := by
        rw [pivotEndpointGap_common_factor]
        exact mul_pos (sub_pos.mpr hsmall) hfactor
      have hhone : h = 1 := le_antisymm hh.2
        (not_lt.mp fun hbelow => (not_le_of_gt hpositive) (hpivot.2 hbelow))
      rw [hhone] at hchild
      norm_num [childEndpointGap, loss] at hchild
      nlinarith
    · exact heq
    · have hnegative : pivotEndpointGap r r r < 0 := by
        rw [pivotEndpointGap_common_factor]
        exact mul_neg_of_neg_of_pos (sub_neg.mpr hlarge) hfactor
      have hhzero : h = 0 := le_antisymm
        (not_lt.mp fun hpositive => (not_le_of_gt hnegative) (hpivot.1 hpositive)) hh.1
      rw [hhzero] at hchild
      norm_num [childEndpointGap, loss] at hchild
      have hsquare := mul_nonneg (sub_nonneg.mpr hlarge.le)
        (show 0 ≤ 19 / 10 - r by linarith [hr.2])
      nlinarith
  have hheq : h = 1 / 10 := by
    rw [hreq] at hchild
    norm_num [childEndpointGap, loss] at hchild
    linarith
  intro who
  fin_cases who
  · exact hheq
  · exact hreq
  · exact h21.trans hreq
  · exact h31.trans hreq

/-- Exact Nash at the literal punishment annotation is equivalent to four hazards `1/10`. -/
theorem rootNash_iff_hazards_eq_tenth (root : Player → PMF Bool) :
    IsεQuittingRootNash survivorReward (fun _ => lower) 0 root ↔
      ∀ who, hazardOfRoot root who = 1 / 10 := by
  refine ⟨rootNash_hazard_eq_tenth root, ?_⟩
  intro hhazard
  have hgap : quittingRootEndpointDifference survivorReward (fun _ => lower) root =
      fun _ => 0 := by
    rw [rootEndpointGap_eq, hhazard 0, hhazard 1, hhazard 2, hhazard 3]
    funext who
    fin_cases who <;> norm_num [childEndpointGap, pivotEndpointGap, loss]
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    survivorReward (fun _ => lower) root).mp
  intro who
  rw [hgap]
  norm_num

/-- No exact root at actual punishment has a sure coordinate. -/
theorem not_rootNash_of_sureCoordinate (root : Player → PMF Bool) (who : Player)
    (hsure : hazardOfRoot root who = 1) :
    ¬ IsεQuittingRootNash survivorReward (fun _ => lower) 0 root := by
  intro hnash
  have h := rootNash_hazard_eq_tenth root hnash who
  rw [hsure] at h
  norm_num at h

end GameTheory.NegativePremiumCyclicChild.Fixtures
