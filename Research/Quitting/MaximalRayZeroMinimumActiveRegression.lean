/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ForwardExactCapTailFlow
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Quitting.Root.FirstOrderProductFlow

/-!
# Three-active-player maximal-ray regression data

This module isolates the finite algebra behind the zero-minimum maximal-ray
regressions.  It defines the active three-player reward table and proves its
exact product-root endpoint equation.  The infinite recurrence is represented
by a certificate whose fields are all scalar equalities and inequalities; it
does not assert that such a certificate comes from a positive-minimum source.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

namespace MaximalRayZeroMinimumActiveRegression

abbrev Player := Fin 3

/-- The zero-diagonal interaction matrix from the regression. -/
def interaction (who owner : Player) : ℝ :=
  ![![0, 1, -2], ![1, 0, -2], ![2 / 5, 2 / 5, 0]] who owner

/-- Passive terminal interaction, equal to `-J/2`. -/
def passive (who owner : Player) : ℝ :=
  -interaction who owner / 2

/-- Active reward table.  A quitter adds its `J` row to the passive `-J/2`
row, while a continuer sees only the passive row. -/
def reward (terminal : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  fun who ↦
    (∑ owner ∈ terminal.val.erase who, passive who owner) +
      if who ∈ terminal.val then
        ∑ owner ∈ terminal.val.erase who, interaction who owner
      else 0

theorem singleton_reward_eq_zero (who observer : Player) :
    reward (quittingSingletonTerminal who) observer =
      if observer = who then 0 else passive observer who := by
  fin_cases who <;> fin_cases observer <;>
    simp +decide [reward, passive, interaction,
      quittingSingletonTerminal]

theorem own_singleton_reward_eq_zero (who : Player) :
    reward (quittingSingletonTerminal who) who = 0 := by
  rw [singleton_reward_eq_zero]
  simp

/-- Product root with displayed marginal Quit hazards. -/
def root (hazard : Player → ℝ)
    (hazard_nonneg : ∀ who, 0 ≤ hazard who)
    (hazard_le_one : ∀ who, hazard who ≤ 1) : Player → PMF Bool :=
  fun who ↦ quittingHazardCoin (hazard who)
    (hazard_nonneg who) (hazard_le_one who)

@[simp] theorem root_true
    (hazard : Player → ℝ)
    (hazard_nonneg : ∀ who, 0 ≤ hazard who)
    (hazard_le_one : ∀ who, hazard who ≤ 1) (who : Player) :
    ((root hazard hazard_nonneg hazard_le_one who) true).toReal = hazard who := by
  simp [root]

@[simp] theorem root_false
    (hazard : Player → ℝ)
    (hazard_nonneg : ∀ who, 0 ≤ hazard who)
    (hazard_le_one : ∀ who, hazard who ≤ 1) (who : Player) :
    ((root hazard hazard_nonneg hazard_le_one who) false).toReal =
      1 - hazard who := by
  simp [root]

/-- Symmetric active cap `(a,a,b)`. -/
def cap (a b : ℝ) : Payoff Player := ![a, a, b]

/-- The literal right-hand side of the active endpoint equation. -/
def endpointPolynomial (a b : ℝ) (hazard : Player → ℝ)
    (who : Player) : ℝ :=
  (∑ owner, interaction who owner * hazard owner) -
    cap a b who * ∏ owner ∈ Finset.univ.erase who, (1 - hazard owner)

/-- Exact endpoint equation of the active product root.  No first-order
approximation is used. -/
theorem endpointDifference_eq_endpointPolynomial
    (a b : ℝ) (hazard : Player → ℝ)
    (hazard_nonneg : ∀ who, 0 ≤ hazard who)
    (hazard_le_one : ∀ who, hazard who ≤ 1) (who : Player) :
    quittingRootEndpointDifference reward (cap a b)
        (root hazard hazard_nonneg hazard_le_one) who =
      endpointPolynomial a b hazard who := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
  have hwho : who = 0 ∨ who = 1 ∨ who = 2 := by
    fin_cases who <;> simp
  rcases hwho with rfl | rfl | rfl
  ·
    rw [show ((Finset.univ.erase (0 : Player)).powerset) =
        {∅, {1}, {2}, {1, 2}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      reward, endpointPolynomial, cap, root, passive, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (0 : Player)) = {1, 2} by decide,
      show ({1, 2} : Finset Player) \ {1} = {2} by decide]
    ring
  ·
    rw [show ((Finset.univ.erase (1 : Player)).powerset) =
        {∅, {0}, {2}, {0, 2}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      reward, endpointPolynomial, cap, root, passive, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (1 : Player)) = {0, 2} by decide,
      show ({0, 2} : Finset Player) \ {0} = {2} by decide]
    ring
  ·
    rw [show ((Finset.univ.erase (2 : Player)).powerset) =
        {∅, {0}, {1}, {0, 1}} by decide]
    simp +decide [quittingOpponentCoalitionMass,
      quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
      reward, endpointPolynomial, cap, root, passive, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (2 : Player)) = {0, 1} by decide,
      show ({0, 1} : Finset Player) \ {0} = {1} by decide]
    ring

/-- Symmetric mixing threshold of players `0` and `1`. -/
def symmetricHazard (a z : ℝ) : ℝ :=
  (a * (1 - z) + 2 * z) / (1 + a * (1 - z))

/-- Player `2`'s remaining scalar indifference equation. -/
def thirdIndifference (a b z : ℝ) : ℝ :=
  -b * (1 - symmetricHazard a z) ^ 2 +
    (4 / 5 : ℝ) * symmetricHazard a z

/-- The positive scalar root selected by one cap in the invariant cone. -/
structure FullRootData (a b : ℝ) where
  z : ℝ
  z_pos : 0 < z
  z_lt_half : z < 1 / 2
  third_indifferent : thirdIndifference a b z = 0

theorem symmetricHazard_zero (a : ℝ) :
    symmetricHazard a 0 = a / (1 + a) := by
  simp [symmetricHazard]

theorem symmetricHazard_half (a : ℝ) (ha : 0 < a) :
    symmetricHazard a (1 / 2) = 1 := by
  unfold symmetricHazard
  have h : 1 + a * (1 - (1 / 2 : ℝ)) ≠ 0 := by
    have : 0 < 1 + a * (1 - (1 / 2 : ℝ)) := by positivity
    exact this.ne'
  field_simp [h]
  ring

/-- Every cap in the displayed invariant cone has a positive full-support
scalar root.  This is an actual IVT construction, not a supplied recurrence
field. -/
theorem nonempty_fullRootData
    (a b : ℝ) (ha : 0 < a) (ha_small : a < 1 / 8)
    (hratio_lower : (9 / 10 : ℝ) < b / a) :
    Nonempty (FullRootData a b) := by
  have hb : 0 < b := by
    have hscaled : (9 / 10 : ℝ) * a < b :=
      (lt_div_iff₀ ha).mp hratio_lower
    nlinarith
  have hdenom : 0 < 1 + a := by linarith
  have hthreshold : (4 / 5 : ℝ) * a * (1 + a) < b := by
    have hscaled : (9 / 10 : ℝ) * a < b := by
      exact (lt_div_iff₀ ha).mp hratio_lower
    have hcoefficient : (4 / 5 : ℝ) * (1 + a) < 9 / 10 := by
      nlinarith
    have := mul_lt_mul_of_pos_right hcoefficient ha
    nlinarith
  have hzero : thirdIndifference a b 0 < 0 := by
    rw [thirdIndifference, symmetricHazard_zero]
    field_simp [hdenom.ne']
    nlinarith [sq_nonneg (1 + a)]
  have hhalf : 0 < thirdIndifference a b (1 / 2) := by
    rw [thirdIndifference, symmetricHazard_half a ha]
    norm_num
  have hcontinuous : ContinuousOn (thirdIndifference a b)
      (Set.Icc 0 (1 / 2)) := by
    have hdenom : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2),
        1 + a * (1 - z) ≠ 0 := by
      intro z hz
      have : 0 < 1 + a * (1 - z) := by
        have hfactor : 0 ≤ 1 - z := by linarith [hz.2]
        positivity
      exact this.ne'
    have honeMinus : ContinuousOn (fun z : ℝ ↦ 1 - z)
        (Set.Icc 0 (1 / 2)) :=
      (continuous_const.sub continuous_id).continuousOn
    have hnumerator : ContinuousOn
        (fun z : ℝ ↦ a * (1 - z) + 2 * z) (Set.Icc 0 (1 / 2)) :=
      (continuousOn_const.mul honeMinus).add
        (continuousOn_const.mul continuous_id.continuousOn)
    have hdenominator : ContinuousOn
        (fun z : ℝ ↦ 1 + a * (1 - z)) (Set.Icc 0 (1 / 2)) :=
      continuousOn_const.add (continuousOn_const.mul honeMinus)
    have ht : ContinuousOn (symmetricHazard a) (Set.Icc 0 (1 / 2)) := by
      change ContinuousOn
        (fun z : ℝ ↦ (a * (1 - z) + 2 * z) / (1 + a * (1 - z)))
        (Set.Icc 0 (1 / 2))
      exact hnumerator.div hdenominator hdenom
    exact (continuousOn_const.mul ((continuousOn_const.sub ht).pow 2)).add
      (continuousOn_const.mul ht)
  obtain ⟨z, hz, hroot⟩ := intermediate_value_Ioo
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) hcontinuous ⟨hzero, hhalf⟩
  exact ⟨⟨z, hz.1, hz.2, hroot⟩⟩

namespace FullRootData

def t {a b : ℝ} (data : FullRootData a b) : ℝ :=
  symmetricHazard a data.z

theorem denominator_pos {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    0 < 1 + a * (1 - data.z) := by
  have hz : data.z < 1 := data.z_lt_half.trans (by norm_num)
  have : 0 < a * (1 - data.z) := mul_pos ha (sub_pos.mpr hz)
  linarith

theorem t_pos {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    0 < data.t := by
  unfold t symmetricHazard
  exact div_pos
    (by
      exact add_pos (mul_pos ha (sub_pos.mpr
        (data.z_lt_half.trans (by norm_num))))
        (mul_pos (by norm_num) data.z_pos))
    (data.denominator_pos ha)

theorem t_lt_one {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    data.t < 1 := by
  unfold t symmetricHazard
  rw [div_lt_one (data.denominator_pos ha)]
  linarith [data.z_lt_half]

theorem z_lt_t {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    data.z < data.t := by
  unfold t symmetricHazard
  rw [lt_div_iff₀ (data.denominator_pos ha)]
  have hzHalf : data.z < 1 := data.z_lt_half.trans (by norm_num)
  have hdiff : 0 < a * (1 - data.z) ^ 2 + data.z := by
    exact add_pos (mul_pos ha (sq_pos_of_pos (sub_pos.mpr hzHalf))) data.z_pos
  nlinarith [hdiff]

theorem balance {a b : ℝ} (data : FullRootData a b) :
    (4 / 5 : ℝ) * data.t = b * (1 - data.t) ^ 2 := by
  have h := data.third_indifferent
  simp only [thirdIndifference, t] at h ⊢
  linarith

theorem t_le_five_fourths_b {a b : ℝ} (data : FullRootData a b)
    (ha : 0 < a) (hb : 0 < b) :
    data.t ≤ (5 / 4 : ℝ) * b := by
  have ht0 : 0 ≤ data.t := (data.t_pos ha).le
  have ht1 : data.t < 1 := data.t_lt_one ha
  have hsquare : (1 - data.t) ^ 2 ≤ 1 := by nlinarith
  have hbalance := data.balance
  nlinarith [mul_le_mul_of_nonneg_left hsquare hb.le]

end FullRootData

/-! ## Exhaustive scalar root classification -/

/-- Endpoint complementarity written only in the three marginal hazards. -/
def IsHazardEndpointNash (a b : ℝ) (hazard : Player → ℝ) : Prop :=
  ∀ who,
    0 ≤ hazard who ∧ hazard who ≤ 1 ∧
      (1 - hazard who) * endpointPolynomial a b hazard who ≤ 0 ∧
      0 ≤ hazard who * endpointPolynomial a b hazard who

structure ScalarEndpointNash (a b x y z : ℝ) : Prop where
  x_nonneg : 0 ≤ x
  x_le_one : x ≤ 1
  y_nonneg : 0 ≤ y
  y_le_one : y ≤ 1
  z_nonneg : 0 ≤ z
  z_le_one : z ≤ 1
  x_continue : (1 - x) *
    (y - 2 * z - a * (1 - y) * (1 - z)) ≤ 0
  x_quit : 0 ≤ x * (y - 2 * z - a * (1 - y) * (1 - z))
  y_continue : (1 - y) *
    (x - 2 * z - a * (1 - x) * (1 - z)) ≤ 0
  y_quit : 0 ≤ y * (x - 2 * z - a * (1 - x) * (1 - z))
  z_continue : (1 - z) *
    ((2 / 5 : ℝ) * x + (2 / 5 : ℝ) * y - b * (1 - x) * (1 - y)) ≤ 0
  z_quit : 0 ≤ z *
    ((2 / 5 : ℝ) * x + (2 / 5 : ℝ) * y - b * (1 - x) * (1 - y))

namespace ScalarEndpointNash

theorem swap {a b x y z : ℝ} (nash : ScalarEndpointNash a b x y z) :
    ScalarEndpointNash a b y x z where
  x_nonneg := nash.y_nonneg
  x_le_one := nash.y_le_one
  y_nonneg := nash.x_nonneg
  y_le_one := nash.x_le_one
  z_nonneg := nash.z_nonneg
  z_le_one := nash.z_le_one
  x_continue := nash.y_continue
  x_quit := nash.y_quit
  y_continue := nash.x_continue
  y_quit := nash.x_quit
  z_continue := by
    convert nash.z_continue using 1
    ring
  z_quit := by
    convert nash.z_quit using 1
    ring

theorem zero_left {a b x y z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (nash : ScalarEndpointNash a b x y z) (hx : x = 0) :
    y = 0 ∧ z = 0 := by
  have hy : y = 0 := by
    by_contra hyne
    have hypos : 0 < y := lt_of_le_of_ne nash.y_nonneg (Ne.symm hyne)
    have hgain : 0 ≤ x - 2 * z - a * (1 - x) * (1 - z) :=
      nonneg_of_mul_nonneg_left
        (by simpa only [mul_comm] using nash.y_quit) hypos
    rw [hx] at hgain
    have hproduct := mul_nonneg ha.le (sub_nonneg.mpr nash.z_le_one)
    by_cases hz0 : z = 0
    · rw [hz0] at hgain
      linarith
    · have hzpos : 0 < z := lt_of_le_of_ne nash.z_nonneg (Ne.symm hz0)
      linarith
  have hz : z = 0 := by
    by_contra hzne
    have hzpos : 0 < z := lt_of_le_of_ne nash.z_nonneg (Ne.symm hzne)
    rw [hx, hy] at nash
    have hgain : 0 ≤ -(b : ℝ) := by
      have := nonneg_of_mul_nonneg_left
        (by simpa only [mul_comm] using nash.z_quit) hzpos
      simpa using this
    linarith
  exact ⟨hy, hz⟩

theorem active_left_lt_one {a b x y z : ℝ} (ha : 0 < a)
    (nash : ScalarEndpointNash a b x y z) (hxpos : 0 < x) (hypos : 0 < y) :
    x < 1 := by
  by_contra hxnot
  have hx1 : x = 1 := le_antisymm nash.x_le_one (not_lt.mp hxnot)
  have hg1nonneg : 0 ≤ x - 2 * z - a * (1 - x) * (1 - z) :=
    nonneg_of_mul_nonneg_left
      (by simpa only [mul_comm] using nash.y_quit) hypos
  rw [hx1] at hg1nonneg
  by_cases hy1 : y = 1
  · rw [hx1, hy1] at nash
    have hz1 : z = 1 := by
      have hcontinue := nash.z_continue
      nlinarith
    nlinarith
  · have hylt : y < 1 := lt_of_le_of_ne nash.y_le_one hy1
    have hg1nonpos : x - 2 * z - a * (1 - x) * (1 - z) ≤ 0 :=
      nonpos_of_mul_nonpos_left
        (by simpa only [mul_comm] using nash.y_continue) (sub_pos.mpr hylt)
    have hzhalf : z = 1 / 2 := by
      rw [hx1] at hg1nonpos
      nlinarith
    have hg0nonneg : 0 ≤ y - 2 * z - a * (1 - y) * (1 - z) :=
      nonneg_of_mul_nonneg_left
        (by simpa only [mul_comm] using nash.x_quit) hxpos
    have hnormalized : 0 ≤ y - 1 - a * (1 - y) / 2 := by
      calc
        0 ≤ y - 2 * z - a * (1 - y) * (1 - z) := hg0nonneg
        _ = y - 1 - a * (1 - y) / 2 := by rw [hzhalf]; ring
    have hcoefficient : 0 < 1 + a / 2 := by linarith
    have hnegative : y - 1 < 0 := sub_neg.mpr hylt
    have : y - 1 - a * (1 - y) / 2 = (1 + a / 2) * (y - 1) := by ring
    rw [this] at hnormalized
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hcoefficient hnegative)) hnormalized

end ScalarEndpointNash

theorem symmetricHazard_lt_one_iff
    (a z : ℝ) (ha : 0 < a) (hzle : z ≤ 1) :
    symmetricHazard a z < 1 ↔ z < 1 / 2 := by
  have hdenom : 0 < 1 + a * (1 - z) := by
    positivity
  unfold symmetricHazard
  rw [div_lt_one hdenom]
  constructor <;> intro h <;> nlinarith

theorem thirdIndifference_eq_zero_of_symmetric_gain_eq_zero
    (a b z : ℝ)
    (hgain : (2 / 5 : ℝ) * symmetricHazard a z +
      (2 / 5 : ℝ) * symmetricHazard a z -
        b * (1 - symmetricHazard a z) *
          (1 - symmetricHazard a z) = 0) :
    thirdIndifference a b z = 0 := by
  unfold thirdIndifference
  nlinarith [hgain]

theorem symmetricHazard_strictMonoOn_half
    (a : ℝ) (ha : 0 < a) :
    StrictMonoOn (symmetricHazard a) (Set.Icc 0 (1 / 2)) := by
  intro first hfirst second hsecond hlt
  have hdenomFirst : 0 < 1 + a * (1 - first) := by
    have : first ≤ 1 := hfirst.2.trans (by norm_num)
    positivity
  have hdenomSecond : 0 < 1 + a * (1 - second) := by
    have : second ≤ 1 := hsecond.2.trans (by norm_num)
    positivity
  unfold symmetricHazard
  rw [div_lt_div_iff₀ hdenomFirst hdenomSecond]
  have hidentity :
      (a * (1 - second) + 2 * second) * (1 + a * (1 - first)) -
          (a * (1 - first) + 2 * first) * (1 + a * (1 - second)) =
        (2 + a) * (second - first) := by ring
  have hcoefficient : 0 < 2 + a := by linarith
  nlinarith [mul_pos hcoefficient (sub_pos.mpr hlt)]

theorem thirdIndifference_strictMonoOn_half
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    StrictMonoOn (thirdIndifference a b) (Set.Icc 0 (1 / 2)) := by
  intro first hfirst second hsecond hlt
  have htlt := symmetricHazard_strictMonoOn_half a ha hfirst hsecond hlt
  have htSecondLe : symmetricHazard a second ≤ 1 := by
    by_cases heq : second = 1 / 2
    · rw [heq, symmetricHazard_half a ha]
    · exact ((symmetricHazard_lt_one_iff a second ha
        (hsecond.2.trans (by norm_num))).mpr
          (lt_of_le_of_ne hsecond.2 heq)).le
  have hcoefficient : 0 < b *
      (2 - symmetricHazard a first - symmetricHazard a second) + 4 / 5 := by
    have hsum : 0 ≤ 2 - symmetricHazard a first -
        symmetricHazard a second := by
      have htFirstLe : symmetricHazard a first ≤ symmetricHazard a second :=
        htlt.le
      nlinarith
    positivity
  have hidentity : thirdIndifference a b second -
      thirdIndifference a b first =
        (symmetricHazard a second - symmetricHazard a first) *
          (b * (2 - symmetricHazard a first - symmetricHazard a second) +
            4 / 5) := by
    unfold thirdIndifference
    ring
  nlinarith [mul_pos (sub_pos.mpr htlt) hcoefficient]

theorem FullRootData.eq_of_third_indifferent
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) (hb : 0 < b)
    {z : ℝ} (hzpos : 0 < z) (hzhalf : z < 1 / 2)
    (hzero : thirdIndifference a b z = 0) :
    z = data.z := by
  have hmono := thirdIndifference_strictMonoOn_half a b ha hb
  have hzmem : z ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hzpos.le, hzhalf.le⟩
  have hdatamem : data.z ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨data.z_pos.le, data.z_lt_half.le⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hmono hzmem hdatamem hlt
    rw [hzero, data.third_indifferent] at this
    exact (lt_irrefl 0 this)
  · have := hmono hdatamem hzmem hgt
    rw [hzero, data.third_indifferent] at this
    exact (lt_irrefl 0 this)

/-- The complete support classification before uniqueness of the positive
scalar zero is invoked. -/
theorem hazardEndpointNash_classification
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hazard : Player → ℝ)
    (hnash : IsHazardEndpointNash a b hazard) :
    (hazard 0 = 0 ∧ hazard 1 = 0 ∧ hazard 2 = 0) ∨
      (hazard 2 = 0 ∧
        hazard 0 = a / (1 + a) ∧ hazard 1 = a / (1 + a)) ∨
      (0 < hazard 2 ∧ hazard 2 < 1 / 2 ∧
        hazard 0 = symmetricHazard a (hazard 2) ∧
        hazard 1 = symmetricHazard a (hazard 2) ∧
        thirdIndifference a b (hazard 2) = 0) := by
  let x := hazard 0
  let y := hazard 1
  let z := hazard 2
  have hx := hnash 0
  have hy := hnash 1
  have hz := hnash 2
  have hg0 : endpointPolynomial a b hazard 0 =
      y - 2 * z - a * (1 - y) * (1 - z) := by
    simp [endpointPolynomial, cap, interaction, y, z, Fin.sum_univ_three,
      show (Finset.univ.erase (0 : Player)) = {1, 2} by decide]
    ring
  have hg1 : endpointPolynomial a b hazard 1 =
      x - 2 * z - a * (1 - x) * (1 - z) := by
    simp [endpointPolynomial, cap, interaction, x, z, Fin.sum_univ_three,
      show (Finset.univ.erase (1 : Player)) = {0, 2} by decide]
    ring
  have hg2 : endpointPolynomial a b hazard 2 =
      (2 / 5 : ℝ) * x + (2 / 5 : ℝ) * y -
        b * (1 - x) * (1 - y) := by
    simp [endpointPolynomial, cap, interaction, x, y, Fin.sum_univ_three,
      show (Finset.univ.erase (2 : Player)) = {0, 1} by decide]
    ring
  rw [hg0] at hx
  rw [hg1] at hy
  rw [hg2] at hz
  let scalar : ScalarEndpointNash a b x y z := {
    x_nonneg := hx.1
    x_le_one := hx.2.1
    y_nonneg := hy.1
    y_le_one := hy.2.1
    z_nonneg := hz.1
    z_le_one := hz.2.1
    x_continue := hx.2.2.1
    x_quit := hx.2.2.2
    y_continue := hy.2.2.1
    y_quit := hy.2.2.2
    z_continue := hz.2.2.1
    z_quit := hz.2.2.2 }
  by_cases hx0 : x = 0
  · obtain ⟨hy0, hz0⟩ := scalar.zero_left ha hb hx0
    left
    exact ⟨hx0, hy0, hz0⟩
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hypos : 0 < y := by
      by_contra hynpos
      have hy0 : y = 0 := le_antisymm (not_lt.mp hynpos) hy.1
      have := scalar.swap.zero_left ha hb hy0
      exact hx0 this.1
    have hxlt : x < 1 := scalar.active_left_lt_one ha hxpos hypos
    have hylt : y < 1 := scalar.swap.active_left_lt_one ha hypos hxpos
    have hg0nonpos : y - 2 * z - a * (1 - y) * (1 - z) ≤ 0 :=
      nonpos_of_mul_nonpos_left
        (by simpa only [mul_comm] using scalar.x_continue) (sub_pos.mpr hxlt)
    have hg0nonneg : 0 ≤ y - 2 * z - a * (1 - y) * (1 - z) :=
      nonneg_of_mul_nonneg_left
        (by simpa only [mul_comm] using scalar.x_quit) hxpos
    have hg0 : y - 2 * z - a * (1 - y) * (1 - z) = 0 :=
      le_antisymm hg0nonpos hg0nonneg
    have hg1nonpos : x - 2 * z - a * (1 - x) * (1 - z) ≤ 0 :=
      nonpos_of_mul_nonpos_left
        (by simpa only [mul_comm] using scalar.y_continue) (sub_pos.mpr hylt)
    have hg1nonneg : 0 ≤ x - 2 * z - a * (1 - x) * (1 - z) :=
      nonneg_of_mul_nonneg_left
        (by simpa only [mul_comm] using scalar.y_quit) hypos
    have hg1 : x - 2 * z - a * (1 - x) * (1 - z) = 0 :=
      le_antisymm hg1nonpos hg1nonneg
    have hdenom : 0 < 1 + a * (1 - z) := by
      have hzle := hz.2.1
      positivity
    have hxy : x = y := by
      have hfactor : (y - x) * (1 + a * (1 - z)) = 0 := by
        calc
          (y - x) * (1 + a * (1 - z)) =
              (y - 2 * z - a * (1 - y) * (1 - z)) -
                (x - 2 * z - a * (1 - x) * (1 - z)) := by ring
          _ = 0 := by rw [hg0, hg1]; ring
      exact (sub_eq_zero.mp
        ((mul_eq_zero.mp hfactor).resolve_right hdenom.ne')).symm
    have hyformula : y = symmetricHazard a z := by
      unfold symmetricHazard
      rw [eq_div_iff hdenom.ne']
      nlinarith [hg0]
    have hxformula : x = symmetricHazard a z := hxy.trans hyformula
    by_cases hz0 : z = 0
    · right; left
      refine ⟨hz0, ?_, ?_⟩
      · change x = a / (1 + a)
        rw [hxformula, hz0, symmetricHazard_zero]
      · change y = a / (1 + a)
        rw [hyformula, hz0, symmetricHazard_zero]
    · right; right
      have hzpos : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
      have hzlt : z < 1 := by
        have htlt : symmetricHazard a z < 1 := by simpa [← hxformula]
        by_contra h
        have : 1 ≤ z := not_lt.mp h
        unfold symmetricHazard at htlt
        rw [div_lt_one hdenom] at htlt
        nlinarith
      have hg2nonneg : 0 ≤ (2 / 5 : ℝ) * x + (2 / 5 : ℝ) * y -
          b * (1 - x) * (1 - y) :=
        by nlinarith [hz.2.2.2]
      have hg2nonpos : (2 / 5 : ℝ) * x + (2 / 5 : ℝ) * y -
          b * (1 - x) * (1 - y) ≤ 0 :=
        nonpos_of_mul_nonpos_left
          (by simpa only [mul_comm] using hz.2.2.1) (sub_pos.mpr hzlt)
      have hzhalf : z < 1 / 2 := by
        have htlt : symmetricHazard a z < 1 := by simpa [← hxformula]
        exact (symmetricHazard_lt_one_iff a z ha hz.2.1).mp htlt
      refine ⟨hzpos, hzhalf, hxformula, hyformula, ?_⟩
      apply thirdIndifference_eq_zero_of_symmetric_gain_eq_zero
      simpa only [hxformula, hyformula] using
        (le_antisymm hg2nonpos hg2nonneg)

theorem isHazardEndpointNash_hazardOfRoot_of_isZeroNash
    (a b : ℝ) (other : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (cap a b) 0 other) :
    IsHazardEndpointNash a b (hazardOfRoot other) := by
  let hazard := hazardOfRoot other
  have hroot : root hazard (hazardOfRoot_nonneg other)
      (hazardOfRoot_le_one other) = other :=
    rootOfHazard_hazardOfRoot other
  have hnashRoot : IsεQuittingRootNash reward (cap a b) 0
      (root hazard (hazardOfRoot_nonneg other)
        (hazardOfRoot_le_one other)) := by
    rw [hroot]
    exact hnash
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward
      (cap a b) _).2 hnashRoot
  intro who
  have hwho := hendpoint who
  rw [endpointDifference_eq_endpointPolynomial] at hwho
  refine ⟨hazardOfRoot_nonneg other who, hazardOfRoot_le_one other who, ?_, ?_⟩
  · simpa only [hazard, root_false, sub_zero] using hwho.1
  · simpa only [hazard, root_true, neg_zero, zero_le] using hwho.2

theorem hazardOfRoot_classification_of_isZeroNash
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (other : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (cap a b) 0 other) :
    (hazardOfRoot other 0 = 0 ∧ hazardOfRoot other 1 = 0 ∧
        hazardOfRoot other 2 = 0) ∨
      (hazardOfRoot other 2 = 0 ∧
        hazardOfRoot other 0 = a / (1 + a) ∧
        hazardOfRoot other 1 = a / (1 + a)) ∨
      (0 < hazardOfRoot other 2 ∧ hazardOfRoot other 2 < 1 / 2 ∧
        hazardOfRoot other 0 = symmetricHazard a (hazardOfRoot other 2) ∧
        hazardOfRoot other 1 = symmetricHazard a (hazardOfRoot other 2) ∧
        thirdIndifference a b (hazardOfRoot other 2) = 0) :=
  hazardEndpointNash_classification a b ha hb (hazardOfRoot other)
    (isHazardEndpointNash_hazardOfRoot_of_isZeroNash a b other hnash)

namespace FullRootData

def hazard {a b : ℝ} (data : FullRootData a b) : Player → ℝ :=
  ![data.t, data.t, data.z]

theorem hazard_nonneg {a b : ℝ} (data : FullRootData a b) (ha : 0 < a)
    (who : Player) : 0 ≤ data.hazard who := by
  fin_cases who <;> simp [hazard, (data.t_pos ha).le, data.z_pos.le]

theorem hazard_le_one {a b : ℝ} (data : FullRootData a b) (ha : 0 < a)
    (who : Player) : data.hazard who ≤ 1 := by
  have hz : data.z < 1 := data.z_lt_half.trans (by norm_num)
  fin_cases who <;> simp [hazard, (data.t_lt_one ha).le, hz.le]

def productRoot {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    Player → PMF Bool :=
  root data.hazard (data.hazard_nonneg ha) (data.hazard_le_one ha)

theorem endpointPolynomial_eq_zero
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) (who : Player) :
    endpointPolynomial a b data.hazard who = 0 := by
  have hdenom := data.denominator_pos ha
  fin_cases who
  · simp [endpointPolynomial, hazard, cap, interaction, Fin.sum_univ_three,
      show (Finset.univ.erase (0 : Player)) = {1, 2} by decide]
    unfold t symmetricHazard
    field_simp [hdenom.ne']
    ring
  · simp [endpointPolynomial, hazard, cap, interaction, Fin.sum_univ_three,
      show (Finset.univ.erase (1 : Player)) = {0, 2} by decide]
    unfold t symmetricHazard
    field_simp [hdenom.ne']
    ring
  · simp [endpointPolynomial, hazard, cap, interaction, Fin.sum_univ_three,
      show (Finset.univ.erase (2 : Player)) = {0, 1} by decide]
    linarith [data.balance]

theorem productRoot_exactNash
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    IsεQuittingRootNash reward (cap a b) 0 (data.productRoot ha) := by
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro who
  unfold productRoot
  rw [endpointDifference_eq_endpointPolynomial]
  rw [data.endpointPolynomial_eq_zero ha who]
  simp

theorem productRoot_successorPayoff
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    quittingRootSuccessorPayoff reward (cap a b) (data.productRoot ha) =
      cap ((1 / 2 : ℝ) * a * (1 - data.t) * (1 - data.z))
        ((1 / 2 : ℝ) * b * (1 - data.t) ^ 2) := by
  have hhazard : hazardOfRoot (data.productRoot ha) = data.hazard := by
    unfold productRoot root
    exact hazardOfRoot_rootOfHazard _ _ _
  funext who
  fin_cases who
  · have hendpoint := data.endpointPolynomial_eq_zero ha (0 : Player)
    simp [endpointPolynomial, FullRootData.hazard, cap, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (0 : Player)) = {1, 2} by decide] at hendpoint
    rw [quittingRootSuccessorPayoff,
      quittingRootExpectedPayoff_eq_sum_coalitionMass]
    rw [show (Finset.univ : Finset (Finset Player)) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    rw [hhazard]
    simp +decide [coalitionMass, quittingStageCoalitionPayoff, reward, cap,
      passive, interaction, FullRootData.hazard, Fin.prod_univ_three,
      show ({0} : Finset Player)ᶜ = {1, 2} by decide,
      show ({1} : Finset Player)ᶜ = {0, 2} by decide,
      show ({2} : Finset Player)ᶜ = {0, 1} by decide,
      show ({0, 1} : Finset Player).erase 1 = {0} by decide]
    ring_nf at hendpoint ⊢
    linear_combination (data.t - 1 / 2) * hendpoint
  · have hendpoint := data.endpointPolynomial_eq_zero ha (1 : Player)
    simp [endpointPolynomial, FullRootData.hazard, cap, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (1 : Player)) = {0, 2} by decide] at hendpoint
    rw [quittingRootSuccessorPayoff,
      quittingRootExpectedPayoff_eq_sum_coalitionMass]
    rw [show (Finset.univ : Finset (Finset Player)) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    rw [hhazard]
    simp +decide [coalitionMass, quittingStageCoalitionPayoff, reward, cap,
      passive, interaction, FullRootData.hazard, Fin.prod_univ_three,
      show ({0} : Finset Player)ᶜ = {1, 2} by decide,
      show ({1} : Finset Player)ᶜ = {0, 2} by decide,
      show ({2} : Finset Player)ᶜ = {0, 1} by decide,
      show ({0, 1} : Finset Player).erase 1 = {0} by decide]
    ring_nf at hendpoint ⊢
    linear_combination (data.t - 1 / 2) * hendpoint
  · have hendpoint := data.endpointPolynomial_eq_zero ha (2 : Player)
    simp [endpointPolynomial, FullRootData.hazard, cap, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (2 : Player)) = {0, 1} by decide] at hendpoint
    rw [quittingRootSuccessorPayoff,
      quittingRootExpectedPayoff_eq_sum_coalitionMass]
    rw [show (Finset.univ : Finset (Finset Player)) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    rw [hhazard]
    simp +decide [coalitionMass, quittingStageCoalitionPayoff, reward, cap,
      passive, interaction, FullRootData.hazard, Fin.prod_univ_three,
      show ({0} : Finset Player)ᶜ = {1, 2} by decide,
      show ({1} : Finset Player)ᶜ = {0, 2} by decide,
      show ({2} : Finset Player)ᶜ = {0, 1} by decide,
      show ({0, 1} : Finset Player).erase 1 = {0} by decide]
    ring_nf at hendpoint ⊢
    linear_combination (data.z - 1 / 2) * hendpoint

end FullRootData

theorem quittingRootAbsorptionMass_eq_hazardOfRoot_finThree
    (other : Player → PMF Bool) :
    quittingRootAbsorptionMass other =
      1 - (1 - hazardOfRoot other 0) * (1 - hazardOfRoot other 1) *
        (1 - hazardOfRoot other 2) := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [Fin.prod_univ_three, hazardOfRoot, pmfBool_false_toReal]

theorem FullRootData.productRoot_maximal
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) (hb : 0 < b)
    (other : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (cap a b) 0 other) :
    quittingRootAbsorptionMass other ≤
      quittingRootAbsorptionMass (data.productRoot ha) := by
  have hselectedHazard : hazardOfRoot (data.productRoot ha) = data.hazard := by
    exact hazardOfRoot_rootOfHazard _ _ _
  rcases hazardOfRoot_classification_of_isZeroNash a b ha hb other hnash with
      hall | hpair | hfull
  · rw [quittingRootAbsorptionMass_eq_hazardOfRoot_finThree,
      hall.1, hall.2.1, hall.2.2]
    simpa using quittingRootAbsorptionMass_nonneg (data.productRoot ha)
  · rw [quittingRootAbsorptionMass_eq_hazardOfRoot_finThree,
      quittingRootAbsorptionMass_eq_hazardOfRoot_finThree]
    rw [hpair.1, hpair.2.1, hpair.2.2, hselectedHazard]
    simp only [FullRootData.hazard]
    simp
    have hzeroMem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := by norm_num
    have hzMem : data.z ∈ Set.Icc (0 : ℝ) (1 / 2) :=
      ⟨data.z_pos.le, data.z_lt_half.le⟩
    have htStrict := symmetricHazard_strictMonoOn_half a ha hzeroMem hzMem
      data.z_pos
    rw [symmetricHazard_zero] at htStrict
    have hpairNonneg : 0 ≤ 1 - a / (1 + a) := by
      have hdenom : 0 < 1 + a := by linarith
      rw [sub_nonneg, div_le_one hdenom]
      linarith
    have hselectedNonneg : 0 ≤ 1 - data.t :=
      sub_nonneg.mpr (data.t_lt_one ha).le
    have hsquare : (1 - data.t) ^ 2 ≤ (1 - a / (1 + a)) ^ 2 :=
      (sq_le_sq₀ hselectedNonneg hpairNonneg).2 (by
        unfold FullRootData.t
        linarith)
    have hzfactor : 0 ≤ 1 - data.z :=
      sub_nonneg.mpr (data.z_lt_half.trans (by norm_num)).le
    have hzfactorLe : 1 - data.z ≤ 1 := by linarith [data.z_pos]
    have hfirst : (1 - data.t) ^ 2 * (1 - data.z) ≤
        (1 - data.t) ^ 2 := by
      nlinarith [sq_nonneg (1 - data.t)]
    nlinarith
  · obtain ⟨hzpos, hzhalf, hx, hy, hzero⟩ := hfull
    have hzEq := data.eq_of_third_indifferent ha hb hzpos hzhalf hzero
    rw [quittingRootAbsorptionMass_eq_hazardOfRoot_finThree,
      quittingRootAbsorptionMass_eq_hazardOfRoot_finThree,
      hselectedHazard]
    simp only [FullRootData.hazard]
    simp
    rw [hx, hy, hzEq]
    simp [FullRootData.t]

theorem FullRootData.pairAbsorption_lt
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) :
    1 - (1 - a / (1 + a)) ^ 2 <
      quittingRootAbsorptionMass (data.productRoot ha) := by
  rw [quittingRootAbsorptionMass_eq_hazardOfRoot_finThree]
  have hselectedHazard : hazardOfRoot (data.productRoot ha) = data.hazard :=
    hazardOfRoot_rootOfHazard _ _ _
  rw [hselectedHazard]
  simp [FullRootData.hazard]
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := by norm_num
  have hzMem : data.z ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨data.z_pos.le, data.z_lt_half.le⟩
  have htStrict := symmetricHazard_strictMonoOn_half a ha hzeroMem hzMem
    data.z_pos
  rw [symmetricHazard_zero] at htStrict
  have hpairNonneg : 0 ≤ 1 - a / (1 + a) := by
    have hdenom : 0 < 1 + a := by linarith
    rw [sub_nonneg, div_le_one hdenom]
    linarith
  have hselectedNonneg : 0 ≤ 1 - data.t :=
    sub_nonneg.mpr (data.t_lt_one ha).le
  have hsquare : (1 - data.t) ^ 2 < (1 - a / (1 + a)) ^ 2 :=
    (sq_lt_sq₀ hselectedNonneg hpairNonneg).2 (by
      unfold FullRootData.t
      linarith)
  have hzfactor : 0 ≤ 1 - data.z :=
    sub_nonneg.mpr (data.z_lt_half.trans (by norm_num)).le
  have hzfactorLe : 1 - data.z ≤ 1 := by linarith [data.z_pos]
  have hfirst : (1 - data.t) ^ 2 * (1 - data.z) ≤
      (1 - data.t) ^ 2 := by
    nlinarith [sq_nonneg (1 - data.t)]
  nlinarith

theorem FullRootData.eq_productRoot_of_absorption_ge
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) (hb : 0 < b)
    (other : Player → PMF Bool)
    (hnash : IsεQuittingRootNash reward (cap a b) 0 other)
    (hge : quittingRootAbsorptionMass (data.productRoot ha) ≤
      quittingRootAbsorptionMass other) :
    other = data.productRoot ha := by
  rcases hazardOfRoot_classification_of_isZeroNash a b ha hb other hnash with
      hall | hpair | hfull
  · have hotherZero : quittingRootAbsorptionMass other = 0 := by
      rw [quittingRootAbsorptionMass_eq_hazardOfRoot_finThree,
        hall.1, hall.2.1, hall.2.2]
      norm_num
    have hquit := quitProbability_le_quittingRootAbsorptionMass
      (data.productRoot ha) (2 : Player)
    have htrue : ((data.productRoot ha (2 : Player)) true).toReal = data.z := by
      simp [FullRootData.productRoot, FullRootData.hazard, root]
    rw [htrue] at hquit
    rw [hotherZero] at hge
    linarith [data.z_pos]
  · have hotherPair : quittingRootAbsorptionMass other =
        1 - (1 - a / (1 + a)) ^ 2 := by
      rw [quittingRootAbsorptionMass_eq_hazardOfRoot_finThree,
        hpair.1, hpair.2.1, hpair.2.2]
      ring
    rw [hotherPair] at hge
    exact False.elim (not_lt_of_ge hge (data.pairAbsorption_lt ha))
  · obtain ⟨hzpos, hzhalf, hx, hy, hzero⟩ := hfull
    have hzEq := data.eq_of_third_indifferent ha hb hzpos hzhalf hzero
    have hhazard : hazardOfRoot other = data.hazard := by
      funext who
      fin_cases who
      · simpa [FullRootData.hazard, FullRootData.t, hzEq] using hx
      · simpa [FullRootData.hazard, FullRootData.t, hzEq] using hy
      · simpa [FullRootData.hazard] using hzEq
    rw [← rootOfHazard_hazardOfRoot other]
    unfold FullRootData.productRoot root
    congr

theorem FullRootData.maximalAbsorptionCapRoot_eq
    {a b : ℝ} (data : FullRootData a b) (ha : 0 < a) (hb : 0 < b) :
    quittingMaximalAbsorptionCapRoot reward (cap a b) = data.productRoot ha := by
  let selected := quittingMaximalAbsorptionCapRoot reward (cap a b)
  have hnash : IsεQuittingRootNash reward (cap a b) 0 selected :=
    quittingMaximalAbsorptionCapRoot_exactNash reward (cap a b)
  have hge : quittingRootAbsorptionMass (data.productRoot ha) ≤
      quittingRootAbsorptionMass selected :=
    quittingMaximalAbsorptionCapRoot_maximal reward (cap a b)
      (data.productRoot ha) (data.productRoot_exactNash ha)
  exact data.eq_productRoot_of_absorption_ge ha hb selected hnash hge

/-! ## Actual recurrence selected inside a quantitative invariant cone -/

/-- One state of the explicit scalar recurrence.  The strengthened lower
bound pays in advance for every future ratio loss, so it is locally
preserved. -/
structure ConeState (d : ℝ) where
  a : ℝ
  b : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  a_le_initial : a ≤ d
  ratio_upper : b / a ≤ 1
  ratio_budget : 1 - 5 * d + 5 * b ≤ b / a

def initialConeState (d : ℝ) (hd : 0 < d) : ConeState d where
  a := d
  b := d
  a_pos := hd
  b_pos := hd
  a_le_initial := le_rfl
  ratio_upper := by
    simp [hd.ne']
  ratio_budget := by
    field_simp [hd.ne']
    linarith

namespace ConeState

def fullRootData {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) : FullRootData state.a state.b :=
  Classical.choice (nonempty_fullRootData state.a state.b state.a_pos
    (state.a_le_initial.trans_lt (hd_small.trans (by norm_num)))
    (by
      have hlower : (9 / 10 : ℝ) < 1 - 5 * d + 5 * state.b := by
        nlinarith [state.b_pos]
      exact hlower.trans_le state.ratio_budget))

def nextA {d : ℝ} (state : ConeState d) (hd_small : d < 1 / 50) : ℝ :=
  (1 / 2 : ℝ) * state.a * (1 - (state.fullRootData hd_small).t) *
    (1 - (state.fullRootData hd_small).z)

def nextB {d : ℝ} (state : ConeState d) (hd_small : d < 1 / 50) : ℝ :=
  (1 / 2 : ℝ) * state.b * (1 - (state.fullRootData hd_small).t) ^ 2

theorem nextA_pos {d : ℝ} (state : ConeState d) (hd_small : d < 1 / 50) :
    0 < state.nextA hd_small := by
  unfold nextA
  have ht := (state.fullRootData hd_small).t_lt_one state.a_pos
  have hz := (state.fullRootData hd_small).z_lt_half.trans
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  exact mul_pos
    (mul_pos (mul_pos hhalf state.a_pos) (sub_pos.mpr ht))
    (sub_pos.mpr hz)

theorem nextB_pos {d : ℝ} (state : ConeState d) (hd_small : d < 1 / 50) :
    0 < state.nextB hd_small := by
  unfold nextB
  have ht := (state.fullRootData hd_small).t_lt_one state.a_pos
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  exact mul_pos (mul_pos hhalf state.b_pos)
    (sq_pos_of_pos (sub_pos.mpr ht))

theorem nextA_lt_half {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) :
    state.nextA hd_small < state.a / 2 := by
  unfold nextA
  have ht0 := (state.fullRootData hd_small).t_pos state.a_pos
  have ht1 := (state.fullRootData hd_small).t_lt_one state.a_pos
  have hz0 := (state.fullRootData hd_small).z_pos
  have hz1 := (state.fullRootData hd_small).z_lt_half.trans
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hproduct : (1 - (state.fullRootData hd_small).t) *
      (1 - (state.fullRootData hd_small).z) < 1 := by
    nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hz1)]
  have htwo : (0 : ℝ) < 2 := by norm_num
  calc
    (1 / 2 : ℝ) * state.a * (1 - (state.fullRootData hd_small).t) *
        (1 - (state.fullRootData hd_small).z) =
        (state.a / 2) * ((1 - (state.fullRootData hd_small).t) *
          (1 - (state.fullRootData hd_small).z)) := by ring
    _ < (state.a / 2) * 1 :=
      mul_lt_mul_of_pos_left hproduct (div_pos state.a_pos htwo)
    _ = state.a / 2 := by ring

theorem nextB_le_half {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) :
    state.nextB hd_small ≤ state.b / 2 := by
  unfold nextB
  have ht0 := (state.fullRootData hd_small).t_pos state.a_pos
  have ht1 := (state.fullRootData hd_small).t_lt_one state.a_pos
  have hsquare : (1 - (state.fullRootData hd_small).t) ^ 2 ≤ 1 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsquare state.b_pos.le]

theorem next_ratio_eq {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) :
    state.nextB hd_small / state.nextA hd_small =
      (state.b / state.a) *
        ((1 - (state.fullRootData hd_small).t) /
          (1 - (state.fullRootData hd_small).z)) := by
  have ha : state.a ≠ 0 := state.a_pos.ne'
  have ht : 1 - (state.fullRootData hd_small).t ≠ 0 :=
    (sub_pos.mpr ((state.fullRootData hd_small).t_lt_one state.a_pos)).ne'
  have hz : 1 - (state.fullRootData hd_small).z ≠ 0 :=
    (sub_pos.mpr ((state.fullRootData hd_small).z_lt_half.trans
      (by norm_num))).ne'
  unfold nextA nextB
  field_simp [ha, ht, hz]

theorem ratio_factor_nonneg {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) :
    0 ≤ (1 - (state.fullRootData hd_small).t) /
      (1 - (state.fullRootData hd_small).z) := by
  exact div_nonneg
    (sub_nonneg.mpr ((state.fullRootData hd_small).t_lt_one state.a_pos).le)
    (sub_nonneg.mpr ((state.fullRootData hd_small).z_lt_half.trans
      (by norm_num)).le)

theorem ratio_factor_le_one {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) :
    (1 - (state.fullRootData hd_small).t) /
        (1 - (state.fullRootData hd_small).z) ≤ 1 := by
  rw [div_le_one (sub_pos.mpr
    ((state.fullRootData hd_small).z_lt_half.trans (by norm_num)))]
  linarith [(state.fullRootData hd_small).z_lt_t state.a_pos]

theorem ratio_loss_le {d : ℝ} (state : ConeState d)
    (hd_small : d < 1 / 50) :
    state.b / state.a - state.nextB hd_small / state.nextA hd_small ≤
      (5 / 2 : ℝ) * state.b := by
  rw [state.next_ratio_eq hd_small]
  let data := state.fullRootData hd_small
  have hr0 : 0 ≤ state.b / state.a :=
    div_nonneg state.b_pos.le state.a_pos.le
  have hdenom : 0 < 1 - data.z :=
    sub_pos.mpr (data.z_lt_half.trans (by norm_num))
  have hu0 : 0 ≤ (data.t - data.z) / (1 - data.z) :=
    div_nonneg (sub_nonneg.mpr (data.z_lt_t state.a_pos).le) hdenom.le
  have hdenomHalf : (1 / 2 : ℝ) < 1 - data.z := by
    linarith [data.z_lt_half]
  have hu_le : (data.t - data.z) / (1 - data.z) ≤ 2 * data.t := by
    rw [div_le_iff₀ hdenom]
    have ht0 := data.t_pos state.a_pos
    have hzfactor : 0 < 1 - 2 * data.z := by linarith [data.z_lt_half]
    have hpositive : 0 < data.t * (1 - 2 * data.z) + data.z :=
      add_pos (mul_pos ht0 hzfactor) data.z_pos
    nlinarith [hpositive]
  have ht_le := data.t_le_five_fourths_b state.a_pos state.b_pos
  have hrewrite : 1 - (1 - data.t) / (1 - data.z) =
      (data.t - data.z) / (1 - data.z) := by
    field_simp [hdenom.ne']
    ring
  have hrule : (state.b / state.a) *
      ((data.t - data.z) / (1 - data.z)) ≤
        (data.t - data.z) / (1 - data.z) :=
    mul_le_of_le_one_left hu0 state.ratio_upper
  calc
    state.b / state.a -
        state.b / state.a * ((1 - data.t) / (1 - data.z)) =
        (state.b / state.a) *
          (1 - (1 - data.t) / (1 - data.z)) := by ring
    _ = (state.b / state.a) *
        ((data.t - data.z) / (1 - data.z)) := by rw [hrewrite]
    _ ≤ (data.t - data.z) / (1 - data.z) := hrule
    _ ≤ 2 * data.t := hu_le
    _ ≤ (5 / 2 : ℝ) * state.b := by linarith

def next {d : ℝ} (state : ConeState d) (hd_small : d < 1 / 50) :
    ConeState d where
  a := state.nextA hd_small
  b := state.nextB hd_small
  a_pos := state.nextA_pos hd_small
  b_pos := state.nextB_pos hd_small
  a_le_initial := (state.nextA_lt_half hd_small).le.trans
    (by linarith [state.a_le_initial, state.a_pos])
  ratio_upper := by
    rw [state.next_ratio_eq hd_small]
    exact (mul_le_of_le_one_left (state.ratio_factor_nonneg hd_small)
      state.ratio_upper).trans
        (by simpa using state.ratio_factor_le_one hd_small)
  ratio_budget := by
    have hloss := state.ratio_loss_le hd_small
    have hbnext := state.nextB_le_half hd_small
    linarith [state.ratio_budget]

end ConeState

def coneOrbit (d : ℝ) (hd : 0 < d) (hd_small : d < 1 / 50) :
    ℕ → ConeState d
  | 0 => initialConeState d hd
  | time + 1 => (coneOrbit d hd hd_small time).next hd_small

@[simp] theorem coneOrbit_zero (d : ℝ) (hd : 0 < d) (hd_small : d < 1 / 50) :
    coneOrbit d hd hd_small 0 = initialConeState d hd := rfl

@[simp] theorem coneOrbit_succ (d : ℝ) (hd : 0 < d) (hd_small : d < 1 / 50)
    (time : ℕ) :
    coneOrbit d hd hd_small (time + 1) =
      (coneOrbit d hd hd_small time).next hd_small := rfl

/-- Scalar recurrence and invariant cone retained by the active orbit.  This
is a checkable recurrence certificate, not a source producer. -/
structure Recurrence where
  a : ℕ → ℝ
  b : ℕ → ℝ
  t : ℕ → ℝ
  z : ℕ → ℝ
  a_pos : ∀ time, 0 < a time
  b_pos : ∀ time, 0 < b time
  t_pos : ∀ time, 0 < t time
  t_lt_one : ∀ time, t time < 1
  z_pos : ∀ time, 0 < z time
  z_lt_t : ∀ time, z time < t time
  t_eq : ∀ time, t time = symmetricHazard (a time) (z time)
  third_indifferent : ∀ time,
    thirdIndifference (a time) (b time) (z time) = 0
  a_succ : ∀ time,
    a (time + 1) = (1 / 2 : ℝ) * a time *
      (1 - t time) * (1 - z time)
  b_succ : ∀ time,
    b (time + 1) = (1 / 2 : ℝ) * b time * (1 - t time) ^ 2
  ratio_lower : ∀ time, (9 / 10 : ℝ) < b time / a time
  ratio_upper : ∀ time, b time / a time ≤ 1
  t_le_five_fourths_b : ∀ time, t time ≤ (5 / 4 : ℝ) * b time

/-- The recurrence generated by the actual IVT-selected scalar root at every
date.  Its cone proof is local and inductive; no infinite sequence is supplied
as a hypothesis. -/
def explicitRecurrence (d : ℝ) (hd : 0 < d) (hd_small : d < 1 / 50) :
    Recurrence where
  a := fun time ↦ (coneOrbit d hd hd_small time).a
  b := fun time ↦ (coneOrbit d hd hd_small time).b
  t := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).t
  z := fun time ↦
    (coneOrbit d hd hd_small time).fullRootData hd_small |>.z
  a_pos := fun time ↦ (coneOrbit d hd hd_small time).a_pos
  b_pos := fun time ↦ (coneOrbit d hd hd_small time).b_pos
  t_pos := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).t_pos
      (coneOrbit d hd hd_small time).a_pos
  t_lt_one := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).t_lt_one
      (coneOrbit d hd hd_small time).a_pos
  z_pos := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).z_pos
  z_lt_t := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).z_lt_t
      (coneOrbit d hd hd_small time).a_pos
  t_eq := fun _ ↦ rfl
  third_indifferent := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).third_indifferent
  a_succ := fun time ↦ rfl
  b_succ := fun time ↦ rfl
  ratio_lower := fun time ↦ by
    have hbudget := (coneOrbit d hd hd_small time).ratio_budget
    have hb := (coneOrbit d hd hd_small time).b_pos
    have hbase : (9 / 10 : ℝ) < 1 - 5 * d + 5 *
        (coneOrbit d hd hd_small time).b := by
      nlinarith
    exact hbase.trans_le hbudget
  ratio_upper := fun time ↦ (coneOrbit d hd hd_small time).ratio_upper
  t_le_five_fourths_b := fun time ↦
    ((coneOrbit d hd hd_small time).fullRootData hd_small).t_le_five_fourths_b
      (coneOrbit d hd hd_small time).a_pos
      (coneOrbit d hd hd_small time).b_pos

@[simp] theorem explicitRecurrence_a_zero
    (d : ℝ) (hd : 0 < d) (hd_small : d < 1 / 50) :
    (explicitRecurrence d hd hd_small).a 0 = d := rfl

@[simp] theorem explicitRecurrence_b_zero
    (d : ℝ) (hd : 0 < d) (hd_small : d < 1 / 50) :
    (explicitRecurrence d hd hd_small).b 0 = d := rfl

namespace Recurrence

/-- Fully mixed active hazard selected by one recurrence row. -/
def hazard (orbit : Recurrence) (time : ℕ) : Player → ℝ :=
  ![orbit.t time, orbit.t time, orbit.z time]

theorem hazard_nonneg (orbit : Recurrence) (time : ℕ) (who : Player) :
    0 ≤ orbit.hazard time who := by
  fin_cases who <;> simp [hazard, (orbit.t_pos time).le,
    (orbit.z_pos time).le]

theorem hazard_le_one (orbit : Recurrence) (time : ℕ) (who : Player) :
    orbit.hazard time who ≤ 1 := by
  have hz : orbit.z time < 1 :=
    (orbit.z_lt_t time).trans (orbit.t_lt_one time)
  fin_cases who <;> simp [hazard, (orbit.t_lt_one time).le, hz.le]

/-- The active product root associated with the recurrence. -/
def productRoot (orbit : Recurrence) (time : ℕ) : Player → PMF Bool :=
  root (orbit.hazard time) (orbit.hazard_nonneg time)
    (orbit.hazard_le_one time)

theorem endpointPolynomial_eq_zero
    (orbit : Recurrence) (time : ℕ) (who : Player) :
    endpointPolynomial (orbit.a time) (orbit.b time)
      (orbit.hazard time) who = 0 := by
  have hzlt : orbit.z time < 1 :=
    (orbit.z_lt_t time).trans (orbit.t_lt_one time)
  have hdenom : 1 + orbit.a time * (1 - orbit.z time) ≠ 0 := by
    have : 0 < 1 + orbit.a time * (1 - orbit.z time) := by
      have hmul : 0 < orbit.a time * (1 - orbit.z time) :=
        mul_pos (orbit.a_pos time) (sub_pos.mpr hzlt)
      linarith
    exact this.ne'
  have hwho : who = 0 ∨ who = 1 ∨ who = 2 := by
    fin_cases who <;> simp
  rcases hwho with rfl | rfl | rfl
  · simp [endpointPolynomial, hazard, cap, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (0 : Player)) = {1, 2} by decide]
    rw [orbit.t_eq]
    unfold symmetricHazard
    field_simp [hdenom]
    ring
  · simp [endpointPolynomial, hazard, cap, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (1 : Player)) = {0, 2} by decide]
    rw [orbit.t_eq]
    unfold symmetricHazard
    field_simp [hdenom]
    ring
  · have hthird := orbit.third_indifferent time
    simp [endpointPolynomial, hazard, cap, interaction,
      Fin.sum_univ_three,
      show (Finset.univ.erase (2 : Player)) = {0, 1} by decide]
    unfold thirdIndifference at hthird
    rw [← orbit.t_eq time] at hthird
    linarith

theorem productRoot_endpointDifference_eq_zero
    (orbit : Recurrence) (time : ℕ) (who : Player) :
    quittingRootEndpointDifference reward (cap (orbit.a time) (orbit.b time))
      (orbit.productRoot time) who = 0 := by
  unfold productRoot
  rw [endpointDifference_eq_endpointPolynomial]
  exact orbit.endpointPolynomial_eq_zero time who

/-- Every recurrence row is an exact root of its displayed cap. -/
theorem productRoot_exactNash (orbit : Recurrence) (time : ℕ) :
    IsεQuittingRootNash reward (cap (orbit.a time) (orbit.b time)) 0
      (orbit.productRoot time) := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  intro who
  rw [quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart,
    orbit.productRoot_endpointDifference_eq_zero time who]
  simp

theorem a_succ_lt_half (orbit : Recurrence) (time : ℕ) :
    orbit.a (time + 1) < orbit.a time / 2 := by
  rw [orbit.a_succ]
  have ht : 0 < 1 - orbit.t time := sub_pos.mpr (orbit.t_lt_one time)
  have hz0 : 0 < 1 - orbit.z time := by
    linarith [orbit.z_lt_t time, orbit.t_lt_one time]
  have ht1 : 1 - orbit.t time < 1 := by linarith [orbit.t_pos time]
  have hz1 : 1 - orbit.z time < 1 := by linarith [orbit.z_pos time]
  have hproduct : (1 - orbit.t time) * (1 - orbit.z time) < 1 := by
    calc
      (1 - orbit.t time) * (1 - orbit.z time) <
          1 * (1 - orbit.z time) :=
        mul_lt_mul_of_pos_right ht1 hz0
      _ < 1 := by simpa using hz1
  calc
    (1 / 2 : ℝ) * orbit.a time * (1 - orbit.t time) *
        (1 - orbit.z time) =
        (orbit.a time / 2) *
          ((1 - orbit.t time) * (1 - orbit.z time)) := by ring
    _ < (orbit.a time / 2) * 1 :=
      mul_lt_mul_of_pos_left hproduct (div_pos (orbit.a_pos time) (by norm_num))
    _ = orbit.a time / 2 := by ring

theorem b_succ_le_half (orbit : Recurrence) (time : ℕ) :
    orbit.b (time + 1) ≤ orbit.b time / 2 := by
  rw [orbit.b_succ]
  have ht0 : 0 ≤ 1 - orbit.t time := (sub_pos.mpr (orbit.t_lt_one time)).le
  have ht1 : 1 - orbit.t time ≤ 1 := by linarith [orbit.t_pos time]
  have hsquare : (1 - orbit.t time) ^ 2 ≤ 1 := by nlinarith
  calc
    (1 / 2 : ℝ) * orbit.b time * (1 - orbit.t time) ^ 2 =
        (orbit.b time / 2) * (1 - orbit.t time) ^ 2 := by ring
    _ ≤ (orbit.b time / 2) * 1 :=
      mul_le_mul_of_nonneg_left hsquare
        (div_nonneg (orbit.b_pos time).le (by norm_num))
    _ = orbit.b time / 2 := by ring

theorem b_le_geometric (orbit : Recurrence) (time : ℕ) :
    orbit.b time ≤ orbit.b 0 * (1 / 2 : ℝ) ^ time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [show time + 1 = Nat.succ time by omega]
      calc
        orbit.b (Nat.succ time) ≤ orbit.b time / 2 := by
          simpa [Nat.succ_eq_add_one] using orbit.b_succ_le_half time
        _ ≤ (orbit.b 0 * (1 / 2 : ℝ) ^ time) / 2 :=
          div_le_div_of_nonneg_right ih (by norm_num)
        _ = orbit.b 0 * (1 / 2 : ℝ) ^ Nat.succ time := by
          rw [pow_succ]
          ring

theorem a_le_geometric (orbit : Recurrence) (time : ℕ) :
    orbit.a time ≤ orbit.a 0 * (1 / 2 : ℝ) ^ time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [show time + 1 = Nat.succ time by omega]
      calc
        orbit.a (Nat.succ time) ≤ orbit.a time / 2 := by
          exact (by simpa [Nat.succ_eq_add_one] using
            (orbit.a_succ_lt_half time).le)
        _ ≤ (orbit.a 0 * (1 / 2 : ℝ) ^ time) / 2 :=
          div_le_div_of_nonneg_right ih (by norm_num)
        _ = orbit.a 0 * (1 / 2 : ℝ) ^ Nat.succ time := by
          rw [pow_succ]
          ring

theorem tendsto_a_zero (orbit : Recurrence) :
    Tendsto orbit.a atTop (nhds 0) := by
  have hbound : ∀ time, ‖orbit.a time‖ ≤
      orbit.a 0 * (1 / 2 : ℝ) ^ time := by
    intro time
    rw [Real.norm_eq_abs, abs_of_pos (orbit.a_pos time)]
    exact orbit.a_le_geometric time
  have hzero : Tendsto (fun time : ℕ ↦
      orbit.a 0 * (1 / 2 : ℝ) ^ time) atTop (nhds 0) := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          (orbit.a 0)
  exact squeeze_zero_norm hbound hzero

theorem tendsto_b_zero (orbit : Recurrence) :
    Tendsto orbit.b atTop (nhds 0) := by
  have hbound : ∀ time, ‖orbit.b time‖ ≤
      orbit.b 0 * (1 / 2 : ℝ) ^ time := by
    intro time
    rw [Real.norm_eq_abs, abs_of_pos (orbit.b_pos time)]
    exact orbit.b_le_geometric time
  have hzero : Tendsto (fun time : ℕ ↦
      orbit.b 0 * (1 / 2 : ℝ) ^ time) atTop (nhds 0) := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          (orbit.b 0)
  exact squeeze_zero_norm hbound hzero

theorem tendsto_t_zero (orbit : Recurrence) :
    Tendsto orbit.t atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun time ↦ (orbit.t_pos time).le
  · exact fun time ↦ orbit.t_le_five_fourths_b time
  · simpa using orbit.tendsto_b_zero.const_mul (5 / 4 : ℝ)

theorem tendsto_z_zero (orbit : Recurrence) :
    Tendsto orbit.z atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun time ↦ (orbit.z_pos time).le
  · exact fun time ↦ (orbit.z_lt_t time).le
  · exact orbit.tendsto_t_zero

theorem ratio_succ (orbit : Recurrence) (time : ℕ) :
    orbit.b (time + 1) / orbit.a (time + 1) =
      (orbit.b time / orbit.a time) *
        ((1 - orbit.t time) / (1 - orbit.z time)) := by
  rw [orbit.a_succ, orbit.b_succ]
  have ha := (orbit.a_pos time).ne'
  have ht := (sub_pos.mpr (orbit.t_lt_one time)).ne'
  have hz := (sub_pos.mpr
    ((orbit.z_lt_t time).trans (orbit.t_lt_one time))).ne'
  field_simp [ha, ht, hz]

theorem ratio_antitone (orbit : Recurrence) :
    Antitone (fun time ↦ orbit.b time / orbit.a time) := by
  apply antitone_nat_of_succ_le
  intro time
  rw [orbit.ratio_succ]
  have hratio0 : 0 ≤ orbit.b time / orbit.a time :=
    div_nonneg (orbit.b_pos time).le (orbit.a_pos time).le
  have hdenom : 0 < 1 - orbit.z time :=
    sub_pos.mpr ((orbit.z_lt_t time).trans (orbit.t_lt_one time))
  have hfactor : (1 - orbit.t time) / (1 - orbit.z time) ≤ 1 := by
    rw [div_le_one hdenom]
    linarith [orbit.z_lt_t time]
  exact mul_le_of_le_one_right hratio0 hfactor

/-- Limit of the active cap-coordinate ratio. -/
def ratioLimit (orbit : Recurrence) : ℝ :=
  sInf (Set.range fun time ↦ orbit.b time / orbit.a time)

theorem ratio_tendsto (orbit : Recurrence) :
    Tendsto (fun time ↦ orbit.b time / orbit.a time) atTop
      (nhds orbit.ratioLimit) := by
  apply tendsto_atTop_ciInf orbit.ratio_antitone
  exact ⟨0, fun value ⟨time, htime⟩ ↦ by
    rw [← htime]
    exact div_nonneg (orbit.b_pos time).le (orbit.a_pos time).le⟩

theorem ratioLimit_lower (orbit : Recurrence) :
    (9 / 10 : ℝ) ≤ orbit.ratioLimit := by
  exact ge_of_tendsto' orbit.ratio_tendsto fun time ↦
    (orbit.ratio_lower time).le

theorem ratioLimit_upper (orbit : Recurrence) : orbit.ratioLimit ≤ 1 := by
  exact le_of_tendsto' orbit.ratio_tendsto orbit.ratio_upper

theorem t_div_a_eq (orbit : Recurrence) (time : ℕ) :
    orbit.t time / orbit.a time =
      (5 / 4 : ℝ) * (orbit.b time / orbit.a time) *
        (1 - orbit.t time) ^ 2 := by
  have hthird := orbit.third_indifferent time
  have ha := (orbit.a_pos time).ne'
  unfold thirdIndifference at hthird
  rw [← orbit.t_eq time] at hthird
  field_simp [ha]
  nlinarith

theorem t_div_a_tendsto (orbit : Recurrence) :
    Tendsto (fun time ↦ orbit.t time / orbit.a time) atTop
      (nhds ((5 / 4 : ℝ) * orbit.ratioLimit)) := by
  have honeSub : Tendsto (fun time ↦ 1 - orbit.t time) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub orbit.tendsto_t_zero
  have hproduct := (orbit.ratio_tendsto.mul (honeSub.pow 2)).const_mul (5 / 4 : ℝ)
  convert hproduct using 1
  · funext time
    rw [orbit.t_div_a_eq]
    ring
  · norm_num

theorem z_div_a_eq (orbit : Recurrence) (time : ℕ) :
    orbit.z time / orbit.a time =
      (1 / 2 : ℝ) *
        ((orbit.t time / orbit.a time) *
          (1 + orbit.a time * (1 - orbit.z time)) -
            (1 - orbit.z time)) := by
  have ht := orbit.t_eq time
  have ha := (orbit.a_pos time).ne'
  have hdenom : 1 + orbit.a time * (1 - orbit.z time) ≠ 0 := by
    have hz : 0 < 1 - orbit.z time :=
      sub_pos.mpr ((orbit.z_lt_t time).trans (orbit.t_lt_one time))
    have hmul : 0 < orbit.a time * (1 - orbit.z time) :=
      mul_pos (orbit.a_pos time) hz
    linarith
  unfold symmetricHazard at ht
  field_simp [ha, hdenom] at ht ⊢
  nlinarith

theorem z_div_a_tendsto (orbit : Recurrence) :
    Tendsto (fun time ↦ orbit.z time / orbit.a time) atTop
      (nhds ((1 / 2 : ℝ) * ((5 / 4 : ℝ) * orbit.ratioLimit - 1))) := by
  have honeSub : Tendsto (fun time ↦ 1 - orbit.z time) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub orbit.tendsto_z_zero
  have hdenom : Tendsto (fun time ↦
      1 + orbit.a time * (1 - orbit.z time)) atTop (nhds 1) := by
    convert tendsto_const_nhds.add (orbit.tendsto_a_zero.mul honeSub) using 1
    · norm_num
  have hinside := (orbit.t_div_a_tendsto.mul hdenom).sub honeSub
  have hscaled := hinside.const_mul (1 / 2 : ℝ)
  convert hscaled using 1
  · funext time
    exact orbit.z_div_a_eq time
  · ring

/-- The active marginal hazard `2t+z`. -/
def totalHazard (orbit : Recurrence) (time : ℕ) : ℝ :=
  2 * orbit.t time + orbit.z time

theorem totalHazard_pos (orbit : Recurrence) (time : ℕ) :
    0 < orbit.totalHazard time := by
  unfold totalHazard
  linarith [orbit.t_pos time, orbit.z_pos time]

/-- The active total hazard is asymptotic to a positive multiple of `a`. -/
theorem totalHazard_div_a_tendsto (orbit : Recurrence) :
    Tendsto (fun time ↦ orbit.totalHazard time / orbit.a time) atTop
      (nhds ((25 / 8 : ℝ) * orbit.ratioLimit - 1 / 2)) := by
  have hsum := (orbit.t_div_a_tendsto.const_mul 2).add orbit.z_div_a_tendsto
  convert hsum using 1
  · funext time
    unfold totalHazard
    field_simp [(orbit.a_pos time).ne']
  · ring

theorem totalHazard_div_a_limit_pos (orbit : Recurrence) :
    0 < (25 / 8 : ℝ) * orbit.ratioLimit - 1 / 2 := by
  nlinarith [orbit.ratioLimit_lower]

theorem a_succ_div_a_tendsto_half (orbit : Recurrence) :
    Tendsto (fun time ↦ orbit.a (time + 1) / orbit.a time) atTop
      (nhds (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun time ↦ 1 - orbit.t time) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub orbit.tendsto_t_zero
  have hz : Tendsto (fun time ↦ 1 - orbit.z time) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub orbit.tendsto_z_zero
  have hproduct := (ht.mul hz).const_mul (1 / 2 : ℝ)
  convert hproduct using 1
  · funext time
    rw [orbit.a_succ]
    field_simp [(orbit.a_pos time).ne']
  · norm_num

theorem totalHazard_succ_div_tendsto_half (orbit : Recurrence) :
    Tendsto (fun time ↦ orbit.totalHazard (time + 1) /
      orbit.totalHazard time) atTop (nhds (1 / 2 : ℝ)) := by
  let limit := (25 / 8 : ℝ) * orbit.ratioLimit - 1 / 2
  have hscaledNext : Tendsto (fun time ↦
      orbit.totalHazard (time + 1) / orbit.a (time + 1)) atTop
      (nhds limit) := by
    simpa [limit, Function.comp_def, Nat.add_comm] using
      orbit.totalHazard_div_a_tendsto.comp (tendsto_add_atTop_nat 1)
  have hscaled := orbit.totalHazard_div_a_tendsto
  have hquotient := (hscaledNext.mul orbit.a_succ_div_a_tendsto_half).div
    hscaled (orbit.totalHazard_div_a_limit_pos.ne')
  have heq : ∀ time,
      ((orbit.totalHazard (time + 1) / orbit.a (time + 1)) *
          (orbit.a (time + 1) / orbit.a time)) /
            (orbit.totalHazard time / orbit.a time) =
        orbit.totalHazard (time + 1) / orbit.totalHazard time := by
    intro time
    have ha := (orbit.a_pos time).ne'
    have haNext := (orbit.a_pos (time + 1)).ne'
    have htotal := (orbit.totalHazard_pos time).ne'
    field_simp [ha, haNext, htotal]
  have htarget : Tendsto (fun time ↦ orbit.totalHazard (time + 1) /
      orbit.totalHazard time) atTop
      (nhds (limit * (1 / 2 : ℝ) / limit)) :=
    hquotient.congr' (Eventually.of_forall heq)
  have hlimit : limit ≠ 0 := by
    dsimp only [limit]
    exact orbit.totalHazard_div_a_limit_pos.ne'
  have hvalue : limit * (1 / 2 : ℝ) / limit = 1 / 2 := by
    field_simp [hlimit]
  rw [hvalue] at htarget
  exact htarget

/-- A positive summable sequence whose successive ratio tends to one half has
one-half renewal ratio against its remaining tail. -/
theorem tendsto_self_div_tailSum_half_of_ratio
    (f : ℕ → ℝ) (hpos : ∀ time, 0 < f time) (hsum : Summable f)
    (hratio : Tendsto (fun time ↦ f (time + 1) / f time) atTop
      (nhds (1 / 2 : ℝ))) :
    Tendsto (fun time ↦ f time / ∑' offset, f (time + offset)) atTop
      (nhds (1 / 2 : ℝ)) := by
  let normalized : ℕ → ℕ → ℝ := fun time offset ↦
    f (time + offset) / f time
  have hnormalized_succ (time offset : ℕ) :
      normalized time (offset + 1) =
        (f (time + offset + 1) / f (time + offset)) *
          normalized time offset := by
    dsimp only [normalized]
    field_simp [(hpos time).ne', (hpos (time + offset)).ne']
    rw [Nat.add_assoc]
  have hpointwise (offset : ℕ) :
      Tendsto (fun time ↦ normalized time offset) atTop
        (nhds ((1 / 2 : ℝ) ^ offset)) := by
    induction offset with
    | zero =>
        convert (tendsto_const_nhds :
          Tendsto (fun _time : ℕ ↦ (1 : ℝ)) atTop (nhds 1)) using 1
        · funext time
          simp [normalized, (hpos time).ne']
        · norm_num
    | succ offset ih =>
        have hshift : Tendsto (fun time ↦
            f (time + offset + 1) / f (time + offset)) atTop
            (nhds (1 / 2 : ℝ)) := by
          simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
              hratio.comp (tendsto_add_atTop_nat offset)
        simpa [hnormalized_succ, pow_succ, mul_comm] using hshift.mul ih
  have hratioBound : ∀ᶠ time in atTop,
      f (time + 1) / f time ≤ (3 / 4 : ℝ) :=
    ((tendsto_order.1 hratio).2 (3 / 4 : ℝ) (by norm_num)).mono
      fun _ hlt ↦ hlt.le
  obtain ⟨start, hstart⟩ := (eventually_atTop.1 hratioBound)
  have hdominated : ∀ᶠ time in atTop, ∀ offset,
      ‖normalized time offset‖ ≤ (3 / 4 : ℝ) ^ offset := by
    filter_upwards [eventually_ge_atTop start] with time htime
    intro offset
    induction offset with
    | zero => simp [normalized, (hpos time).ne']
    | succ offset ih =>
        rw [hnormalized_succ]
        have hratioNonneg : 0 ≤ f (time + offset + 1) /
            f (time + offset) :=
          div_nonneg (hpos _).le (hpos _).le
        have hratioLe := hstart (time + offset) (by omega)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hratioNonneg]
        rw [pow_succ]
        calc
          f (time + offset + 1) / f (time + offset) *
              |normalized time offset| ≤
              (3 / 4 : ℝ) * (3 / 4 : ℝ) ^ offset :=
            mul_le_mul hratioLe (by simpa [Real.norm_eq_abs] using ih)
              (abs_nonneg _) (by norm_num)
          _ = (3 / 4 : ℝ) ^ offset * (3 / 4 : ℝ) := by ring
  have hgeometric : Summable (fun offset : ℕ ↦ (3 / 4 : ℝ) ^ offset) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hnormalizedTsum : Tendsto (fun time ↦ ∑' offset,
      normalized time offset) atTop
      (nhds (∑' offset : ℕ, (1 / 2 : ℝ) ^ offset)) :=
    tendsto_tsum_of_dominated_convergence hgeometric hpointwise hdominated
  have hgeometricHalf : (∑' offset : ℕ, (1 / 2 : ℝ) ^ offset) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (by norm_num)]
    norm_num
  rw [hgeometricHalf] at hnormalizedTsum
  have htailQuotient : Tendsto (fun time ↦
      (∑' offset, f (time + offset)) / f time) atTop (nhds 2) := by
    apply hnormalizedTsum.congr'
    exact Eventually.of_forall fun time ↦ by
      dsimp only [normalized]
      rw [div_eq_mul_inv, ← tsum_mul_right]
      congr 1
  have hinverse := htailQuotient.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
  have htailPos (time : ℕ) : 0 < ∑' offset, f (time + offset) := by
    have hshift : Summable (fun offset ↦ f (time + offset)) := by
      simpa [Nat.add_comm] using (summable_nat_add_iff time).2 hsum
    have hle := hshift.le_tsum 0 (fun offset _ ↦ (hpos _).le)
    exact (hpos time).trans_le (by simpa using hle)
  have heq (time : ℕ) :
      ((∑' offset, f (time + offset)) / f time)⁻¹ =
        f time / ∑' offset, f (time + offset) := by
    field_simp [(hpos time).ne', (htailPos time).ne']
  have htarget := hinverse.congr'
    (Eventually.of_forall fun time ↦ heq time)
  norm_num at htarget ⊢
  exact htarget

theorem summable_b (orbit : Recurrence) : Summable orbit.b := by
  apply Summable.of_nonneg_of_le (fun time ↦ (orbit.b_pos time).le)
    (orbit.b_le_geometric)
  exact (summable_geometric_of_norm_lt_one (by norm_num :
    ‖(1 / 2 : ℝ)‖ < 1)).mul_left (orbit.b 0)

theorem summable_t (orbit : Recurrence) : Summable orbit.t := by
  apply orbit.summable_b.mul_left (5 / 4 : ℝ) |>.of_nonneg_of_le
  · exact fun time ↦ (orbit.t_pos time).le
  · intro time
    simpa [mul_comm] using orbit.t_le_five_fourths_b time

theorem totalHazard_le_three_t (orbit : Recurrence) (time : ℕ) :
    orbit.totalHazard time ≤ 3 * orbit.t time := by
  unfold totalHazard
  linarith [orbit.z_lt_t time]

theorem summable_totalHazard (orbit : Recurrence) :
    Summable orbit.totalHazard := by
  apply (orbit.summable_t.mul_left 3).of_nonneg_of_le
  · exact fun time ↦ (orbit.totalHazard_pos time).le
  · intro time
    simpa [mul_comm] using orbit.totalHazard_le_three_t time

end Recurrence

end MaximalRayZeroMinimumActiveRegression

end GameTheory
