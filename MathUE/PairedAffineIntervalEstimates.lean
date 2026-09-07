import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact interval estimates for paired affine Bellman maps -/

noncomputable section

namespace Math.PairedAffine

/-- Absorption probability of two independent hazards. -/
def absorption (u v : ℝ) : ℝ := u + v - u * v

/-- Absorbing contribution from two singleton outcomes and their tie. -/
def contribution (left right tie u v : ℝ) : ℝ :=
  u * (1 - v) * left + (1 - u) * v * right + u * v * tie

/-- The affine Bellman map of one independent pair. -/
def bellman (left right tie u v value : ℝ) : ℝ :=
  contribution left right tie u v + (1 - u) * (1 - v) * value

/-- The active player's pure-Quit endpoint. -/
def activeValue (singleton joint h : ℝ) : ℝ :=
  singleton + h * (joint - singleton)

/-- The continuation making the active player indifferent. -/
def postValue (singleton partner joint h : ℝ) : ℝ :=
  singleton + h * (joint - partner) / (1 - h)

def gap (singleton partner joint left right tie h u v : ℝ) : ℝ :=
  postValue singleton partner joint h -
    bellman left right tie u v (activeValue singleton joint h)

structure OwnBounds (singleton partner joint : ℝ) : Prop where
  singleton_lower : 9 / 10 ≤ singleton
  singleton_upper : singleton ≤ 11 / 10
  partner_lower : -(1 / 10) ≤ partner
  partner_upper : partner ≤ 1 / 10
  joint_lower : 19 / 10 ≤ joint
  joint_upper : joint ≤ 21 / 10

structure PassiveBounds (left right tie : ℝ) : Prop where
  left_lower : 19 / 10 ≤ left
  left_upper : left ≤ 21 / 10
  right_lower : 19 / 10 ≤ right
  right_upper : right ≤ 21 / 10
  tie_lower : -(1 / 10) ≤ tie
  tie_upper : tie ≤ 1 / 10

theorem continue_eq_active (singleton partner joint h : ℝ) (hh : h ≠ 1) :
    h * partner + (1 - h) * postValue singleton partner joint h =
      activeValue singleton joint h := by
  unfold postValue activeValue
  field_simp
  ring

theorem prescribed_eq_active (singleton partner joint h own : ℝ) (hh : h ≠ 1) :
    own * activeValue singleton joint h +
        (1 - own) * (h * partner + (1 - h) * postValue singleton partner joint h) =
      activeValue singleton joint h := by
  rw [continue_eq_active singleton partner joint h hh]
  ring

theorem absorption_eq_one_sub (u v : ℝ) :
    absorption u v = 1 - (1 - u) * (1 - v) := by
  unfold absorption
  ring

theorem survival_mem_Icc {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    (1 - u) * (1 - v) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2)
  · nlinarith [hv.1, mul_nonneg hu.1 (sub_nonneg.mpr hv.2)]

theorem monotone_bellman (left right tie : ℝ) {u v : ℝ}
    (hu : u ≤ 1) (hv : v ≤ 1) : Monotone (bellman left right tie u v) := by
  intro first second hle
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hle (mul_nonneg (sub_nonneg.mpr hu)
      (sub_nonneg.mpr hv))) _

theorem bellman_le {left right tie u v value bound : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hleft : left ≤ bound) (hright : right ≤ bound) (htie : tie ≤ bound)
    (hvalue : value ≤ bound) : bellman left right tie u v value ≤ bound := by
  have hl := mul_le_mul_of_nonneg_left hleft (mul_nonneg hu.1 (sub_nonneg.mpr hv.2))
  have hr := mul_le_mul_of_nonneg_left hright (mul_nonneg (sub_nonneg.mpr hu.2) hv.1)
  have ht := mul_le_mul_of_nonneg_left htie (mul_nonneg hu.1 hv.1)
  have hc := mul_le_mul_of_nonneg_left hvalue (survival_mem_Icc hu hv).1
  unfold bellman contribution
  nlinarith

theorem active_gt_singleton {singleton partner joint h : ℝ}
    (hown : OwnBounds singleton partner joint) (hh : 0 < h) :
    singleton < activeValue singleton joint h := by
  have hj : 0 < joint - singleton := by
    linarith [hown.joint_lower, hown.singleton_upper]
  exact lt_add_of_pos_right _ (mul_pos hh hj)

theorem active_le_eight_fifths {singleton partner joint h : ℝ}
    (hown : OwnBounds singleton partner joint) (hh : h ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    activeValue singleton joint h ≤ 8 / 5 := by
  have hj : 0 ≤ joint - singleton := by
    linarith [hown.joint_lower, hown.singleton_upper]
  have hmul := mul_le_mul_of_nonneg_right hh.2 hj
  unfold activeValue
  linarith [hown.singleton_upper, hown.joint_upper]

theorem post_upper_face_ge {singleton partner joint : ℝ}
    (hown : OwnBounds singleton partner joint) :
    27 / 10 ≤ postValue singleton partner joint (1 / 2) := by
  unfold postValue
  norm_num
  linarith [hown.singleton_lower, hown.partner_upper, hown.joint_lower]

theorem gap_eq_coefficients (singleton partner joint left right tie h u v : ℝ) :
    gap singleton partner joint left right tie h u v =
      (1 - (1 - u) * (1 - v) * (1 - h)) * singleton +
        (h / (1 - h) - (1 - u) * (1 - v) * h) * joint -
        (h / (1 - h)) * partner - contribution left right tie u v := by
  unfold gap postValue bellman activeValue
  ring

private theorem gap_coefficient_nonneg {h u v : ℝ}
    (hh : h ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ 1 - (1 - u) * (1 - v) * (1 - h) ∧
      0 ≤ h / (1 - h) - (1 - u) * (1 - v) * h ∧
      0 ≤ h / (1 - h) := by
  have hc := survival_mem_Icc hu hv
  have hd : 0 < 1 - h := sub_pos.mpr hh.2
  have hprod := mul_le_mul_of_nonneg_left (show 1 - h ≤ 1 by linarith [hh.1]) hc.1
  have hdiv : h ≤ h / (1 - h) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg h]
  have hch := mul_le_mul_of_nonneg_right hc.2 hh.1
  exact ⟨by nlinarith [hc.2], by nlinarith, div_nonneg hh.1 hd.le⟩

theorem gap_le_reward_corner {singleton partner joint left right tie h u v : ℝ}
    (hown : OwnBounds singleton partner joint) (hpassive : PassiveBounds left right tie)
    (hh : h ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    gap singleton partner joint left right tie h u v ≤
      gap (11 / 10) (-(1 / 10)) (21 / 10) (19 / 10) (19 / 10) (-(1 / 10)) h u v := by
  rw [gap_eq_coefficients, gap_eq_coefficients]
  obtain ⟨hs, hj, hb⟩ := gap_coefficient_nonneg hh hu hv
  have hs' := mul_le_mul_of_nonneg_left hown.singleton_upper hs
  have hj' := mul_le_mul_of_nonneg_left hown.joint_upper hj
  have hb' := mul_le_mul_of_nonneg_left hown.partner_lower hb
  have hl := mul_le_mul_of_nonneg_left hpassive.left_lower
    (mul_nonneg hu.1 (sub_nonneg.mpr hv.2))
  have hr := mul_le_mul_of_nonneg_left hpassive.right_lower
    (mul_nonneg (sub_nonneg.mpr hu.2) hv.1)
  have ht := mul_le_mul_of_nonneg_left hpassive.tie_lower (mul_nonneg hu.1 hv.1)
  unfold contribution
  linarith

theorem reward_corner_le_gap {singleton partner joint left right tie h u v : ℝ}
    (hown : OwnBounds singleton partner joint) (hpassive : PassiveBounds left right tie)
    (hh : h ∈ Set.Ico (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    gap (9 / 10) (1 / 10) (19 / 10) (21 / 10) (21 / 10) (1 / 10) h u v ≤
      gap singleton partner joint left right tie h u v := by
  rw [gap_eq_coefficients, gap_eq_coefficients]
  obtain ⟨hs, hj, hb⟩ := gap_coefficient_nonneg hh hu hv
  have hs' := mul_le_mul_of_nonneg_left hown.singleton_lower hs
  have hj' := mul_le_mul_of_nonneg_left hown.joint_lower hj
  have hb' := mul_le_mul_of_nonneg_left hown.partner_upper hb
  have hl := mul_le_mul_of_nonneg_left hpassive.left_upper
    (mul_nonneg hu.1 (sub_nonneg.mpr hv.2))
  have hr := mul_le_mul_of_nonneg_left hpassive.right_upper
    (mul_nonneg (sub_nonneg.mpr hu.2) hv.1)
  have ht := mul_le_mul_of_nonneg_left hpassive.tie_upper (mul_nonneg hu.1 hv.1)
  unfold contribution
  linarith

private theorem affine_le_of_endpoints {a b x A B bound : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b)
    (ha : A + B * a ≤ bound) (hb : A + B * b ≤ bound) :
    A + B * x ≤ bound := by
  have hleft := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr ha)
  have hright := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hb)
  by_contra hnot
  have hpositive := mul_pos (sub_pos.mpr hab) (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith

private theorem bilinear_le_of_corners {a b u v A B C D bound : ℝ}
    (hab : a < b) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
    (haa : A + B * a + C * a + D * a * a ≤ bound)
    (hab' : A + B * a + C * b + D * a * b ≤ bound)
    (hba : A + B * b + C * a + D * b * a ≤ bound)
    (hbb : A + B * b + C * b + D * b * b ≤ bound) :
    A + B * u + C * v + D * u * v ≤ bound := by
  have ha : A + C * a + (B + D * a) * u ≤ bound :=
    affine_le_of_endpoints hab hu (by nlinarith [haa]) (by nlinarith [hba])
  have hb : A + C * b + (B + D * b) * u ≤ bound :=
    affine_le_of_endpoints hab hu (by nlinarith [hab']) (by nlinarith [hbb])
  have h := affine_le_of_endpoints hab hv
    (A := A + B * u) (B := C + D * u) (bound := bound)
    (by nlinarith [ha]) (by nlinarith [hb])
  nlinarith

theorem lower_reward_corner_eq (u v : ℝ) :
    gap (11 / 10) (-(1 / 10)) (21 / 10) (19 / 10) (19 / 10) (-(1 / 10))
        (1 / 100) u v =
      11 / 900 - 79 / 100 * u - 79 / 100 * v + 279 / 100 * u * v := by
  unfold gap postValue bellman contribution activeValue
  ring

theorem upper_reward_corner_eq (u v : ℝ) :
    gap (9 / 10) (1 / 10) (19 / 10) (21 / 10) (21 / 10) (1 / 10)
        (1 / 2) u v =
      13 / 10 - 7 / 10 * u - 7 / 10 * v + 27 / 10 * u * v := by
  unfold gap postValue bellman contribution activeValue
  ring

/-- The four exact lower-face corner values, in lexicographic hazard order. -/
theorem lower_face_corner_values :
    (fun u v : ℝ => 11 / 900 - 79 / 100 * u - 79 / 100 * v + 279 / 100 * u * v)
        (1 / 100) (1 / 100) = -(29689 / 9000000) ∧
    (fun u v : ℝ => 11 / 900 - 79 / 100 * u - 79 / 100 * v + 279 / 100 * u * v)
        (1 / 100) (1 / 2) = -(67811 / 180000) ∧
    (fun u v : ℝ => 11 / 900 - 79 / 100 * u - 79 / 100 * v + 279 / 100 * u * v)
        (1 / 2) (1 / 100) = -(67811 / 180000) ∧
    (fun u v : ℝ => 11 / 900 - 79 / 100 * u - 79 / 100 * v + 279 / 100 * u * v)
        (1 / 2) (1 / 2) = -(289 / 3600) := by
  norm_num

/-- The four exact upper-face corner values, in lexicographic hazard order. -/
theorem upper_face_corner_values :
    (fun u v : ℝ => 13 / 10 - 7 / 10 * u - 7 / 10 * v + 27 / 10 * u * v)
        (1 / 100) (1 / 100) = 128627 / 100000 ∧
    (fun u v : ℝ => 13 / 10 - 7 / 10 * u - 7 / 10 * v + 27 / 10 * u * v)
        (1 / 100) (1 / 2) = 1913 / 2000 ∧
    (fun u v : ℝ => 13 / 10 - 7 / 10 * u - 7 / 10 * v + 27 / 10 * u * v)
        (1 / 2) (1 / 100) = 1913 / 2000 ∧
    (fun u v : ℝ => 13 / 10 - 7 / 10 * u - 7 / 10 * v + 27 / 10 * u * v)
        (1 / 2) (1 / 2) = 51 / 40 := by
  norm_num

/-- Uniform strict lower-partner-face sign from the literal rational ranges. -/
theorem lower_face_gap_le {singleton partner joint left right tie u v : ℝ}
    (hown : OwnBounds singleton partner joint) (hpassive : PassiveBounds left right tie)
    (hu : u ∈ Set.Icc (1 / 100 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (1 / 100 : ℝ) (1 / 2)) :
    gap singleton partner joint left right tie (1 / 100) u v ≤ -(29689 / 9000000) := by
  have hcorner := gap_le_reward_corner hown hpassive
    (h := 1 / 100) (by norm_num) (u := u) (v := v)
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [lower_reward_corner_eq] at hcorner
  have hrectangle := bilinear_le_of_corners (a := 1 / 100) (b := 1 / 2)
    (A := 11 / 900) (B := -(79 / 100)) (C := -(79 / 100)) (D := 279 / 100)
    (bound := -(29689 / 9000000)) (by norm_num) hu hv
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Uniform strict upper-partner-face sign for one quiet pair. -/
theorem upper_face_gap_ge {singleton partner joint left right tie u v : ℝ}
    (hown : OwnBounds singleton partner joint) (hpassive : PassiveBounds left right tie)
    (hu : u ∈ Set.Icc (1 / 100 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (1 / 100 : ℝ) (1 / 2)) :
    1913 / 2000 ≤ gap singleton partner joint left right tie (1 / 2) u v := by
  have hcorner := reward_corner_le_gap hown hpassive
    (h := 1 / 2) (by norm_num) (u := u) (v := v)
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hv.1], by linarith [hv.2]⟩
  rw [upper_reward_corner_eq] at hcorner
  have hrectangle := bilinear_le_of_corners (a := 1 / 100) (b := 1 / 2)
    (A := -(13 / 10)) (B := 7 / 10) (C := 7 / 10) (D := -(27 / 10))
    (bound := -(1913 / 2000)) (by norm_num) hu hv
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem post_sub_active (singleton partner joint h : ℝ) (hh : h ≠ 1) :
    postValue singleton partner joint h - activeValue singleton joint h =
      h * (activeValue singleton joint h - partner) / (1 - h) := by
  unfold postValue activeValue
  field_simp
  ring

theorem post_gt_active {singleton partner joint h : ℝ}
    (hown : OwnBounds singleton partner joint) (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    activeValue singleton joint h < postValue singleton partner joint h := by
  apply sub_pos.mp
  rw [post_sub_active singleton partner joint h (ne_of_lt hh.2)]
  have hx := active_gt_singleton hown hh.1
  exact div_pos (mul_pos hh.1 (by linarith [hown.singleton_lower, hown.partner_upper]))
    (sub_pos.mpr hh.2)

theorem absorption_pos {u v : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 ≤ v) :
    0 < absorption u v := by
  unfold absorption
  nlinarith [mul_nonneg (sub_nonneg.mpr hu1) hv]

theorem three_mul_tie_le_absorption {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    3 * (u * v) ≤ absorption u v := by
  have hfirst := mul_le_mul_of_nonneg_left hv.2 hu.1
  have hsecond := mul_le_mul_of_nonneg_left hu.2 hv.1
  unfold absorption
  nlinarith

theorem conditional_tie_le_third {u v : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    u * v / absorption u v ≤ 1 / 3 := by
  have ha := absorption_pos hu.1 (by linarith [hu.2]) hv.1
  apply (div_le_iff₀ ha).mpr
  linarith [three_mul_tie_le_absorption ⟨hu.1.le, hu.2⟩ hv]

theorem contribution_ge_absorption {left right tie u v : ℝ}
    (hpassive : PassiveBounds left right tie)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    37 / 30 * absorption u v ≤ contribution left right tie u v := by
  have hl := mul_le_mul_of_nonneg_left hpassive.left_lower
    (mul_nonneg hu.1 (by linarith [hv.2] : 0 ≤ 1 - v))
  have hr := mul_le_mul_of_nonneg_left hpassive.right_lower
    (mul_nonneg (by linarith [hu.2] : 0 ≤ 1 - u) hv.1)
  have ht := mul_le_mul_of_nonneg_left hpassive.tie_lower (mul_nonneg hu.1 hv.1)
  have hthree := three_mul_tie_le_absorption hu hv
  unfold contribution absorption at *
  linarith

theorem conditional_passive_ge {left right tie u v : ℝ}
    (hpassive : PassiveBounds left right tie)
    (hu : u ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    37 / 30 ≤ contribution left right tie u v / absorption u v := by
  apply (le_div_iff₀ (absorption_pos hu.1 (by linarith [hu.2]) hv.1)).mpr
  exact contribution_ge_absorption hpassive ⟨hu.1.le, hu.2⟩ hv

theorem quiet_continue_advantage {singleton left right tie u v value : ℝ}
    (hs : singleton ≤ 11 / 10) (hpassive : PassiveBounds left right tie)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) (hvalue : singleton ≤ value) :
    singleton + 2 / 15 * absorption u v ≤ bellman left right tie u v value := by
  have hc := contribution_ge_absorption hpassive hu hv
  have hsuv := survival_mem_Icc
    (u := u) (v := v) ⟨hu.1, by linarith [hu.2]⟩ ⟨hv.1, by linarith [hv.2]⟩
  have htail := mul_le_mul_of_nonneg_left hvalue hsuv.1
  have ha : 0 ≤ absorption u v := by rw [absorption_eq_one_sub]; linarith [hsuv.2]
  have hsmul := mul_le_mul_of_nonneg_right hs ha
  rw [absorption_eq_one_sub] at hc hsmul ⊢
  unfold bellman
  nlinarith

theorem quiet_quit_le {singleton firstJoin secondJoin tieJoin u v : ℝ}
    (hfirst : firstJoin ≤ singleton + 1 / 50)
    (hsecond : secondJoin ≤ singleton + 1 / 50)
    (htie : tieJoin ≤ singleton + 1 / 50)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    bellman firstJoin secondJoin tieJoin u v singleton ≤
      singleton + 1 / 50 * absorption u v := by
  have hl := mul_le_mul_of_nonneg_left hfirst (mul_nonneg hu.1 (sub_nonneg.mpr hv.2))
  have hr := mul_le_mul_of_nonneg_left hsecond (mul_nonneg (sub_nonneg.mpr hu.2) hv.1)
  have ht := mul_le_mul_of_nonneg_left htie (mul_nonneg hu.1 hv.1)
  unfold bellman contribution absorption
  nlinarith

theorem quiet_gap_ge {singleton left right tie firstJoin secondJoin tieJoin u v value : ℝ}
    (hs : singleton ≤ 11 / 10) (hpassive : PassiveBounds left right tie)
    (hfirst : firstJoin ≤ singleton + 1 / 50)
    (hsecond : secondJoin ≤ singleton + 1 / 50)
    (htie : tieJoin ≤ singleton + 1 / 50)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (0 : ℝ) (1 / 2)) (hvalue : singleton ≤ value) :
    17 / 150 * absorption u v ≤ bellman left right tie u v value -
      bellman firstJoin secondJoin tieJoin u v singleton := by
  have hcontinue := quiet_continue_advantage hs hpassive hu hv hvalue
  have hquit := quiet_quit_le hfirst hsecond htie
    ⟨hu.1, by linarith [hu.2]⟩ ⟨hv.1, by linarith [hv.2]⟩
  linarith

/-- Scalar data for one member of an ordered family of quiet-pair maps. -/
structure Row where
  left : ℝ
  right : ℝ
  tie : ℝ
  firstHazard : ℝ
  secondHazard : ℝ

def Row.apply (row : Row) (value : ℝ) : ℝ :=
  bellman row.left row.right row.tie row.firstHazard row.secondHazard value

structure Row.Valid (row : Row) : Prop where
  passive : PassiveBounds row.left row.right row.tie
  first : row.firstHazard ∈ Set.Icc (1 / 100 : ℝ) (1 / 2)
  second : row.secondHazard ∈ Set.Icc (1 / 100 : ℝ) (1 / 2)

/-- First list entry is the outermost, chronologically earliest Bellman map. -/
def compose (rows : List Row) (value : ℝ) : ℝ :=
  rows.foldr Row.apply value

theorem Row.monotone_apply {row : Row} (hrow : row.Valid) : Monotone row.apply :=
  monotone_bellman _ _ _ (by linarith [hrow.first.2]) (by linarith [hrow.second.2])

theorem compose_le_upper {rows : List Row} {value : ℝ}
    (hrows : ∀ row ∈ rows, row.Valid) (hvalue : value ≤ 21 / 10) :
    compose rows value ≤ 21 / 10 := by
  induction rows with
  | nil => exact hvalue
  | cons row rows ih =>
      have hrow := hrows row (by simp)
      apply bellman_le
        ⟨by linarith [hrow.first.1], by linarith [hrow.first.2]⟩
        ⟨by linarith [hrow.second.1], by linarith [hrow.second.2]⟩
        hrow.passive.left_upper hrow.passive.right_upper
        (by linarith [hrow.passive.tie_upper])
      exact ih (fun next hnext => hrows next (by simp [hnext]))

theorem compose_gt_singleton {rows : List Row} {singleton value : ℝ}
    (hrows : ∀ row ∈ rows, row.Valid) (hs : singleton ≤ 11 / 10)
    (hvalue : singleton < value) : singleton < compose rows value := by
  induction rows with
  | nil => exact hvalue
  | cons row rows ih =>
      have hrow := hrows row (by simp)
      have htail := ih (fun next hnext => hrows next (by simp [hnext]))
      have hcontinue := quiet_continue_advantage hs hrow.passive
        ⟨by linarith [hrow.first.1], hrow.first.2⟩
        ⟨by linarith [hrow.second.1], hrow.second.2⟩ htail.le
      have ha := absorption_pos (v := row.secondHazard)
        (by linarith [hrow.first.1] : 0 < row.firstHazard)
        (by linarith [hrow.first.2]) (by linarith [hrow.second.1])
      change singleton < bellman row.left row.right row.tie
        row.firstHazard row.secondHazard (compose rows value)
      linarith

private theorem active_le_compose_lower_face {rows : List Row}
    {singleton partner joint : ℝ}
    (hown : OwnBounds singleton partner joint) (hrows : ∀ row ∈ rows, row.Valid) :
    activeValue singleton joint (1 / 100) ≤
      compose rows (activeValue singleton joint (1 / 100)) := by
  induction rows with
  | nil => exact le_rfl
  | cons row rows ih =>
      have hrow := hrows row (by simp)
      have htail := ih (fun next hnext => hrows next (by simp [hnext]))
      have hmap := Row.monotone_apply hrow htail
      have hgap := lower_face_gap_le hown hrow.passive hrow.first hrow.second
      have hpost := post_gt_active hown (h := 1 / 100) (by norm_num)
      unfold gap at hgap
      change activeValue _ _ _ ≤ row.apply (compose rows (activeValue _ _ _))
      change bellman _ _ _ _ _ _ ≤ _ at hmap
      linarith

/-- Any nonempty ordered list has the same strict lower-face separation. -/
theorem compose_lower_face_gap_le {rows : List Row} {singleton partner joint : ℝ}
    (hown : OwnBounds singleton partner joint) (hrows : ∀ row ∈ rows, row.Valid)
    (hne : rows ≠ []) :
    postValue singleton partner joint (1 / 100) -
        compose rows (activeValue singleton joint (1 / 100)) ≤ -(29689 / 9000000) := by
  cases rows with
  | nil => exact (hne rfl).elim
  | cons row rows =>
      have hrow := hrows row (by simp)
      have htail := active_le_compose_lower_face (rows := rows) hown
        (fun next hnext => hrows next (by simp [hnext]))
      have hmap := Row.monotone_apply hrow htail
      have hgap := lower_face_gap_le hown hrow.passive hrow.first hrow.second
      unfold gap at hgap
      change postValue _ _ _ _ - row.apply (compose rows (activeValue _ _ _)) ≤ _
      change bellman _ _ _ _ _ _ ≤ _ at hmap
      linarith

/-- The upper face has a uniform margin, independent even of the number of maps. -/
theorem compose_upper_face_gap_ge {rows : List Row} {singleton partner joint : ℝ}
    (hown : OwnBounds singleton partner joint) (hrows : ∀ row ∈ rows, row.Valid) :
    3 / 5 ≤ postValue singleton partner joint (1 / 2) -
      compose rows (activeValue singleton joint (1 / 2)) := by
  have hx := active_le_eight_fifths hown (h := 1 / 2) (by norm_num)
  have hcomp := compose_le_upper hrows
    (by linarith : activeValue singleton joint (1 / 2) ≤ 21 / 10)
  have hpost := post_upper_face_ge hown
  linarith

theorem bellman_sub (left right tie u v first second : ℝ) :
    bellman left right tie u v first - bellman left right tie u v second =
      (1 - u) * (1 - v) * (first - second) := by
  unfold bellman
  ring

theorem abs_bellman_sub_le (left right tie first second : ℝ) {u v : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    |bellman left right tie u v first - bellman left right tie u v second| ≤
      |first - second| := by
  rw [bellman_sub, abs_mul, abs_of_nonneg (survival_mem_Icc hu hv).1]
  exact mul_le_of_le_one_left (abs_nonneg _) (survival_mem_Icc hu hv).2

theorem compose_append (first second : List Row) (value : ℝ) :
    compose (first ++ second) value = compose first (compose second value) := by
  simp [compose, List.foldr_append]

theorem Row.Valid.hazards {row : Row} (hrow : row.Valid) :
    row.firstHazard ∈ Set.Icc (0 : ℝ) 1 ∧ row.secondHazard ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨⟨by linarith [hrow.first.1], by linarith [hrow.first.2]⟩,
    ⟨by linarith [hrow.second.1], by linarith [hrow.second.2]⟩⟩

theorem abs_compose_sub_le {rows : List Row}
    (hrows : ∀ row ∈ rows,
      row.firstHazard ∈ Set.Icc (0 : ℝ) 1 ∧ row.secondHazard ∈ Set.Icc (0 : ℝ) 1)
    (first second : ℝ) : |compose rows first - compose rows second| ≤ |first - second| := by
  induction rows with
  | nil => exact le_rfl
  | cons row rows ih =>
      have hrow := hrows row (by simp)
      have htail := ih (fun next hnext => hrows next (by simp [hnext]))
      have hstep := abs_bellman_sub_le row.left row.right row.tie
        (compose rows first) (compose rows second)
        (u := row.firstHazard) (v := row.secondHazard)
        hrow.1 hrow.2
      exact hstep.trans htail

/-- One strictly contracting active pair makes a nonexpansive quiet word have at most one
fixed active value. Only hazard bounds are used; all rewards are unrestricted. -/
theorem eq_of_active_cycle_fixed {rows : List Row}
    (hrows : ∀ row ∈ rows,
      row.firstHazard ∈ Set.Icc (0 : ℝ) 1 ∧ row.secondHazard ∈ Set.Icc (0 : ℝ) 1)
    {left right tie u v first second : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hfirst : first = bellman left right tie u v (compose rows first))
    (hsecond : second = bellman left right tie u v (compose rows second)) : first = second := by
  have hc := survival_mem_Icc ⟨hu.1.le, hu.2⟩ hv
  have hstrict : (1 - u) * (1 - v) < 1 := by
    have hmul := mul_le_mul_of_nonneg_left (show 1 - v ≤ 1 by linarith [hv.1])
      (sub_nonneg.mpr hu.2)
    nlinarith [hu.1]
  have hdiff : first - second = (1 - u) * (1 - v) *
      (compose rows first - compose rows second) := by
    calc
      first - second = bellman left right tie u v (compose rows first) -
          bellman left right tie u v (compose rows second) := congrArg₂ (· - ·) hfirst hsecond
      _ = _ := bellman_sub _ _ _ _ _ _ _
  have habs := congrArg abs hdiff
  rw [abs_mul, abs_of_nonneg hc.1] at habs
  have hbound := mul_le_mul_of_nonneg_left (abs_compose_sub_le hrows first second) hc.1
  have hzero : |first - second| = 0 := by
    nlinarith [abs_nonneg (first - second)]
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

end Math.PairedAffine
