import Research.Literature.Sorin1986.UniformPayoffSet

/-!
# Weighted Blackwell--Ferguson primitives for Sorin's absorbing game

This is an isolated research lane for the forward segment construction in
Sorin's absorbing game.  The definitions use the real-valued account from the
weighted proof; no production umbrella imports this module.
-/

noncomputable section

namespace Research.Literature.Sorin1986.WeightedBlackwellFerguson

open GameTheory StochasticGame
open Literature.Papers.Sorin1986

namespace SorinAbsorbingGame

/-! ## Scalar parameters -/

def b (a : ℝ) : ℝ := 1 - a

def c (a : ℝ) : ℝ := 2 * a - 1

def d (a : ℝ) : ℝ := 2 - 3 * a

theorem b_eq_one_sub (a : ℝ) : b a = 1 - a := rfl

theorem c_eq_a_sub_b (a : ℝ) : c a = a - b a := by
  unfold c b
  ring

theorem d_eq_two_b_sub_a (a : ℝ) : d a = 2 * b a - a := by
  unfold d b
  ring

theorem b_pos {a : ℝ} (ha : a ≤ 2 / 3) : 0 < b a := by
  unfold b
  linarith

theorem b_nonneg {a : ℝ} (ha : a ≤ 2 / 3) : 0 ≤ b a :=
  (b_pos ha).le

theorem c_nonneg {a : ℝ} (ha : 1 / 2 ≤ a) : 0 ≤ c a := by
  unfold c
  linarith

theorem d_nonneg {a : ℝ} (ha : a ≤ 2 / 3) : 0 ≤ d a := by
  unfold d
  linarith

theorem a_eq_b_add_c (a : ℝ) : a = b a + c a := by
  unfold b c
  ring

theorem b_add_c_eq_a (a : ℝ) : b a + c a = a :=
  (a_eq_b_add_c a).symm

/-! ## Account and stopping primitives -/

def increment (a : ℝ) (column : Bool) : ℝ :=
  if column then a else -(b a)

def denominator (a R : ℝ) : ℝ := max R (b a)

def stopProbability (a R : ℝ) : ℝ :=
  (a * b a) / (denominator a R * (denominator a R + c a))

def potential (a D : ℝ) : ℝ := -(a * b a) / D

def energy (a R : ℝ) : ℝ := R * (R + c a)

theorem denominator_ge_b {a R : ℝ} : b a ≤ denominator a R := by
  exact le_max_right _ _

theorem denominator_pos {a R : ℝ} (ha : a ≤ 2 / 3) :
    0 < denominator a R := by
  have hb : 0 < b a := b_pos ha
  exact lt_of_lt_of_le hb (denominator_ge_b (a := a) (R := R))

theorem denominator_add_c_pos {a R : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2 / 3) :
    0 < denominator a R + c a := by
  have hD := denominator_pos (a := a) (R := R) ha'
  have hc := c_nonneg ha
  linarith

theorem stopProbability_nonneg {a R : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2 / 3) :
    0 ≤ stopProbability a R := by
  have hD := denominator_pos (a := a) (R := R) ha'
  have hc := c_nonneg ha
  unfold stopProbability
  exact div_nonneg (mul_nonneg (by linarith) (b_nonneg ha'))
    (mul_nonneg hD.le (by linarith))

theorem stopProbability_le_one {a R : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2 / 3) :
    stopProbability a R ≤ 1 := by
  have hD : b a ≤ denominator a R := denominator_ge_b
  have hb : 0 < b a := b_pos ha'
  have hc : 0 ≤ c a := c_nonneg ha
  have hden : 0 < denominator a R * (denominator a R + c a) := by
    exact mul_pos (denominator_pos ha') (denominator_add_c_pos ha ha')
  unfold stopProbability
  rw [div_le_one hden]
  have ha0 : 0 ≤ a := by linarith
  have hbc : a * b a ≤ denominator a R * (denominator a R + c a) := by
    have hD0 : 0 ≤ denominator a R := le_trans hb.le hD
    have hDa : a ≤ denominator a R + c a := by
      calc
        a = b a + c a := a_eq_b_add_c a
        _ ≤ denominator a R + c a := by linarith [hD]
    nlinarith
  exact hbc

/-! ## The two rational Bellman identities -/

theorem potential_right_id {a D : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2 / 3)
    (hD : b a < D) :
    (stopProbability a D) * b a +
        (1 - stopProbability a D) * potential a (D - b a) = potential a D := by
  have hb : 0 < b a := b_pos ha'
  have hc : 0 ≤ c a := c_nonneg ha
  have hDpos : 0 < D := lt_of_lt_of_le hb hD.le
  have hDb : 0 < D - b a := sub_pos.mpr hD
  have hDc : 0 < D + c a := by linarith
  have hden : D * (D + c a) ≠ 0 := by positivity
  have hden' : (D - b a) ≠ 0 := ne_of_gt hDb
  unfold stopProbability potential denominator
  rw [max_eq_left hD.le]
  field_simp
  have hrel : a * b a = b a * (b a + c a) := by
    calc
      a * b a = (b a + c a) * b a :=
        congrArg (fun x => x * b a) (a_eq_b_add_c a)
      _ = b a * (b a + c a) := by ring
  nlinarith [hrel]

theorem potential_left_id {a D : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2 / 3)
    (hD : b a < D) :
    -(stopProbability a D) * a +
        (1 - stopProbability a D) * potential a (D + a) = potential a D := by
  have hb : 0 < b a := b_pos ha'
  have hDpos : 0 < D := lt_of_lt_of_le hb hD.le
  have hDa : 0 < D + a := by linarith
  have hDc : 0 < D + c a := by
    have hc := c_nonneg ha
    linarith
  have hden : D * (D + c a) ≠ 0 := by positivity
  have hden' : (D + a) ≠ 0 := ne_of_gt hDa
  unfold stopProbability potential denominator
  rw [max_eq_left hD.le]
  field_simp
  have hrel : a * b a = b a * (b a + c a) := by
    calc
      a * b a = (b a + c a) * b a :=
        congrArg (fun x => x * b a) (a_eq_b_add_c a)
      _ = b a * (b a + c a) := by ring
  nlinarith [hrel]

theorem energy_step_identity (a R : ℝ) (column : Bool) :
    energy a (R + increment a column) =
      energy a R +
        (if column then a * (R + c a + R + a) else
          -b a * (R + c a + R - b a)) := by
  unfold energy increment
  split <;> ring

theorem energy_expect_coin (a R : ℝ) (q : ℝ) :
    q * energy a (R + a) + (1 - q) * energy a (R - b a) =
      energy a R +
        (q * (a * (R + c a + R + a)) -
          (1 - q) * (b a * (R + c a + R - b a))) := by
  unfold energy
  ring

end SorinAbsorbingGame

end Research.Literature.Sorin1986.WeightedBlackwellFerguson
