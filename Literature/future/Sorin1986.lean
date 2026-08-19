import Literature.Catalog
import UniformEquilibrium.Examples.Sorin.OccupationVanishing
import UniformEquilibrium.Certificates.Adaptive.Certificate

/-!
# Literature audit

Bibliography label: Sorin 1986

The primary paper was inspected for both equilibrium-payoff-set statements and
their separation.
-/

namespace Literature.Sorin1986

open GameTheory StochasticGame

/-! The paper's `E(∞)` is the set of semantic uniform-equilibrium
payoffs from the live state.  The bounds in the parametrization are part of
the claim; the affine equation alone is strictly weaker. -/

def UniformEquilibriumPayoffSetClaim : Prop :=
  ∀ payoff : Payoff SorinAbsorbingGame.Player,
    SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
        SorinAbsorbingGame.State.live payoff ↔
      ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 2 / 3 ∧
        payoff = SorinAbsorbingGame.pair a (2 * (1 - a))

/-- The discount-constant endpoint of Sorin's displayed stationary family is
not a uniform-equilibrium payoff of the displayed absorbing game. -/
theorem discountedEndpoint_not_isUniformEquilibriumPayoff :
    ¬ SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live
      (SorinAbsorbingGame.pair (1 / 2) (2 / 3)) :=
  SorinAbsorbingGame.discountedEndpoint_not_isUniformEquilibriumPayoff

/-- Every uniform-equilibrium payoff of Sorin's displayed game lies on the
affine line `2 * payoff false + payoff true = 2`. -/
theorem uniformEquilibriumPayoff_weighted_eq_two
    (payoff : GameTheory.Payoff SorinAbsorbingGame.Player)
    (hpayoff : SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live payoff) :
    2 * payoff false + payoff true = 2 :=
  SorinAbsorbingGame.uniformEquilibriumPayoff_weighted_eq_two payoff hpayoff

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "sorin_1986"
  bibliographyLabel := "Sorin 1986"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Sorin 1986"
  role := .counterexamples
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "finite_and_discounted_payoff_sets"
        paperLocator := "Theorem 1"
        summary := "Every finite-horizon and discounted equilibrium payoff set is {V}."
        status := .paperOnly },
      { claimId := "uniform_equilibrium_payoff_set"
        paperLocator := "Theorem 2"
        summary := "The uniform equilibrium payoff set is the bounded Pareto segment F."
        status := .openInLean
          "Literature.Sorin1986.UniformEquilibriumPayoffSetClaim" },
      { claimId := "approximation_sets_disjoint_from_uniform_set"
        paperLocator := "separation statement on page 107"
        summary := "The constant approximation payoff set is disjoint from F."
        status := .paperOnly },
      { claimId := "discounted_endpoint_not_uniform"
        paperLocator := "separation statement on page 107"
        summary := "The discount-constant endpoint (1/2, 2/3) is not a uniform payoff."
        status := .provedInLean
          "Literature.Sorin1986.discountedEndpoint_not_isUniformEquilibriumPayoff"
          "GameTheory.StochasticGame.SorinAbsorbingGame.\
discountedEndpoint_not_isUniformEquilibriumPayoff" },
      { claimId := "uniform_payoffs_satisfy_affine_line"
        paperLocator := "Theorem 2"
        summary := "Every uniform payoff lies on 2 w1 + w2 = 2."
        status := .provedInLean
          "Literature.Sorin1986.uniformEquilibriumPayoff_weighted_eq_two"
          "GameTheory.StochasticGame.SorinAbsorbingGame.\
uniformEquilibriumPayoff_weighted_eq_two" } ]

end Literature.Sorin1986

/-!
# Research reduction for Sorin's uniform-payoff segment

The paper's Theorem 2 identifies the uniform-equilibrium payoff set with a
bounded segment.  This module states the exact semantic claim through the
paper module and proves the inclusion supplied by the two security
certificates.  The converse inclusion is not claimed here.
-/

namespace Literature.Sorin1986

open GameTheory StochasticGame
open Literature.Sorin1986

theorem uniformPayoff_mem_sorinSegment_of_paper_claim
    (hclaim : Literature.Sorin1986.UniformEquilibriumPayoffSetClaim)
    (payoff : Payoff SorinAbsorbingGame.Player)
    (hpayoff : SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live payoff) :
    ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 2 / 3 ∧
      payoff = SorinAbsorbingGame.pair a (2 * (1 - a)) :=
  (hclaim payoff).mp hpayoff

theorem uniformPayoff_mem_sorinSegment
    (payoff : Payoff SorinAbsorbingGame.Player)
    (hpayoff : SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live payoff) :
    ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 2 / 3 ∧
      payoff = SorinAbsorbingGame.pair a (2 * (1 - a)) := by
  have hplayerOne :=
    uniformEquilibriumPayoff_coordinate_ge_of_isOneSidedGuaranteeCertificate
      SorinAbsorbingGame.game SorinAbsorbingGame.State.live false (1 / 2)
    SorinAbsorbingGame.isOneSidedGuaranteeCertificate_playerOne hpayoff
  have hplayerTwo :=
    uniformEquilibriumPayoff_coordinate_ge_of_isOneSidedGuaranteeCertificate
      SorinAbsorbingGame.game SorinAbsorbingGame.State.live true (2 / 3)
    SorinAbsorbingGame.isOneSidedGuaranteeCertificate_playerTwo hpayoff
  have hline := SorinAbsorbingGame.uniformEquilibriumPayoff_weighted_eq_two
    payoff hpayoff
  refine ⟨payoff false, hplayerOne, ?_, ?_⟩
  · linarith
  · funext who
    cases who
    · simp [SorinAbsorbingGame.pair]
    · simp [SorinAbsorbingGame.pair]
      nlinarith [hline]

end Literature.Sorin1986

/-!
# Weighted Blackwell--Ferguson primitives for Sorin's absorbing game

This is an isolated research lane for the forward segment construction in
Sorin's absorbing game.  The definitions use the real-valued account from the
weighted proof; no production umbrella imports this module.
-/

noncomputable section

namespace Literature.Sorin1986.WeightedBlackwellFerguson

open GameTheory StochasticGame
open Literature.Sorin1986

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

end Literature.Sorin1986.WeightedBlackwellFerguson
