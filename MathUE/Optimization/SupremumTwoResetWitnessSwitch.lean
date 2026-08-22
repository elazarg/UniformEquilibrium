/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Approximate witness switching for a four-corner supremum envelope

For four payoff families indexed by the same deviation type, a pointwise
mixed-difference bound controls the mixed difference of their suprema unless
an approximately optimal witness switches corners.  The statements use
explicit `sSup` values and approximate witnesses, so no supremum attainment is
assumed.  The finite-mixture lemma is only an algebraic extraction result; it
does not assert a behavioral-to-pure decomposition.
-/

noncomputable section

open scoped BigOperators

namespace Math.Optimization

variable {D : Type*}

/-- Mixed difference of the four supremum-envelope values. -/
def supMixedDifference
    (f₀ f₁ f₂ f₁₂ : D → ℝ) : ℝ :=
  sSup (Set.range f₁₂) - sSup (Set.range f₁) -
    sSup (Set.range f₂) + sSup (Set.range f₀)

/-- The regret of a witness at the base corner. -/
def baseRegret (f₀ : D → ℝ) (d : D) : ℝ :=
  sSup (Set.range f₀) - f₀ d

/-- The regret at corner `2` of a witness selected at corner `1`. -/
def oppositeRegret₂ (f₂ : D → ℝ) (d : D) : ℝ :=
  sSup (Set.range f₂) - f₂ d

/-- The regret at corner `1` of a witness selected at corner `2`. -/
def oppositeRegret₁ (f₁ : D → ℝ) (d : D) : ℝ :=
  sSup (Set.range f₁) - f₁ d

/-- The full quantitative data retained when a witness selected near the
supremum at `source` becomes suboptimal at `receiving`.  In addition to both
approximate-optimality inequalities, the certificate records the direct gain
at the receiving corner, the reverse-edge budget at the source corner, and
their oriented rectangle. -/
structure OrientedSupremumWitnessSwitch
    (source receiving : D → ℝ) (charge eta : ℝ) where
  sourceWitness : D
  receivingWitness : D
  source_approx :
    sSup (Set.range source) - eta ≤ source sourceWitness
  receiving_approx :
    sSup (Set.range receiving) - eta ≤ receiving receivingWitness
  receiving_regret :
    charge + 2 * eta ≤
      sSup (Set.range receiving) - receiving sourceWitness
  receiving_gain :
    charge + eta ≤
      receiving receivingWitness - receiving sourceWitness
  source_gain_le :
    source receivingWitness - source sourceWitness ≤ eta
  rectangle :
    charge ≤
      receiving receivingWitness - receiving sourceWitness -
        source receivingWitness + source sourceWitness

/-- Propositional existence wrapper for an oriented witness-switch
certificate. -/
def HasOrientedSupremumWitnessSwitch
    (source receiving : D → ℝ) (charge eta : ℝ) : Prop :=
  Nonempty (OrientedSupremumWitnessSwitch source receiving charge eta)

/-- A bounded nonempty real-valued family has an `eta`-optimal witness for
every positive `eta`; no supremum attainment is used. -/
theorem exists_ge_sSup_sub
    [Nonempty D] (f : D → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ d, sSup (Set.range f) - eta ≤ f d := by
  obtain ⟨value, ⟨d, rfl⟩, hvalue⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty f)
      (sub_lt_self (sSup (Set.range f)) heta)
  exact ⟨d, hvalue.le⟩

/-- Complete an oriented switch once the source witness and its receiving
regret are known.  The second witness is only approximately optimal, so this
constructor applies even when the receiving supremum is not attained. -/
theorem orientedSupremumWitnessSwitch_of_regret
    [Nonempty D] (source receiving : D → ℝ)
    (hsource : BddAbove (Set.range source))
    (charge eta : ℝ) (heta : 0 < eta) (sourceWitness : D)
    (hsourceApprox :
      sSup (Set.range source) - eta ≤ source sourceWitness)
    (hregret : charge + 2 * eta ≤
      sSup (Set.range receiving) - receiving sourceWitness) :
    HasOrientedSupremumWitnessSwitch source receiving charge eta := by
  obtain ⟨receivingWitness, hreceivingApprox⟩ :=
    exists_ge_sSup_sub receiving eta heta
  have hsourceUpper : source receivingWitness ≤ sSup (Set.range source) :=
    le_csSup hsource ⟨receivingWitness, rfl⟩
  have hreceivingGain : charge + eta ≤
      receiving receivingWitness - receiving sourceWitness := by
    linarith
  have hsourceGain :
      source receivingWitness - source sourceWitness ≤ eta := by
    linarith
  exact ⟨{
    sourceWitness := sourceWitness
    receivingWitness := receivingWitness
    source_approx := hsourceApprox
    receiving_approx := hreceivingApprox
    receiving_regret := hregret
    receiving_gain := hreceivingGain
    source_gain_le := hsourceGain
    rectangle := by linarith
  }⟩

/-- If a two-step path carries a total increase of at least `charge`, one of
its two literal edges carries at least half of that increase. -/
theorem half_le_one_twoStep_increment
    (charge source middle receiving : ℝ)
    (htotal : charge ≤ receiving - source) :
    charge / 2 ≤ middle - source ∨
      charge / 2 ≤ receiving - middle := by
  by_cases hfirst : charge / 2 ≤ middle - source
  · exact Or.inl hfirst
  · right
    have hfirst' : middle - source < charge / 2 := lt_of_not_ge hfirst
    linarith

/-! ## Finite-cube common passports -/

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]

/-- Regret of one fixed witness at one face of a finite cube. -/
def finiteCubeRegret
    (cap : Finset Coordinate → ℝ)
    (payoff : Finset Coordinate → D → ℝ)
    (face : Finset Coordinate) (d : D) : ℝ :=
  cap face - payoff face d

/-- Error in the common-source affine expansion of one fixed-witness payoff
on a finite cube face. -/
def finiteCubeAffineRemainder
    (payoff : Finset Coordinate → D → ℝ)
    (face : Finset Coordinate) (d : D) : ℝ :=
  payoff face d -
    (payoff ∅ d + ∑ coordinate ∈ face,
      (payoff {coordinate} d - payoff ∅ d))

/-- Failure of the cap at the full face to equal the sum of its singleton
increments at the common source. -/
def finiteCubeCapNonadditivity
    (cap : Finset Coordinate → ℝ) : ℝ :=
  (∑ coordinate, (cap {coordinate} - cap ∅)) -
    (cap Finset.univ - cap ∅)

omit [Fintype Coordinate] in
/-- A large regret drop from the empty face to a nonempty face is carried by
one literal insertion edge of that face. -/
theorem exists_finsetEdge_regretDrop_gt
    (value : Finset Coordinate → ℝ) (face : Finset Coordinate)
    (hface : face.Nonempty) (threshold : ℝ)
    (htotal : (face.card : ℝ) * threshold < value ∅ - value face) :
    ∃ base mover, base ⊆ face ∧ mover ∈ face ∧ mover ∉ base ∧
      threshold < value base - value (insert mover base) := by
  induction face using Finset.induction with
  | empty => exact (Finset.not_nonempty_empty hface).elim
  | @insert mover face hmover ih =>
      by_cases hedge :
          threshold < value face - value (insert mover face)
      · exact ⟨face, mover, Finset.subset_insert _ _,
          Finset.mem_insert_self mover face,
          hmover, hedge⟩
      · have hedgeLe :
            value face - value (insert mover face) ≤ threshold :=
          le_of_not_gt hedge
        have htail : (face.card : ℝ) * threshold < value ∅ - value face := by
          simp only [Finset.card_insert_of_notMem hmover, Nat.cast_add,
            Nat.cast_one] at htotal
          linarith
        have hfaceNonempty : face.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at htail
          simp at htail
        obtain ⟨base, changed, hbase, hchanged, hchangedBase, hdrop⟩ :=
          ih hfaceNonempty htail
        exact ⟨base, changed, hbase.trans (Finset.subset_insert _ _),
          Finset.mem_insert_of_mem hchanged, hchangedBase, hdrop⟩

omit [DecidableEq Coordinate] in
/-- Exact identity relating cap nonadditivity, the regrets of one fixed
witness, and its full-face affine remainder. -/
theorem finiteCubeCapNonadditivity_eq_regrets_sub_remainder
    (cap : Finset Coordinate → ℝ)
    (payoff : Finset Coordinate → D → ℝ) (d : D) :
    finiteCubeCapNonadditivity cap =
      (∑ coordinate,
          finiteCubeRegret cap payoff {coordinate} d) -
        ((Fintype.card Coordinate : ℝ) - 1) *
          finiteCubeRegret cap payoff ∅ d -
        finiteCubeRegret cap payoff Finset.univ d -
        finiteCubeAffineRemainder payoff Finset.univ d := by
  simp only [finiteCubeCapNonadditivity, finiteCubeRegret,
    finiteCubeAffineRemainder, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [Fintype Coordinate] [DecidableEq Coordinate] in
/-- Exact two-witness version of the affine face expansion. -/
theorem finiteCubePayoff_sub_eq_sum_sub_base_add_remainder
    (payoff : Finset Coordinate → D → ℝ)
    (face : Finset Coordinate) (first second : D) :
    payoff face first - payoff face second =
      (∑ coordinate ∈ face,
          (payoff {coordinate} first - payoff {coordinate} second)) -
        ((face.card : ℝ) - 1) *
          (payoff ∅ first - payoff ∅ second) +
        finiteCubeAffineRemainder payoff face first -
        finiteCubeAffineRemainder payoff face second := by
  simp only [finiteCubeAffineRemainder, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Finite-scale common passport or literal edge switch.**

Every face has a supplied `eta`-optimal witness.  Fixed-witness payoffs are
uniformly affine from the empty face up to error `omega`, and the cap's
full-face nonadditivity is at most `delta`.  The proof first tests whether a
selected face witness has empty-face regret larger than `beta`.

If so, one insertion edge inside that same face lowers its regret by more than
`(beta - eta) / face.card`.  Otherwise the full-face witness is quantitatively
near-optimal on every face, with the displayed finite remainder budget.  This
is a priority case split, not an exclusive alternative, and contains no
asymptotic or attainment assumption. -/
theorem finiteCube_commonPassport_or_edgeWitnessSwitch
    (cap : Finset Coordinate → ℝ)
    (payoff : Finset Coordinate → D → ℝ)
    (witness : Finset Coordinate → D)
    (eta beta delta omega : ℝ)
    (hetaBeta : eta ≤ beta)
    (hupper : ∀ face d, payoff face d ≤ cap face)
    (happrox : ∀ face,
      cap face - eta ≤ payoff face (witness face))
    (hremainder : ∀ face d,
      |finiteCubeAffineRemainder payoff face d| ≤ omega)
    (hnonadditivity : finiteCubeCapNonadditivity cap ≤ delta) :
    (∃ face base mover,
        face.Nonempty ∧ base ⊆ face ∧ mover ∈ face ∧ mover ∉ base ∧
          (beta - eta) / (face.card : ℝ) <
            finiteCubeRegret cap payoff base (witness face) -
              finiteCubeRegret cap payoff (insert mover base) (witness face)) ∨
      ∀ face,
        finiteCubeRegret cap payoff face (witness Finset.univ) ≤
          if face = ∅ then beta else
            delta + 2 * eta +
              (((Fintype.card Coordinate : ℝ) - 1) +
                  ((face.card : ℝ) - 1)) * beta +
                3 * omega := by
  have hregretNonneg : ∀ face d,
      0 ≤ finiteCubeRegret cap payoff face d := by
    intro face d
    exact sub_nonneg.mpr (hupper face d)
  have hselectedRegret : ∀ face,
      finiteCubeRegret cap payoff face (witness face) ≤ eta := by
    intro face
    dsimp only [finiteCubeRegret]
    linarith [happrox face]
  by_cases hbad : ∃ face,
      beta < finiteCubeRegret cap payoff ∅ (witness face)
  · left
    obtain ⟨face, hbaseRegret⟩ := hbad
    have hfaceNonempty : face.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hbaseRegret
      linarith [hselectedRegret ∅]
    have htotal : beta - eta <
        finiteCubeRegret cap payoff ∅ (witness face) -
          finiteCubeRegret cap payoff face (witness face) := by
      linarith [hselectedRegret face]
    have hcardPositive : 0 < (face.card : ℝ) := by
      exact_mod_cast hfaceNonempty.card_pos
    have hscaled : (face.card : ℝ) *
          ((beta - eta) / (face.card : ℝ)) <
        finiteCubeRegret cap payoff ∅ (witness face) -
          finiteCubeRegret cap payoff face (witness face) := by
      calc
        (face.card : ℝ) * ((beta - eta) / (face.card : ℝ)) =
            beta - eta := by field_simp
        _ < _ := htotal
    obtain ⟨base, mover, hbase, hmover, hmoverBase, hdrop⟩ :=
      exists_finsetEdge_regretDrop_gt
        (fun candidate ↦ finiteCubeRegret cap payoff candidate (witness face))
        face hfaceNonempty ((beta - eta) / (face.card : ℝ)) hscaled
    exact ⟨face, base, mover, hfaceNonempty, hbase, hmover, hmoverBase,
      hdrop⟩
  · right
    have hbaseRegret : ∀ face,
        finiteCubeRegret cap payoff ∅ (witness face) ≤ beta := by
      intro face
      exact le_of_not_gt (not_exists.mp hbad face)
    intro face
    by_cases hfaceEmpty : face = ∅
    · simp only [hfaceEmpty, if_pos]
      exact hbaseRegret Finset.univ
    · rw [if_neg hfaceEmpty]
      have hfaceNonempty : face.Nonempty := Finset.nonempty_iff_ne_empty.mpr hfaceEmpty
      have hcoordinateNonempty : Nonempty Coordinate := by
        obtain ⟨coordinate, _hcoordinate⟩ := hfaceNonempty
        exact ⟨coordinate⟩
      have hcoordinateCoefficient :
          0 ≤ (Fintype.card Coordinate : ℝ) - 1 := by
        have hcard : 1 ≤ Fintype.card Coordinate :=
          Fintype.card_pos_iff.mpr hcoordinateNonempty
        have hcardReal : (1 : ℝ) ≤ Fintype.card Coordinate := by
          exact_mod_cast hcard
        linarith
      have hfaceCoefficient : 0 ≤ (face.card : ℝ) - 1 := by
        have hcardReal : (1 : ℝ) ≤ face.card := by
          exact_mod_cast hfaceNonempty.card_pos
        linarith
      let fullWitness := witness (Finset.univ : Finset Coordinate)
      have hfullRegret :
          finiteCubeRegret cap payoff Finset.univ fullWitness ≤ eta := by
        exact hselectedRegret Finset.univ
      have hfullBaseRegret :
          finiteCubeRegret cap payoff ∅ fullWitness ≤ beta := by
        exact hbaseRegret Finset.univ
      have hremainderFull :
          finiteCubeAffineRemainder payoff Finset.univ fullWitness ≤ omega :=
        (le_abs_self _).trans (hremainder Finset.univ fullWitness)
      have hsumAll :
          (∑ coordinate,
              finiteCubeRegret cap payoff {coordinate} fullWitness) ≤
            delta + ((Fintype.card Coordinate : ℝ) - 1) * beta +
              eta + omega := by
        have hidentity :=
          finiteCubeCapNonadditivity_eq_regrets_sub_remainder
            cap payoff fullWitness
        have hbaseMul :
            ((Fintype.card Coordinate : ℝ) - 1) *
                finiteCubeRegret cap payoff ∅ fullWitness ≤
              ((Fintype.card Coordinate : ℝ) - 1) * beta :=
          mul_le_mul_of_nonneg_left hfullBaseRegret hcoordinateCoefficient
        linarith
      have hsumFace :
          (∑ coordinate ∈ face,
              finiteCubeRegret cap payoff {coordinate} fullWitness) ≤
            delta + ((Fintype.card Coordinate : ℝ) - 1) * beta +
              eta + omega := by
        apply (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ face) ?_).trans hsumAll
        intro coordinate _hcoordinate _hcoordinateFace
        exact hregretNonneg {coordinate} fullWitness
      let faceWitness := witness face
      have hpayoffSingleton :
          (∑ coordinate ∈ face,
              (payoff {coordinate} faceWitness -
                payoff {coordinate} fullWitness)) ≤
            ∑ coordinate ∈ face,
              finiteCubeRegret cap payoff {coordinate} fullWitness := by
        apply Finset.sum_le_sum
        intro coordinate _hcoordinate
        dsimp only [finiteCubeRegret]
        linarith [hupper {coordinate} faceWitness]
      have hbaseDifference :
          -((face.card : ℝ) - 1) *
              (payoff ∅ faceWitness - payoff ∅ fullWitness) ≤
            ((face.card : ℝ) - 1) * beta := by
        have hpayoffIdentity :
            -(payoff ∅ faceWitness - payoff ∅ fullWitness) =
              finiteCubeRegret cap payoff ∅ faceWitness -
                finiteCubeRegret cap payoff ∅ fullWitness := by
          dsimp only [finiteCubeRegret]
          ring
        have hmulIdentity :
            -((face.card : ℝ) - 1) *
                (payoff ∅ faceWitness - payoff ∅ fullWitness) =
              ((face.card : ℝ) - 1) *
                (-(payoff ∅ faceWitness - payoff ∅ fullWitness)) := by
          ring
        rw [hmulIdentity, hpayoffIdentity]
        have hdifference :
            finiteCubeRegret cap payoff ∅ faceWitness -
                finiteCubeRegret cap payoff ∅ fullWitness ≤ beta := by
          linarith [hbaseRegret face,
            hregretNonneg ∅ fullWitness]
        exact mul_le_mul_of_nonneg_left hdifference hfaceCoefficient
      have hremainderDifference :
          finiteCubeAffineRemainder payoff face faceWitness -
              finiteCubeAffineRemainder payoff face fullWitness ≤
            2 * omega := by
        have hfirst := hremainder face faceWitness
        have hsecond := hremainder face fullWitness
        have hfirstUpper := (le_abs_self _).trans hfirst
        have hsecondLower := neg_le_of_abs_le hsecond
        linarith
      have hpayoffDifference :
          payoff face faceWitness - payoff face fullWitness ≤
            (delta + ((Fintype.card Coordinate : ℝ) - 1) * beta +
              eta + omega) +
            ((face.card : ℝ) - 1) * beta + 2 * omega := by
        have hidentity :=
          finiteCubePayoff_sub_eq_sum_sub_base_add_remainder
            payoff face faceWitness fullWitness
        linarith
      dsimp only [finiteCubeRegret]
      have hfaceApprox := happrox face
      dsimp only [faceWitness] at hfaceApprox hpayoffDifference
      linarith

/-- Positive upper-to-base witness switching, with an unattained supremum
allowed. -/
theorem upperToBase_regret_ge_supMixedDifference_sub
    (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₁ : BddAbove (Set.range f₁))
    (h₂ : BddAbove (Set.range f₂))
    (q eta : ℝ) (d : D)
    (hface : ∀ d,
      |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hupper : sSup (Set.range f₁₂) - eta ≤ f₁₂ d) :
    supMixedDifference f₀ f₁ f₂ f₁₂ - (q + eta) ≤
      baseRegret f₀ d := by
  have hf₁ : f₁ d ≤ sSup (Set.range f₁) :=
    le_csSup h₁ ⟨d, rfl⟩
  have hf₂ : f₂ d ≤ sSup (Set.range f₂) :=
    le_csSup h₂ ⟨d, rfl⟩
  have hcurvature :
      f₁₂ d - f₁ d - f₂ d + f₀ d ≤ q := by
    exact (le_abs_self _).trans (hface d)
  dsimp [supMixedDifference, baseRegret]
  linarith

/-- Negative side-to-opposite-side witness switching from corner `1` to
corner `2`, with an unattained supremum allowed. -/
theorem sideOneToSideTwo_regret_ge_neg_supMixedDifference_sub
    (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₀ : BddAbove (Set.range f₀))
    (h₁₂ : BddAbove (Set.range f₁₂))
    (q eta : ℝ) (d : D)
    (hface : ∀ d,
      |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hside : sSup (Set.range f₁) - eta ≤ f₁ d) :
    -supMixedDifference f₀ f₁ f₂ f₁₂ - (q + eta) ≤
      oppositeRegret₂ f₂ d := by
  have hf₀ : f₀ d ≤ sSup (Set.range f₀) :=
    le_csSup h₀ ⟨d, rfl⟩
  have hf₁₂ : f₁₂ d ≤ sSup (Set.range f₁₂) :=
    le_csSup h₁₂ ⟨d, rfl⟩
  have hcurvature :
      -q ≤ f₁₂ d - f₁ d - f₂ d + f₀ d := by
    exact neg_le_of_abs_le (hface d)
  dsimp [supMixedDifference, oppositeRegret₂]
  linarith

/-- Negative side-to-opposite-side witness switching from corner `2` to
corner `1`, with an unattained supremum allowed. -/
theorem sideTwoToSideOne_regret_ge_neg_supMixedDifference_sub
    (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₀ : BddAbove (Set.range f₀))
    (h₁₂ : BddAbove (Set.range f₁₂))
    (q eta : ℝ) (d : D)
    (hface : ∀ d,
      |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hside : sSup (Set.range f₂) - eta ≤ f₂ d) :
    -supMixedDifference f₀ f₁ f₂ f₁₂ - (q + eta) ≤
      oppositeRegret₁ f₁ d := by
  have hf₀ : f₀ d ≤ sSup (Set.range f₀) :=
    le_csSup h₀ ⟨d, rfl⟩
  have hf₁₂ : f₁₂ d ≤ sSup (Set.range f₁₂) :=
    le_csSup h₁₂ ⟨d, rfl⟩
  have hcurvature :
      -q ≤ f₁₂ d - f₁ d - f₂ d + f₀ d := by
    exact neg_le_of_abs_le (hface d)
  dsimp [supMixedDifference, oppositeRegret₁]
  linarith

/-- **Oriented four-corner witness switch with all quantitative data.**

If the absolute curvature of a supremum envelope exceeds the uniform
fixed-witness square budget by `charge + 3 * eta`, the proof selects one of
the two diagonal orientations.  Its source witness is `eta`-optimal, has
receiving regret at least `charge + 2 * eta`, and can be replaced by an
`eta`-optimal receiving witness whose direct gain is at least
`charge + eta`.  The reverse source edge costs at most `eta`, leaving an
oriented rectangle of at least `charge`.

The disjunction is proof-selected; its branches need not be exclusive. -/
theorem orientedSupremumWitnessSwitch_of_abs_mixedDifference
    [Nonempty D] (f₀ f₁ f₂ f₁₂ : D → ℝ)
    (h₀ : BddAbove (Set.range f₀))
    (h₁ : BddAbove (Set.range f₁))
    (h₂ : BddAbove (Set.range f₂))
    (h₁₂ : BddAbove (Set.range f₁₂))
    (q charge eta : ℝ) (heta : 0 < eta)
    (hface : ∀ d, |f₁₂ d - f₁ d - f₂ d + f₀ d| ≤ q)
    (hcurvature : charge + q + 3 * eta ≤
      |supMixedDifference f₀ f₁ f₂ f₁₂|) :
    HasOrientedSupremumWitnessSwitch f₁₂ f₀ charge eta ∨
      HasOrientedSupremumWitnessSwitch f₁ f₂ charge eta := by
  by_cases hnonneg : 0 ≤ supMixedDifference f₀ f₁ f₂ f₁₂
  · left
    obtain ⟨sourceWitness, hsourceApprox⟩ :=
      exists_ge_sSup_sub f₁₂ eta heta
    have hraw := upperToBase_regret_ge_supMixedDifference_sub
      f₀ f₁ f₂ f₁₂ h₁ h₂ q eta sourceWitness hface
        hsourceApprox
    have hcurvature' : charge + q + 3 * eta ≤
        supMixedDifference f₀ f₁ f₂ f₁₂ := by
      simpa only [abs_of_nonneg hnonneg] using hcurvature
    apply orientedSupremumWitnessSwitch_of_regret
      f₁₂ f₀ h₁₂ charge eta heta sourceWitness
        hsourceApprox
    dsimp only [baseRegret] at hraw
    linarith
  · right
    have hnegative : supMixedDifference f₀ f₁ f₂ f₁₂ < 0 :=
      lt_of_not_ge hnonneg
    obtain ⟨sourceWitness, hsourceApprox⟩ :=
      exists_ge_sSup_sub f₁ eta heta
    have hraw := sideOneToSideTwo_regret_ge_neg_supMixedDifference_sub
      f₀ f₁ f₂ f₁₂ h₀ h₁₂ q eta sourceWitness hface
        hsourceApprox
    have hcurvature' : charge + q + 3 * eta ≤
        -supMixedDifference f₀ f₁ f₂ f₁₂ := by
      simpa only [abs_of_neg hnegative] using hcurvature
    apply orientedSupremumWitnessSwitch_of_regret
      f₁ f₂ h₁ charge eta heta sourceWitness hsourceApprox
    dsimp only [oppositeRegret₂] at hraw
    linarith

/-- Pointwise mixed curvature of a debt difference is the envelope curvature
minus the prescribed-payoff curvature. -/
theorem debtMixedDifference_eq_envelope_sub_prescribed
    (envelope prescribed : D → ℝ)
    (base one two both : D) :
    ((envelope both - prescribed both) -
        (envelope one - prescribed one) -
        (envelope two - prescribed two) +
        (envelope base - prescribed base)) =
      (envelope both - envelope one - envelope two + envelope base) -
        (prescribed both - prescribed one - prescribed two + prescribed base) := by
  ring

/-- A positive weighted average of oriented regrets contains a positive
oriented pure component. -/
theorem exists_pos_regret_difference_of_weighted_pos
    {ι : Type*} [Fintype ι]
    (weight source target : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : 0 < ∑ i, weight i * (source i - target i)) :
    ∃ i, 0 < source i - target i := by
  by_contra hnone
  push Not at hnone
  have hsum : ∑ i, weight i * (source i - target i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hweight i) (hnone i)
  linarith

end Math.Optimization
