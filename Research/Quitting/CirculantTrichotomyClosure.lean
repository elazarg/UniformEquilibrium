/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CirculantConstantStepCycle
import Research.Quitting.CirculantPocketAnchoredNoGo

/-!
# Assembling the branches of the five-player circulant trichotomy

For a five-player table whose singleton and two-element rows are rotation
symmetric, three branches are available.

* Nonpositive margin sum makes the normalized solo matrix fail standard `Q`,
  and the counterexample gate is collapsed by
  `Research/Quitting/CirculantTrichotomy.lean`.
* Positive margin sum together with a step `c` whose own margin is negative
  while the margins at `4 * c` and `3 * c` — the complementary and doubled
  complementary distances — are nonnegative puts an anchor root strictly inside
  the unit interval, at which the four floor inequalities of the constant-step
  producer of `Research/Quitting/CirculantConstantStepCycle.lean` reduce to
  nonpositivity of the join margins along the same progression.  The floor at
  the deepest elapsed phase needs no sign hypothesis at all: the anchor
  equation itself makes the backward partial sum positive.
* Everything else.

This module proves the first two and delimits the third.  Two obstruction
lemmas record where the step sign condition is unavailable: when three of the
four nonzero margins are negative, and when the negatives occupy one
complementary pair.  Both are statements about that *sign condition* only.  A
table can still carry a constant-step equilibrium without meeting it, by
satisfying the producer's floor inequalities directly.

## Main definitions

* `ConstantStepCyclicResolution` — the proposition that the step sign condition
  resolves a table of positive margin sum with no hypothesis on rows of two or
  more players

## Main results

* `hasCirculantSoloMatrix_of_isCirculantPairTable` — rotation-symmetric
  singleton rows give a circulant normalized solo matrix
* `exists_uniformEquilibriumPayoff_of_negativeStep` and
  `isEmpty_counterexampleRegime_of_negativeStep` — the step branch
* `isEmpty_counterexampleRegime_of_nonpositiveSum_or_negativeStep` — the two
  branches together
* `not_exists_negativeStep_of_unique_nonneg` and
  `not_exists_negativeStep_of_isOpenPocketMargin` — where the sign condition is
  unavailable
-/

noncomputable section

namespace GameTheory
namespace CirculantTrichotomyClosure

open QuittingLCPClassification CirculantConstantStepCycle

/-! ## Arithmetic of the five-cycle -/

theorem mul_ne_zero_five : ∀ k c : ZMod 5, k ≠ 0 → c ≠ 0 → k * c ≠ 0 := by decide

theorem exists_mul_eq_neg_one : ∀ c : ZMod 5, c ≠ 0 → ∃ c' : ZMod 5, c * c' = -1 := by
  decide

/-! ## Rotation-symmetric singleton rows -/

variable {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
  {s : ℝ} {m J : ZMod 5 → ℝ}

/-- Rotation-symmetric singleton rows around a common solo self value give a
circulant normalized solo matrix with the same margin vector: the common value
cancels against each receiver's own solo payoff. -/
theorem hasCirculantSoloMatrix_of_isCirculantPairTable
    (htable : IsCirculantPairTable reward s m J) :
    HasCirculantSoloMatrix reward m := by
  funext who owner
  show (normalizedQuittingPayoffTable reward).singletonMatrix who owner =
    m (owner - who)
  rw [normalized_singletonMatrix_eq_quittingSingletonMatrix, quittingSingletonMatrix,
    show (⟨{owner}, Finset.singleton_nonempty owner⟩ :
        {S : Finset (ZMod 5) // S.Nonempty}) = quittingSingletonTerminal owner from rfl,
    show (⟨{who}, Finset.singleton_nonempty who⟩ :
        {S : Finset (ZMod 5) // S.Nonempty}) = quittingSingletonTerminal who from rfl,
    htable.singleton, htable.singleton, sub_self, htable.margin_zero]
  ring

/-! ## The step branch -/

/-- The backward partial sum of the constant-step anchor, written the way the
constant-step producer's second floor reads it. -/
theorem constantStepAnchorTail_eq (m : ZMod 5 → ℝ) (c : ZMod 5) (q : ℝ) :
    constantStepAnchorTail m c q =
      m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c) := by
  rw [constantStepAnchorTail, Math.cubicAnchorTail]
  norm_num [nsmul_eq_mul]
  ring

/-- **The step branch.**  A rotation-symmetric table of positive margin sum
whose join margins along the progression of a step `c` are nonpositive, and
whose margins satisfy `m c < 0 ≤ m (4 * c)` and `0 ≤ m (3 * c)`, has an
ordinary uniform-equilibrium payoff.

The anchor root supplies the first floor and, through positivity of the
backward partial sum at that root, the second; the two margin sign hypotheses
supply the remaining two. -/
theorem exists_uniformEquilibriumPayoff_of_negativeStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {c : ZMod 5} (hc : c ≠ 0) (hneg : m c < 0)
    (hcomplement : 0 ≤ m (4 * c)) (hdoubled : 0 ≤ m (3 * c))
    (hjoin : ∀ k : ZMod 5, k ≠ 0 → J (k * c) ≤ 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨q, hq, hroot, htail⟩ :=
    exists_constantStepAnchor_root_zmod_five m htable.margin_zero hc hneg hsum
  obtain ⟨c', hcc'⟩ := exists_mul_eq_neg_one c hc
  have hrootStep : stepAnchor m c q = 0 :=
    (stepAnchor_eq_constantStepAnchor m c q).trans hroot
  have hfloor₁ : J c ≤ 0 := by
    have := hjoin 1 (by decide)
    rwa [one_mul] at this
  have hfloor₂ : J (2 * c) ≤ m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c) := by
    rw [constantStepAnchorTail_eq] at htail
    linarith [hjoin 2 (by decide)]
  have hfloor₃ : J (3 * c) ≤ m (3 * c) + q * m (4 * c) := by
    have hqm : 0 ≤ q * m (4 * c) := mul_nonneg hq.1.le hcomplement
    linarith [hjoin 3 (by decide)]
  have hfloor₄ : J (4 * c) ≤ m (4 * c) := by
    linarith [hjoin 4 (by decide)]
  exact ⟨_, isUniformEquilibriumPayoff_constantStep htable hcc' hs hq.1 hq.2
    hrootStep hfloor₁ hfloor₂ hfloor₃ hfloor₄⟩

/-- The step branch, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_negativeStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {c : ZMod 5} (hc : c ≠ 0) (hneg : m c < 0)
    (hcomplement : 0 ≤ m (4 * c)) (hdoubled : 0 ≤ m (3 * c))
    (hjoin : ∀ k : ZMod 5, k ≠ 0 → J (k * c) ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_of_negativeStep htable hs hsum hc hneg
      hcomplement hdoubled hjoin)⟩

/-- **The two branches together.**  A rotation-symmetric table with nonnegative
solo self value and nonpositive join margins carries no counterexample regime as
soon as its margin sum is nonpositive, or some step has negative margin with
nonnegative complementary and doubled complementary margins. -/
theorem isEmpty_counterexampleRegime_of_nonpositiveSum_or_negativeStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hbranch : (∑ e, m e) ≤ 0 ∨
      ∃ c : ZMod 5, c ≠ 0 ∧ m c < 0 ∧ 0 ≤ m (4 * c) ∧ 0 ≤ m (3 * c)) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  have hcirculant := hasCirculantSoloMatrix_of_isCirculantPairTable htable
  rcases hbranch with hsum | ⟨c, hc, hneg, hcomplement, hdoubled⟩
  · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
      hcirculant hsum
  · by_cases hsum : (∑ e, m e) ≤ 0
    · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
        hcirculant hsum
    · exact isEmpty_counterexampleRegime_of_negativeStep htable hs (not_le.mp hsum)
        hc hneg hcomplement hdoubled fun k hk =>
          hjoin (k * c) (mul_ne_zero_five k c hk hc)

/-! ## Where the step sign condition is unavailable -/

/-- **At most one nonnegative margin leaves no step.**  If every nonzero
distance other than `g` carries a negative margin, no step meets the sign
condition: its complementary and doubled complementary distances would both
have to be `g`, forcing the step to vanish.  Three negative margins are the
case where `g` is the single nonnegative distance, and four negative margins
the case `g = 0`. -/
theorem not_exists_negativeStep_of_unique_nonneg {g : ZMod 5}
    (hnegative : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0) :
    ¬ ∃ c : ZMod 5, c ≠ 0 ∧ m c < 0 ∧ 0 ≤ m (4 * c) ∧ 0 ≤ m (3 * c) := by
  rintro ⟨c, hc, hneg, hcomplement, hdoubled⟩
  have hfour : 4 * c = g := by
    by_contra hne
    exact absurd hcomplement
      (not_le.mpr (hnegative _ (mul_ne_zero_five 4 c (by decide) hc) hne))
  have hthree : 3 * c = g := by
    by_contra hne
    exact absurd hdoubled
      (not_le.mpr (hnegative _ (mul_ne_zero_five 3 c (by decide) hc) hne))
  exact hc (by linear_combination hfour - hthree)

/-- **A complementary pair of negatives leaves no step.**  In the open pocket
the two distant margins are positive and the two neighbour margins are
negative, so a step of negative margin has a negative complementary margin. -/
theorem not_exists_negativeStep_of_isOpenPocketMargin
    (hpocket : IsOpenPocketMargin m) :
    ¬ ∃ c : ZMod 5, c ≠ 0 ∧ m c < 0 ∧ 0 ≤ m (4 * c) ∧ 0 ≤ m (3 * c) := by
  obtain ⟨hone, hfour, htwo, hthree⟩ := hpocket
  rintro ⟨c, hc, hneg, hcomplement, hdoubled⟩
  rcases zmod_five_cases c with h | h | h | h | h <;> subst h
  · exact hc rfl
  · rw [show (4 : ZMod 5) * 1 = 4 from by decide] at hcomplement
    linarith
  · linarith
  · linarith
  · rw [show (4 : ZMod 5) * 4 = 1 from by decide] at hcomplement
    linarith

/-! ## The residual -/

/-- The constant-step resolution without structure on the larger rows: a
five-player table whose normalized solo matrix is circulant with positive
margin sum, and which has a step of negative margin whose complementary and
doubled complementary margins are nonnegative, has an ordinary
uniform-equilibrium payoff, whatever its rows on two or more players. -/
def ConstantStepCyclicResolution
    (reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5))
    (margin : ZMod 5 → ℝ) : Prop :=
  HasCirculantSoloMatrix reward margin →
    0 < ∑ e, margin e →
    (∃ c : ZMod 5, c ≠ 0 ∧ margin c < 0 ∧ 0 ≤ margin (4 * c) ∧
      0 ≤ margin (3 * c)) →
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff

end CirculantTrichotomyClosure
end GameTheory
