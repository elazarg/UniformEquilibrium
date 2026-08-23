/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.Trichotomy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.UniformPayoffBridge
import UniformEquilibrium.Quitting.Classification.Circulant.TrichotomyClosure

/-!
# The five-player circulant trichotomy, against the regime

`UniformEquilibrium/Quitting/Classification/Circulant/TrichotomyClosure.lean`
assembles the firing-step, solo-exit, and complementary-pocket branches of the
five-player circulant trichotomy without reference to
`QuittingCounterexampleRegime`.  This module reads each branch against the
regime, and assembles the resulting census: a rotation-symmetric table with
nonnegative solo self value and nonpositive join margins either carries no
counterexample regime, or has positive margin sum with negative margins
forming exactly one complementary pair — and even that residual closes once
either of the two cap pairs of its pocket holds.

## Main results

* `isEmpty_counterexampleRegime_of_isFiringStep` — the firing-step branch
* `isEmpty_counterexampleRegime_of_nonneg_margins` — the solo exit branch
* `isEmpty_counterexampleRegime_of_unique_nonneg` — three negative margins
* `isEmpty_counterexampleRegime_of_neighbourPocket` and
  `isEmpty_counterexampleRegime_of_distantPocket` — either pocket at either cap
* `isEmpty_counterexampleRegime_of_nonpositiveSum_or_isFiringStep` — the two
  branches together
* `isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin` and
  `isEmpty_counterexampleRegime_or_isComplementaryPocketMargin` — the closure
  up to the complementary pockets, and the census they leave
* `isEmpty_counterexampleRegime_or_uncappedComplementaryPocket` — the same
  census with the four cap pairs removed from the residual
-/

noncomputable section

namespace GameTheory
namespace CirculantTrichotomyClosure

open QuittingLCPClassification CirculantConstantStepCycle

variable {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
  {s : ℝ} {m J : ZMod 5 → ℝ}

/-! ## The firing-step branch -/

/-- The firing-step branch, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_isFiringStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {c : ZMod 5} (hfire : IsFiringStep m c)
    (hjoin : ∀ k : ZMod 5, k ≠ 0 → J (k * c) ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_of_isFiringStep htable hs hsum hfire hjoin)

/-! ## The solo exit branch -/

/-- The solo exit branch, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_nonneg_margins
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm : ∀ d : ZMod 5, d ≠ 0 → 0 ≤ m d) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_of_nonneg_margins htable hs hjoin hm)

/-! ## Three negative margins -/

/-- Three negative margins, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_of_unique_nonneg
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hsum : 0 < ∑ e, m e) {g : ZMod 5} (hgm : 0 ≤ m g)
    (hother : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_quittingCounterexampleRegime_of_exists_uniformEquilibriumPayoff _
    (exists_uniformEquilibriumPayoff_of_unique_nonneg htable hs hsum hgm hother
      hjoin)

/-! ## The neighbour pocket -/

/-- **The neighbour pocket at either cap.**  In the pocket proper both cycles
are available in principle, and the pocket closes as soon as one of the two
cap pairs holds. -/
theorem isEmpty_counterexampleRegime_of_neighbourPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm1 : m 1 < 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < ∑ e, m e)
    (hcap : (J 1 ≤ m 1 ∧ J 2 ≤ m 1) ∨ (J 3 ≤ m 4 ∧ J 4 ≤ m 4)) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff ?_⟩
  rcases hcap with ⟨hone, htwo⟩ | ⟨hthree, hfour⟩
  · exact exists_uniformEquilibriumPayoff_of_neighbourPocket htable hs hm1.le hm4
      hm2 hsum (hjoin 3 (by decide)) (hjoin 4 (by decide)) hone htwo
  · exact exists_uniformEquilibriumPayoff_of_neighbourPocket_stepOne htable hs hm1
      hm4.le hm3 hsum (hjoin 1 (by decide)) (hjoin 2 (by decide)) hthree hfour

/-! ## The distant pocket -/

/-- **The distant pocket at either cap.** -/
theorem isEmpty_counterexampleRegime_of_distantPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hm2 : m 2 < 0) (hm3 : m 3 < 0) (hm4 : 0 ≤ m 4) (hm1 : 0 ≤ m 1)
    (hsum : 0 < ∑ e, m e)
    (hcap : (J 1 ≤ m 3 ∧ J 3 ≤ m 3) ∨ (J 2 ≤ m 2 ∧ J 4 ≤ m 2)) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff ?_⟩
  rcases hcap with ⟨hone, hthree⟩ | ⟨htwo, hfour⟩
  · exact exists_uniformEquilibriumPayoff_of_distantPocket htable hs hm2 hm3.le
      hm1 hsum (hjoin 2 (by decide)) (hjoin 4 (by decide)) hone hthree
  · exact exists_uniformEquilibriumPayoff_of_distantPocket_stepThree htable hs hm3
      hm2.le hm4 hsum (hjoin 3 (by decide)) (hjoin 1 (by decide)) hfour htwo

/-! ## The branches together -/

/-- **The two branches together.**  A rotation-symmetric table with nonnegative
solo self value and nonpositive join margins carries no counterexample regime as
soon as its margin sum is nonpositive, or some step fires. -/
theorem isEmpty_counterexampleRegime_of_nonpositiveSum_or_isFiringStep
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hbranch : (∑ e, m e) ≤ 0 ∨ ∃ c : ZMod 5, IsFiringStep m c) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  have hcirculant := hasCirculantSoloMatrix_of_isCirculantPairTable htable
  rcases hbranch with hsum | ⟨c, hfire⟩
  · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
      hcirculant hsum
  · by_cases hsum : (∑ e, m e) ≤ 0
    · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
        hcirculant hsum
    · exact isEmpty_counterexampleRegime_of_isFiringStep htable hs (not_le.mp hsum)
        hfire fun k hk => hjoin (k * c) (mul_ne_zero_five k c hk hfire.1)

/-- **The closure up to the complementary pockets.**  A rotation-symmetric
table with nonnegative solo self value and nonpositive join margins carries no
counterexample regime unless its margin sum is positive and its negative
margins are exactly one complementary pair.

Three producers divide the sign patterns between them.  Nonpositive margin sum
is the failure of standard `Q`.  Positive margin sum with a negative margin and
no complementary pocket has a firing step.  No negative margin at all leaves
the solo exit self-enforcing. -/
theorem isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0)
    (hbranch : (∑ e, m e) ≤ 0 ∨ ¬ IsComplementaryPocketMargin m) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  rcases hbranch with hsum | hpocket
  · exact isEmpty_counterexampleRegime_of_pentagonCirculant_surplus_nonpos
      (hasCirculantSoloMatrix_of_isCirculantPairTable htable) hsum
  · by_cases hneg : ∃ a : ZMod 5, a ≠ 0 ∧ m a < 0
    · refine isEmpty_counterexampleRegime_of_nonpositiveSum_or_isFiringStep htable
        hs hjoin ?_
      by_cases hsum : (∑ e, m e) ≤ 0
      · exact Or.inl hsum
      · exact Or.inr
          (exists_isFiringStep htable.margin_zero (not_le.mp hsum) hneg hpocket)
    · refine isEmpty_counterexampleRegime_of_nonneg_margins htable hs hjoin ?_
      intro d hd
      rcases le_or_gt 0 (m d) with h | h
      · exact h
      · exact absurd ⟨d, hd, h⟩ hneg

/-- **The census.**  A rotation-symmetric table with nonnegative solo self
value and nonpositive join margins either carries no counterexample regime, or
has positive margin sum and negative margins forming exactly one complementary
pair.  No sign pattern is left unaccounted for. -/
theorem isEmpty_counterexampleRegime_or_isComplementaryPocketMargin
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) ∨
      (0 < ∑ e, m e ∧ IsComplementaryPocketMargin m) := by
  by_cases hpocket : IsComplementaryPocketMargin m
  · by_cases hsum : (∑ e, m e) ≤ 0
    · exact Or.inl (isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin
        htable hs hjoin (Or.inl hsum))
    · exact Or.inr ⟨not_le.mp hsum, hpocket⟩
  · exact Or.inl (isEmpty_counterexampleRegime_of_not_isComplementaryPocketMargin
      htable hs hjoin (Or.inr hpocket))

/-- **The census at the pocket caps.**  A rotation-symmetric table with
nonnegative solo self value and nonpositive join margins either carries no
counterexample regime, or has positive margin sum, negative margins forming
exactly one complementary pair, and *both* cap pairs of that pocket violated.

Against `isEmpty_counterexampleRegime_or_isComplementaryPocketMargin` this
removes from the residual every pocket table meeting one of its two cap pairs.
For the neighbour pocket the two pairs are `J 1, J 2 ≤ m 1` (step four) and
`J 3, J 4 ≤ m 4` (step one); for the distant pocket they are `J 1, J 3 ≤ m 3`
(step two) and `J 2, J 4 ≤ m 2` (step three).  What survives is a table whose
join margins are nonpositive yet still strictly above both negative margins of
its own pocket, in one coordinate of each cap pair. -/
theorem isEmpty_counterexampleRegime_or_uncappedComplementaryPocket
    (htable : IsCirculantPairTable reward s m J) (hs : 0 ≤ s)
    (hjoin : ∀ d : ZMod 5, d ≠ 0 → J d ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime reward) ∨
      (0 < ∑ e, m e ∧
        ((m 1 < 0 ∧ m 4 < 0 ∧ 0 ≤ m 2 ∧ 0 ≤ m 3 ∧
            (m 1 < J 1 ∨ m 1 < J 2) ∧ (m 4 < J 3 ∨ m 4 < J 4)) ∨
          (m 2 < 0 ∧ m 3 < 0 ∧ 0 ≤ m 4 ∧ 0 ≤ m 1 ∧
            (m 3 < J 1 ∨ m 3 < J 3) ∧ (m 2 < J 2 ∨ m 2 < J 4)))) := by
  rcases isEmpty_counterexampleRegime_or_isComplementaryPocketMargin htable hs
    hjoin with hempty | ⟨hsum, hpocket⟩
  · exact Or.inl hempty
  rcases neighbour_or_distant_of_isComplementaryPocketMargin hpocket with
    ⟨hm1, hm4, hm2, hm3⟩ | ⟨hm2, hm3, hm4, hm1⟩
  · by_cases hfirst : J 1 ≤ m 1 ∧ J 2 ≤ m 1
    · exact Or.inl (isEmpty_counterexampleRegime_of_neighbourPocket htable hs hjoin
        hm1 hm4 hm2 hm3 hsum (Or.inl hfirst))
    by_cases hsecond : J 3 ≤ m 4 ∧ J 4 ≤ m 4
    · exact Or.inl (isEmpty_counterexampleRegime_of_neighbourPocket htable hs hjoin
        hm1 hm4 hm2 hm3 hsum (Or.inr hsecond))
    refine Or.inr ⟨hsum, Or.inl ⟨hm1, hm4, hm2, hm3, ?_, ?_⟩⟩
    · rcases not_and_or.mp hfirst with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    · rcases not_and_or.mp hsecond with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
  · by_cases hfirst : J 1 ≤ m 3 ∧ J 3 ≤ m 3
    · exact Or.inl (isEmpty_counterexampleRegime_of_distantPocket htable hs hjoin
        hm2 hm3 hm4 hm1 hsum (Or.inl hfirst))
    by_cases hsecond : J 2 ≤ m 2 ∧ J 4 ≤ m 2
    · exact Or.inl (isEmpty_counterexampleRegime_of_distantPocket htable hs hjoin
        hm2 hm3 hm4 hm1 hsum (Or.inr hsecond))
    refine Or.inr ⟨hsum, Or.inr ⟨hm2, hm3, hm4, hm1, ?_, ?_⟩⟩
    · rcases not_and_or.mp hfirst with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    · rcases not_and_or.mp hsecond with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)

end CirculantTrichotomyClosure
end GameTheory
