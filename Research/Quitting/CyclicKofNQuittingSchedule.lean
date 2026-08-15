/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNArithmetic
import Research.Quitting.ActiveSetSupport
import Research.Quitting.KActiveCompactPath

/-!
# Cyclic `K/N` blocks as literal quitting-game schedules

`CyclicKofNArithmetic` classifies the possible compression of a translated
`K`-block.  This file connects that combinatorics to quitting games.

The distinct translates are enumerated periodically.  Giving every player in
the current block one common positive hazard `β` produces a behavioral root
whose positive-hazard support is *exactly* the block.  Consequently:

* every stage is literally `K`-active;
* the schedule repeats after the translation-orbit length;
* the orbit length obeys the `N / gcd(K,N)` denominator obstruction; and
* every exact Bellman spine respecting this schedule has degree at most `K`.

No payoff feasibility is asserted here.  The construction is the public
support/clock adapter that can be combined with a payoff-specific circulation
or Bellman certificate.
-/

namespace GameTheory

namespace CyclicKofNQuittingSchedule

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic
open scoped BigOperators Pointwise

noncomputable section

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]

/-! ## A periodic enumeration of the distinct translates -/

/-- Enumerate the finite translation orbit in an arbitrary fixed order and
repeat it periodically. -/
def translationClock (A : Finset G) (time : ℕ) : TranslationPhase A :=
  (Fintype.equivFin (TranslationPhase A)).symm
    ⟨time % Fintype.card (TranslationPhase A),
      Nat.mod_lt _ (Fintype.card_pos_iff.mpr inferInstance)⟩

/-- The clock has the translation-orbit cardinality as a period. -/
theorem translationClock_add_period (A : Finset G) (time : ℕ) :
    translationClock A (time + Fintype.card (TranslationPhase A)) =
      translationClock A time := by
  apply (Fintype.equivFin (TranslationPhase A)).injective
  apply Fin.ext
  simp [translationClock]

/-- Every distinct translate occurs within one clock period. -/
theorem translationClock_surjective_period (A : Finset G)
    (B : TranslationPhase A) :
    ∃ time < Fintype.card (TranslationPhase A),
      translationClock A time = B := by
  let index := Fintype.equivFin (TranslationPhase A) B
  refine ⟨index, index.isLt, ?_⟩
  unfold translationClock
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  change index.val % Fintype.card (TranslationPhase A) = index.val
  exact Nat.mod_eq_of_lt index.isLt

/-- The public infinite schedule obtained by cycling through the distinct
translates of `A`. -/
def cyclicSchedule (A : Finset G) : QuittingKActiveSchedule G A.card where
  active := fun time => orbitSchedule A (translationClock A time)
  card_le := fun time => (orbitSchedule_phaseLoad A (translationClock A time)).le

@[simp] theorem cyclicSchedule_active (A : Finset G) (time : ℕ) :
    (cyclicSchedule A).active time = orbitSchedule A (translationClock A time) :=
  rfl

/-- The active-set schedule repeats after its orbit length. -/
theorem cyclicSchedule_active_add_period (A : Finset G) (time : ℕ) :
    (cyclicSchedule A).active
        (time + Fintype.card (TranslationPhase A)) =
      (cyclicSchedule A).active time := by
  change orbitSchedule A
      (translationClock A (time + Fintype.card (TranslationPhase A))) =
    orbitSchedule A (translationClock A time)
  rw [translationClock_add_period]

/-- Every scheduled active set has exactly `|A|`, not merely at most `|A|`,
players. -/
theorem card_cyclicSchedule_active (A : Finset G) (time : ℕ) :
    ((cyclicSchedule A).active time).card = A.card :=
  orbitSchedule_phaseLoad A (translationClock A time)

/-- The period of the cyclic quitting schedule satisfies the sharp reduced
denominator obstruction. -/
theorem reducedPopulation_dvd_cyclicSchedule_period (A : Finset G) :
    Fintype.card G / A.card.gcd (Fintype.card G) ∣
      Fintype.card (TranslationPhase A) :=
  reducedPopulation_dvd_card_translationPhase A

/-- A one-at-a-time balanced cyclic quitting schedule has exactly one phase
per player. -/
theorem oneActive_cyclicSchedule_period_eq_population
    (A : Finset G) (hA : A.card = 1) :
    Fintype.card (TranslationPhase A) = Fintype.card G :=
  card_translationPhase_eq_card_of_singleton A hA

/-- A three-at-a-time cyclic schedule has either `N` phases or `N/3`
phases. -/
theorem threeActive_cyclicSchedule_period_classification
    (A : Finset G) (hA : A.card = 3) :
    Fintype.card (TranslationPhase A) = Fintype.card G ∨
      Fintype.card (TranslationPhase A) = Fintype.card G / 3 := by
  have hprime : Nat.Prime A.card := by simpa [hA] using Nat.prime_three
  simpa [hA] using
    card_translationPhase_eq_card_or_div_card_of_prime A hprime

/-- A four-at-a-time cyclic schedule has exactly one of the three arithmetic
periods `N`, `N/2`, and `N/4`. -/
theorem fourActive_cyclicSchedule_period_classification
    (A : Finset G) (hA : A.card = 4) :
    Fintype.card (TranslationPhase A) = Fintype.card G ∨
      Fintype.card (TranslationPhase A) = Fintype.card G / 2 ∨
        Fintype.card (TranslationPhase A) = Fintype.card G / 4 :=
  card_translationPhase_eq_card_or_half_or_quarter A hA

/-- In the `4/5` case no collapse is possible. -/
theorem fourOfFive_cyclicSchedule_period_eq_five
    (A : Finset G) (hA : A.card = 4) (hG : Fintype.card G = 5) :
    Fintype.card (TranslationPhase A) = 5 := by
  have hcoprime : Nat.Coprime A.card (Fintype.card G) := by
    rw [hA, hG]
    decide
  simpa [hG] using card_translationPhase_eq_card_of_coprime A hcoprime

/-! ## Turning blocks into literal positive-hazard supports -/

/-- A root with common hazard `β` on `active` and forced Continue outside. -/
def uniformActiveRoot (active : Finset G) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : G → PMF Bool :=
  quittingActiveRoot active (fun _ => quittingHazardCoin β hβ0 hβ1)

omit [AddGroup G] [Fintype G] in
/-- The uniform active root respects its prescribed active set. -/
theorem isQuittingActiveRoot_uniformActiveRoot
    (active : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsQuittingActiveRoot active (uniformActiveRoot active β hβ0 hβ1) :=
  isQuittingActiveRoot_quittingActiveRoot active _

omit [AddGroup G] in
/-- With positive common hazard, the canonical positive-hazard support is
exactly the prescribed active set. -/
theorem quittingPositiveHazardSupport_uniformActiveRoot
    (active : Finset G) (β : ℝ) (hβ1 : β ≤ 1)
    (hβpos : 0 < β) :
    quittingPositiveHazardSupport (uniformActiveRoot active β hβpos.le hβ1) =
      active := by
  ext who
  by_cases hwho : who ∈ active
  · simp [quittingPositiveHazardSupport, uniformActiveRoot,
      hwho, hazardOfRoot,
      quittingHazardCoin_true_toReal, hβpos]
  · simp [quittingPositiveHazardSupport, uniformActiveRoot,
      hazardOfRoot_quittingActiveRoot, hwho]

/-- Put the uniform positive hazard on the current cyclic block. -/
def cyclicRoots (A : Finset G) (β : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : ℕ → G → PMF Bool :=
  fun time => uniformActiveRoot ((cyclicSchedule A).active time) β hβ0 hβ1

/-- The root sequence respects the public cyclic schedule. -/
theorem cyclicRoots_respects_schedule
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsQuittingActiveScheduleRoot (cyclicSchedule A)
      (cyclicRoots A β hβ0 hβ1) := by
  intro time
  exact isQuittingActiveRoot_uniformActiveRoot _ β hβ0 hβ1

/-- Every root in the cyclic sequence has exactly `|A|` positive quitting
hazards. -/
theorem card_positiveHazardSupport_cyclicRoots
    (A : Finset G) (β : ℝ) (hβ1 : β ≤ 1)
    (hβpos : 0 < β) (time : ℕ) :
    (quittingPositiveHazardSupport (cyclicRoots A β hβpos.le hβ1 time)).card =
      A.card := by
  unfold cyclicRoots
  rw [quittingPositiveHazardSupport_uniformActiveRoot _ β hβ1 hβpos]
  exact card_cyclicSchedule_active A time

/-- In particular, the roots satisfy the literal support-card predicate used
by compact `K`-active path extraction. -/
theorem hasQuittingSupportCardAtMost_cyclicRoots
    (A : Finset G) (β : ℝ) (hβ1 : β ≤ 1)
    (hβpos : 0 < β) (time : ℕ) :
    HasQuittingSupportCardAtMost A.card
      (cyclicRoots A β hβpos.le hβ1 time) := by
  unfold HasQuittingSupportCardAtMost
  rw [card_positiveHazardSupport_cyclicRoots A β hβ1 hβpos time]

/-- The cyclic root sequence itself repeats after the translation-orbit
period. -/
theorem cyclicRoots_add_period
    (A : Finset G) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (time : ℕ) :
    cyclicRoots A β hβ0 hβ1
        (time + Fintype.card (TranslationPhase A)) =
      cyclicRoots A β hβ0 hβ1 time := by
  unfold cyclicRoots
  rw [cyclicSchedule_active_add_period]

/-! ## Bellman degree consequence -/

/-- Any exact quitting Bellman spine respecting the cyclic block schedule
has a recursion polynomial of degree at most the block size, independently
of the ambient population. -/
theorem exactBellmanSpine_value_eq_next_add_sum_layers_of_cyclicSchedule
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (value : ℕ → Payoff G) (roots : ℕ → G → PMF Bool)
    (A : Finset G)
    (hsupport : IsQuittingActiveScheduleRoot (cyclicSchedule A) roots)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (time : ℕ) (who : G) :
    value time who = value (time + 1) who +
      ∑ degree ∈ Finset.range (A.card + 1),
        quittingActiveMobiusLayer reward (value (time + 1))
          ((cyclicSchedule A).active time) (roots time) who degree := by
  exact exactBellmanSpine_value_eq_next_add_sum_layers_of_activeSchedule
    reward value roots (cyclicSchedule A) hsupport hspine time who

/-- For a singleton block the cyclic Bellman recursion is affine: every
collision layer vanishes.  The ownership clock still has `N` phases by
`oneActive_cyclicSchedule_period_eq_population`. -/
theorem exactBellmanSpine_value_eq_next_add_singletonLayer_of_cyclicSchedule
    (reward : {S : Finset G // S.Nonempty} → Payoff G)
    (value : ℕ → Payoff G) (roots : ℕ → G → PMF Bool)
    (A : Finset G) (hA : A.card = 1)
    (hsupport : IsQuittingActiveScheduleRoot (cyclicSchedule A) roots)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (time : ℕ) (who : G) :
    value time who = value (time + 1) who +
      quittingActiveMobiusLayer reward (value (time + 1))
        ((cyclicSchedule A).active time) (roots time) who 1 := by
  rw [exactBellmanSpine_value_eq_next_add_sum_layers_of_cyclicSchedule
    reward value roots A hsupport hspine time who]
  have hrange : Finset.range (A.card + 1) = Finset.range 2 := by rw [hA]
  rw [hrange]
  simp [Finset.sum_range_succ]

end

end CyclicKofNQuittingSchedule

end GameTheory
