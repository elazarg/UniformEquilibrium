/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.GroupAction.CyclicKofNArithmetic
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport

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
open Math.CyclicKofNArithmetic
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

/-- Every proper translated block orbit has a phase omitting any prescribed
player. -/
theorem exists_not_mem_cyclicSchedule_active
    (A : Finset G) (hproper : A ≠ Finset.univ) (player : G) :
    ∃ phase : Fin (Fintype.card (TranslationPhase A)),
      player ∉ orbitSchedule A (translationClock A phase.val) := by
  have hmissing : ∃ missing : G, missing ∉ A := by
    by_contra hnone
    push Not at hnone
    exact hproper (Finset.eq_univ_iff_forall.mpr hnone)
  obtain ⟨missing, hmissingA⟩ := hmissing
  let block : TranslationPhase A :=
    ⟨(player - missing) +ᵥ A, ⟨player - missing, rfl⟩⟩
  have hplayer : player ∉ orbitSchedule A block := by
    change player ∉ (player - missing) +ᵥ A
    intro hmem
    have htranslated :
        (player - missing) + missing ∈ (player - missing) +ᵥ A := by
      simpa only [sub_add_cancel] using hmem
    exact hmissingA
      ((Finset.vadd_mem_vadd_finset_iff (s := A) (b := missing)
        (player - missing)).mp htranslated)
  obtain ⟨time, htime, hclock⟩ :=
    translationClock_surjective_period A block
  refine ⟨⟨time, htime⟩, ?_⟩
  rw [hclock]
  exact hplayer

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

/-- Every player occurs in some phase of a nonempty translated block. -/
theorem exists_mem_cyclicSchedule_active
    (A : Finset G) (hA : A.Nonempty) (player : G) :
    ∃ phase : Fin (Fintype.card (TranslationPhase A)),
      player ∈ (cyclicSchedule A).active phase.val := by
  obtain ⟨member, hmember⟩ := hA
  let block : TranslationPhase A :=
    ⟨(player - member) +ᵥ A, ⟨player - member, rfl⟩⟩
  have hplayer : player ∈ orbitSchedule A block := by
    change player ∈ (player - member) +ᵥ A
    have htranslated :=
      (Finset.vadd_mem_vadd_finset_iff (s := A) (b := member)
        (player - member)).2 hmember
    simpa only [vadd_eq_add, sub_add_cancel] using htranslated
  obtain ⟨time, htime, hclock⟩ := translationClock_surjective_period A block
  refine ⟨⟨time, htime⟩, ?_⟩
  rw [cyclicSchedule_active, hclock]
  exact hplayer

/-- If the population has at least two players, every player faces an active
opponent somewhere in one turn of a nonempty cyclic block. -/
theorem exists_ne_mem_cyclicSchedule_active
    (A : Finset G) (hA : A.Nonempty) (hG : 1 < Fintype.card G)
    (who : G) :
    ∃ phase : Fin (Fintype.card (TranslationPhase A)),
      ∃ opponent ≠ who,
        opponent ∈ (cyclicSchedule A).active phase.val := by
  obtain ⟨opponent, hopponent⟩ := Fintype.exists_ne_of_one_lt_card hG who
  obtain ⟨phase, hphase⟩ := exists_mem_cyclicSchedule_active A hA opponent
  exact ⟨phase, opponent, hopponent, hphase⟩

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
collision layer vanishes. The ownership clock still has `N` phases by
`Math.CyclicKofNArithmetic.card_translationPhase_eq_card_of_singleton`. -/
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
