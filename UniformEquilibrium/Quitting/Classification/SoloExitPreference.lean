/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-!
# Solo-exit preference conditions on a quitting reward table

Four conditions on the reward table alone, with no strategic content.

* Unit solo exit: every player's own solo exit pays it exactly `1`.
* Capped joint exit: no quitter is paid more than `1`.
* Weak solo-exit preference: no quitter is paid more than its own solo exit
  pays it.  Also called weak self-preference for quitting alone.
* Strict joint-exit attraction: some quitter is paid strictly more than its own
  solo exit pays it.  Also called strictly attractive joint exit, or strict
  joint-exit preference.

The first two are the pair of assumptions carried by the quitting existence
theorem of Solan and Vieille, *Quitting games*, Math. Oper. Res. 26 (2001),
Theorem 1.2.  The last two are the scale-free pair: strict joint-exit
attraction is exactly the negation of weak solo-exit preference.

The two pairs are not interchangeable.  Unit solo exit together with capped
joint exit implies weak solo-exit preference, and under unit solo exit the
converse holds as well, but weak solo-exit preference alone does not pin the
common solo value to `1` and does not imply it is positive.  Since this
development carries no transport of quitting semantics along a positive
rescaling of the reward table, the normalization is a genuine restriction here
and is kept explicit.

The source theorem's own conclusion, and what it yields for the fixed-target
uniform-equilibrium-payoff notion, are stated in
`UniformEquilibrium/Quitting/Classification/SoloExitPreferenceExistence.lean`.

Real-valued tables carry no computable order, so the conditions here have no
usable `Decidable` instances; concrete tables discharge them by ordinary
arithmetic over their finitely many coalition rows.
-/

noncomputable section

namespace GameTheory

variable {ι : Type}

/-! ## The table conditions -/

/-- **Unit solo exit.**  Each player's own solo exit pays it exactly `1`.

This is assumption A.1 of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Theorem 1.2. -/
def QuittingUnitSoloExit (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Prop :=
  ∀ who : ι, quittingSoloReward reward who who = 1

/-- **Capped joint exit.**  No member of a quitting coalition is paid more
than `1`.

This is assumption A.2 of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Theorem 1.2. -/
def QuittingCappedJointExit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (quitters : {S : Finset ι // S.Nonempty}) (who : ι),
    who ∈ quitters.1 → reward quitters who ≤ 1

/-- **Weak solo-exit preference.**  No member of a quitting coalition is paid
more than its own solo exit pays it: every player weakly prefers quitting
alone to quitting alongside anybody.  Also called weak self-preference for
quitting alone. -/
def QuittingWeakSoloExitPreference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (quitters : {S : Finset ι // S.Nonempty}) (who : ι),
    who ∈ quitters.1 →
      reward quitters who ≤ quittingSoloReward reward who who

/-- **Strict joint-exit attraction.**  Some player is paid strictly more by
some coalition it belongs to than by its own solo exit.  Also called a
strictly attractive joint exit, or strict joint-exit preference. -/
def QuittingStrictJointExitAttraction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (quitters : {S : Finset ι // S.Nonempty}) (who : ι),
    who ∈ quitters.1 ∧
      quittingSoloReward reward who who < reward quitters who

/-- Capped joint exit splits along coalition size: a solo row is indexed by its
unique member, and every other row is checked directly.  Tables defined by a
case split on coalition size discharge the condition this way. -/
theorem quittingCappedJointExit_of_solo_of_larger
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hsolo : ∀ who : ι, quittingSoloReward reward who who ≤ 1)
    (hlarger : ∀ (quitters : {S : Finset ι // S.Nonempty}) (who : ι),
      who ∈ quitters.1 → quitters.1.card ≠ 1 → reward quitters who ≤ 1) :
    QuittingCappedJointExit reward := by
  intro quitters who hmem
  by_cases hcard : quitters.1.card = 1
  · obtain ⟨owner, howner⟩ := Finset.card_eq_one.1 hcard
    rw [howner] at hmem
    have hwho : who = owner := Finset.mem_singleton.1 hmem
    subst hwho
    rw [show quitters = ⟨{who}, Finset.singleton_nonempty who⟩ from
      Subtype.ext howner]
    exact hsolo who
  · exact hlarger quitters who hmem hcard

/-! ## Relations between the conditions -/

/-- Strict joint-exit attraction is exactly the failure of weak solo-exit
preference. -/
theorem not_quittingWeakSoloExitPreference_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ¬ QuittingWeakSoloExitPreference reward ↔
      QuittingStrictJointExitAttraction reward := by
  unfold QuittingWeakSoloExitPreference QuittingStrictJointExitAttraction
  push Not
  rfl

/-- Weak solo-exit preference is exactly the failure of strict joint-exit
attraction. -/
theorem not_quittingStrictJointExitAttraction_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ¬ QuittingStrictJointExitAttraction reward ↔
      QuittingWeakSoloExitPreference reward := by
  unfold QuittingWeakSoloExitPreference QuittingStrictJointExitAttraction
  push Not
  rfl

/-- The pair of source assumptions implies the scale-free weak preference. -/
theorem quittingWeakSoloExitPreference_of_unitSoloExit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcapped : QuittingCappedJointExit reward) :
    QuittingWeakSoloExitPreference reward := by
  intro quitters who hmem
  rw [hunit who]
  exact hcapped quitters who hmem

/-- Under unit solo exit, the scale-free weak preference recovers the cap. -/
theorem quittingCappedJointExit_of_unitSoloExit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hweak : QuittingWeakSoloExitPreference reward) :
    QuittingCappedJointExit reward := by
  intro quitters who hmem
  rw [← hunit who]
  exact hweak quitters who hmem

/-- Under unit solo exit the source cap and the scale-free weak preference are
the same condition. -/
theorem quittingCappedJointExit_iff_weakSoloExitPreference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    QuittingCappedJointExit reward ↔
      QuittingWeakSoloExitPreference reward :=
  ⟨fun hcapped ↦ quittingWeakSoloExitPreference_of_unitSoloExit hunit hcapped,
    fun hweak ↦ quittingCappedJointExit_of_unitSoloExit hunit hweak⟩

/-- Under unit solo exit, failure of the source cap is a strictly attractive
joint exit. -/
theorem quittingStrictJointExitAttraction_of_unitSoloExit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcapped : ¬ QuittingCappedJointExit reward) :
    QuittingStrictJointExitAttraction reward :=
  (not_quittingWeakSoloExitPreference_iff reward).1
    fun hweak ↦ hcapped (quittingCappedJointExit_of_unitSoloExit hunit hweak)

end GameTheory
