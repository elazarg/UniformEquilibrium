/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Classification.Circulant.PocketAnchoredNoGo

/-!
# The anchored cyclic on-path values as a patience system

`quittingAnchoredCyclicOnPathValue` is the terminal payoff of the repository's
single-quitter periodic profile read from a phase, and
`quittingAnchoredCyclicOnPathValue_renewal` is exactly the one-step recursion
required by `QuittingAnchoredCyclicPatienceSystem`, with survival `1 - p_k` and
the cyclic successor written as `finRotate`.  This file packages those on-path
values into a patience system whenever the hazards are positive and the anchor
and patience conditions are supplied, and reads the five-player open-pocket
consequence off it.  A phase that quits for sure is allowed.

The anchor and patience conditions are inputs here.  Nothing below asserts that
a uniform or approximate equilibrium forces them, and nothing below evaluates a
deviation: the statements concern the on-path values alone.

The two conditions are not on the same footing.  The anchor is the exact
indifference of the phase's own quitter, whose quit-now value is its solo self
payoff because the other players continue with certainty at that phase; it is
the equality that `IsExactAnchoredSoloPeriodic` yields at each phase, through
`anchor_of_isExactAnchoredSoloPeriodic`, at the very hazards supplied here.
Patience is instead the vanishing-hazard reading of a spectator's incentive: at
hazard `p` a spectator compares against `spectatorQuitNowValue`, the mixture of
its pair row with the quitter and its solo self payoff.  Where pair rows pay
their members strictly less than their solo self payoffs, patience asks strictly
more than that comparison — it is not the spectator floor
`spectatorFloor_of_isExactAnchoredSoloPeriodic` — so a schedule may fail to be
patient while its spectators still have no profitable one-phase quit.  Failure
of the conjunction below is therefore failure of the anchored demand, not of
any incentive condition on the profile.

`spectatorQuitNowValue_le_onPathValue_of_isExactAnchoredSoloPeriodic` writes
that spectator floor in the same vocabulary as patience, so the gap between the
two readings is one inequality on a table's pair rows and nothing else.

## Main definitions

* `quittingAnchoredCyclicPatienceSystemOfOnPathValue` — the packaging

## Main results

* `spectatorQuitNowValue_le_onPathValue_of_isExactAnchoredSoloPeriodic` — the
  spectator half of fixed-hazard exactness, as a bound on
  `spectatorQuitNowValue`
* `not_anchored_patient_onPathValue_of_isOpenPocketMargin` — over a five-player
  open-pocket circulant table no schedule with positive hazards has on-path
  values that are both anchored and patient
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- The singleton terminal state of one quitter, in its two spellings. -/
theorem quittingSingletonTerminal_eq_projective (who : ι) :
    quittingSingletonTerminal who = quittingProjectiveSingletonTerminal who := rfl

/-- **The spectator half of fixed-hazard exactness, written as the
fixed-hazard comparison.**  At every phase of an exact anchored solo-periodic
profile, a player other than that phase's scheduled quitter values quitting
there — the mixture `spectatorQuitNowValue` of its pair row with the quitter
and its own solo self payoff — at no more than the on-path value it already
receives.

This is the comparison whose place the patience field of
`QuittingAnchoredCyclicPatienceSystem` gives to the bare solo self payoff.  The
two agree exactly where a pair row pays its member that member's solo self
payoff, by `spectatorQuitNowValue_eq_solo_of_pair_eq`, and patience is the
strictly stronger demand wherever a pair row pays strictly less, by
`spectatorQuitNowValue_lt_solo_of_pair_lt`.  The anchor field, by contrast, is
the same equality in both readings, by
`anchor_of_isExactAnchoredSoloPeriodic`. -/
theorem spectatorQuitNowValue_le_onPathValue_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (phase : Fin m) {who : ι} (hne : who ≠ w phase) :
    spectatorQuitNowValue reward (hazard phase) (w phase) who ≤
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase who := by
  have hfloor := spectatorFloor_of_isExactAnchoredSoloPeriodic hexact phase hne
  have hren :=
    quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1 phase who
  have hpair : (⟨{who, w phase}, Finset.insert_nonempty who {w phase}⟩ :
      {S : Finset ι // S.Nonempty}) =
      ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ :=
    Subtype.ext (Finset.pair_comm who (w phase))
  rw [spectatorQuitNowValue, hpair, ← quittingSingletonTerminal_eq_projective,
    hren]
  linarith

/-- **The on-path values of an anchored cyclic schedule form a patience
system.**  Survival is the complementary hazard, the renewal system supplies
the recursion, and the anchor and patience conditions are carried over
unchanged. -/
def quittingAnchoredCyclicPatienceSystemOfOnPathValue [NeZero m]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k)
    (hanchor : ∀ k,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (k + 1) (w k) =
        reward (quittingProjectiveSingletonTerminal (w k)) (w k))
    (hpatience : ∀ k y, reward (quittingProjectiveSingletonTerminal y) y ≤
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 k y) :
    QuittingAnchoredCyclicPatienceSystem reward m where
  order := w
  survival := fun k => 1 - hazard k
  phaseValue := quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
  survival_nonneg := fun k => by linarith [h1 k]
  survival_lt_one := fun k => by linarith [hpos k]
  recursion := by
    intro k y
    have hren := quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1 k y
    rw [finRotate_apply, quittingSingletonTerminal_eq_projective] at hren
    rw [hren]
    ring
  anchor := hanchor
  patience := hpatience

/-- **No anchored and patient on-path values over a five-player open-pocket
circulant table.**  For a table whose normalized solo matrix is circulant with
both neighbour margins negative and both distant margins positive, no period, no
schedule and no positive hazard vector make the on-path values both anchored and
patient.  Phases that quit for sure are covered.

Patience is the vanishing-hazard spectator floor, above the fixed-hazard
comparison `spectatorQuitNowValue` on tables whose pair rows pay their members
less than their solo self payoffs, so this excludes a pair of conditions on the
on-path values rather than a class of profiles. -/
theorem not_anchored_patient_onPathValue_of_isOpenPocketMargin
    {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
    {margin : ZMod 5 → ℝ} (hcirculant : HasCirculantSoloMatrix reward margin)
    (hpocket : IsOpenPocketMargin margin) [NeZero m]
    (w : Fin m → ZMod 5) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) :
    ¬((∀ k, quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (k + 1) (w k) =
          reward (quittingProjectiveSingletonTerminal (w k)) (w k)) ∧
      ∀ k y, reward (quittingProjectiveSingletonTerminal y) y ≤
        quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 k y) := by
  rintro ⟨hanchor, hpatience⟩
  exact (isEmpty_anchoredCyclicPatienceSystem_of_isOpenPocketMargin hcirculant
    hpocket m).elim
    (quittingAnchoredCyclicPatienceSystemOfOnPathValue reward w hazard h0 h1 hpos
      hanchor hpatience)

end GameTheory
