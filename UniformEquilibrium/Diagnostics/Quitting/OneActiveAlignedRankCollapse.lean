/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.OneActiveTransferDefectGraph
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification

/-!
# Aligned one-active clocks collapse the five-role window

The exceptional `3 + 2` graph survives only while the singleton clock and
the positive transfer owner live on different semantic objects.  At one
literal positive minimum pair and one exact Nash root, a positive singleton
clock exposes its owner as the unique debt gate.  Every other debt coordinate
is zero.  Consequently any positive debt owner must be that singleton owner.

Combining this fact with the one-active graph gives an exact rank collapse:
if a fixed positive opponent-singleton atom, a positive transfer owner, and
the exact minimum Nash root are all aligned, their two-edge role window omits
a player.  The exceptional disjoint `3 + 2` branch is impossible.

No alignment theorem is asserted here.  The remaining game-facing task is
precisely to put the clock atom and the transfer edge on the same minimum pair
and exact root (or to charge the failure of doing so).
-/

noncomputable section

namespace GameTheory

open Finset Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Debt ownership at an aligned singleton clock -/

/-- At a positive minimum exact-Nash root, a positive singleton clock and a
positive debt coordinate have the same owner. -/
theorem minimumExactNash_positiveSingletonClock_positiveDebt_owner_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (clockOwner debtOwner : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hclock : 0 < quittingRootCoalitionMass root {clockOwner})
    (hdebt : 0 < quittingTerminalSemanticDebt pair debtOwner) :
    debtOwner = clockOwner := by
  have hgate := minimumTerminalSemantic_debtGate_of_singletonMass_pos
    (reward := reward) pair root hpair hminimum hpositive
      hnash clockOwner hclock
  by_contra hne
  have hne' : clockOwner ≠ debtOwner := Ne.symm hne
  have hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  have htwoLe :
      quittingTerminalSemanticDebt pair clockOwner +
          quittingTerminalSemanticDebt pair debtOwner ≤
        quittingTerminalSemanticDebtSum pair := by
    calc
      quittingTerminalSemanticDebt pair clockOwner +
          quittingTerminalSemanticDebt pair debtOwner =
        ∑ player ∈ ({clockOwner, debtOwner} : Finset ι),
          quittingTerminalSemanticDebt pair player := by simp [hne']
      _ ≤ ∑ player, quittingTerminalSemanticDebt pair player :=
        Finset.sum_le_univ_sum_of_nonneg hdebtNonneg
      _ = quittingTerminalSemanticDebtSum pair := rfl
  rw [hgate.1] at htwoLe
  linarith

/-- Quantitative approximate alignment.  A singleton clock and a distinct
positive-debt owner can coexist at the same approximately Nash row only by
paying tail excess or local Nash error. -/
theorem singletonClock_mul_distinctDebtFloor_le_tailExcess_add_nashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (clockOwner debtOwner : ι)
    (hne : debtOwner ≠ clockOwner) (eta kappa epsilon : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hkappa0 : 0 ≤ kappa)
    (hclock : eta ≤ quittingRootCoalitionMass root {clockOwner})
    (hkappa : kappa ≤ quittingTerminalSemanticDebt tail debtOwner)
    (hnash : IsεQuittingRootNash reward tail.1 epsilon root) :
    eta * kappa ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card ι * epsilon := by
  have htailDebt : ∀ player,
      0 ≤ quittingTerminalSemanticDebt tail player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward htail
  have hkappaErase : kappa ≤
      ∑ player ∈ (Finset.univ : Finset ι).erase clockOwner,
        quittingTerminalSemanticDebt tail player := by
    calc
      kappa ≤ quittingTerminalSemanticDebt tail debtOwner := hkappa
      _ ≤ ∑ player ∈ (Finset.univ : Finset ι).erase clockOwner,
          quittingTerminalSemanticDebt tail player :=
        Finset.single_le_sum
          (fun player _ => htailDebt player)
          (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ debtOwner⟩)
  have hclockNonneg : 0 ≤ quittingRootCoalitionMass root {clockOwner} :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {clockOwner}
  calc
    eta * kappa ≤
        quittingRootCoalitionMass root {clockOwner} * kappa :=
      mul_le_mul_of_nonneg_right hclock hkappa0
    _ ≤ quittingRootCoalitionMass root {clockOwner} *
        (∑ player ∈ (Finset.univ : Finset ι).erase clockOwner,
          quittingTerminalSemanticDebt tail player) :=
      mul_le_mul_of_nonneg_left hkappaErase hclockNonneg
    _ ≤ (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card ι * epsilon :=
      singletonMass_mul_otherDebt_le_tailExcess_add_card_mul_nashError
        reward minimum tail root clockOwner epsilon
          hminimum htail hnash

/-! ## Actual-profile alignment without a rowwise Nash premise -/

/-- Terminal `epsilon`-Nash bounds every literal semantic debt coordinate by
`epsilon`. -/
theorem quittingTerminalSemanticDebt_le_of_isEpsilonAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (epsilon : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile)
    (who : ι) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who ≤ epsilon := by
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward
      (Function.update profile who deviation) who
  have hvalues : values.Nonempty := by
    exact ⟨quittingTerminalPayoff reward
      (Function.update profile who (profile who)) who, profile who, rfl⟩
  have hcap : quittingContinuationBestResponseValue reward profile who ≤
      quittingTerminalPayoff reward profile who + epsilon := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le hvalues
    rintro value ⟨deviation, rfl⟩
    exact hnash who deviation
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  linarith

/-- Hence total terminal debt costs at most `card * epsilon`. -/
theorem quittingTerminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (epsilon : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤
        Fintype.card ι * epsilon := by
  unfold quittingTerminalSemanticDebtSum
  calc
    (∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who) ≤
      ∑ _who : ι, epsilon :=
        Finset.sum_le_sum fun who _ =>
          quittingTerminalSemanticDebt_le_of_isEpsilonAsymptoticNash
            reward profile epsilon hnash who
    _ = Fintype.card ι * epsilon := by simp

/-- At one literal profile stage, a singleton clock and a distinct shifted-
tail debt coordinate are paid by that tail's minimum excess plus the source
profile's total terminal debt.  Local Nash provenance is supplied by legal
one-row deviations and therefore need not be assumed. -/
theorem stageSingletonMass_mul_distinctTailDebtFloor_le_liveTailExcess_add_initialDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (clockOwner debtOwner : ι) (hne : debtOwner ≠ clockOwner)
    (kappa : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappa : kappa ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1)))
      debtOwner) :
    quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal clockOwner) * kappa ≤
      quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1))) -
            quittingTerminalSemanticDebtSum minimum) +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  have htail : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : ∀ player,
      0 ≤ quittingTerminalSemanticDebt tail player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward htail
  have hrootMass : 0 ≤ quittingRootCoalitionMass root {clockOwner} :=
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {clockOwner}
  have hrootToOpponent :
      quittingRootCoalitionMass root {clockOwner} ≤
        quittingRootOpponentAbsorptionMass root debtOwner := by
    exact quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
      root {clockOwner} debtOwner clockOwner (by simp) hne.symm
  have hcoordinate : quittingRootCoalitionMass root {clockOwner} * kappa ≤
      quittingRootOpponentAbsorptionMass root debtOwner *
        quittingTerminalSemanticDebt tail debtOwner := by
    calc
      quittingRootCoalitionMass root {clockOwner} * kappa ≤
          quittingRootCoalitionMass root {clockOwner} *
            quittingTerminalSemanticDebt tail debtOwner :=
        mul_le_mul_of_nonneg_left hkappa hrootMass
      _ ≤ quittingRootOpponentAbsorptionMass root debtOwner *
            quittingTerminalSemanticDebt tail debtOwner :=
        mul_le_mul_of_nonneg_right hrootToOpponent (htailDebt debtOwner)
  have hsingleToSum :
      quittingRootOpponentAbsorptionMass root debtOwner *
          quittingTerminalSemanticDebt tail debtOwner ≤
        ∑ player, quittingRootOpponentAbsorptionMass root player *
          quittingTerminalSemanticDebt tail player := by
    exact Finset.single_le_sum
      (fun player _ => mul_nonneg
        (quittingRootOpponentAbsorptionMass_nonneg root player)
        (htailDebt player))
      (Finset.mem_univ debtOwner)
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail root hminimumCarrier hminimum htail
  have hrootBound : quittingRootCoalitionMass root {clockOwner} * kappa ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1 root :=
    hcoordinate.trans (hsingleToSum.trans hcharge)
  have hlive0 : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have hscaled := mul_le_mul_of_nonneg_left hrootBound hlive0
  have hcoordinateCollect : ∀ player,
      quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward tail.1 root player ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) player := by
    intro player
    simpa only [tail, root] using
      quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
        (reward := reward) profile player time
  have htotalCollect :
      quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail.1 root ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by
    unfold quittingRootTotalNashDefect quittingTerminalSemanticDebtSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun player _ => hcoordinateCollect player
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  change quittingLiveMass reward profile time *
      quittingRootCoalitionMass root {clockOwner} * kappa ≤ _
  calc
    quittingLiveMass reward profile time *
        quittingRootCoalitionMass root {clockOwner} * kappa =
      quittingLiveMass reward profile time *
        (quittingRootCoalitionMass root {clockOwner} * kappa) := by ring
    _ ≤ quittingLiveMass reward profile time *
        ((quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum) +
          quittingRootTotalNashDefect reward tail.1 root) := hscaled
    _ = quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum) +
        quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward tail.1 root := by ring
    _ ≤ quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum) +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by linarith
    _ = _ := by rfl

/-! ## Converting the one-active opponent atom to the exact singleton clock -/

/-- In a one-active row, a positive opponent singleton atom is the positive
mass of the same literal terminal singleton. -/
theorem quittingRootCoalitionMass_singleton_pos_of_oneActive_opponentMass_pos
    (root : ι → PMF Bool) (markedPlayer clockOwner : ι)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass
      root markedPlayer {clockOwner}) :
    0 < quittingRootCoalitionMass root {clockOwner} := by
  have hroot :=
    quittingRoot_eq_soloStationaryRoot_of_oneActive_singletonMass_pos
      root markedPlayer clockOwner hactive hmass
  have hhazard : 0 < (root clockOwner true).toReal := by
    have heq :=
      quittingOpponentCoalitionMass_singleton_eq_hazard_of_oneActive
        root markedPlayer clockOwner hactive hmass
    rw [heq] at hmass
    exact hmass
  rw [hroot,
    quittingRootCoalitionMass_solo_of_nonempty clockOwner
      (root clockOwner) {clockOwner} (by simp)]
  simpa using hhazard

/-! ## The aligned five-to-four collapse -/

private theorem exists_omitted_transferDefectRoleWindow_of_first_eq_partner
    (first shared second marked partner : Fin 5)
    (heq : first = partner) :
    ∃ omitted,
      omitted ∉ quittingTransferDefectRoleWindow
        first shared second marked partner := by
  let four : Finset (Fin 5) := {partner, shared, second, marked}
  have hsubset : quittingTransferDefectRoleWindow
      first shared second marked partner ⊆ four := by
    intro player hplayer
    simp only [quittingTransferDefectRoleWindow, four, Finset.mem_insert,
      Finset.mem_singleton] at hplayer ⊢
    aesop
  have hfour : four.card ≤ 4 := by
    dsimp only [four]
    have h1 := Finset.card_insert_le partner
      ({shared, second, marked} : Finset (Fin 5))
    have h2 := Finset.card_insert_le shared
      ({second, marked} : Finset (Fin 5))
    have h3 := Finset.card_insert_le second
      ({marked} : Finset (Fin 5))
    simp only [Finset.card_singleton] at h3
    omega
  have hcard : (quittingTransferDefectRoleWindow
      first shared second marked partner).card < Fintype.card (Fin 5) := by
    have := Finset.card_le_card hsubset
    norm_num
    omega
  have hproper : quittingTransferDefectRoleWindow
      first shared second marked partner ≠ Finset.univ := by
    intro hfull
    have : (quittingTransferDefectRoleWindow
        first shared second marked partner).card = Fintype.card (Fin 5) := by
      rw [hfull, Finset.card_univ]
    omega
  by_contra hnone
  push Not at hnone
  exact hproper (Finset.eq_univ_iff_forall.mpr hnone)

/-- **Same-profile four-role-or-charge alternative.**  A literal retained
singleton stage can be aligned with a positive shifted-tail transfer owner
without manufacturing a rowwise Nash root.  If their owners differ, the
product of their quantitative floors is charged to shifted-tail excess plus
the original profile's total terminal debt. -/
theorem exists_omitted_transferDefectRole_or_sameProfileClockDebtCharge
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (minimum : QuittingTerminalSemanticPair (Fin 5))
    (profile : (quittingGame reward).BehaviorProfile)
    (path : ℕ → Fin 5) (time : ℕ)
    (markedPlayer clockOwner : Fin 5) (rho kappa : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappa0 : 0 ≤ kappa)
    (hclockFloor : rho ≤ quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal clockOwner))
    (hdebtFloor : kappa ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1)))
      (path time)) :
    (∃ omitted,
      omitted ∉ quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          markedPlayer clockOwner) ∨
      rho * kappa ≤
        quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1))) -
            quittingTerminalSemanticDebtSum minimum) +
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) := by
  by_cases heq : path time = clockOwner
  · left
    exact exists_omitted_transferDefectRoleWindow_of_first_eq_partner
      (path time) (path (time + 1)) (path (time + 2))
        markedPlayer clockOwner heq
  · right
    have hscaled := mul_le_mul_of_nonneg_right hclockFloor hkappa0
    exact hscaled.trans
      (stageSingletonMass_mul_distinctTailDebtFloor_le_liveTailExcess_add_initialDebt
        reward minimum profile time clockOwner (path time) heq kappa
          hminimumCarrier hminimum hdebtFloor)

/-- Terminal-Nash specialization of the same-profile alternative.  This is
the form consumed by finite-splice Nashification: no rowwise Nash certificate
is requested, and the entire strategic error is the literal `5 * epsilon`. -/
theorem exists_omitted_transferDefectRole_or_terminalNashClockDebtCharge
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (minimum : QuittingTerminalSemanticPair (Fin 5))
    (profile : (quittingGame reward).BehaviorProfile)
    (path : ℕ → Fin 5) (time : ℕ)
    (markedPlayer clockOwner : Fin 5) (rho kappa epsilon : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappa0 : 0 ≤ kappa)
    (hclockFloor : rho ≤ quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal clockOwner))
    (hdebtFloor : kappa ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1)))
      (path time))
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) epsilon profile) :
    (∃ omitted,
      omitted ∉ quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          markedPlayer clockOwner) ∨
      rho * kappa ≤
        quittingLiveMass reward profile time *
          (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1))) -
            quittingTerminalSemanticDebtSum minimum) + 5 * epsilon := by
  rcases exists_omitted_transferDefectRole_or_sameProfileClockDebtCharge
      reward minimum profile path time markedPlayer clockOwner rho kappa
        hminimumCarrier hminimum hkappa0 hclockFloor hdebtFloor with
    homitted | hcharge
  · exact Or.inl homitted
  · right
    have hdebt :=
      quittingTerminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash
        reward profile epsilon hnash
    norm_num at hdebt ⊢
    linarith

/-- **Quantitative aligned rank alternative.**  At an approximately Nash
near-minimum row, either the displayed two-edge/fixed-edge packet already
omits one of five players, or the product of the marked clock floor and the
transfer-owner debt floor is paid by tail excess plus local Nash error. -/
theorem exists_omitted_transferDefectRole_or_clockDebtCharge
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (minimum tail : QuittingTerminalSemanticPair (Fin 5))
    (root : Fin 5 → PMF Bool) (path : ℕ → Fin 5) (time : ℕ)
    (markedPlayer clockOwner : Fin 5)
    (eta kappa epsilon : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hkappa0 : 0 ≤ kappa)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass
      root markedPlayer {clockOwner})
    (hclockFloor : eta ≤ quittingOpponentCoalitionMass
      root markedPlayer {clockOwner})
    (hdebtFloor : kappa ≤
      quittingTerminalSemanticDebt tail (path time))
    (hnash : IsεQuittingRootNash reward tail.1 epsilon root) :
    (∃ omitted,
      omitted ∉ quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          markedPlayer clockOwner) ∨
      eta * kappa ≤
        (quittingTerminalSemanticDebtSum tail -
            quittingTerminalSemanticDebtSum minimum) + 5 * epsilon := by
  by_cases heq : path time = clockOwner
  · left
    exact exists_omitted_transferDefectRoleWindow_of_first_eq_partner
      (path time) (path (time + 1)) (path (time + 2))
        markedPlayer clockOwner heq
  · right
    have hmassEq :=
      quittingOpponentCoalitionMass_singleton_eq_rootCoalitionMass_of_oneActive
        root markedPlayer clockOwner hactive hmass
    have hclockRoot : eta ≤ quittingRootCoalitionMass root {clockOwner} := by
      rw [← hmassEq]
      exact hclockFloor
    have hcharge :=
      singletonClock_mul_distinctDebtFloor_le_tailExcess_add_nashError
        reward minimum tail root clockOwner (path time) heq eta kappa epsilon
          hminimum htail hkappa0 hclockRoot
            hdebtFloor hnash
    norm_num at hcharge ⊢
    exact hcharge

/-- **Aligned one-active rank collapse.**  Take two consecutive transfer
vertices beginning at a positive debt owner.  If the same exact minimum Nash
root carries a fixed positive one-active opponent-singleton atom, the five
displayed roles cannot be distinct; an omitted player exists. -/
theorem exists_omitted_transferDefectRole_of_alignedMinimumRoot
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (pair : QuittingTerminalSemanticPair (Fin 5))
    (root : Fin 5 → PMF Bool) (path : ℕ → Fin 5) (time : ℕ)
    (markedPlayer clockOwner : Fin 5)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hactive : HasQuittingSupportCardAtMost 1 root)
    (hmass : 0 < quittingOpponentCoalitionMass
      root markedPlayer {clockOwner})
    (htransferOwner :
      0 < quittingTerminalSemanticDebt pair (path time)) :
    ∃ omitted,
      omitted ∉ quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          markedPlayer clockOwner := by
  have hclock : 0 < quittingRootCoalitionMass root {clockOwner} :=
    quittingRootCoalitionMass_singleton_pos_of_oneActive_opponentMass_pos
      root markedPlayer clockOwner hactive hmass
  have hownerEq : path time = clockOwner :=
    minimumExactNash_positiveSingletonClock_positiveDebt_owner_eq
      reward pair root clockOwner (path time) hpair hminimum
        hpositive hnash hclock htransferOwner
  have hproper : quittingTransferDefectRoleWindow
      (path time) (path (time + 1)) (path (time + 2))
        markedPlayer clockOwner ≠ Finset.univ := by
    intro hfull
    have hpartition :=
      transferTriple_defectEdge_partition_of_window_full
        path markedPlayer clockOwner time hfull
    have hnot : path time ∉ quittingDefectEdge markedPlayer clockOwner :=
      Finset.disjoint_left.mp hpartition.1 (by
        simp [quittingTransferTriple])
    apply hnot
    simp [quittingDefectEdge, hownerEq]
  by_contra hnone
  push Not at hnone
  exact hproper (Finset.eq_univ_iff_forall.mpr hnone)

end GameTheory
