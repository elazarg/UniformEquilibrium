/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetAlignment

/-!
# Repair of an underfloor pair-base coordinate

At a stationary row where one player Quits surely, immediate Quit gives that
player the prescribed stationary payoff.  If this payoff lies below the
behavioral punishment value, weak duality forces `Never` to be strictly
better.  The violation therefore has a fixed temporal orientation: it
produces a paid first-disagreement row from immediate Quit to `Never`.

Replacing the player by Always Continue realizes the stationary cap, puts
that coordinate above punishment, and makes its unrestricted semantic debt
zero.  For the four-player paid reset target, the other member of the forced
pair remains a sure quitter.  No Nash, floor, debt, paid-row, reset, or law
claim is made for any other coordinate of the repaired profile.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- At a stationary row where the selected player Quits surely, immediate
Quit gives exactly the prescribed stationary payoff. -/
theorem quittingPureTimeDeviationPayoff_some_zero_eq_stationaryPayoff_of_pureQuit
    (root : iota → PMF Bool) (who : iota)
    (hwho : root who = PMF.pure true) :
    quittingPureTimeDeviationPayoff reward
        (quittingStationaryProfile reward root) who (some 0) =
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who := by
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hwho
  have htarget : quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) who =
        quittingRootAbsorbingContribution reward root who := by
    rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
    · rw [hcontinue]
      norm_num
    · rw [hcontinue]
      norm_num
  have hquit : quittingPureTimeDeviationPayoff reward
      (quittingStationaryProfile reward root) who (some 0) =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
    dsimp only [quittingPureTimeDeviationPayoff]
    rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue]
    simp
  have hquitTarget :
      quittingStationaryFixedOpponentsQuitValue reward root who =
        quittingRootAbsorbingContribution reward root who := by
    change quittingRootAbsorbingContribution reward
        (Function.update root who (PMF.pure true)) who = _
    rw [← hwho, Function.update_eq_self]
  rw [hquit, hquitTarget, htarget]

/-- A sure-Quit stationary payoff below punishment forces a quantitatively
paid `Quit now`-to-`Never` edge. -/
theorem punishmentGap_le_never_sub_quitNow_of_stationary_pureQuit
    (root : iota → PMF Bool) (who : iota)
    (hwho : root who = PMF.pure true)
    (hbelow : quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who <
      quittingPunishmentValue reward who) :
    quittingPunishmentValue reward who -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who ≤
      quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who none -
        quittingPureTimeDeviationPayoff reward
          (quittingStationaryProfile reward root) who (some 0) := by
  let profile := quittingStationaryProfile reward root
  let quitNow := quittingPureTimeDeviationPayoff reward profile who (some 0)
  let never := quittingPureTimeDeviationPayoff reward profile who none
  have hquit : quitNow = quittingTerminalPayoff reward profile who := by
    exact
      quittingPureTimeDeviationPayoff_some_zero_eq_stationaryPayoff_of_pureQuit
        root who hwho
  have hfloor : quittingPunishmentValue reward who ≤
      quittingStationaryUnilateralCap reward root who :=
    quittingPunishmentValue_le_stationaryUnilateralCap reward who root
  have hcap : quittingStationaryUnilateralCap reward root who =
      max quitNow never := by
    exact quittingStationaryUnilateralCap_eq_max_quitNow_never
      reward root who
  have horder : quitNow ≤ never := by
    by_contra hnot
    have hreverse : never ≤ quitNow := le_of_not_ge hnot
    rw [hcap, max_eq_left hreverse, hquit] at hfloor
    exact (not_lt_of_ge hfloor) hbelow
  rw [hcap, max_eq_right horder] at hfloor
  dsimp only [profile, quitNow, never] at hfloor hquit ⊢
  rw [hquit]
  linarith

/-- The underfloor sure-Quit branch has a later-receiving paid row with
literal source witness `Quit now` and receiving witness `Never`. -/
theorem exists_laterReceiving_paidRow_of_stationary_pureQuit_underfloor
    (root : iota → PMF Bool) (who : iota)
    (hwho : root who = PMF.pure true)
    (hbelow : quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who <
      quittingPunishmentValue reward who) :
    ∃ row : QuittingPaidFirstDisagreementRow reward
        (quittingStationaryProfile reward root) who
          (quittingPunishmentValue reward who -
            quittingTerminalPayoff reward
              (quittingStationaryProfile reward root) who),
      row.sourceWitness = some 0 ∧
        row.receivingWitness = none ∧
        row.receivingEarlier = false := by
  have hgap : 0 < quittingPunishmentValue reward who -
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who := sub_pos.mpr hbelow
  have hedge :=
    punishmentGap_le_never_sub_quitNow_of_stationary_pureQuit
      root who hwho hbelow
  obtain ⟨row, hsource, hreceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward (quittingStationaryProfile reward root) who (some 0) none
        (quittingPunishmentValue reward who -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who) hgap hedge
  refine ⟨row, hsource, hreceiving, ?_⟩
  cases hearlier : row.receivingEarlier with
  | false => rfl
  | true =>
      have hchronology := row.chronology
      rw [hearlier] at hchronology
      simp only [if_true] at hchronology
      rw [hreceiving] at hchronology
      simp at hchronology

/-- Updating an underfloor sure quitter to Always Continue realizes its
stationary cap, hence repairs exactly that coordinate above punishment and to
zero unrestricted semantic debt. -/
theorem stationary_pureQuit_underfloor_alwaysContinue_repair
    (root : iota → PMF Bool) (who : iota)
    (hwho : root who = PMF.pure true)
    (hbelow : quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who <
      quittingPunishmentValue reward who) :
    let repairedRoot := Function.update root who (PMF.pure false)
    let repaired := quittingStationaryProfile reward repairedRoot
    quittingTerminalPayoff reward repaired who =
        quittingStationaryUnilateralCap reward root who ∧
      quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward repaired who ∧
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward repaired) who = 0 := by
  dsimp only
  let profile := quittingStationaryProfile reward root
  let repairedRoot := Function.update root who (PMF.pure false)
  let repaired := quittingStationaryProfile reward repairedRoot
  let quitNow := quittingPureTimeDeviationPayoff reward profile who (some 0)
  let never := quittingPureTimeDeviationPayoff reward profile who none
  have hquit : quitNow = quittingTerminalPayoff reward profile who := by
    exact
      quittingPureTimeDeviationPayoff_some_zero_eq_stationaryPayoff_of_pureQuit
        root who hwho
  have hgap := punishmentGap_le_never_sub_quitNow_of_stationary_pureQuit
    root who hwho hbelow
  have horder : quitNow ≤ never := by
    linarith
  have hcap : quittingStationaryUnilateralCap reward root who = never := by
    rw [quittingStationaryUnilateralCap_eq_max_quitNow_never,
      max_eq_right horder]
  have hrepairedPayoff : quittingTerminalPayoff reward repaired who = never := by
    dsimp only [never, quittingPureTimeDeviationPayoff, profile, repaired]
    rw [quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue,
      update_quittingStationaryProfile_alwaysContinue]
  have hcapCongr : quittingStationaryUnilateralCap reward repairedRoot who =
      quittingStationaryUnilateralCap reward root who := by
    apply quittingStationaryUnilateralCap_congr_of_opponents reward who
    intro player hplayer
    dsimp only [repairedRoot]
    rw [Function.update_of_ne hplayer]
  have hfloor : quittingPunishmentValue reward who ≤
      quittingStationaryUnilateralCap reward root who :=
    quittingPunishmentValue_le_stationaryUnilateralCap reward who root
  refine ⟨?_, ?_, ?_⟩
  · rw [hrepairedPayoff, hcap]
  · rw [hrepairedPayoff, ← hcap]
    exact hfloor
  · unfold quittingTerminalSemanticDebt
    rw [quittingTerminalSemanticPair_stationary_envelope_eq_cap,
      hcapCongr]
    change quittingStationaryUnilateralCap reward root who -
      quittingTerminalPayoff reward repaired who = 0
    rw [hrepairedPayoff, hcap]
    exact sub_self _

namespace FinFourPairBasePaidResetTarget

/-- The stationary root underlying a pair-base paid reset target. -/
def root
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) : Fin 4 → PMF Bool :=
  quittingPersistentBaseRoot {baseFirst, baseSecond}
    (finFourPairBaseComplement {baseFirst, baseSecond})
      target.localization.point

/-- The unilateral Always-Continue repair of one coordinate of the target. -/
def floorRepairProfile
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) (who : Fin 4) :
    (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (Function.update target.root who (PMF.pure false))

@[simp] theorem profile_eq_stationary_root
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) :
    target.profile = quittingStationaryProfile reward target.root :=
  rfl

/-- A punishment-floor violation at a forced pair-base coordinate is consumed
by a source-matched, later-receiving paid row and a unilateral zero-debt
repair.  The other base coordinate remains a sure quitter at the repaired
root. -/
theorem exists_other_and_laterPaidRow_and_floorRepair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (who : Fin 4) (hwho : who ∈ ({baseFirst, baseSecond} : Finset (Fin 4)))
    (hbelow : target.semanticPair.1 who <
      quittingPunishmentValue reward who) :
    ∃ (other : Fin 4)
        (row : QuittingPaidFirstDisagreementRow reward target.profile who
          (quittingPunishmentValue reward who -
            quittingTerminalPayoff reward target.profile who)),
      other ∈ ({baseFirst, baseSecond} : Finset (Fin 4)) ∧
        other ≠ who ∧
        target.root other = PMF.pure true ∧
        (Function.update target.root who (PMF.pure false)) other =
          PMF.pure true ∧
        0 < quittingPunishmentValue reward who -
          quittingTerminalPayoff reward target.profile who ∧
        target.floorRepairProfile who =
          Function.update target.profile who
            (quittingAlwaysContinueStrategy reward who) ∧
        quittingRootAbsorptionMass
            (Function.update target.root who (PMF.pure false)) = 1 ∧
        quittingTerminalSemanticPair reward (target.floorRepairProfile who) ∈
          quittingTerminalSemanticCarrier reward ∧
        row.sourceWitness = some 0 ∧
        row.receivingWitness = none ∧
        row.receivingEarlier = false ∧
        quittingPunishmentValue reward who ≤
          quittingTerminalPayoff reward (target.floorRepairProfile who) who ∧
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (target.floorRepairProfile who)) who = 0 := by
  have hrootWho : target.root who = PMF.pure true := by
    apply quittingPersistentBaseRoot_apply_of_mem_base
    exact hwho
  change quittingTerminalPayoff reward target.profile who <
    quittingPunishmentValue reward who at hbelow
  have hbelow' : quittingTerminalPayoff reward
      (quittingStationaryProfile reward target.root) who <
        quittingPunishmentValue reward who := by
    simpa using hbelow
  obtain ⟨row, hsource, hreceiving, hlater⟩ :=
    exists_laterReceiving_paidRow_of_stationary_pureQuit_underfloor
      target.root who hrootWho hbelow'
  obtain ⟨hrepairedPayoff, hrepairedFloor, hrepairedDebt⟩ :=
    stationary_pureQuit_underfloor_alwaysContinue_repair
      target.root who hrootWho hbelow'
  have hrepairFloor : quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward (target.floorRepairProfile who) who := by
    simpa [floorRepairProfile] using hrepairedFloor
  have hrepairDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (target.floorRepairProfile who))
        who = 0 := by
    simpa [floorRepairProfile] using hrepairedDebt
  have hgap : 0 < quittingPunishmentValue reward who -
      quittingTerminalPayoff reward target.profile who := sub_pos.mpr hbelow
  have hrepairProfile : target.floorRepairProfile who =
      Function.update target.profile who
        (quittingAlwaysContinueStrategy reward who) := by
    symm
    exact update_quittingStationaryProfile_alwaysContinue
      reward target.root who
  have hrepairMem : quittingTerminalSemanticPair reward
      (target.floorRepairProfile who) ∈
        quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward
      (target.floorRepairProfile who)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
  rcases hwho with hfirst | hsecond
  · subst who
    have hotherRoot : target.root baseSecond = PMF.pure true := by
      apply quittingPersistentBaseRoot_apply_of_mem_base
      simp
    have hupdated :
        (Function.update target.root baseFirst (PMF.pure false)) baseSecond =
          PMF.pure true := by
      rw [Function.update_of_ne target.base_ne.symm, hotherRoot]
    have habsorption : quittingRootAbsorptionMass
        (Function.update target.root baseFirst (PMF.pure false)) = 1 := by
      unfold quittingRootAbsorptionMass
      rw [quittingStationaryContinueMass_of_sureQuitter hupdated]
      norm_num
    exact ⟨baseSecond, row, by simp, target.base_ne.symm,
      hotherRoot, hupdated, hgap, hrepairProfile, habsorption, hrepairMem,
      hsource, hreceiving, hlater, hrepairFloor, hrepairDebt⟩
  · subst who
    have hotherRoot : target.root baseFirst = PMF.pure true := by
      apply quittingPersistentBaseRoot_apply_of_mem_base
      simp
    have hupdated :
        (Function.update target.root baseSecond (PMF.pure false)) baseFirst =
          PMF.pure true := by
      rw [Function.update_of_ne target.base_ne, hotherRoot]
    have habsorption : quittingRootAbsorptionMass
        (Function.update target.root baseSecond (PMF.pure false)) = 1 := by
      unfold quittingRootAbsorptionMass
      rw [quittingStationaryContinueMass_of_sureQuitter hupdated]
      norm_num
    exact ⟨baseFirst, row, by simp, target.base_ne, hotherRoot, hupdated,
      hgap, hrepairProfile, habsorption, hrepairMem, hsource, hreceiving,
      hlater, hrepairFloor, hrepairDebt⟩

end FinFourPairBasePaidResetTarget

end GameTheory
