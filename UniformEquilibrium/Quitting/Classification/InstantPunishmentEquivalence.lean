/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ExistenceBranches

/-!
# The instant-punishment branch does not depend on the punishment's shape

Ashkenazi-Golan, Krasikov, Rainer and Solan, *Absorption paths and equilibria
in quitting games*, Mathematical Programming (2022), Theorem 3.4, branch S.2,
asks for an `ε`-equilibrium in which one player quits surely at the first
stage and is thereafter punished to within `ε` of its min-max level, leaving
the punishment continuation an arbitrary behavior profile.
`GameTheory.QuittingInstantPunishmentεEquilibriumExistence` instead fixes the
continuation to a constant row.

`QuittingProfilePunishmentεEquilibriumExistence` states the paper's shape, and
`quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment` proves
the two existence statements equivalent.  The constant-row form is therefore
the canonical one and the arbitrary-profile form is derived from it.

The mechanism is that a sure first-stage quitter makes the continuation
unreachable for every player but that quitter.  Formally:

* `quittingTerminalPayoff_update_of_sureAbsorbingDeviatedRow` shows a
  deviation's value is read off the deviated first row alone whenever that row
  still absorbs surely, which for every non-quitter it does;
* the quitter's own deviations are capped by
  `quittingTerminalPayoff_update_oneStagePunishedProfile_le`, whose only
  continuation input is the constant row's cap
  `quittingStationaryUnilateralCap`; and
* `quittingStationaryPunishmentValue_le_of_forall_hazard_le` turns the spliced
  profile's own equilibrium inequality into a lower bound
  `quittingPunishmentValue ≤ B` on the same quantity, so a constant row within
  `ε / 2` of the min-max costs at most `ε / 2` more.

The punishment clause of the paper's branch is not needed for the harder
direction: `quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter`
derives the constant-row branch from the bare existence of approximate
equilibria with a sure first-stage quitter.  The equilibrium condition already
forces the quitter's continuation value down to its min-max, since by
`quittingPunishmentValue_eq_stationaryPunishmentValue` no opponent plan can
promise less.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Sure absorption at the first stage -/

/-- A deviation whose deviated first row still absorbs surely is worth exactly
that row's absorbing contribution, so its value depends on the profile only
through the profile's first live row. -/
theorem quittingTerminalPayoff_update_of_sureAbsorbingDeviatedRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (hmass : quittingStationaryContinueMass
      (Function.update (quittingProfileLiveRoot reward profile 0) who
        (quittingBehaviorLiveHazard reward deviation 0)) = 0) :
    quittingTerminalPayoff reward
        (Function.update profile who deviation) who =
      quittingRootAbsorbingContribution reward
        (Function.update (quittingProfileLiveRoot reward profile 0) who
          (quittingBehaviorLiveHazard reward deviation 0)) who := by
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
    quittingRootSequenceHazardTerminalValue_zero_split, hmass, zero_mul,
    add_zero]

/-- A row in which some player quits surely absorbs surely, whatever any other
single player is doing. -/
theorem quittingStationaryContinueMass_update_of_sureQuitter
    {root : ι → PMF Bool} {quitter who : ι} (hne : who ≠ quitter)
    (hquit : root quitter = PMF.pure true) (marginal : PMF Bool) :
    quittingStationaryContinueMass (Function.update root who marginal) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_eq_zero (Finset.mem_univ quitter) ?_
  rw [Function.update_of_ne (Ne.symm hne), hquit]
  simp

omit [DecidableEq ι] in
/-- A row in which some player quits surely absorbs surely. -/
theorem quittingStationaryContinueMass_of_sureQuitter
    {root : ι → PMF Bool} {quitter : ι} (hquit : root quitter = PMF.pure true) :
    quittingStationaryContinueMass root = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_eq_zero (Finset.mem_univ quitter) ?_
  rw [hquit]
  simp

omit [DecidableEq ι] in
/-- The first live row of a spliced profile is its declared root. -/
@[simp] theorem quittingProfileLiveRoot_rootThenContinuation_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingProfileLiveRoot reward
        (quittingRootThenContinuationProfile reward root continuation) 0 =
      root := rfl

omit [DecidableEq ι] in
/-- The one-stage punished profile is the splice of its root with the constant
punishment row played forever. -/
theorem quittingOneStagePunishedProfile_eq_rootThenContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root punishRow : ι → PMF Bool) :
    quittingOneStagePunishedProfile reward root punishRow =
      quittingRootThenContinuationProfile reward root
        (quittingStationaryProfile reward punishRow) := by
  funext player time history
  cases time with
  | zero => rfl
  | succ time =>
      change quittingPhaseSwitchRoots (fun _ => root) (fun _ => punishRow) 1
        (0 + (time + 1)) player = punishRow player
      rw [Nat.zero_add]
      exact congrFun (quittingPhaseSwitchRoots_of_le _ _
        (Nat.succ_le_succ (Nat.zero_le time))) player

omit [DecidableEq ι] in
/-- A profile whose first live row absorbs surely pays exactly that row's
absorbing contribution. -/
theorem quittingTerminalPayoff_of_sureAbsorbingLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (hmass : quittingStationaryContinueMass
      (quittingProfileLiveRoot reward profile 0) = 0) :
    quittingTerminalPayoff reward profile who =
      quittingRootAbsorbingContribution reward
        (quittingProfileLiveRoot reward profile 0) who := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot,
    quittingRootSequenceTerminalValue_zero_of_continueMass_eq_zero
      reward _ who hmass]

/-! ## Branch S.2 with an arbitrary punishment profile -/

/-- **Branch S.2 as the paper states it.**  For every positive tolerance
there is a player who quits surely at the first stage and an arbitrary
behavior profile played from the second stage on that holds that player within
the tolerance of its exact min-max, such that the splice is a terminal
approximate equilibrium. -/
def QuittingProfilePunishmentεEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (quitter : ι) (root : ι → PMF Bool)
      (punish : (quittingGame reward).BehaviorProfile),
    root quitter = PMF.pure true ∧
      quittingBestReplyValue reward punish quitter ≤
        quittingPunishmentValue reward quitter + ε ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingRootThenContinuationProfile reward root punish)

/-! ## The constant-row branch already follows from a sure first-stage quitter -/

/-- **The punishment clause is automatic.**  If at every positive tolerance
some terminal approximate equilibrium has a player quitting surely at the
first stage, then the constant-row branch `S.2` holds.

Only the quitter can reach the continuation, and its own equilibrium
inequality already caps every continuation value it could obtain there.  That
cap is at least the min-max level, so a constant row chosen within `ε / 2` of
the min-max replaces the original continuation at a cost of at most
`ε / 2`. -/
theorem quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hexists : ∀ ε : ℝ, 0 < ε → ∃ (quitter : ι) (root : ι → PMF Bool)
        (punish : (quittingGame reward).BehaviorProfile),
      root quitter = PMF.pure true ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
          ε (quittingRootThenContinuationProfile reward root punish)) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨quitter, root, punish, hquit, hnash⟩ := hexists (ε / 2) hhalf
  obtain ⟨punishRow, hrow⟩ :=
    exists_punishRow_stationaryUnilateralCap_le reward quitter hhalf
  refine ⟨quitter, root, punishRow, hquit, hrow.trans (by linarith), ?_⟩
  set splice := quittingRootThenContinuationProfile reward root punish
    with hsplice
  set target := quittingOneStagePunishedProfile reward root punishRow
    with htarget
  set cap := quittingStationaryUnilateralCap reward punishRow quitter
    with hcapdef
  have hmass0 : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hquit
  have hspliceRoot : quittingProfileLiveRoot reward splice 0 = root := rfl
  have htargetRoot : quittingProfileLiveRoot reward target 0 = root :=
    quittingProfileLiveRoot_oneStagePunishedProfile_zero reward root punishRow
  have hvalue : ∀ player : ι,
      quittingTerminalPayoff reward target player =
        quittingRootAbsorbingContribution reward root player := fun player =>
    quittingTerminalPayoff_oneStagePunishedProfile reward root punishRow player
      hmass0
  have hspliceValue : ∀ player : ι,
      quittingTerminalPayoff reward splice player =
        quittingRootAbsorbingContribution reward root player := by
    intro player
    rw [quittingTerminalPayoff_of_sureAbsorbingLiveRoot reward splice player
      (by rw [hspliceRoot]; exact hmass0), hspliceRoot]
  intro who deviation
  rw [hvalue who]
  by_cases hne : who = quitter
  · subst who
    have hbound := quittingTerminalPayoff_update_oneStagePunishedProfile_le
      reward root punishRow quitter deviation
    rw [← htarget, ← hcapdef] at hbound
    have hquitLeg :
        quittingStationaryFixedOpponentsQuitValue reward root quitter =
          quittingRootAbsorbingContribution reward root quitter := by
      change quittingRootAbsorbingContribution reward
        (Function.update root quitter (PMF.pure true)) quitter = _
      rw [← hquit, Function.update_eq_self]
    have hmassNonneg :
        0 ≤ quittingStationaryFixedOpponentsContinueMass root quitter :=
      quittingStationaryFixedOpponentsContinueMass_nonneg root quitter
    have hmassLeOne :
        quittingStationaryFixedOpponentsContinueMass root quitter ≤ 1 :=
      quittingStationaryFixedOpponentsContinueMass_le_one root quitter
    have hcontinueLeg :
        quittingStationaryFixedOpponentsContinueReward reward root quitter +
            quittingStationaryFixedOpponentsContinueMass root quitter * cap ≤
          quittingRootAbsorbingContribution reward root quitter + ε := by
      by_cases hzero :
          quittingStationaryFixedOpponentsContinueMass root quitter = 0
      · have hnever := quittingTerminalPayoff_update_neverQuit reward splice
          quitter (by rw [hspliceRoot]; exact hzero)
        rw [hspliceRoot] at hnever
        have hdev := hnash quitter
          (fun _time _history => (PMF.pure false : PMF Bool))
        rw [hnever, hspliceValue quitter] at hdev
        rw [hzero]
        linarith
      · have hpos :
            0 < quittingStationaryFixedOpponentsContinueMass root quitter :=
          lt_of_le_of_ne hmassNonneg (Ne.symm hzero)
        set mass := quittingStationaryFixedOpponentsContinueMass root quitter
          with hmassdef
        set gain := quittingStationaryFixedOpponentsContinueReward reward root
          quitter with hgaindef
        set payoff := quittingRootAbsorbingContribution reward root quitter
          with hpayoffdef
        have hall : ∀ hazard : ℕ → PMF Bool,
            quittingRootSequenceHazardTerminalValue reward
                (fun time => quittingProfileLiveRoot reward splice (time + 1))
                quitter hazard 0 ≤
              (payoff + ε / 2 - gain) / mass := by
          intro hazard
          obtain ⟨deviation, hdeviation⟩ :=
            exists_quittingTerminalPayoff_update_continueThen reward splice
              quitter hazard
          rw [hspliceRoot] at hdeviation
          have hdev := hnash quitter deviation
          rw [hdeviation, hspliceValue quitter] at hdev
          rw [le_div_iff₀ hpos]
          nlinarith
        have hminmax := quittingStationaryPunishmentValue_le_of_forall_hazard_le
          reward (fun time => quittingProfileLiveRoot reward splice (time + 1))
          quitter hall
        rw [← quittingPunishmentValue_eq_stationaryPunishmentValue] at hminmax
        have hcapLe : cap ≤ quittingPunishmentValue reward quitter + ε / 2 :=
          hrow
        have hscaled : mass * cap ≤
            mass * (quittingPunishmentValue reward quitter + ε / 2) :=
          mul_le_mul_of_nonneg_left hcapLe hmassNonneg
        have hminmaxScaled :
            mass * quittingPunishmentValue reward quitter ≤
              payoff + ε / 2 - gain := by
          have := mul_le_mul_of_nonneg_left hminmax hmassNonneg
          rwa [mul_div_cancel₀ _ (ne_of_gt hpos)] at this
        nlinarith
    exact le_trans hbound (max_le (by rw [hquitLeg]; linarith) hcontinueLeg)
  · have hdeviated : quittingStationaryContinueMass
        (Function.update root who
          (quittingBehaviorLiveHazard reward deviation 0)) = 0 :=
      quittingStationaryContinueMass_update_of_sureQuitter hne hquit _
    have htargetDev := quittingTerminalPayoff_update_of_sureAbsorbingDeviatedRow
      reward target who deviation (by rw [htargetRoot]; exact hdeviated)
    have hspliceDev := quittingTerminalPayoff_update_of_sureAbsorbingDeviatedRow
      reward splice who deviation (by rw [hspliceRoot]; exact hdeviated)
    rw [htargetRoot] at htargetDev
    rw [hspliceRoot] at hspliceDev
    have hdev := hnash who deviation
    rw [hspliceDev, hspliceValue who] at hdev
    rw [htargetDev]
    linarith

/-! ## The two shapes of branch S.2 agree -/

/-- The constant-row branch implies the arbitrary-profile branch: a constant
punishment row is a behavior profile, and by
`quittingTerminalPayoff_update_stationary_le_cap` its best-reply value is at
most the row's selected cap. -/
theorem quittingProfilePunishmentεEquilibriumExistence_of_constantRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hbranch : QuittingInstantPunishmentεEquilibriumExistence reward) :
    QuittingProfilePunishmentεEquilibriumExistence reward := by
  intro ε hε
  obtain ⟨quitter, root, punishRow, hquit, hcap, hnash⟩ := hbranch ε hε
  haveI : Nonempty ((quittingGame reward).BehaviorStrategy quitter) :=
    ⟨fun _ _ => PMF.pure false⟩
  refine ⟨quitter, root, quittingStationaryProfile reward punishRow, hquit,
    ?_, ?_⟩
  · refine le_trans (ciSup_le fun deviation =>
      quittingTerminalPayoff_update_stationary_le_cap reward punishRow quitter
        deviation) hcap
  · rwa [← quittingOneStagePunishedProfile_eq_rootThenContinuation]

/-- **The two shapes of branch S.2 are equivalent.**  Restricting the
punishment continuation to a constant row costs nothing at the level of the
existence statement, so the constant-row form
`QuittingInstantPunishmentεEquilibriumExistence` is the canonical one and the
arbitrary-profile form is derived from it. -/
theorem quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingInstantPunishmentεEquilibriumExistence reward ↔
      QuittingProfilePunishmentεEquilibriumExistence reward := by
  refine ⟨quittingProfilePunishmentεEquilibriumExistence_of_constantRow,
    fun hprofile => quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
      fun ε hε => ?_⟩
  obtain ⟨quitter, root, punish, hquit, _, hnash⟩ := hprofile ε hε
  exact ⟨quitter, root, punish, hquit, hnash⟩

end GameTheory
