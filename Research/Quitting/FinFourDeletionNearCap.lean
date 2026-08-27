/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Punishment.SharedPunishment
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# The deletion and near-cap half of the Fin4 collision producer

This Research module makes the literal deletion source and the finite
near-cap update from a terminal exploitability gap.  The final seven-atom
collision expansion is kept as a separate interface: the deletion and
near-cap construction does not silently identify a root-semantic expression
with a stage-mass decomposition.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Unrestricted terminal best-reply debt. -/
def quittingTerminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) : ℝ :=
  quittingBestReplyValue reward profile who -
    quittingTerminalPayoff reward profile who

@[simp] theorem quittingTerminalDebt_def
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalDebt reward profile who =
      quittingBestReplyValue reward profile who -
        quittingTerminalPayoff reward profile who := rfl

/-- Nonempty terminal coalitions not containing the deleted player. -/
abbrev FinFourDeletionSurvivorTerminal (j : Fin 4) :=
  {terminal : {S : Finset (Fin 4) // S.Nonempty} // j ∉ terminal.1}

/-- The terminal obtained by adjoining the deleted player to a survivor
coalition. -/
def finFourDeletionJoinTerminal (j : Fin 4)
    (terminal : FinFourDeletionSurvivorTerminal j) :
    {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨terminal.1.1 ∪ {j}, by simp⟩

/-- The floor used by the deleted-player solo premium. -/
def finFourDeletionFloor
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (j : Fin 4) : ℝ :=
  min 0 (sInf (Set.range fun terminal : FinFourDeletionSurvivorTerminal j =>
    reward terminal.1 j))

/-- The deleted player's solo premium over the survivor floor. -/
def finFourDeletionSoloPremium
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (j : Fin 4) : ℝ :=
  max 0 (reward (quittingSingletonTerminal j) j -
    finFourDeletionFloor reward j)

/-- The largest gain from joining a nonempty survivor coalition. -/
def finFourDeletionCollisionCap
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (j : Fin 4) : ℝ :=
  max 0 (sSup (Set.range fun terminal : FinFourDeletionSurvivorTerminal j =>
    reward (finFourDeletionJoinTerminal j terminal) j - reward terminal.1 j))

/-- The literal data supplied by deletion and the near-cap choice.  The
`coalition` field is intentionally not included: its stage-mass expansion is
a separate root-to-stage adapter. -/
structure FinFourDeletionNearCapData
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (j : Fin 4) (epsilon delta gamma : ℝ) where
  rho : (quittingGame (quittingDeletePlayerReward reward j)).BehaviorProfile
  solo_premium_lt : finFourDeletionSoloPremium reward j < gamma
  sigma : (quittingGame reward).BehaviorProfile
  sigma_eq : sigma = quittingLiftDeletedProfile reward (fun who => who = j) rho
  t : ℕ
  tau : (quittingGame reward).BehaviorProfile
  tau_eq : tau = Function.update sigma j
    (quittingPureTimeBehaviorStrategy reward j (some t))
  survivor : QuittingDeletedPlayer j
  all_survivor_debt : ∀ who : QuittingDeletedPlayer j,
    quittingTerminalDebt reward sigma who.1 ≤ epsilon
  survivor_debt : quittingTerminalDebt reward sigma survivor.1 ≤ epsilon
  omitted_debt : gamma ≤ quittingTerminalDebt reward sigma j
  near_cap_gain : gamma - delta ≤
    quittingTerminalPayoff reward tau j - quittingTerminalPayoff reward sigma j
  cap_preserved : quittingBestReplyValue reward tau j =
    quittingBestReplyValue reward sigma j
  near_cap_debt : quittingTerminalDebt reward tau j ≤ delta
  survivor_after : gamma ≤ quittingTerminalDebt reward tau survivor.1
  payoff_update : quittingTerminalPayoff reward tau j =
    quittingTerminalPayoff reward
      (Function.update sigma j
        (quittingPureTimeBehaviorStrategy reward j (some t))) j

/-! ## The literal deletion/near-cap producer -/

theorem exists_finFour_deletionNearCapData
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (j : Fin 4) {gamma epsilon delta : ℝ}
    (_hgamma : 0 < gamma)
    (hexploit : HasTerminalExploitabilityGap reward gamma)
    (_hPi : finFourDeletionSoloPremium reward j < gamma)
    (hepsilon : 0 < epsilon) (hepsilon_lt : epsilon < gamma)
    (hdelta : 0 < delta)
    (_hdelta_ltPi : delta < gamma - finFourDeletionSoloPremium reward j) :
    Nonempty (FinFourDeletionNearCapData reward j epsilon delta gamma) := by
  have hdelta_lt_gamma : delta < gamma := by
    have hPi_nonneg : 0 ≤ finFourDeletionSoloPremium reward j :=
      le_max_left _ _
    exact lt_of_lt_of_le _hdelta_ltPi (sub_le_self _ hPi_nonneg)
  let deleted : Fin 4 → Prop := fun who => who = j
  let reducedReward := quittingDeletePlayerReward reward j
  have hcard : Fintype.card (QuittingDeletedPlayer j) = 3 := by
    exact card_quittingDeletedPlayer_eq_three_of_card_eq_four j (by decide)
  obtain ⟨target, htarget⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three hcard reducedReward
  obtain ⟨rho, hrho⟩ :=
    quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
      reducedReward target htarget epsilon hepsilon
  let sigma := quittingLiftDeletedProfile reward deleted rho
  have hsurvivor : ∀ who : QuittingDeletedPlayer j,
      quittingTerminalDebt reward sigma who.1 ≤ epsilon := by
    intro who
    rw [quittingTerminalDebt_def]
    change quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward deleted rho) who.1 -
      quittingTerminalPayoff reward
        (quittingLiftDeletedProfile reward deleted rho) who.1 ≤ epsilon
    rw [quittingBestReplyValue_liftDeletedProfile,
      quittingTerminalPayoff_liftDeletedProfile]
    have h := hrho who
      (quittingPureTimeBehaviorStrategy reducedReward who none)
    have hbest := quittingBestReplyValue_le reducedReward rho who
      (fun deviation => by
        exact hrho who deviation)
    linarith
  have hgap := hexploit sigma
  obtain ⟨witness, deviation, hwitness⟩ := hgap
  have hdebt_witness : gamma ≤ quittingTerminalDebt reward sigma witness := by
    rw [quittingTerminalDebt_def]
    have hbest := le_quittingBestReplyValue reward sigma witness deviation
    linarith
  have hnot_survivor : witness = j := by
    by_contra hne
    let who : QuittingDeletedPlayer j := ⟨witness, hne⟩
    have hsmall := hsurvivor who
    linarith
  subst witness
  let cap := quittingBestReplyValue reward sigma j
  let current := quittingTerminalPayoff reward sigma j
  have hdebt : gamma ≤ cap - current := by
    exact hdebt_witness
  let behaviorValues : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy j =>
    quittingTerminalPayoff reward (Function.update sigma j deviation) j
  let pureValues : Set ℝ := Set.range fun quitTime : Option ℕ =>
    quittingTerminalPayoff reward
      (Function.update sigma j (quittingPureTimeBehaviorStrategy reward j quitTime)) j
  have hpure_nonempty : pureValues.Nonempty := by
    exact ⟨current, ⟨none, by
      change quittingTerminalPayoff reward
        (Function.update sigma j
          (quittingPureTimeBehaviorStrategy reward j none)) j = current
      rw [show Function.update sigma j
          (quittingPureTimeBehaviorStrategy reward j none) = sigma by
            exact Function.update_liftDeletedProfile_never reward deleted rho
              (howner := rfl)]
      ⟩⟩
  have hcap_sSup : cap = sSup behaviorValues := by
    rw [sSup_range]
    rfl
  have hpure_sSup : sSup pureValues = cap := by
    rw [show pureValues = Set.range (fun quitTime : Option ℕ =>
        quittingTerminalPayoff reward
          (Function.update sigma j
            (quittingPureTimeBehaviorStrategy reward j quitTime)) j) by rfl]
    rw [← sSup_range_quittingTerminalPayoff_update_eq_pureTime reward sigma j]
    exact hcap_sSup.symm
  have hbelow : current + (cap - current) - delta < sSup pureValues := by
    rw [hpure_sSup]
    linarith
  obtain ⟨value, hvalue_mem, hvalue⟩ :=
    exists_lt_of_lt_csSup hpure_nonempty hbelow
  obtain ⟨quitTime, rfl⟩ := hvalue_mem
  have htime_never : quitTime ≠ none := by
    intro hnone
    subst quitTime
    have heq : Function.update sigma j
        (quittingPureTimeBehaviorStrategy reward j none) = sigma := by
      exact Function.update_liftDeletedProfile_never reward deleted rho
        (howner := rfl)
    simp only [heq] at hvalue
    linarith
  obtain ⟨t, rfl⟩ := Option.ne_none_iff_exists'.mp htime_never
  let tau := Function.update sigma j
    (quittingPureTimeBehaviorStrategy reward j (some t))
  have hgain : gamma - delta ≤
      quittingTerminalPayoff reward tau j - quittingTerminalPayoff reward sigma j := by
    dsimp [tau, current] at hvalue
    linarith
  have hcap_tau : quittingBestReplyValue reward tau j = cap := by
    apply quittingBestReplyValue_congr_of_opponents reward j
    intro player hplayer
    simp [tau, hplayer]
  have hdebt_tau : quittingTerminalDebt reward tau j ≤ delta := by
    rw [quittingTerminalDebt_def, hcap_tau]
    dsimp [tau, current] at hvalue
    linarith
  have hgap_tau := hexploit tau
  obtain ⟨i, deviation_i, hi⟩ := hgap_tau
  have hi_debt : gamma ≤ quittingTerminalDebt reward tau i := by
    rw [quittingTerminalDebt_def]
    have hbest := le_quittingBestReplyValue reward tau i deviation_i
    linarith
  have hi_survivor : i ≠ j := by
    intro hij
    subst i
    linarith
  let survivor : QuittingDeletedPlayer j := ⟨i, hi_survivor⟩
  exact ⟨{
    rho := rho
    solo_premium_lt := _hPi
    sigma := sigma
    sigma_eq := rfl
    t := t
    tau := tau
    tau_eq := rfl
    survivor := survivor
    all_survivor_debt := hsurvivor
    survivor_debt := hsurvivor survivor
    omitted_debt := hdebt_witness
    near_cap_gain := hgain
    cap_preserved := by simpa [cap] using hcap_tau
    near_cap_debt := hdebt_tau
    survivor_after := hi_debt
    payoff_update := rfl
  }⟩

end GameTheory
