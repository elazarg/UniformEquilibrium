/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.NearMinimumActualDeviationRectangle

/-!
# Recentring a near-minimum reset gives a literal strategic sign

The zero-source-debt branch of the stopping-law reset rectangle is not
actually signless.  It is only signless at the *old* source.  A reset which
decreases the mover's debt by more than the near-minimum error must transfer
positive debt to an opponent at the mixed profile.  Choosing an approximate
best response there realizes that transferred debt as a strictly profitable
behavioral deviation.

Thus no sign has to be transported across the reset square.  The mixed
profile itself is the new, literal source of the profitable deviation.  The
price is explicit: the best-response error must be smaller than the average
transferred debt.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Recentered source-side strategic sign.**

Let `profile` be within `epsilon` of the global semantic-debt minimum and mix
one player's whole stopping law toward `target` with weight `lambda`.  If the
scaled mover gain exceeds `epsilon`, then every best-response tolerance
strictly below the average excess transfer produces one opponent and one
actual behavioral deviation which is strictly profitable at the mixed
profile.

This includes the branch in which the selected opponent has zero debt at the
original profile: the relevant source is the legal mixed profile, where the
opponent has acquired positive debt. -/
theorem exists_nearMinimumReset_recentered_actualDeviation_gain_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda epsilon eta : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1) (heta : 0 < eta)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon)
    (hscale : epsilon < lambda *
      (quittingTerminalPayoff reward (Function.update profile mover target) mover -
        quittingTerminalPayoff reward profile mover))
    (hetaSmall : eta <
      (lambda *
          (quittingTerminalPayoff reward
              (Function.update profile mover target) mover -
            quittingTerminalPayoff reward profile mover) - epsilon) /
        ((Finset.univ.erase mover).card : ℝ)) :
    let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward
      mover (profile mover) target lambda hlambda0.le hlambda1
    let mixedProfile := Function.update profile mover mixedStrategy
    ∃ recipient ∈ Finset.univ.erase mover,
      ∃ deviation : (quittingGame reward).BehaviorStrategy recipient,
        (lambda *
              (quittingTerminalPayoff reward
                  (Function.update profile mover target) mover -
                quittingTerminalPayoff reward profile mover) - epsilon) /
              ((Finset.univ.erase mover).card : ℝ) - eta ≤
            quittingTerminalPayoff reward
                (Function.update mixedProfile recipient deviation) recipient -
              quittingTerminalPayoff reward mixedProfile recipient ∧
          0 < quittingTerminalPayoff reward
                (Function.update mixedProfile recipient deviation) recipient -
              quittingTerminalPayoff reward mixedProfile recipient := by
  let endpointProfile := Function.update profile mover target
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    (profile mover) target lambda hlambda0.le hlambda1
  let mixedProfile := Function.update profile mover mixedStrategy
  let source := quittingTerminalSemanticPair reward profile
  let mixed := quittingTerminalSemanticPair reward mixedProfile
  let endpointMoverGain := quittingTerminalPayoff reward endpointProfile mover -
    quittingTerminalPayoff reward profile mover
  let debtChange : ι → ℝ := fun recipient ↦
    quittingTerminalSemanticDebtChange source mixed recipient
  let opponents := Finset.univ.erase mover
  have htarget : mixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward mixedProfile
  have hendpointDebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward endpointProfile) mover =
      quittingTerminalSemanticDebt source mover - endpointMoverGain := by
    dsimp only [endpointProfile, endpointMoverGain, source,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  have hmoverDecrease : quittingTerminalSemanticDebt mixed mover =
      quittingTerminalSemanticDebt source mover - lambda * endpointMoverGain := by
    have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward profile mover (profile mover) target lambda hlambda0.le hlambda1
    rw [Function.update_eq_self] at haffine
    change quittingTerminalSemanticDebt mixed mover =
        (1 - lambda) * quittingTerminalSemanticDebt source mover +
          lambda * quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward endpointProfile) mover at haffine
    rw [hendpointDebt] at haffine
    linarith
  have htransfer : lambda * endpointMoverGain ≤ epsilon +
      ∑ recipient ∈ opponents, debtChange recipient := by
    exact nearMinimumDebt_opponentTransfer_of_coordinateDecrease reward source
      mixed mover (lambda * endpointMoverGain) epsilon hnear htarget
        hmoverDecrease
  have haggregatePositive : 0 < lambda * endpointMoverGain - epsilon := by
    dsimp only [endpointMoverGain] at hscale ⊢
    linarith
  have hopponents : opponents.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at htransfer
    simp at htransfer
    linarith
  obtain ⟨recipient, hrecipient, hrecipientMax⟩ :=
    Finset.exists_max_image opponents debtChange hopponents
  have hsumLe : (∑ other ∈ opponents, debtChange other) ≤
      (opponents.card : ℝ) * debtChange recipient := by
    have hbound := opponents.sum_le_card_nsmul debtChange
      (debtChange recipient) (fun other hother => hrecipientMax other hother)
    simpa [nsmul_eq_mul, mul_comm] using hbound
  have hcardPositive : 0 < (opponents.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hopponents
  have hrise :
      (lambda * endpointMoverGain - epsilon) / (opponents.card : ℝ) ≤
        debtChange recipient := by
    apply (div_le_iff₀ hcardPositive).2
    linarith
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward mixedProfile recipient
      heta hM hreward
  have hsourceDebtNonneg : 0 ≤ quittingTerminalSemanticDebt source recipient :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hM hreward
      (quittingTerminalSemanticPair_mem_carrier reward profile) recipient
  have hmixedDebt : quittingTerminalSemanticDebt source recipient +
      debtChange recipient = quittingTerminalSemanticDebt mixed recipient := by
    simp only [debtChange, quittingTerminalSemanticDebtChange]
    ring
  have hdeviationGain :
      quittingTerminalSemanticDebt mixed recipient - eta ≤
        quittingTerminalPayoff reward
              (Function.update mixedProfile recipient deviation) recipient -
            quittingTerminalPayoff reward mixedProfile recipient := by
    change quittingContinuationBestResponseValue reward mixedProfile recipient -
        quittingTerminalPayoff reward mixedProfile recipient - eta ≤ _
    linarith
  have hgainLower :
      debtChange recipient - eta ≤
        quittingTerminalPayoff reward
              (Function.update mixedProfile recipient deviation) recipient -
            quittingTerminalPayoff reward mixedProfile recipient := by
    rw [← hmixedDebt] at hdeviationGain
    linarith
  have hetaBound : eta < debtChange recipient := by
    apply lt_of_lt_of_le _ hrise
    simpa only [endpointMoverGain, opponents] using hetaSmall
  dsimp only
  refine ⟨recipient, ?_, deviation, ?_⟩
  · simpa only [opponents] using hrecipient
  constructor
  · have := (sub_le_sub_right hrise eta).trans hgainLower
    simpa only [endpointMoverGain, opponents] using this
  · linarith

end GameTheory
