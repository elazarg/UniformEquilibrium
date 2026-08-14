/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CounterexampleAtomEndpointRisePassport

/-!
# Minimum accounting for the prescribed off-diagonal atom

The prescribed branch of the fixed-label atom packet raises one observer's
debt by a fixed amount at the full mover-reset endpoint.  Global minimality
forces a very small algebraic dichotomy: either that endpoint makes a fixed
total-debt excursion, or some coordinate other than the observer loses a
fixed average amount of debt.

The second alternative is not a new transfer edge.  The same reset already
realizes the mover's payoff gain as an exact loss of mover debt, while global
minimality gives precisely the standard opposite-face passive-transfer
account.  Thus the compensating coordinate may be the mover itself.  If it
is a third player, its debt decrease still carries neither a deviation by
that player nor the prescribed atom label.  Consequently this accounting
does not feed the current surface-tension, minimum-tangent, or atomic-label
consumers without an additional reset-face or response provenance premise.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If one coordinate rises by `charge` while the target stays within
`charge / 2` of a lower reference level, some other coordinate must pay a
strict average share.  This is only a finite-coordinate debt identity; it
contains no reset or terminal-law information. -/
theorem endpointDebtRise_excursion_or_compensatingDecrease
    (minimum source target : QuittingTerminalSemanticPair ι)
    (mover observer : ι) (hobserver : observer ≠ mover)
    (charge : ℝ)
    (hsourceLower : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum source)
    (hrise : charge ≤
      quittingTerminalSemanticDebt target observer -
        quittingTerminalSemanticDebt source observer) :
    charge / 2 ≤
        quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum minimum ∨
      ∃ payer ∈ Finset.univ.erase observer,
        charge / 2 /
            ((Finset.univ.erase observer).card : ℝ) <
          quittingTerminalSemanticDebt source payer -
            quittingTerminalSemanticDebt target payer := by
  classical
  by_cases hexcur : charge / 2 ≤
      quittingTerminalSemanticDebtSum target -
        quittingTerminalSemanticDebtSum minimum
  · exact Or.inl hexcur
  · right
    let payers : Finset ι := Finset.univ.erase observer
    let decrease : ι → ℝ := fun payer =>
      quittingTerminalSemanticDebt source payer -
        quittingTerminalSemanticDebt target payer
    have hpayers : payers.Nonempty := by
      refine ⟨mover, ?_⟩
      simp only [payers, Finset.mem_erase, Finset.mem_univ, and_true]
      exact Ne.symm hobserver
    have htotal : (∑ player, decrease player) =
        quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebtSum target := by
      unfold decrease quittingTerminalSemanticDebtSum
      rw [Finset.sum_sub_distrib]
    have hsplit := Finset.sum_erase_add Finset.univ decrease
      (Finset.mem_univ observer)
    have hcomplement : charge / 2 < ∑ payer ∈ payers, decrease payer := by
      have htargetUpper :
          quittingTerminalSemanticDebtSum target -
              quittingTerminalSemanticDebtSum minimum <
            charge / 2 := lt_of_not_ge hexcur
      have hobserverDecrease : decrease observer ≤ -charge := by
        dsimp only [decrease]
        linarith
      change (∑ payer ∈ payers, decrease payer) + decrease observer =
          ∑ player, decrease player at hsplit
      rw [htotal] at hsplit
      linarith
    obtain ⟨payer, hpayer, hpayerMax⟩ :=
      Finset.exists_max_image payers decrease hpayers
    refine ⟨payer, by simpa only [payers] using hpayer, ?_⟩
    have hsumLe : (∑ other ∈ payers, decrease other) ≤
        (payers.card : ℝ) * decrease payer := by
      have hbound := payers.sum_le_card_nsmul decrease (decrease payer)
        (fun other hother => hpayerMax other hother)
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hbound
    have hcard : 0 < (payers.card : ℝ) := by
      exact_mod_cast hpayers.card_pos
    apply (div_lt_iff₀ hcard).2
    dsimp only [payers]
    nlinarith

/-- A unilateral replacement converts the mover's debt loss exactly into
the mover's prescribed-payoff gain.  This is the familiar debt-realization
identity, not a new observer-side certificate. -/
theorem terminalSemanticDebt_source_sub_update_self_eq_payoffGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) mover =
      quittingTerminalPayoff reward
          (Function.update profile mover target) mover -
        quittingTerminalPayoff reward profile mover := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change (quittingContinuationBestResponseValue reward profile mover -
      quittingTerminalPayoff reward profile mover) -
      (quittingContinuationBestResponseValue reward
          (Function.update profile mover target) mover -
        quittingTerminalPayoff reward
          (Function.update profile mover target) mover) = _
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- The fixed prescribed sequence yields only the preceding ledger
dichotomy.  In the compensating branch the selected payer is allowed to be
the reset mover. -/
theorem QuittingStoppingLawPrescribedAtomEndpointRiseSequence.endpointExcursion_or_compensatingDecrease
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet)
    (n : ℕ) :
    let profile := frontier.profiles (frontier.subseq (sequence.rank n))
    let endpoint := Function.update profile packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n)))
    packet.chronology.charge / 2 ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward endpoint) -
          quittingTerminalSemanticDebtSum frontier.base ∨
      ∃ payer ∈ Finset.univ.erase packet.chronology.observer,
        packet.chronology.charge / 2 /
            ((Finset.univ.erase packet.chronology.observer).card : ℝ) <
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) payer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward endpoint) payer := by
  dsimp only
  apply endpointDebtRise_excursion_or_compensatingDecrease
    frontier.base
    (quittingTerminalSemanticPair reward
      (frontier.profiles (frontier.subseq (sequence.rank n))))
    (quittingTerminalSemanticPair reward
      (Function.update
        (frontier.profiles (frontier.subseq (sequence.rank n)))
        packet.chronology.mover.1
        (frontier.bestResponse packet.chronology.mover
          (frontier.subseq (sequence.rank n)))))
    packet.chronology.mover.1 packet.chronology.observer
    packet.chronology.observer_ne_mover packet.chronology.charge
  · apply frontier.base_minimum
    exact quittingTerminalSemanticPair_mem_carrier reward _
  · exact sequence.endpointDebtRise n

/-- Exact passive-transfer passport for the same prescribed endpoint.  The
positive observer rise is already one off-diagonal recipient of the mover's
ordinary minimum-reference transfer.  Hence the global-minimum input has not
created a second reset edge. -/
theorem QuittingStoppingLawPrescribedAtomEndpointRiseSequence.endpointPassiveTransferAccount
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet)
    (n : ℕ) :
    let profile := frontier.profiles (frontier.subseq (sequence.rank n))
    let endpoint := Function.update profile packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n)))
    let sourcePair := quittingTerminalSemanticPair reward profile
    let endpointPair := quittingTerminalSemanticPair reward endpoint
    let gain := quittingTerminalPayoff reward endpoint
        packet.chronology.mover.1 -
      quittingTerminalPayoff reward profile packet.chronology.mover.1
    quittingTerminalSemanticDebt endpointPair packet.chronology.mover.1 =
        quittingTerminalSemanticDebt sourcePair packet.chronology.mover.1 -
          gain ∧
      gain ≤
        (quittingTerminalSemanticDebtSum sourcePair -
          quittingTerminalSemanticDebtSum frontier.base) +
        ∑ recipient ∈ Finset.univ.erase packet.chronology.mover.1,
          quittingTerminalSemanticDebtChange sourcePair endpointPair recipient ∧
      packet.chronology.observer ∈
          Finset.univ.erase packet.chronology.mover.1 ∧
      packet.chronology.charge ≤
        quittingTerminalSemanticDebtChange sourcePair endpointPair
          packet.chronology.observer := by
  dsimp only
  let profile := frontier.profiles (frontier.subseq (sequence.rank n))
  let endpoint := Function.update profile packet.chronology.mover.1
    (frontier.bestResponse packet.chronology.mover
      (frontier.subseq (sequence.rank n)))
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let gain := quittingTerminalPayoff reward endpoint
      packet.chronology.mover.1 -
    quittingTerminalPayoff reward profile packet.chronology.mover.1
  have hdecrease : quittingTerminalSemanticDebt endpointPair
      packet.chronology.mover.1 =
      quittingTerminalSemanticDebt sourcePair packet.chronology.mover.1 -
        gain := by
    have hidentity := terminalSemanticDebt_source_sub_update_self_eq_payoffGain
      reward profile packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n)))
    dsimp only [sourcePair, endpointPair, endpoint, gain] at hidentity ⊢
    linarith
  have htransfer := minimumReference_opponentTransfer_of_coordinateDecrease
    reward frontier.base sourcePair endpointPair packet.chronology.mover.1 gain
    frontier.base_minimum
    (quittingTerminalSemanticPair_mem_carrier reward _) hdecrease
  refine ⟨hdecrease, htransfer, ?_, ?_⟩
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact packet.chronology.observer_ne_mover
  · simpa only [quittingTerminalSemanticDebtChange, sourcePair,
      endpointPair, endpoint, profile] using sequence.endpointDebtRise n

/-- If the compensating coordinate selected by the minimum ledger is the
mover, its bound is literally just the already-known mover payoff gain.
Otherwise the packet exposes only an unlabelled third-coordinate debt drop.
Neither alternative retains a second reset or the prescribed atom. -/
theorem QuittingStoppingLawPrescribedAtomEndpointRiseSequence.endpointExcursion_or_knownMoverGain_or_unlabelledThirdDecrease
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {packet : QuittingStoppingLawAtomEndpointRiseChronology frontier}
    (sequence : QuittingStoppingLawPrescribedAtomEndpointRiseSequence packet)
    (n : ℕ) :
    let profile := frontier.profiles (frontier.subseq (sequence.rank n))
    let endpoint := Function.update profile packet.chronology.mover.1
      (frontier.bestResponse packet.chronology.mover
        (frontier.subseq (sequence.rank n)))
    let threshold := packet.chronology.charge / 2 /
      ((Finset.univ.erase packet.chronology.observer).card : ℝ)
    packet.chronology.charge / 2 ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward endpoint) -
          quittingTerminalSemanticDebtSum frontier.base ∨
      threshold <
          quittingTerminalPayoff reward endpoint packet.chronology.mover.1 -
            quittingTerminalPayoff reward profile packet.chronology.mover.1 ∨
      ∃ payer ∈ Finset.univ.erase packet.chronology.observer,
        payer ≠ packet.chronology.mover.1 ∧
          threshold <
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) payer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward endpoint) payer := by
  dsimp only
  rcases sequence.endpointExcursion_or_compensatingDecrease n with hexcur |
      ⟨payer, hpayer, hpayerDecrease⟩
  · exact Or.inl hexcur
  · right
    by_cases hpayerMover : payer = packet.chronology.mover.1
    · left
      subst payer
      rw [terminalSemanticDebt_source_sub_update_self_eq_payoffGain] at hpayerDecrease
      exact hpayerDecrease
    · exact Or.inr ⟨payer, hpayer, hpayerMover, hpayerDecrease⟩

end GameTheory
