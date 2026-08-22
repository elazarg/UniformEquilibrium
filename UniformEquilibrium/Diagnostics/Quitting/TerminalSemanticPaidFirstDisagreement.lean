/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Quitting.Paths.SurvivalWeightedSuffixRegret

/-!
# Paid first disagreement of two pure quit times

An oriented witness switch retains an ordered source witness and receiving
witness.  On the receiving profile, their positive payoff difference is paid
at their first temporal disagreement.  This module keeps that chronology as
data: it records which selected witness is earlier, the exact opponents' live
mass reaching that date, and the reached Quit-versus-wait comparison.

The division-free estimate

`gain <= 2 * quittingRewardBound reward * liveMass`

is valid even when the reached mass is zero.  In particular, no informal
division by a possibly vanishing reach probability is used.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A relative pure-time plan waits strictly beyond the reached date.
`Never` is later than every finite date. -/
def IsQuittingStrictlyLaterDelay : Option ℕ → Prop
  | none => True
  | some delay => 0 < delay

/-- A data-bearing first-disagreement row for an ordered witness switch.

`receivingEarlier = true` means that the receiving witness Quits at `start`
and the source witness waits by `later`.  The false case has the opposite
chronology.  Thus the carrier remembers the ordered source and receiving
witnesses rather than only an unoriented Quit/Continue disjunction. -/
structure QuittingPaidFirstDisagreementRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (gain : ℝ) where
  sourceWitness : Option ℕ
  receivingWitness : Option ℕ
  start : ℕ
  later : Option ℕ
  later_strict : IsQuittingStrictlyLaterDelay later
  receivingEarlier : Bool
  chronology :
    if receivingEarlier then
      receivingWitness = some start ∧
        sourceWitness = quittingAbsolutePureTime start later
    else
      sourceWitness = some start ∧
        receivingWitness = quittingAbsolutePureTime start later
  liveMass : ℝ
  liveMass_eq : liveMass =
    quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward receiving) observer 0 start
  reachedGain : ℝ
  reachedGain_eq : reachedGain =
    if receivingEarlier then
      quittingFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward receiving) observer start -
        quittingRootSequenceRelativePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward receiving) observer start later
    else
      quittingRootSequenceRelativePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward receiving) observer start later -
        quittingFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward receiving) observer start
  edge_identity :
    quittingPureTimeDeviationPayoff reward receiving observer
          receivingWitness -
        quittingPureTimeDeviationPayoff reward receiving observer
          sourceWitness = liveMass * reachedGain
  gain_le_paid : gain ≤ liveMass * reachedGain
  gain_le_liveMass :
    gain ≤ 2 * quittingRewardBound reward * liveMass

private theorem abs_relativePureTimeTerminalValue_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (observer : ι) (start : ℕ)
    (later : Option ℕ) :
    |quittingRootSequenceRelativePureTimeTerminalValue
        reward roots observer start later| ≤ quittingRewardBound reward := by
  unfold quittingRootSequenceRelativePureTimeTerminalValue
    quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
  exact abs_quittingRootSequenceTerminalValue_le reward
    (quittingRootSequenceUpdate roots observer
      (quittingPureTimeHazard (quittingAbsolutePureTime start later)))
    observer start (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)

private theorem paidFirstDisagreement_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (start : ℕ) (later : Option ℕ)
    (liveMass reachedGain : ℝ)
    (hlive : liveMass = quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward receiving) observer 0 start)
    (hreached : reachedGain =
      quittingFixedOpponentsQuitValue reward
          (quittingProfileLiveRoot reward receiving) observer start -
        quittingRootSequenceRelativePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward receiving) observer start later ∨
      reachedGain =
        quittingRootSequenceRelativePureTimeTerminalValue reward
            (quittingProfileLiveRoot reward receiving) observer start later -
          quittingFixedOpponentsQuitValue reward
            (quittingProfileLiveRoot reward receiving) observer start) :
    liveMass * reachedGain ≤
      2 * quittingRewardBound reward * liveMass := by
  have hlive0 : 0 ≤ liveMass := by
    rw [hlive]
    exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
  have hquit := abs_quittingFixedOpponentsQuitValue_le_rewardBound
    reward (quittingProfileLiveRoot reward receiving) observer start
  have hlater := abs_relativePureTimeTerminalValue_le_rewardBound
    reward (quittingProfileLiveRoot reward receiving) observer start later
  rw [abs_le] at hquit hlater
  rcases hreached with hreached | hreached <;> rw [hreached]
  · nlinarith
  · nlinarith

/-- A positive receiving-edge difference between two deterministic quit
times yields an exact paid first-disagreement row, with a division-free live
mass estimate.  Finite times and `Never` are all retained. -/
theorem exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (sourceWitness receivingWitness : Option ℕ) (gain : ℝ)
    (hgain : 0 < gain)
    (hedge : gain ≤
      quittingPureTimeDeviationPayoff reward receiving observer
          receivingWitness -
        quittingPureTimeDeviationPayoff reward receiving observer
          sourceWitness) :
    ∃ row : QuittingPaidFirstDisagreementRow reward receiving observer gain,
      row.sourceWitness = sourceWitness ∧
        row.receivingWitness = receivingWitness := by
  rw [quittingPureTimeDeviationPayoff,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingPureTimeDeviationPayoff,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at hedge
  let roots := quittingProfileLiveRoot reward receiving
  cases receivingWitness with
  | none =>
      cases sourceWitness with
      | none =>
          simp at hedge
          linarith
      | some sourceTime =>
          let liveMass := quittingOpponentSurvivalWeight roots observer 0 sourceTime
          let reachedGain :=
            quittingRootSequenceRelativePureTimeTerminalValue reward roots observer
                sourceTime none -
              quittingFixedOpponentsQuitValue reward roots observer sourceTime
          have hdecoder :=
            quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
              reward roots observer sourceTime none
          have hedgeIdentity :
              quittingRootSequencePureTimeTerminalValue reward roots observer none 0 -
                  quittingRootSequencePureTimeTerminalValue reward roots observer
                    (some sourceTime) 0 =
                liveMass * reachedGain := by
            dsimp only [liveMass, reachedGain]
            have hneg := congrArg Neg.neg hdecoder
            calc
              _ = -(quittingOpponentSurvivalWeight roots observer 0 sourceTime *
                    (quittingFixedOpponentsQuitValue reward roots observer
                        sourceTime -
                      quittingRootSequenceRelativePureTimeTerminalValue reward
                        roots observer sourceTime none)) := by
                  simpa [quittingAbsolutePureTime] using hneg
              _ = _ := by ring
          have hpaidBound : liveMass * reachedGain ≤
              2 * quittingRewardBound reward * liveMass := by
            apply paidFirstDisagreement_bound reward receiving observer sourceTime
              none liveMass reachedGain rfl
            exact Or.inr rfl
          let row : QuittingPaidFirstDisagreementRow reward receiving observer gain := {
            sourceWitness := some sourceTime
            receivingWitness := none
            start := sourceTime
            later := none
            later_strict := trivial
            receivingEarlier := false
            chronology := by simp [quittingAbsolutePureTime]
            liveMass := liveMass
            liveMass_eq := rfl
            reachedGain := reachedGain
            reachedGain_eq := by dsimp [reachedGain, roots]
            edge_identity := by
              simpa [roots, quittingPureTimeDeviationPayoff] using hedgeIdentity
            gain_le_paid := by exact hedge.trans_eq hedgeIdentity
            gain_le_liveMass := hedge.trans_eq hedgeIdentity |>.trans hpaidBound
          }
          exact ⟨row, rfl, rfl⟩
  | some receivingTime =>
      cases sourceWitness with
      | none =>
          let liveMass :=
            quittingOpponentSurvivalWeight roots observer 0 receivingTime
          let reachedGain :=
            quittingFixedOpponentsQuitValue reward roots observer receivingTime -
              quittingRootSequenceRelativePureTimeTerminalValue reward roots observer
                receivingTime none
          have hdecoder :=
            quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
              reward roots observer receivingTime none
          have hpaidBound : liveMass * reachedGain ≤
              2 * quittingRewardBound reward * liveMass := by
            apply paidFirstDisagreement_bound reward receiving observer receivingTime
              none liveMass reachedGain rfl
            exact Or.inl rfl
          let row : QuittingPaidFirstDisagreementRow reward receiving observer gain := {
            sourceWitness := none
            receivingWitness := some receivingTime
            start := receivingTime
            later := none
            later_strict := trivial
            receivingEarlier := true
            chronology := by simp [quittingAbsolutePureTime]
            liveMass := liveMass
            liveMass_eq := rfl
            reachedGain := reachedGain
            reachedGain_eq := by dsimp [reachedGain, roots]
            edge_identity := by
              simpa [roots, quittingAbsolutePureTime,
                quittingPureTimeDeviationPayoff] using hdecoder
            gain_le_paid := by exact hedge.trans_eq hdecoder
            gain_le_liveMass := hedge.trans_eq hdecoder |>.trans hpaidBound
          }
          exact ⟨row, rfl, rfl⟩
      | some sourceTime =>
          by_cases hbefore : receivingTime < sourceTime
          · let delay := some (sourceTime - receivingTime)
            let liveMass :=
              quittingOpponentSurvivalWeight roots observer 0 receivingTime
            let reachedGain :=
              quittingFixedOpponentsQuitValue reward roots observer receivingTime -
                quittingRootSequenceRelativePureTimeTerminalValue reward roots observer
                  receivingTime delay
            have hle : receivingTime ≤ sourceTime := hbefore.le
            have hdecoder :=
              quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
                reward roots observer receivingTime delay
            have hdecoder' :
                quittingRootSequencePureTimeTerminalValue reward roots observer
                      (some receivingTime) 0 -
                    quittingRootSequencePureTimeTerminalValue reward roots observer
                      (some sourceTime) 0 = liveMass * reachedGain := by
              simpa [delay, liveMass, reachedGain, quittingAbsolutePureTime,
                Nat.add_sub_of_le hle] using hdecoder
            have hpaidBound : liveMass * reachedGain ≤
                2 * quittingRewardBound reward * liveMass := by
              apply paidFirstDisagreement_bound reward receiving observer
                receivingTime delay liveMass reachedGain rfl
              exact Or.inl rfl
            let row : QuittingPaidFirstDisagreementRow reward receiving observer gain := {
              sourceWitness := some sourceTime
              receivingWitness := some receivingTime
              start := receivingTime
              later := delay
              later_strict := by
                simpa [delay, IsQuittingStrictlyLaterDelay,
                  Nat.sub_pos_iff_lt] using hbefore
              receivingEarlier := true
              chronology := by
                simp [delay, quittingAbsolutePureTime, Nat.add_sub_of_le hle]
              liveMass := liveMass
              liveMass_eq := rfl
              reachedGain := reachedGain
              reachedGain_eq := by dsimp [reachedGain, roots]
              edge_identity := by
                simpa [roots, quittingPureTimeDeviationPayoff] using hdecoder'
              gain_le_paid := by exact hedge.trans_eq hdecoder'
              gain_le_liveMass := hedge.trans_eq hdecoder' |>.trans hpaidBound
            }
            exact ⟨row, rfl, rfl⟩
          · by_cases heq : receivingTime = sourceTime
            · subst sourceTime
              simp at hedge
              linarith
            · have hreverse : sourceTime < receivingTime := by omega
              let delay := some (receivingTime - sourceTime)
              let liveMass :=
                quittingOpponentSurvivalWeight roots observer 0 sourceTime
              let reachedGain :=
                quittingRootSequenceRelativePureTimeTerminalValue reward roots observer
                    sourceTime delay -
                  quittingFixedOpponentsQuitValue reward roots observer sourceTime
              have hle : sourceTime ≤ receivingTime := hreverse.le
              have hdecoder :=
                quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
                  reward roots observer sourceTime delay
              have hdecoder' :
                  quittingRootSequencePureTimeTerminalValue reward roots observer
                        (some receivingTime) 0 -
                      quittingRootSequencePureTimeTerminalValue reward roots observer
                        (some sourceTime) 0 = liveMass * reachedGain := by
                have hbase :
                    quittingRootSequencePureTimeTerminalValue reward roots observer
                          (some sourceTime) 0 -
                        quittingRootSequencePureTimeTerminalValue reward roots observer
                          (some receivingTime) 0 =
                      quittingOpponentSurvivalWeight roots observer 0 sourceTime *
                        (quittingFixedOpponentsQuitValue reward roots observer
                            sourceTime -
                          quittingRootSequenceRelativePureTimeTerminalValue reward roots
                            observer sourceTime delay) := by
                  simpa [delay, quittingAbsolutePureTime,
                    Nat.add_sub_of_le hle] using hdecoder
                dsimp only [liveMass, reachedGain]
                have hneg := congrArg Neg.neg hbase
                calc
                  _ = -(quittingRootSequencePureTimeTerminalValue reward roots
                          observer (some sourceTime) 0 -
                        quittingRootSequencePureTimeTerminalValue reward roots
                          observer (some receivingTime) 0) := by ring
                  _ = -(quittingOpponentSurvivalWeight roots observer 0
                          sourceTime *
                        (quittingFixedOpponentsQuitValue reward roots observer
                            sourceTime -
                          quittingRootSequenceRelativePureTimeTerminalValue
                            reward roots observer sourceTime delay)) := hneg
                  _ = _ := by ring
              have hpaidBound : liveMass * reachedGain ≤
                  2 * quittingRewardBound reward * liveMass := by
                apply paidFirstDisagreement_bound reward receiving observer
                  sourceTime delay liveMass reachedGain rfl
                exact Or.inr rfl
              let row : QuittingPaidFirstDisagreementRow reward receiving observer gain := {
                sourceWitness := some sourceTime
                receivingWitness := some receivingTime
                start := sourceTime
                later := delay
                later_strict := by
                  simpa [delay, IsQuittingStrictlyLaterDelay,
                    Nat.sub_pos_iff_lt] using hreverse
                receivingEarlier := false
                chronology := by
                  simp [delay, quittingAbsolutePureTime,
                    Nat.add_sub_of_le hle]
                liveMass := liveMass
                liveMass_eq := rfl
                reachedGain := reachedGain
                reachedGain_eq := by dsimp [reachedGain, roots]
                edge_identity := by
                  simpa [roots, quittingPureTimeDeviationPayoff] using hdecoder'
                gain_le_paid := by exact hedge.trans_eq hdecoder'
                gain_le_liveMass := hedge.trans_eq hdecoder' |>.trans hpaidBound
              }
              exact ⟨row, rfl, rfl⟩

/-- The profitable receiving edge of an oriented witness-switch certificate
supplies the ordered, data-bearing first-disagreement row. -/
theorem QuittingPureTimeWitnessSwitchCertificate.exists_paidFirstDisagreementRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {charge eta : ℝ}
    (certificate : QuittingPureTimeWitnessSwitchCertificate reward source
      receiving observer charge eta)
    (hpositive : 0 < charge + eta) :
    ∃ row : QuittingPaidFirstDisagreementRow reward receiving observer
        (charge + eta),
      row.sourceWitness = certificate.switch.sourceWitness ∧
        row.receivingWitness = certificate.switch.receivingWitness := by
  exact exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
    reward receiving observer certificate.switch.sourceWitness
      certificate.switch.receivingWitness (charge + eta) hpositive
        certificate.switch.receiving_gain

end GameTheory
