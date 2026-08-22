/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Quitting.Paths.SurvivalWeightedSuffixRegret

/-!
# Reached-history consumers for pure-time witness switches

An oriented cap witness switch gives two deterministic quit times whose payoff
ordering reverses between two literal profiles.  The receiving-profile edge is
already a legal unilateral comparison, but its strategic content is clearer at
the first date at which the two pure plans disagree.

This file decodes every positive pure-time payoff difference into one literal
reached Quit-versus-Continue comparison, weighted by the opponents' actual
survival to that date.  The comparison remains on the supplied receiving
profile.  No source/target substitution, best-response attainment, or
chronological reset-cube realization is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A relative pure-time plan is strictly later than the reached date.  `Never`
is treated as later than every finite date. -/
def IsQuittingStrictlyLaterDelay : Option ℕ → Prop
  | none => True
  | some delay => 0 < delay

/-- One literal first-disagreement comparison on an actual quitting profile.

At `start`, one plan Quits immediately and the other waits for the positive
relative delay `later` (or Never).  The disjunction records which action is
better.  The gain is measured in source units: reached gain multiplied by the
opponents' actual survival to `start`. -/
def HasQuittingPureTimeFirstDisagreementGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (lower : ℝ) : Prop :=
  ∃ start : ℕ, ∃ later : Option ℕ,
    IsQuittingStrictlyLaterDelay later ∧
      (lower ≤
          quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 start *
            (quittingFixedOpponentsQuitValue reward
                (quittingProfileLiveRoot reward profile) who start -
              quittingRootSequenceRelativePureTimeTerminalValue reward
                (quittingProfileLiveRoot reward profile) who start later) ∨
        lower ≤
          quittingOpponentSurvivalWeight
              (quittingProfileLiveRoot reward profile) who 0 start *
            (quittingRootSequenceRelativePureTimeTerminalValue reward
                (quittingProfileLiveRoot reward profile) who start later -
              quittingFixedOpponentsQuitValue reward
                (quittingProfileLiveRoot reward profile) who start))

/-- Every strictly positive payoff difference between two deterministic quit
times is a literal reached Quit-versus-Continue comparison at their first
disagreement.  Both finite times and `Never` are covered. -/
theorem hasQuittingPureTimeFirstDisagreementGain_of_pureTimePayoff_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (better worse : Option ℕ) (lower : ℝ)
    (hlower : 0 < lower)
    (hgain : lower ≤
      quittingPureTimeDeviationPayoff reward profile who better -
        quittingPureTimeDeviationPayoff reward profile who worse) :
    HasQuittingPureTimeFirstDisagreementGain reward profile who lower := by
  rw [quittingPureTimeDeviationPayoff,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingPureTimeDeviationPayoff,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at hgain
  unfold HasQuittingPureTimeFirstDisagreementGain
  cases better with
  | none =>
      cases worse with
      | none =>
          simp at hgain
          linarith
      | some stop =>
          refine ⟨stop, none, trivial, Or.inr ?_⟩
          have hdecoder :=
            quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
              reward (quittingProfileLiveRoot reward profile) who stop none
          calc
            lower ≤
                quittingRootSequencePureTimeTerminalValue reward
                    (quittingProfileLiveRoot reward profile) who none 0 -
                  quittingRootSequencePureTimeTerminalValue reward
                    (quittingProfileLiveRoot reward profile) who (some stop) 0 :=
              hgain
            _ = -(
                quittingRootSequencePureTimeTerminalValue reward
                    (quittingProfileLiveRoot reward profile) who (some stop) 0 -
                  quittingRootSequencePureTimeTerminalValue reward
                    (quittingProfileLiveRoot reward profile) who none 0) := by
              ring
            _ = -(
                quittingOpponentSurvivalWeight
                    (quittingProfileLiveRoot reward profile) who 0 stop *
                  (quittingFixedOpponentsQuitValue reward
                      (quittingProfileLiveRoot reward profile) who stop -
                    quittingRootSequenceRelativePureTimeTerminalValue reward
                      (quittingProfileLiveRoot reward profile) who stop none)) := by
              rw [hdecoder]
            _ = quittingOpponentSurvivalWeight
                    (quittingProfileLiveRoot reward profile) who 0 stop *
                  (quittingRootSequenceRelativePureTimeTerminalValue reward
                      (quittingProfileLiveRoot reward profile) who stop none -
                    quittingFixedOpponentsQuitValue reward
                      (quittingProfileLiveRoot reward profile) who stop) := by
              ring
  | some betterTime =>
      cases worse with
      | none =>
          refine ⟨betterTime, none, trivial, Or.inl ?_⟩
          have hdecoder :=
            quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
              reward (quittingProfileLiveRoot reward profile) who betterTime none
          exact hgain.trans_eq hdecoder
      | some worseTime =>
          by_cases hbefore : betterTime < worseTime
          · have hle : betterTime ≤ worseTime := Nat.le_of_lt hbefore
            refine ⟨betterTime, some (worseTime - betterTime), ?_, Or.inl ?_⟩
            · simpa [IsQuittingStrictlyLaterDelay, Nat.sub_pos_iff_lt] using hbefore
            · have hdecoder :=
                quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
                  reward (quittingProfileLiveRoot reward profile) who betterTime
                    (some (worseTime - betterTime))
              calc
                lower ≤
                    quittingRootSequencePureTimeTerminalValue reward
                        (quittingProfileLiveRoot reward profile) who
                        (some betterTime) 0 -
                      quittingRootSequencePureTimeTerminalValue reward
                        (quittingProfileLiveRoot reward profile) who
                        (some worseTime) 0 := hgain
                _ = quittingOpponentSurvivalWeight
                        (quittingProfileLiveRoot reward profile) who 0 betterTime *
                      (quittingFixedOpponentsQuitValue reward
                          (quittingProfileLiveRoot reward profile) who betterTime -
                        quittingRootSequenceRelativePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who betterTime
                            (some (worseTime - betterTime))) := by
                  simpa [quittingAbsolutePureTime, Nat.add_sub_of_le hle] using
                    hdecoder
          · by_cases heq : betterTime = worseTime
            · subst worseTime
              simp at hgain
              linarith
            · have hreverse : worseTime < betterTime := by omega
              have hle : worseTime ≤ betterTime := Nat.le_of_lt hreverse
              refine ⟨worseTime, some (betterTime - worseTime), ?_, Or.inr ?_⟩
              · simpa [IsQuittingStrictlyLaterDelay, Nat.sub_pos_iff_lt] using
                  hreverse
              · have hdecoder :=
                  quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul
                    reward (quittingProfileLiveRoot reward profile) who worseTime
                      (some (betterTime - worseTime))
                have hdecoder' :
                    quittingRootSequencePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who
                          (some worseTime) 0 -
                        quittingRootSequencePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who
                          (some betterTime) 0 =
                      quittingOpponentSurvivalWeight
                          (quittingProfileLiveRoot reward profile) who 0 worseTime *
                        (quittingFixedOpponentsQuitValue reward
                            (quittingProfileLiveRoot reward profile) who worseTime -
                          quittingRootSequenceRelativePureTimeTerminalValue reward
                            (quittingProfileLiveRoot reward profile) who worseTime
                              (some (betterTime - worseTime))) := by
                  simpa [quittingAbsolutePureTime, Nat.add_sub_of_le hle] using
                    hdecoder
                calc
                  lower ≤
                      quittingRootSequencePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who
                          (some betterTime) 0 -
                        quittingRootSequencePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who
                          (some worseTime) 0 := hgain
                  _ = -(
                      quittingRootSequencePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who
                          (some worseTime) 0 -
                        quittingRootSequencePureTimeTerminalValue reward
                          (quittingProfileLiveRoot reward profile) who
                          (some betterTime) 0) := by ring
                  _ = -(
                      quittingOpponentSurvivalWeight
                          (quittingProfileLiveRoot reward profile) who 0 worseTime *
                        (quittingFixedOpponentsQuitValue reward
                            (quittingProfileLiveRoot reward profile) who worseTime -
                          quittingRootSequenceRelativePureTimeTerminalValue reward
                            (quittingProfileLiveRoot reward profile) who worseTime
                              (some (betterTime - worseTime)))) := by
                    rw [hdecoder']
                  _ = quittingOpponentSurvivalWeight
                          (quittingProfileLiveRoot reward profile) who 0 worseTime *
                        (quittingRootSequenceRelativePureTimeTerminalValue reward
                            (quittingProfileLiveRoot reward profile) who worseTime
                              (some (betterTime - worseTime)) -
                          quittingFixedOpponentsQuitValue reward
                            (quittingProfileLiveRoot reward profile) who
                              worseTime) := by ring

/-- The profitable receiving edge retained by an oriented witness-switch
certificate lands directly in the reached first-disagreement consumer. -/
theorem QuittingPureTimeWitnessSwitchCertificate.hasReceivingFirstDisagreementGain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {charge eta : ℝ}
    (certificate : QuittingPureTimeWitnessSwitchCertificate reward source
      receiving observer charge eta)
    (hpositive : 0 < charge + eta) :
    HasQuittingPureTimeFirstDisagreementGain reward receiving observer
      (charge + eta) := by
  exact hasQuittingPureTimeFirstDisagreementGain_of_pureTimePayoff_sub
    reward receiving observer certificate.switch.receivingWitness
      certificate.switch.sourceWitness (charge + eta) hpositive
        certificate.switch.receiving_gain

end GameTheory
