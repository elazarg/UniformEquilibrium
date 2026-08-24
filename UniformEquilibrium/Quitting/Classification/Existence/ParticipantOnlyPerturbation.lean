/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Finset.InsertExtremum
import UniformEquilibrium.Quitting.Classification.Existence.ParticipantOnlyStationary
import UniformEquilibrium.Quitting.PayoffProcess.TailStepSelector
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Passive-reward magnitude and participant-only approximation

The passive magnitude is the largest absolute reward paid to an absent player,
clamped below by zero.  The clamp makes the definition total when there are no
passive coordinates, including for an empty player type.  Projecting away all
passive coordinates gives a participant-only table.  Its exact stationary
terminal Nash profile remains terminal `2 * delta`-Nash for the original table
by the generic reward-perturbation theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The largest magnitude of a reward paid to a player absent from the
terminal coalition, with zero inserted before taking the finite maximum. -/
def quittingPassiveMagnitude
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  Math.Finset.insertMax 0 (Finset.univ ×ˢ Finset.univ) fun entry =>
    if entry.2 ∉ entry.1.1 then |reward entry.1 entry.2| else 0

/-- The passive magnitude is nonnegative, even when its coordinate family is
empty. -/
theorem quittingPassiveMagnitude_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingPassiveMagnitude reward :=
  Math.Finset.base_le_insertMax 0 _ _

/-- Every passive reward coordinate is bounded by the passive magnitude. -/
theorem abs_reward_le_quittingPassiveMagnitude
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι)
    (habsent : who ∉ terminal.1) :
    |reward terminal who| ≤ quittingPassiveMagnitude reward := by
  have hbound := Math.Finset.le_insertMax
    (indices := ((Finset.univ ×ˢ Finset.univ) :
      Finset ({S : Finset ι // S.Nonempty} × ι))) 0
    (fun entry : {S : Finset ι // S.Nonempty} × ι =>
      if entry.2 ∉ entry.1.1 then |reward entry.1 entry.2| else 0)
    (show (terminal, who) ∈
      ((Finset.univ ×ˢ Finset.univ) :
        Finset ({S : Finset ι // S.Nonempty} × ι)) by simp)
  rw [if_pos habsent] at hbound
  simpa only [quittingPassiveMagnitude] using hbound

/-- The participant projection retains rewards of coalition members and
replaces all passive coordinates by zero. -/
def quittingParticipantProjection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who => if who ∈ terminal.1 then reward terminal who else 0

omit [Fintype ι] in
/-- The participant projection is participant-only. -/
theorem isQuittingParticipantOnly_participantProjection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsQuittingParticipantOnly (quittingParticipantProjection reward) := by
  intro terminal who habsent
  simp [quittingParticipantProjection, habsent]

/-- Projection changes every reward coordinate by at most the passive
magnitude. -/
theorem abs_participantProjection_sub_reward_le_passiveMagnitude
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    |quittingParticipantProjection reward terminal who - reward terminal who| ≤
      quittingPassiveMagnitude reward := by
  by_cases hmember : who ∈ terminal.1
  · simp [quittingParticipantProjection, hmember,
      quittingPassiveMagnitude_nonneg reward]
  · simpa [quittingParticipantProjection, hmember, abs_neg] using
      abs_reward_le_quittingPassiveMagnitude reward terminal who hmember

/-- Participant-only tables have passive magnitude exactly zero. -/
theorem quittingPassiveMagnitude_eq_zero_of_participantOnly
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hparticipant : IsQuittingParticipantOnly reward) :
    quittingPassiveMagnitude reward = 0 := by
  apply le_antisymm
  · unfold quittingPassiveMagnitude
    apply Math.Finset.insertMax_le
    · exact le_rfl
    · intro entry _
      by_cases habsent : entry.2 ∉ entry.1.1
      · simp [habsent, hparticipant entry.1 entry.2 habsent]
      · simp [habsent]
  · exact quittingPassiveMagnitude_nonneg reward

/-- Every finite quitting table has a stationary product profile whose full
behavioral terminal exploitability is at most twice its passive magnitude. -/
theorem exists_stationary_isTwoPassiveMagnitudeAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ root : ι → PMF Bool,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (2 * quittingPassiveMagnitude reward)
        (quittingStationaryProfile reward root) := by
  let projected := quittingParticipantProjection reward
  obtain ⟨root, hnash⟩ :=
    exists_stationary_isZeroAsymptoticNash_of_participantOnly projected
      (isQuittingParticipantOnly_participantProjection reward)
  have hstable := IsεAsymptoticNash.of_reward_close projected reward
    (quittingStationaryProfile projected root)
    (quittingPassiveMagnitude_nonneg reward)
    (abs_participantProjection_sub_reward_le_passiveMagnitude reward) hnash
  have hprofile :
      (quittingStationaryProfile projected root :
        (quittingGame reward).BehaviorProfile) =
        quittingStationaryProfile reward root := rfl
  exact ⟨root, by simpa only [hprofile, zero_add] using hstable⟩

/-- A universal terminal exploitability gap cannot exceed twice the passive
reward magnitude. -/
theorem terminalExploitabilityGap_le_two_mul_quittingPassiveMagnitude
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {gap : ℝ}
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    gap ≤ 2 * quittingPassiveMagnitude reward := by
  obtain ⟨root, hnash⟩ :=
    exists_stationary_isTwoPassiveMagnitudeAsymptoticNash reward
  obtain ⟨who, deviation, hgap⟩ :=
    hexploit (quittingStationaryProfile reward root)
  have hcap := hnash who deviation
  linarith

/-- Quantitative passive-reward obstruction: a fixed terminal gap `gap`
requires passive magnitude at least `gap / 2`. -/
theorem half_terminalExploitabilityGap_le_quittingPassiveMagnitude
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {gap : ℝ}
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    gap / 2 ≤ quittingPassiveMagnitude reward := by
  have hgap :=
    terminalExploitabilityGap_le_two_mul_quittingPassiveMagnitude
      reward hexploit
  linarith

end GameTheory
