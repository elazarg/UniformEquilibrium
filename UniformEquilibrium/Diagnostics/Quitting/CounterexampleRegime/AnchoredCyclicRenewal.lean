/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicRenewal

/-!
# Discharging the anchored cyclic screen's refusal hypothesis

`exists_anchoredCyclicResponse_gain`
(`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/AnchoredCyclicScreen.lean`)
carries an explicit refusal hypothesis `hrefusal`.  This module discharges
that hypothesis against the max-linear response system, using the refusal
identity and response-cap bounds of
`UniformEquilibrium/Quitting/Cycles/AnchoredCyclicRenewal.lean`.

`exists_anchoredCyclicResponse_gain_of_refusalOnPathValue_le` reads
`hrefusal` as a comparison between the zeroed on-path value and the candidate
solution, via `quittingPeriodicWindowRefusalValue_anchoredCyclic`.  The
remaining three theorems discharge that comparison outright from a solution
of the max-linear system:
`exists_anchoredCyclicResponse_gain_of_degenerate_nonneg` needs only
nonnegativity of the solution for a player owning every positive-hazard
phase, `exists_anchoredCyclicResponse_gain_of_exists_spectatorHazard` removes
that residual under the spectator condition "every player is a spectator at
some phase carrying positive hazard", and its contrapositive
`isEmpty_of_anchoredCyclicResponseSolution_le` excludes every counterexample
regime from a schedule whose response system has a solution no larger than
the on-path value at the starting phase.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- **The screen against the max-linear system, with its refusal branch read
as a zeroed on-path value.**  The hypothesis compares the solution `S` with the
on-path value of the schedule whose phases owned by the deviator carry hazard
zero, which the renewal closed form `quittingAnchoredCyclicOnPathValue_eq_div`
evaluates as a ratio of finite sums. -/
theorem exists_anchoredCyclicResponse_gain_of_refusalOnPathValue_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hzeroed : ∀ who,
      quittingAnchoredCyclicOnPathValue reward w
          (quittingAnchoredCyclicRefusalHazard w hazard who)
          (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
          (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)
          (quittingAnchoredCyclicStart m) who ≤
        S (quittingAnchoredCyclicStart m) who) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + witness.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who :=
  exists_anchoredCyclicResponse_gain witness w hazard h0 h1 S hS fun who ↦
    (quittingPeriodicWindowRefusalValue_anchoredCyclic reward w hazard h0 h1
      (quittingAnchoredCyclicStart m) who).trans_le (hzeroed who)

/-- **The screen against the max-linear system with no refusal hypothesis.**
The only residual is nonnegativity of the solution for the players who own
every positive-hazard phase. -/
theorem exists_anchoredCyclicResponse_gain_of_degenerate_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hdegenerate : ∀ who, (∀ k, w k ≠ who → hazard k = 0) →
      0 ≤ S (quittingAnchoredCyclicStart m) who) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + witness.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨who, hgain⟩ := witness.exists_anchoredCyclicCap_gain w hazard h0 h1
  exact ⟨who, hgain.trans (quittingAnchoredCyclicResponseCap_le_of_response w
    hazard h0 h1 S hS who (hdegenerate who))⟩

/-- **The screen against the max-linear system, unconditionally.**  When every
player is a spectator at some phase carrying positive hazard, the refusal
hypothesis of `exists_anchoredCyclicResponse_gain` is discharged outright. -/
theorem exists_anchoredCyclicResponse_gain_of_exists_spectatorHazard
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward) [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hspectator : ∀ who, ∃ k, w k ≠ who ∧ 0 < hazard k) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + witness.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨who, hgain⟩ := witness.exists_anchoredCyclicCap_gain w hazard h0 h1
  exact ⟨who, hgain.trans
    (quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard w hazard
      h0 h1 S hS who (hspectator who))⟩

/-- **The screen's contrapositive against the max-linear system.**  A schedule
whose response system has a solution no larger than the on-path value at the
starting phase excludes every terminal exploitability witness.  Every input is finite:
the max recursion, the spectator condition, and one comparison per player. -/
theorem isEmpty_of_anchoredCyclicResponseSolution_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} [NeZero m]
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hspectator : ∀ who, ∃ k, w k ≠ who ∧ 0 < hazard k)
    (hle : ∀ who, S (quittingAnchoredCyclicStart m) who ≤
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (quittingAnchoredCyclicStart m) who) :
    IsEmpty (QuittingTerminalExploitabilityWitness reward) :=
  QuittingTerminalExploitabilityWitness.isEmpty_of_anchoredCyclicCap_le w hazard h0 h1
    fun who ↦
      (quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard w hazard
        h0 h1 S hS who (hspectator who)).trans (hle who)

end GameTheory
