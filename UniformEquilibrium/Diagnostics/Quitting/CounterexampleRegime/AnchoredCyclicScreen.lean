/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicWindows
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicScreen

/-!
# The anchored cyclic screen for single-quitter periodic schedules

The single-quitter periodic profile of a period `m`, a schedule
`w : Fin m → ι` of designated quitters (repetitions allowed), and a per-phase
quit hazard `hazard : Fin m → ℝ` is `quittingAnchoredCyclicProfile`, and its
exact on-path value is `quittingAnchoredCyclicOnPathValue`
(`UniformEquilibrium/Quitting/Cycles/AnchoredCyclicScreen.lean`).  This module
evaluates that profile against a counterexample regime.

The screen says: in a counterexample regime, for *every* `(m, w, p)`, some
player's response cap beats the on-path value by the full terminal gap.
Contrapositively, exhibiting one schedule whose cap is everywhere at most the
on-path value excludes the table from every counterexample regime
(`isEmpty_of_anchoredCyclicCap_le`), and an anchored cyclic profile that is
exactly asymptotic Nash for the terminal payoff also excludes the regime
(`isEmpty_of_anchoredCyclic_isεAsymptoticNash`).

The last theorem reads the screen against the max-linear response system of
the production module.  Given a solution `S` of `IsAnchoredCyclicResponseSolution`
whose refusal branch is also dominated, a counterexample regime forces some
player to satisfy `S⁰ ≥ U⁰ + γ` (`exists_anchoredCyclicResponse_gain`).  The
refusal hypothesis `hrefusal` is the one step of the bridge not proved here:
the deterministic-stop half is `quittingAnchoredCyclicPhaseStop_le`, and the
refusal half is discharged in
`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/AnchoredCyclicRenewal.lean`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-! ## The screen -/

namespace QuittingCounterexampleRegime

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- **The anchored cyclic screen.**  In a counterexample regime, *every*
period `m`, *every* schedule `w` (repetitions allowed), and *every* hazard
vector leave some player whose exact finite response cap beats the on-path
renewal value by the full terminal gap.  No limit profiles and no `γ / 2`
loss. -/
theorem exists_anchoredCyclicCap_gain
    (regime : QuittingCounterexampleRegime reward)
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who := by
  have hperiodic : ∀ time,
      quittingProfileLiveRoot reward
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) (time + m) =
        quittingProfileLiveRoot reward
          (quittingAnchoredCyclicProfile reward w hazard h0 h1) time := by
    intro time
    unfold quittingAnchoredCyclicProfile
    rw [quittingProfileLiveRoot_cyclicBehaviorProfile]
    exact quittingCyclicRootSequence_add_period _ _ time
  obtain ⟨who, hgain⟩ := regime.exists_periodicCap_gain
    (quittingAnchoredCyclicProfile reward w hazard h0 h1) m hperiodic
  refine ⟨who, ?_⟩
  rw [quittingTerminalPayoff_anchoredCyclicProfile] at hgain
  refine hgain.trans_eq ?_
  unfold quittingAnchoredCyclicResponseCap quittingAnchoredCyclicProfile
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile]

/-- **The contrapositive.**  A table carrying one anchored cyclic schedule
whose exact response cap is everywhere at most the on-path renewal value
carries no counterexample regime at all. -/
theorem isEmpty_of_anchoredCyclicCap_le
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hexact : ∀ who,
      quittingAnchoredCyclicResponseCap reward w hazard h0 h1 who ≤
        quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who) :
    IsEmpty (QuittingCounterexampleRegime reward) := by
  refine ⟨fun regime ↦ ?_⟩
  obtain ⟨who, hgain⟩ := regime.exists_anchoredCyclicCap_gain w hazard h0 h1
  linarith [hexact who, regime.terminalGap_pos]

/-- A table admitting one anchored cyclic profile that is asymptotic Nash at
accuracy zero for the terminal payoff carries no counterexample regime. -/
theorem isEmpty_of_anchoredCyclic_isεAsymptoticNash
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingAnchoredCyclicProfile reward w hazard h0 h1)) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_of_anchoredCyclicCap_le w hazard h0 h1
    (quittingAnchoredCyclicResponseCap_le_onPathValue_of_isεAsymptoticNash reward
      w hazard h0 h1 hnash)

end QuittingCounterexampleRegime

/-- **The screen against the max-linear system.**  Given a solution `S` of
`IsAnchoredCyclicResponseSolution` whose refusal branch is also dominated, a
counterexample regime forces some player to satisfy `S⁰ ≥ U⁰ + γ`.

`hrefusal` is the one step of the bridge that is not proved here: the
deterministic-stop half is `quittingAnchoredCyclicPhaseStop_le`. -/
theorem exists_anchoredCyclicResponse_gain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward)
    {m : ℕ} [NeZero m] (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (S : Fin m → ι → ℝ)
    (hS : IsAnchoredCyclicResponseSolution reward w hazard S)
    (hrefusal : ∀ who,
      quittingPeriodicWindowRefusalValue reward
          (quittingCyclicRootSequence
            (quittingAnchoredCyclicCycle w hazard h0 h1)
            (quittingAnchoredCyclicStart m)) who ≤
        S (quittingAnchoredCyclicStart m) who) :
    ∃ who,
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
          (quittingAnchoredCyclicStart m) who + regime.terminalGap ≤
        S (quittingAnchoredCyclicStart m) who := by
  obtain ⟨who, hgain⟩ := regime.exists_anchoredCyclicCap_gain w hazard h0 h1
  refine ⟨who, hgain.trans ?_⟩
  unfold quittingAnchoredCyclicResponseCap quittingPeriodicWindowBestResponseValue
  refine max_le (hrefusal who) ?_
  unfold quittingPeriodicWindowBestPhaseStop
  refine Finset.sup'_le _ _ fun stop _ ↦ ?_
  exact quittingAnchoredCyclicPhaseStop_le reward w hazard h0 h1 S hS who stop

end GameTheory
