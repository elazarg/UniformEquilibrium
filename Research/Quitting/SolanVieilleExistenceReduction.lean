/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SolanVieillePeriodicSelection
import UniformEquilibrium.Quitting.Classification.SoloExitPreferenceExistence

/-!
# Reduction of the Solan–Vieille existence law to sequence extraction

The proof of the quitting existence theorem of Solan and Vieille, *Quitting
games*, Math. Oper. Res. 26 (2001), Theorem 1.2, factors here into three
layers.  The first two are proved in this development:

* the one-shot perturbation
  `exists_quittingPerfectAbsorbingRow_of_soloExitPreference`
  (the source's Proposition 2.2); and
* the self-consistent perfect row sequence
  `exists_quittingPerfectAbsorbingRootSequence_of_soloExitPreference`
  (the source's Proposition 2.3).

The remaining layer is the source's Proposition 2.4, its block-decomposition
core: from a row sequence with a per-stage absorption floor whose every row
is one-stage `ε`-perfect against its own continuation, extract a profile that
is a terminal approximate equilibrium — either the sequence itself or a
stationary repair.  `QuittingPerfectSequenceExtraction` names exactly that
open step, at a hypothesis strength the second layer delivers.

`quittingCappedJointExitUniformεExistence_of_perfectSequenceExtraction`
closes the chain: granting the extraction step for every table with unit
solo exit and capped joint exit, the open proposition
`QuittingCappedJointExitUniformεExistence` holds.  The bridge from terminal
approximate equilibria at every error to uniform `ε`-equilibria is the
notion-alignment waist
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
together with the easy direction of
`quittingGame_exists_uniformEquilibriumPayoff_iff_uniformεEquilibrium_all_errors`.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Open step: perfect-sequence extraction** (Solan and Vieille, *Quitting
games*, Math. Oper. Res. 26 (2001), Proposition 2.4).  For every target
tolerance there is a row tolerance such that any root sequence with a
per-stage absorption floor, each of whose rows is one-stage perfect at the
row tolerance against the sequence's own next-stage continuation vector,
yields some profile that is a terminal approximate equilibrium at the target
tolerance.

The source proves this with a block decomposition of time: either some
player's opponents are inactive over long stretches, and a stationary repair
with that player as the sole quitter is an approximate equilibrium, or every
player faces recurrent opponent activity and the sequence itself caps every
deviation.  The extracted profile is existentially quantified, so both
branches land in this statement. -/
def QuittingPerfectSequenceExtraction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ εout : ℝ, 0 < εout → ∃ εrow : ℝ, 0 < εrow ∧
    ∀ (roots : ℕ → ι → PMF Bool) (δ : ℝ), 0 < δ →
      (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) →
      (∀ n, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (n + 1)) (roots n)
        εrow) →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) εout profile

/-- Granting perfect-sequence extraction on every table with unit solo exit
and capped joint exit, terminal approximate equilibria exist at every
positive error: the two proved layers supply the extraction step's row
sequence. -/
theorem quittingGame_terminalNash_all_errors_of_perfectSequenceExtraction
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward)
    (hextract : QuittingPerfectSequenceExtraction reward) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  obtain ⟨εrow, hεrow0, hεrow⟩ := hextract ε hε
  obtain ⟨roots, δ, hδ0, habsorb, hperfect⟩ :=
    exists_quittingPerfectAbsorbingRootSequence_of_soloExitPreference
      hunit hcap hεrow0
  exact hεrow roots δ hδ0 habsorb hperfect

/-- **Conditional form of Solan–Vieille Theorem 1.2.**  Granting the
perfect-sequence extraction step on every table with unit solo exit and
capped joint exit, the existence law
`QuittingCappedJointExitUniformεExistence` holds: every such table has a
uniform `ε`-equilibrium at every positive `ε`.

With no players every profile is vacuously a uniform equilibrium; with at
least one player the two proved layers feed the extraction step, terminal
approximate equilibria exist at every error, and the notion-alignment waist
returns uniform `ε`-equilibria at every error. -/
theorem quittingCappedJointExitUniformεExistence_of_perfectSequenceExtraction
    (hextract : ∀ reward : {S : Finset ι // S.Nonempty} → Payoff ι,
      QuittingUnitSoloExit reward → QuittingCappedJointExit reward →
        QuittingPerfectSequenceExtraction reward) :
    QuittingCappedJointExitUniformεExistence ι := by
  intro reward hunit hcap ε hε
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      refine ⟨fun who => (hempty.elim who), 0, fun horizon _ => ?_⟩
      intro who
      exact (hempty.elim who)
  | inr hnonempty =>
      have hterminal := quittingGame_terminalNash_all_errors_of_perfectSequenceExtraction
        hunit hcap (hextract reward hunit hcap)
      obtain ⟨payoff, hpayoff⟩ :=
        (quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
          reward).mpr hterminal
      obtain ⟨profile, threshold, hprofile⟩ := hpayoff ε hε
      exact ⟨profile, threshold,
        fun horizon hhorizon => (hprofile horizon hhorizon).1⟩

end GameTheory
