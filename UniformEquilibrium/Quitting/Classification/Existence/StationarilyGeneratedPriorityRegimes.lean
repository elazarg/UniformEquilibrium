/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.FixedHorizonPositiveJointSource
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedWitnessRegimes

/-!
# Priority regimes for diffuse stationarily generated witnesses

The usual witness-regime theorem sends the fixed-horizon positive-live case
to an unclassified uniform-payoff witness.  Retaining the source data gives a
sharper classification boundary: vanishing live mass yields S.2, fixed
horizon with positive live mass yields S.2 or a positive-reach no-sure-exit
endpoint residual, and only the positive-live divergent-horizon regime
remains for the exceptional-owner analysis.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- **Source-prioritized stationarily generated regimes.**  A diffuse
stationarily generated family yields S.2, the literal positive-joint
no-sure-exit endpoint residual, or an actual positive-live source with
divergent prefix horizons.  In particular, fixed horizon is no longer hidden
inside a generic uniform-payoff conclusion. -/
theorem
    instant_or_positiveJointNoSureExitResidual_or_positiveLive_divergentHorizon
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      Nonempty (QuittingPositiveJointPrefixReachNoSureExitResidual reward) ∨
        ∃ (family : QuittingDiffuseStationaryPrefixFamily reward)
            (subsequence : ℕ → ℕ) (punished : iota) (liveLimit : ℝ),
          StrictMono subsequence ∧
            (∀ n, family.punished (subsequence n) = punished) ∧
            0 < liveLimit ∧
            Tendsto
              (fun n ↦ quittingStationaryContinueMass
                (family.root (subsequence n))) atTop (nhds liveLimit) ∧
            Tendsto (fun n ↦ family.horizon (subsequence n)) atTop atTop := by
  classical
  let family := Classical.choice
    (exists_quittingDiffuseStationaryPrefixFamily hgenerated)
  obtain ⟨punished, playerSubsequence, hplayerSubsequence, hpunished⟩ :=
    exists_fixedPlayer_strictMono_subsequence family.punished
  obtain ⟨horizonSubsequence, hhorizonSubsequence, hhorizonNormal⟩ :=
    Math.PureTimeWitnessNormalForm.exists_strictMono_hasNormalForm
      (fun n ↦ some (family.horizon (playerSubsequence n)))
  let firstSubsequence := playerSubsequence ∘ horizonSubsequence
  have hfirstSubsequence : StrictMono firstSubsequence :=
    hplayerSubsequence.comp hhorizonSubsequence
  have hpunishedFirst : ∀ n,
      family.punished (firstSubsequence n) = punished :=
    fun n ↦ hpunished (horizonSubsequence n)
  have hhorizonFirst : HasFixedOrDivergentStationaryPrefixHorizon
      (fun n ↦ family.horizon (firstSubsequence n)) := by
    rcases hhorizonNormal with
      ⟨fixed, hfixed⟩ | hnone | ⟨values, hvalues, heq⟩
    · exact Or.inl ⟨fixed, fun n ↦ Option.some.inj (hfixed n)⟩
    · exact False.elim (Option.some_ne_none _ (hnone 0))
    · exact Or.inr (hvalues.congr' (Filter.Eventually.of_forall fun n ↦ by
        exact Option.some.inj (heq n).symm))
  let liveMass : ℕ → ℝ := fun n ↦
    quittingStationaryContinueMass (family.root (firstSubsequence n))
  have hliveMem : ∀ n, liveMass n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact ⟨quittingStationaryContinueMass_nonneg _,
      quittingStationaryContinueMass_le_one _⟩
  obtain ⟨liveLimit, hliveLimitMem, liveSubsequence, hliveSubsequence,
      hliveLimit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq hliveMem
  let subsequence := firstSubsequence ∘ liveSubsequence
  have hsubsequence : StrictMono subsequence :=
    hfirstSubsequence.comp hliveSubsequence
  have hpunishedFinal : ∀ n,
      family.punished (subsequence n) = punished :=
    fun n ↦ hpunishedFirst (liveSubsequence n)
  have hhorizonFinal : HasFixedOrDivergentStationaryPrefixHorizon
      (fun n ↦ family.horizon (subsequence n)) := by
    simpa [subsequence, Function.comp_def] using
      hhorizonFirst.comp_of_tendsto_atTop hliveSubsequence.tendsto_atTop
  have hliveFinal : Tendsto
      (fun n ↦ quittingStationaryContinueMass
        (family.root (subsequence n))) atTop (nhds liveLimit) := by
    simpa [liveMass, subsequence, Function.comp_def] using hliveLimit
  rcases eq_or_lt_of_le hliveLimitMem.1 with hliveZero | hlivePositive
  · left
    apply quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero
      family subsequence hsubsequence
    simpa only [hliveZero] using hliveFinal
  · rcases hhorizonFinal with
      ⟨fixedHorizon, hhorizonFixed⟩ | hhorizonDivergent
    · have hliveEventually : ∀ᶠ n in atTop,
          liveLimit / 2 ≤ quittingStationaryContinueMass
            (family.root (subsequence n)) := by
        have hhalf : liveLimit / 2 < liveLimit := by linarith
        have hstrict := hliveFinal.eventually (Ioi_mem_nhds hhalf)
        filter_upwards [hstrict] with n hn
        exact hn.le
      obtain ⟨start, hstart⟩ := eventually_atTop.1 hliveEventually
      let selected : ℕ → ℕ := fun n ↦ subsequence (start + n)
      have hselected : StrictMono selected := by
        apply hsubsequence.comp
        intro first second hlt
        exact Nat.add_lt_add_left hlt start
      rcases instantPunishment_or_noSureExitResidual_of_fixedHorizon_liveFloor
          family selected fixedHorizon (liveLimit / 2) hselected
          (fun n ↦ hhorizonFixed (start + n)) (by linarith)
          (fun n ↦ hstart (start + n) (Nat.le_add_right start n)) with
        hinstant | hresidual
      · exact Or.inl hinstant
      · exact Or.inr (Or.inl hresidual)
    · exact Or.inr (Or.inr ⟨family, subsequence, punished, liveLimit,
        hsubsequence, hpunishedFinal, hlivePositive, hliveFinal,
        hhorizonDivergent⟩)

end GameTheory
