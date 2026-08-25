/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointPrefixReachEndpoint

/-!
# Positive punishment reach at fixed stationary-prefix horizon

The fixed-horizon, uniformly positive-live regime of a diffuse stationary-
prefix family has a positive lower bound on survival through the whole
prefix.  Compactness therefore produces an actual positive-joint-reach
source.  This routes the fixed-horizon regime to the existing S.2 endpoint
consumer instead of stopping at an unclassified uniform-payoff witness.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A fixed prefix horizon and a uniform positive one-row live floor produce
an actual source whose punishment suffix retains positive limiting reach. -/
theorem nonempty_positiveJointPrefixReachSource_of_fixedHorizon_liveFloor
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (horizon : ℕ) (liveFloor : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hhorizon : ∀ n, family.horizon (subsequence n) = horizon)
    (hliveFloor : 0 < liveFloor)
    (hlive : ∀ n, liveFloor ≤
      quittingStationaryContinueMass (family.root (subsequence n))) :
    Nonempty (QuittingPositiveJointPrefixReachSource reward) := by
  have hjointMem : ∀ n,
      family.prefixJointSurvival (subsequence n) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact family.prefixJointSurvival_mem_Icc _
  obtain ⟨jointLimit, _hjointLimitMem, selected, hselected, hjointLimit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq hjointMem
  let chosen := subsequence ∘ selected
  have hchosen : StrictMono chosen := hsubsequence.comp hselected
  have hjointChosen : Tendsto
      (fun n ↦ family.prefixJointSurvival (chosen n))
      atTop (nhds jointLimit) := by
    simpa [chosen, Function.comp_def] using hjointLimit
  have hlower : ∀ n, liveFloor ^ (horizon + 1) ≤
      family.prefixJointSurvival (chosen n) := by
    intro n
    unfold QuittingDiffuseStationaryPrefixFamily.prefixJointSurvival
    rw [quittingJointSurvivalWeight_const]
    change liveFloor ^ (horizon + 1) ≤
      quittingStationaryContinueMass
          (family.root (subsequence (selected n))) ^
        (family.horizon (subsequence (selected n)) + 1)
    rw [hhorizon (selected n)]
    exact pow_le_pow_left₀ hliveFloor.le (hlive (selected n)) _
  have hjointLower : liveFloor ^ (horizon + 1) ≤ jointLimit :=
    ge_of_tendsto hjointChosen (Filter.Eventually.of_forall hlower)
  have hjointPositive : 0 < jointLimit :=
    (pow_pos hliveFloor (horizon + 1)).trans_le hjointLower
  exact ⟨⟨family, chosen, jointLimit, hchosen, hjointPositive,
    hjointChosen⟩⟩

/-- Consequently the fixed-horizon positive-live regime either yields the
instant-punishment branch S.2 or reaches the already isolated no-sure-exit
punishment-endpoint residual. -/
theorem instantPunishment_or_noSureExitResidual_of_fixedHorizon_liveFloor
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (family : QuittingDiffuseStationaryPrefixFamily reward)
    (subsequence : ℕ → ℕ) (horizon : ℕ) (liveFloor : ℝ)
    (hsubsequence : StrictMono subsequence)
    (hhorizon : ∀ n, family.horizon (subsequence n) = horizon)
    (hliveFloor : 0 < liveFloor)
    (hlive : ∀ n, liveFloor ≤
      quittingStationaryContinueMass (family.root (subsequence n))) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      Nonempty (QuittingPositiveJointPrefixReachNoSureExitResidual reward) := by
  obtain ⟨source⟩ :=
    nonempty_positiveJointPrefixReachSource_of_fixedHorizon_liveFloor
      family subsequence horizon liveFloor hsubsequence hhorizon
        hliveFloor hlive
  exact source.instantPunishment_or_noSureExitResidual

end GameTheory
