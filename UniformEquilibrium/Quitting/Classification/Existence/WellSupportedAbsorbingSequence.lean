/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Paths.SupportWitnessClockCollapse

/-!
# Well-supported absorbing quitting sequences

The sequential branch in the Simon--Solan--Vieille classification is often
produced first in endpoint form: every action used at a live row is nearly as
good as the other endpoint, and the resulting root sequence absorbs almost
surely.  This file relates that support-witness formulation to branch `S.3`,
whose one-stage predicate compares both pure endpoints with the mixed row
payoff.

Support optimality at tolerance `δ` implies row perfectness at the same
tolerance.  Conversely, row perfectness at tolerance `ε` implies support
optimality at tolerance `2 * ε`.  Hence the two existence branches, which
quantify over every positive tolerance, are equivalent.

This is a semantic adapter, not an equilibrium-to-sequence extraction
theorem.  In particular it does not assume or manufacture the compactness and
purification step needed to obtain such a sequence from arbitrary approximate
equilibria.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Support-local endpoint optimality implies one-stage perfectness at the
same tolerance. -/
theorem quittingRowεPerfect_of_supportApproxNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsupport : IsQuittingRootSupportApproxNash reward tail ε root) :
    QuittingRowεPerfect reward tail root ε := by
  intro who
  have hcontinue0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hquit0 : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinue1 : (root who false).toReal ≤ 1 := by
    linarith [quittingRoot_continueProbability_add_quitProbability root who]
  have hquit1 : (root who true).toReal ≤ 1 := by
    linarith [quittingRoot_continueProbability_add_quitProbability root who]
  have hquitSub := quittingRootQuitPayoff_sub_successorPayoff
    reward tail root who
  have hcontinueSub := quittingRootContinuePayoff_sub_successorPayoff
    reward tail root who
  have hweighted := isQuittingRootEndpointNash_of_supportApproxNash
    reward tail root hε hsupport who
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · intro hused
    have husedReal : 0 < (root who true).toReal :=
      ENNReal.toReal_pos hused (PMF.apply_ne_top _ _)
    have hgap := (hsupport who).1 husedReal
    have hscaled := mul_le_mul_of_nonneg_left hgap hcontinue0
    have hfloor : -ε ≤ (root who false).toReal * (-ε) := by
      nlinarith
    linarith
  · intro hused
    have husedReal : 0 < (root who false).toReal :=
      ENNReal.toReal_pos hused (PMF.apply_ne_top _ _)
    have hgap := (hsupport who).2 husedReal
    have hscaled := mul_le_mul_of_nonneg_left hgap hquit0
    have hcap : (root who true).toReal * ε ≤ ε := by
      nlinarith
    linarith

/-- One-stage perfectness gives support-local endpoint optimality at twice the
tolerance.  The factor two is the triangle inequality through the mixed row
payoff. -/
theorem supportApproxNash_of_quittingRowεPerfect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {ε : ℝ}
    (hperfect : QuittingRowεPerfect reward tail root ε) :
    IsQuittingRootSupportApproxNash reward tail (2 * ε) root := by
  intro who
  obtain ⟨hquit, hcontinue, hsupportQuit, hsupportContinue⟩ := hperfect who
  constructor
  · intro hpositive
    have hused : root who true ≠ 0 := by
      intro hzero
      simp [hzero] at hpositive
    have hlower := hsupportQuit hused
    unfold quittingRootEndpointDifference
    linarith
  · intro hpositive
    have hused : root who false ≠ 0 := by
      intro hzero
      simp [hzero] at hpositive
    have hlower := hsupportContinue hused
    unfold quittingRootEndpointDifference
    linarith

/-- For every positive tolerance there is a completely absorbing root
sequence whose used actions are support-locally optimal against the sequence's
actual continuation values. -/
def QuittingWellSupportedAbsorbingSequenceExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ roots : ℕ → ι → PMF Bool,
    IsCompletelyAbsorbing roots ∧
      IsQuittingRootSequenceSupportApproxNash reward roots δ

/-- A well-supported completely absorbing sequence supplies branch `S.3`. -/
theorem quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hwitness : QuittingWellSupportedAbsorbingSequenceExistence reward) :
    QuittingSequentiallyεPerfectAbsorbingExistence reward := by
  intro ε hε
  obtain ⟨roots, habsorb, hsupport⟩ := hwitness ε hε
  refine ⟨roots, habsorb, fun time => ?_⟩
  exact quittingRowεPerfect_of_supportApproxNash hε.le (hsupport time)

/-- Branch `S.3` supplies a well-supported completely absorbing sequence
after halving the requested tolerance. -/
theorem quittingWellSupportedAbsorbingSequenceExistence_of_sequentiallyPerfect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hbranch : QuittingSequentiallyεPerfectAbsorbingExistence reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  intro δ hδ
  obtain ⟨roots, habsorb, hperfect⟩ := hbranch (δ / 2) (by linarith)
  refine ⟨roots, habsorb, fun time => ?_⟩
  convert supportApproxNash_of_quittingRowεPerfect (hperfect time) using 1
  ring

/-- The support-witness and sequentially-perfect formulations of branch
`S.3` are equivalent when required at every positive tolerance. -/
theorem quittingWellSupportedAbsorbingSequenceExistence_iff_sequentiallyPerfect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ↔
      QuittingSequentiallyεPerfectAbsorbingExistence reward :=
  ⟨quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported,
    quittingWellSupportedAbsorbingSequenceExistence_of_sequentiallyPerfect⟩

/-! ## Selecting one fixed branch from pointwise alternatives -/

/-- The stationary branch at one displayed tolerance. -/
def QuittingStationaryεEquilibriumAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ root : ι → PMF Bool,
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
      (quittingStationaryProfile reward root)

/-- The instant-punishment branch at one displayed tolerance. -/
def QuittingInstantPunishmentεEquilibriumAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (ε : ℝ) : Prop :=
  ∃ (quitter : ι) (root punishRow : ι → PMF Bool),
    root quitter = PMF.pure true ∧
      quittingStationaryUnilateralCap reward punishRow quitter ≤
        quittingPunishmentValue reward quitter + ε ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε
        (quittingOneStagePunishedProfile reward root punishRow)

/-- The well-supported absorbing branch at one displayed tolerance. -/
def QuittingWellSupportedAbsorbingSequenceAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) : Prop :=
  ∃ roots : ℕ → ι → PMF Bool,
    IsCompletelyAbsorbing roots ∧
      IsQuittingRootSequenceSupportApproxNash reward roots δ

/-- Support-local endpoint optimality is monotone in its tolerance. -/
theorem IsQuittingRootSupportApproxNash.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {δ δ' : ℝ}
    (hsupport : IsQuittingRootSupportApproxNash reward tail δ root)
    (hle : δ ≤ δ') :
    IsQuittingRootSupportApproxNash reward tail δ' root := by
  intro who
  constructor
  · intro hpositive
    have hbound := (hsupport who).1 hpositive
    linarith
  · intro hpositive
    have hbound := (hsupport who).2 hpositive
    linarith

/-- A well-supported root sequence remains so when its tolerance is relaxed. -/
theorem IsQuittingRootSequenceSupportApproxNash.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {δ δ' : ℝ}
    (hsupport : IsQuittingRootSequenceSupportApproxNash reward roots δ)
    (hle : δ ≤ δ') :
    IsQuittingRootSequenceSupportApproxNash reward roots δ' :=
  fun stage => (hsupport stage).mono hle

/-- A stationary witness remains a witness when its tolerance is relaxed. -/
theorem QuittingStationaryεEquilibriumAt.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε ε' : ℝ}
    (hwitness : QuittingStationaryεEquilibriumAt reward ε) (hle : ε ≤ ε') :
    QuittingStationaryεEquilibriumAt reward ε' := by
  obtain ⟨root, hnash⟩ := hwitness
  exact ⟨root, StochasticGame.IsεAsymptoticNash.mono hnash hle⟩

/-- An instant-punishment witness remains one when its tolerance is relaxed. -/
theorem QuittingInstantPunishmentεEquilibriumAt.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε ε' : ℝ}
    (hwitness : QuittingInstantPunishmentεEquilibriumAt reward ε)
    (hle : ε ≤ ε') :
    QuittingInstantPunishmentεEquilibriumAt reward ε' := by
  obtain ⟨quitter, root, punishRow, hquitter, hcap, hnash⟩ := hwitness
  refine ⟨quitter, root, punishRow, hquitter, by linarith, hnash.mono hle⟩

/-- A well-supported absorbing witness remains one when its tolerance is
relaxed. -/
theorem QuittingWellSupportedAbsorbingSequenceAt.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ δ' : ℝ}
    (hwitness : QuittingWellSupportedAbsorbingSequenceAt reward δ)
    (hle : δ ≤ δ') :
    QuittingWellSupportedAbsorbingSequenceAt reward δ' := by
  obtain ⟨roots, habsorb, hsupport⟩ := hwitness
  exact ⟨roots, habsorb, hsupport.mono hle⟩

/-- If at every positive scale at least one of the three semantic alternatives
has a witness, then one fixed alternative has witnesses at every positive
scale.  Finiteness of the branch set and monotonicity of each error predicate
are the only ingredients. -/
theorem fixedQuittingBranch_of_pointwiseAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hpointwise : ∀ ε : ℝ, 0 < ε →
      QuittingStationaryεEquilibriumAt reward ε ∨
        QuittingInstantPunishmentεEquilibriumAt reward ε ∨
          QuittingWellSupportedAbsorbingSequenceAt reward ε) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward := by
  classical
  by_cases hstationary : QuittingStationaryεEquilibriumExistence reward
  · exact Or.inl hstationary
  right
  by_cases hinstant : QuittingInstantPunishmentεEquilibriumExistence reward
  · exact Or.inl hinstant
  right
  rw [QuittingStationaryεEquilibriumExistence] at hstationary
  rw [QuittingInstantPunishmentεEquilibriumExistence] at hinstant
  push Not at hstationary hinstant
  obtain ⟨stationaryScale, hstationaryScale, hnoStationary⟩ := hstationary
  obtain ⟨instantScale, hinstantScale, hnoInstant⟩ := hinstant
  intro δ hδ
  let scale := min δ (min stationaryScale instantScale) / 2
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hscaleδ : scale ≤ δ := by
    dsimp only [scale]
    have hmin : min δ (min stationaryScale instantScale) ≤ δ := min_le_left _ _
    have hminPositive : 0 < min δ (min stationaryScale instantScale) := by
      positivity
    linarith
  have hscaleStationary : scale ≤ stationaryScale := by
    dsimp only [scale]
    have hmin : min δ (min stationaryScale instantScale) ≤ stationaryScale :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hminPositive : 0 < min δ (min stationaryScale instantScale) := by
      positivity
    linarith
  have hscaleInstant : scale ≤ instantScale := by
    dsimp only [scale]
    have hmin : min δ (min stationaryScale instantScale) ≤ instantScale :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hminPositive : 0 < min δ (min stationaryScale instantScale) := by
      positivity
    linarith
  rcases hpointwise scale hscale with hsmall | hsmall | hsmall
  · obtain ⟨root, hnash⟩ := hsmall.mono hscaleStationary
    exact False.elim (hnoStationary root hnash)
  · obtain ⟨quitter, root, punishRow, hquitter, hcap, hnash⟩ :=
      hsmall.mono hscaleInstant
    exact False.elim (hnoInstant quitter root punishRow hquitter hcap hnash)
  · exact hsmall.mono hscaleδ

end GameTheory
