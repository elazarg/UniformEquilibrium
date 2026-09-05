/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.JumpFlowClosure
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Root.FiniteWordSurvivalSeams
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCarrierBridge

/-! # Finite compatible words of exact jumps and proper singleton flows -/

noncomputable section

namespace GameTheory

open Math.Probability
open IdealSingletonBlockApproximation
open IdealSingletonCarrierBridge
open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- A typed finite word, oriented from its source toward its terminal tail.
Every constructor retains the witness needed by its corresponding executable
one-step closure theorem. -/
inductive CompatibleFiniteJumpFlowWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Payoff ι → Payoff ι → Type
  | refl (tail : Payoff ι) : CompatibleFiniteJumpFlowWord reward tail tail
  | jump (source next tail : Payoff ι) (root : ι → PMF Bool)
      (hsource : source = quittingRootSuccessorPayoff reward next root)
      (hnash : IsεQuittingRootNash reward next 0 root)
      (rest : CompatibleFiniteJumpFlowWord reward next tail) :
      CompatibleFiniteJumpFlowWord reward source tail
  | flow (source next tail : Payoff ι) (owner : ι) (p : ℝ)
      (hp : p ∈ Set.Ioo (0 : ℝ) 1)
      (harc : source = quittingSingletonArcPayoff p
        (quittingSoloReward reward owner) next)
      (hactive : source owner = quittingSoloReward reward owner owner)
      (hsourceViable : QuittingEssentialAPSViable reward source)
      (hnextViable : QuittingEssentialAPSViable reward next)
      (rest : CompatibleFiniteJumpFlowWord reward next tail) :
      CompatibleFiniteJumpFlowWord reward source tail

/-- Every supplied finite ordering of exact jumps and proper viable singleton
flows transports a uniform-payoff terminal tail to its fixed source target. -/
theorem CompatibleFiniteJumpFlowWord.isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {source tail : Payoff ι}
    (word : CompatibleFiniteJumpFlowWord reward source tail)
    (htail : (quittingGame reward).IsUniformEquilibriumPayoff none tail) :
    (quittingGame reward).IsUniformEquilibriumPayoff none source := by
  induction word with
  | refl => exact htail
  | jump source next tail root hsource hnash rest ih =>
      rw [hsource]
      exact isUniformEquilibriumPayoff_rootSuccessor_of_isZeroRootNash
        reward next root (ih htail) hnash
  | flow source next tail owner p hp harc hactive hsource hnext rest ih =>
      exact isUniformEquilibriumPayoff_singletonArc_of_viable_proper
        reward owner p source next hp harc hactive hsource hnext (ih htail)

/-! ## Executable quantitative proper-singleton block -/

/-- Prefix an actual tail profile by `steps` copies of one singleton-hazard
row. -/
def repeatedSingletonProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    ℕ → (quittingGame reward).BehaviorProfile →
      (quittingGame reward).BehaviorProfile
  | 0, tail => tail
  | n + 1, tail => quittingRootThenContinuationProfile reward
      (singletonHazardRoot owner h hh0 hh1)
      (repeatedSingletonProfile reward owner h hh0 hh1 n tail)

omit [Nonempty ι] in
theorem quittingTerminalSemanticPair_repeatedSingletonProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (steps : ℕ) (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (repeatedSingletonProfile reward owner h hh0 hh1 steps tail) =
      repeatedSingletonPrefix reward owner h hh0 hh1 steps
        (quittingTerminalSemanticPair reward tail) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [repeatedSingletonProfile, repeatedSingletonPrefix_succ,
        quittingTerminalSemanticPair_rootThenContinuation, ih]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A proper singleton arc forces the declared tail's owner coordinate to
equal the owner's singleton reward. -/
theorem properSingletonArc_tail_owner_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source tail : Payoff ι) (owner : ι) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (hactive : source owner = quittingSoloReward reward owner owner) :
    tail owner = quittingSoloReward reward owner owner := by
  rw [harc] at hactive
  unfold quittingSingletonArcPayoff at hactive
  have hfactor : (1 - p) *
      (tail owner - quittingSoloReward reward owner owner) = 0 := by
    linear_combination hactive
  rcases mul_eq_zero.mp hfactor with hpzero | htail
  · linarith [hp.2]
  · linarith

omit [Nonempty ι] in
theorem capClearance_prefix_singletonHazardRoot_owner_eq_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    capClearance reward
        (quittingTerminalSemanticPrefix reward
          (singletonHazardRoot owner h hh0 hh1) pair).2 owner =
      max 0 (capClearance reward pair.2 owner) := by
  unfold capClearance quittingTerminalSemanticPrefix
  dsimp only
  rw [quitPayoff_singletonHazardRoot_owner,
    continuePayoff_singletonHazardRoot_owner]
  rw [← max_sub_sub_right]
  simp [ownSingleton, quittingProjectiveSingletonTerminal]

omit [Nonempty ι] in
theorem capClearance_repeatedSingletonPrefix_owner_eq_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (steps : ℕ) (hsteps : 0 < steps) :
    capClearance reward
        (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).2 owner =
      max 0 (capClearance reward pair.2 owner) := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      rw [repeatedSingletonPrefix_succ,
        capClearance_prefix_singletonHazardRoot_owner_eq_max]
      cases steps with
      | zero => rfl
      | succ steps => rw [ih (Nat.succ_pos _), max_eq_right (le_max_left _ _)]

omit [Nonempty ι] in
/-- The executable finite singleton mesh transports the prescribed payoff
with no discretization error: only the surviving tail error remains. -/
theorem abs_quittingTerminalPayoff_repeatedSingletonProfile_sub_arc_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) (owner who : ι) (p h η : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (steps : ℕ)
    (hpow : (1 - h) ^ steps = 1 - p)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (htail : |quittingTerminalPayoff reward tailProfile who - tail who| ≤ η)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |quittingTerminalPayoff reward
          (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile)
          who - source who| ≤ η := by
  have hpair := congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.1 who)
    (quittingTerminalSemanticPair_repeatedSingletonProfile
      reward owner h hh0 hh1 steps tailProfile)
  rw [prescribed_repeatedSingletonPrefix, hpow] at hpair
  change quittingTerminalPayoff reward
      (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile) who = _
    at hpair
  unfold quittingTerminalSemanticPair at hpair
  rw [harc]
  unfold quittingSingletonArcPayoff
  rw [hpair]
  have hfactor :
      (1 - p) * quittingTerminalPayoff reward tailProfile who +
          (1 - (1 - p)) *
            reward (quittingProjectiveSingletonTerminal owner) who -
        (p * quittingSoloReward reward owner who + (1 - p) * tail who) =
        (1 - p) *
          (quittingTerminalPayoff reward tailProfile who - tail who) := by
    simp [quittingSoloReward, quittingProjectiveSingletonTerminal]
    ring
  rw [hfactor, abs_mul]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans htail
  exact (mul_le_mul_of_nonneg_left htail (abs_nonneg (1 - p))).trans
    (by
      rw [abs_of_nonneg (sub_nonneg.mpr hp1)]
      exact mul_le_of_le_one_left hη0 (sub_le_self 1 hp0))

omit [Nonempty ι] in
/-- Sharp outsider alternative: either the deviation reaches the actual tail,
or it first quits within the singleton mesh. -/
theorem quittingTerminalSemanticDebt_repeatedSingletonProfile_other_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) {owner who : ι} (hne : who ≠ owner)
    (p h e d M : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (steps : ℕ)
    (hpow : (1 - h) ^ steps = 1 - p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (hsourceViable : QuittingEssentialAPSViable reward source)
    (htailViable : QuittingEssentialAPSViable reward tail)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htailError :
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ e)
    (htailDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ d) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile))
        who ≤ max ((1 - p) * d) (2 * M * h + e) := by
  let pair := quittingTerminalSemanticPair reward tailProfile
  let t := capClearance reward pair.2 who
  let α := 1 - p
  let A := pairSurplus reward who owner
  let C := normalizedSoloMatrix reward who owner
  let P := α * (pair.1 who - ownSingleton reward who) + (1 - α) * C
  have he0 : 0 ≤ e := (abs_nonneg _).trans htailError
  have hα0 : 0 ≤ α := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by dsimp [α]; linarith
  have hdebt0 : 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_attainable reward
      ⟨tailProfile, rfl⟩ who
  have hd0 : 0 ≤ d := hdebt0.trans htailDebt
  have hA : |A| ≤ 2 * M := by
    dsimp [A, pairSurplus, ownSingleton]
    exact (abs_sub _ _).trans <| by
      have hfirst := hreward
        ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who
      have hsecond := hreward (quittingProjectiveSingletonTerminal who) who
      linarith
  have hM0 : 0 ≤ M := by nlinarith [abs_nonneg A, hA]
  have hP : -e ≤ P := by
    have hsource := hsourceViable who
    have herr := (abs_le.mp htailError).1
    have hscaled : -e ≤ α * (pair.1 who - tail who) := by
      have herrPair : -e ≤ pair.1 who - tail who := by
        simpa [pair, quittingTerminalSemanticPair] using herr
      have hmul := mul_le_mul_of_nonneg_left herrPair hα0
      have hscale := mul_le_of_le_one_left he0 hα1
      calc
        -e ≤ -(α * e) := neg_le_neg hscale
        _ = α * (-e) := by ring
        _ ≤ α * (pair.1 who - tail who) := hmul
    have hbase : 0 ≤ α * (tail who - ownSingleton reward who) +
        (1 - α) * C := by
      rw [harc] at hsource
      dsimp [α, C]
      rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
      unfold quittingProjectiveLCPMatrix quittingSingletonArcPayoff
        quittingSoloBaseline quittingSoloReward ownSingleton at *
      simp only [quittingProjectiveSingletonTerminal]
      nlinarith [hsource]
    dsimp [P]
    rw [show α * (pair.1 who - ownSingleton reward who) + (1 - α) * C =
      α * (pair.1 who - tail who) +
        (α * (tail who - ownSingleton reward who) + (1 - α) * C) by ring]
    linarith
  have hu : -e ≤ pair.1 who - ownSingleton reward who := by
    have hv := htailViable who
    have hv' : ownSingleton reward who ≤ tail who := by
      simpa [QuittingEssentialAPSViable, quittingSoloBaseline,
        quittingSoloReward, ownSingleton, quittingProjectiveSingletonTerminal]
        using hv
    have herr := (abs_le.mp htailError).1
    have herrPair : -e ≤ pair.1 who - tail who := by
      simpa [pair, quittingTerminalSemanticPair] using herr
    linarith
  have henvelope := scalarClearanceIter_le_envelope
    (β := 1 - h) (A := A) (M := C) (t := t) (sub_nonneg.mpr hh1)
      (by linarith) steps
  rw [hpow] at henvelope
  have hfirst : α * t + (1 - α) * C - P ≤ α * d := by
    have ht : t - (pair.1 who - ownSingleton reward who) =
        quittingTerminalSemanticDebt pair who := by
      dsimp [t, capClearance, quittingTerminalSemanticDebt]
      ring
    dsimp [P]
    rw [show α * t + (1 - α) * C -
      (α * (pair.1 who - ownSingleton reward who) + (1 - α) * C) =
        α * (t - (pair.1 who - ownSingleton reward who)) by ring, ht]
    exact mul_le_mul_of_nonneg_left htailDebt hα0
  have hcollision : h * max A 0 ≤ 2 * M * h := by
    have hmax : max A 0 ≤ 2 * M := max_le
      ((le_abs_self A).trans hA) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hmax hh0]
  have hremain : max 0 ((1 - α) * C) - P ≤ e := by
    apply sub_le_iff_le_add.mpr
    apply max_le
    · linarith
    · dsimp [P]
      have hscaled := mul_le_mul_of_nonneg_left hu hα0
      nlinarith [mul_le_of_le_one_left he0 hα1]
  have hsecond : h * max A 0 + max 0 ((1 - α) * C) - P ≤
      2 * M * h + e := by linarith
  have hbound : scalarClearanceIter (1 - h) A C t steps - P ≤
      max (α * d) (2 * M * h + e) := by
    apply (sub_le_sub_right henvelope P).trans
    rw [← max_sub_sub_right]
    apply max_le
    · exact hfirst.trans (le_max_left _ _)
    · simpa [α, show 1 - (1 - h) = h by ring] using
        hsecond.trans (le_max_right (α * d) (2 * M * h + e))
  rw [quittingTerminalSemanticPair_repeatedSingletonProfile]
  unfold quittingTerminalSemanticDebt
  rw [show
    (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).2 who -
        (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).1 who =
      capClearance reward
          (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).2 who +
        ownSingleton reward who -
          (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).1 who by
      simp [capClearance]]
  rw [capClearance_repeatedSingletonPrefix_other reward pair hne,
    prescribed_repeatedSingletonPrefix, hpow]
  have hC : C = reward (quittingProjectiveSingletonTerminal owner) who -
      ownSingleton reward who := by
    dsimp [C]
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
    unfold quittingProjectiveLCPMatrix ownSingleton
    rfl
  rw [show scalarClearanceIter (1 - h) A C t steps +
      ownSingleton reward who -
        (α * pair.1 who + (1 - α) *
          reward (quittingProjectiveSingletonTerminal owner) who) =
      scalarClearanceIter (1 - h) A C t steps - P by
    dsimp [P]
    rw [hC]
    ring]
  exact hbound

omit [Nonempty ι] in
/-- An outsider's unrestricted behavioral debt after an actual finite
singleton mesh has the packet's sharp local bound. -/
theorem quittingTerminalSemanticDebt_repeatedSingletonProfile_other_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) {owner who : ι} (hne : who ≠ owner)
    (p h e d M : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (steps : ℕ)
    (hpow : (1 - h) ^ steps = 1 - p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (hsourceViable : QuittingEssentialAPSViable reward source)
    (htailViable : QuittingEssentialAPSViable reward tail)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htailError :
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ e)
    (htailDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ d) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile))
        who ≤ d + 2 * e + 2 * M * h := by
  have hsharp := quittingTerminalSemanticDebt_repeatedSingletonProfile_other_le_max
    reward tailProfile source tail hne p h e d M hh0 hh1 steps hpow hp0 hp1
    harc hsourceViable htailViable hreward htailError htailDebt
  have he0 : 0 ≤ e := (abs_nonneg _).trans htailError
  have hdebt0 : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who :=
    quittingTerminalSemanticDebt_nonneg_of_attainable reward
      ⟨tailProfile, rfl⟩ who
  have hd0 : 0 ≤ d := hdebt0.trans htailDebt
  have hM0 : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingProjectiveSingletonTerminal who) who)
  apply hsharp.trans
  apply max_le
  · have hsurvive := mul_le_of_le_one_left hd0 (by linarith : 1 - p ≤ 1)
    nlinarith [mul_nonneg hM0 hh0]
  · nlinarith [mul_nonneg hM0 hh0]

omit [Nonempty ι] in
/-- The clock owner's debt bound has no survival contraction: deleting every
prefix hazard still exposes the tail. -/
theorem quittingTerminalSemanticDebt_repeatedSingletonProfile_owner_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) (owner : ι) (p h e d : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (steps : ℕ) (hsteps : 0 < steps)
    (hpow : (1 - h) ^ steps = 1 - p)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (hactive : source owner = quittingSoloReward reward owner owner)
    (htailError :
      |quittingTerminalPayoff reward tailProfile owner - tail owner| ≤ e)
    (htailDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) owner ≤ d) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile))
        owner ≤ d + 2 * e := by
  let pair := quittingTerminalSemanticPair reward tailProfile
  let solo := ownSingleton reward owner
  let δ := pair.1 owner - solo
  let α := 1 - p
  have he0 : 0 ≤ e := (abs_nonneg _).trans htailError
  have hdebt0 : 0 ≤ quittingTerminalSemanticDebt pair owner :=
    quittingTerminalSemanticDebt_nonneg_of_attainable reward
      ⟨tailProfile, rfl⟩ owner
  have hd0 : 0 ≤ d := hdebt0.trans htailDebt
  have htailOwner := properSingletonArc_tail_owner_eq
    reward source tail owner p hp harc hactive
  have hδ : |δ| ≤ e := by
    dsimp [δ, pair, solo, quittingTerminalSemanticPair, ownSingleton]
    simpa [htailOwner, quittingSoloReward,
      quittingProjectiveSingletonTerminal] using htailError
  have hα0 : 0 ≤ α := by dsimp [α]; linarith [hp.2]
  have hα1 : α ≤ 1 := by dsimp [α]; linarith [hp.1]
  rw [quittingTerminalSemanticPair_repeatedSingletonProfile]
  unfold quittingTerminalSemanticDebt
  rw [show
    (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).2 owner -
        (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).1 owner =
      capClearance reward
          (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).2 owner +
        solo -
          (repeatedSingletonPrefix reward owner h hh0 hh1 steps pair).1 owner by
      simp [capClearance, solo]]
  rw [capClearance_repeatedSingletonPrefix_owner_eq_max
    reward pair owner h hh0 hh1 steps hsteps]
  rw [prescribed_repeatedSingletonPrefix, hpow]
  have ht : capClearance reward pair.2 owner =
      quittingTerminalSemanticDebt pair owner + δ := by
    dsimp [pair, δ, solo, capClearance, quittingTerminalSemanticDebt]
    ring
  have hmax : max 0 (capClearance reward pair.2 owner) ≤
      quittingTerminalSemanticDebt pair owner + δ + e := by
    apply max_le
    · have := (abs_le.mp hδ).1
      linarith
    · rw [ht]
      linarith
  have hδupper := (abs_le.mp hδ).2
  dsimp [α, δ, solo, pair] at *
  unfold quittingTerminalSemanticPair ownSingleton at *
  nlinarith [mul_le_mul_of_nonneg_left hδupper (sub_nonneg.mpr hα1)]

omit [Nonempty ι] in
/-- One actual finite proper-singleton mesh simultaneously transports the
target payoff and caps every player's unrestricted behavioral debt. -/
theorem repeatedSingletonProfile_error_and_debt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) (owner : ι) (p h e d M : ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (steps : ℕ) (hsteps : 0 < steps)
    (hpow : (1 - h) ^ steps = 1 - p)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (harc : source = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) tail)
    (hactive : source owner = quittingSoloReward reward owner owner)
    (hsourceViable : QuittingEssentialAPSViable reward source)
    (htailViable : QuittingEssentialAPSViable reward tail)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htailError : ∀ who,
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ e)
    (htailDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ d) :
    (∀ who, |quittingTerminalPayoff reward
        (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile)
        who - source who| ≤ e) ∧
      ∀ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (repeatedSingletonProfile reward owner h hh0 hh1 steps tailProfile))
        who ≤ d + 2 * e + 2 * M * h := by
  constructor
  · intro who
    exact abs_quittingTerminalPayoff_repeatedSingletonProfile_sub_arc_le
      reward tailProfile source tail owner who p h e hh0 hh1 steps hpow harc
      (htailError who) hp.1.le hp.2.le
  · intro who
    by_cases hwho : who = owner
    · subst who
      exact (quittingTerminalSemanticDebt_repeatedSingletonProfile_owner_le
        reward tailProfile source tail owner p h e d hh0 hh1 steps hsteps hpow
        hp harc hactive (htailError owner) (htailDebt owner)).trans
        (by
          have hM0 : 0 ≤ M := (abs_nonneg _).trans (hreward
            (quittingProjectiveSingletonTerminal owner) owner)
          nlinarith [mul_nonneg hM0 hh0])
    · exact quittingTerminalSemanticDebt_repeatedSingletonProfile_other_le
        reward tailProfile source tail hwho p h e d M hh0 hh1 steps hpow
        hp.1.le hp.2.le harc hsourceViable htailViable hreward
        (htailError who) (htailDebt who)

/-! ## Literal jump transport and finite-word execution -/

/-- Coefficient-resolved literal jump transport. -/
theorem rootThenContinuation_coefficient_error_and_debt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) (root : ι → PMF Bool) (e d : ℝ)
    (hsource : source = quittingRootSuccessorPayoff reward tail root)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (htailError : ∀ who,
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ e)
    (htailDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ d) :
    (∀ who, |quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward root tailProfile) who -
          source who| ≤ quittingStationaryContinueMass root * e) ∧
      ∀ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root tailProfile)) who ≤
        quittingRootOpponentContinueMass root who * d +
          (quittingRootOpponentContinueMass root who +
            quittingStationaryContinueMass root) * e := by
  let witness : ι := Classical.choice (inferInstance : Nonempty ι)
  have he0 : 0 ≤ e := (abs_nonneg _).trans (htailError witness)
  have hdebt0 : ∀ who, 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who :=
    quittingTerminalSemanticDebt_nonneg_of_attainable reward ⟨tailProfile, rfl⟩
  have hd0 : 0 ≤ d := (hdebt0 witness).trans (htailDebt witness)
  constructor
  · intro who
    rw [quittingTerminalPayoff_rootThenContinuation_eq, hsource]
    change |quittingRootSuccessorPayoff reward
      (quittingTerminalPayoff reward tailProfile) root who -
        quittingRootSuccessorPayoff reward tail root who| ≤ _
    have hdiff := quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul
      reward [root] (quittingTerminalPayoff reward tailProfile) tail who
    simp only [quittingFiniteRootWordPayoff, List.foldr_cons, List.foldr_nil,
      quittingLiteralRootStackJointSurvival, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] at hdiff
    rw [hdiff]
    rw [abs_mul, abs_of_nonneg (quittingStationaryContinueMass_nonneg root)]
    exact mul_le_mul_of_nonneg_left (htailError who)
      (quittingStationaryContinueMass_nonneg root)
  · intro who
    have hsplice := literalRootStack_debt_le_referenceDebt_add_transmittedSeams
      reward [root] tailProfile tail who
    rw [quittingLiteralRootStackProfile_cons,
      quittingLiteralRootStackProfile_nil] at hsplice
    have href : quittingTerminalSemanticDebt
        (quittingFiniteRootWordSemanticPrefix reward [root] (tail, tail)) who = 0 := by
      rw [quittingFiniteRootWordSemanticPrefix_diagonal_of_exactChain]
      · simp [quittingTerminalSemanticDebt]
      · intro before current after heq
        have hcases : before = [] ∧ current = root ∧ after = [] := by
          simpa using List.cons_eq_append_iff.mp heq
        rcases hcases with ⟨rfl, rfl, rfl⟩
        simpa [quittingFiniteRootWordPayoff] using hnash
    rw [href, zero_add] at hsplice
    simp only [quittingLiteralRootStackOpponentSurvival, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      quittingLiteralRootStackJointSurvival] at hsplice
    have hcap : max 0
        (quittingContinuationBestResponseValue reward tailProfile who - tail who) ≤
          d + e := by
      apply max_le
      · linarith
      · have htd := htailDebt who
        unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at htd
        have habs := (abs_le.mp (htailError who)).2
        linarith
    have hβcap := mul_le_mul_of_nonneg_left hcap
      (quittingRootOpponentContinueMass_nonneg root who)
    have hαerr := mul_le_mul_of_nonneg_left (htailError who)
      (quittingStationaryContinueMass_nonneg root)
    unfold quittingTerminalDeviationDebt at hsplice
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    nlinarith

theorem rootThenContinuation_error_and_debt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tailProfile : (quittingGame reward).BehaviorProfile)
    (source tail : Payoff ι) (root : ι → PMF Bool) (e d : ℝ)
    (hsource : source = quittingRootSuccessorPayoff reward tail root)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (htailError : ∀ who,
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ e)
    (htailDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ d) :
    (∀ who, |quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward root tailProfile) who -
          source who| ≤ e) ∧
      ∀ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root tailProfile)) who ≤
        d + 2 * e := by
  obtain ⟨herror, hdebt⟩ := rootThenContinuation_coefficient_error_and_debt_le
    reward tailProfile source tail root e d hsource hnash htailError htailDebt
  let witness : ι := Classical.choice (inferInstance : Nonempty ι)
  have he0 : 0 ≤ e := (abs_nonneg _).trans (htailError witness)
  have hdebt0 : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) witness :=
    quittingTerminalSemanticDebt_nonneg_of_attainable reward
      ⟨tailProfile, rfl⟩ witness
  have hd0 : 0 ≤ d := hdebt0.trans (htailDebt witness)
  constructor
  · intro who
    exact (herror who).trans
      (mul_le_of_le_one_left he0 (quittingStationaryContinueMass_le_one root))
  · intro who
    have hβd := mul_le_of_le_one_left hd0
      (quittingRootOpponentContinueMass_le_one root who)
    have hβe := mul_le_of_le_one_left he0
      (quittingRootOpponentContinueMass_le_one root who)
    have hαe := mul_le_of_le_one_left he0
      (quittingStationaryContinueMass_le_one root)
    exact (hdebt who).trans (by nlinarith)

/-- A caller-supplied number of extra mesh rows for every retained flow.
The compiler uses `meshCount ... + 1`, so every block is nonempty. -/
abbrev FiniteJumpFlowMeshCount := ℕ → ℕ

/-- Number of jump/flow operations in a compatible word. -/
def CompatibleFiniteJumpFlowWord.length
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} :
    {source tail : Payoff ι} → CompatibleFiniteJumpFlowWord reward source tail → ℕ
  | _, _, .refl _ => 0
  | _, _, .jump _ _ _ _ _ _ rest => rest.length + 1
  | _, _, .flow _ _ _ _ _ _ _ _ _ _ rest => rest.length + 1

/-- Sum of the actual per-row hazards used by the retained flow blocks. -/
def CompatibleFiniteJumpFlowWord.meshHazardSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (meshCount : FiniteJumpFlowMeshCount) :
    {source tail : Payoff ι} → CompatibleFiniteJumpFlowWord reward source tail → ℝ
  | _, _, .refl _ => 0
  | _, _, .jump _ _ _ _ _ _ rest =>
      rest.meshHazardSum (fun n => meshCount (n + 1))
  | _, _, .flow _ _ _ _ p _ _ _ _ _ rest =>
      quittingMeshHazard p (meshCount 0 + 1) +
        rest.meshHazardSum (fun n => meshCount (n + 1))

/-- Execute every retained root literally, splitting each proper singleton
flow into the caller-specified positive number of identical mesh rows. -/
def CompatibleFiniteJumpFlowWord.execute
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (meshCount : FiniteJumpFlowMeshCount) :
    {source tail : Payoff ι} → CompatibleFiniteJumpFlowWord reward source tail →
      (quittingGame reward).BehaviorProfile → (quittingGame reward).BehaviorProfile
  | _, _, .refl _, profile => profile
  | _, _, .jump _ _ _ root _ _ rest, profile =>
      quittingRootThenContinuationProfile reward root
        (rest.execute (fun n => meshCount (n + 1)) profile)
  | _, _, .flow _ _ _ owner p hp _ _ _ _ rest, profile =>
      let steps := meshCount 0 + 1
      let h := quittingMeshHazard p steps
      repeatedSingletonProfile reward owner h
        (quittingMeshHazard_nonneg steps hp.1.le hp.2.le)
        (quittingMeshHazard_le_one steps hp.2.le) steps
        (rest.execute (fun n => meshCount (n + 1)) profile)

/-- Literal finite-word compiler with separate invariant target error and
accumulating debt. -/
theorem CompatibleFiniteJumpFlowWord.execute_error_and_debt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {source tail : Payoff ι}
    (word : CompatibleFiniteJumpFlowWord reward source tail)
    (meshCount : FiniteJumpFlowMeshCount)
    (tailProfile : (quittingGame reward).BehaviorProfile) (e d M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htailError : ∀ who,
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ e)
    (htailDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ d) :
    (∀ who, |quittingTerminalPayoff reward
        (word.execute meshCount tailProfile) who - source who| ≤ e) ∧
      ∀ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (word.execute meshCount tailProfile)) who ≤
        d + 2 * word.length * e + 2 * M * word.meshHazardSum meshCount := by
  induction word generalizing meshCount with
  | refl =>
      simpa [CompatibleFiniteJumpFlowWord.execute,
        CompatibleFiniteJumpFlowWord.length,
        CompatibleFiniteJumpFlowWord.meshHazardSum] using
        And.intro htailError htailDebt
  | jump source next tail root hsource hnash rest ih =>
      let shifted : FiniteJumpFlowMeshCount := fun n => meshCount (n + 1)
      obtain ⟨herror, hdebt⟩ := ih shifted htailError
      obtain ⟨herror', hdebt'⟩ := rootThenContinuation_error_and_debt_le
        reward (rest.execute shifted tailProfile) source next root e
        (d + 2 * rest.length * e + 2 * M * rest.meshHazardSum shifted)
        hsource hnash herror hdebt
      refine ⟨herror', fun who => (hdebt' who).trans ?_⟩
      simp only [CompatibleFiniteJumpFlowWord.length,
        CompatibleFiniteJumpFlowWord.meshHazardSum]
      simp only [shifted, Nat.add_comm]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
      exact le_rfl
  | flow source next tail owner p hp harc hactive hsource hnext rest ih =>
      let shifted : FiniteJumpFlowMeshCount := fun n => meshCount (n + 1)
      obtain ⟨herror, hdebt⟩ := ih shifted htailError
      let steps := meshCount 0 + 1
      let h := quittingMeshHazard p steps
      have hh0 : 0 ≤ h := quittingMeshHazard_nonneg steps hp.1.le hp.2.le
      have hh1 : h ≤ 1 := quittingMeshHazard_le_one steps hp.2.le
      have hsteps : 0 < steps := by dsimp [steps]; omega
      have hpow : (1 - h) ^ steps = 1 - p := by
        dsimp [h]
        exact one_sub_quittingMeshHazard_pow hp.2.le hsteps
      obtain ⟨herror', hdebt'⟩ := repeatedSingletonProfile_error_and_debt_le
        reward (rest.execute shifted tailProfile) source next owner p h e
        (d + 2 * rest.length * e + 2 * M * rest.meshHazardSum shifted) M
        hh0 hh1 steps hsteps hpow hp harc hactive hsource hnext hreward herror hdebt
      refine ⟨herror', fun who => (hdebt' who).trans ?_⟩
      simp only [CompatibleFiniteJumpFlowWord.length,
        CompatibleFiniteJumpFlowWord.meshHazardSum]
      dsimp [h, steps]
      simp only [shifted, Nat.add_comm]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
      exact le_rfl

/-- Starting from a common tail target-error and debt bound `η`, a
word of length `L` has debt `(2L+1)η` plus the sum of mesh charges. -/
theorem CompatibleFiniteJumpFlowWord.execute_common_error_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {source tail : Payoff ι}
    (word : CompatibleFiniteJumpFlowWord reward source tail)
    (meshCount : FiniteJumpFlowMeshCount)
    (tailProfile : (quittingGame reward).BehaviorProfile) (η M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htailError : ∀ who,
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ η)
    (htailDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ η) :
    (∀ who, |quittingTerminalPayoff reward
        (word.execute meshCount tailProfile) who - source who| ≤ η) ∧
      ∀ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (word.execute meshCount tailProfile)) who ≤
        (2 * word.length + 1) * η +
          2 * M * word.meshHazardSum meshCount := by
  obtain ⟨herror, hdebt⟩ := word.execute_error_and_debt_le
    reward meshCount tailProfile η η M hreward htailError htailDebt
  refine ⟨herror, fun who => (hdebt who).trans ?_⟩
  ring_nf
  exact le_rfl

/-- The common-error compiler's coordinate bounds give the literal terminal
exploitability estimate for its executed behavioral profile. -/
theorem CompatibleFiniteJumpFlowWord.execute_exploitability_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {source tail : Payoff ι}
    (word : CompatibleFiniteJumpFlowWord reward source tail)
    (meshCount : FiniteJumpFlowMeshCount)
    (tailProfile : (quittingGame reward).BehaviorProfile) (η M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htailError : ∀ who,
      |quittingTerminalPayoff reward tailProfile who - tail who| ≤ η)
    (htailDebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward tailProfile) who ≤ η) :
    quittingTerminalExploitability reward (word.execute meshCount tailProfile) ≤
      (2 * word.length + 1) * η +
        2 * M * word.meshHazardSum meshCount := by
  have hdebt := (word.execute_common_error_bound reward meshCount tailProfile η M
    hreward htailError htailDebt).2
  rw [quittingTerminalExploitability_eq_max_debt]
  apply QuittingBoundaryHolonomy.finitePlayerMax_le
  intro who
  simpa [quittingTerminalDeviationDebt, quittingTerminalSemanticDebt,
    quittingTerminalSemanticPair] using hdebt who

end GameTheory
