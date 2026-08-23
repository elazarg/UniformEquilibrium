/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Quitting.Chronology.TightFaceCollisionEscape

/-!
# Semantic debt paid by collision on an exact finite path

One carrier lift at the source of a finite exact Nash--Bellman prefix propagates
coherently through every displayed root.  Exact Nash removes the local defect,
so every literal collision is paid by a decrease of unrestricted behavioral
best-response debt.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPunishmentFloorFinitePrefix

variable (path : QuittingPunishmentFloorFinitePrefix reward)

/-- Coherent semantic chronology obtained by recursively prefixing the one
supplied source pair. -/
def semanticPrefixPath (path : QuittingPunishmentFloorFinitePrefix reward)
    (source : QuittingTerminalSemanticPair ι) :
    ℕ → QuittingTerminalSemanticPair ι
  | 0 => source
  | time + 1 => quittingTerminalSemanticPrefix reward (path.roots time)
      (semanticPrefixPath path source time)

@[simp] theorem semanticPrefixPath_zero (source : QuittingTerminalSemanticPair ι) :
    path.semanticPrefixPath source 0 = source := rfl

theorem semanticPrefixPath_succ (source : QuittingTerminalSemanticPair ι)
    (time : ℕ) :
    path.semanticPrefixPath source (time + 1) =
      quittingTerminalSemanticPrefix reward (path.roots time)
        (path.semanticPrefixPath source time) := rfl

/-- The prescribed coordinate of the coherent semantic chronology is exactly
the displayed finite-prefix value. -/
theorem semanticPrefixPath_fst_eq
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source.1 = path.value 0) (time : ℕ) (htime : time ≤ path.horizon) :
    (path.semanticPrefixPath source time).1 = path.value time := by
  induction time with
  | zero => exact hsource
  | succ time ih =>
      rw [path.semanticPrefixPath_succ]
      change quittingRootSuccessorPayoff reward
        (path.semanticPrefixPath source time).1 (path.roots time) = _
      rw [ih (Nat.le_of_succ_le htime)]
      exact (path.policy time (Nat.lt_of_succ_le htime)).symm

/-- Every recursively prefixed pair remains in the actual compact terminal
semantic carrier. -/
theorem semanticPrefixPath_mem_carrier
    (source : QuittingTerminalSemanticPair ι)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward) (time : ℕ) :
    path.semanticPrefixPath source time ∈ quittingTerminalSemanticCarrier reward := by
  induction time with
  | zero => exact hsource
  | succ time ih =>
      rw [path.semanticPrefixPath_succ]
      exact quittingTerminalSemanticPrefix_mem_carrier reward _ _ ih

/-- **One-row semantic collision payment.**  Literal collision mass times
the entire incoming unrestricted debt is paid by the debt decrease. -/
theorem collisionMass_mul_debtSum_le_debtDrop
    (source : QuittingTerminalSemanticPair ι)
    (hsourceCarrier : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceFst : source.1 = path.value 0)
    (time : ℕ) (htime : time < path.horizon) :
    quittingRootCollisionMass (path.roots time) *
        quittingTerminalSemanticDebtSum (path.semanticPrefixPath source time) ≤
      quittingTerminalSemanticDebtSum (path.semanticPrefixPath source time) -
        quittingTerminalSemanticDebtSum
          (path.semanticPrefixPath source (time + 1)) := by
  let pair := path.semanticPrefixPath source time
  have hpairCarrier := path.semanticPrefixPath_mem_carrier source hsourceCarrier time
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpairCarrier
  have hcollision :=
    quittingRootCollisionMass_mul_sum_le_sum_opponentAbsorptionMass_mul
      (path.roots time) (fun who ↦ quittingTerminalSemanticDebt pair who) hdebt
  have hdefect :=
    sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect
      reward pair (path.roots time) hdebt
  have hpairFst : pair.1 = path.value time :=
    path.semanticPrefixPath_fst_eq source hsourceFst time (Nat.le_of_lt htime)
  have hnash : IsεQuittingRootNash reward pair.1 0 (path.roots time) := by
    rw [hpairFst]
    exact path.exactNash time htime
  have hzero : quittingRootTotalNashDefect reward pair.1 (path.roots time) = 0 :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward pair.1 (path.roots time)).1 hnash
  rw [hzero, add_zero, ← path.semanticPrefixPath_succ source time] at hdefect
  exact hcollision.trans hdefect

/-- Collision mass along the whole exact prefix is paid by the source-to-end
decrease of total semantic debt. -/
theorem collisionMass_mul_minimumDebt_le_sourceDebt_sub_endDebt
    (source minimum : QuittingTerminalSemanticPair ι)
    (hsourceCarrier : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceFst : source.1 = path.value 0)
    (_hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum minimum *
        (∑ time ∈ Finset.range path.horizon,
          quittingRootCollisionMass (path.roots time)) ≤
      quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum
          (path.semanticPrefixPath source path.horizon) := by
  have hrows := Finset.sum_le_sum fun time (htime : time ∈
      Finset.range path.horizon) ↦
    path.collisionMass_mul_debtSum_le_debtDrop source
      hsourceCarrier hsourceFst time (Finset.mem_range.1 htime)
  have hminimumEach : ∀ time,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum (path.semanticPrefixPath source time) :=
    fun time ↦ hminimum _ (path.semanticPrefixPath_mem_carrier source
      hsourceCarrier time)
  have hcollisionNonneg : ∀ time,
      0 ≤ quittingRootCollisionMass (path.roots time) :=
    fun time ↦ quittingRootCollisionMass_nonneg _
  have hlower := Finset.sum_le_sum fun time (_htime : time ∈
      Finset.range path.horizon) ↦
    mul_le_mul_of_nonneg_left (hminimumEach time) (hcollisionNonneg time)
  have htelescope : (∑ time ∈ Finset.range path.horizon,
      (quittingTerminalSemanticDebtSum (path.semanticPrefixPath source time) -
        quittingTerminalSemanticDebtSum
          (path.semanticPrefixPath source (time + 1)))) =
      quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum
          (path.semanticPrefixPath source path.horizon) := by
    have h : ∀ length, (∑ time ∈ Finset.range length,
        (quittingTerminalSemanticDebtSum (path.semanticPrefixPath source time) -
          quittingTerminalSemanticDebtSum
            (path.semanticPrefixPath source (time + 1)))) =
        quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebtSum
            (path.semanticPrefixPath source length) := by
      intro length
      induction length with
      | zero => simp
      | succ length ih =>
          rw [Finset.sum_range_succ, ih]
          ring
    exact h path.horizon
  rw [htelescope] at hrows
  have hlower' : quittingTerminalSemanticDebtSum minimum *
      (∑ time ∈ Finset.range path.horizon,
        quittingRootCollisionMass (path.roots time)) ≤
      ∑ time ∈ Finset.range path.horizon,
        quittingRootCollisionMass (path.roots time) *
          quittingTerminalSemanticDebtSum (path.semanticPrefixPath source time) := by
    rw [Finset.mul_sum]
    simpa only [mul_comm] using hlower
  exact hlower'.trans hrows

/-- The end pair remains above minimum debt, giving the packet's final debt
excursion inequality. -/
theorem minimumDebt_mul_collisionMass_le_sourceExcess
    (source minimum : QuittingTerminalSemanticPair ι)
    (hsourceCarrier : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceFst : source.1 = path.value 0)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum minimum *
        (∑ time ∈ Finset.range path.horizon,
          quittingRootCollisionMass (path.roots time)) ≤
      quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum := by
  have hdrop := path.collisionMass_mul_minimumDebt_le_sourceDebt_sub_endDebt
    source minimum hsourceCarrier hsourceFst hminimumCarrier hminimum
  have hend := hminimum _
    (path.semanticPrefixPath_mem_carrier source hsourceCarrier path.horizon)
  linarith

/-- **Composed tight-face semantic excursion.**  A local payoff near-return
with one high-absorption edge forces the explicit source excess above every
positive minimum-debt carrier point. -/
theorem minimumDebt_mul_tightFaceGap_le_sourceExcess
    [Nonempty ι]
    (data : TightFaceSeparatorData reward)
    (source minimum : QuittingTerminalSemanticPair ι)
    (hsourceCarrier : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceFst : source.1 = path.value 0)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    {a : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < path.horizon ∧
      a ≤ quittingRootAbsorptionMass (path.roots time))
    (hnear : ∀ who,
      |path.value 0 who - path.value path.horizon who| ≤
        data.margin * a / (4 * data.covectorL1)) :
    quittingTerminalSemanticDebtSum minimum *
        (data.margin * a /
          (4 * data.rewardCeiling * data.covectorL1)) ≤
      quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum := by
  have hcollision :=
    data.collisionMass_lowerBound_of_highAbsorption_nearReturn
      path hsupport hlocal ha hhigh hnear
  have hsemantic := path.minimumDebt_mul_collisionMass_le_sourceExcess
    source minimum hsourceCarrier hsourceFst hminimumCarrier hminimum
  have hscaled := mul_le_mul_of_nonneg_left hcollision hminimumPositive.le
  exact hscaled.trans hsemantic

/-- A literal behavioral source profile discharges the only semantic
provenance hypothesis in the debt-excursion theorem. -/
theorem minimumDebt_mul_tightFaceGap_le_profileSourceExcess
    [Nonempty ι]
    (data : TightFaceSeparatorData reward)
    (profile : (quittingGame reward).BehaviorProfile)
    (minimum : QuittingTerminalSemanticPair ι)
    (hsourceFst : (quittingTerminalSemanticPair reward profile).1 = path.value 0)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    {a : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < path.horizon ∧
      a ≤ quittingRootAbsorptionMass (path.roots time))
    (hnear : ∀ who,
      |path.value 0 who - path.value path.horizon who| ≤
        data.margin * a / (4 * data.covectorL1)) :
    quittingTerminalSemanticDebtSum minimum *
        (data.margin * a /
          (4 * data.rewardCeiling * data.covectorL1)) ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) -
        quittingTerminalSemanticDebtSum minimum := by
  exact path.minimumDebt_mul_tightFaceGap_le_sourceExcess data
    (quittingTerminalSemanticPair reward profile) minimum
    (quittingTerminalSemanticPair_mem_carrier reward profile) hsourceFst
    hminimumCarrier hminimum hminimumPositive hsupport hlocal ha hhigh hnear

/-- A positive minimum-debt semantic source cannot support a local
tight-face payoff near-return containing a fixed positive absorption row. -/
theorem no_localTightFace_highAbsorption_nearReturn_from_minimum
    [Nonempty ι]
    (data : TightFaceSeparatorData reward)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hminimumFst : minimum.1 = path.value 0)
    (hsupport : ∀ time, time < path.horizon → ∀ owner,
      0 < (path.roots time owner true).toReal → owner ∈ data.owners)
    (hlocal : ∀ time, time ≤ path.horizon → ∀ who,
      |path.value time who - data.boundary who| ≤ data.localRadius)
    {a : ℝ} (ha : 0 < a)
    (hhigh : ∃ time, time < path.horizon ∧
      a ≤ quittingRootAbsorptionMass (path.roots time))
    (hnear : ∀ who,
      |path.value 0 who - path.value path.horizon who| ≤
        data.margin * a / (4 * data.covectorL1)) : False := by
  have hgap := path.minimumDebt_mul_tightFaceGap_le_sourceExcess data
    minimum minimum hminimumCarrier hminimumFst hminimumCarrier hminimum
    hminimumPositive hsupport hlocal ha hhigh hnear
  have hfactor : 0 < data.margin * a /
      (4 * data.rewardCeiling * data.covectorL1) := by
    exact div_pos (mul_pos data.margin_pos ha)
      (mul_pos (mul_pos (by norm_num) data.rewardCeiling_pos)
        data.covectorL1_pos)
  nlinarith

end QuittingPunishmentFloorFinitePrefix

end GameTheory
