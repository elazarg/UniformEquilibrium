/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NormalizedPassportMinimumReturn
import Research.Quitting.NormalizedPassportSingleDensityToll
import UniformEquilibrium.Quitting.Root.StrictAllContinueBasinLinearAbsorptionDefect

/-!
# Vanishing-density boundary of a normalized passport

Starting from one fixed decorated family, minimum tail, positive reference
limit, and exact gain-to-mass identity, this module constructs the densities,
slice minimizers, compact subsequence, and one fixed decorated limit.  The
limit either returns to minimum debt with positive mass and an internally
constructed actualizer, loses both passport coordinates, or carries the
global absorption-defect barrier at one common cap.

No minimizer sequence, subsequence, cluster, barrier, or actualizer is supplied
by the caller.  The limit lies in the enlarged arbitrary-prefix carrier; no
claim places it in the original base-family cluster.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Density `M_ref / D_ref / (n + 2)` generated from one positive reference
passport. -/
def quittingVanishingPassportDensity
    (reference : QuittingMarkedPairDecoration ι) (rank : ℕ) : ℝ :=
  reference.markedMass / reference.wholeDebt / (rank + 2 : ℝ)

/-- The corresponding gain density under a fixed gain-to-mass gap. -/
def quittingVanishingPassportGainDensity
    (gap : ℝ) (reference : QuittingMarkedPairDecoration ι) (rank : ℕ) : ℝ :=
  gap * quittingVanishingPassportDensity reference rank

/-- Internally selected minimizers of every vanishing-density slice. -/
structure QuittingVanishingDensityPassportSequence
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι) (gap : ℝ)
    (passport : family.ConvergentPassport minimum) where
  point : ℕ → QuittingMarkedPairDecoration ι
  point_mem : ∀ rank, point rank ∈ family.normalizedPassportSlice minimum
    (quittingVanishingPassportDensity passport.limit rank)
    (quittingVanishingPassportGainDensity gap passport.limit rank)
  point_minimal : ∀ rank candidate, candidate ∈
      family.normalizedPassportSlice minimum
        (quittingVanishingPassportDensity passport.limit rank)
        (quittingVanishingPassportGainDensity gap passport.limit rank) →
    (point rank).wholeDebt ≤ candidate.wholeDebt

namespace QuittingVanishingDensityPassportSequence

variable {family : QuittingMarkedPairDecoratedFamily reward}
variable {minimum : QuittingTerminalSemanticPair ι} {gap : ℝ}
variable {passport : family.ConvergentPassport minimum}

/-- Every selected minimizer remains in the common compact prefix carrier. -/
theorem point_mem_carrier
    (sequence : QuittingVanishingDensityPassportSequence
      family minimum gap passport) (rank : ℕ) :
    sequence.point rank ∈ family.prefixOrbitCarrier :=
  (sequence.point_mem rank).1

/-- Every selected minimizer retains the one fixed minimum tail debt. -/
theorem point_tailDebt_eq
    (sequence : QuittingVanishingDensityPassportSequence
      family minimum gap passport) (rank : ℕ) :
    (sequence.point rank).tailDebt =
      quittingTerminalSemanticDebtSum minimum :=
  (sequence.point_mem rank).2.1

end QuittingVanishingDensityPassportSequence

namespace QuittingMarkedPairDecoratedFamily

variable (family : QuittingMarkedPairDecoratedFamily reward)

/-- The canonical density is positive at every finite rank. -/
theorem quittingVanishingPassportDensity_pos
    (minimum : QuittingTerminalSemanticPair ι)
    (passport : family.ConvergentPassport minimum) (rank : ℕ) :
    0 < quittingVanishingPassportDensity passport.limit rank := by
  unfold quittingVanishingPassportDensity
  exact div_pos (div_pos passport.markedMass_pos passport.wholeDebt_pos)
    (by positivity)

/-- The canonical density tends to zero. -/
theorem quittingVanishingPassportDensity_tendsto_zero
    (minimum : QuittingTerminalSemanticPair ι)
    (passport : family.ConvergentPassport minimum) :
    Tendsto (quittingVanishingPassportDensity passport.limit) atTop
      (nhds 0) := by
  have hbase : Tendsto (fun rank : ℕ => (1 : ℝ) / (rank + 1)) atTop
      (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hshift : Tendsto (fun rank : ℕ => (1 : ℝ) / (rank + 2)) atTop
      (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
      one_add_one_eq_two] using
      (tendsto_add_atTop_iff_nat 1).2 hbase
  have hscaled := hshift.const_mul
    (passport.limit.markedMass / passport.limit.wholeDebt)
  rw [show quittingVanishingPassportDensity passport.limit = fun rank : ℕ =>
      (passport.limit.markedMass / passport.limit.wholeDebt) *
        ((1 : ℝ) / (rank + 2)) by
    funext rank
    simp only [quittingVanishingPassportDensity]
    ring]
  simpa using hscaled

/-- The reference limit strictly satisfies every canonical vanishing-density
mass constraint. -/
theorem reference_mass_constraint_strict
    (minimum : QuittingTerminalSemanticPair ι)
    (passport : family.ConvergentPassport minimum) (rank : ℕ) :
    quittingVanishingPassportDensity passport.limit rank *
        passport.limit.wholeDebt < passport.limit.markedMass := by
  unfold quittingVanishingPassportDensity
  have hrank : (0 : ℝ) ≤ rank := by positivity
  have hdenom : (1 : ℝ) < rank + 2 := by linarith
  have hdebtNe : passport.limit.wholeDebt ≠ 0 :=
    ne_of_gt passport.wholeDebt_pos
  field_simp [hdebtNe]
  nlinarith [passport.markedMass_pos]

/-- Exact carrier proportionality gives the matching strict gain constraint
at the reference limit. -/
theorem reference_gain_constraint_strict
    (minimum : QuittingTerminalSemanticPair ι)
    (passport : family.ConvergentPassport minimum)
    (gap : ℝ) (hgap : 0 < gap)
    (hidentity : ∀ point ∈ family.prefixOrbitCarrier,
      point.actualGain = gap * point.markedMass)
    (rank : ℕ) :
    quittingVanishingPassportGainDensity gap passport.limit rank *
        passport.limit.wholeDebt < passport.limit.actualGain := by
  rw [hidentity passport.limit passport.limit_mem_prefixOrbitCarrier]
  unfold quittingVanishingPassportGainDensity
  simpa only [mul_assoc] using mul_lt_mul_of_pos_left
    (family.reference_mass_constraint_strict minimum passport rank) hgap

/-- The entire minimizer sequence is constructed from the fixed reference;
no choices are exposed as hypotheses. -/
theorem nonempty_vanishingDensityPassportSequence
    (minimum : QuittingTerminalSemanticPair ι)
    (passport : family.ConvergentPassport minimum)
    (gap : ℝ) (hgap : 0 < gap)
    (hidentity : ∀ point ∈ family.prefixOrbitCarrier,
      point.actualGain = gap * point.markedMass) :
    Nonempty (QuittingVanishingDensityPassportSequence
      family minimum gap passport) := by
  have hexists : ∀ rank, ∃ point ∈ family.normalizedPassportSlice minimum
      (quittingVanishingPassportDensity passport.limit rank)
      (quittingVanishingPassportGainDensity gap passport.limit rank),
      ∀ candidate ∈ family.normalizedPassportSlice minimum
        (quittingVanishingPassportDensity passport.limit rank)
        (quittingVanishingPassportGainDensity gap passport.limit rank),
        point.wholeDebt ≤ candidate.wholeDebt := by
    intro rank
    apply family.exists_minimum_normalizedPassportSlice
    refine ⟨passport.limit, passport.limit_mem_normalizedPassportSlice _ _ ?_ ?_⟩
    · exact family.reference_mass_constraint_strict minimum passport rank
    · exact family.reference_gain_constraint_strict
        minimum passport gap hgap hidentity rank
  choose point hpoint hminimal using hexists
  exact ⟨{
    point := point
    point_mem := hpoint
    point_minimal := hminimal
  }⟩

end QuittingMarkedPairDecoratedFamily

/-! ## Deterministic Continue tremble -/

/-- A positive deterministic tremble scale tending to zero. -/
def quittingContinueTrembleRate (rank : ℕ) : ℝ :=
  1 / (rank + 2 : ℝ)

/-- Scale every Quit marginal by `1 - quittingContinueTrembleRate rank`.
Every coordinate consequently has positive Continue probability. -/
def quittingContinueTrembleRoot
    (root : ι → PMF Bool) (rank : ℕ) : ι → PMF Bool := fun who =>
  let rate := quittingContinueTrembleRate rank
  let quit := (root who true).toReal
  bernoulliBool ((1 - rate) * quit) (by
    apply mul_nonneg
    · exact sub_nonneg.mpr (by
        unfold rate quittingContinueTrembleRate
        have hrank : (0 : ℝ) ≤ rank := by positivity
        rw [div_le_one] <;> linarith)
    · exact ENNReal.toReal_nonneg) (by
    have hquit : quit ≤ 1 := by
      dsimp only [quit]
      linarith [quittingRoot_continueProbability_add_quitProbability root who,
        show 0 ≤ (root who false).toReal from ENNReal.toReal_nonneg]
    calc
      (1 - rate) * quit ≤ 1 * quit := by
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        exact sub_le_self 1 (by
          unfold rate quittingContinueTrembleRate
          positivity)
      _ ≤ 1 := by simpa using hquit)

/-- Simplex coordinates of the deterministic Continue tremble. -/
def quittingContinueTrembleSimplex
    (root : ι → PMF Bool) (rank : ℕ) : QuittingRootSimplex ι :=
  fun who => stdSimplexEquiv (quittingContinueTrembleRoot root rank who)

theorem quittingContinueTrembleRate_pos (rank : ℕ) :
    0 < quittingContinueTrembleRate rank := by
  unfold quittingContinueTrembleRate
  positivity

theorem quittingContinueTrembleRate_le_one (rank : ℕ) :
    quittingContinueTrembleRate rank ≤ 1 := by
  unfold quittingContinueTrembleRate
  have hrank : (0 : ℝ) ≤ rank := by positivity
  rw [div_le_one] <;> linarith

theorem quittingContinueTrembleRate_tendsto_zero :
    Tendsto quittingContinueTrembleRate atTop (nhds 0) := by
  have hbase : Tendsto (fun rank : ℕ => (1 : ℝ) / (rank + 1)) atTop
      (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun rank : ℕ => (1 : ℝ) / (rank + 2)) atTop (nhds 0)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
    one_add_one_eq_two] using
    (tendsto_add_atTop_iff_nat 1).2 hbase

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingContinueTrembleRoot_true_toReal
    (root : ι → PMF Bool) (rank : ℕ) (who : ι) :
    (quittingContinueTrembleRoot root rank who true).toReal =
      (1 - quittingContinueTrembleRate rank) * (root who true).toReal := by
  simp [quittingContinueTrembleRoot]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingContinueTrembleRoot_false_toReal
    (root : ι → PMF Bool) (rank : ℕ) (who : ι) :
    (quittingContinueTrembleRoot root rank who false).toReal =
      1 - (1 - quittingContinueTrembleRate rank) *
        (root who true).toReal := by
  simp [quittingContinueTrembleRoot]

omit [DecidableEq ι] in
/-- Every finite Continue tremble has strictly positive joint Continue mass. -/
theorem quittingContinueTrembleRoot_continueMass_pos
    (root : ι → PMF Bool) (rank : ℕ) :
    0 < quittingStationaryContinueMass
      (quittingContinueTrembleRoot root rank) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_pos
  intro who _
  rw [quittingContinueTrembleRoot_false_toReal]
  have hquit : (root who true).toReal ≤ 1 := by
    linarith [quittingRoot_continueProbability_add_quitProbability root who,
      show 0 ≤ (root who false).toReal from ENNReal.toReal_nonneg]
  have hrate := quittingContinueTrembleRate_pos rank
  have hrateOne := quittingContinueTrembleRate_le_one rank
  nlinarith [show 0 ≤ (root who true).toReal from ENNReal.toReal_nonneg]

omit [DecidableEq ι] in
/-- The deterministic Continue trembles converge to the original product
root in finite simplex coordinates. -/
theorem quittingContinueTrembleSimplex_tendsto
    (root : ι → PMF Bool) :
    Tendsto (quittingContinueTrembleSimplex root) atTop
      (nhds (fun who => stdSimplexEquiv (root who))) := by
  rw [tendsto_pi_nhds]
  intro who
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro action
  have hscaled : Tendsto (fun rank =>
      (1 - quittingContinueTrembleRate rank) * (root who true).toReal)
      atTop (nhds ((root who true).toReal)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hquit : Tendsto (fun _ : ℕ => (root who true).toReal) atTop
        (nhds ((root who true).toReal)) := tendsto_const_nhds
    simpa using (hone.sub quittingContinueTrembleRate_tendsto_zero).mul hquit
  cases action with
  | false =>
      change Tendsto (fun rank =>
        (quittingContinueTrembleRoot root rank who false).toReal) atTop
          (nhds ((root who false).toReal))
      have hcontinue : (root who false).toReal =
          1 - (root who true).toReal := by
        linarith [quittingRoot_continueProbability_add_quitProbability root who]
      simpa only [quittingContinueTrembleRoot_false_toReal, hcontinue] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
          (nhds 1)).sub hscaled
  | true =>
      change Tendsto (fun rank =>
        (quittingContinueTrembleRoot root rank who true).toReal) atTop
          (nhds ((root who true).toReal))
      simpa only [quittingContinueTrembleRoot_true_toReal] using hscaled

omit [DecidableEq ι] in
@[simp] theorem quittingRootOfSimplex_continueTrembleSimplex
    (root : ι → PMF Bool) (rank : ℕ) :
    quittingRootOfSimplex (quittingContinueTrembleSimplex root rank) =
      quittingContinueTrembleRoot root rank := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
    (quittingContinueTrembleRoot root rank who)

/-- The internally compactified vanishing-density boundary and its exact
three-way outcome.  The subsequence and limit are fixed before the barrier's
universal root quantifier. -/
structure QuittingVanishingDensityPassportBoundary
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair ι) (gap : ℝ)
    (passport : family.ConvergentPassport minimum) where
  sequence : QuittingVanishingDensityPassportSequence
    family minimum gap passport
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  limit : QuittingMarkedPairDecoration ι
  limit_mem_carrier : limit ∈ family.prefixOrbitCarrier
  points_tendsto : Tendsto (sequence.point ∘ subsequence) atTop (nhds limit)
  outcome :
    (limit.wholeDebt = quittingTerminalSemanticDebtSum minimum ∧
      0 < limit.markedMass ∧
      Nonempty (QuittingMarkedPairMinimumReturnActualizer family minimum
        (limit.markedMass /
          (2 * quittingTerminalSemanticDebtSum minimum))
        (gap * (limit.markedMass /
          (2 * quittingTerminalSemanticDebtSum minimum))) limit)) ∨
    (limit.markedMass = 0 ∧ limit.actualGain = 0) ∨
    ∀ root : ι → PMF Bool,
      limit.wholeDebt *
          quittingRootAbsorptionMass root ≤
        quittingRootTotalNashDefect reward limit.whole.1.2 root

namespace QuittingVanishingDensityPassportBoundary

variable {family : QuittingMarkedPairDecoratedFamily reward}
variable {minimum : QuittingTerminalSemanticPair ι} {gap : ℝ}
variable {passport : family.ConvergentPassport minimum}

/-- The selected limit retains the same fixed tail debt. -/
theorem limit_tailDebt_eq
    (boundary : QuittingVanishingDensityPassportBoundary
      family minimum gap passport) :
    boundary.limit.tailDebt = quittingTerminalSemanticDebtSum minimum := by
  have hleft := QuittingMarkedPairDecoration.continuous_tailDebt.tendsto
    boundary.limit |>.comp boundary.points_tendsto
  have hright : Tendsto (fun _ : ℕ =>
      quittingTerminalSemanticDebtSum minimum) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum)) := tendsto_const_nhds
  apply tendsto_nhds_unique hleft
  refine hright.congr' ?_
  filter_upwards [] with rank
  exact (boundary.sequence.point_tailDebt_eq
    (boundary.subsequence rank)).symm

end QuittingVanishingDensityPassportBoundary

namespace QuittingMarkedPairDecoratedFamily

variable (family : QuittingMarkedPairDecoratedFamily reward)

private theorem vanishingDensity_limit_barrier
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (passport : family.ConvergentPassport minimum)
    (gap : ℝ) (hgap : 0 < gap)
    (hidentity : ∀ point ∈ family.prefixOrbitCarrier,
      point.actualGain = gap * point.markedMass)
    (sequence : QuittingVanishingDensityPassportSequence
      family minimum gap passport)
    (subsequence : ℕ → ℕ)
    (hsubsequence : StrictMono subsequence)
    (limit : QuittingMarkedPairDecoration ι)
    (_hlimitMem : limit ∈ family.prefixOrbitCarrier)
    (htendsto : Tendsto (sequence.point ∘ subsequence) atTop (nhds limit))
    (hmass : 0 < limit.markedMass) :
    ∀ root : ι → PMF Bool,
      limit.wholeDebt *
          quittingRootAbsorptionMass root ≤
        quittingRootTotalNashDefect reward limit.whole.1.2 root := by
  have hpositive : ∀ testRoot : ι → PMF Bool,
      0 < quittingStationaryContinueMass testRoot →
      limit.wholeDebt * quittingRootAbsorptionMass testRoot ≤
        quittingRootTotalNashDefect reward limit.whole.1.2 testRoot := by
    intro root hcontinuationPos
    let continuation := quittingStationaryContinueMass root
    let absorption := quittingRootAbsorptionMass root
    have hdensity := (family.quittingVanishingPassportDensity_tendsto_zero
      minimum passport).comp hsubsequence.tendsto_atTop
    have hmassTendsto : Tendsto (fun rank =>
        (sequence.point (subsequence rank)).markedMass) atTop
        (nhds limit.markedMass) :=
      ((continuous_fst.comp continuous_snd).tendsto limit).comp htendsto
    have hdebtTendsto : Tendsto (fun rank =>
        (sequence.point (subsequence rank)).wholeDebt) atTop
        (nhds limit.wholeDebt) :=
      QuittingMarkedPairDecoration.continuous_wholeDebt.tendsto limit
        |>.comp htendsto
    have htailTendsto : Tendsto (fun rank =>
        (sequence.point (subsequence rank)).whole.1.2) atTop
        (nhds limit.whole.1.2) := by
      have hprojection : Continuous (fun point :
          QuittingMarkedPairDecoration ι => point.whole.1.2) := by
        have hraw : Continuous (fun point :
            QuittingMarkedPairDecoration ι => point.1.1.1.2) := by fun_prop
        simpa only [QuittingMarkedPairDecoration.whole] using hraw
      exact hprojection.tendsto limit |>.comp htendsto
    have hdefectTendsto : Tendsto (fun rank =>
        quittingRootTotalNashDefect reward
          (sequence.point (subsequence rank)).whole.1.2 root) atTop
        (nhds (quittingRootTotalNashDefect reward limit.whole.1.2 root)) :=
      (continuous_quittingRootTotalNashDefect_fixedRoot reward root).tendsto
        limit.whole.1.2 |>.comp htailTendsto
    have hleft : Tendsto (fun rank =>
        quittingVanishingPassportDensity passport.limit (subsequence rank) *
          quittingRootTotalNashDefect reward
            (sequence.point (subsequence rank)).whole.1.2 root) atTop
        (nhds 0) := by
      simpa using hdensity.mul hdefectTendsto
    have hslack : Tendsto (fun rank =>
        (sequence.point (subsequence rank)).markedMass -
          quittingVanishingPassportDensity passport.limit
              (subsequence rank) *
            (sequence.point (subsequence rank)).wholeDebt) atTop
        (nhds limit.markedMass) := by
      simpa using hmassTendsto.sub (hdensity.mul hdebtTendsto)
    have hright : Tendsto (fun rank => continuation *
        ((sequence.point (subsequence rank)).markedMass -
          quittingVanishingPassportDensity passport.limit
              (subsequence rank) *
            (sequence.point (subsequence rank)).wholeDebt)) atTop
        (nhds (continuation * limit.markedMass)) :=
      hslack.const_mul continuation
    have heventuallyFeasible : ∀ᶠ rank in atTop,
        quittingVanishingPassportDensity passport.limit (subsequence rank) *
            quittingRootTotalNashDefect reward
              (sequence.point (subsequence rank)).whole.1.2 root ≤
          continuation *
            ((sequence.point (subsequence rank)).markedMass -
              quittingVanishingPassportDensity passport.limit
                  (subsequence rank) *
                (sequence.point (subsequence rank)).wholeDebt) := by
      exact (hleft.eventually_lt hright
        (mul_pos hcontinuationPos hmass)).mono fun _ hlt => hlt.le
    have heventuallyBound : ∀ᶠ rank in atTop,
        (sequence.point (subsequence rank)).wholeDebt * absorption ≤
          quittingRootTotalNashDefect reward
            (sequence.point (subsequence rank)).whole.1.2 root := by
      filter_upwards [heventuallyFeasible] with rank hfeasible
      let point := sequence.point (subsequence rank)
      have hprefixed : family.prefixMap root point ∈
          family.normalizedPassportSlice minimum
            (quittingVanishingPassportDensity passport.limit
              (subsequence rank))
            (quittingVanishingPassportGainDensity gap passport.limit
              (subsequence rank)) := by
        let hdata : QuittingSingleDensityPassportMinimizer family minimum := {
          gap := gap
          density := quittingVanishingPassportDensity passport.limit
            (subsequence rank)
          gap_pos := hgap
          density_pos := family.quittingVanishingPassportDensity_pos
            minimum passport (subsequence rank)
          point := point
          carrier_identity := hidentity
          point_mem := sequence.point_mem (subsequence rank)
          point_minimal := sequence.point_minimal (subsequence rank)
          pointDebt_pos := hminimum_pos.trans_le
            (hminimum _ (family.whole_semantic_mem_carrier
              (sequence.point_mem_carrier (subsequence rank))))
        }
        have hcriterion : hdata.density *
              quittingRootTotalNashDefect reward hdata.point.whole.1.2 root ≤
            quittingStationaryContinueMass root * hdata.slack := by
          simpa only [hdata, point, continuation,
            QuittingSingleDensityPassportMinimizer.slack] using hfeasible
        have hprefixed := (hdata.prefixMap_mem_slice_iff root).2 hcriterion
        simpa only [hdata, point,
          quittingVanishingPassportGainDensity] using hprefixed
      have hminimal := sequence.point_minimal (subsequence rank)
        (family.prefixMap root point) hprefixed
      have hledger := family.prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect
        root point
      change point.wholeDebt ≤ (family.prefixMap root point).wholeDebt at hminimal
      rw [hledger] at hminimal
      change point.wholeDebt ≤ continuation * point.wholeDebt +
        quittingRootTotalNashDefect reward point.whole.1.2 root at hminimal
      change point.wholeDebt * (1 - continuation) ≤ _
      linarith
    apply le_of_tendsto_of_tendsto (hdebtTendsto.mul_const absorption)
      hdefectTendsto
      heventuallyBound
  intro root
  by_cases hcontinuation : quittingStationaryContinueMass root = 0
  · let simplexRoot : QuittingRootSimplex ι :=
      fun who => stdSimplexEquiv (root who)
    let tremble : ℕ → QuittingRootSimplex ι :=
      quittingContinueTrembleSimplex root
    have htremble : Tendsto tremble atTop (nhds simplexRoot) := by
      exact quittingContinueTrembleSimplex_tendsto root
    have hrootEq : quittingRootOfSimplex simplexRoot = root := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
    have habsorptionTendsto : Tendsto (fun rank =>
        quittingRootAbsorptionMass (quittingRootOfSimplex (tremble rank)))
        atTop (nhds (quittingRootAbsorptionMass root)) := by
      have hcontinuous :=
        continuous_quittingRootAbsorptionMass_simplex (ι := ι)
      have htendsto := (hcontinuous.tendsto simplexRoot).comp htremble
      rwa [hrootEq] at htendsto
    have hdefectTendsto : Tendsto (fun rank =>
        quittingRootTotalNashDefect reward limit.whole.1.2
          (quittingRootOfSimplex (tremble rank))) atTop
        (nhds (quittingRootTotalNashDefect reward limit.whole.1.2 root)) := by
      have hpair : Tendsto (fun rank => (limit.whole.1.2, tremble rank))
          atTop (nhds (limit.whole.1.2, simplexRoot)) :=
        tendsto_const_nhds.prodMk_nhds htremble
      have htendsto :=
        (continuous_quittingRootTotalNashDefect_simplex reward).tendsto
          (limit.whole.1.2, simplexRoot) |>.comp hpair
      rwa [hrootEq] at htendsto
    have hbarrier : ∀ rank,
        limit.wholeDebt *
            quittingRootAbsorptionMass (quittingRootOfSimplex (tremble rank)) ≤
          quittingRootTotalNashDefect reward limit.whole.1.2
            (quittingRootOfSimplex (tremble rank)) := by
      intro rank
      apply hpositive
      rw [show quittingRootOfSimplex (tremble rank) =
          quittingContinueTrembleRoot root rank by
        exact quittingRootOfSimplex_continueTrembleSimplex root rank]
      exact quittingContinueTrembleRoot_continueMass_pos root rank
    exact le_of_tendsto_of_tendsto
      (tendsto_const_nhds.mul habsorptionTendsto) hdefectTendsto
      (Filter.Eventually.of_forall hbarrier)
  · apply hpositive
    exact lt_of_le_of_ne (quittingStationaryContinueMass_nonneg root)
      (Ne.symm hcontinuation)

/-- The density-to-zero construction, including its minimizers, one compact
subsequence, one fixed limit, and the exact three-way boundary outcome. -/
theorem nonempty_vanishingDensityPassportBoundary
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (passport : family.ConvergentPassport minimum)
    (gap : ℝ) (hgap : 0 < gap)
    (hidentity : ∀ point ∈ family.prefixOrbitCarrier,
      point.actualGain = gap * point.markedMass) :
    Nonempty (QuittingVanishingDensityPassportBoundary
      family minimum gap passport) := by
  obtain ⟨sequence⟩ := family.nonempty_vanishingDensityPassportSequence
    minimum passport gap hgap hidentity
  obtain ⟨limit, hlimitMem, subsequence, hsubsequence, htendsto⟩ :=
    family.prefixOrbitCarrier_isCompact.tendsto_subseq
      sequence.point_mem_carrier
  have htailTendsto : Tendsto (fun rank =>
      (sequence.point (subsequence rank)).tailDebt) atTop
      (nhds limit.tailDebt) :=
    QuittingMarkedPairDecoration.continuous_tailDebt.tendsto limit
      |>.comp htendsto
  have htailEq : limit.tailDebt =
      quittingTerminalSemanticDebtSum minimum := by
    have hconstant : Tendsto (fun _ : ℕ =>
        quittingTerminalSemanticDebtSum minimum) atTop
        (nhds (quittingTerminalSemanticDebtSum minimum)) := tendsto_const_nhds
    apply tendsto_nhds_unique htailTendsto
    refine hconstant.congr' ?_
    filter_upwards [] with rank
    exact (sequence.point_tailDebt_eq (subsequence rank)).symm
  have hambient := family.prefixOrbitCarrier_subset_ambient hlimitMem
  have hmassNonneg : 0 ≤ limit.markedMass := hambient.2.1.1
  have hlimitIdentity := hidentity limit hlimitMem
  by_cases hmassZero : limit.markedMass = 0
  · refine ⟨{
      sequence := sequence
      subsequence := subsequence
      subsequence_strictMono := hsubsequence
      limit := limit
      limit_mem_carrier := hlimitMem
      points_tendsto := htendsto
      outcome := Or.inr (Or.inl ⟨hmassZero, ?_⟩)
    }⟩
    rw [hlimitIdentity, hmassZero, mul_zero]
  · have hmassPos : 0 < limit.markedMass :=
      lt_of_le_of_ne hmassNonneg (Ne.symm hmassZero)
    by_cases hreturn : limit.wholeDebt =
        quittingTerminalSemanticDebtSum minimum
    · let massDensity := limit.markedMass /
        (2 * quittingTerminalSemanticDebtSum minimum)
      have hmassDensityPos : 0 < massDensity := by
        exact div_pos hmassPos (mul_pos (by norm_num) hminimum_pos)
      have hgainDensityPos : 0 < gap * massDensity :=
        mul_pos hgap hmassDensityPos
      have hmassConstraint : massDensity * limit.wholeDebt ≤
          limit.markedMass := by
        dsimp only [massDensity]
        rw [hreturn]
        have hminimumNe : quittingTerminalSemanticDebtSum minimum ≠ 0 :=
          ne_of_gt hminimum_pos
        field_simp [hminimumNe]
        nlinarith [hmassPos]
      have hlimitSlice : limit ∈ family.normalizedPassportSlice minimum
          massDensity (gap * massDensity) := by
        refine ⟨hlimitMem, htailEq, hmassConstraint, ?_⟩
        · rw [hlimitIdentity]
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hmassConstraint hgap.le
      obtain ⟨actualizer⟩ :=
        nonempty_quittingMarkedPairMinimumReturnActualizer family minimum
          massDensity (gap * massDensity) limit hmassDensityPos
            hgainDensityPos hminimum_pos hlimitSlice hreturn
      refine ⟨{
        sequence := sequence
        subsequence := subsequence
        subsequence_strictMono := hsubsequence
        limit := limit
        limit_mem_carrier := hlimitMem
        points_tendsto := htendsto
        outcome := Or.inl ⟨hreturn, hmassPos, ?_⟩
      }⟩
      simpa only [massDensity] using (show Nonempty
        (QuittingMarkedPairMinimumReturnActualizer family minimum massDensity
          (gap * massDensity) limit) from ⟨actualizer⟩)
    · have hbarrier := family.vanishingDensity_limit_barrier
        minimum hminimum hminimum_pos passport gap hgap hidentity sequence
          subsequence hsubsequence limit hlimitMem htendsto hmassPos
      exact ⟨{
        sequence := sequence
        subsequence := subsequence
        subsequence_strictMono := hsubsequence
        limit := limit
        limit_mem_carrier := hlimitMem
        points_tendsto := htendsto
        outcome := Or.inr (Or.inr hbarrier)
      }⟩

end QuittingMarkedPairDecoratedFamily

end GameTheory
