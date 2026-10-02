/-
Postmark immediate atom or reached block, sections 1-3.

Fix one quitting reward, one behavior profile, one nonempty terminal coalition
`A`, and a positive scale `mu`.  The date-`t` stage mass of `A` is the
unconditional probability that first absorption happens at date `t` at exactly
`A`.  That family sums to the `A` coordinate of the terminal law.

Assume the coordinate floor `3 * mu / 4`.  Then exactly one of two alternatives
is available on the same profile.  Either the date-zero stage mass already
reaches `mu / 8`, or the strictly later dates carry more than `5 * mu / 8`; in
the latter case there is a finite exit cut `1 < e` whose block `[1, e)` carries
stage mass above `mu / 2`, joint survival to date one exceeds `5 * mu / 8`, and
the total marginal quit rate summed over that block exceeds `mu / 2`.

The block floors rest on two elementary per-date estimates.  Stage mass at a
date is survival there times the live root's exact coalition mass, so it is
dominated both by the survival drop across that date (which telescopes to the
survival floor) and by the live root's total marginal quit rate (which gives
the hazard floor).

The sequence wrapper takes the eventual coordinate floor as a hypothesis and
returns one strictly monotone extraction along which a single arm holds at
every index.  No semantic or law compactification is performed here: the
eventual coordinate floor is supplied, not derived.  The section 4 two-cut
instantiation is out of scope for this file.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Boundary.Exceptional.Hazard
import UniformEquilibrium.Quitting.Cycles.CyclicGreenDebt
import UniformEquilibrium.Quitting.Paths.LiveMassRecurrence
import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Per-date estimates -/

omit [DecidableEq ι] in
/-- The joint all-Continue mass of a date is the stationary all-Continue mass
of the profile's live root at that date. -/
theorem fablePostmark_jointContinueMass_eq_stationaryContinueMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingJointContinueMass reward profile time =
      quittingStationaryContinueMass
        (quittingProfileLiveRoot reward profile time) := by
  rw [quittingJointContinueMass_eq_product,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  rfl

omit [DecidableEq ι] in
/-- The survival-weighted root absorption mass of a date is exactly the
survival drop across that date. -/
theorem fablePostmark_liveMass_mul_rootAbsorptionMass_eq_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time *
        quittingRootAbsorptionMass
          (quittingProfileLiveRoot reward profile time) =
      quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
  have hsucc : quittingLiveMass reward profile (time + 1) =
      quittingLiveMass reward profile time *
        quittingStationaryContinueMass
          (quittingProfileLiveRoot reward profile time) := by
    rw [quittingLiveMass_succ,
      fablePostmark_jointContinueMass_eq_stationaryContinueMass]
  rw [hsucc]
  unfold quittingRootAbsorptionMass
  ring

/-- One date's stage mass is dominated by the survival drop across that
date. -/
theorem fablePostmark_stageCoalitionMass_le_liveMass_sub_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    ← fablePostmark_liveMass_mul_rootAbsorptionMass_eq_sub]
  exact mul_le_mul_of_nonneg_left
    (quittingRootCoalitionMass_le_absorptionMass_of_nonempty
      (quittingProfileLiveRoot reward profile time) terminal.val
      terminal.property)
    (quittingLiveMass_nonneg reward profile time)

/-- One date's stage mass is dominated by the total marginal quit rate of the
profile's live root at that date. -/
theorem fablePostmark_stageCoalitionMass_le_sum_quitRates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hcoalition := quittingRootCoalitionMass_nonneg
    (quittingProfileLiveRoot reward profile time) terminal.val
  have hlive := quittingLiveMass_le_one reward profile time
  have habsorb := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    (quittingProfileLiveRoot reward profile time) terminal.val
    terminal.property
  have hrates := quittingRootAbsorptionMass_le_sum_quitRates
    (quittingProfileLiveRoot reward profile time)
  nlinarith

/-- Every finite prefix of the strictly later stage masses is bounded by joint
survival to date one. -/
theorem fablePostmark_sum_range_succ_le_liveMass_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ) :
    ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile (time + 1) terminal ≤
      quittingLiveMass reward profile 1 := by
  have htelescope :
      ∑ time ∈ Finset.range cutoff, (quittingLiveMass reward profile (time + 1) -
          quittingLiveMass reward profile (time + 1 + 1)) =
        quittingLiveMass reward profile 1 -
          quittingLiveMass reward profile (cutoff + 1) := by
    simpa using
      Finset.sum_range_sub' (fun time => quittingLiveMass reward profile (time + 1))
        cutoff
  have hterm := Finset.sum_le_sum (f := fun time =>
      quittingStageCoalitionMass reward profile (time + 1) terminal)
    (g := fun time => quittingLiveMass reward profile (time + 1) -
      quittingLiveMass reward profile (time + 1 + 1))
    (s := Finset.range cutoff)
    (fun time _ => fablePostmark_stageCoalitionMass_le_liveMass_sub_succ
      reward profile (time + 1) terminal)
  have hnonneg := quittingLiveMass_nonneg reward profile (cutoff + 1)
  rw [htelescope] at hterm
  linarith

/-! ## The later-arm floors -/

/-- Truncation: below a small immediate atom, the strictly later stage masses
carry more than `5 * mu / 8`. -/
theorem fablePostmark_tsum_succ_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ}
    (hlaw : 3 * μ / 4 < quittingAbsorbedMassLimit reward profile terminal)
    (himmediate :
      quittingStageCoalitionMass reward profile 0 terminal < μ / 8) :
    5 * μ / 8 <
      ∑' time, quittingStageCoalitionMass reward profile (time + 1) terminal := by
  have hsum := hasSum_quittingStageCoalitionMass reward profile terminal
  have hsplit := hsum.summable.tsum_eq_zero_add
  rw [hsum.tsum_eq] at hsplit
  linarith

/-- Survival floor: below a small immediate atom, joint survival to date one
exceeds `5 * mu / 8`. -/
theorem fablePostmark_liveMass_one_gt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ}
    (hlaw : 3 * μ / 4 < quittingAbsorbedMassLimit reward profile terminal)
    (himmediate :
      quittingStageCoalitionMass reward profile 0 terminal < μ / 8) :
    5 * μ / 8 < quittingLiveMass reward profile 1 := by
  have htail :=
    fablePostmark_tsum_succ_gt reward profile terminal hlaw himmediate
  have hshift : Summable (fun time =>
      quittingStageCoalitionMass reward profile (time + 1) terminal) :=
    (summable_nat_add_iff 1).mpr
      (hasSum_quittingStageCoalitionMass reward profile terminal).summable
  have hbound :
      (∑' time, quittingStageCoalitionMass reward profile (time + 1) terminal) ≤
        quittingLiveMass reward profile 1 :=
    le_of_tendsto hshift.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall fun cutoff =>
        fablePostmark_sum_range_succ_le_liveMass_one reward profile terminal cutoff)
  linarith

/-- Countable additivity supplies a finite exit cut strictly after date one
whose block carries stage mass above `mu / 2`. -/
theorem fablePostmark_exists_exitCut
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hlaw : 3 * μ / 4 < quittingAbsorbedMassLimit reward profile terminal)
    (himmediate :
      quittingStageCoalitionMass reward profile 0 terminal < μ / 8) :
    ∃ exitCut : ℕ, 1 < exitCut ∧
      μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
        quittingStageCoalitionMass reward profile time terminal := by
  have htail :=
    fablePostmark_tsum_succ_gt reward profile terminal hlaw himmediate
  have hshift : Summable (fun time =>
      quittingStageCoalitionMass reward profile (time + 1) terminal) :=
    (summable_nat_add_iff 1).mpr
      (hasSum_quittingStageCoalitionMass reward profile terminal).summable
  have hgt : μ / 2 <
      ∑' time, quittingStageCoalitionMass reward profile (time + 1) terminal := by
    linarith
  obtain ⟨cutoff, hcutoff⟩ :=
    (hshift.hasSum.tendsto_sum_nat.eventually_const_lt hgt).exists
  refine ⟨cutoff + 2, by omega, ?_⟩
  have hstep : ∑ time ∈ Finset.Ico 1 (cutoff + 2),
      quittingStageCoalitionMass reward profile time terminal =
    (∑ time ∈ Finset.Ico 1 (cutoff + 1),
      quittingStageCoalitionMass reward profile time terminal) +
        quittingStageCoalitionMass reward profile (cutoff + 1) terminal :=
    Finset.sum_Ico_succ_top (Nat.succ_le_succ (Nat.zero_le cutoff)) _
  have hrange : ∑ time ∈ Finset.Ico 1 (cutoff + 1),
      quittingStageCoalitionMass reward profile time terminal =
    ∑ time ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward profile (time + 1) terminal := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have hlast :=
    quittingStageCoalitionMass_nonneg reward profile (cutoff + 1) terminal
  rw [hstep, hrange]
  linarith

/-! ## The dichotomy -/

/-- The literal postmark block data read off one profile: a finite exit cut
strictly after date one, its stage-mass floor, the entry-reach floor at date
one, and its total marginal hazard floor. -/
def FablePostmarkBlockData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (μ : ℝ) : Prop :=
  ∃ exitCut : ℕ, 1 < exitCut ∧
    μ / 2 < (∑ time ∈ Finset.Ico 1 exitCut,
      quittingStageCoalitionMass reward profile time terminal) ∧
    5 * μ / 8 < quittingLiveMass reward profile 1 ∧
    μ / 2 < ∑ time ∈ Finset.Ico 1 exitCut,
      ∑ who, quittingRootQuitRates
        (quittingProfileLiveRoot reward profile time) who

/-- A small immediate atom under the coordinate floor produces the whole block
data, hazard floor included. -/
theorem fablePostmark_blockData_of_immediate_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hlaw : 3 * μ / 4 < quittingAbsorbedMassLimit reward profile terminal)
    (himmediate :
      quittingStageCoalitionMass reward profile 0 terminal < μ / 8) :
    FablePostmarkBlockData reward profile terminal μ := by
  obtain ⟨exitCut, hcut, hmass⟩ :=
    fablePostmark_exists_exitCut reward profile terminal hμ hlaw himmediate
  refine ⟨exitCut, hcut, hmass,
    fablePostmark_liveMass_one_gt reward profile terminal hlaw himmediate, ?_⟩
  have hhazard := Finset.sum_le_sum (f := fun time =>
      quittingStageCoalitionMass reward profile time terminal)
    (g := fun time => ∑ who, quittingRootQuitRates
      (quittingProfileLiveRoot reward profile time) who)
    (s := Finset.Ico 1 exitCut)
    (fun time _ => fablePostmark_stageCoalitionMass_le_sum_quitRates
      reward profile time terminal)
  linarith

/-- Per-profile dichotomy: under the coordinate floor `3 * mu / 4`, either the
date-zero stage mass already reaches `mu / 8`, or the profile carries the
postmark block data. -/
theorem fablePostmark_immediate_atom_or_blockData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hlaw : 3 * μ / 4 < quittingAbsorbedMassLimit reward profile terminal) :
    μ / 8 ≤ quittingStageCoalitionMass reward profile 0 terminal ∨
      FablePostmarkBlockData reward profile terminal μ := by
  by_cases himmediate :
      μ / 8 ≤ quittingStageCoalitionMass reward profile 0 terminal
  · exact Or.inl himmediate
  · exact Or.inr (fablePostmark_blockData_of_immediate_lt reward profile terminal
      hμ hlaw (not_le.mp himmediate))

/-- Sequence wrapper: from an eventual coordinate floor for one fixed nonempty
coalition, one strictly monotone extraction carries a single arm of the
dichotomy at every index. -/
theorem fablePostmark_exists_strictMono_immediate_atom_or_blockData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hlaw : ∀ᶠ index in Filter.atTop,
      3 * μ / 4 < quittingAbsorbedMassLimit reward (profiles index) terminal) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step, μ / 8 ≤
          quittingStageCoalitionMass reward (profiles (φ step)) 0 terminal) ∨
        (∀ step,
          FablePostmarkBlockData reward (profiles (φ step)) terminal μ)) := by
  classical
  by_cases hfrequent : ∃ᶠ index in Filter.atTop,
      μ / 8 ≤ quittingStageCoalitionMass reward (profiles index) 0 terminal
  · obtain ⟨φ, hmono, hφ⟩ := extraction_of_frequently_atTop hfrequent
    exact ⟨φ, hmono, Or.inl hφ⟩
  · rw [Filter.not_frequently] at hfrequent
    obtain ⟨start, hstart⟩ := Filter.eventually_atTop.mp (hlaw.and hfrequent)
    refine ⟨fun step => start + step,
      fun a b hab => Nat.add_lt_add_left hab start, Or.inr fun step => ?_⟩
    obtain ⟨hlawStep, himmediateStep⟩ :=
      hstart (start + step) (Nat.le_add_right start step)
    exact fablePostmark_blockData_of_immediate_lt reward (profiles (start + step))
      terminal hμ hlawStep (not_le.mp himmediateStep)

end GameTheory
