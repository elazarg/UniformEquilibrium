import MathUE.ExponentialExcessScale
import UniformEquilibrium.Diagnostics.Quitting.StationaryQuitNowSegment
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumTwoCutPaidSplice

/-!
# The stationary Quit-now installation returns to its off-minimum source

An opening root followed by a positive Quit0 installation has literal entry
and exit cuts one and two. A positive source excess determines a small enough
positive hazard floor that the existing two-cut theorem's off-minimum arm is
already satisfied. This pointwise construction does not require root Nash
or convergence of the prefixed profiles to the minimum fibre. It supplies
neither a paid-splice conclusion nor a source return at a minimum.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One opening root, one installation row, and the original stationary tail. -/
def quittingStationaryQuitNowSegmentTwoCutRoots
    (root openingRoot : ι → PMF Bool) (owner : ι)
    (parameter : Set.Icc (0 : ℝ) 1) : ℕ → ι → PMF Bool
  | 0 => openingRoot
  | 1 => quittingStationaryQuitNowSegmentRoot root owner parameter
  | _ + 2 => root

theorem quittingStationaryQuitNowSegmentTwoCutRoots_exitProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root openingRoot : ι → PMF Bool) (owner : ι)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingRootSequenceProfile reward
        (quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter) 2 =
      quittingStationaryProfile reward root := by
  funext who time history
  change quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter
    (2 + time) who = root who
  rw [Nat.add_comm 2 time]
  rfl

theorem quittingStationaryQuitNowSegmentTwoCutRoots_entryProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root openingRoot : ι → PMF Bool) (owner : ι)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingRootSequenceProfile reward
        (quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter) 1 =
      quittingStationaryQuitNowSegment reward root owner parameter := by
  rw [quittingRootSequenceProfile_eq_rootThenContinuation]
  change quittingRootThenContinuationProfile reward
      (quittingStationaryQuitNowSegmentRoot root owner parameter)
      (quittingRootSequenceProfile reward
        (quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter) 2) = _
  rw [quittingStationaryQuitNowSegmentTwoCutRoots_exitProfile]
  rfl

theorem quittingStationaryQuitNowSegmentTwoCutRoots_parentProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root openingRoot : ι → PMF Bool) (owner : ι)
    (parameter : Set.Icc (0 : ℝ) 1) :
    quittingRootSequenceProfile reward
        (quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter) 0 =
      quittingRootThenContinuationProfile reward openingRoot
        (quittingStationaryQuitNowSegment reward root owner parameter) := by
  rw [quittingRootSequenceProfile_eq_rootThenContinuation]
  change quittingRootThenContinuationProfile reward openingRoot
      (quittingRootSequenceProfile reward
        (quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter) 1) = _
  rw [quittingStationaryQuitNowSegmentTwoCutRoots_entryProfile]

/-- The literal installation supplies a reached two-cut block whose exit is
the original source and already satisfies the quantitative off-minimum arm.
The conclusion does not exclude simultaneous existence of a paid splice. -/
theorem exists_quittingStationaryQuitNowSegmentTwoCut_offMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root openingRoot : ι → PMF Bool) (owner : ι)
    (parameter : Set.Icc (0 : ℝ) 1) (hparameter : 0 < parameter.val)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤ quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    {excess reachFloor : ℝ} (hexcess : 0 < excess) (hreach : 0 < reachFloor)
    (hsource : quittingTerminalSemanticDebtSum minimum + excess ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (quittingStationaryProfile reward root)))
    (hopening : reachFloor ≤ quittingStationaryContinueMass openingRoot) :
    ∃ block : QuittingUniformlyReachedPostMarkTwoCutBlock reward,
      block.roots = quittingStationaryQuitNowSegmentTwoCutRoots
          root openingRoot owner parameter ∧
      block.markedRow = 0 ∧ block.entryCut = 1 ∧ block.exitCut = 2 ∧
      block.minimum = minimum ∧ block.reachFloor = reachFloor ∧
      block.hazardFloor = Math.exponentialExcessScale parameter.val excess
          (quittingTerminalSemanticDebtSum minimum) ∧
      block.parentProfile = quittingRootThenContinuationProfile reward openingRoot
          (quittingStationaryQuitNowSegment reward root owner parameter) ∧
      block.entryProfile = quittingStationaryQuitNowSegment reward root owner parameter ∧
      block.exitPair = quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward root) ∧
      quittingTerminalSemanticDebtSum block.minimum +
          (Real.exp block.hazardFloor - 1) / 2 *
            quittingTerminalSemanticDebtSum block.minimum ≤
        quittingTerminalSemanticDebtSum block.exitPair := by
  let scale := Math.exponentialExcessScale parameter.val excess
    (quittingTerminalSemanticDebtSum minimum)
  have hscale : 0 < scale :=
    Math.exponentialExcessScale_pos hparameter hexcess hminimumPos
  have hscaleLe : scale ≤ parameter.val :=
    Math.exponentialExcessScale_le_rowScale _ _ _
  have hthreshold : (Real.exp scale - 1) / 2 *
      quittingTerminalSemanticDebtSum minimum ≤ excess :=
    Math.exponentialExcessScale_threshold_le hexcess hminimumPos
  let block : QuittingUniformlyReachedPostMarkTwoCutBlock reward := {
    roots := quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter
    entryCut := 1
    exitCut := 2
    entryCut_lt_exitCut := by decide
    minimum := minimum
    minimum_mem := hminimumMem
    minimum_le := hminimumLe
    minimum_pos := hminimumPos
    markedRow := 0
    markedRow_lt_entryCut := Nat.zero_lt_one
    hazardFloor := scale
    hazardFloor_pos := hscale
    totalMarginalHazard_ge := by
      simpa only [Nat.reduceSub, Finset.sum_range_one, Nat.add_zero,
        quittingStationaryQuitNowSegmentTwoCutRoots] using
        hscaleLe.trans (quittingStationaryQuitNowSegmentRoot_hazard_ge root owner parameter)
    reachFloor := reachFloor
    reachFloor_pos := hreach
    entryReach_ge := by
      rw [quittingJointSurvivalWeight_succ]
      simpa only [quittingJointSurvivalWeight_zero_fuel, Nat.zero_add, one_mul,
        quittingStationaryQuitNowSegmentTwoCutRoots] using hopening }
  have hexit : block.exitPair = quittingTerminalSemanticPair reward
      (quittingStationaryProfile reward root) := by
    change quittingTerminalSemanticPair reward
      (quittingRootSequenceProfile reward
        (quittingStationaryQuitNowSegmentTwoCutRoots root openingRoot owner parameter) 2) = _
    rw [quittingStationaryQuitNowSegmentTwoCutRoots_exitProfile]
  refine ⟨block, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, hexit, ?_⟩
  · exact quittingStationaryQuitNowSegmentTwoCutRoots_parentProfile
      reward root openingRoot owner parameter
  · exact quittingStationaryQuitNowSegmentTwoCutRoots_entryProfile
      reward root openingRoot owner parameter
  · rw [hexit]
    change quittingTerminalSemanticDebtSum minimum +
      (Real.exp scale - 1) / 2 * quittingTerminalSemanticDebtSum minimum ≤ _
    linarith

end GameTheory
