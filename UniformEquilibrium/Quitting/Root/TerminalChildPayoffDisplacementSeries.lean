import UniformEquilibrium.Quitting.Paths.SummableRootSurvival
import MathUE.AffineRecurrenceInfiniteUnroll
import UniformEquilibrium.Quitting.Root.NestedCapChildFixedDebtor
import UniformEquilibrium.Quitting.Root.TerminalChildPayoffDisplacementSequence

/-! # Infinite series for literal cap-child payoff displacement -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact additive correction charge in the owner-forced child
displacement recurrence is absolutely summable. -/
theorem summable_abs_terminalCapChildDisplacementCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal)) :
    Summable (fun time =>
      |(roots time owner true).toReal *
        quittingForcedContinueOwnerCorrection reward
          (fun player => quittingTerminalPayoff reward (profiles time) player)
          (roots time) owner who|) := by
  have howner :=
    summable_coordinateHazard_of_summable_marginalHazard roots owner hhazard
  have hM : 0 ≤ M :=
    (abs_nonneg (quittingTerminalPayoff reward (profiles 0) who)).trans
      (abs_quittingTerminalPayoff_le reward (profiles 0) who hreward)
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun time => ?_) (howner.mul_right (2 * M))
  rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left
    (abs_quittingForcedContinueOwnerCorrection_le_two_mul reward
      (fun player => quittingTerminalPayoff reward (profiles time) player)
      (roots time) owner who hreward
      (fun player => abs_quittingTerminalPayoff_le
        reward (profiles time) player hreward)) ENNReal.toReal_nonneg

/-- The limiting literal cap-child minus source payoff is its
depth-`R` displacement transported by the infinite forced-root product, plus
the absolutely convergent series of exact owner-correction charges. -/
theorem exists_terminalCapChildDisplacement_limit_series
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ time, profiles (time + 1) =
      quittingRootThenContinuationProfile reward (roots time) (profiles time))
    (hhazard : Summable (fun time =>
      ∑ player, (roots time player true).toReal))
    (R : ℕ) :
    let displacement := fun time =>
      quittingTerminalPayoff reward
            (quittingPureTimeCapChild reward (profiles time) owner time) who -
        quittingTerminalPayoff reward (profiles time) who
    let survival := fun time => quittingStationaryContinueMass
      (Function.update (roots time) owner (PMF.pure false))
    let charge := fun time => (roots time owner true).toReal *
      quittingForcedContinueOwnerCorrection reward
        (fun player => quittingTerminalPayoff reward (profiles time) player)
        (roots time) owner who
    ∃ limit, Tendsto displacement atTop (nhds limit) ∧
      Summable (fun offset => |charge (R + offset)|) ∧
      Summable (fun offset =>
        Math.affineProductTail survival (R + offset + 1) *
          charge (R + offset)) ∧
      limit = Math.affineProductTail survival R * displacement R +
        ∑' offset, Math.affineProductTail survival (R + offset + 1) *
          charge (R + offset) := by
  dsimp only
  let source : ℕ → Payoff ι := fun time player =>
    quittingTerminalPayoff reward (profiles time) player
  let childProfile : ℕ → (quittingGame reward).BehaviorProfile := fun time =>
    quittingPureTimeCapChild reward (profiles time) owner time
  let child : ℕ → Payoff ι := fun time player =>
    quittingTerminalPayoff reward (childProfile time) player
  let survival : ℕ → ℝ := fun time => quittingStationaryContinueMass
    (Function.update (roots time) owner (PMF.pure false))
  let charge : ℕ → ℝ := fun time => (roots time owner true).toReal *
    quittingForcedContinueOwnerCorrection reward (source time)
      (roots time) owner who
  have hsourceNext : ∀ time, source (time + 1) =
      quittingRootSuccessorPayoff reward (source time) (roots time) := by
    intro time
    funext player
    simp only [source, hnested time,
      quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  have hchildNested : ∀ time, childProfile (time + 1) =
      quittingRootThenContinuationProfile reward
        (Function.update (roots time) owner (PMF.pure false))
        (childProfile time) := by
    intro time
    dsimp only [childProfile]
    rw [hnested time]
    exact update_quittingRootThenContinuationProfile_pureTime_succ_eq
      reward (roots time) (profiles time) owner time
  have hchildNext : ∀ time, child (time + 1) =
      quittingRootSuccessorPayoff reward (child time)
        (Function.update (roots time) owner (PMF.pure false)) := by
    intro time
    funext player
    simp only [child, hchildNested time,
      quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  have hforced :=
    summable_forcedContinue_absorption_of_summable_marginalHazard
      roots owner hhazard
  have howner :=
    summable_coordinateHazard_of_summable_marginalHazard roots owner hhazard
  obtain ⟨limit, hlimit⟩ := exists_tendsto_terminalChildPayoffDisplacement
    reward source child roots owner who hreward
      (fun time player => abs_quittingTerminalPayoff_le
        reward (profiles time) player hreward)
      (fun time player => abs_quittingTerminalPayoff_le
        reward (childProfile time) player hreward)
      hsourceNext hchildNext hforced howner
  have hcharge : Summable (fun time => |charge time|) := by
    simpa [charge, source] using
      summable_abs_terminalCapChildDisplacementCharge
        reward profiles roots owner who hreward hhazard
  have hrecurrence : ∀ time,
      child (time + 1) who - source (time + 1) who =
        survival time * (child time who - source time who) + charge time := by
    intro time
    exact terminalChildPayoffDisplacement_next_eq reward
      (source time) (child time) (source (time + 1)) (child (time + 1))
      (roots time) owner who (hsourceNext time) (hchildNext time)
  have htail : ∀ start,
      Math.affineProductTail (fun offset => survival (R + offset)) start =
        Math.affineProductTail survival (R + start) := by
    intro start
    unfold Math.affineProductTail
    congr 2
    funext horizon
    apply Finset.prod_congr rfl
    intro offset _
    simp only [Nat.add_assoc]
  have hseries := Math.affineRecurrence_limit_eq_productTail_add_tsum
    (fun offset => child (R + offset) who - source (R + offset) who)
    (fun offset => survival (R + offset))
    (fun offset => charge (R + offset)) limit
    (fun offset => by simpa [Nat.add_assoc] using hrecurrence (R + offset))
    (fun offset => quittingStationaryContinueMass_nonneg _)
    (fun offset => quittingStationaryContinueMass_le_one _)
    (hcharge.comp_injective (fun _ _ h => Nat.add_left_cancel h))
    (hlimit.comp (by simpa [add_comm] using tendsto_add_atTop_nat R))
  have hchargeTail : Summable (fun offset => |charge (R + offset)|) :=
    hcharge.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have htailBounds : ∀ start,
      0 ≤ Math.affineProductTail survival start ∧
        Math.affineProductTail survival start ≤ 1 := by
    intro start
    have htendsto := Math.tendsto_affineProductTail survival
      (fun _ => quittingStationaryContinueMass_nonneg _)
      (fun _ => quittingStationaryContinueMass_le_one _) start
    constructor
    · exact ge_of_tendsto htendsto (Eventually.of_forall fun horizon =>
        Finset.prod_nonneg fun _ _ => quittingStationaryContinueMass_nonneg _)
    · exact le_of_tendsto htendsto (Eventually.of_forall fun horizon =>
        Finset.prod_le_one
          (fun _ _ => quittingStationaryContinueMass_nonneg _)
          (fun _ _ => quittingStationaryContinueMass_le_one _))
  have hweighted : Summable (fun offset =>
      Math.affineProductTail survival (R + offset + 1) *
        charge (R + offset)) := by
    apply hchargeTail.of_norm_bounded
    intro offset
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (htailBounds (R + offset + 1)).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (htailBounds _).2
  refine ⟨limit, ?_, hchargeTail, hweighted, ?_⟩
  · simpa [child, childProfile, source] using hlimit
  · rw [htail 0] at hseries
    simp only [Nat.add_zero] at hseries
    have htailSucc : ∀ offset,
        Math.affineProductTail
            (fun index => survival (R + index)) (offset + 1) =
          Math.affineProductTail survival (R + offset + 1) := by
      intro offset
      rw [htail]
      rw [show R + (offset + 1) = R + offset + 1 by omega]
    simpa [survival, charge, child, childProfile, source,
      htailSucc, Nat.add_assoc] using hseries

end GameTheory
