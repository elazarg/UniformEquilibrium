import MathUE.ProbabilityMassFunction.OptionNatEscape
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw
import UniformEquilibrium.Quitting.Paths.StoppingLawFiniteTail
import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival
import UniformEquilibrium.Quitting.Root.SelfTailClosure
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-!
# Stopping laws of reverse literal root prefixes

A reverse prefix places `roots (depth - 1)` first and `roots 0` last before a
supplied behavioral tail.  If the absorption masses of `roots` vanish, every
fixed stopping date disappears as the depth grows.  A zero-Never tail then
forces all mass to escape to later finite dates.

These are stopping-law statements.  They assert no Nash, debt, source, or
finite-player specialization.
-/

noncomputable section

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The finite word `roots (depth - 1), ..., roots 0`. -/
def quittingReversePrefixRootStack (roots : ℕ → ι → PMF Bool) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | depth + 1 => roots depth :: quittingReversePrefixRootStack roots depth

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingReversePrefixRootStack_zero (roots : ℕ → ι → PMF Bool) :
    quittingReversePrefixRootStack roots 0 = [] := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingReversePrefixRootStack_succ
    (roots : ℕ → ι → PMF Bool) (depth : ℕ) :
    quittingReversePrefixRootStack roots (depth + 1) =
      roots depth :: quittingReversePrefixRootStack roots depth := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingReversePrefixRootStack_length
    (roots : ℕ → ι → PMF Bool) (depth : ℕ) :
    (quittingReversePrefixRootStack roots depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [quittingReversePrefixRootStack, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem quittingReversePrefixRootStack_getElem
    (roots : ℕ → ι → PMF Bool) (depth time : ℕ) (htime : time < depth) :
    (quittingReversePrefixRootStack roots depth)[time]'(by
      simpa using htime) =
      roots (depth - time - 1) := by
  induction depth generalizing time with
  | zero => omega
  | succ depth ih =>
      cases time with
      | zero => simp [quittingReversePrefixRootStack]
      | succ time =>
          simp only [quittingReversePrefixRootStack, List.getElem_cons_succ]
          rw [ih time (by omega)]
          congr 2
          omega

/-- The executable profile consisting of a reverse finite root prefix and a
depth-dependent complete behavioral tail. -/
def quittingReversePrefixProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingReversePrefixRootStack roots depth) (tails depth)

omit [DecidableEq ι] in
private theorem quittingBehaviorLiveHazard_rootThen_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorLiveHazard reward
        ((quittingRootThenContinuationProfile reward root continuation) who) 0 =
      root who := rfl

omit [DecidableEq ι] in
private theorem quittingBehaviorLiveHazard_rootThen_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingBehaviorLiveHazard reward
        ((quittingRootThenContinuationProfile reward root continuation) who)
        (time + 1) =
      quittingBehaviorLiveHazard reward (continuation who) time := by
  rfl

omit [DecidableEq ι] in
private theorem quittingHazardSurvival_rootThen_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (cutoff : ℕ) :
    quittingHazardSurvival
        (quittingBehaviorLiveHazard reward
          ((quittingRootThenContinuationProfile reward root continuation) who))
        (cutoff + 1) =
      (root who false).toReal *
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward (continuation who)) cutoff := by
  unfold quittingHazardSurvival
  rw [Math.survivalProduct_succ_left]
  congr 1
  unfold Math.survivalProduct
  apply Finset.prod_congr rfl
  intro offset hoffset
  rw [show 0 + 1 + offset = offset + 1 by omega,
    show 0 + offset = offset by omega]
  exact congrArg ENNReal.toReal
    (congrArg (fun law : PMF Bool => law false)
      (quittingBehaviorLiveHazard_rootThen_succ
        reward root continuation who offset))

omit [DecidableEq ι] in
private theorem quittingHazardNeverMass_rootThen
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward
          ((quittingRootThenContinuationProfile reward root continuation) who)) =
      (root who false).toReal *
        quittingHazardNeverMass
          (quittingBehaviorLiveHazard reward (continuation who)) := by
  let openingHazard := quittingBehaviorLiveHazard reward
    ((quittingRootThenContinuationProfile reward root continuation) who)
  let tailHazard := quittingBehaviorLiveHazard reward (continuation who)
  have hopen : Tendsto
      (fun cutoff => quittingHazardSurvival openingHazard (cutoff + 1)) atTop
      (𝓝 (quittingHazardNeverMass openingHazard)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_quittingHazardSurvival_neverMass openingHazard)
  have htail : Tendsto
      (fun cutoff => (root who false).toReal *
        quittingHazardSurvival tailHazard cutoff) atTop
      (𝓝 ((root who false).toReal * quittingHazardNeverMass tailHazard)) :=
    tendsto_const_nhds.mul
      (tendsto_quittingHazardSurvival_neverMass tailHazard)
  apply tendsto_nhds_unique hopen
  apply htail.congr'
  exact Eventually.of_forall fun cutoff => by
    simpa only [openingHazard, tailHazard] using
      (quittingHazardSurvival_rootThen_succ
        reward root continuation who cutoff).symm

omit [DecidableEq ι] in
/-- Never-stopping mass is transported through a literal root word by the
product of the selected player's own Continue probabilities. -/
theorem quittingBehaviorStoppingLaw_none_literalRootStackProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingBehaviorStoppingLaw reward
        ((quittingLiteralRootStackProfile reward roots terminal) who) none).toReal =
      quittingLiteralRootStackOwnSurvival roots who *
        (quittingBehaviorStoppingLaw reward (terminal who) none).toReal := by
  induction roots with
  | nil => simp [quittingLiteralRootStackOwnSurvival]
  | cons root roots ih =>
      rw [quittingLiteralRootStackProfile_cons]
      simp only [quittingBehaviorStoppingLaw_none_toReal,
        quittingHazardNeverMass_rootThen]
      change (root who false).toReal *
          quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward
              ((quittingLiteralRootStackProfile reward roots terminal) who)) =
        ((root who false).toReal *
          quittingLiteralRootStackOwnSurvival roots who) *
          quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward (terminal who))
      have ih' :
          quittingHazardNeverMass
              (quittingBehaviorLiveHazard reward
                ((quittingLiteralRootStackProfile reward roots terminal) who)) =
            quittingLiteralRootStackOwnSurvival roots who *
              quittingHazardNeverMass
                (quittingBehaviorLiveHazard reward (terminal who)) := by
        simpa only [quittingBehaviorStoppingLaw_none_toReal] using ih
      rw [ih']
      ring

omit [DecidableEq ι] in
/-- At a date inside the reverse prefix, the live root is the corresponding
root of the original sequence, read in decreasing order. -/
theorem quittingProfileLiveRoot_reversePrefixProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (depth time : ℕ) (htime : time < depth) :
    quittingProfileLiveRoot reward
        (quittingReversePrefixProfile reward roots tails depth) time =
      roots (depth - time - 1) := by
  rw [quittingReversePrefixProfile,
    quittingProfileLiveRoot_literalRootStackProfile_eq_getElem]
  exact quittingReversePrefixRootStack_getElem roots depth time htime

omit [DecidableEq ι] in
/-- The probability of stopping at a date within a reverse prefix is bounded
by the absorption mass of the root displayed at that date. -/
theorem quittingReversePrefixStoppingLaw_finiteCoordinate_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (who : ι) (depth time : ℕ) (htime : time < depth) :
    (quittingBehaviorStoppingLaw reward
        ((quittingReversePrefixProfile reward roots tails depth) who)
        (some time)).toReal ≤
      quittingRootAbsorptionMass (roots (depth - time - 1)) := by
  rw [quittingBehaviorStoppingLaw_some_toReal,
    quittingHazardStopMass_eq_survival_mul_stop]
  have hsurvival0 := quittingHazardSurvival_nonneg
    (quittingBehaviorLiveHazard reward
      ((quittingReversePrefixProfile reward roots tails depth) who)) time
  have hsurvival1 := quittingHazardSurvival_le_one
    (quittingBehaviorLiveHazard reward
      ((quittingReversePrefixProfile reward roots tails depth) who)) time
  have hquit0 :
      0 ≤ (roots (depth - time - 1) who true).toReal :=
    ENNReal.toReal_nonneg
  have hlive := congrFun
    (quittingProfileLiveRoot_reversePrefixProfile_eq
      reward roots tails depth time htime) who
  change quittingHazardSurvival _ time *
      (quittingProfileLiveRoot reward
        (quittingReversePrefixProfile reward roots tails depth) time who
        true).toReal ≤ _
  rw [hlive]
  exact (mul_le_of_le_one_left hquit0 hsurvival1).trans
    (quittingQuitProbability_le_absorptionMass
      (roots (depth - time - 1)) who)

omit [DecidableEq ι] in
/-- If reverse-prefix root absorption tends to zero, every fixed stopping
date of the resulting profile sequence has asymptotically zero mass. -/
theorem quittingReversePrefix_finiteCoordinate_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorption : Tendsto
      (fun index => quittingRootAbsorptionMass (roots index)) atTop (𝓝 0))
    (time : ℕ) :
    Tendsto
      (fun depth =>
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward roots tails depth) who)
          (some time)).toReal)
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  · filter_upwards [eventually_gt_atTop time] with depth hdepth
    exact quittingReversePrefixStoppingLaw_finiteCoordinate_le
      reward roots tails who depth time hdepth
  · change Tendsto
      ((fun index => quittingRootAbsorptionMass (roots index)) ∘
        fun depth => depth - (time + 1)) atTop (𝓝 0)
    exact habsorption.comp (Filter.tendsto_sub_atTop_nat (time + 1))

omit [DecidableEq ι] in
/-- Every fixed finite head of a reverse-prefix stopping law vanishes when
the root absorption masses tend to zero. -/
theorem quittingReversePrefix_finiteHead_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorption : Tendsto
      (fun index => quittingRootAbsorptionMass (roots index)) atTop (𝓝 0))
    (horizon : ℕ) :
    Tendsto
      (fun depth => stoppingLawFiniteHeadMass
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward roots tails depth) who)) horizon)
      atTop (𝓝 0) := by
  simpa [stoppingLawFiniteHeadMass] using
    tendsto_finsetSum (Finset.range (horizon + 1)) fun time _ =>
      quittingReversePrefix_finiteCoordinate_tendsto_zero
        reward roots tails who habsorption time

omit [DecidableEq ι] in
/-- A zero-Never tail stays zero-Never after every finite reverse literal
prefix. -/
theorem quittingReversePrefixStoppingLaw_none_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (htailNever : ∀ depth,
      (quittingBehaviorStoppingLaw reward (tails depth who) none).toReal = 0)
    (depth : ℕ) :
    (quittingBehaviorStoppingLaw reward
        ((quittingReversePrefixProfile reward roots tails depth) who)
        none).toReal = 0 := by
  rw [quittingReversePrefixProfile,
    quittingBehaviorStoppingLaw_none_literalRootStackProfile_eq,
    htailNever]
  ring

omit [DecidableEq ι] in
/-- Under vanishing root absorption and zero-Never tails, all stopping mass
eventually lies at finite dates beyond any fixed cutoff. -/
theorem quittingReversePrefix_lateFiniteMass_tendsto_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorption : Tendsto
      (fun index => quittingRootAbsorptionMass (roots index)) atTop (𝓝 0))
    (htailNever : ∀ depth,
      (quittingBehaviorStoppingLaw reward (tails depth who) none).toReal = 0)
    (horizon : ℕ) :
    Tendsto
      (fun depth => stoppingLawLateFiniteMass
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward roots tails depth) who)) horizon)
      atTop (𝓝 1) := by
  have hnone : Tendsto
      (fun depth =>
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward roots tails depth) who)
          none).toReal)
      atTop (𝓝 0) := by
    simpa only [quittingReversePrefixStoppingLaw_none_eq_zero
      reward roots tails who htailNever] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hhead := quittingReversePrefix_finiteHead_tendsto_zero
    reward roots tails who habsorption horizon
  simpa [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead] using
    tendsto_const_nhds.sub hnone |>.sub hhead

omit [DecidableEq ι] in
/-- A zero-Never reverse-prefix family becomes maximally separated in
general total variation from every fixed stopping law. -/
theorem quittingReversePrefix_pmfGeneralTV_tendsto_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tails : ℕ → (quittingGame reward).BehaviorProfile) (who : ι)
    (habsorption : Tendsto
      (fun index => quittingRootAbsorptionMass (roots index)) atTop (𝓝 0))
    (htailNever : ∀ depth,
      (quittingBehaviorStoppingLaw reward (tails depth who) none).toReal = 0)
    (fixed : PMF (Option ℕ)) :
    Tendsto
      (fun depth => Math.Probability.pmfGeneralTV
        (quittingBehaviorStoppingLaw reward
          ((quittingReversePrefixProfile reward roots tails depth) who)) fixed)
      atTop (𝓝 1) := by
  exact
    pmfGeneralTV_tendsto_one_of_finiteCoordinates_tendsto_zero_of_never_eq_zero
      (fun depth => quittingBehaviorStoppingLaw reward
        ((quittingReversePrefixProfile reward roots tails depth) who))
      fixed
      (quittingReversePrefix_finiteCoordinate_tendsto_zero
        reward roots tails who habsorption)
      (quittingReversePrefixStoppingLaw_none_eq_zero
        reward roots tails who htailNever)

end GameTheory
