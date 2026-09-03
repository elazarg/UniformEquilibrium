import UniformEquilibrium.Quitting.AbsorptionPath.HomogeneousContinuousPath
import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence

/-!
# Endpoint-unbounded weak-limit counterexample

The project `AbsorptionPath` predicate currently carries a lower clock bound
but no total-mass upper bound.  It therefore permits an additional jump at
clock one: the normalized jump equation divides by `1 - 1`, so an
all-Continue root witnesses any endpoint jump.  The weak-convergence predicate
ignores jumps of the limit, while `absorptionPathPayoff` still reads the
endpoint.  This file turns that interface mismatch into a concrete
counterexample.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath.EndpointUnboundedWeakLimitCounterexample

open Filter Set
open scoped Topology
open GameTheory

private def baseWeight : stdSimplex ℝ Bool := stdSimplex.pure false

private def baseCadlagPath : CadlagPath (ι := Bool) :=
  linearSingletonCadlagPath baseWeight

private def addedCoalition : {S : Finset Bool // S.Nonempty} :=
  quittingProjectiveSingletonTerminal true

@[simp] private theorem baseCadlagPath_value_addedCoalition (time : ℝ) :
    baseCadlagPath.value time addedCoalition = 0 := by
  change time * singletonCoalitionDistribution baseWeight addedCoalition = 0
  rw [show addedCoalition = quittingProjectiveSingletonTerminal true by rfl,
    singletonCoalitionDistribution_singleton]
  have hweight : baseWeight true = 0 := by
    rfl
  rw [hweight, mul_zero]

private def endpointSpikeCadlagPath : CadlagPath (ι := Bool) where
  value time coalition :=
    baseCadlagPath.value time coalition +
      if time = 1 ∧ coalition = addedCoalition then 1 else 0
  leftValue := baseCadlagPath.leftValue
  value_mem := by
    intro time htime coalition
    by_cases hcoalition : coalition = addedCoalition
    · subst coalition
      rw [baseCadlagPath_value_addedCoalition]
      by_cases htimeOne : time = 1
      · simp [htimeOne]
      · simp [htimeOne]
    · simp only [hcoalition, and_false, ↓reduceIte, add_zero]
      exact baseCadlagPath.value_mem time htime coalition
  monotone := by
    intro coalition first hfirst second hsecond hle
    by_cases hcoalition : coalition = addedCoalition
    · subst coalition
      change (baseCadlagPath.value first addedCoalition +
          if first = 1 ∧ addedCoalition = addedCoalition then 1 else 0) ≤
        baseCadlagPath.value second addedCoalition +
          if second = 1 ∧ addedCoalition = addedCoalition then 1 else 0
      rw [baseCadlagPath_value_addedCoalition,
        baseCadlagPath_value_addedCoalition]
      simp only [and_true, zero_add]
      by_cases hfirstOne : first = 1
      · subst first
        have hsecondOne : second = 1 := le_antisymm hsecond.2 hle
        subst second
        simp
      · rw [if_neg hfirstOne]
        by_cases hsecondOne : second = 1
        · rw [if_pos hsecondOne]
          norm_num
        · rw [if_neg hsecondOne]
    · simp only [hcoalition, and_false, ↓reduceIte, add_zero]
      exact baseCadlagPath.monotone coalition hfirst hsecond hle
  right_continuous := by
    intro coalition time htime
    by_cases htimeOne : time = 1
    · subst time
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with later hlater
      have hlaterOne : later = 1 := by
        exact le_antisymm hlater.2 hlater.1
      simp [hlaterOne]
    · have htimeLt : time < 1 := lt_of_le_of_ne htime.2 htimeOne
      have heq : Filter.EventuallyEq (nhdsWithin time (Icc time 1))
          (fun later => baseCadlagPath.value later coalition)
          (fun later => baseCadlagPath.value later coalition +
            if later = 1 ∧ coalition = addedCoalition then 1 else 0) := by
        filter_upwards [mem_inf_of_left (Iio_mem_nhds htimeLt)] with later hlater
        have hlaterOne : later ≠ 1 := ne_of_lt hlater
        simp [hlaterOne]
      simpa only [htimeOne, false_and, ↓reduceIte, add_zero] using
        (baseCadlagPath.right_continuous coalition time htime).congr' heq
  left_limit := by
    intro coalition time htime
    have heq : Filter.EventuallyEq (nhdsWithin time (Icc 0 time \ {time}))
        (fun later => baseCadlagPath.value later coalition)
        (fun later => baseCadlagPath.value later coalition +
          if later = 1 ∧ coalition = addedCoalition then 1 else 0) := by
      filter_upwards [self_mem_nhdsWithin] with later hlater
      have hlaterLt : later < 1 :=
        lt_of_le_of_ne (hlater.1.2.trans htime.2) fun heq => by
          have htimeOne : time = 1 := le_antisymm htime.2 (heq ▸ hlater.1.2)
          exact hlater.2 (heq.trans htimeOne.symm)
      simp [ne_of_lt hlaterLt]
    exact (baseCadlagPath.left_limit coalition time htime).congr' heq
  left_zero := baseCadlagPath.left_zero

@[simp] private theorem pathTotal_endpointSpikeCadlagPath (time : ℝ) :
    pathTotal endpointSpikeCadlagPath time =
      time + if time = 1 then 1 else 0 := by
  rw [pathTotal]
  simp_rw [endpointSpikeCadlagPath]
  rw [Finset.sum_add_distrib]
  change pathTotal baseCadlagPath time +
      (∑ coalition, if time = 1 ∧ coalition = addedCoalition then 1 else 0) = _
  rw [show pathTotal baseCadlagPath time = time by
    exact pathTotal_linearSingletonCadlagPath baseWeight time]
  by_cases htimeOne : time = 1
  · subst time
    simp
  · simp [htimeOne]

@[simp] private theorem pathJump_endpointSpikeCadlagPath
    (time : ℝ) (coalition : {S : Finset Bool // S.Nonempty}) :
    pathJump endpointSpikeCadlagPath time coalition =
      if time = 1 ∧ coalition = addedCoalition then 1 else 0 := by
  simp [pathJump, endpointSpikeCadlagPath, baseCadlagPath,
    linearSingletonCadlagPath]

private theorem pathJumps_endpointSpikeCadlagPath :
    pathJumps endpointSpikeCadlagPath = {1} := by
  ext time
  constructor
  · intro htime
    obtain ⟨_, coalition, hcoalition⟩ := htime
    by_contra htimeOne
    have htimeNe : time ≠ 1 := by simpa using htimeOne
    simp [pathJump_endpointSpikeCadlagPath, htimeNe] at hcoalition
  · intro htime
    have htimeOne : time = 1 := by simpa using htime
    subst time
    refine ⟨by norm_num, addedCoalition, ?_⟩
    simp

private theorem pathTimes_endpointSpikeCadlagPath :
    pathTimes endpointSpikeCadlagPath = Ico 0 1 := by
  ext time
  constructor
  · rintro ⟨htime, htotal⟩
    refine ⟨htime.1, ?_⟩
    by_contra hnot
    have htimeOne : time = 1 := le_antisymm htime.2 (not_lt.mp hnot)
    subst time
    norm_num at htotal
  · intro htime
    refine ⟨⟨htime.1, htime.2.le⟩, ?_⟩
    simp [ne_of_lt htime.2]

private theorem pathRightDerivative_endpointSpike_eq_base
    {time : ℝ} (htime : time < 1)
    (coalition : {S : Finset Bool // S.Nonempty}) :
    pathRightDerivative endpointSpikeCadlagPath time coalition =
      pathRightDerivative baseCadlagPath time coalition := by
  unfold pathRightDerivative
  apply Filter.liminf_congr
  filter_upwards [self_mem_nhdsWithin] with later hlater
  simp [endpointSpikeCadlagPath, ne_of_lt hlater.2, ne_of_lt htime]

private theorem isAbsorptionPath_endpointSpikeCadlagPath :
    IsAbsorptionPath endpointSpikeCadlagPath := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro time htime
    by_cases htimeOne : time = 1
    · subst time
      norm_num
    · simp [htimeOne]
  · intro time htime
    have hcovered : time ∈
        pathJumps endpointSpikeCadlagPath ∪
          pathTimes endpointSpikeCadlagPath := by
      rw [pathJumps_endpointSpikeCadlagPath,
        pathTimes_endpointSpikeCadlagPath]
      by_cases htimeOne : time = 1
      · exact Or.inl (by simp [htimeOne])
      · exact Or.inr ⟨htime.1.1,
          lt_of_le_of_ne htime.1.2 htimeOne⟩
    exact (htime.2 hcovered).elim
  · intro time htime
    rw [pathJumps_endpointSpikeCadlagPath] at htime
    have htimeOne : time = 1 := by simpa using htime
    subst time
    refine ⟨quittingAllContinueRoot, ?_⟩
    intro coalition
    have hmass : quittingRootCoalitionMass
        (quittingAllContinueRoot : Bool → PMF Bool) coalition.1 = 0 := by
      obtain ⟨player, hplayer⟩ := coalition.2
      have hrate : quittingRootQuitRates
          (quittingAllContinueRoot : Bool → PMF Bool) player = 0 := by
        simp [quittingRootQuitRates, quittingAllContinueRoot]
      unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
      rw [Finset.prod_eq_zero hplayer hrate, zero_mul]
    rw [hmass]
    simp
  · intro time htime htimeOne coalition hderivative
    have htimeLt : time < 1 := by
      rw [pathTimes_endpointSpikeCadlagPath] at htime
      exact htime.2
    have hbaseDerivative :
        pathRightDerivative baseCadlagPath time coalition ≠ 0 := by
      rwa [pathRightDerivative_endpointSpike_eq_base htimeLt coalition]
        at hderivative
    have hbaseTime : time ∈ pathTimes baseCadlagPath := by
      rw [show baseCadlagPath = linearSingletonCadlagPath baseWeight by rfl,
        pathTimes_linearSingletonCadlagPath]
      exact htime.1
    exact (isAbsorptionPath_linearSingletonCadlagPath baseWeight).2.2.2
      time hbaseTime htimeOne coalition hbaseDerivative

private def endpointSpikeAbsorptionPath : AbsorptionPath (ι := Bool) :=
  ⟨endpointSpikeCadlagPath, isAbsorptionPath_endpointSpikeCadlagPath⟩

private def baseAbsorptionPath : AbsorptionPath (ι := Bool) :=
  linearSingletonAbsorptionPath baseWeight

private def reward
    (coalition : {S : Finset Bool // S.Nonempty}) (player : Bool) : ℝ :=
  if player = false ∧ coalition = addedCoalition then 1 else 0

@[simp] private theorem reward_baseOwnerSolo :
    reward (quittingProjectiveSingletonTerminal false) false = 0 := by
  simp [reward, addedCoalition, quittingProjectiveSingletonTerminal]

private theorem absorptionPathPayoff_base_false
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) (htimeOne : time ≠ 1) :
    absorptionPathPayoff reward baseAbsorptionPath time false = 0 := by
  change absorptionPathPayoff reward
      (linearSingletonAbsorptionPath baseWeight) time false = 0
  have hpayoff := congrFun
    (absorptionPathPayoff_linearSingletonAbsorptionPath
      baseWeight reward htime htimeOne) false
  rw [hpayoff]
  have hweightTrue : baseWeight true = 0 := by rfl
  simp [reward, addedCoalition, quittingProjectiveSingletonTerminal,
    hweightTrue]

private theorem base_player_false_zeroPerfect :
    IsPlayerSequentiallyPerfectAbsorptionPath reward
      baseAbsorptionPath false 0 := by
  constructor
  · intro time htime
    change time ∈ pathJumps (linearSingletonCadlagPath baseWeight) at htime
    rw [pathJumps_linearSingletonCadlagPath] at htime
    exact htime.elim
  · intro time htime htimeOne
    have htimeMem : time ∈ Icc (0 : ℝ) 1 := by
      change time ∈ pathTimes (linearSingletonCadlagPath baseWeight) at htime
      rw [pathTimes_linearSingletonCadlagPath] at htime
      exact htime
    rw [absorptionPathPayoff_base_false htimeMem htimeOne]
    constructor
    · simp [reward, addedCoalition, quittingProjectiveSingletonTerminal]
    · intro _
      simp [reward, addedCoalition, quittingProjectiveSingletonTerminal]

private theorem weaklyConverges_base_to_endpointSpike :
    WeaklyConvergesAbsorptionPaths
      (fun _ => baseAbsorptionPath) endpointSpikeAbsorptionPath := by
  intro time _htime hnotJump
  have htimeOne : time ≠ 1 := by
    intro htimeOne
    apply hnotJump
    change time ∈ pathJumps endpointSpikeCadlagPath
    rw [pathJumps_endpointSpikeCadlagPath, htimeOne]
    simp
  have heq :
      (fun coalition => endpointSpikeCadlagPath.value time coalition) =
        fun coalition => baseCadlagPath.value time coalition := by
    funext coalition
    simp [endpointSpikeCadlagPath, htimeOne]
  change Tendsto (fun _ coalition => baseCadlagPath.value time coalition)
    atTop (𝓝 fun coalition => endpointSpikeCadlagPath.value time coalition)
  rw [heq]
  exact tendsto_const_nhds

private theorem pathRightDerivative_endpointSpike_false_zero :
    pathRightDerivative endpointSpikeCadlagPath 0
        (quittingProjectiveSingletonTerminal false) = 1 := by
  rw [pathRightDerivative_endpointSpike_eq_base (by norm_num)]
  letI : NeBot (nhdsWithin (0 : ℝ) (Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot (by norm_num)
  unfold pathRightDerivative baseCadlagPath linearSingletonCadlagPath
  have hquotient : ∀ᶠ later in nhdsWithin (0 : ℝ) (Ioo 0 1),
      (later * singletonCoalitionDistribution baseWeight
            (quittingProjectiveSingletonTerminal false) -
          0 * singletonCoalitionDistribution baseWeight
            (quittingProjectiveSingletonTerminal false)) /
          (later - 0) = 1 := by
    filter_upwards [self_mem_nhdsWithin] with later hlater
    rw [singletonCoalitionDistribution_singleton]
    have hweight : baseWeight false = 1 := by rfl
    rw [hweight]
    field_simp [ne_of_gt hlater.1]
  rw [Filter.liminf_congr hquotient, Filter.liminf_const]

private theorem absorptionPathPayoff_endpointSpike_zero_false :
    absorptionPathPayoff reward endpointSpikeAbsorptionPath 0 false = 1 := by
  rw [absorptionPathPayoff, if_pos (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
  change (if pathTotal endpointSpikeCadlagPath 0 < 1 then fun who =>
      (∑ coalition,
        (endpointSpikeCadlagPath.value 1 coalition -
          endpointSpikeCadlagPath.value 0 coalition) * reward coalition who) /
            (1 - pathTotal endpointSpikeCadlagPath 0) else 0) false = 1
  rw [if_pos (by simp : pathTotal endpointSpikeCadlagPath 0 < 1)]
  rw [pathTotal_endpointSpikeCadlagPath]
  norm_num
  simp [endpointSpikeCadlagPath, reward]

private theorem endpointSpike_not_player_false_zeroPerfect :
    ¬IsPlayerSequentiallyPerfectAbsorptionPath reward
      endpointSpikeAbsorptionPath false 0 := by
  intro hperfect
  have hcontinuous := hperfect.2 0 (by
    change (0 : ℝ) ∈ pathTimes endpointSpikeCadlagPath
    rw [pathTimes_endpointSpikeCadlagPath]
    norm_num) (by norm_num)
  have hderivative : pathRightDerivative endpointSpikeCadlagPath 0
      (quittingProjectiveSingletonTerminal false) > 0 := by
    rw [pathRightDerivative_endpointSpike_false_zero]
    norm_num
  have hupper := hcontinuous.2 hderivative
  rw [absorptionPathPayoff_endpointSpike_zero_false] at hupper
  simp only [add_zero] at hupper
  change (1 : ℝ) ≤ reward
      (quittingProjectiveSingletonTerminal false) false at hupper
  rw [reward_baseOwnerSolo] at hupper
  norm_num at hupper

/-- Unrestricted playerwise sequential perfection is not closed under the
current endpoint-unbounded absorption-path interface.  The missing total-mass
upper bound permits the endpoint spike used by this counterexample. -/
theorem playerSequentialPerfection_not_closedUnderWeakLimits_without_totalMassUpperBound :
    ¬PlayerSequentialPerfectionClosedUnderWeakLimits reward := by
  intro hclosed
  have hlimit := hclosed (fun _ => 0) (fun _ => baseAbsorptionPath)
    endpointSpikeAbsorptionPath false
    (by simp) tendsto_const_nhds weaklyConverges_base_to_endpointSpike
    (fun _ => base_player_false_zeroPerfect)
  exact endpointSpike_not_player_false_zeroPerfect hlimit

/-- Some two-player reward table violates unrestricted weak-limit closedness
when absorption paths do not carry the total-mass upper bound. -/
theorem exists_reward_not_closedUnderWeakLimits_without_totalMassUpperBound :
    ∃ reward : {S : Finset Bool // S.Nonempty} → Payoff Bool,
      ¬PlayerSequentialPerfectionClosedUnderWeakLimits reward := by
  exact ⟨reward,
    playerSequentialPerfection_not_closedUnderWeakLimits_without_totalMassUpperBound⟩

end GameTheory.QuittingAbsorptionPath.EndpointUnboundedWeakLimitCounterexample
