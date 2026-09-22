import MathUE.Topology.SourceOmegaChain
import UniformEquilibrium.Quitting.ControllerTester.ForwardLedger
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Quitting.Paths.JointSurvivalSelection
import UniformEquilibrium.Quitting.Paths.StrictDeficitFiniteWordRates

/-! # Source-faithful reverse-prefix limits of strict-deficit exact words -/

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability Math.Topology
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def strictDeficitWordProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (quittingStrictDeficitExactWords reward gap depth)
    (quittingAlwaysContinueProfile reward)

def quittingStrictDeficitExactWordValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth : ℕ) : Payoff ι :=
  fun who => quittingTerminalPayoff reward
    (strictDeficitWordProfile reward gap depth) who

def quittingStrictDeficitExactWordNextRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth : ℕ) : ι → PMF Bool :=
  quittingStrictDeficitSelectedRoot reward
    (quittingTerminalSemanticPair reward
      (strictDeficitWordProfile reward gap depth)) gap

private theorem strictDeficitWordValue_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth : ℕ) :
    quittingStrictDeficitExactWordValue reward gap (depth + 1) =
      quittingRootSuccessorPayoff reward
        (quittingStrictDeficitExactWordValue reward gap depth)
        (quittingStrictDeficitExactWordNextRoot reward gap depth) := by
  funext who
  simp only [quittingStrictDeficitExactWordValue, strictDeficitWordProfile,
    quittingStrictDeficitExactWordNextRoot, quittingStrictDeficitExactWords_succ,
    quittingLiteralRootStackProfile_cons,
    quittingTerminalPayoff_rootThenContinuation_eq]
  rfl

private theorem strictDeficitNextRoot_absorption_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (depth : ℕ) :
    gap / (4 * M + gap) ≤
      quittingRootAbsorptionMass
        (quittingStrictDeficitExactWordNextRoot reward gap depth) := by
  exact (quittingStrictDeficitExactWords_step reward hgap hreward hdeficit depth).1

private def strictDeficitForwardPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ)
    (depth : ℕ) : QuittingNashBellmanPoint ι :=
  (quittingStrictDeficitExactWordValue reward gap (depth + 1),
    quittingSimplexOfRoot
      (quittingStrictDeficitExactWordNextRoot reward gap depth))

private theorem strictDeficitForwardPoint_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap M : ℝ) (hreward : ∀ S who, |reward S who| ≤ M)
    (depth : ℕ) :
    strictDeficitForwardPoint reward gap depth ∈
      quittingCirculationPathBox M (fun _ => -M) := by
  apply mem_quittingCirculationPathBox_of_bounds
  · intro who
    exact abs_quittingTerminalPayoff_le reward
      (strictDeficitWordProfile reward gap (depth + 1)) who hreward
  · intro who
    exact (abs_le.mp (abs_quittingTerminalPayoff_le reward
      (strictDeficitWordProfile reward gap (depth + 1)) who hreward)).1

private abbrev StrictDeficitReverseBox (M : ℝ) : Type :=
  {point : QuittingNashBellmanPoint ι //
    point ∈ quittingCirculationPathBox M (fun _ => -M)}

private def strictDeficitBoxSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap M : ℝ) (hreward : ∀ S who, |reward S who| ≤ M) :
    ℕ → StrictDeficitReverseBox (ι := ι) M :=
  fun depth => ⟨strictDeficitForwardPoint reward gap depth,
    strictDeficitForwardPoint_mem_box reward gap M hreward depth⟩

private def strictDeficitReverseEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ)
    (earlier later : StrictDeficitReverseBox (ι := ι) M) : Prop :=
  later.1.1 = quittingRootSuccessorPayoff reward earlier.1.1
    (quittingRootOfSimplex later.1.2)

omit [DecidableEq ι] in
private theorem isClosed_strictDeficitReverseEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ) :
    IsClosed {edge : StrictDeficitReverseBox (ι := ι) M ×
        StrictDeficitReverseBox (ι := ι) M |
      strictDeficitReverseEdge reward M edge.1 edge.2} := by
  let edgeData : (StrictDeficitReverseBox (ι := ι) M ×
      StrictDeficitReverseBox (ι := ι) M) →
      Payoff ι × QuittingRootSimplex ι :=
    fun edge => (edge.1.1.1, edge.2.1.2)
  have hdata : Continuous edgeData := by
    fun_prop
  exact isClosed_eq
    (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
    ((continuous_quittingRootSuccessorPayoff_simplex reward).comp hdata)

private theorem strictDeficitBoxSource_edge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap M : ℝ) (hreward : ∀ S who, |reward S who| ≤ M)
    (depth : ℕ) :
    strictDeficitReverseEdge reward M
      (strictDeficitBoxSource reward gap M hreward depth)
      (strictDeficitBoxSource reward gap M hreward (depth + 1)) := by
  change quittingStrictDeficitExactWordValue reward gap (depth + 2) =
    quittingRootSuccessorPayoff reward
      (quittingStrictDeficitExactWordValue reward gap (depth + 1))
      (quittingRootOfSimplex
        (quittingSimplexOfRoot
          (quittingStrictDeficitExactWordNextRoot reward gap (depth + 1))))
  simpa using strictDeficitWordValue_succ reward gap (depth + 1)

private theorem centeredSequence_neg_succ {Point : Type}
    (source : ℕ → Point) (center time : ℕ) :
    Math.Topology.centeredSequence source center
        (-((time + 1 : ℕ) : ℤ)) = source (center - (time + 1)) := by
  have hoffset : -((time + 1 : ℕ) : ℤ) = Int.negSucc time := by omega
  rw [hoffset]
  rfl

/-- One common strict reverse-prefix selection of the checked exact words.
The selected depth `centers rank + 1 - time` is the literal suffix of the
same word of depth `centers rank + 1`; no suffix is selected independently. -/
theorem exists_strictDeficitExactSuffix_payoffDiagonal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap) :
    ∃ (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
      (centers : ℕ → ℕ),
      StrictMono centers ∧
      (∀ time, Tendsto
        (fun rank => quittingSimplexOfRoot
          (quittingStrictDeficitExactWordNextRoot reward gap
            (centers rank - time))) atTop
          (nhds (quittingSimplexOfRoot (roots time)))) ∧
      (∀ time, Tendsto
        (fun rank => quittingStrictDeficitExactWordValue reward gap
          (centers rank + 1 - time)) atTop (nhds (value time))) ∧
      (∀ time, gap / (4 * M + gap) ≤
        quittingRootAbsorptionMass (roots time)) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      ∀ time, value time =
        fun who => quittingRootSequenceTerminalValue reward roots who time := by
  let source : ℕ → StrictDeficitReverseBox (ι := ι) M :=
    strictDeficitBoxSource reward gap M hreward
  let _ : CompactSpace (StrictDeficitReverseBox (ι := ι) M) :=
    isCompact_iff_compactSpace.mp
      (quittingCirculationPathBox_isCompact (ι := ι) M (fun _ => -M))
  obtain ⟨chain⟩ := Math.Topology.nonempty_sourceOmegaChain source
  let value : ℕ → Payoff ι :=
    fun time => (chain.path (-(time : ℤ))).1.1
  let roots : ℕ → ι → PMF Bool :=
    fun time => quittingRootOfSimplex (chain.path (-(time : ℤ))).1.2
  have hcenters : StrictMono chain.centers := chain.centers_strictMono
  have hpolicy : ∀ time, value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time) := by
    intro time
    have hedge := chain.relation
      (strictDeficitReverseEdge reward M)
      (isClosed_strictDeficitReverseEdge reward M)
      (strictDeficitBoxSource_edge reward gap M hreward)
      (Int.negSucc time)
    have hcurrent : Int.negSucc time + 1 = -(time : ℤ) := by omega
    have hnext : Int.negSucc time = -((time + 1 : ℕ) : ℤ) := by omega
    have hcurrent' : -((time + 1 : ℕ) : ℤ) + 1 = -(time : ℤ) := by omega
    change (chain.path (Int.negSucc time + 1)).1.1 =
      quittingRootSuccessorPayoff reward
        (chain.path (Int.negSucc time)).1.1
        (quittingRootOfSimplex
          (chain.path (Int.negSucc time + 1)).1.2) at hedge
    simpa only [hcurrent, hnext, hcurrent', value, roots] using hedge
  have hlower : ∀ depth, gap / (4 * M + gap) ≤
      quittingSimplexAbsorptionMass (source depth).1.2 := by
    intro depth
    change gap / (4 * M + gap) ≤ quittingSimplexAbsorptionMass
      (quittingSimplexOfRoot
        (quittingStrictDeficitExactWordNextRoot reward gap depth))
    rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass,
      quittingRootOfSimplex_simplexOfRoot]
    exact strictDeficitNextRoot_absorption_lower reward hgap hreward hdeficit depth
  have habsorption : ∀ time, gap / (4 * M + gap) ≤
      quittingRootAbsorptionMass (roots time) := by
    intro time
    have hpoint := chain.centered_coordinate_tendsto (-(time : ℤ))
    have hmass := (continuous_quittingSimplexAbsorptionMass.comp
      (continuous_snd.comp continuous_subtype_val)).tendsto
        (chain.path (-(time : ℤ))) |>.comp hpoint
    have heventual : ∀ rank, gap / (4 * M + gap) ≤
        quittingSimplexAbsorptionMass
          (Math.Topology.centeredSequence source (chain.centers rank)
            (-(time : ℤ))).1.2 := by
      intro rank
      cases time with
      | zero => simpa [Math.Topology.centeredSequence] using
          hlower (chain.centers rank)
      | succ time =>
          rw [centeredSequence_neg_succ]
          exact hlower _
    have hbound := ge_of_tendsto' hmass heventual
    simpa [roots, quittingSimplexAbsorptionMass_eq_rootAbsorptionMass] using hbound
  have hvalueBound : ∀ time who, |value time who| ≤ M := by
    intro time who
    have hmem := (chain.path (-(time : ℤ))).2
    exact abs_le.mpr ⟨hmem.1.1 who, hmem.1.2 who⟩
  obtain ⟨who, _⟩ := hdeficit []
  have hM0 : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hcharge : 0 < gap / (4 * M + gap) := by positivity
  have hterminal : ∀ time, value time =
      fun who => quittingRootSequenceTerminalValue reward roots who time :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_jointSurvival_tendsto_zero
      reward roots value
      (fun time => tendsto_zero_quittingJointSurvivalWeight_of_absorption_lower
        roots hcharge habsorption time)
      hreward hvalueBound hpolicy
  refine ⟨roots, value, chain.centers, hcenters, ?_, ?_, habsorption,
    hpolicy, hterminal⟩
  · intro time
    have hpoint := chain.centered_coordinate_tendsto (-(time : ℤ))
    have hrow := ((continuous_snd.comp continuous_subtype_val).tendsto
        (chain.path (-(time : ℤ)))).comp hpoint
    have hlimit : quittingSimplexOfRoot (roots time) =
        (chain.path (-(time : ℤ))).1.2 := by
      simp [roots]
    rw [hlimit]
    change Tendsto (fun rank =>
        (Math.Topology.centeredSequence source (chain.centers rank)
          (-(time : ℤ))).1.2) atTop
        (nhds (chain.path (-(time : ℤ))).1.2) at hrow
    apply hrow.congr'
    exact Eventually.of_forall fun rank => by
      cases time with
      | zero =>
          simp [Math.Topology.centeredSequence, source,
            strictDeficitBoxSource, strictDeficitForwardPoint]
      | succ time =>
          simp only [centeredSequence_neg_succ, source,
            strictDeficitBoxSource, strictDeficitForwardPoint]
  intro time
  have hpoint := chain.centered_coordinate_tendsto (-(time : ℤ))
  have hcoordinate := ((continuous_fst.comp continuous_subtype_val).tendsto
      (chain.path (-(time : ℤ)))).comp hpoint
  change Tendsto (fun rank =>
      (Math.Topology.centeredSequence source (chain.centers rank)
        (-(time : ℤ))).1.1) atTop (nhds (value time)) at hcoordinate
  apply hcoordinate.congr'
  filter_upwards [chain.centers_tendsto_atTop.eventually
    (eventually_ge_atTop time)] with rank hlarge
  cases time with
  | zero => simp [Math.Topology.centeredSequence, source,
      strictDeficitBoxSource, strictDeficitForwardPoint]
  | succ time =>
      have hindex : chain.centers rank + 1 - (time + 1) =
          (chain.centers rank - (time + 1)) + 1 := by omega
      simp only [centeredSequence_neg_succ, source,
        strictDeficitBoxSource, strictDeficitForwardPoint, hindex]

/-- The complete-response debt vanishes along every fixed literal suffix of
one strictly increasing selection of exact words. -/
theorem tendsto_strictDeficitExactWordDebt_literalSuffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S who, |reward S who| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (centers : ℕ → ℕ) (hcenters : StrictMono centers) (time : ℕ) :
    Tendsto (fun rank => quittingStrictDeficitExactWordDebt reward gap
      (centers rank + 1 - time)) atTop (nhds 0) := by
  have hdepth : Tendsto (fun rank => centers rank + 1 - time) atTop atTop := by
    apply tendsto_atTop.2
    intro lower
    filter_upwards [hcenters.tendsto_atTop.eventually
      (eventually_ge_atTop (lower + time))] with rank hlarge
    omega
  exact (tendsto_quittingStrictDeficitExactWordDebt_zero
    reward hgap hreward hdeficit).comp hdepth

/-- A fixed pure Quit date uses only finitely many opponent coefficients.
This finite-product transport requires no opponent-survival-at-infinity claim. -/
theorem tendsto_quittingPureTimeTerminalValue_some_of_stageCoefficients
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (approximants : ℕ → ℕ → ι → PMF Bool)
    (limit : ℕ → ι → PMF Bool) (who : ι) (date : ℕ)
    (hmass : ∀ time, Tendsto
      (fun rank => quittingFixedOpponentsContinueMass
        (approximants rank) who time) atTop
      (nhds (quittingFixedOpponentsContinueMass limit who time)))
    (hcontinue : ∀ time, Tendsto
      (fun rank => quittingFixedOpponentsContinueReward reward
        (approximants rank) who time) atTop
      (nhds (quittingFixedOpponentsContinueReward reward limit who time)))
    (hquit : Tendsto
      (fun rank => quittingFixedOpponentsQuitValue reward
        (approximants rank) who date) atTop
      (nhds (quittingFixedOpponentsQuitValue reward limit who date))) :
    Tendsto (fun rank => quittingRootSequencePureTimeTerminalValue
      reward (approximants rank) who (some date) 0) atTop
      (nhds (quittingRootSequencePureTimeTerminalValue
        reward limit who (some date) 0)) := by
  have hsurvival (time : ℕ) : Tendsto
      (fun rank => quittingOpponentSurvivalWeight
        (approximants rank) who 0 time) atTop
      (nhds (quittingOpponentSurvivalWeight limit who 0 time)) := by
    simpa only [quittingOpponentSurvivalWeight, Nat.zero_add] using
      (tendsto_finsetProd (Finset.range time)
        (fun offset _ => hmass offset))
  have hledger : Tendsto
      (fun rank => quittingLiveLedgerAccum reward
        (approximants rank) who 0 date) atTop
      (nhds (quittingLiveLedgerAccum reward limit who 0 date)) := by
    simpa only [quittingLiveLedgerAccum, Nat.zero_add] using
      (tendsto_finsetSum (Finset.range date) (fun offset _ =>
        (hsurvival offset).mul (hcontinue offset)))
  simpa only [quittingRootSequencePureTimeTerminalValue_some_eq] using
    hledger.add ((hsurvival date).mul hquit)

/-- Pointwise convergence of simplex rows gives convergence of every fixed
pure finite-date response against their literal opponent rows. -/
theorem tendsto_quittingPureTimeTerminalValue_some_of_simplexRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (approximants : ℕ → ℕ → ι → PMF Bool)
    (limit : ℕ → ι → PMF Bool) (who : ι) (date : ℕ)
    (hrows : ∀ time, Tendsto
      (fun rank => quittingSimplexOfRoot (approximants rank time)) atTop
      (nhds (quittingSimplexOfRoot (limit time)))) :
    Tendsto (fun rank => quittingRootSequencePureTimeTerminalValue
      reward (approximants rank) who (some date) 0) atTop
      (nhds (quittingRootSequencePureTimeTerminalValue
        reward limit who (some date) 0)) := by
  have hmass (time : ℕ) : Tendsto
      (fun rank => quittingFixedOpponentsContinueMass
        (approximants rank) who time) atTop
      (nhds (quittingFixedOpponentsContinueMass limit who time)) := by
    have h := (continuous_quittingTesterOpponentContinueMass_simplex who).tendsto
      (quittingSimplexOfRoot (limit time)) |>.comp (hrows time)
    change Tendsto (fun rank => quittingStationaryContinueMass
      (Function.update
        (quittingRootOfSimplex (quittingSimplexOfRoot (approximants rank time)))
        who (PMF.pure false))) atTop
      (nhds (quittingStationaryContinueMass
        (Function.update
          (quittingRootOfSimplex (quittingSimplexOfRoot (limit time)))
          who (PMF.pure false)))) at h
    simpa only [quittingRootOfSimplex_simplexOfRoot,
      quittingFixedOpponentsContinueMass] using h
  have hcontinue (time : ℕ) : Tendsto
      (fun rank => quittingFixedOpponentsContinueReward reward
        (approximants rank) who time) atTop
      (nhds (quittingFixedOpponentsContinueReward reward limit who time)) := by
    have hpair : Tendsto
        (fun rank => ((0 : Payoff ι),
          quittingSimplexOfRoot (approximants rank time))) atTop
        (nhds ((0 : Payoff ι), quittingSimplexOfRoot (limit time))) :=
      tendsto_const_nhds.prodMk_nhds (hrows time)
    have h := (continuous_quittingRootContinuePayoff_simplex reward who).tendsto
      ((0 : Payoff ι), quittingSimplexOfRoot (limit time)) |>.comp hpair
    change Tendsto (fun rank => quittingRootContinuePayoff reward 0
      (quittingRootOfSimplex (quittingSimplexOfRoot (approximants rank time))) who)
      atTop (nhds (quittingRootContinuePayoff reward 0
        (quittingRootOfSimplex (quittingSimplexOfRoot (limit time))) who)) at h
    simpa only [quittingRootOfSimplex_simplexOfRoot,
      quittingRootContinuePayoff_eq_fixedOpponents, Pi.zero_apply,
      mul_zero, add_zero] using h
  have hquit : Tendsto
      (fun rank => quittingFixedOpponentsQuitValue reward
        (approximants rank) who date) atTop
      (nhds (quittingFixedOpponentsQuitValue reward limit who date)) := by
    have hpair : Tendsto
        (fun rank => ((0 : Payoff ι),
          quittingSimplexOfRoot (approximants rank date))) atTop
        (nhds ((0 : Payoff ι), quittingSimplexOfRoot (limit date))) :=
      tendsto_const_nhds.prodMk_nhds (hrows date)
    have h := (continuous_quittingRootQuitPayoff_simplex reward who).tendsto
      ((0 : Payoff ι), quittingSimplexOfRoot (limit date)) |>.comp hpair
    change Tendsto (fun rank => quittingRootQuitPayoff reward 0
      (quittingRootOfSimplex (quittingSimplexOfRoot (approximants rank date))) who)
      atTop (nhds (quittingRootQuitPayoff reward 0
        (quittingRootOfSimplex (quittingSimplexOfRoot (limit date))) who)) at h
    simpa only [quittingRootOfSimplex_simplexOfRoot,
      quittingRootQuitPayoff_eq_fixedOpponentsQuitValue] using h
  exact tendsto_quittingPureTimeTerminalValue_some_of_stageCoefficients
    reward approximants limit who date hmass hcontinue hquit

end GameTheory
