import UniformEquilibrium.Quitting.Root.RationalFiniteClockLaw
import UniformEquilibrium.Quitting.Root.TerminalSemanticPrefixSimplex
import UniformEquilibrium.Quitting.Root.FiniteDeadlineTimingWord
import UniformEquilibrium.Quitting.Terminal.FiniteMenuFullProfileApproximation
import MathUE.Interval.RationalCubeGrid
import Mathlib.Data.Nat.Find
import Mathlib.Data.List.GetD

/-! # Target-free terminating rational finite-word search

The executable search dovetails consecutive calendar lengths and rational hazard
grids, including the empty calendar. Acceptance uses the canonical rational full
payoff/cap fold, not a restricted reply menu. Actual terminal approximate-equilibrium
existence proves termination through finite-menu approximation and rational density.
The selected word has actual independent finite date-or-Never laws. No prescribed
real payoff target, runtime bound, or equilibrium-existence decision is computed.
-/

namespace GameTheory

open GameTheory.Finite Filter
open _root_.Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {players : ℕ}

/-- A common-denominator grid of every chronological hazard coordinate. -/
def rationalQuittingFiniteGridWord (deadline resolution : ℕ)
    (point : Fin (deadline * players) → Fin (resolution + 2)) :
    List (RationalQuittingRoot players) :=
  List.ofFn fun date : Fin deadline =>
    { probability := fun who =>
        rationalBooleanGridProbability resolution point (finProdFinEquiv (date, who))
      nonnegative := fun who =>
        (rationalBooleanGridProbability_mem_unitInterval resolution point
          (finProdFinEquiv (date, who))).1
      le_one := fun who =>
        (rationalBooleanGridProbability_mem_unitInterval resolution point
          (finProdFinEquiv (date, who))).2 }

/-- Every finite length and every denominator up to the budget is enumerated. -/
def rationalQuittingFiniteWordCandidates (budget : ℕ) :
    List (List (RationalQuittingRoot players)) :=
  (List.range (budget + 1)).flatMap fun deadline =>
    (List.range (budget + 1)).flatMap fun resolution =>
      (rationalBooleanGridPoints (deadline * players) resolution).map
        (rationalQuittingFiniteGridWord deadline resolution)

/-- Strict full terminal regret test, evaluated entirely in rational arithmetic. -/
def rationalQuittingFiniteWordAccepts (reward : RationalQuittingReward players)
    (tolerance : ℚ) (word : List (RationalQuittingRoot players)) : Bool :=
  decide (∀ who, (rationalQuittingFiniteWordSemanticPair reward word).2 who -
    (rationalQuittingFiniteWordSemanticPair reward word).1 who < tolerance)

def rationalQuittingFiniteWordBoundedSearch? (reward : RationalQuittingReward players)
    (tolerance : ℚ) (budget : ℕ) : Option (List (RationalQuittingRoot players)) :=
  (rationalQuittingFiniteWordCandidates budget).find?
    (rationalQuittingFiniteWordAccepts reward tolerance)

theorem mem_rationalQuittingFiniteWordCandidates
    (deadline resolution budget : ℕ) (hdeadline : deadline ≤ budget)
    (hresolution : resolution ≤ budget)
    (point : Fin (deadline * players) → Fin (resolution + 2)) :
    rationalQuittingFiniteGridWord deadline resolution point ∈
      rationalQuittingFiniteWordCandidates budget := by
  apply List.mem_flatMap.mpr
  refine ⟨deadline, List.mem_range.mpr (Nat.lt_succ_of_le hdeadline), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨resolution, List.mem_range.mpr (Nat.lt_succ_of_le hresolution), ?_⟩
  exact List.mem_map.mpr
    ⟨point, mem_rationalBooleanGridPoints resolution point, rfl⟩

noncomputable section

/-- Fixed-length continuity delegates to the canonical semantic fold, including its caps. -/
theorem continuous_quittingFiniteRootWordSemanticPrefix_simplex
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (deadline : ℕ) (tail : QuittingTerminalSemanticPair (Fin players)) :
    Continuous (fun roots : Fin deadline → QuittingRootSimplex (Fin players) =>
      quittingFiniteRootWordSemanticPrefix reward
        (List.ofFn fun date => quittingRootOfSimplex (roots date)) tail) := by
  induction deadline with
  | zero =>
      simpa [quittingFiniteRootWordSemanticPrefix, quittingFiniteRootWordPayoff,
        quittingFiniteRootWordCap] using
        (continuous_const : Continuous (fun _ : Fin 0 → QuittingRootSimplex (Fin players) =>
          tail))
  | succ deadline ih =>
      have htail : Continuous
          (fun roots : Fin (deadline + 1) → QuittingRootSimplex (Fin players) =>
            quittingFiniteRootWordSemanticPrefix reward
              (List.ofFn fun date => quittingRootOfSimplex (Fin.tail roots date)) tail) :=
        ih.comp (continuous_pi fun date => continuous_apply date.succ)
      have h := (continuous_quittingTerminalSemanticPrefixSimplex reward).comp
        ((continuous_apply 0).prodMk htail)
      simpa only [Function.comp_def, List.ofFn_succ,
        quittingFiniteRootWordSemanticPrefix_eq_foldr,
        List.foldr_cons, Fin.tail, quittingTerminalSemanticPrefixSimplex] using h

private def finiteWordClip (value : ℝ) : ℝ := min 1 (max 0 value)

private theorem finiteWordClip_nonneg (value : ℝ) : 0 ≤ finiteWordClip value :=
  le_min (by norm_num) (le_max_left _ _)

private theorem finiteWordClip_le_one (value : ℝ) : finiteWordClip value ≤ 1 :=
  min_le_left _ _

private theorem finiteWordClip_eq {value : ℝ} (hzero : 0 ≤ value) (hone : value ≤ 1) :
    finiteWordClip value = value := by
  simp [finiteWordClip, max_eq_right hzero, min_eq_right hone]

private def finiteWordScalarSimplex (value : ℝ) : Convexity.StdSimplex ℝ Bool :=
  stdSimplexEquiv (bernoulliBool (finiteWordClip value)
    (finiteWordClip_nonneg value) (finiteWordClip_le_one value))

private theorem continuous_finiteWordScalarSimplex :
    Continuous finiteWordScalarSimplex := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ Bool).continuous_iff.mpr
  apply continuous_pi
  intro action
  have hclip : Continuous finiteWordClip :=
    continuous_const.min (continuous_const.max continuous_id)
  cases action
  · have hfalse : Continuous (fun value : ℝ => 1 - finiteWordClip value) :=
      continuous_const.sub hclip
    simpa [Function.comp_def, finiteWordScalarSimplex, simplexEquiv_apply_weights,
      toVector] using hfalse
  · simpa [Function.comp_def, finiteWordScalarSimplex, simplexEquiv_apply_weights,
      toVector] using hclip

private def finiteWordCubeRoots (deadline : ℕ)
    (probability : Fin (deadline * players) → ℝ) :
    Fin deadline → QuittingRootSimplex (Fin players) :=
  fun date who => finiteWordScalarSimplex (probability (finProdFinEquiv (date, who)))

private theorem continuous_finiteWordCubeRoots (deadline : ℕ) :
    Continuous (finiteWordCubeRoots (players := players) deadline) := by
  apply continuous_pi
  intro date
  apply continuous_pi
  intro who
  exact continuous_finiteWordScalarSimplex.comp
    (continuous_apply (finProdFinEquiv (date, who)))

private def finiteWordCubePair (reward : RationalQuittingReward players)
    (deadline : ℕ) (probability : Fin (deadline * players) → ℝ) :
    QuittingTerminalSemanticPair (Fin players) :=
  quittingFiniteRootWordSemanticPrefix (rationalQuittingRewardToReal reward)
    (List.ofFn fun date => quittingRootOfSimplex (finiteWordCubeRoots deadline probability date))
    (0, fun who => max 0 (reward (quittingSingletonTerminal who) who : ℝ))

private theorem continuous_finiteWordCubePair (reward : RationalQuittingReward players)
    (deadline : ℕ) : Continuous (finiteWordCubePair reward deadline) :=
  (continuous_quittingFiniteRootWordSemanticPrefix_simplex
    (rationalQuittingRewardToReal reward) deadline _).comp
    (continuous_finiteWordCubeRoots deadline)

private theorem finiteWordAlwaysContinuePair_eq (reward : RationalQuittingReward players) :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)) =
      (0, fun who => max 0 (reward (quittingSingletonTerminal who) who : ℝ)) := by
  apply Prod.ext
  · funext who
    change quittingTerminalPayoff (rationalQuittingRewardToReal reward)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)) who = 0
    exact quittingTerminalPayoff_quittingAlwaysContinue (rationalQuittingRewardToReal reward) who
  · funext who
    change quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)) who = _
    exact quittingContinuationBestResponseValue_quittingAlwaysContinueProfile
      (rationalQuittingRewardToReal reward) who

private theorem finiteWordCubePair_eq_actual (reward : RationalQuittingReward players)
    (deadline : ℕ) (roots : Fin deadline → Fin players → PMF Bool) :
    finiteWordCubePair reward deadline
        (fun coordinate => hazardOfRoot (roots (finProdFinEquiv.symm coordinate).1)
          (finProdFinEquiv.symm coordinate).2) =
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (List.ofFn roots)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) := by
  have hroots : (List.ofFn fun date =>
      quittingRootOfSimplex (finiteWordCubeRoots deadline
        (fun coordinate => hazardOfRoot (roots (finProdFinEquiv.symm coordinate).1)
          (finProdFinEquiv.symm coordinate).2) date)) = List.ofFn roots := by
    congr 1
    funext date who
    simp only [finiteWordCubeRoots, Equiv.symm_apply_apply,
      finiteWordScalarSimplex, quittingRootOfSimplex]
    apply eq_of_forall_toReal_eq
    intro action
    cases action
    · simp only [bernoulliBool_false_toReal, finiteWordClip_eq
        (hazardOfRoot_nonneg (roots date) who) (hazardOfRoot_le_one (roots date) who)]
      exact (Math.PMFProduct.pmfBool_false_toReal (roots date who)).symm
    · simp only [bernoulliBool_true_toReal, finiteWordClip_eq
        (hazardOfRoot_nonneg (roots date) who) (hazardOfRoot_le_one (roots date) who)]
      rfl
  rw [finiteWordCubePair, hroots, quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix]
  congr 1
  exact (finiteWordAlwaysContinuePair_eq reward).symm

private theorem finiteWordCubePair_grid_eq_cast (reward : RationalQuittingReward players)
    (deadline resolution : ℕ)
    (point : Fin (deadline * players) → Fin (resolution + 2)) :
    finiteWordCubePair reward deadline
        (fun coordinate => (rationalBooleanGridProbability resolution point coordinate : ℝ)) =
      (fun who => ((rationalQuittingFiniteWordSemanticPair reward
          (rationalQuittingFiniteGridWord deadline resolution point)).1 who : ℝ),
        fun who => ((rationalQuittingFiniteWordSemanticPair reward
          (rationalQuittingFiniteGridWord deadline resolution point)).2 who : ℝ)) := by
  have hroots : (List.ofFn fun date =>
      quittingRootOfSimplex (finiteWordCubeRoots deadline
        (fun coordinate => (rationalBooleanGridProbability resolution point coordinate : ℝ))
        date)) = (rationalQuittingFiniteGridWord deadline resolution point).map
      RationalQuittingRoot.toPMF := by
    rw [rationalQuittingFiniteGridWord, List.map_ofFn]
    congr 1
    funext date who
    simp only [Function.comp_apply, finiteWordCubeRoots, finiteWordScalarSimplex,
      quittingRootOfSimplex, RationalQuittingRoot.toPMF]
    rw [Equiv.symm_apply_apply]
    have hbox := rationalBooleanGridProbability_mem_unitInterval resolution point
      (finProdFinEquiv (date, who))
    have hzero : (0 : ℝ) ≤
        (rationalBooleanGridProbability resolution point (finProdFinEquiv (date, who)) : ℝ) :=
      Rat.cast_nonneg.mpr hbox.1
    have hone :
        (rationalBooleanGridProbability resolution point (finProdFinEquiv (date, who)) : ℝ) ≤
          1 := by exact_mod_cast hbox.2
    apply eq_of_forall_toReal_eq
    intro action
    cases action <;> simp only [bernoulliBool_false_toReal, bernoulliBool_true_toReal,
      finiteWordClip_eq hzero hone]
  rw [finiteWordCubePair, hroots]
  have hsemantic := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast
    reward (rationalQuittingFiniteGridWord deadline resolution point)
  rw [quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix,
    finiteWordAlwaysContinuePair_eq] at hsemantic
  exact hsemantic

private theorem finiteMenu_semanticPair_eq_liveWord
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (deadline : ℕ)
    (mixed : Fin players → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
      quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward
          (List.ofFn fun date : Fin deadline =>
            quittingProfileLiveRoot reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) date.val)
          (quittingAlwaysContinueProfile reward)) := by
  simpa only [quittingFiniteDeadlineTimingRootWord] using
    congrArg (quittingTerminalSemanticPair reward)
      (quittingFiniteDeadlineTimingProfile_eq_literalRootStack reward deadline mixed)

/-- Rational density preserves every strict complete-cap inequality on a fixed calendar. -/
theorem exists_rationalQuittingFiniteGridWord_accepts_of_finiteWord
    (reward : RationalQuittingReward players) (deadline : ℕ)
    (roots : Fin deadline → Fin players → PMF Bool)
    (tolerance : ℚ) (hregret : ∀ who,
      quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (List.ofFn roots)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who -
        quittingTerminalPayoff (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (List.ofFn roots)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who <
      (tolerance : ℝ)) :
    ∃ resolution : ℕ, ∃ point : Fin (deadline * players) → Fin (resolution + 2),
      rationalQuittingFiniteWordAccepts reward tolerance
        (rationalQuittingFiniteGridWord deadline resolution point) = true := by
  let probability : Fin (deadline * players) → ℝ := fun coordinate =>
    hazardOfRoot (roots (finProdFinEquiv.symm coordinate).1)
      (finProdFinEquiv.symm coordinate).2
  have hgood : ∀ᶠ candidate in 𝓝 probability, ∀ who,
      (finiteWordCubePair reward deadline candidate).2 who -
        (finiteWordCubePair reward deadline candidate).1 who < (tolerance : ℝ) := by
    apply Filter.eventually_all.mpr
    intro who
    have hcontinuous := (continuous_apply who).comp
      (continuous_snd.comp (continuous_finiteWordCubePair reward deadline))
    have hpayoff := (continuous_apply who).comp
      (continuous_fst.comp (continuous_finiteWordCubePair reward deadline))
    have hstrict : (finiteWordCubePair reward deadline probability).2 who -
        (finiteWordCubePair reward deadline probability).1 who < (tolerance : ℝ) := by
      simpa only [probability, finiteWordCubePair_eq_actual, quittingTerminalSemanticPair]
        using hregret who
    exact (hcontinuous.sub hpayoff).continuousAt.eventually (gt_mem_nhds hstrict)
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hgood
  obtain ⟨resolution, point, hclose⟩ := Math.RationalCubeGrid.exists_point_dist_lt
    probability
    (fun coordinate => hazardOfRoot_nonneg _ _)
    (fun coordinate => hazardOfRoot_le_one _ _) radius hradius
  have hchosen := hball (show
      (fun coordinate => (rationalBooleanGridProbability resolution point coordinate : ℝ)) ∈
        Metric.ball probability radius from
      by simpa only [Metric.mem_ball, rationalBooleanGridProbability] using hclose)
  change ∀ who,
    (finiteWordCubePair reward deadline
      (fun coordinate => (rationalBooleanGridProbability resolution point coordinate : ℝ))).2
        who -
      (finiteWordCubePair reward deadline
        (fun coordinate => (rationalBooleanGridProbability resolution point coordinate : ℝ))).1
          who < (tolerance : ℝ) at hchosen
  rw [finiteWordCubePair_grid_eq_cast] at hchosen
  dsimp only at hchosen
  refine ⟨resolution, point, ?_⟩
  simp only [rationalQuittingFiniteWordAccepts, decide_eq_true_eq]
  intro who
  exact_mod_cast hchosen who

/-- Actual terminal approximate-equilibrium existence, not a supplied good finite word,
proves eventual success at every positive rational requested accuracy. -/
theorem rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_terminalApproximation
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (happrox : ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame (rationalQuittingRewardToReal reward)).BehaviorProfile,
        (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) error profile)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true := by
  have hpositive : (0 : ℝ) < tolerance := by exact_mod_cast htolerance
  obtain ⟨profile, hnash⟩ := happrox ((tolerance : ℝ) / 4) (by positivity)
  have hexploit := quittingTerminalExploitability_le_of_isεAsymptoticNash
    (rationalQuittingRewardToReal reward) profile (by positivity) hnash
  obtain ⟨deadline, _, mixed, hmenu, _⟩ := exists_finiteDeadlineTimingProfile_approximation
    (rationalQuittingRewardToReal reward) profile
      (show 0 < (tolerance : ℝ) / 4 by positivity) 0
  let roots := fun date : Fin deadline =>
    quittingProfileLiveRoot (rationalQuittingRewardToReal reward)
      (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward) deadline mixed)
      date.val
  have hregret (who : Fin players) :
      quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (List.ofFn roots)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who -
        quittingTerminalPayoff (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (List.ofFn roots)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who <
      (tolerance : ℝ) := by
    have hdebt := quittingTerminalDeviationDebt_le_exploitability
      (rationalQuittingRewardToReal reward)
      (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward) deadline mixed)
      who
    have hequal := finiteMenu_semanticPair_eq_liveWord
      (rationalQuittingRewardToReal reward) deadline mixed
    have hpayoff := congrFun (congrArg Prod.fst hequal) who
    have hcap := congrFun (congrArg Prod.snd hequal) who
    unfold quittingTerminalDeviationDebt at hdebt
    dsimp only [quittingTerminalSemanticPair] at hpayoff hcap
    dsimp only [roots]
    rw [← hcap, ← hpayoff]
    linarith
  obtain ⟨resolution, point, haccepts⟩ :=
    exists_rationalQuittingFiniteGridWord_accepts_of_finiteWord
      reward deadline roots tolerance hregret
  refine ⟨max deadline resolution, fun budget hbudget => ?_⟩
  apply List.find?_isSome.mpr
  refine ⟨rationalQuittingFiniteGridWord deadline resolution point, ?_, haccepts⟩
  exact mem_rationalQuittingFiniteWordCandidates deadline resolution budget
    ((Nat.le_max_left _ _).trans hbudget) ((Nat.le_max_right _ _).trans hbudget) point

/-- One actual UE payoff implies termination without supplying any target to the search. -/
theorem rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_uniformPayoff
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (huniform : ∃ target : Payoff (Fin players),
      (quittingGame (rationalQuittingRewardToReal reward)).IsUniformEquilibriumPayoff none target)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true := by
  rcases huniform with ⟨target, htarget⟩
  apply rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_terminalApproximation
    reward _ tolerance htolerance
  intro error herror
  obtain ⟨profile, hnash, _⟩ :=
    exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff
      (rationalQuittingRewardToReal reward) target htarget herror
  exact ⟨profile, hnash⟩

end

/-- Executable first-success selector. Only the termination proof is erased. -/
def rationalQuittingFiniteWordSearchSelector (reward : RationalQuittingReward players)
    (tolerance : ℚ) (hsuccess : ∃ budget,
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true) :
    List (RationalQuittingRoot players) :=
  (rationalQuittingFiniteWordBoundedSearch? reward tolerance (Nat.find hsuccess)).get
    (Nat.find_spec hsuccess)

theorem rationalQuittingFiniteWordSearchSelector_accepts (reward : RationalQuittingReward players)
    (tolerance : ℚ) (hsuccess : ∃ budget,
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true) :
    rationalQuittingFiniteWordAccepts reward tolerance
      (rationalQuittingFiniteWordSearchSelector reward tolerance hsuccess) = true := by
  let search := rationalQuittingFiniteWordBoundedSearch? reward tolerance (Nat.find hsuccess)
  have hsome : search = some (search.get (Nat.find_spec hsuccess)) := (Option.some_get _).symm
  exact List.find?_some
    (p := rationalQuittingFiniteWordAccepts reward tolerance) hsome

/-- No real target is a data input to this executable selector. -/
def rationalQuittingFiniteWordSearchOfUniformPayoff [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (tolerance : ℚ) (htolerance : 0 < tolerance)
    (huniform : ∃ target : Payoff (Fin players),
      (quittingGame (rationalQuittingRewardToReal reward)).IsUniformEquilibriumPayoff none target) :
    List (RationalQuittingRoot players) :=
  rationalQuittingFiniteWordSearchSelector reward tolerance (by
    obtain ⟨threshold, hthreshold⟩ :=
      rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_uniformPayoff
        reward huniform tolerance htolerance
    exact ⟨threshold, hthreshold threshold le_rfl⟩)

noncomputable section

/-- Acceptance is literal complete behavioral terminal regret, with all post-calendar
responses and Never included by the existing exact rational semantic-pair theorem. -/
theorem rationalQuittingFiniteWordAccepts_iff (reward : RationalQuittingReward players)
    (tolerance : ℚ) (word : List (RationalQuittingRoot players)) :
    rationalQuittingFiniteWordAccepts reward tolerance word = true ↔
      ∀ who, quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (word.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who <
        (tolerance : ℝ) := by
  have heq := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word
  have hpayoff := congrArg Prod.fst heq
  have hcap := congrArg Prod.snd heq
  simp only [quittingTerminalSemanticPair] at hpayoff hcap
  simp only [rationalQuittingFiniteWordAccepts, decide_eq_true_eq,
    quittingTerminalDeviationDebt, hpayoff, hcap]
  constructor
  · intro h who
    exact_mod_cast h who
  · intro h who
    exact_mod_cast h who

/-- The same selected actual word has terminal Nash error strictly below tolerance. -/
theorem rationalQuittingFiniteWordSearchSelector_spec [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (tolerance : ℚ) (htolerance : 0 < tolerance)
    (hsuccess : ∃ budget,
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true) :
    let word := rationalQuittingFiniteWordSearchSelector reward tolerance hsuccess
    let profile := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
      (word.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    quittingTerminalExploitability (rationalQuittingRewardToReal reward) profile <
      (tolerance : ℝ) := by
  have hdebt := (rationalQuittingFiniteWordAccepts_iff reward tolerance _).mp
    (rationalQuittingFiniteWordSearchSelector_accepts reward tolerance hsuccess)
  dsimp only
  rw [quittingTerminalExploitability, QuittingBoundaryHolonomy.finitePlayerMax]
  apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
  intro who _
  exact max_lt (by exact_mod_cast htolerance) (hdebt who)

end

/-- Rational all-Continue padding is data, not a selected tail certificate. -/
def rationalQuittingZeroRoot (players : ℕ) : RationalQuittingRoot players where
  probability := 0
  nonnegative := fun _ => le_rfl
  le_one := fun _ => by norm_num

/-- The rational chronological word padded with zero hazards. -/
def rationalQuittingFiniteWordSequence (word : List (RationalQuittingRoot players)) :
    ℕ → RationalQuittingRoot players
  | time => word.getD time (rationalQuittingZeroRoot players)

noncomputable section

/-- Literal finite laws of the accepted word retain exact rational masses and its full cap.
The empty calendar is handled separately by pure Never laws, not silently excluded. -/
theorem exists_rationalQuittingFiniteWordLaws_exact
    (reward : RationalQuittingReward players) (word : List (RationalQuittingRoot players)) :
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed) =
        (fun who => ((rationalQuittingFiniteWordSemanticPair reward word).1 who : ℝ),
          fun who => ((rationalQuittingFiniteWordSemanticPair reward word).2 who : ℝ)) := by
  by_cases hzero : word.length = 0
  · have hnil : word = [] := List.length_eq_zero_iff.mp hzero
    subst word
    let mixed : Fin players → PMF (Option (Fin 0)) := fun _ => PMF.pure none
    refine ⟨mixed, ?_, ?_⟩
    · intro who choice
      cases choice with
      | none => simp [mixed, rationalFiniteClockMass, rationalFiniteClockPrefix]
      | some date => exact Fin.elim0 date
    · have hprofile : quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          0 mixed = quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward) := by
        funext who
        exact quittingFiniteDeadlineTimingProfile_eq_alwaysContinue_of_pure_none _ 0 mixed who rfl
      change quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward) 0 mixed) = _
      rw [hprofile]
      exact quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward []
  · have hpositive : 0 < word.length := Nat.pos_of_ne_zero hzero
    obtain ⟨mixed, hmass, _, hsemantic⟩ := exists_rationalFiniteClockLaws_exact
      (rationalQuittingRewardToReal reward) (rationalQuittingFiniteWordSequence word)
      word.length hpositive
    refine ⟨mixed, hmass, ?_⟩
    rw [hsemantic, rationalFiniteClock_truncated_semanticPair_eq_cast]
    have hword : (List.ofFn fun date : Fin word.length =>
        rationalQuittingFiniteWordSequence word date.val) = word := by
      calc
        _ = List.ofFn (fun date : Fin word.length => word[date.val]) := by
          congr 1
          funext date
          exact List.getD_eq_getElem word (rationalQuittingZeroRoot players) date.isLt
        _ = word := List.ofFn_getElem
    rw [hword]

/-- The executable selected word has actual independent rational finite laws with
unrestricted terminal exploitability strictly below the requested tolerance. -/
theorem rationalQuittingFiniteWordSearchSelector_finiteLaws [Nonempty (Fin players)]
    (reward : RationalQuittingReward players) (tolerance : ℚ) (htolerance : 0 < tolerance)
    (hsuccess : ∃ budget,
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true) :
    let word := rationalQuittingFiniteWordSearchSelector reward tolerance hsuccess
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalExploitability (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) < (tolerance : ℝ) := by
  dsimp only
  let word := rationalQuittingFiniteWordSearchSelector reward tolerance hsuccess
  obtain ⟨mixed, hmass, hsemantic⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  refine ⟨mixed, hmass, ?_⟩
  have hword := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word
  have hsame := hsemantic.trans hword.symm
  have hequal := congrArg (fun pair : QuittingTerminalSemanticPair (Fin players) =>
    QuittingBoundaryHolonomy.finitePlayerMax
      (fun who => max 0 (pair.2 who - pair.1 who))) hsame
  change quittingTerminalExploitability (rationalQuittingRewardToReal reward)
      (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
        word.length mixed) =
    quittingTerminalExploitability (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (word.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) at hequal
  have hbound := rationalQuittingFiniteWordSearchSelector_spec
    reward tolerance htolerance hsuccess
  change quittingTerminalExploitability _ _ < _ at hbound
  exact hequal.trans_lt hbound

/-- The target-free terminating source producer returns these very finite laws.
The existence proof is used only for termination, never to select strategy data. -/
theorem rationalQuittingFiniteWordSearchOfUniformPayoff_finiteLaws
    [Nonempty (Fin players)] (reward : RationalQuittingReward players)
    (tolerance : ℚ) (htolerance : 0 < tolerance)
    (huniform : ∃ target : Payoff (Fin players),
      (quittingGame (rationalQuittingRewardToReal reward)).IsUniformEquilibriumPayoff none target) :
    let word := rationalQuittingFiniteWordSearchOfUniformPayoff
      reward tolerance htolerance huniform
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalExploitability (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) < (tolerance : ℝ) := by
  unfold rationalQuittingFiniteWordSearchOfUniformPayoff
  exact rationalQuittingFiniteWordSearchSelector_finiteLaws reward tolerance htolerance _

end

end GameTheory
