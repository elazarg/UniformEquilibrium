/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.MinimumLawCausalSuffixInertStack
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization

/-!
# Pure-Never marginal limits of inert causal suffix stacks

Arbitrarily deep source-matched all-Continue stacks admit one strict
subsequence whose every marginal compact stopping-law limit is literally
Dirac at `Never`, while the selected joint profiles retain a positive finite
terminal atom through relative timing. The resulting sequence is neither
joint-tight nor opponent-tight.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-! ## Pure-Never marginal limit of the inert chronology -/

omit [DecidableEq iota] in
private theorem quittingProfileLiveRoot_literal_replicate_allContinue_of_lt
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (depth time : ℕ) (htime : time < depth) :
    quittingProfileLiveRoot reward
        (quittingLiteralRootStackProfile reward
          (List.replicate depth
            (quittingAllContinueRoot : iota → PMF Bool)) terminal)
        time = (quittingAllContinueRoot : iota → PMF Bool) := by
  induction depth generalizing time with
  | zero => omega
  | succ depth ih =>
      rw [List.replicate_succ, quittingLiteralRootStackProfile_cons]
      cases time with
      | zero => exact quittingProfileLiveRoot_rootThenContinuation_zero _ _ _
      | succ time =>
          rw [quittingProfileLiveRoot_rootThenContinuation_succ]
          exact ih time (by omega)

omit [DecidableEq iota] in
private theorem quittingCompactStoppingLaw_finiteMass_literal_allContinue_eq_zero
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (depth time : ℕ) (htime : time < depth) (player : iota) :
    (quittingCompactStoppingLawsOfProfile reward
        (quittingLiteralRootStackProfile reward
          (List.replicate depth
            (quittingAllContinueRoot : iota → PMF Bool)) terminal)
        player).realMass
          {(time : _root_.Math.Probability.CompactStoppingTime)} = 0 := by
  rw [← _root_.Math.Probability.CompactStoppingLaw.toPMF_apply_toReal]
  simp only [quittingCompactStoppingLawsOfProfile,
    _root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  have hroot :=
    quittingProfileLiveRoot_literal_replicate_allContinue_of_lt
      reward terminal depth time htime
  have hrootPlayer := congrFun hroot player
  have hhazard : quittingBehaviorLiveHazard reward
      ((quittingLiteralRootStackProfile reward
        (List.replicate depth
          (quittingAllContinueRoot : iota → PMF Bool)) terminal) player)
      time = PMF.pure false := by
    simpa only [quittingProfileLiveRoot, quittingBehaviorLiveHazard,
      quittingAllContinueRoot] using hrootPlayer
  have hsource : ((quittingBehaviorStoppingLaw reward
      ((quittingLiteralRootStackProfile reward
        (List.replicate depth
          (quittingAllContinueRoot : iota → PMF Bool)) terminal) player)
      (some time)).toReal = 0) := by
    rw [quittingBehaviorStoppingLaw_some_toReal,
      quittingHazardStopMass_eq_survival_mul_stop, hhazard]
    simp
  exact hsource

private theorem compactStoppingLaw_eq_pureNever_of_finiteMass_eventually_zero
    {lawSeq : ℕ → _root_.Math.Probability.CompactStoppingLaw}
    {law : _root_.Math.Probability.CompactStoppingLaw}
    (hlaw : Tendsto lawSeq atTop (nhds law))
    (hzero : ∀ time : ℕ, ∀ᶠ n in atTop,
      (lawSeq n).realMass
        {(time : _root_.Math.Probability.CompactStoppingTime)} = 0) :
    law = _root_.Math.Probability.CompactStoppingLaw.ofPMF
      (PMF.pure (⊤ : _root_.Math.Probability.CompactStoppingTime)) := by
  have hfinite (time : ℕ) : law.realMass
      {(time : _root_.Math.Probability.CompactStoppingTime)} = 0 := by
    have hlimit :=
      _root_.Math.Probability.CompactStoppingLaw.tendsto_realMass_of_isClopen
        hlaw
        (_root_.Math.Probability.compactStoppingTime_finiteSingleton_isClopen time)
    have hzeroLimit : Tendsto (fun n ↦
        (lawSeq n).realMass
          {(time : _root_.Math.Probability.CompactStoppingTime)})
        atTop (nhds 0) :=
      tendsto_const_nhds.congr'
        ((hzero time).mono fun _ hn ↦ hn.symm)
    exact tendsto_nhds_unique hlimit hzeroLimit
  have hfinitePMF (time : ℕ) :
      (law.toPMF
        (time : _root_.Math.Probability.CompactStoppingTime)).toReal = 0 := by
    rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_apply_toReal]
    exact hfinite time
  have hsupportSubset : law.toPMF.support ⊆
      {(⊤ : _root_.Math.Probability.CompactStoppingTime)} := by
    intro choice hchoice
    induction choice using WithTop.recTopCoe with
    | top => simp
    | coe time =>
        exfalso
        have hne : law.toPMF
            (time : _root_.Math.Probability.CompactStoppingTime) ≠ 0 :=
          (PMF.mem_support_iff _ _).mp hchoice
        have hzero : law.toPMF
            (time : _root_.Math.Probability.CompactStoppingTime) = 0 :=
          (ENNReal.toReal_eq_zero_iff _).mp (hfinitePMF time)
            |>.resolve_right (PMF.apply_ne_top _ _)
        exact hne hzero
  have hsupport : law.toPMF.support =
      {(⊤ : _root_.Math.Probability.CompactStoppingTime)} := by
    apply Set.Subset.antisymm hsupportSubset
    obtain ⟨choice, hchoice⟩ := law.toPMF.support_nonempty
    have hchoiceTop : choice =
        (⊤ : _root_.Math.Probability.CompactStoppingTime) := by
      simpa using hsupportSubset hchoice
    subst choice
    simpa using hchoice
  have htop : law.toPMF
      (⊤ : _root_.Math.Probability.CompactStoppingTime) = 1 :=
    (law.toPMF.apply_eq_one_iff _).mpr hsupport
  have hpmf : law.toPMF =
      PMF.pure (⊤ : _root_.Math.Probability.CompactStoppingTime) := by
    apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
    intro choice
    induction choice using WithTop.recTopCoe with
    | top => simp [htop]
    | coe time => simpa using hfinitePMF time
  rw [← _root_.Math.Probability.CompactStoppingLaw.ofPMF_toPMF law]
  exact congrArg _root_.Math.Probability.CompactStoppingLaw.ofPMF hpmf

private theorem compactStoppingLawTailMass_pureNever (horizon : ℕ) :
    compactStoppingLawTailMass
      (_root_.Math.Probability.CompactStoppingLaw.ofPMF
        (PMF.pure
          (⊤ : _root_.Math.Probability.CompactStoppingTime))) horizon = 1 := by
  unfold compactStoppingLawTailMass
  rw [_root_.Math.Probability.CompactStoppingLaw.realMass_eq_pmfMass_toReal _
    (_root_.Math.Probability.compactStoppingTime_tail_isClopen horizon).1.measurableSet]
  rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  unfold _root_.Math.ProbabilityMassFunction.pmfMass
  rw [tsum_eq_single
    (⊤ : _root_.Math.Probability.CompactStoppingTime)]
  · simp [_root_.Math.ProbabilityMassFunction.pmfMask]
  · intro choice hchoice
    unfold _root_.Math.ProbabilityMassFunction.pmfMask
    split_ifs
    · rw [PMF.pure_apply_of_ne _ _ hchoice]
    · rfl

/-- One source-matched inert chronology above a fixed limiting joint point.

The terminal label and limiting point are fixed.  At every selected depth,
the literal all-Continue prefix preserves that depth's suffix semantic pair
and full terminal law exactly, and the same finite terminal label has positive
mass in both source and shifted stages.  The depth-dependent coordinates are
only asserted to converge jointly to `point`; no cross-depth equality of
semantic pairs or full terminal laws is claimed.

After one strict subsequence, every coordinate compact stopping-law limit is
literally the Dirac law at Never.  These marginal weak limits do not recover
the positive joint finite terminal atom retained by the relative timing of
the actual profiles. -/
structure QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point) where
  chronologyIndex : ℕ → ℕ
  chronologyIndex_strictMono : StrictMono chronologyIndex
  suffixProfile : ℕ → (quittingGame reward).BehaviorProfile
  cutoff : ℕ → ℕ
  stage : ℕ → ℕ
  roots : ℕ → List (iota → PMF Bool)
  roots_length : ∀ n, (roots n).length = chronologyIndex n + 1
  requestedDepth_lt_roots_length : ∀ n, n < (roots n).length
  rootStack : ∀ n,
    IsQuittingCapNashRootStack reward (roots n) (suffixProfile n)
  cap_uniqueAllContinue : ∀ n, ∀ candidate : iota → PMF Bool,
    IsεQuittingRootNash reward
        (quittingTerminalSemanticPair reward (suffixProfile n)).2 0 candidate →
      candidate = (quittingAllContinueRoot : iota → PMF Bool)
  roots_eq_replicate_allContinue : ∀ n,
    roots n = List.replicate (roots n).length
      (quittingAllContinueRoot : iota → PMF Bool)
  absorptionSum_eq_zero : ∀ n,
    quittingCapNashStackAbsorptionSum (roots n) = 0
  pointAtom_pos : 0 < point.2 (some atom.terminal)
  sourceAtom_cumulative_pos : ∀ n,
    point.2 (some atom.terminal) / 2 <
      ∑ time ∈ Finset.range (cutoff n),
        quittingStageCoalitionMass reward
          (suffixProfile n) time atom.terminal
  stage_lt_cutoff : ∀ n, stage n < cutoff n
  sourceAtom_pos : ∀ n, 0 < quittingStageCoalitionMass reward
    (suffixProfile n) (stage n) atom.terminal
  shiftedSourceAtom_pos : ∀ n, 0 < quittingStageCoalitionMass reward
    (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n))
    ((roots n).length + stage n) atom.terminal
  semanticPair_eq : ∀ n,
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n)) =
      quittingTerminalSemanticPair reward (suffixProfile n)
  terminalOutcomeMass_eq : ∀ n,
    quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n)) =
      quittingTerminalOutcomeMass reward (suffixProfile n)
  suffix_joint_tendsto : Tendsto (fun n ↦
    (quittingTerminalSemanticPair reward (suffixProfile n),
      quittingTerminalOutcomeMass reward (suffixProfile n)))
    atTop (nhds point)
  prefixed_joint_tendsto : Tendsto (fun n ↦
    (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n)),
      quittingTerminalOutcomeMass reward
        (quittingLiteralRootStackProfile reward (roots n) (suffixProfile n))))
    atTop (nhds point)
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  marginalLimit : iota → _root_.Math.Probability.CompactStoppingLaw
  marginal_tendsto : ∀ player, Tendsto (fun n ↦
    quittingCompactStoppingLawsOfProfile reward
      (quittingLiteralRootStackProfile reward
        (roots (subseq n)) (suffixProfile (subseq n))) player)
    atTop (nhds (marginalLimit player))
  marginalLimit_eq_pureNever : ∀ player,
    marginalLimit player =
      _root_.Math.Probability.CompactStoppingLaw.ofPMF
        (PMF.pure (⊤ : _root_.Math.Probability.CompactStoppingTime))

/-- Near-minimum cap freezing turns the source chronology of one fixed atom
into the pure-Never marginal-limit normal form.  The target joint point is
retained as a limit, not upgraded to an exact value at each selected depth. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_pureNeverMarginalLimit
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (point : QuittingTerminalSemanticLawPoint iota)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    Nonempty
      (QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
        reward point atom) := by
  obtain ⟨epsilon, hepsilon, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPositive hminimum
  obtain ⟨profiles, cutoff, mark, roots, hprofiles, hlength,
      hstack, _hdebt, hatomEventually⟩ := atom.chronology
  have hpairTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp hprofiles
  have hdebtTendsto : Tendsto
      (fun n ↦ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (profiles n)))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairTendsto
  have hnearEventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (profiles n)) <
        quittingTerminalSemanticDebtSum point.1 + epsilon :=
    (tendsto_order.1 hdebtTendsto).2
      (quittingTerminalSemanticDebtSum point.1 + epsilon) (by linarith)
  have hdataEventually := hatomEventually.and hnearEventually
  rw [eventually_atTop] at hdataEventually
  obtain ⟨first, hfirst⟩ := hdataEventually
  let index : ℕ → ℕ := fun n ↦ n + first
  let suffix : ℕ → (quittingGame reward).BehaviorProfile :=
    fun n ↦ profiles (index n)
  let selectedCutoff : ℕ → ℕ := fun n ↦ cutoff (index n)
  let selectedStage : ℕ → ℕ := fun n ↦ mark (index n)
  let selectedRoots : ℕ → List (iota → PMF Bool) :=
    fun n ↦ roots (index n)
  let prefixed : ℕ → (quittingGame reward).BehaviorProfile :=
    fun n ↦ quittingLiteralRootStackProfile reward
      (selectedRoots n) (suffix n)
  have hindexStrict : StrictMono index := by
    intro a b hab
    dsimp only [index]
    omega
  have hindexTendsto : Tendsto index atTop atTop :=
    hindexStrict.tendsto_atTop
  have hdata (n : ℕ) := hfirst (index n) (by
    dsimp only [index]
    omega)
  have hselectedLength (n : ℕ) :
      (selectedRoots n).length = index n + 1 := by
    simpa only [selectedRoots] using hlength (index n)
  have hdepth (n : ℕ) : n < (selectedRoots n).length := by
    rw [hselectedLength]
    dsimp only [index]
    omega
  have hselectedStack (n : ℕ) :
      IsQuittingCapNashRootStack reward (selectedRoots n) (suffix n) := by
    simpa only [selectedRoots, suffix] using hstack (index n)
  have hunique (n : ℕ) : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward
          (quittingTerminalSemanticPair reward (suffix n)).2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
    intro candidate hcandidate
    have hprofileMem : quittingTerminalSemanticPair reward (suffix n) ∈
        quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPair_mem_carrier reward (suffix n)
    exact hfreeze (quittingTerminalSemanticPair reward (suffix n))
      hprofileMem (by simpa only [suffix] using (hdata n).2.le)
      candidate hcandidate
  have hstackData (n : ℕ) :=
    capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap
      reward (suffix n) (selectedRoots n) (hunique n) (hselectedStack n)
  have hcharge (n : ℕ) :=
    capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap
      reward (suffix n) (selectedRoots n) (hunique n) (hselectedStack n)
  have hlaw (n : ℕ) :=
    capNashRootStack_terminalOutcomeMass_eq_of_unique_terminalCap
      reward (suffix n) (selectedRoots n) (hunique n) (hselectedStack n)
  have hsuffixJoint : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (suffix n),
        quittingTerminalOutcomeMass reward (suffix n)))
      atTop (nhds point) := by
    simpa [suffix, Function.comp_def] using
      hprofiles.comp hindexTendsto
  have hprefixedJoint : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (prefixed n),
        quittingTerminalOutcomeMass reward (prefixed n)))
      atTop (nhds point) := by
    apply hsuffixJoint.congr'
    filter_upwards [] with n
    dsimp only [prefixed]
    rw [(hstackData n).2, hlaw n]
  obtain ⟨laws, subseq, hsubseq, hlaws⟩ :=
    exists_quittingCompactStoppingLawsOfProfile_tendsto_subseq
      reward prefixed
  have hlawsPureNever (player : iota) : laws player =
      _root_.Math.Probability.CompactStoppingLaw.ofPMF
        (PMF.pure
          (⊤ : _root_.Math.Probability.CompactStoppingTime)) := by
    apply compactStoppingLaw_eq_pureNever_of_finiteMass_eventually_zero
      (hlaws player)
    intro time
    filter_upwards [eventually_ge_atTop time] with n hn
    have hnSubseq : n ≤ subseq n := hsubseq.id_le n
    have htime : time < (selectedRoots (subseq n)).length :=
      lt_of_le_of_lt (hn.trans hnSubseq) (hdepth (subseq n))
    dsimp only [prefixed]
    rw [(hstackData (subseq n)).1]
    exact quittingCompactStoppingLaw_finiteMass_literal_allContinue_eq_zero
      reward (suffix (subseq n)) (selectedRoots (subseq n)).length
        time htime player
  exact ⟨{
    chronologyIndex := index
    chronologyIndex_strictMono := hindexStrict
    suffixProfile := suffix
    cutoff := selectedCutoff
    stage := selectedStage
    roots := selectedRoots
    roots_length := hselectedLength
    requestedDepth_lt_roots_length := hdepth
    rootStack := hselectedStack
    cap_uniqueAllContinue := hunique
    roots_eq_replicate_allContinue := fun n ↦ (hstackData n).1
    absorptionSum_eq_zero := hcharge
    pointAtom_pos := atom.terminalMass_pos
    sourceAtom_cumulative_pos := fun n ↦ by
      simpa only [suffix, selectedCutoff] using (hdata n).1.1
    stage_lt_cutoff := fun n ↦ by
      simpa only [selectedStage, selectedCutoff] using (hdata n).1.2.1
    sourceAtom_pos := fun n ↦ by
      simpa only [suffix, selectedStage] using (hdata n).1.2.2.1
    shiftedSourceAtom_pos := fun n ↦ by
      simpa only [suffix, selectedStage, selectedRoots,
        hlength (index n)] using (hdata n).1.2.2.2
    semanticPair_eq := fun n ↦ (hstackData n).2
    terminalOutcomeMass_eq := hlaw
    suffix_joint_tendsto := hsuffixJoint
    prefixed_joint_tendsto := by simpa only [prefixed] using hprefixedJoint
    subseq := subseq
    subseq_strictMono := hsubseq
    marginalLimit := laws
    marginal_tendsto := by simpa only [prefixed] using hlaws
    marginalLimit_eq_pureNever := hlawsPureNever }⟩

/-- The selected actual marginal-law sequence of the pure-Never normal form. -/
def QuittingMinimumLawCausalSuffixPureNeverMarginalLimit.selectedMarginalLawSequence
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) :
    ℕ → iota → _root_.Math.Probability.CompactStoppingLaw :=
  fun n player ↦ quittingCompactStoppingLawsOfProfile reward
    (quittingLiteralRootStackProfile reward
      (packet.roots (packet.subseq n))
      (packet.suffixProfile (packet.subseq n))) player

namespace QuittingMinimumLawCausalSuffixPureNeverMarginalLimit

/-- Vanishing-error Nash roots against the selected literal suffix caps have
vanishing one-stage absorption.  The cap sequence is the one retained by the
causal packet and converges to the displayed minimum cap; no cap is
recomputed from marginal limits.

This rules out macroscopic approximate-prefix escape at the same source caps.
It does not rule out vanishing-absorption tangent or paid structure. -/
theorem approximateRoot_absorption_tendsto_zero
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (error : ℕ → ℝ) (root : ℕ → QuittingRootSimplex iota)
    (herror : Tendsto error atTop (nhds 0))
    (hnash : ∀ n, IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward (packet.suffixProfile n)).2
      (error n) (quittingRootOfSimplex (root n))) :
    Tendsto (fun n ↦ quittingSimplexAbsorptionMass (root n))
      atTop (nhds 0) := by
  have hpairTendsto : Tendsto (fun n ↦
      quittingTerminalSemanticPair reward (packet.suffixProfile n))
      atTop (nhds point.1) :=
    continuous_fst.continuousAt.tendsto.comp packet.suffix_joint_tendsto
  have hpointMem : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    (quittingTerminalSemanticCarrier_isCompact reward).isClosed.mem_of_tendsto
      hpairTendsto (Filter.Eventually.of_forall fun n ↦
        quittingTerminalSemanticPair_mem_carrier reward
          (packet.suffixProfile n))
  obtain ⟨radius, hradius, hfreeze⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum point.1)
        hminimumPositive hminimum
  have hpointUnique : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward point.1.2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
    exact hfreeze point.1 hpointMem (by linarith)
  have hcapTendsto : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (packet.suffixProfile n)).2)
      atTop (nhds point.1.2) :=
    continuous_snd.continuousAt.tendsto.comp hpairTendsto
  have hscaledError : Tendsto
      (fun n ↦ (Fintype.card iota : ℝ) * error n)
      atTop (nhds 0) := by
    simpa using herror.const_mul (Fintype.card iota : ℝ)
  apply tendsto_order.2
  constructor
  · intro lower hlower
    filter_upwards [] with n
    have hnonneg : 0 ≤ quittingSimplexAbsorptionMass (root n) := by
      rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
      exact quittingRootAbsorptionMass_nonneg _
    exact hlower.trans_le hnonneg
  · intro eta heta
    obtain ⟨moat, hmoat, hnear⟩ :=
      exists_eventually_absorptionNashDefect_moat_of_unique_allContinue
        reward point.1.2 eta heta hpointUnique
    have hcapNear := hcapTendsto.eventually hnear
    have herrorSmall : ∀ᶠ n in atTop,
        (Fintype.card iota : ℝ) * error n < moat :=
      (tendsto_order.1 hscaledError).2 moat hmoat
    filter_upwards [hcapNear, herrorSmall] with n hnearCap hsmall
    apply lt_of_not_ge
    intro habsorption
    have hdefectLower := hnearCap (root n) habsorption
    have hdefectUpper :=
      quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
        reward
          (quittingTerminalSemanticPair reward (packet.suffixProfile n)).2
          (quittingRootOfSimplex (root n)) (error n) (hnash n)
    linarith

/-- At every fixed horizon, the joint late-or-Never product along the
selected actual subsequence tends to one.  The horizon is fixed before the
limit; no uniform-in-horizon convergence is asserted. -/
theorem jointTailProduct_tendsto_one
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) (horizon : ℕ) :
    Tendsto (fun n ↦ quittingJointTailProduct
      (packet.selectedMarginalLawSequence n) horizon) atTop (nhds 1) := by
  have hlimit := quittingJointTailProduct_tendsto
    packet.marginal_tendsto horizon
  have hproduct : quittingJointTailProduct packet.marginalLimit horizon = 1 := by
    unfold quittingJointTailProduct
    apply Finset.prod_eq_one
    intro player _
    rw [packet.marginalLimit_eq_pureNever player]
    exact compactStoppingLawTailMass_pureNever horizon
  rw [hproduct] at hlimit
  change Tendsto (fun n ↦ quittingJointTailProduct
    (quittingCompactStoppingLawsOfProfile reward
      (quittingLiteralRootStackProfile reward
        (packet.roots (packet.subseq n))
        (packet.suffixProfile (packet.subseq n)))) horizon)
    atTop (nhds 1)
  exact hlimit

/-- For every owner and fixed horizon, the product of that owner's opponent
late-or-Never masses along the selected actual subsequence tends to one. -/
theorem opponentTailProduct_tendsto_one
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) (owner : iota) (horizon : ℕ) :
    Tendsto (fun n ↦ quittingOpponentTailProduct
      (packet.selectedMarginalLawSequence n) owner horizon)
      atTop (nhds 1) := by
  have hlimit := quittingOpponentTailProduct_tendsto
    packet.marginal_tendsto owner horizon
  have hproduct : quittingOpponentTailProduct
      packet.marginalLimit owner horizon = 1 := by
    unfold quittingOpponentTailProduct
    apply Finset.prod_eq_one
    intro player _
    rw [packet.marginalLimit_eq_pureNever player]
    exact compactStoppingLawTailMass_pureNever horizon
  rw [hproduct] at hlimit
  change Tendsto (fun n ↦ quittingOpponentTailProduct
    (quittingCompactStoppingLawsOfProfile reward
      (quittingLiteralRootStackProfile reward
        (packet.roots (packet.subseq n))
        (packet.suffixProfile (packet.subseq n)))) owner horizon)
    atTop (nhds 1)
  exact hlimit

/-- The selected marginal sequence is not jointly tight.  This is a
fixed-horizon consequence of convergence to one, not a uniform-in-horizon
limit statement or a uniform-equilibrium contradiction. -/
theorem not_jointTight
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) :
    ¬ QuittingJointTightLawSequence packet.selectedMarginalLawSequence := by
  intro htight
  obtain ⟨horizon, hsmall⟩ := htight (1 / 2) (by norm_num)
  have hlarge : ∀ᶠ n in atTop, 1 / 2 < quittingJointTailProduct
      (packet.selectedMarginalLawSequence n) horizon :=
    (tendsto_order.1 (packet.jointTailProduct_tendsto_one horizon)).1
      (1 / 2) (by norm_num)
  obtain ⟨n, hnSmall, hnLarge⟩ := (hsmall.and hlarge).exists
  linarith

/-- For each displayed owner, its opponent-tail sequence is not tight. -/
theorem not_opponentTightAt
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) (owner : iota) :
    ¬ QuittingOpponentTightAtLawSequence
      packet.selectedMarginalLawSequence owner := by
  intro htight
  obtain ⟨horizon, hsmall⟩ := htight (1 / 2) (by norm_num)
  have hlarge : ∀ᶠ n in atTop, 1 / 2 < quittingOpponentTailProduct
      (packet.selectedMarginalLawSequence n) owner horizon :=
    (tendsto_order.1
      (packet.opponentTailProduct_tendsto_one owner horizon)).1
        (1 / 2) (by norm_num)
  obtain ⟨n, hnSmall, hnLarge⟩ := (hsmall.and hlarge).exists
  linarith

/-- With a displayed player available, the selected marginal sequence fails
the uniform opponent-tightness condition. -/
theorem not_opponentTight
    [Nonempty iota]
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    {point : QuittingTerminalSemanticLawPoint iota}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (packet : QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
      reward point atom) :
    ¬ QuittingOpponentTightLawSequence
      packet.selectedMarginalLawSequence := by
  intro htight
  let owner : iota := Classical.choice inferInstance
  exact packet.not_opponentTightAt owner (htight owner)

end QuittingMinimumLawCausalSuffixPureNeverMarginalLimit

/-- Punishment-normality and failure of uniform-payoff existence select the
fixed finite atom needed for the pure-Never marginal-limit normal form at
every supplied minimizing joint-law point. -/
theorem exists_minimumLawCausalSuffixPureNeverMarginalLimit_of_punishmentNormal_of_not_uniform
    [Nonempty iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (hno : ¬∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (point : QuittingTerminalSemanticLawPoint iota)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ atom : QuittingMinimumLawCausalSuffixAtom reward point,
      Nonempty
        (QuittingMinimumLawCausalSuffixPureNeverMarginalLimit
          reward point atom) := by
  obtain ⟨atom⟩ :=
    nonempty_minimumLawCausalSuffixAtom_of_punishmentNormal_of_not_uniformPayoff
      reward hno hnormal point hpoint hminimum
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr
      hno
  have hcarrier := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hminimumValue : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward :=
    (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      point.1 hcarrier hminimum).symm
  have hminimumPositive : 0 <
      quittingTerminalSemanticDebtSum point.1 := by
    rw [hminimumValue]
    exact hinf
  exact ⟨atom, atom.nonempty_pureNeverMarginalLimit
    reward point hminimum hminimumPositive⟩


end GameTheory
