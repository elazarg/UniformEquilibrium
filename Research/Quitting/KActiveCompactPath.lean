/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath

/-!
# Compact chronological extraction preserving `K`-active support

The production circulation compiler constructs forward rows with a single
positive hazard, then reverses finite prefixes and passes to a compact limit.
Its public relation remembers Bellman evaluation, support-perfect inequalities
and positive absorption, but not the finite support bound.

This experiment adds the missing closed invariant.  A nonnegative hazard
vector has at most `K` positive coordinates exactly when every squarefree
monomial on more than `K` coordinates vanishes.  The monomial formulation is
closed, so compact chronological extraction preserves it.
-/

noncomputable section

namespace GameTheory

open Finset Set StochasticGame Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Canonical positive support -/

/-- Players with strictly positive Quit probability at a PMF root. -/
def quittingPositiveHazardSupport (root : ι → PMF Bool) : Finset ι :=
  Finset.univ.filter fun who => 0 < hazardOfRoot root who

omit [DecidableEq ι] in
/-- Every player outside the canonical positive-hazard support surely
Continues. -/
theorem quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport
    (root : ι → PMF Bool) {who : ι}
    (hwho : who ∉ quittingPositiveHazardSupport root) :
    root who = PMF.pure false := by
  have hzero : hazardOfRoot root who = 0 := by
    have hnonpos : ¬ 0 < hazardOfRoot root who := by
      simpa [quittingPositiveHazardSupport] using hwho
    exact le_antisymm (le_of_not_gt hnonpos) (hazardOfRoot_nonneg root who)
  have hround := congrFun (rootOfHazard_hazardOfRoot root) who
  rw [← hround]
  unfold rootOfHazard
  apply PMF.ext
  intro action
  cases action <;>
    simp [quittingHazardCoin, PMF.ofFintype_apply, hzero]

/-- Cardinal support predicate on PMF roots. -/
def HasQuittingSupportCardAtMost (K : ℕ) (root : ι → PMF Bool) : Prop :=
  (quittingPositiveHazardSupport root).card ≤ K

/-! ## The closed monomial formulation -/

/-- Polynomial support-card condition on real hazard rows. -/
def IsQuittingHazardKActive (K : ℕ) (x : ι → ℝ) : Prop :=
  ∀ coalition : Finset ι, K < coalition.card →
    (∏ who ∈ coalition, x who) = 0

/-- Polynomial support-card condition in simplex coordinates. -/
def IsQuittingSimplexKActive (K : ℕ) (root : QuittingRootSimplex ι) : Prop :=
  ∀ coalition : Finset ι, K < coalition.card →
    (∏ who ∈ coalition, root who true) = 0

omit [DecidableEq ι] in
/-- The simplex `K`-active locus is closed. -/
theorem isClosed_isQuittingSimplexKActive (K : ℕ) :
    IsClosed {root : QuittingRootSimplex ι |
      IsQuittingSimplexKActive K root} := by
  have hclosed : ∀ coalition : Finset ι,
      IsClosed {root : QuittingRootSimplex ι |
        (∏ who ∈ coalition, root who true) = 0} := by
    intro coalition
    apply isClosed_eq
    · exact continuous_finsetProd (s := coalition) fun who _ =>
        (continuous_apply true).comp
          (continuous_subtype_val.comp (continuous_apply who))
    · exact continuous_const
  rw [show {root : QuittingRootSimplex ι |
        IsQuittingSimplexKActive K root} =
      ⋂ coalition : Finset ι, ⋂ (_h : K < coalition.card),
        {root | (∏ who ∈ coalition, root who true) = 0} by
    ext root
    simp [IsQuittingSimplexKActive]]
  exact isClosed_iInter fun coalition =>
    isClosed_iInter fun _h => hclosed coalition

omit [DecidableEq ι] in
/-- Hazard-row `K`-activity is preserved by conversion to simplex roots. -/
theorem isQuittingSimplexKActive_quittingRootSimplexOfHazard
    (K : ℕ) (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hactive : IsQuittingHazardKActive K x) :
    IsQuittingSimplexKActive K
      (quittingRootSimplexOfHazard x hx0 hx1) := by
  intro coalition hlarge
  have hcoordinate : ∀ who,
      quittingRootSimplexOfHazard x hx0 hx1 who true = x who := by
    intro who
    rw [← quittingRootOfSimplex_apply_toReal,
      quittingRootOfSimplex_quittingRootSimplexOfHazard]
    simp [rootOfHazard]
  simp_rw [hcoordinate]
  exact hactive coalition hlarge

omit [DecidableEq ι] in
/-- The closed monomial condition gives the literal positive-support card
bound on the associated PMF root. -/
theorem hasQuittingSupportCardAtMost_quittingRootOfSimplex
    (K : ℕ) (root : QuittingRootSimplex ι)
    (hactive : IsQuittingSimplexKActive K root) :
    HasQuittingSupportCardAtMost K (quittingRootOfSimplex root) := by
  unfold HasQuittingSupportCardAtMost
  by_contra hcard
  have hlarge : K < (quittingPositiveHazardSupport
      (quittingRootOfSimplex root)).card := by omega
  have hzero := hactive
    (quittingPositiveHazardSupport (quittingRootOfSimplex root)) hlarge
  have hpos : 0 < ∏ who ∈
      quittingPositiveHazardSupport (quittingRootOfSimplex root),
        root who true := by
    apply Finset.prod_pos
    intro who hwho
    have hhazard : 0 < hazardOfRoot (quittingRootOfSimplex root) who :=
      (Finset.mem_filter.mp hwho).2
    simpa [hazardOfRoot, quittingRootOfSimplex_apply_toReal] using hhazard
  linarith

/-! ## A closed chronological edge carrying the support bound -/

/-- The production circulation edge augmented by the closed `K`-active
invariant on its current root. -/
def IsQuittingKActiveCirculationPathEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (δ charge : ℝ)
    (current tail : QuittingNashBellmanPoint ι) : Prop :=
  IsQuittingCirculationPathEdge reward δ charge current tail ∧
    IsQuittingSimplexKActive K current.2

/-- The box-restricted augmented edge graph remains closed. -/
theorem isClosed_quittingKActiveCirculationPathEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (lower : Payoff ι) (K : ℕ) (δ charge : ℝ) :
    IsClosed {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingCirculationPathBox bound lower ∧
      edge.2 ∈ quittingCirculationPathBox bound lower ∧
      IsQuittingKActiveCirculationPathEdge
        reward K δ charge edge.1 edge.2} := by
  have hbase := isClosed_quittingCirculationPathEdgeGraph
    reward bound lower δ charge
  have hactive : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        IsQuittingSimplexKActive K edge.1.2} :=
    (isClosed_isQuittingSimplexKActive K).preimage
      (continuous_snd.comp continuous_fst)
  rw [show {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingCirculationPathBox bound lower ∧
      edge.2 ∈ quittingCirculationPathBox bound lower ∧
      IsQuittingKActiveCirculationPathEdge
        reward K δ charge edge.1 edge.2} =
      {edge | edge.1 ∈ quittingCirculationPathBox bound lower ∧
        edge.2 ∈ quittingCirculationPathBox bound lower ∧
        IsQuittingCirculationPathEdge reward δ charge edge.1 edge.2} ∩
      {edge | IsQuittingSimplexKActive K edge.1.2} by
    ext edge
    constructor
    · rintro ⟨hcurrent, htail, hedge, hactive⟩
      exact ⟨⟨hcurrent, htail, hedge⟩, hactive⟩
    · rintro ⟨⟨hcurrent, htail, hedge⟩, hactive⟩
      exact ⟨hcurrent, htail, hedge, hactive⟩]
  exact hbase.inter hactive

/-! ## Singleton rows are genuinely `1/N` -/

omit [Fintype ι] in
theorem isQuittingHazardKActive_singletonRow
    (h : ℝ) (owner : ι) :
    IsQuittingHazardKActive 1 (singletonRow h owner) := by
  intro coalition hlarge
  have hnot : ¬ coalition ⊆ ({owner} : Finset ι) := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    simp at hcard
    omega
  rw [Finset.not_subset] at hnot
  obtain ⟨who, hwho, houtside⟩ := hnot
  apply Finset.prod_eq_zero hwho
  have hne : who ≠ owner := by simpa using houtside
  exact singletonRow_of_ne h hne

omit [Fintype ι] in
theorem isQuittingHazardKActive_multiRow
    {L : ℕ} [NeZero L] (word : ZMod L → ℕ → ι)
    (β : ZMod L → ℝ) (N time : ℕ) :
    IsQuittingHazardKActive 1 (multiRow word β N time) := by
  unfold multiRow
  exact isQuittingHazardKActive_singletonRow _ _

/-! ## Compact reverse extraction preserving `K`-activity -/

/-- **`K`-active chronological compact extraction.** A bounded forward
Bellman orbit whose rows have support cardinality at most `K` yields an
infinite chronological path with the same literal PMF-root support bound.
-/
theorem exists_chronologicalKActiveSupportPath_of_forwardOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (K : ℕ) (row : ℕ → ι → ℝ) (forward : ℕ → Payoff ι)
    (lower : Payoff ι) {δ charge bound : ℝ}
    (hrow0 : ∀ time who, 0 ≤ row time who)
    (hrow1 : ∀ time who, row time who ≤ 1)
    (hrowK : ∀ time, IsQuittingHazardKActive K (row time))
    (hforwardBound : ∀ time who, |forward time who| ≤ bound)
    (hforwardLower : ∀ time who, lower who ≤ forward time who)
    (hpolicy : ∀ time,
      forward (time + 1) = quittingRootSuccessorPayoff reward
        (forward time)
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)))
    (hsupport : ∀ time,
      IsQuittingRootSupportApproxNash reward (forward time) δ
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)))
    (habsorption : ∀ time,
      charge ≤ quittingRootAbsorptionMass
        (rootOfHazard (row time) (hrow0 time) (hrow1 time))) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ bound) ∧
      (∀ time who, lower who ≤ value time who) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      (∀ time, IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time)) ∧
      (∀ time, charge ≤ quittingRootAbsorptionMass (roots time)) ∧
      ∀ time, HasQuittingSupportCardAtMost K (roots time) := by
  let simplexRow : ℕ → QuittingRootSimplex ι :=
    fun time => quittingRootSimplexOfHazard
      (row time) (hrow0 time) (hrow1 time)
  let box : Set (QuittingNashBellmanPoint ι) :=
    quittingCirculationPathBox bound lower
  let relation : QuittingNashBellmanPoint ι →
      QuittingNashBellmanPoint ι → Prop :=
    IsQuittingKActiveCirculationPathEdge reward K δ charge
  have hbox : IsCompact box :=
    quittingCirculationPathBox_isCompact bound lower
  have hgraph : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1 ∈ box ∧ edge.2 ∈ box ∧ relation edge.1 edge.2} := by
    simpa only [box, relation] using
      isClosed_quittingKActiveCirculationPathEdgeGraph
        reward bound lower K δ charge
  have hprefix : ∀ horizon,
      (compactFinitePrefixSolutionSet box relation horizon).Nonempty := by
    intro horizon
    let finitePath : ℕ → QuittingNashBellmanPoint ι := fun time =>
      if time ≤ horizon then
        (forward (horizon - time), simplexRow (horizon - (time + 1)))
      else
        (forward 0, simplexRow 0)
    refine ⟨finitePath, ?_, ?_⟩
    · intro time
      by_cases htime : time ≤ horizon
      · rw [show finitePath time =
          (forward (horizon - time),
            simplexRow (horizon - (time + 1))) by
          simp [finitePath, htime]]
        exact mem_quittingCirculationPathBox_of_bounds
          (simplexRow (horizon - (time + 1)))
          (hforwardBound (horizon - time))
          (hforwardLower (horizon - time))
      · rw [show finitePath time = (forward 0, simplexRow 0) by
          simp [finitePath, htime]]
        exact mem_quittingCirculationPathBox_of_bounds
          (simplexRow 0) (hforwardBound 0) (hforwardLower 0)
    · intro time
      have htime : (time : ℕ) < horizon := time.isLt
      have hcurrent : (time : ℕ) ≤ horizon := htime.le
      have htail : (time : ℕ) + 1 ≤ horizon := htime
      let index := horizon - ((time : ℕ) + 1)
      have hindex : horizon - (time : ℕ) = index + 1 := by
        dsimp only [index]
        omega
      rw [show finitePath time =
          (forward (horizon - (time : ℕ)), simplexRow index) by
        simp [finitePath, hcurrent, index],
        show finitePath ((time : ℕ) + 1) =
          (forward index,
            simplexRow (horizon - (((time : ℕ) + 1) + 1))) by
          simp [finitePath, htail, index]]
      unfold relation IsQuittingKActiveCirculationPathEdge
      constructor
      · unfold IsQuittingCirculationPathEdge
        constructor
        · rw [hindex]
          simpa [simplexRow] using hpolicy index
        constructor
        · apply (isQuittingSimplexRootSupportApproxNash_iff
            reward (forward index) δ (simplexRow index)).2
          simpa [simplexRow] using hsupport index
        · rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
          simpa [simplexRow] using habsorption index
      · exact isQuittingSimplexKActive_quittingRootSimplexOfHazard
          K (row index) (hrow0 index) (hrow1 index) (hrowK index)
  obtain ⟨state, hstateBox, hstateEdge⟩ :=
    exists_infiniteChain_of_finitePrefixes box relation hbox hgraph hprefix
  let value : ℕ → Payoff ι := fun time => (state time).1
  let roots : ℕ → ι → PMF Bool :=
    fun time => quittingRootOfSimplex (state time).2
  refine ⟨value, roots, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro time who
    exact abs_le.mpr
      ⟨(hstateBox time).1.1 who, (hstateBox time).1.2 who⟩
  · intro time who
    exact (hstateBox time).2 who
  · intro time
    exact (hstateEdge time).1.1
  · intro time
    exact (isQuittingSimplexRootSupportApproxNash_iff
      reward (value (time + 1)) δ (state time).2).1
        (hstateEdge time).1.2.1
  · intro time
    rw [← quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
    exact (hstateEdge time).1.2.2
  · intro time
    exact hasQuittingSupportCardAtMost_quittingRootOfSimplex
      K (state time).2 (hstateEdge time).2

/-! ## Applying the invariant to arbitrary-player face circulations -/

/-- **Every multi-owner circulation compiles to a literal `1/N` path.**
Although an ideal phase may mix arbitrarily many owners, the balanced-word
realization serializes them.  Closed support extraction now proves that the
resulting infinite chronological PMF path still has at most one positive
quitting hazard at every stage. -/
theorem exists_oneActiveSupportRationalDivergentPath_of_multiCirculation
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash
          (rewardOfWeight r) plan ε ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      (∀ target time,
        quittingPunishmentValue (rewardOfWeight r) target - ε ≤
          quittingRootSequenceTerminalValue
            (rewardOfWeight r) plan target time) ∧
      ∀ time, HasQuittingSupportCardAtMost 1 (plan time) := by
  obtain ⟨N, β, word, hN, hβ0, hβ1, hβN,
      hforwardPolicy, hforwardSupport, hforwardFloor,
      hquitLower, _hprefix⟩ :=
    exists_multiCirculation_orbit_uniform_prefix C M hM0 hM s hs
      a ha ha1 ε hε
  let row : ℕ → ι → ℝ := multiRow word β N
  let forward : ℕ → Payoff ι := multiActual C word β N
  let lower : Payoff ι := fun who => floor who - ε
  let bound : ℝ := M + ∑ who, |C.vertex 0 who|
  let charge : ℝ := (1 - a) / (N : ℝ)
  have hrow0 : ∀ time who, 0 ≤ row time who := by
    intro time who
    have hinterval := singletonRow_mem_unitInterval
      (1 - β (chainPhase L N time))
      (sub_nonneg.mpr (hβ1 (chainPhase L N time)))
      (by linarith [hβ0 (chainPhase L N time)])
      (word (chainPhase L N time) (chainStep L N time)) who
    simpa [row, multiRow] using hinterval.1
  have hrow1 : ∀ time who, row time who ≤ 1 := by
    intro time who
    have hinterval := singletonRow_mem_unitInterval
      (1 - β (chainPhase L N time))
      (sub_nonneg.mpr (hβ1 (chainPhase L N time)))
      (by linarith [hβ0 (chainPhase L N time)])
      (word (chainPhase L N time) (chainStep L N time)) who
    simpa [row, multiRow] using hinterval.2
  have hrowK : ∀ time, IsQuittingHazardKActive 1 (row time) := by
    intro time
    exact isQuittingHazardKActive_multiRow word β N time
  have hbound0 : 0 ≤ bound := by
    dsimp only [bound]
    exact add_nonneg hM0 (Finset.sum_nonneg fun who _ =>
      abs_nonneg (C.vertex 0 who))
  have hforwardBound : ∀ time who, |forward time who| ≤ bound := by
    intro time who
    simpa [forward, bound] using
      abs_multiActual_le_reward_add_vertex C word β N hβ0 hβ1
        M hM0 hM time who
  have hforwardLower : ∀ time who, lower who ≤ forward time who := by
    intro time who
    simpa [lower, forward] using hforwardFloor time who
  have hpolicy : ∀ time,
      forward (time + 1) = quittingRootSuccessorPayoff
        (rewardOfWeight r) (forward time)
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
    intro time
    calc
      forward (time + 1) = oneStageNext r (row time) (forward time) := by
        funext who
        simpa [forward, row] using hforwardPolicy time who
      _ = quittingRootSuccessorPayoff
          (rewardOfWeight r) (forward time)
          (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
        symm
        exact quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext
          r (row time) (hrow0 time) (hrow1 time) (forward time)
  have hsupport : ∀ time,
      IsQuittingRootSupportApproxNash
        (rewardOfWeight r) (forward time) ε
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
    intro time
    exact
      isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow
        r (row time) (hrow0 time) (hrow1 time) (forward time) ε
        (by simpa [row, forward] using hforwardSupport time)
  have habsorption : ∀ time,
      charge ≤ quittingRootAbsorptionMass
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
    intro time
    rw [quittingRootAbsorptionMass_rootOfHazard]
    simpa [charge, row] using hquitLower time
  obtain ⟨value, roots, hvalueBound, hvalueLower,
      hvaluePolicy, hvalueSupport, hvalueAbsorption, hvalueK⟩ :=
    exists_chronologicalKActiveSupportPath_of_forwardOrbit
      (rewardOfWeight r) 1 row forward lower hrow0 hrow1 hrowK
      hforwardBound hforwardLower hpolicy hsupport habsorption
  have hcharge : 0 < charge := by
    dsimp only [charge]
    exact div_pos (sub_pos.mpr ha1) (by exact_mod_cast hN)
  have hreward : ∀ terminal who,
      |rewardOfWeight r terminal who| ≤ bound := by
    intro terminal who
    change |r terminal.1 who| ≤ bound
    exact (hM terminal.1 who).trans
      (le_add_of_nonneg_right
        (Finset.sum_nonneg fun player _ => abs_nonneg (C.vertex 0 player)))
  have hselected : ∀ time,
      value time = fun who =>
        quittingRootSequenceTerminalValue
          (rewardOfWeight r) roots who time :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_absorption_lower
      (rewardOfWeight r) roots value hcharge hvalueAbsorption
      hbound0 hreward hvalueBound hvaluePolicy
  have hsupportSequence :
      IsQuittingRootSequenceSupportApproxNash
        (rewardOfWeight r) roots ε := by
    intro time
    have htail :
        quittingRootSequenceTailVector (rewardOfWeight r) roots
            (time + 1) = value (time + 1) := by
      funext who
      change quittingRootSequenceTerminalValue
          (rewardOfWeight r) roots who (time + 1) = value (time + 1) who
      exact (congrFun (hselected (time + 1)) who).symm
    rw [htail]
    exact hvalueSupport time
  have hdiverges : ¬Summable (quittingTotalAbsorptionCharge roots) := by
    apply not_summable_quittingTotalAbsorptionCharge_of_uniform_lower
      roots hcharge
    intro time
    simpa [quittingTotalAbsorptionCharge] using hvalueAbsorption time
  refine ⟨roots, hsupportSequence, hdiverges, ?_, hvalueK⟩
  intro target time
  rw [← congrFun (hselected time) target]
  have hfloor := hpunishmentFloor target
  have hlower := hvalueLower time target
  dsimp only [lower] at hlower
  linarith

/-! ## A general `K/N` path-to-existence interface -/

/-- For every accuracy, a support-rational divergent path whose root support
has cardinality at most `K` at every time. -/
def HasQuittingKActiveSupportRationalDivergentPaths
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (K : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan ε ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      (∀ target time,
        quittingPunishmentValue reward target - ε ≤
          quittingRootSequenceTerminalValue reward plan target time) ∧
      ∀ time, HasQuittingSupportCardAtMost K (plan time)

/-! ## The exact `K/N` hierarchy -/

omit [DecidableEq ι] in
/-- Support-card bounds weaken monotonically with `K`. -/
theorem hasQuittingSupportCardAtMost_mono {K K' : ℕ} (hKK' : K ≤ K')
    {root : ι → PMF Bool} (hroot : HasQuittingSupportCardAtMost K root) :
    HasQuittingSupportCardAtMost K' root := by
  unfold HasQuittingSupportCardAtMost at *
  exact hroot.trans hKK'

omit [DecidableEq ι] in
/-- Every root is automatically `N/N`-active. -/
theorem hasQuittingSupportCardAtMost_fintypeCard (root : ι → PMF Bool) :
    HasQuittingSupportCardAtMost (Fintype.card ι) root := by
  unfold HasQuittingSupportCardAtMost
  simpa using Finset.card_le_univ (quittingPositiveHazardSupport root)

/-- The path hypotheses form an increasing hierarchy in `K`. -/
theorem HasQuittingKActiveSupportRationalDivergentPaths.mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {K K' : ℕ} (hKK' : K ≤ K')
    (hpaths : HasQuittingKActiveSupportRationalDivergentPaths reward K) :
    HasQuittingKActiveSupportRationalDivergentPaths reward K' := by
  intro ε hε
  obtain ⟨plan, hsupport, hdiverges, hir, hK⟩ := hpaths ε hε
  exact ⟨plan, hsupport, hdiverges, hir,
    fun time => hasQuittingSupportCardAtMost_mono hKK' (hK time)⟩

/-- The same path condition with no support-card restriction. -/
def HasQuittingSupportRationalDivergentPaths
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash reward plan ε ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue reward target - ε ≤
          quittingRootSequenceTerminalValue reward plan target time

/-- **`N/N` is exactly the unrestricted problem.**  At the ambient player
cardinality the active-set condition contains no additional information. -/
theorem hasQuittingFintypeCardActivePaths_iff_unrestricted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasQuittingKActiveSupportRationalDivergentPaths reward (Fintype.card ι) ↔
      HasQuittingSupportRationalDivergentPaths reward := by
  constructor
  · intro hpaths ε hε
    obtain ⟨plan, hsupport, hdiverges, hir, _⟩ := hpaths ε hε
    exact ⟨plan, hsupport, hdiverges, hir⟩
  · intro hpaths ε hε
    obtain ⟨plan, hsupport, hdiverges, hir⟩ := hpaths ε hε
    exact ⟨plan, hsupport, hdiverges, hir,
      fun time => hasQuittingSupportCardAtMost_fintypeCard (plan time)⟩

omit [DecidableEq ι] in
/-- A zero-active schedule is identically all-Continue. -/
theorem quittingTotalAbsorptionCharge_eq_zero_of_zeroActive
    (plan : ℕ → ι → PMF Bool)
    (hzero : ∀ time, HasQuittingSupportCardAtMost 0 (plan time))
    (time : ℕ) :
    quittingTotalAbsorptionCharge plan time = 0 := by
  have hempty : quittingPositiveHazardSupport (plan time) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact Nat.le_zero.mp (hzero time)
  have hroot : ∀ who, plan time who = PMF.pure false := by
    intro who
    apply quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport
    rw [hempty]
    simp
  unfold quittingTotalAbsorptionCharge quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp_rw [hroot]
  simp

/-- **`0/N` cannot carry a productive path.**  Thus `K=1` is the first
nontrivial serialized regime, while `K=N` is the original unrestricted one. -/
theorem not_hasQuittingZeroActiveSupportRationalDivergentPaths
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ¬ HasQuittingKActiveSupportRationalDivergentPaths reward 0 := by
  intro hpaths
  obtain ⟨plan, _hsupport, hdiverges, _hir, hzero⟩ :=
    hpaths 1 (by norm_num)
  apply hdiverges
  have hidenticallyZero : quittingTotalAbsorptionCharge plan = 0 := by
    funext time
    exact quittingTotalAbsorptionCharge_eq_zero_of_zeroActive plan hzero time
  rw [hidenticallyZero]
  exact summable_zero

/-- **General `K/N` existence theorem at the path interface.** The ambient
player type remains arbitrary.  Once support-rational divergent witnesses
can be chosen with a uniform support-card bound `K`, the ordinary quitting
game has a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_KActivePaths
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (K : ℕ)
    (hpaths : HasQuittingKActiveSupportRationalDivergentPaths reward K) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
      reward
  intro ε hε
  obtain ⟨plan, hsupport, hdiverges, hir, _hK⟩ := hpaths ε hε
  exact ⟨plan, hsupport, hdiverges, hir⟩

/-- Every arbitrary-player face circulation produces the `K=1` hypothesis
of the general path theorem. -/
theorem hasQuittingOneActiveSupportRationalDivergentPaths_of_multiCirculation
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who) :
    HasQuittingKActiveSupportRationalDivergentPaths
      (rewardOfWeight r) 1 := by
  intro ε hε
  exact exists_oneActiveSupportRationalDivergentPath_of_multiCirculation
    C M hM0 hM s hs a ha ha1 hpunishmentFloor ε hε

/-- Uniform-payoff corollary routed explicitly through the serialized
one-active path invariant. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_oneActiveCirculationPath
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who) :
    ∃ payoff : Payoff ι,
      (quittingGame (rewardOfWeight r)).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_KActivePaths
    (rewardOfWeight r) 1
  exact hasQuittingOneActiveSupportRationalDivergentPaths_of_multiCirculation
    C M hM0 hM s hs a ha ha1 hpunishmentFloor

end GameTheory
