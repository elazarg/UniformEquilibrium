import UniformEquilibrium.Quitting.ControllerTester.FunctionBarrierDuality

/-! # Universal prefix hulls and renewable barrier ledgers -/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Points reached by arbitrary finite literal product-root prefixes from a
seed set. -/
def quittingUniversalPrefixReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) :
    Set (QuittingTerminalSemanticPair ι) :=
  {pair | ∃ tail ∈ seed, ∃ roots : ℕ → ι → PMF Bool, ∃ cutoff : ℕ,
    quittingFinitePrefixSemanticEval reward roots cutoff tail = pair}

/-- Closed universal-prefix hull of a semantic seed set. -/
def quittingUniversalPrefixHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) :
    Set (QuittingTerminalSemanticPair ι) :=
  closure (quittingUniversalPrefixReachable reward seed)

theorem subset_quittingUniversalPrefixReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) :
    seed ⊆ quittingUniversalPrefixReachable reward seed := by
  intro pair hpair
  exact ⟨pair, hpair, fun _ => quittingAllContinueRoot, 0, rfl⟩

theorem subset_quittingUniversalPrefixHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) :
    seed ⊆ quittingUniversalPrefixHull reward seed :=
  (subset_quittingUniversalPrefixReachable reward seed).trans subset_closure

theorem isClosed_quittingUniversalPrefixHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) :
    IsClosed (quittingUniversalPrefixHull reward seed) :=
  isClosed_closure

private theorem quittingFinitePrefixSemanticEval_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (tail : QuittingTerminalSemanticPair ι) :
    quittingFinitePrefixSemanticEval reward (fun
        | 0 => root
        | time + 1 => roots time) (cutoff + 1) tail =
      quittingTerminalSemanticPrefix reward root
        (quittingFinitePrefixSemanticEval reward roots cutoff tail) := by
  simp [quittingFinitePrefixSemanticEval]

theorem quittingTerminalSemanticPrefix_mem_universalPrefixReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingUniversalPrefixReachable reward seed) :
    quittingTerminalSemanticPrefix reward root pair ∈
      quittingUniversalPrefixReachable reward seed := by
  obtain ⟨tail, htail, roots, cutoff, rfl⟩ := hpair
  refine ⟨tail, htail, (fun | 0 => root | time + 1 => roots time),
    cutoff + 1, ?_⟩
  exact quittingFinitePrefixSemanticEval_cons reward root roots cutoff tail

/-- The closed universal hull is invariant under every literal product root. -/
theorem quittingTerminalSemanticPrefix_mem_universalPrefixHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingUniversalPrefixHull reward seed) :
    quittingTerminalSemanticPrefix reward root pair ∈
      quittingUniversalPrefixHull reward seed := by
  let prefixMap := quittingTerminalSemanticPrefix reward root
  have hclosed : IsClosed
      (prefixMap ⁻¹' quittingUniversalPrefixHull reward seed) :=
    (isClosed_quittingUniversalPrefixHull reward seed).preimage
      (continuous_quittingTerminalSemanticPrefix reward root)
  apply (closure_minimal ?_ hclosed) hpair
  intro reachable hreachable
  exact subset_closure <|
    quittingTerminalSemanticPrefix_mem_universalPrefixReachable
      reward seed root reachable hreachable

theorem quittingUniversalPrefixReachable_subset_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hseed : seed ⊆ quittingTerminalSemanticBox ι M) :
    quittingUniversalPrefixReachable reward seed ⊆
      quittingTerminalSemanticBox ι M := by
  rintro pair ⟨tail, htail, roots, cutoff, rfl⟩
  induction cutoff generalizing roots with
  | zero => exact hseed htail
  | succ cutoff ih =>
      simp only [quittingFinitePrefixSemanticEval]
      exact quittingTerminalSemanticPrefix_mem_box reward (roots 0) _ hreward
        (ih (fun time => roots (time + 1)))

theorem quittingUniversalPrefixHull_subset_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hseed : seed ⊆ quittingTerminalSemanticBox ι M) :
    quittingUniversalPrefixHull reward seed ⊆
      quittingTerminalSemanticBox ι M := by
  apply closure_minimal
  · exact quittingUniversalPrefixReachable_subset_box reward seed M hreward hseed
  · exact (quittingTerminalSemanticBox_isCompact M).isClosed

/-- A universally prefixed hull of seeds in a common reward box is compact. -/
theorem isCompact_quittingUniversalPrefixHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hseed : seed ⊆ quittingTerminalSemanticBox ι M) :
    IsCompact (quittingUniversalPrefixHull reward seed) := by
  exact (quittingTerminalSemanticBox_isCompact M).of_isClosed_subset
    (isClosed_quittingUniversalPrefixHull reward seed)
    (quittingUniversalPrefixHull_subset_box reward seed M hreward hseed)

theorem quittingFinitePrefixSemanticEval_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (tail : QuittingTerminalSemanticPair ι)
    (htail : tail ∈ quittingTerminalSemanticBox ι M)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingFinitePrefixSemanticEval reward roots cutoff tail ∈
      quittingTerminalSemanticBox ι M := by
  induction cutoff generalizing roots with
  | zero => exact htail
  | succ cutoff ih =>
      simp only [quittingFinitePrefixSemanticEval]
      exact quittingTerminalSemanticPrefix_mem_box reward (roots 0) _ hreward
        (ih (fun time => roots (time + 1)))

theorem quittingControllerWordInf_le_finitePrefix_of_boxLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (M lower : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι M, lower ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι)
    (htail : tail ∈ quittingTerminalSemanticBox ι M)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingControllerWordInf reward objective tail ≤
      quittingControllerWordInf reward objective
        (quittingFinitePrefixSemanticEval reward roots cutoff tail) := by
  have hwordBox (base : QuittingTerminalSemanticPair ι)
      (hbase : base ∈ quittingTerminalSemanticBox ι M)
      (word : List (QuittingRootSimplex ι)) :
      quittingControllerRootListEvalFrom reward word base ∈
        quittingTerminalSemanticBox ι M := by
    induction word with
    | nil => exact hbase
    | cons root word ih =>
        exact quittingTerminalSemanticPrefix_mem_box reward
          (quittingRootOfSimplex root) _ hreward ih
  have hwordBdd (base : QuittingTerminalSemanticPair ι)
      (hbase : base ∈ quittingTerminalSemanticBox ι M) :
      BddBelow (Set.range fun word : List (QuittingRootSimplex ι) =>
        objective (quittingControllerRootListEvalFrom reward word base)) := by
    refine ⟨lower, ?_⟩
    rintro _ ⟨word, rfl⟩
    exact hlower _ (hwordBox base hbase word)
  induction cutoff generalizing roots with
  | zero => exact le_rfl
  | succ cutoff ih =>
      let suffix := quittingFinitePrefixSemanticEval reward
        (fun time => roots (time + 1)) cutoff tail
      have hsuffix := quittingFinitePrefixSemanticEval_mem_box reward M hreward
        tail htail (fun time => roots (time + 1)) cutoff
      have hstep : quittingControllerWordInf reward objective suffix ≤
          quittingControllerWordInf reward objective
            (quittingTerminalSemanticPrefix reward (roots 0) suffix) := by
        unfold quittingControllerWordInf
        apply le_ciInf
        intro word
        have hword := ciInf_le (hwordBdd suffix hsuffix)
          (word ++ [quittingSimplexOfRoot (roots 0)])
        rw [quittingControllerRootListEvalFrom_append] at hword
        simpa using hword
      exact (ih (fun time => roots (time + 1))).trans
        (by simpa [suffix, quittingFinitePrefixSemanticEval] using hstep)

theorem quittingUniversalPrefixReachable_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (hseed : seed ⊆ quittingTerminalSemanticCarrier reward) :
    quittingUniversalPrefixReachable reward seed ⊆
      quittingTerminalSemanticCarrier reward := by
  rintro pair ⟨tail, htail, roots, cutoff, rfl⟩
  induction cutoff generalizing roots with
  | zero => exact hseed htail
  | succ cutoff ih =>
      simp only [quittingFinitePrefixSemanticEval]
      exact quittingTerminalSemanticPrefix_mem_carrier reward (roots 0) _
        (ih (fun time => roots (time + 1)))

theorem quittingUniversalPrefixHull_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (hseed : seed ⊆ quittingTerminalSemanticCarrier reward) :
    quittingUniversalPrefixHull reward seed ⊆
      quittingTerminalSemanticCarrier reward := by
  exact closure_minimal
    (quittingUniversalPrefixReachable_subset_carrier reward seed hseed)
    isClosed_closure

private theorem quittingUniversalPrefixReachable_singleton_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingUniversalPrefixReachable reward
        {quittingNeverBoundarySemanticPair reward} =
      quittingNeverGeneratedSemanticReachable reward := by
  ext pair
  constructor
  · rintro ⟨tail, htail, roots, cutoff, heval⟩
    rw [Set.mem_singleton_iff] at htail
    subst tail
    exact ⟨roots, cutoff, heval.symm⟩
  · rintro ⟨roots, cutoff, heval⟩
    exact ⟨quittingNeverBoundarySemanticPair reward, Set.mem_singleton _,
      roots, cutoff, heval.symm⟩

/-- Adding the mandatory Never base to any carrier seed saturates the
universal-prefix hull to the entire executable semantic carrier. -/
theorem quittingUniversalPrefixHull_union_never_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (hseed : seed ⊆ quittingTerminalSemanticCarrier reward) :
    quittingUniversalPrefixHull reward
        (seed ∪ {quittingNeverBoundarySemanticPair reward}) =
      quittingTerminalSemanticCarrier reward := by
  apply Set.Subset.antisymm
  · apply quittingUniversalPrefixHull_subset_carrier reward
    rintro pair (hpair | hpair)
    · exact hseed hpair
    · rw [Set.mem_singleton_iff] at hpair
      subst pair
      rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
      exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  · rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable,
      ← quittingUniversalPrefixReachable_singleton_never]
    apply closure_mono
    rintro pair ⟨tail, htail, roots, cutoff, heval⟩
    exact ⟨tail, Set.mem_union_right seed htail, roots, cutoff, heval⟩

/-- Arbitrary invariant-box form of the hull-infimum theorem. The objective
need only have a lower bound on that box, not on the ambient pair space. -/
theorem exists_minimizer_universalPrefixHull_eq_sInf_wordInf_of_boxLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) (M lower : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hseedBox : seed ⊆ quittingTerminalSemanticBox ι M)
    (hseedNonempty : seed.Nonempty)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι M, lower ≤ objective pair) :
    ∃ minimizer ∈ quittingUniversalPrefixHull reward seed,
      (∀ pair ∈ quittingUniversalPrefixHull reward seed,
        objective minimizer ≤ objective pair) ∧
      objective minimizer = sInf (Set.range fun pair : seed =>
        quittingControllerWordInf reward objective pair.1) := by
  have hwordBox (tail : QuittingTerminalSemanticPair ι)
      (htail : tail ∈ quittingTerminalSemanticBox ι M)
      (roots : List (QuittingRootSimplex ι)) :
      quittingControllerRootListEvalFrom reward roots tail ∈
        quittingTerminalSemanticBox ι M := by
    induction roots with
    | nil => exact htail
    | cons root roots ih =>
        exact quittingTerminalSemanticPrefix_mem_box reward
          (quittingRootOfSimplex root) _ hreward ih
  have hwordBdd (tail : QuittingTerminalSemanticPair ι)
      (htail : tail ∈ quittingTerminalSemanticBox ι M) :
      BddBelow (Set.range fun roots : List (QuittingRootSimplex ι) =>
        objective (quittingControllerRootListEvalFrom reward roots tail)) := by
    refine ⟨lower, ?_⟩
    rintro _ ⟨roots, rfl⟩
    exact hlower _ (hwordBox tail htail roots)
  have hhullNonempty := hseedNonempty.mono
    (subset_quittingUniversalPrefixHull reward seed)
  obtain ⟨minimizer, hminimizer, hminimum⟩ :=
    (isCompact_quittingUniversalPrefixHull reward seed M hreward hseedBox).exists_isMinOn
      hhullNonempty hobjectiveContinuous.continuousOn
  let floor := sInf (Set.range fun pair : seed =>
    quittingControllerWordInf reward objective pair.1)
  have hfloorBdd : BddBelow (Set.range fun pair : seed =>
      quittingControllerWordInf reward objective pair.1) := by
    refine ⟨lower, ?_⟩
    rintro _ ⟨pair, rfl⟩
    unfold quittingControllerWordInf
    exact le_ciInf fun roots => hlower _
      (hwordBox pair.1 (hseedBox pair.2) roots)
  have hfloorNonempty : (Set.range fun pair : seed =>
      quittingControllerWordInf reward objective pair.1).Nonempty := by
    obtain ⟨pair, hpair⟩ := hseedNonempty
    exact ⟨_, ⟨⟨pair, hpair⟩, rfl⟩⟩
  have hminLeFloor : objective minimizer ≤ floor := by
    apply le_csInf hfloorNonempty
    rintro _ ⟨pair, rfl⟩
    unfold quittingControllerWordInf
    apply le_ciInf
    intro roots
    apply hminimum
    induction roots with
    | nil => exact subset_quittingUniversalPrefixHull reward seed pair.2
    | cons root roots ih =>
        exact quittingTerminalSemanticPrefix_mem_universalPrefixHull
          reward seed (quittingRootOfSimplex root) _ ih
  have hfloorLeReachable : ∀ pair ∈ quittingUniversalPrefixReachable reward seed,
      floor ≤ objective pair := by
    rintro pair ⟨tail, htail, roots, cutoff, rfl⟩
    have hfloorLeInf : floor ≤
        quittingControllerWordInf reward objective tail :=
      csInf_le hfloorBdd ⟨⟨tail, htail⟩, rfl⟩
    have htailBox := hseedBox htail
    have hevalBox := quittingUniversalPrefixReachable_subset_box
      reward seed M hreward hseedBox
      ⟨tail, htail, roots, cutoff, rfl⟩
    have hinfLeValue : quittingControllerWordInf reward objective
        (quittingFinitePrefixSemanticEval reward roots cutoff tail) ≤
        objective (quittingFinitePrefixSemanticEval reward roots cutoff tail) := by
      unfold quittingControllerWordInf
      simpa using ciInf_le
        (hwordBdd _ hevalBox) ([] : List (QuittingRootSimplex ι))
    exact hfloorLeInf.trans
      ((quittingControllerWordInf_le_finitePrefix_of_boxLower reward M lower
        hreward objective hlower tail htailBox roots cutoff).trans hinfLeValue)
  have hfloorLeHull : ∀ pair ∈ quittingUniversalPrefixHull reward seed,
      floor ≤ objective pair :=
    closure_minimal hfloorLeReachable
      (isClosed_Ici.preimage hobjectiveContinuous)
  exact ⟨minimizer, hminimizer, hminimum,
    le_antisymm hminLeFloor (hfloorLeHull minimizer hminimizer)⟩


/-- On a nonempty seed, the compact hull attains exactly the infimum of the
finite-word envelope over the seeds. -/
theorem exists_minimizer_universalPrefixHull_eq_sInf_wordInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hseedBox : seed ⊆ quittingTerminalSemanticBox ι M)
    (hseedNonempty : seed.Nonempty)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjectiveNonneg : ∀ pair, 0 ≤ objective pair) :
    ∃ minimizer ∈ quittingUniversalPrefixHull reward seed,
      (∀ pair ∈ quittingUniversalPrefixHull reward seed,
        objective minimizer ≤ objective pair) ∧
      objective minimizer = sInf (Set.range fun pair : seed =>
        quittingControllerWordInf reward objective pair.1) := by
  apply exists_minimizer_universalPrefixHull_eq_sInf_wordInf_of_boxLower
    reward seed M 0 hreward hseedBox hseedNonempty objective
    hobjectiveContinuous
  exact fun pair _ => hobjectiveNonneg pair
/-- Raw-debt specialization on an arbitrary invariant reward box. In
particular, the seeds need not lie in the executable carrier or in the
canonical box determined by `quittingRewardBound`. -/
theorem exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf_of_box
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι)) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hseedBox : seed ⊆ quittingTerminalSemanticBox ι M)
    (hseedNonempty : seed.Nonempty) :
    ∃ minimizer ∈ quittingUniversalPrefixHull reward seed,
      (∀ pair ∈ quittingUniversalPrefixHull reward seed,
        quittingControllerRawMaximumDebt minimizer ≤
          quittingControllerRawMaximumDebt pair) ∧
      quittingControllerRawMaximumDebt minimizer =
        sInf (Set.range fun pair : seed =>
          quittingControllerWordInf reward
            quittingControllerRawMaximumDebt pair.1) := by
  classical
  let who : ι := Classical.choice inferInstance
  let terminal : {S : Finset ι // S.Nonempty} :=
    ⟨{who}, Finset.singleton_nonempty who⟩
  have hM : 0 ≤ M :=
    (abs_nonneg (reward terminal who)).trans (hreward terminal who)
  apply exists_minimizer_universalPrefixHull_eq_sInf_wordInf_of_boxLower
    reward seed M (-2 * M) hreward hseedBox hseedNonempty
    quittingControllerRawMaximumDebt continuous_quittingControllerRawMaximumDebt
  intro pair hpair
  have hbound := abs_quittingControllerRawMaximumDebt_le_of_mem_box hM hpair
  linarith [neg_le_of_abs_le hbound]

/-- Carrier specialization retaining the literal signed raw-debt objective
on both sides; the invariant reward-box bound is derived from membership. -/
theorem exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (hseedCarrier : seed ⊆ quittingTerminalSemanticCarrier reward)
    (hseedNonempty : seed.Nonempty) :
    ∃ minimizer ∈ quittingUniversalPrefixHull reward seed,
      (∀ pair ∈ quittingUniversalPrefixHull reward seed,
        quittingControllerRawMaximumDebt minimizer ≤
          quittingControllerRawMaximumDebt pair) ∧
      quittingControllerRawMaximumDebt minimizer =
        sInf (Set.range fun pair : seed =>
          quittingControllerWordInf reward quittingControllerRawMaximumDebt pair.1) :=
  exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf_of_box
    reward seed (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)
    (fun pair hpair => quittingTerminalSemanticCarrier_mem_box reward pair
      (abs_reward_le_quittingRewardBound reward) (hseedCarrier hpair)) hseedNonempty

theorem quittingControllerTesterFunctionBarrier_eq_wordInf
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingControllerRewardBox reward) :
    quittingControllerTesterFunctionBarrier reward pair =
      quittingControllerWordInf reward quittingControllerRawMaximumDebt pair.1 := by
  unfold quittingControllerTesterFunctionBarrier
    quittingControllerRewardBoxWordInf quittingControllerWordInf
  congr 1
  funext roots
  rw [quittingControllerRewardBoxRootListEvalFrom_coe]

/-- Full ambient-box form of the universal-hull floor formula. Unlike the
carrier specialization, raw maximum debt may be negative here; its reward-box
lower bound replaces any global nonnegativity assumption. -/
theorem exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_boxWordInf
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (hseedBox : seed ⊆ quittingTerminalSemanticBox ι (quittingRewardBound reward))
    (hseedNonempty : seed.Nonempty) :
    ∃ minimizer ∈ quittingUniversalPrefixHull reward seed,
      (∀ pair ∈ quittingUniversalPrefixHull reward seed,
        quittingControllerRawMaximumDebt minimizer ≤
          quittingControllerRawMaximumDebt pair) ∧
      quittingControllerRawMaximumDebt minimizer =
        sInf (Set.range fun pair : seed =>
          quittingControllerTesterFunctionBarrier reward ⟨pair.1, hseedBox pair.2⟩) := by
  obtain ⟨minimizer, hminimizer, hminimum, heq⟩ :=
    exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_wordInf_of_box
      reward seed (quittingRewardBound reward)
      (abs_reward_le_quittingRewardBound reward) hseedBox hseedNonempty
  refine ⟨minimizer, hminimizer, hminimum, ?_⟩
  rw [heq]
  congr 2
  funext pair
  exact (quittingControllerTesterFunctionBarrier_eq_wordInf reward
    ⟨pair.1, hseedBox pair.2⟩).symm
/-- Adding the Never base to carrier seeds makes the ambient-box hull floor
literally the global carrier minimum, while retaining its expression as the
seedwise infimum of the canonical raw-debt barrier. -/
theorem exists_globalMinimum_unionNeverHull_eq_sInf_rawBarrier
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (seed : Set (QuittingTerminalSemanticPair ι))
    (hseed : seed ⊆ quittingTerminalSemanticCarrier reward) :
    ∃ minimum ∈ quittingTerminalSemanticCarrier reward,
      (∀ pair ∈ quittingTerminalSemanticCarrier reward,
        quittingControllerRawMaximumDebt minimum ≤
          quittingControllerRawMaximumDebt pair) ∧
      quittingControllerRawMaximumDebt minimum =
        sInf (Set.range fun pair : {pair //
          pair ∈ seed ∪ {quittingNeverBoundarySemanticPair reward}} =>
          quittingControllerTesterFunctionBarrier reward
            ⟨pair.1, quittingTerminalSemanticCarrier_mem_box reward pair.1
              (abs_reward_le_quittingRewardBound reward)
              (by
                rcases pair.2 with hpair | hpair
                · exact hseed hpair
                · rw [Set.mem_singleton_iff] at hpair
                  rw [hpair]
                  rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
                  exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩)⟩) := by
  let enlarged := seed ∪ {quittingNeverBoundarySemanticPair reward}
  have henlargedCarrier : enlarged ⊆ quittingTerminalSemanticCarrier reward := by
    rintro pair (hpair | hpair)
    · exact hseed hpair
    · rw [Set.mem_singleton_iff] at hpair
      subst pair
      rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
      exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  have henlargedBox : enlarged ⊆ quittingTerminalSemanticBox ι
      (quittingRewardBound reward) := fun pair hpair =>
    quittingTerminalSemanticCarrier_mem_box reward pair
      (abs_reward_le_quittingRewardBound reward) (henlargedCarrier hpair)
  have henlargedNonempty : enlarged.Nonempty :=
    ⟨quittingNeverBoundarySemanticPair reward, Set.mem_union_right seed (Set.mem_singleton _)⟩
  obtain ⟨minimum, hminimumHull, hminimum, heq⟩ :=
    exists_minimizer_rawMaximumDebt_universalPrefixHull_eq_sInf_boxWordInf
      reward enlarged henlargedBox henlargedNonempty
  rw [quittingUniversalPrefixHull_union_never_eq_carrier reward seed hseed]
    at hminimumHull hminimum
  exact ⟨minimum, hminimumHull, hminimum, heq⟩

/-- A displayed finite prefix with zero nonnegative objective forces the
future-prefix envelope at its source to vanish.  This is the reusable core of
the two-sure-clock sentinel regression. -/
theorem quittingControllerWordInf_eq_zero_of_finitePrefix_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (source : QuittingTerminalSemanticPair ι)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (hzero : objective
      (quittingFinitePrefixSemanticEval reward roots cutoff source) = 0) :
    quittingControllerWordInf reward objective source = 0 := by
  apply le_antisymm
  · calc
      quittingControllerWordInf reward objective source ≤
          quittingControllerWordInf reward objective
            (quittingFinitePrefixSemanticEval reward roots cutoff source) :=
        quittingControllerWordInf_le_finitePrefixSemanticEval
          reward objective hobjective roots cutoff source
      _ ≤ objective
          (quittingFinitePrefixSemanticEval reward roots cutoff source) :=
        quittingControllerWordInf_le_word reward objective hobjective _ []
      _ = 0 := hzero
  · exact quittingControllerWordInf_nonneg reward objective hobjective source

/-- The literal raw-debt word envelope is bounded on the invariant reward
box. No global extension away from that box is needed. -/
theorem abs_quittingControllerRawWordInf_le_of_mem_box [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticBox ι (quittingRewardBound reward)) :
    |quittingControllerWordInf reward quittingControllerRawMaximumDebt pair| ≤
      2 * quittingRewardBound reward := by
  rw [← quittingControllerTesterFunctionBarrier_eq_wordInf reward ⟨pair, hpair⟩]
  apply abs_le.mpr
  constructor
  · unfold quittingControllerTesterFunctionBarrier
    simpa only [neg_mul] using
      quittingControllerRewardBoxWordInf_lower reward _ _
        (quittingControllerRawMaximumDebt_box_lower reward) ⟨pair, hpair⟩
  · exact (quittingControllerRewardBoxWordInf_le_word reward _ _
        (quittingControllerRawMaximumDebt_box_lower reward) ⟨pair, hpair⟩ []).trans
      (quittingControllerRawMaximumDebt_box_upper reward pair hpair)

/-- Literal finite-prefix monotonicity of the canonical raw-debt envelope. -/
theorem quittingControllerRawWordInf_le_finitePrefix_of_mem_box [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticBox ι (quittingRewardBound reward))
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ) :
    quittingControllerWordInf reward quittingControllerRawMaximumDebt pair ≤
      quittingControllerWordInf reward quittingControllerRawMaximumDebt
        (quittingFinitePrefixSemanticEval reward roots cutoff pair) :=
  quittingControllerWordInf_le_finitePrefix_of_boxLower reward
    (quittingRewardBound reward) (-2 * quittingRewardBound reward)
    (abs_reward_le_quittingRewardBound reward) quittingControllerRawMaximumDebt
    (fun point hpoint => quittingControllerRawMaximumDebt_box_lower reward point hpoint)
    pair hpair roots cutoff

/-! ## Renewable finite telescopes -/

/-- Lift of a response seam measured by a future-prefix envelope. -/
def quittingRenewableBarrierLift
    (Q : QuittingTerminalSemanticPair ι → ℝ)
    (prefixed next : ℕ → QuittingTerminalSemanticPair ι) (index : ℕ) : ℝ :=
  Q (next (index + 1)) - Q (prefixed index)

omit [Fintype ι] [DecidableEq ι] in
/-- Exact finite renewable ledger.  The correction term is the increase of
the future-prefix envelope along each finite controller word. -/
theorem sum_quittingRenewableBarrierLift_eq
    (Q : QuittingTerminalSemanticPair ι → ℝ)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (horizon : ℕ) :
    (∑ index ∈ Finset.range horizon,
        quittingRenewableBarrierLift Q prefixed source index) =
      Q (source horizon) - Q (source 0) -
        ∑ index ∈ Finset.range horizon,
          (Q (prefixed index) - Q (source index)) := by
  simp_rw [quittingRenewableBarrierLift]
  have hpoint : ∀ index,
      Q (source (index + 1)) - Q (prefixed index) =
        (Q (source (index + 1)) - Q (source index)) -
          (Q (prefixed index) - Q (source index)) := by
    intro index
    ring
  simp_rw [hpoint]
  have htelescope := Finset.sum_range_sub (fun index => Q (source index)) horizon
  rw [Finset.sum_sub_distrib, htelescope]

/-- Every displayed finite prefix moves the canonical word infimum weakly
upward. -/
theorem quittingControllerWordInf_source_le_prefixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (roots : ℕ → ℕ → ι → PMF Bool) (cutoff : ℕ → ℕ)
    (hprefixed : ∀ index, prefixed index =
      quittingFinitePrefixSemanticEval reward (roots index) (cutoff index)
        (source index)) (index : ℕ) :
    quittingControllerWordInf reward objective (source index) ≤
      quittingControllerWordInf reward objective (prefixed index) := by
  rw [hprefixed index]
  exact quittingControllerWordInf_le_finitePrefixSemanticEval
    reward objective hobjective (roots index) (cutoff index) (source index)

omit [Fintype ι] [DecidableEq ι] in
/-- A bounded future-prefix envelope gives a uniform finite upper bound on
the total renewable lift.  No response seam is assumed monotone. -/
theorem sum_quittingRenewableBarrierLift_le_two_mul_bound
    (Q : QuittingTerminalSemanticPair ι → ℝ)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (bound : ℝ) (hsourceBound : ∀ index, |Q (source index)| ≤ bound)
    (hprefix : ∀ index, Q (source index) ≤ Q (prefixed index))
    (horizon : ℕ) :
    (∑ index ∈ Finset.range horizon,
        quittingRenewableBarrierLift Q prefixed source index) ≤
      2 * bound := by
  rw [sum_quittingRenewableBarrierLift_eq Q source prefixed horizon]
  have hpenalty : 0 ≤ ∑ index ∈ Finset.range horizon,
      (Q (prefixed index) - Q (source index)) :=
    Finset.sum_nonneg fun index _ => sub_nonneg.mpr (hprefix index)
  have hupper := le_of_abs_le (hsourceBound horizon)
  have hlower := neg_le_of_abs_le (hsourceBound 0)
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- The Cesaro limsup of renewable lifts is nonpositive.  This is an averaged
statement; individual response lifts can have either sign. -/
theorem limsup_average_quittingRenewableBarrierLift_le_zero
    (Q : QuittingTerminalSemanticPair ι → ℝ)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (bound : ℝ)
    (hsourceBound : ∀ index, |Q (source index)| ≤ bound)
    (hprefixedBound : ∀ index, |Q (prefixed index)| ≤ bound)
    (hprefix : ∀ index, Q (source index) ≤ Q (prefixed index)) :
    Filter.limsup (fun horizon : ℕ =>
      (∑ index ∈ Finset.range horizon,
        quittingRenewableBarrierLift Q prefixed source index) / horizon)
      atTop ≤ 0 := by
  apply le_of_forall_gt
  intro epsilon hepsilon
  have hlimsup : Filter.limsup (fun horizon : ℕ =>
      (∑ index ∈ Finset.range horizon,
        quittingRenewableBarrierLift Q prefixed source index) / horizon)
      atTop ≤ epsilon / 2 := by
    have htendsto : Tendsto (fun horizon : ℕ => 2 * bound / (horizon : ℝ))
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hepsilonHalf : 0 < epsilon / 2 := by linarith
    have heventually : ∀ᶠ horizon : ℕ in atTop,
        (∑ index ∈ Finset.range horizon,
          quittingRenewableBarrierLift Q prefixed source index) / horizon ≤
            epsilon / 2 := by
      filter_upwards [(tendsto_order.1 htendsto).2 _ hepsilonHalf,
          eventually_gt_atTop (0 : ℕ)] with horizon hratio hpositive
      have hsum := sum_quittingRenewableBarrierLift_le_two_mul_bound
        Q source prefixed bound hsourceBound hprefix horizon
      have hcast : 0 < (horizon : ℝ) := by exact_mod_cast hpositive
      exact (div_le_div_of_nonneg_right hsum hcast.le).trans hratio.le
    have hcobounded : Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop
        (fun horizon : ℕ =>
          (∑ index ∈ Finset.range horizon,
            quittingRenewableBarrierLift Q prefixed source index) / horizon) := by
      apply isCoboundedUnder_le_of_le atTop (x := -2 * bound)
      intro horizon
      have hboundNonneg : 0 ≤ bound :=
        (abs_nonneg (Q (source 0))).trans (hsourceBound 0)
      cases horizon with
      | zero => simpa using hboundNonneg
      | succ horizon =>
          have hpositive : 0 < ((horizon + 1 : ℕ) : ℝ) := by positivity
          have hterm : ∀ index,
              -2 * bound ≤ quittingRenewableBarrierLift Q prefixed source index := by
            intro index
            have hnext := neg_le_of_abs_le (hsourceBound (index + 1))
            have hprefixed := le_of_abs_le (hprefixedBound index)
            simp only [quittingRenewableBarrierLift]
            linarith
          have hsum : (horizon + 1 : ℝ) * (-2 * bound) ≤
              ∑ index ∈ Finset.range (horizon + 1),
                quittingRenewableBarrierLift Q prefixed source index := by
            calc
              (horizon + 1 : ℝ) * (-2 * bound) =
                  ∑ _index ∈ Finset.range (horizon + 1), (-2 * bound) := by
                    simp
              _ ≤ _ := Finset.sum_le_sum fun index _ => hterm index
          rw [le_div_iff₀ hpositive]
          simpa [mul_comm, mul_left_comm] using hsum
    exact Filter.limsup_le_of_le (hf := hcobounded) (h := heventually)
  exact hlimsup.trans_lt (by linarith)

/-- Canonical raw-barrier specialization of the renewable ledger. Carrier
membership supplies all reward-box bounds, and literal finite-prefix ancestry
supplies the nonnegative correction term. -/
theorem canonicalRawBarrier_renewableLedger_and_limsup
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (hsource : ∀ index, source index ∈ quittingTerminalSemanticCarrier reward)
    (roots : ℕ → ℕ → ι → PMF Bool) (cutoff : ℕ → ℕ)
    (hprefixEval : ∀ index, prefixed index =
      quittingFinitePrefixSemanticEval reward (roots index) (cutoff index)
        (source index)) :
    (∀ horizon,
      (∑ index ∈ Finset.range horizon,
          quittingRenewableBarrierLift
            (quittingControllerWordInf reward quittingControllerRawMaximumDebt)
              prefixed source index) =
        quittingControllerWordInf reward quittingControllerRawMaximumDebt (source horizon) -
          quittingControllerWordInf reward quittingControllerRawMaximumDebt (source 0) -
          ∑ index ∈ Finset.range horizon,
            (quittingControllerWordInf reward quittingControllerRawMaximumDebt (prefixed index) -
              quittingControllerWordInf reward quittingControllerRawMaximumDebt (source index))) ∧
      Filter.limsup (fun horizon : ℕ =>
        (∑ index ∈ Finset.range horizon,
          quittingRenewableBarrierLift
            (quittingControllerWordInf reward quittingControllerRawMaximumDebt)
              prefixed source index) / horizon)
        atTop ≤ 0 := by
  let boxMem := fun pair : QuittingTerminalSemanticPair ι =>
    pair ∈ quittingTerminalSemanticBox ι (quittingRewardBound reward)
  have hsourceBox : ∀ index, boxMem (source index) := fun index =>
    quittingTerminalSemanticCarrier_mem_box reward (source index)
      (abs_reward_le_quittingRewardBound reward) (hsource index)
  have hprefixedBox : ∀ index, boxMem (prefixed index) := by
    intro index
    rw [hprefixEval index]
    exact quittingFinitePrefixSemanticEval_mem_box reward
      (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward)
      (source index) (hsourceBox index) (roots index) (cutoff index)
  have hmono : ∀ index,
      quittingControllerWordInf reward quittingControllerRawMaximumDebt (source index) ≤
        quittingControllerWordInf reward quittingControllerRawMaximumDebt (prefixed index) := by
    intro index
    rw [hprefixEval index]
    exact quittingControllerRawWordInf_le_finitePrefix_of_mem_box reward
      (source index) (hsourceBox index) (roots index) (cutoff index)
  constructor
  · exact fun horizon => sum_quittingRenewableBarrierLift_eq
      (quittingControllerWordInf reward quittingControllerRawMaximumDebt) source prefixed horizon
  · apply limsup_average_quittingRenewableBarrierLift_le_zero
      (quittingControllerWordInf reward quittingControllerRawMaximumDebt) source prefixed
      (2 * quittingRewardBound reward)
    · intro index
      exact abs_quittingControllerRawWordInf_le_of_mem_box reward _ (hsourceBox index)
    · intro index
      exact abs_quittingControllerRawWordInf_le_of_mem_box reward _ (hprefixedBox index)
    · exact hmono

end GameTheory
