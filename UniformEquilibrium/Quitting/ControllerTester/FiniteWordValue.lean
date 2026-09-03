/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.ControllerValue

/-!
# Finite-word controller minima

Finite words are parameterized by products of Boolean probability simplexes.
Their semantic endpoint is obtained by backward prefix evaluation from the
Never boundary. Compactness gives an attained value at every length. Appending
an all-Continue root changes no endpoint, so the minima decrease. Exact
Never-generated density identifies their limit with the compact semantic
controller value.
-/

noncomputable section

namespace GameTheory

open Filter Math.ProbabilityMassFunction Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Backward semantic evaluation of a fixed-length simplex root word from the
Never boundary. Index zero is the first chronological root. -/
def quittingControllerFiniteWordEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ length : ℕ, (Fin length → QuittingRootSimplex ι) →
      QuittingTerminalSemanticPair ι
  | 0, _ => quittingNeverBoundarySemanticPair reward
  | length + 1, word =>
      quittingTerminalSemanticPrefix reward
        (quittingRootOfSimplex (word 0))
        (quittingControllerFiniteWordEval reward length (Fin.tail word))

omit [Nonempty ι] in
theorem continuous_quittingControllerFiniteWordEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (length : ℕ) :
    Continuous (quittingControllerFiniteWordEval reward length) := by
  induction length with
  | zero =>
      exact continuous_const
  | succ length ih =>
      have hhead : Continuous (fun word : Fin (length + 1) →
          QuittingRootSimplex ι => word 0) :=
        continuous_apply 0
      have htail : Continuous (fun word : Fin (length + 1) →
          QuittingRootSimplex ι => Fin.tail word) :=
        continuous_id.finTail
      change Continuous (fun word : Fin (length + 1) → QuittingRootSimplex ι =>
        quittingTerminalSemanticPrefixSimplex reward
          (word 0, quittingControllerFiniteWordEval reward length (Fin.tail word)))
      exact (continuous_quittingTerminalSemanticPrefixSimplex reward).comp
        (hhead.prodMk (ih.comp htail))

omit [Nonempty ι] in
/-- Simplex evaluation is the existing finite-prefix semantic evaluator
after converting the displayed finite word to literal PMF roots. -/
theorem quittingControllerFiniteWordEval_eq_finitePrefixSemanticEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (length : ℕ) :
    quittingControllerFiniteWordEval reward length
        (fun index => quittingSimplexOfRoot (roots index)) =
      quittingFinitePrefixSemanticEval reward roots length
        (quittingNeverBoundarySemanticPair reward) := by
  induction length generalizing roots with
  | zero => rfl
  | succ length ih =>
      simp only [quittingControllerFiniteWordEval,
        quittingFinitePrefixSemanticEval]
      rw [quittingRootOfSimplex_simplexOfRoot]
      congr 1
      have htail : Fin.tail
          (fun index : Fin (length + 1) => quittingSimplexOfRoot (roots index)) =
          (fun index : Fin length =>
            quittingSimplexOfRoot (roots (index.1 + 1))) := by
        funext index
        rfl
      rw [htail]
      exact ih (fun time => roots (time + 1))

omit [Nonempty ι] in
/-- Every finite-word semantic endpoint belongs to the compact executable
terminal-semantic carrier. -/
theorem quittingControllerFiniteWordEval_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (length : ℕ) (word : Fin length → QuittingRootSimplex ι) :
    quittingControllerFiniteWordEval reward length word ∈
      quittingTerminalSemanticCarrier reward := by
  induction length with
  | zero =>
      rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
      exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  | succ length ih =>
      exact quittingTerminalSemanticPrefix_mem_carrier reward
        (quittingRootOfSimplex (word 0)) _ (ih (Fin.tail word))

/-- Append an all-Continue simplex root at the chronological end of a word. -/
def quittingControllerFiniteWordAppendAllContinue
    {length : ℕ} (word : Fin length → QuittingRootSimplex ι) :
    Fin (length + 1) → QuittingRootSimplex ι :=
  Fin.lastCases (quittingSimplexOfRoot quittingAllContinueRoot) word

omit [Nonempty ι] in
/-- Appending an all-Continue root at the end leaves the finite-word semantic
endpoint unchanged. -/
theorem quittingControllerFiniteWordEval_appendAllContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (length : ℕ) (word : Fin length → QuittingRootSimplex ι) :
    quittingControllerFiniteWordEval reward (length + 1)
        (quittingControllerFiniteWordAppendAllContinue word) =
      quittingControllerFiniteWordEval reward length word := by
  induction length with
  | zero =>
      have hword : quittingControllerFiniteWordAppendAllContinue word =
          (fun _ => quittingSimplexOfRoot quittingAllContinueRoot) := by
        funext index
        exact Fin.eq_zero index ▸ Fin.lastCases_last
      rw [hword, quittingControllerFiniteWordEval]
      change quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex (quittingSimplexOfRoot quittingAllContinueRoot))
          (quittingNeverBoundarySemanticPair reward) = _
      rw [quittingRootOfSimplex_simplexOfRoot]
      apply quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
      intro who
      simp [quittingNeverBoundarySemanticPair]
  | succ length ih =>
      have hhead : quittingControllerFiniteWordAppendAllContinue word 0 = word 0 := by
        change Fin.lastCases _ word (0 : Fin (length + 2)) = word 0
        rw [show (0 : Fin (length + 2)) = (0 : Fin (length + 1)).castSucc by rfl,
          Fin.lastCases_castSucc]
      have htail : Fin.tail (quittingControllerFiniteWordAppendAllContinue word) =
          quittingControllerFiniteWordAppendAllContinue (Fin.tail word) := by
        change Fin.tail (Fin.lastCases
            (motive := fun _ : Fin (length + 2) => QuittingRootSimplex ι)
            (quittingSimplexOfRoot quittingAllContinueRoot) word) =
          Fin.lastCases
            (motive := fun _ : Fin (length + 1) => QuittingRootSimplex ι)
            (quittingSimplexOfRoot quittingAllContinueRoot) (Fin.tail word)
        funext index
        refine Fin.lastCases (motive := fun index =>
          Fin.tail (Fin.lastCases
            (motive := fun _ : Fin (length + 2) => QuittingRootSimplex ι)
            (quittingSimplexOfRoot quittingAllContinueRoot) word) index =
          Fin.lastCases
            (motive := fun _ : Fin (length + 1) => QuittingRootSimplex ι)
            (quittingSimplexOfRoot quittingAllContinueRoot)
            (Fin.tail word) index) ?_ (fun earlier => ?_) index
        · simp [Fin.tail]
        · simp only [Fin.tail, Fin.lastCases_castSucc]
          rw [show Fin.succ (Fin.castSucc earlier) =
              Fin.castSucc (Fin.succ earlier) by
            apply Fin.ext
            rfl]
          rw [Fin.lastCases_castSucc]
      change quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex
            (quittingControllerFiniteWordAppendAllContinue word 0))
          (quittingControllerFiniteWordEval reward (length + 1)
            (Fin.tail (quittingControllerFiniteWordAppendAllContinue word))) =
        quittingTerminalSemanticPrefix reward (quittingRootOfSimplex (word 0))
          (quittingControllerFiniteWordEval reward length (Fin.tail word))
      rw [hhead, htail, ih (Fin.tail word)]

/-- A fixed-target finite-word loss attains its minimum at every length. -/
theorem exists_minimum_quittingControllerFiniteWordTargetLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (length : ℕ) :
    ∃ word : Fin length → QuittingRootSimplex ι,
      ∀ candidate : Fin length → QuittingRootSimplex ι,
        quittingControllerTargetLoss target
            (quittingControllerFiniteWordEval reward length word) ≤
          quittingControllerTargetLoss target
            (quittingControllerFiniteWordEval reward length candidate) := by
  obtain ⟨word, _hword, hminimum⟩ :=
    (isCompact_univ : IsCompact
      (Set.univ : Set (Fin length → QuittingRootSimplex ι))).exists_isMinOn
      Set.univ_nonempty
      ((continuous_quittingControllerTargetLoss target).comp
        (continuous_quittingControllerFiniteWordEval reward length)).continuousOn
  exact ⟨word, fun candidate => hminimum (Set.mem_univ candidate)⟩

/-- Canonical choice of a minimizing root word at a fixed target and length. -/
def quittingControllerFiniteWordTargetMinimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (length : ℕ) :
    Fin length → QuittingRootSimplex ι :=
  Classical.choose <|
    exists_minimum_quittingControllerFiniteWordTargetLoss reward target length

/-- The attained fixed-target controller value at a finite word length. -/
def quittingControllerFiniteWordTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (length : ℕ) : ℝ :=
  quittingControllerTargetLoss target <|
    quittingControllerFiniteWordEval reward length <|
      quittingControllerFiniteWordTargetMinimizer reward target length

theorem quittingControllerFiniteWordTargetValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (length : ℕ)
    (word : Fin length → QuittingRootSimplex ι) :
    quittingControllerFiniteWordTargetValue reward target length ≤
      quittingControllerTargetLoss target
        (quittingControllerFiniteWordEval reward length word) :=
  Classical.choose_spec
    (exists_minimum_quittingControllerFiniteWordTargetLoss reward target length)
      word

/-- Finite-word target values decrease with the allowed word length. -/
theorem antitone_quittingControllerFiniteWordTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    Antitone (quittingControllerFiniteWordTargetValue reward target) := by
  apply antitone_nat_of_succ_le
  intro length
  let word := quittingControllerFiniteWordTargetMinimizer reward target length
  calc
    quittingControllerFiniteWordTargetValue reward target (length + 1) ≤
        quittingControllerTargetLoss target
          (quittingControllerFiniteWordEval reward (length + 1)
            (quittingControllerFiniteWordAppendAllContinue word)) :=
      quittingControllerFiniteWordTargetValue_le reward target _ _
    _ = quittingControllerFiniteWordTargetValue reward target length := by
      rw [quittingControllerFiniteWordEval_appendAllContinue]
      rfl

/-- Every compact target value lower-bounds the corresponding finite-word
controller value. -/
theorem quittingControllerTargetValue_le_finiteWordTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (length : ℕ) :
    quittingControllerTargetValue reward target ≤
      quittingControllerFiniteWordTargetValue reward target length := by
  unfold quittingControllerFiniteWordTargetValue
  exact quittingControllerTargetMinimizer_isMinimum reward target
    (quittingControllerFiniteWordEval_mem_carrier reward _ _)

/-- The decreasing fixed-length controller minima converge to the exact
compact fixed-target controller value. -/
theorem tendsto_quittingControllerFiniteWordTargetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    Tendsto (quittingControllerFiniteWordTargetValue reward target)
      atTop (nhds (quittingControllerTargetValue reward target)) := by
  apply tendsto_order.2
  constructor
  · intro lower hlower
    exact Filter.Eventually.of_forall fun length =>
      hlower.trans_le
        (quittingControllerTargetValue_le_finiteWordTargetValue
          reward target length)
  · intro upper hupper
    let minimizer := quittingControllerTargetMinimizer reward target
    have hminimizer : minimizer ∈ quittingTerminalSemanticCarrier reward :=
      quittingControllerTargetMinimizer_mem reward target
    rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
      at hminimizer
    obtain ⟨pairs, hpairs, hpairsLimit⟩ :=
      mem_closure_iff_seq_limit.mp hminimizer
    have hloss : Tendsto
        (fun index => quittingControllerTargetLoss target (pairs index))
        atTop (nhds (quittingControllerTargetValue reward target)) := by
      exact ((continuous_quittingControllerTargetLoss target).tendsto
        minimizer).comp hpairsLimit
    have heventually : ∀ᶠ index in atTop,
        quittingControllerTargetLoss target (pairs index) < upper :=
      hloss.eventually (Iio_mem_nhds hupper)
    obtain ⟨index, hindex⟩ := heventually.exists
    obtain ⟨roots, cutoff, hpairsEq⟩ := hpairs index
    let word : Fin cutoff → QuittingRootSimplex ι :=
      fun time => quittingSimplexOfRoot (roots time)
    have heval : quittingControllerFiniteWordEval reward cutoff word =
        pairs index := by
      rw [quittingControllerFiniteWordEval_eq_finitePrefixSemanticEval]
      exact hpairsEq.symm
    have hcutoff : quittingControllerFiniteWordTargetValue reward target cutoff <
        upper :=
      (quittingControllerFiniteWordTargetValue_le reward target cutoff word).trans_lt
        (by simpa only [heval] using hindex)
    apply eventually_atTop.2
    refine ⟨cutoff, fun length hlength => ?_⟩
    exact (antitone_quittingControllerFiniteWordTargetValue reward target
      hlength).trans_lt hcutoff

/-- A target-free finite-word loss attains its minimum at every length. -/
theorem exists_minimum_quittingControllerFiniteWordLoss
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (length : ℕ) :
    ∃ word : Fin length → QuittingRootSimplex ι,
      ∀ candidate : Fin length → QuittingRootSimplex ι,
        quittingControllerRawMaximumDebt
            (quittingControllerFiniteWordEval reward length word) ≤
          quittingControllerRawMaximumDebt
            (quittingControllerFiniteWordEval reward length candidate) := by
  obtain ⟨word, _hword, hminimum⟩ :=
    (isCompact_univ : IsCompact
      (Set.univ : Set (Fin length → QuittingRootSimplex ι))).exists_isMinOn
      Set.univ_nonempty
      (continuous_quittingControllerRawMaximumDebt.comp
        (continuous_quittingControllerFiniteWordEval reward length)).continuousOn
  exact ⟨word, fun candidate => hminimum (Set.mem_univ candidate)⟩

/-- Canonical target-free minimizing word at a fixed length. -/
def quittingControllerFiniteWordMinimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (length : ℕ) :
    Fin length → QuittingRootSimplex ι :=
  Classical.choose (exists_minimum_quittingControllerFiniteWordLoss reward length)

/-- The attained target-free controller value at a finite word length. -/
def quittingControllerFiniteWordValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (length : ℕ) : ℝ :=
  quittingControllerRawMaximumDebt <|
    quittingControllerFiniteWordEval reward length <|
      quittingControllerFiniteWordMinimizer reward length

private theorem quittingControllerFiniteWordValue_isMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (length : ℕ) :
    ∃ word : Fin length → QuittingRootSimplex ι,
      quittingControllerFiniteWordValue reward length =
          quittingControllerRawMaximumDebt
            (quittingControllerFiniteWordEval reward length word) ∧
        ∀ candidate : Fin length → QuittingRootSimplex ι,
          quittingControllerFiniteWordValue reward length ≤
            quittingControllerRawMaximumDebt
              (quittingControllerFiniteWordEval reward length candidate) := by
  let word := quittingControllerFiniteWordMinimizer reward length
  refine ⟨word, ?_, fun candidate => ?_⟩
  · rfl
  · exact Classical.choose_spec
      (exists_minimum_quittingControllerFiniteWordLoss reward length) candidate

/-- Target-free finite-word controller values decrease with the allowed word
length. -/
theorem antitone_quittingControllerFiniteWordValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Antitone (quittingControllerFiniteWordValue reward) := by
  apply antitone_nat_of_succ_le
  intro length
  let word := quittingControllerFiniteWordMinimizer reward length
  have hminimum :=
    (quittingControllerFiniteWordValue_isMinimum reward (length + 1)).choose_spec.2
  calc
    quittingControllerFiniteWordValue reward (length + 1) ≤
        quittingControllerRawMaximumDebt
          (quittingControllerFiniteWordEval reward (length + 1)
            (quittingControllerFiniteWordAppendAllContinue word)) :=
      hminimum (quittingControllerFiniteWordAppendAllContinue word)
    _ = quittingControllerFiniteWordValue reward length := by
      rw [quittingControllerFiniteWordEval_appendAllContinue]
      rfl

/-- The finite target-free minima converge to `eta(r)`. -/
theorem tendsto_quittingControllerFiniteWordValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (quittingControllerFiniteWordValue reward)
      atTop (nhds (quittingControllerTesterValue reward)) := by
  let target := (quittingControllerTesterMinimizer reward).1
  have hlower : ∀ length, quittingControllerTesterValue reward ≤
      quittingControllerFiniteWordValue reward length := by
    intro length
    obtain ⟨word, hvalue, _hminimum⟩ :=
      quittingControllerFiniteWordValue_isMinimum reward length
    rw [hvalue]
    exact (quittingControllerTesterValue_eq_minimum_rawMaximumDebt reward).2.2 _
      (quittingControllerFiniteWordEval_mem_carrier reward length word)
  have hupper : ∀ length, quittingControllerFiniteWordValue reward length ≤
      quittingControllerFiniteWordTargetValue reward target length := by
    intro length
    obtain ⟨_word, _hvalue, hminimum⟩ :=
      quittingControllerFiniteWordValue_isMinimum reward length
    let targetWord :=
      quittingControllerFiniteWordTargetMinimizer reward target length
    exact (hminimum targetWord).trans (le_max_right _ _)
  have htarget := tendsto_quittingControllerFiniteWordTargetValue reward target
  rw [quittingControllerTargetValue_at_minimizer_eq_targetFree] at htarget
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds htarget hlower hupper

end GameTheory
