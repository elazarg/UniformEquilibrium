/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.FiniteWordValue

/-!
# Upper-semicontinuous controller barrier duality

Finite root words act on an arbitrary terminal semantic tail. Taking the
infimum of a continuous nonnegative objective over all such words gives its
canonical upper-semicontinuous Bellman barrier. A second box-local construction
handles raw maximum debt, which can be negative off the executable carrier but
is uniformly bounded on the invariant reward box. This module proves exact
Bellman equations and greatest-barrier properties for both constructions.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Backward action of a finite list of simplex roots on an arbitrary tail
semantic pair.  The head of the list is the first chronological root. -/
def quittingControllerRootListEvalFrom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (QuittingRootSimplex ι) → QuittingTerminalSemanticPair ι →
      QuittingTerminalSemanticPair ι
  | [], tail => tail
  | root :: roots, tail =>
      quittingTerminalSemanticPrefix reward (quittingRootOfSimplex root)
        (quittingControllerRootListEvalFrom reward roots tail)

@[simp] theorem quittingControllerRootListEvalFrom_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : QuittingTerminalSemanticPair ι) :
    quittingControllerRootListEvalFrom reward [] tail = tail := rfl

@[simp] theorem quittingControllerRootListEvalFrom_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : QuittingRootSimplex ι) (roots : List (QuittingRootSimplex ι))
    (tail : QuittingTerminalSemanticPair ι) :
    quittingControllerRootListEvalFrom reward (root :: roots) tail =
      quittingTerminalSemanticPrefix reward (quittingRootOfSimplex root)
        (quittingControllerRootListEvalFrom reward roots tail) := rfl

/-- Appending a last chronological root is the same as first applying that
root to the supplied tail. -/
theorem quittingControllerRootListEvalFrom_append
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : List (QuittingRootSimplex ι))
    (tail : QuittingTerminalSemanticPair ι) :
    quittingControllerRootListEvalFrom reward (first ++ second) tail =
      quittingControllerRootListEvalFrom reward first
        (quittingControllerRootListEvalFrom reward second tail) := by
  induction first with
  | nil => rfl
  | cons root first ih =>
      simp only [List.cons_append, quittingControllerRootListEvalFrom_cons, ih]

/-- Every fixed root list acts continuously on its terminal semantic tail. -/
theorem continuous_quittingControllerRootListEvalFrom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (QuittingRootSimplex ι)) :
    Continuous (quittingControllerRootListEvalFrom reward roots) := by
  induction roots with
  | nil => exact continuous_id
  | cons root roots ih =>
      exact (continuous_quittingTerminalSemanticPrefix reward
        (quittingRootOfSimplex root)).comp ih

/-- Every semantic prefix preserves a common coordinate box whenever that
box bounds both the absorbing rewards and the supplied semantic tail. -/
theorem quittingTerminalSemanticPrefix_mem_box
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticBox ι M) :
    quittingTerminalSemanticPrefix reward root pair ∈
      quittingTerminalSemanticBox ι M := by
  have hprescribed (who : ι) :
      |quittingRootSuccessorPayoff reward pair.1 root who| ≤ M :=
    abs_quittingRootExpectedPayoff_le_bound reward pair.1 root who hreward
      (fun player => abs_le.mpr ⟨hpair.1.1 player, hpair.1.2 player⟩)
  have hquit (who : ι) :
      |quittingRootQuitPayoff reward pair.1 root who| ≤ M := by
    exact abs_quittingRootExpectedPayoff_le_bound reward pair.1
      (Function.update root who (PMF.pure true)) who hreward
      (fun player => abs_le.mpr ⟨hpair.1.1 player, hpair.1.2 player⟩)
  have hupdated (who player : ι) :
      |Function.update pair.1 who (pair.2 who) player| ≤ M := by
    by_cases hplayer : player = who
    · subst player
      simpa using abs_le.mpr ⟨hpair.2.1 who, hpair.2.2 who⟩
    · simpa [Function.update_of_ne hplayer] using
        abs_le.mpr ⟨hpair.1.1 player, hpair.1.2 player⟩
  have hcontinue (who : ι) :
      |quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who| ≤ M := by
    exact abs_quittingRootExpectedPayoff_le_bound reward
      (Function.update pair.1 who (pair.2 who))
      (Function.update root who (PMF.pure false)) who hreward (hupdated who)
  constructor <;> constructor
  · exact fun who => neg_le_of_abs_le (hprescribed who)
  · exact fun who => le_of_abs_le (hprescribed who)
  · intro who
    exact (neg_le_of_abs_le (hquit who)).trans (le_max_left _ _)
  · intro who
    exact max_le (le_of_abs_le (hquit who)) (le_of_abs_le (hcontinue who))

/-- Infimum of a semantic objective over all finite root words from a tail. -/
def quittingControllerWordInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (tail : QuittingTerminalSemanticPair ι) : ℝ :=
  ⨅ roots : List (QuittingRootSimplex ι),
    objective (quittingControllerRootListEvalFrom reward roots tail)

private theorem bddBelow_range_wordObjective
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι) :
    BddBelow (Set.range fun roots : List (QuittingRootSimplex ι) =>
      objective (quittingControllerRootListEvalFrom reward roots tail)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨roots, rfl⟩
  exact hobjective _

/-- The word infimum is no larger than any displayed word value. -/
theorem quittingControllerWordInf_le_word
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι)
    (roots : List (QuittingRootSimplex ι)) :
    quittingControllerWordInf reward objective tail ≤
      objective (quittingControllerRootListEvalFrom reward roots tail) := by
  unfold quittingControllerWordInf
  exact ciInf_le (bddBelow_range_wordObjective reward objective hobjective tail) roots

/-- The word infimum is nonnegative when the objective is nonnegative. -/
theorem quittingControllerWordInf_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι) :
    0 ≤ quittingControllerWordInf reward objective tail := by
  unfold quittingControllerWordInf
  exact le_ciInf fun roots => hobjective _

/-- The word infimum is upper semicontinuous: it is a pointwise infimum of
continuous finite-word objective functions. -/
theorem upperSemicontinuous_quittingControllerWordInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjective : ∀ pair, 0 ≤ objective pair) :
    UpperSemicontinuous (quittingControllerWordInf reward objective) := by
  unfold quittingControllerWordInf
  apply upperSemicontinuous_ciInf
  · exact fun tail => bddBelow_range_wordObjective
      reward objective hobjective tail
  · intro roots
    exact (hobjectiveContinuous.comp
      (continuous_quittingControllerRootListEvalFrom reward roots)).upperSemicontinuous

/-- Adding one root at the terminal end restricts the word infimum, so the
canonical barrier is monotone under every semantic prefix. -/
theorem quittingControllerWordInf_le_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι) (root : QuittingRootSimplex ι) :
    quittingControllerWordInf reward objective tail ≤
      quittingControllerWordInf reward objective
        (quittingTerminalSemanticPrefix reward (quittingRootOfSimplex root) tail) := by
  unfold quittingControllerWordInf
  apply le_ciInf
  intro roots
  have hword := ciInf_le
    (bddBelow_range_wordObjective reward objective hobjective tail)
    (roots ++ [root])
  rw [quittingControllerRootListEvalFrom_append] at hword
  simpa using hword

/-- Exact Bellman equation for the canonical word-infimum barrier. -/
theorem quittingControllerWordInf_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι) :
    quittingControllerWordInf reward objective tail =
      min (objective tail)
        (⨅ root : QuittingRootSimplex ι,
          quittingControllerWordInf reward objective
            (quittingTerminalSemanticPrefix reward
              (quittingRootOfSimplex root) tail)) := by
  apply le_antisymm
  · apply le_min
    · simpa using quittingControllerWordInf_le_word reward objective
        hobjective tail []
    · exact le_ciInf fun root =>
        quittingControllerWordInf_le_prefix reward objective hobjective tail root
  · unfold quittingControllerWordInf
    apply le_ciInf
    intro roots
    cases roots using List.reverseRecOn with
    | nil => simp
    | append_singleton first root =>
        calc
          min (objective tail)
              (⨅ candidate : QuittingRootSimplex ι,
                quittingControllerWordInf reward objective
                  (quittingTerminalSemanticPrefix reward
                    (quittingRootOfSimplex candidate) tail)) ≤
              ⨅ candidate : QuittingRootSimplex ι,
                quittingControllerWordInf reward objective
                  (quittingTerminalSemanticPrefix reward
                    (quittingRootOfSimplex candidate) tail) := min_le_right _ _
          _ ≤ quittingControllerWordInf reward objective
                (quittingTerminalSemanticPrefix reward
                  (quittingRootOfSimplex root) tail) := by
              apply ciInf_le
              refine ⟨0, ?_⟩
              rintro _ ⟨candidate, rfl⟩
              exact quittingControllerWordInf_nonneg reward objective
                hobjective _
          _ ≤ objective
                (quittingControllerRootListEvalFrom reward first
                  (quittingTerminalSemanticPrefix reward
                    (quittingRootOfSimplex root) tail)) :=
              quittingControllerWordInf_le_word reward objective hobjective _ first
          _ = objective
                (quittingControllerRootListEvalFrom reward
                  (first ++ [root]) tail) := by
              rw [quittingControllerRootListEvalFrom_append]
              rfl

/-- The compact reward box on which the bounded function-barrier duality is
stated.  Defining competitors on this subtype does not require arbitrary
extensions to the unbounded ambient payoff-pair space. -/
abbrev QuittingControllerRewardBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {pair : QuittingTerminalSemanticPair ι //
    pair ∈ quittingTerminalSemanticBox ι (quittingRewardBound reward)}

/-- The all-Continue Never boundary as a point of the compact reward box. -/
def quittingControllerNeverRewardBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingControllerRewardBox reward :=
  ⟨quittingNeverBoundarySemanticPair reward,
    quittingTerminalSemanticCarrier_mem_box reward _
      (abs_reward_le_quittingRewardBound reward) (by
        rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
        exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩)⟩

/-- Every root prefix is a self-map of the compact reward box. -/
def quittingControllerRewardBoxPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : QuittingRootSimplex ι)
    (pair : QuittingControllerRewardBox reward) :
    QuittingControllerRewardBox reward :=
  ⟨quittingTerminalSemanticPrefix reward (quittingRootOfSimplex root) pair.1,
    quittingTerminalSemanticPrefix_mem_box reward _ pair.1
      (abs_reward_le_quittingRewardBound reward) pair.2⟩

/-- Bellman obstacle operator on real functions over the compact reward box. -/
def quittingControllerRewardBoxBellmanOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (value : QuittingControllerRewardBox reward → ℝ)
    (pair : QuittingControllerRewardBox reward) : ℝ :=
  min (objective pair.1)
    (⨅ root : QuittingRootSimplex ι,
      value (quittingControllerRewardBoxPrefix reward root pair))

/-- Backward evaluation of a finite root word inside the compact reward box. -/
def quittingControllerRewardBoxRootListEvalFrom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (QuittingRootSimplex ι) → QuittingControllerRewardBox reward →
      QuittingControllerRewardBox reward
  | [], tail => tail
  | root :: roots, tail =>
      quittingControllerRewardBoxPrefix reward root
        (quittingControllerRewardBoxRootListEvalFrom reward roots tail)

@[simp] theorem quittingControllerRewardBoxRootListEvalFrom_coe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (QuittingRootSimplex ι))
    (tail : QuittingControllerRewardBox reward) :
    (quittingControllerRewardBoxRootListEvalFrom reward roots tail).1 =
      quittingControllerRootListEvalFrom reward roots tail.1 := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      simp only [quittingControllerRewardBoxRootListEvalFrom,
        quittingControllerRootListEvalFrom,
        quittingControllerRewardBoxPrefix, ih]

/-- Every fixed root acts continuously on the compact reward box. -/
theorem continuous_quittingControllerRewardBoxPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : QuittingRootSimplex ι) :
    Continuous (quittingControllerRewardBoxPrefix reward root) := by
  apply Continuous.subtype_mk
  exact (continuous_quittingTerminalSemanticPrefix reward
    (quittingRootOfSimplex root)).comp continuous_subtype_val

/-- Every fixed root list acts continuously inside the compact reward box. -/
theorem continuous_quittingControllerRewardBoxRootListEvalFrom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (QuittingRootSimplex ι)) :
    Continuous (quittingControllerRewardBoxRootListEvalFrom reward roots) := by
  induction roots with
  | nil => exact continuous_id
  | cons root roots ih =>
      exact (continuous_quittingControllerRewardBoxPrefix reward root).comp ih

/-- Appending a terminal root to a reward-box word first applies that root to
the supplied tail. -/
theorem quittingControllerRewardBoxRootListEvalFrom_append_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (QuittingRootSimplex ι)) (root : QuittingRootSimplex ι)
    (tail : QuittingControllerRewardBox reward) :
    quittingControllerRewardBoxRootListEvalFrom reward (roots ++ [root]) tail =
      quittingControllerRewardBoxRootListEvalFrom reward roots
        (quittingControllerRewardBoxPrefix reward root tail) := by
  apply Subtype.ext
  simp only [quittingControllerRewardBoxRootListEvalFrom_coe,
    quittingControllerRootListEvalFrom_append,
    quittingControllerRewardBoxPrefix]
  rfl

/-- Infimum of an objective over reward-box finite words. This box-local
definition permits objectives which are not bounded below on the ambient
semantic-pair space. -/
def quittingControllerRewardBoxWordInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (tail : QuittingControllerRewardBox reward) : ℝ :=
  ⨅ roots : List (QuittingRootSimplex ι),
    objective (quittingControllerRewardBoxRootListEvalFrom reward roots tail).1

private theorem bddBelow_range_rewardBoxWordObjective
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) (lower : ℝ)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι
      (quittingRewardBound reward), lower ≤ objective pair)
    (tail : QuittingControllerRewardBox reward) :
    BddBelow (Set.range fun roots : List (QuittingRootSimplex ι) =>
      objective
        (quittingControllerRewardBoxRootListEvalFrom reward roots tail).1) := by
  refine ⟨lower, ?_⟩
  rintro _ ⟨roots, rfl⟩
  exact hlower _
    (quittingControllerRewardBoxRootListEvalFrom reward roots tail).2

/-- The reward-box word infimum is at most every displayed word value. -/
theorem quittingControllerRewardBoxWordInf_le_word
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) (lower : ℝ)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι
      (quittingRewardBound reward), lower ≤ objective pair)
    (tail : QuittingControllerRewardBox reward)
    (roots : List (QuittingRootSimplex ι)) :
    quittingControllerRewardBoxWordInf reward objective tail ≤
      objective
        (quittingControllerRewardBoxRootListEvalFrom reward roots tail).1 := by
  unfold quittingControllerRewardBoxWordInf
  exact ciInf_le
    (bddBelow_range_rewardBoxWordObjective reward objective lower hlower tail)
    roots

/-- A box-local lower bound passes to the reward-box word infimum. -/
theorem quittingControllerRewardBoxWordInf_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) (lower : ℝ)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι
      (quittingRewardBound reward), lower ≤ objective pair)
    (tail : QuittingControllerRewardBox reward) :
    lower ≤ quittingControllerRewardBoxWordInf reward objective tail := by
  unfold quittingControllerRewardBoxWordInf
  exact le_ciInf fun roots => hlower _
    (quittingControllerRewardBoxRootListEvalFrom reward roots tail).2

/-- The box-local word infimum is upper semicontinuous. -/
theorem upperSemicontinuous_quittingControllerRewardBoxWordInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) (lower : ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι
      (quittingRewardBound reward), lower ≤ objective pair) :
    UpperSemicontinuous
      (quittingControllerRewardBoxWordInf reward objective) := by
  unfold quittingControllerRewardBoxWordInf
  apply upperSemicontinuous_ciInf
  · exact fun tail => bddBelow_range_rewardBoxWordObjective
      reward objective lower hlower tail
  · intro roots
    exact ((hobjectiveContinuous.comp continuous_subtype_val).comp
      (continuous_quittingControllerRewardBoxRootListEvalFrom reward roots)
      ).upperSemicontinuous

/-- Adding one terminal root restricts the box-local word infimum. -/
theorem quittingControllerRewardBoxWordInf_le_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) (lower : ℝ)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι
      (quittingRewardBound reward), lower ≤ objective pair)
    (tail : QuittingControllerRewardBox reward) (root : QuittingRootSimplex ι) :
    quittingControllerRewardBoxWordInf reward objective tail ≤
      quittingControllerRewardBoxWordInf reward objective
        (quittingControllerRewardBoxPrefix reward root tail) := by
  unfold quittingControllerRewardBoxWordInf
  apply le_ciInf
  intro roots
  have hword := ciInf_le
    (bddBelow_range_rewardBoxWordObjective reward objective lower hlower tail)
    (roots ++ [root])
  rw [quittingControllerRewardBoxRootListEvalFrom_append_singleton] at hword
  exact hword

/-- Exact Bellman equation for the box-local word infimum. -/
theorem quittingControllerRewardBoxWordInf_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) (lower : ℝ)
    (hlower : ∀ pair ∈ quittingTerminalSemanticBox ι
      (quittingRewardBound reward), lower ≤ objective pair)
    (tail : QuittingControllerRewardBox reward) :
    quittingControllerRewardBoxWordInf reward objective tail =
      min (objective tail.1)
        (⨅ root : QuittingRootSimplex ι,
          quittingControllerRewardBoxWordInf reward objective
            (quittingControllerRewardBoxPrefix reward root tail)) := by
  apply le_antisymm
  · apply le_min
    · simpa using quittingControllerRewardBoxWordInf_le_word reward
        objective lower hlower tail []
    · exact le_ciInf fun root =>
        quittingControllerRewardBoxWordInf_le_prefix reward objective lower
          hlower tail root
  · unfold quittingControllerRewardBoxWordInf
    apply le_ciInf
    intro roots
    cases roots using List.reverseRecOn with
    | nil => simp
    | append_singleton first root =>
        calc
          min (objective tail.1) (⨅ candidate : QuittingRootSimplex ι,
              quittingControllerRewardBoxWordInf reward objective
                (quittingControllerRewardBoxPrefix reward candidate tail)) ≤
              ⨅ candidate : QuittingRootSimplex ι,
                quittingControllerRewardBoxWordInf reward objective
                  (quittingControllerRewardBoxPrefix reward candidate tail) :=
            min_le_right _ _
          _ ≤ quittingControllerRewardBoxWordInf reward objective
                (quittingControllerRewardBoxPrefix reward root tail) := by
              apply ciInf_le
              refine ⟨lower, ?_⟩
              rintro _ ⟨candidate, rfl⟩
              exact quittingControllerRewardBoxWordInf_lower reward objective
                lower hlower _
          _ ≤ objective
                (quittingControllerRewardBoxRootListEvalFrom reward first
                  (quittingControllerRewardBoxPrefix reward root tail)).1 :=
              quittingControllerRewardBoxWordInf_le_word reward objective lower
                hlower _ first
          _ = objective
                (quittingControllerRewardBoxRootListEvalFrom reward
                  (first ++ [root]) tail).1 := by
              rw [quittingControllerRewardBoxRootListEvalFrom_append_singleton]

/-- A bounded upper-semicontinuous Bellman subbarrier defined literally on
the compact invariant reward box. -/
structure QuittingControllerUpperSemicontinuousBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ) where
  value : QuittingControllerRewardBox reward → ℝ
  upperSemicontinuous : UpperSemicontinuous value
  bounded : ∃ bound : ℝ, ∀ pair, |value pair| ≤ bound
  le_objective : ∀ pair, value pair ≤ objective pair.1
  le_prefix : ∀ pair (root : QuittingRootSimplex ι),
    value pair ≤ value (quittingControllerRewardBoxPrefix reward root pair)

/-- The two elementary barrier inequalities are exactly the post-fixed-point
inequality for the reward-box Bellman operator. -/
theorem QuittingControllerUpperSemicontinuousBarrier.le_bellmanOperator
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {objective : QuittingTerminalSemanticPair ι → ℝ}
    (barrier : QuittingControllerUpperSemicontinuousBarrier reward objective)
    (pair : QuittingControllerRewardBox reward) :
    barrier.value pair ≤
      quittingControllerRewardBoxBellmanOperator reward objective
        barrier.value pair := by
  apply le_min (barrier.le_objective pair)
  exact le_ciInf fun root => barrier.le_prefix pair root

/-- Iterating prefix monotonicity moves every feasible barrier value forward
along an arbitrary finite root word in the reward box. -/
theorem QuittingControllerUpperSemicontinuousBarrier.le_evalFrom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {objective : QuittingTerminalSemanticPair ι → ℝ}
    (barrier : QuittingControllerUpperSemicontinuousBarrier reward objective)
    (tail : QuittingControllerRewardBox reward)
    (roots : List (QuittingRootSimplex ι)) :
    barrier.value tail ≤ barrier.value
      (quittingControllerRewardBoxRootListEvalFrom reward roots tail) := by
  induction roots with
  | nil => exact le_rfl
  | cons root roots ih =>
      exact ih.trans (barrier.le_prefix
        (quittingControllerRewardBoxRootListEvalFrom reward roots tail) root)

/-- Iterating prefix monotonicity and then using the obstacle bounds every
feasible barrier by every finite-word objective value. -/
theorem QuittingControllerUpperSemicontinuousBarrier.le_word
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {objective : QuittingTerminalSemanticPair ι → ℝ}
    (barrier : QuittingControllerUpperSemicontinuousBarrier reward objective)
    (tail : QuittingControllerRewardBox reward)
    (roots : List (QuittingRootSimplex ι)) :
    barrier.value tail ≤
      objective (quittingControllerRootListEvalFrom reward roots tail.1) := by
  simpa using
    (barrier.le_evalFrom tail roots).trans (barrier.le_objective _)

/-- Every feasible reward-box barrier is pointwise bounded by the box-local
word infimum, without requiring an ambient lower bound on the objective. -/
theorem QuittingControllerUpperSemicontinuousBarrier.le_rewardBoxWordInf
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {objective : QuittingTerminalSemanticPair ι → ℝ}
    (barrier : QuittingControllerUpperSemicontinuousBarrier reward objective)
    (tail : QuittingControllerRewardBox reward) :
    barrier.value tail ≤
      quittingControllerRewardBoxWordInf reward objective tail := by
  unfold quittingControllerRewardBoxWordInf
  apply le_ciInf
  intro roots
  simpa only [quittingControllerRewardBoxRootListEvalFrom_coe] using
    barrier.le_word tail roots

/-- Every feasible reward-box barrier is pointwise bounded by the word
infimum restricted to that box. -/
theorem QuittingControllerUpperSemicontinuousBarrier.le_wordInf
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {objective : QuittingTerminalSemanticPair ι → ℝ}
    (barrier : QuittingControllerUpperSemicontinuousBarrier reward objective)
    (tail : QuittingControllerRewardBox reward) :
    barrier.value tail ≤
      quittingControllerWordInf reward objective tail.1 := by
  unfold quittingControllerWordInf
  exact le_ciInf fun roots => barrier.le_word tail roots

/-- The word infimum restricted to the reward box is itself a bounded
upper-semicontinuous Bellman barrier. -/
def quittingControllerCanonicalFunctionBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjective : ∀ pair, 0 ≤ objective pair) :
    QuittingControllerUpperSemicontinuousBarrier reward objective where
  value := fun pair => quittingControllerWordInf reward objective pair.1
  upperSemicontinuous :=
    (upperSemicontinuous_quittingControllerWordInf reward objective
      hobjectiveContinuous hobjective).comp continuous_subtype_val
  bounded := by
    obtain ⟨bound, hbound⟩ :=
      (quittingTerminalSemanticBox_isCompact
        (ι := ι) (quittingRewardBound reward)).bddAbove_image
          hobjectiveContinuous.continuousOn
    refine ⟨bound, fun pair => ?_⟩
    rw [abs_of_nonneg
      (quittingControllerWordInf_nonneg reward objective hobjective pair.1)]
    exact (quittingControllerWordInf_le_word reward objective
      hobjective pair.1 []).trans (hbound ⟨pair.1, pair.2, rfl⟩)
  le_objective := fun pair => by
    simpa using quittingControllerWordInf_le_word reward objective
      hobjective pair.1 []
  le_prefix := fun pair root =>
    quittingControllerWordInf_le_prefix reward objective hobjective pair.1 root

/-- The canonical reward-box word infimum is a fixed point of the Bellman
obstacle operator. -/
theorem quittingControllerCanonicalFunctionBarrier_fixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjective : ∀ pair, 0 ≤ objective pair) :
    quittingControllerRewardBoxBellmanOperator reward objective
        (quittingControllerCanonicalFunctionBarrier reward objective
          hobjectiveContinuous hobjective).value =
      (quittingControllerCanonicalFunctionBarrier reward objective
        hobjectiveContinuous hobjective).value := by
  funext pair
  exact (quittingControllerWordInf_bellman reward objective
    hobjective pair.1).symm

/-- On the compact reward box, the canonical word infimum is the pointwise
greatest bounded upper-semicontinuous Bellman subbarrier. -/
theorem quittingControllerWordInf_isGreatest_upperSemicontinuousBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjective : ∀ pair, 0 ≤ objective pair) :
    (quittingControllerCanonicalFunctionBarrier reward objective
      hobjectiveContinuous hobjective).value =
        (fun pair => quittingControllerWordInf reward objective pair.1) ∧
      ∀ barrier : QuittingControllerUpperSemicontinuousBarrier reward objective,
        ∀ pair, barrier.value pair ≤
          quittingControllerWordInf reward objective pair.1 := by
  exact ⟨rfl, fun barrier pair => barrier.le_wordInf pair⟩

/-- The canonical word infimum is the greatest bounded upper-semicontinuous
post-fixed point of the reward-box Bellman operator, and is itself fixed. -/
theorem quittingControllerWordInf_isGreatest_bellmanFixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjective : ∀ pair, 0 ≤ objective pair) :
    quittingControllerRewardBoxBellmanOperator reward objective
        (quittingControllerCanonicalFunctionBarrier reward objective
          hobjectiveContinuous hobjective).value =
      (quittingControllerCanonicalFunctionBarrier reward objective
        hobjectiveContinuous hobjective).value ∧
      ∀ barrier : QuittingControllerUpperSemicontinuousBarrier reward objective,
        ∀ pair, barrier.value pair ≤
          (quittingControllerCanonicalFunctionBarrier reward objective
            hobjectiveContinuous hobjective).value pair := by
  exact ⟨quittingControllerCanonicalFunctionBarrier_fixedPoint
      reward objective hobjectiveContinuous hobjective,
    fun barrier pair => barrier.le_wordInf pair⟩

/-- Root-list evaluation preserves the canonical semantic carrier from every
carrier tail. -/
theorem quittingControllerRootListEvalFrom_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (QuittingRootSimplex ι))
    (tail : QuittingTerminalSemanticPair ι)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward) :
    quittingControllerRootListEvalFrom reward roots tail ∈
      quittingTerminalSemanticCarrier reward := by
  induction roots with
  | nil => exact htail
  | cons root roots ih =>
      exact quittingTerminalSemanticPrefix_mem_carrier reward
        (quittingRootOfSimplex root) _ ih

/-- The word infimum is monotone under prefixing by an arbitrary literal PMF
root, not only its simplex presentation. -/
theorem quittingControllerWordInf_le_pmfPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (tail : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool) :
    quittingControllerWordInf reward objective tail ≤
      quittingControllerWordInf reward objective
        (quittingTerminalSemanticPrefix reward root tail) := by
  simpa only [quittingRootOfSimplex_simplexOfRoot] using
    quittingControllerWordInf_le_prefix reward objective hobjective tail
      (quittingSimplexOfRoot root)

/-- Every finite literal prefix moves the word infimum weakly upward. -/
theorem quittingControllerWordInf_le_finitePrefixSemanticEval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (tail : QuittingTerminalSemanticPair ι) :
    quittingControllerWordInf reward objective tail ≤
      quittingControllerWordInf reward objective
        (quittingFinitePrefixSemanticEval reward roots cutoff tail) := by
  induction cutoff generalizing roots with
  | zero => exact le_rfl
  | succ cutoff ih =>
      simp only [quittingFinitePrefixSemanticEval]
      exact (ih (fun time => roots (time + 1))).trans
        (quittingControllerWordInf_le_pmfPrefix reward objective hobjective _
          (roots 0))

/-- If an objective has a displayed minimum on the semantic carrier, its
word infimum at the Never boundary equals that minimum. -/
theorem quittingControllerWordInf_never_eq_carrierMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (objective : QuittingTerminalSemanticPair ι → ℝ)
    (hobjectiveContinuous : Continuous objective)
    (hobjective : ∀ pair, 0 ≤ objective pair)
    (minimizer : QuittingTerminalSemanticPair ι)
    (hminimizer : minimizer ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      objective minimizer ≤ objective pair) :
    quittingControllerWordInf reward objective
        (quittingNeverBoundarySemanticPair reward) = objective minimizer := by
  apply le_antisymm
  · rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
      at hminimizer
    obtain ⟨pairs, hpairs, hpairsLimit⟩ := mem_closure_iff_seq_limit.mp hminimizer
    have hlevel : ∀ index,
        quittingControllerWordInf reward objective
            (quittingNeverBoundarySemanticPair reward) ≤
          quittingControllerWordInf reward objective (pairs index) := by
      intro index
      obtain ⟨roots, cutoff, hpairsEq⟩ := hpairs index
      rw [hpairsEq]
      exact quittingControllerWordInf_le_finitePrefixSemanticEval
        reward objective hobjective roots cutoff _
    have hclosed :=
      (upperSemicontinuous_quittingControllerWordInf reward objective
        hobjectiveContinuous hobjective).isClosed_preimage
          (quittingControllerWordInf reward objective
            (quittingNeverBoundarySemanticPair reward))
    have hlimitMem : minimizer ∈
        quittingControllerWordInf reward objective ⁻¹'
          Ici (quittingControllerWordInf reward objective
            (quittingNeverBoundarySemanticPair reward)) :=
      hclosed.mem_of_tendsto hpairsLimit
        (Filter.Eventually.of_forall hlevel)
    exact hlimitMem.trans (by
      simpa using (quittingControllerWordInf_le_word reward objective
        hobjective minimizer []))
  · unfold quittingControllerWordInf
    apply le_ciInf
    intro roots
    exact hminimum _
      (quittingControllerRootListEvalFrom_mem_carrier reward roots _ <|
        by
          rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
          exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩)

section NonemptyPlayer

variable [Nonempty ι]

omit [DecidableEq ι] in
/-- Fixed-target objective is nonnegative on every semantic pair. -/
theorem quittingControllerTargetLoss_nonneg
    (target : Payoff ι) (pair : QuittingTerminalSemanticPair ι) :
    0 ≤ quittingControllerTargetLoss target pair := by
  unfold quittingControllerTargetLoss
  exact le_max_of_le_left (norm_nonneg _)

/-- Canonical fixed-target upper-semicontinuous barrier `Q_v`. -/
def quittingControllerTargetFunctionBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  quittingControllerWordInf reward (quittingControllerTargetLoss target) pair

/-- The canonical fixed-target barrier is upper semicontinuous. -/
theorem upperSemicontinuous_quittingControllerTargetFunctionBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    UpperSemicontinuous (quittingControllerTargetFunctionBarrier reward target) :=
  upperSemicontinuous_quittingControllerWordInf reward _
    (continuous_quittingControllerTargetLoss target)
    (quittingControllerTargetLoss_nonneg target)

/-- The fixed-target word infimum packaged as an admissible bounded
upper-semicontinuous Bellman barrier. -/
def quittingControllerTargetUpperSemicontinuousBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    QuittingControllerUpperSemicontinuousBarrier reward
      (quittingControllerTargetLoss target) :=
  quittingControllerCanonicalFunctionBarrier reward _
    (continuous_quittingControllerTargetLoss target)
    (quittingControllerTargetLoss_nonneg target)

/-- The fixed-target function `Q_v` is pointwise greatest among every
bounded upper-semicontinuous barrier below its loss obstacle and monotone
under every product-root prefix. -/
theorem quittingControllerTargetFunctionBarrier_isGreatest
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    (quittingControllerTargetUpperSemicontinuousBarrier reward target).value =
        (fun pair =>
          quittingControllerTargetFunctionBarrier reward target pair.1) ∧
      ∀ barrier : QuittingControllerUpperSemicontinuousBarrier reward
          (quittingControllerTargetLoss target),
        ∀ pair, barrier.value pair ≤
          quittingControllerTargetFunctionBarrier reward target pair.1 := by
  exact quittingControllerWordInf_isGreatest_upperSemicontinuousBarrier
    reward _ (continuous_quittingControllerTargetLoss target)
      (quittingControllerTargetLoss_nonneg target)

/-- Exact Bellman equation for the fixed-target barrier. -/
theorem quittingControllerTargetFunctionBarrier_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (pair : QuittingTerminalSemanticPair ι) :
    quittingControllerTargetFunctionBarrier reward target pair =
      min (quittingControllerTargetLoss target pair)
        (⨅ root : QuittingRootSimplex ι,
          quittingControllerTargetFunctionBarrier reward target
            (quittingTerminalSemanticPrefix reward
              (quittingRootOfSimplex root) pair)) :=
  quittingControllerWordInf_bellman reward _
    (quittingControllerTargetLoss_nonneg target) pair

/-- At the Never boundary, the fixed-target greatest barrier equals the
compact controller value `W_r(v)`. -/
theorem quittingControllerTargetFunctionBarrier_never_eq_targetValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    quittingControllerTargetFunctionBarrier reward target
        (quittingNeverBoundarySemanticPair reward) =
      quittingControllerTargetValue reward target := by
  exact quittingControllerWordInf_never_eq_carrierMinimum reward _
    (continuous_quittingControllerTargetLoss target)
    (quittingControllerTargetLoss_nonneg target)
    (quittingControllerTargetMinimizer reward target)
    (quittingControllerTargetMinimizer_mem reward target)
    (fun pair hpair =>
      quittingControllerTargetMinimizer_isMinimum reward target hpair)

/-- The compact fixed-target controller value is exactly the canonical
function barrier at Never, and it bounds every admissible barrier there. -/
theorem quittingControllerTargetValue_functionBarrierDuality
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    (quittingControllerTargetUpperSemicontinuousBarrier reward target).value
        (quittingControllerNeverRewardBox reward) =
        quittingControllerTargetValue reward target ∧
      ∀ barrier : QuittingControllerUpperSemicontinuousBarrier reward
          (quittingControllerTargetLoss target),
        barrier.value (quittingControllerNeverRewardBox reward) ≤
          quittingControllerTargetValue reward target := by
  constructor
  · exact quittingControllerTargetFunctionBarrier_never_eq_targetValue
      reward target
  · intro barrier
    exact (barrier.le_wordInf (quittingControllerNeverRewardBox reward)).trans_eq
      (quittingControllerTargetFunctionBarrier_never_eq_targetValue
        reward target)

omit [DecidableEq ι] in
/-- Raw maximum debt has the literal lower reward-box bound `-2R`. -/
theorem quittingControllerRawMaximumDebt_box_lower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈
      quittingTerminalSemanticBox ι (quittingRewardBound reward)) :
    -2 * quittingRewardBound reward ≤
      quittingControllerRawMaximumDebt pair := by
  have hbound := abs_quittingControllerRawMaximumDebt_le_of_mem_box
    (quittingRewardBound_nonneg reward) hpair
  linarith [neg_le_of_abs_le hbound]

omit [DecidableEq ι] in
/-- Raw maximum debt has the literal upper reward-box bound `2R`. -/
theorem quittingControllerRawMaximumDebt_box_upper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈
      quittingTerminalSemanticBox ι (quittingRewardBound reward)) :
    quittingControllerRawMaximumDebt pair ≤
      2 * quittingRewardBound reward :=
  le_of_abs_le <| abs_quittingControllerRawMaximumDebt_le_of_mem_box
    (quittingRewardBound_nonneg reward) hpair

/-- Canonical target-free raw-debt barrier on the full reward box. -/
def quittingControllerTesterFunctionBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingControllerRewardBox reward) : ℝ :=
  quittingControllerRewardBoxWordInf reward
    quittingControllerRawMaximumDebt pair

/-- The full-reward-box raw-debt barrier is upper semicontinuous. -/
theorem upperSemicontinuous_quittingControllerTesterFunctionBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    UpperSemicontinuous (quittingControllerTesterFunctionBarrier reward) :=
  upperSemicontinuous_quittingControllerRewardBoxWordInf reward _
    (-2 * quittingRewardBound reward)
    continuous_quittingControllerRawMaximumDebt
    (quittingControllerRawMaximumDebt_box_lower reward)

/-- The raw-debt word infimum packaged as an admissible bounded
upper-semicontinuous barrier on the full reward box. -/
def quittingControllerTesterUpperSemicontinuousBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingControllerUpperSemicontinuousBarrier reward
      quittingControllerRawMaximumDebt where
  value := quittingControllerTesterFunctionBarrier reward
  upperSemicontinuous :=
    upperSemicontinuous_quittingControllerTesterFunctionBarrier reward
  bounded := by
    refine ⟨2 * quittingRewardBound reward, fun pair => ?_⟩
    change |quittingControllerRewardBoxWordInf reward
      quittingControllerRawMaximumDebt pair| ≤ 2 * quittingRewardBound reward
    apply abs_le.mpr
    constructor
    · simpa only [neg_mul] using
        quittingControllerRewardBoxWordInf_lower reward _ _
          (quittingControllerRawMaximumDebt_box_lower reward) pair
    · exact (quittingControllerRewardBoxWordInf_le_word reward _ _
        (quittingControllerRawMaximumDebt_box_lower reward) pair []).trans
          (quittingControllerRawMaximumDebt_box_upper reward pair.1 pair.2)
  le_objective := fun pair => by
    simpa [quittingControllerTesterFunctionBarrier] using
      quittingControllerRewardBoxWordInf_le_word reward _ _
      (quittingControllerRawMaximumDebt_box_lower reward) pair []
  le_prefix := fun pair root =>
    quittingControllerRewardBoxWordInf_le_prefix reward _ _
      (quittingControllerRawMaximumDebt_box_lower reward) pair root

/-- The target-free raw-debt function is the pointwise greatest bounded
upper-semicontinuous barrier on the entire reward box. -/
theorem quittingControllerTesterFunctionBarrier_isGreatest
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingControllerTesterUpperSemicontinuousBarrier reward).value =
        quittingControllerTesterFunctionBarrier reward ∧
      ∀ barrier : QuittingControllerUpperSemicontinuousBarrier reward
          quittingControllerRawMaximumDebt,
        ∀ pair, barrier.value pair ≤
          quittingControllerTesterFunctionBarrier reward pair := by
  exact ⟨rfl, fun barrier pair => barrier.le_rewardBoxWordInf pair⟩

/-- Exact Bellman equation for the full-reward-box raw-debt barrier. -/
theorem quittingControllerTesterFunctionBarrier_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingControllerRewardBox reward) :
    quittingControllerTesterFunctionBarrier reward pair =
      min (quittingControllerRawMaximumDebt pair.1)
        (⨅ root : QuittingRootSimplex ι,
          quittingControllerTesterFunctionBarrier reward
            (quittingControllerRewardBoxPrefix reward root pair)) :=
  quittingControllerRewardBoxWordInf_bellman reward _ _
    (quittingControllerRawMaximumDebt_box_lower reward) pair

/-- At the Never boundary, the full-box raw-debt greatest barrier equals the
literal minimum raw maximum debt `eta(r)`. -/
theorem quittingControllerTesterFunctionBarrier_never_eq_testerValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingControllerTesterFunctionBarrier reward
        (quittingControllerNeverRewardBox reward) =
      quittingControllerTesterValue reward := by
  have hnever : quittingNeverBoundarySemanticPair reward ∈
      quittingTerminalSemanticCarrier reward := by
    rw [terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable]
    exact subset_closure ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  have hbridge : quittingControllerTesterFunctionBarrier reward
        (quittingControllerNeverRewardBox reward) =
      quittingControllerWordInf reward quittingTerminalSemanticExploitability
        (quittingNeverBoundarySemanticPair reward) := by
    unfold quittingControllerTesterFunctionBarrier
      quittingControllerRewardBoxWordInf quittingControllerWordInf
    congr 1
    funext roots
    rw [quittingControllerRewardBoxRootListEvalFrom_coe]
    exact quittingControllerRawMaximumDebt_eq_semanticExploitability_of_mem_carrier
      reward (quittingControllerRootListEvalFrom_mem_carrier reward roots _ hnever)
  rw [hbridge]
  exact quittingControllerWordInf_never_eq_carrierMinimum reward _
    continuous_quittingTerminalSemanticExploitability
    quittingControllerSemanticExploitability_nonneg
    (quittingControllerTesterMinimizer reward)
    (quittingControllerTesterMinimizer_mem reward)
    (fun pair hpair => quittingControllerTesterMinimizer_isMinimum reward hpair)

/-- The target-free controller value is exactly the canonical raw-debt
function barrier at Never and bounds every admissible raw-debt barrier there. -/
theorem quittingControllerTesterValue_functionBarrierDuality
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingControllerTesterUpperSemicontinuousBarrier reward).value
        (quittingControllerNeverRewardBox reward) =
        quittingControllerTesterValue reward ∧
      ∀ barrier : QuittingControllerUpperSemicontinuousBarrier reward
          quittingControllerRawMaximumDebt,
        barrier.value (quittingControllerNeverRewardBox reward) ≤
          quittingControllerTesterValue reward := by
  constructor
  · exact quittingControllerTesterFunctionBarrier_never_eq_testerValue reward
  · intro barrier
    exact (barrier.le_rewardBoxWordInf
      (quittingControllerNeverRewardBox reward)).trans_eq
        (quittingControllerTesterFunctionBarrier_never_eq_testerValue reward)

end NonemptyPlayer

end GameTheory
