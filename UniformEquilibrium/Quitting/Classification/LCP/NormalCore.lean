/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Recursively normal-player matrices

Solan and Solan, *Quitting games and linear complementarity problems*,
Math. Oper. Res. **45**(2) (2020), use three distinguished player sets that
must be kept apart.

**The min-max normal players** of their Section 2.3.  Player `i` is normal
when its min-max value is nonpositive, that is, no better than the payoff
`r^i_i = 0` it gets by quitting alone under their standing normalization.  This
set carries Lemma 2.6, Lemma 2.12 and Theorem 2.13.  It is defined by a
strategic quantity, represented here by `GameTheory.quittingPunishmentValue`,
and nothing in this file computes it.

**The α-players** of their Section 5.  These are the members of the
intersection of

`Iₙ₊₁ = {i ∈ Iₙ | ∃ j ∈ Iₙ, j ≠ i ∧ M i j ≤ 0}`,

the recursion the paper's Section 5 displays, with its witness condition
written `j ∈ I_l \ {i}`.  Every α-player is normal in the sense above, and the
paper states that the converse may fail.  This is `normalLayer` and
`normalCore` below; the distinct-witness form is the source's, not a repair
made here.

**An earlier draft's display.**  A draft of the same paper displays this
recursion without the distinctness condition,

`Iₙ₊₁ = {i ∈ Iₙ | ∃ j ∈ Iₙ, M i j ≤ 0}`.

Read literally after the standing zero-diagonal normalization that recursion
never removes a player, since `j = i` always qualifies.  It is formalized as
`printedNormalLayer` and `printedNormalCore`, and its collapse is proved, so
that the two displays cannot be confused downstream.

Defining the α-player core does not carry any source theorem with it.  Every
stationary or sunspot consequence over this core must be proved separately;
the algebraic gate imports no abstract record that assumes those conclusions.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The recursion exactly as displayed in an earlier draft of the source,
without the distinctness condition the final Section 5 carries. -/
def printedNormalLayer (M : ι → ι → ℝ) : ℕ → Finset ι
  | 0 => Finset.univ
  | n + 1 =>
      (printedNormalLayer M n).filter fun i =>
        ∃ j ∈ printedNormalLayer M n, M i j ≤ 0

omit [DecidableEq ι] in
/-- With a nonpositive diagonal, the draft's recursion retains every player at
every layer. -/
theorem printedNormalLayer_eq_univ_of_diagonal_nonpos
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i ≤ 0) :
    ∀ n : ℕ, printedNormalLayer M n = Finset.univ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [printedNormalLayer, ih]
      apply Finset.filter_eq_self.mpr
      intro i hi
      exact ⟨i, hi, hdiag i⟩

/-- The literal intersection of the draft's layers. -/
def printedNormalCore (M : ι → ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ n : ℕ, i ∈ printedNormalLayer M n

omit [DecidableEq ι] in
/-- The draft's core is the full player set whenever the diagonal is
nonpositive. -/
theorem printedNormalCore_eq_univ_of_diagonal_nonpos
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i ≤ 0) :
    printedNormalCore M = Finset.univ := by
  classical
  ext i
  simp [printedNormalCore,
    printedNormalLayer_eq_univ_of_diagonal_nonpos M hdiag]

/-- In particular, the source-normalized singleton matrix makes the draft's
literal normal core degenerate. -/
theorem printedNormalCore_normalized_eq_univ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    printedNormalCore (normalizedSoloMatrix reward) = Finset.univ := by
  apply printedNormalCore_eq_univ_of_diagonal_nonpos
  intro i
  simp

/-- The Section 5 normality layers `I₀ = I` and
`Iₙ₊₁ = {i ∈ Iₙ | ∃ j ∈ Iₙ, j ≠ i ∧ M i j ≤ 0}`. -/
def normalLayer (M : ι → ι → ℝ) : ℕ → Finset ι
  | 0 => Finset.univ
  | n + 1 =>
      (normalLayer M n).filter fun i =>
        ∃ j ∈ normalLayer M n, j ≠ i ∧ M i j ≤ 0

@[simp] theorem normalLayer_zero (M : ι → ι → ℝ) :
    normalLayer M 0 = Finset.univ := rfl

@[simp] theorem mem_normalLayer_succ
    (M : ι → ι → ℝ) (n : ℕ) (i : ι) :
    i ∈ normalLayer M (n + 1) ↔
      i ∈ normalLayer M n ∧
        ∃ j ∈ normalLayer M n, j ≠ i ∧ M i j ≤ 0 := by
  simp [normalLayer]

/-- The normality layers form a decreasing sequence. -/
theorem normalLayer_succ_subset
    (M : ι → ι → ℝ) (n : ℕ) :
    normalLayer M (n + 1) ⊆ normalLayer M n := by
  intro i hi
  exact (mem_normalLayer_succ M n i).mp hi |>.1

/-- Normality layers are antitone in their layer index. -/
theorem normalLayer_antitone
    (M : ι → ι → ℝ) {n m : ℕ} (hnm : n ≤ m) :
    normalLayer M m ⊆ normalLayer M n := by
  induction hnm with
  | refl => exact Finset.Subset.rfl
  | @step m hnm ih =>
      exact fun _ hi => ih (normalLayer_succ_subset M m hi)

/-- The α-player set `I∗∗ = ⋂ₙ Iₙ` of the source's Section 5. -/
def normalCore (M : ι → ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∀ n : ℕ, i ∈ normalLayer M n

@[simp] theorem mem_normalCore
    (M : ι → ι → ℝ) (i : ι) :
    i ∈ normalCore M ↔ ∀ n : ℕ, i ∈ normalLayer M n := by
  classical
  simp [normalCore]

/-- Over a finite player set, the decreasing normality recursion reaches its
intersection after finitely many layers. -/
theorem exists_normalLayer_eq_normalCore (M : ι → ι → ℝ) :
    ∃ n : ℕ, normalLayer M n = normalCore M := by
  classical
  have hmissing : ∀ i : ι, i ∉ normalCore M →
      ∃ n : ℕ, i ∉ normalLayer M n := by
    intro i hcore
    rw [mem_normalCore] at hcore
    simpa only [not_forall] using hcore
  let firstMissing : ι → ℕ := fun i =>
    if h : i ∈ normalCore M then 0 else Classical.choose (hmissing i h)
  let cutoff : ℕ := ∑ i : ι, firstMissing i
  refine ⟨cutoff, Finset.Subset.antisymm ?_ ?_⟩
  · intro i hi
    by_contra hcore
    have hnot := Classical.choose_spec (hmissing i hcore)
    have hfirst : i ∉ normalLayer M (firstMissing i) := by
      rw [show firstMissing i = Classical.choose (hmissing i hcore) by
        simp only [firstMissing, dif_neg hcore]]
      exact hnot
    have hle : firstMissing i ≤ cutoff := by
      dsimp only [cutoff]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    exact hfirst (normalLayer_antitone M hle hi)
  · intro i hi
    exact (mem_normalCore M i).1 hi cutoff

/-- Every member of the stabilized α-player core has a distinct nonpositive
comparison witness in that same core. -/
theorem exists_core_blocker_of_mem_normalCore
    (M : ι → ι → ℝ) {i : ι} (hi : i ∈ normalCore M) :
    ∃ j ∈ normalCore M, j ≠ i ∧ M i j ≤ 0 := by
  obtain ⟨n, hn⟩ := exists_normalLayer_eq_normalCore M
  have hisucc : i ∈ normalLayer M (n + 1) :=
    (mem_normalCore M i).1 hi (n + 1)
  obtain ⟨_, j, hj, hne, hentry⟩ :=
    (mem_normalLayer_succ M n i).1 hisucc
  exact ⟨j, by simpa [hn] using hj, hne, hentry⟩

/-- The exact principal matrix on the recursively normal α-players. -/
def normalPlayerMatrix (M : ι → ι → ℝ) :
    normalCore M → normalCore M → ℝ :=
  principalMatrix M (normalCore M)

/-- Game-facing α-player matrix, built after the playerwise solo
normalization. -/
def normalizedNormalPlayerMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalCore (normalizedSoloMatrix reward) →
      normalCore (normalizedSoloMatrix reward) → ℝ :=
  normalPlayerMatrix (normalizedSoloMatrix reward)

/-- A nonempty α-player core.  This is an algebraic side condition, not a
strategic conclusion. -/
def HasNormalPlayers (M : ι → ι → ℝ) : Prop :=
  (normalCore M).Nonempty

/-- The all-abnormal matrix regime: no α-players at all. -/
def AllPlayersAbnormal (M : ι → ι → ℝ) : Prop :=
  normalCore M = ∅

/-- Failure of α-player-core nonemptiness is equivalent to the all-abnormal
matrix regime. -/
theorem allPlayersAbnormal_iff_not_hasNormalPlayers
    (M : ι → ι → ℝ) :
    AllPlayersAbnormal M ↔ ¬HasNormalPlayers M := by
  unfold AllPlayersAbnormal HasNormalPlayers
  constructor
  · intro hempty hnonempty
    rw [hempty] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  · intro h
    exact Finset.not_nonempty_iff_eq_empty.mp h

end QuittingLCPClassification
end GameTheory
