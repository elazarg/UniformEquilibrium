/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedVariational

/-!
# Combined deleted survival of a literal prefix and an actual base chronology

The arbitrary normalized-passport prefix and the roots already present before
the base marked row are distinct pieces of provenance.  This file gives their
literal concatenation and exact joint/deleted survival factorizations.  It is
source independent and asserts no infinite renewal chain.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The chronological list of actual live roots strictly before `stage`. -/
def quittingBehaviorProfilePremarkRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | stage + 1 =>
      quittingBehaviorProfilePremarkRoots reward profile stage ++
        [quittingProfileLiveRoot reward profile stage]

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorProfilePremarkRoots_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    (quittingBehaviorProfilePremarkRoots reward profile stage).length = stage := by
  induction stage with
  | zero => rfl
  | succ stage ih => simp [quittingBehaviorProfilePremarkRoots, ih]

omit [DecidableEq ι] in
/-- Joint survival factors exactly across literal word concatenation. -/
theorem quittingLiteralRootStackJointSurvival_append
    (first second : List (ι → PMF Bool)) :
    quittingLiteralRootStackJointSurvival (first ++ second) =
      quittingLiteralRootStackJointSurvival first *
        quittingLiteralRootStackJointSurvival second := by
  simp [quittingLiteralRootStackJointSurvival]

omit [DecidableEq ι] in
/-- The joint survival of the literal base word is exactly the probability of
reaching its displayed marked row. -/
theorem quittingLiteralRootStackJointSurvival_premarkRoots_eq_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    quittingLiteralRootStackJointSurvival
        (quittingBehaviorProfilePremarkRoots reward profile stage) =
      quittingLiveMass reward profile stage := by
  induction stage with
  | zero => simp [quittingBehaviorProfilePremarkRoots,
      quittingLiteralRootStackJointSurvival]
  | succ stage ih =>
      rw [quittingBehaviorProfilePremarkRoots,
        quittingLiteralRootStackJointSurvival_append, ih,
        quittingLiveMass_succ]
      simp only [quittingLiteralRootStackJointSurvival, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [quittingJointContinueMass_eq_product,
        quittingStationaryContinueMass_eq_prod_continueProbability]
      unfold quittingProfileLiveRoot
      rfl

/-- Player-deleted survival factors exactly across literal word
concatenation. -/
theorem quittingLiteralRootStackOpponentSurvival_append
    (first second : List (ι → PMF Bool)) (who : ι) :
    quittingLiteralRootStackOpponentSurvival (first ++ second) who =
      quittingLiteralRootStackOpponentSurvival first who *
        quittingLiteralRootStackOpponentSurvival second who := by
  simp [quittingLiteralRootStackOpponentSurvival]

/-- The complete premark word of one raw descendant: first its arbitrary new
prefix, then every root already present before the base marked row. -/
def quittingCombinedPremarkWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (newWord : List (ι → PMF Bool))
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (baseMark : ℕ) : List (ι → PMF Bool) :=
  newWord ++ quittingBehaviorProfilePremarkRoots reward baseProfile baseMark

omit [DecidableEq ι] in
@[simp] theorem quittingCombinedPremarkWord_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (newWord : List (ι → PMF Bool))
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (baseMark : ℕ) :
    (quittingCombinedPremarkWord reward newWord baseProfile baseMark).length =
      newWord.length + baseMark := by
  simp [quittingCombinedPremarkWord]

omit [DecidableEq ι] in
/-- Literal joint-survival factorization of the combined word. -/
theorem quittingCombinedPremarkWord_jointSurvival_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (newWord : List (ι → PMF Bool))
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (baseMark : ℕ) :
    quittingLiteralRootStackJointSurvival
        (quittingCombinedPremarkWord reward newWord baseProfile baseMark) =
      quittingLiteralRootStackJointSurvival newWord *
        quittingLiveMass reward baseProfile baseMark := by
  rw [quittingCombinedPremarkWord,
    quittingLiteralRootStackJointSurvival_append,
    quittingLiteralRootStackJointSurvival_premarkRoots_eq_liveMass]

/-- Literal player-deleted-survival factorization of the combined word. -/
theorem quittingCombinedPremarkWord_opponentSurvival_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (newWord : List (ι → PMF Bool))
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (baseMark : ℕ) (who : ι) :
    quittingLiteralRootStackOpponentSurvival
        (quittingCombinedPremarkWord reward newWord baseProfile baseMark) who =
      quittingLiteralRootStackOpponentSurvival newWord who *
        quittingLiteralRootStackOpponentSurvival
          (quittingBehaviorProfilePremarkRoots reward baseProfile baseMark) who := by
  exact quittingLiteralRootStackOpponentSurvival_append _ _ who

/-- A positive base deleted-survival floor transfers vanishing of the
combined deleted clock back to the arbitrary prefix clock. -/
theorem tendsto_prefixOpponentSurvival_zero_of_combined
    (newWord base : ℕ → List (ι → PMF Bool)) (who : ι) (rho : ℝ)
    (hrho : 0 < rho)
    (hbase : ∀ rank, rho ≤
      quittingLiteralRootStackOpponentSurvival (base rank) who)
    (hcombined : Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival
        (newWord rank ++ base rank) who) atTop (nhds 0)) :
    Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival (newWord rank) who)
        atTop (nhds 0) := by
  have hscaled : Tendsto (fun rank =>
      quittingLiteralRootStackOpponentSurvival
        (newWord rank ++ base rank) who / rho) atTop (nhds 0) := by
    simpa using hcombined.div_const rho
  refine squeeze_zero' (Eventually.of_forall fun rank =>
    quittingLiteralRootStackOpponentSurvival_nonneg (newWord rank) who) ?_
      hscaled
  filter_upwards [] with rank
  rw [quittingLiteralRootStackOpponentSurvival_append]
  apply (le_div_iff₀ hrho).2
  exact mul_le_mul_of_nonneg_left (hbase rank)
    (quittingLiteralRootStackOpponentSurvival_nonneg (newWord rank) who)

end GameTheory
