/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FinitePaidCollision
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllPlayerEscapeDebtJump
import UniformEquilibrium.Quitting.Terminal.CompactStoppingLawCapUpperBound

/-!
# Minimum consequences of the all-player escape account

For one supplied terminal-law escape account, nonnegative singleton rewards
make every reconstructed cap drop nonnegative.  At a supplied global carrier
debt minimum, the total cap drop lies between zero and escaped social reward.
If no actual profile attains the same minimum debt value, the reconstructed
debt jump is strict and a finite pigeonhole argument selects a coalition with
positive escape mass and positive social reward at explicit finite-player
scales.

These are conditional consequences of a supplied selected/account package,
global minimality, reward bounds, and minimum-value nonattainment.  They do not
prove the social-nonpositive chamber, attainment, a downstream consumer, a
Fin4 specialization, terminal Nash play, or a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open scoped BigOperators ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

namespace QuittingTerminalSemanticEscapeAccount

omit [Nontrivial ι] in
/-- Downward change of one selected target cap under marginal-law
reconstruction. -/
def reconstructedCapDrop
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (_account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (player : ι) : Real :=
  target.2 player - quittingContinuationBestResponseValue reward
    (quittingCompactStoppingLawProfile reward selected.laws) player

omit [Nontrivial ι] in
/-- Sum of the selected target-to-reconstructed cap drops. -/
def reconstructedCapDropSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected) : Real :=
  ∑ player, account.reconstructedCapDrop player

omit [Nontrivial ι] in
/-- Social reward moment carried by the terminal-law escape defect. -/
def escapeSocialReward
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected) : Real :=
  ∑ terminal, quittingTerminalEscapeMass reward selected.laws
    account.mass terminal * ∑ player, reward terminal player

omit [Nontrivial ι] in
/-- Total-debt increase of the reconstructed marginal-law profile over the
selected target. -/
def reconstructedDebtJump
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (_account : QuittingTerminalSemanticEscapeAccount reward target selected) : Real :=
  quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingCompactStoppingLawProfile reward selected.laws)) -
    quittingTerminalSemanticDebtSum target

omit [Nontrivial ι] in
/-- The selected-law cap correction is a literal nonnegative cap drop when
the corresponding singleton reward is nonnegative. -/
theorem reconstructedCapDrop_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (player : ι)
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal player) player) :
    0 ≤ account.reconstructedCapDrop player := by
  unfold reconstructedCapDrop
  exact sub_nonneg.mpr
    (selected.reconstructedCap_le_of_singleton_nonneg player hsingleton)

omit [Nontrivial ι] in
/-- Reorientation of the exact debt account: escaped social reward is debt
jump plus the total cap drop. -/
theorem escapeSocialReward_eq_reconstructedDebtJump_add_capDropSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected) :
    account.escapeSocialReward =
      account.reconstructedDebtJump + account.reconstructedCapDropSum := by
  have hdebt :=
    account.debtSum_sub_target_eq_escapeSocialReward_sub_capDropSum
  simpa [escapeSocialReward, reconstructedDebtJump, reconstructedCapDropSum,
    reconstructedCapDrop] using (eq_sub_iff_add_eq.mp hdebt).symm

omit [Nontrivial ι] in
/-- At a global carrier debt minimum with nonnegative singleton rewards, the
total cap drop is nonnegative and no larger than escaped social reward. -/
theorem capDropSum_nonneg_and_le_escapeSocialReward_of_minimum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player) :
    0 ≤ account.reconstructedCapDropSum ∧
      account.reconstructedCapDropSum ≤ account.escapeSocialReward := by
  have hcap : 0 ≤ account.reconstructedCapDropSum := by
    unfold reconstructedCapDropSum
    exact Finset.sum_nonneg fun player _ =>
      account.reconstructedCapDrop_nonneg player (hsingleton player)
  have hjump : 0 ≤ account.reconstructedDebtJump := by
    unfold reconstructedDebtJump
    exact sub_nonneg.mpr (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward _))
  have haccount := account.escapeSocialReward_eq_reconstructedDebtJump_add_capDropSum
  constructor
  · exact hcap
  · linarith

omit [Nontrivial ι] in
/-- If no actual profile has the selected global minimum debt value, then the
reconstructed marginal-law profile has a strictly positive debt jump. -/
theorem reconstructedDebtJump_pos_of_minimumValue_not_attained
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≠
        quittingTerminalSemanticDebtSum target) :
    0 < account.reconstructedDebtJump := by
  let profile := quittingCompactStoppingLawProfile reward selected.laws
  have hle : quittingTerminalSemanticDebtSum target ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) :=
    hminimum _ (quittingTerminalSemanticPair_mem_carrier reward profile)
  have hne : quittingTerminalSemanticDebtSum target ≠
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) :=
    (hnotAttained profile).symm
  unfold reconstructedDebtJump
  exact sub_pos.mpr (lt_of_le_of_ne hle hne)

omit [Nontrivial ι] in
/-- A positive lower bound for escaped social reward selects one coalition
with positive social reward, a sharp finite-label product share, and its
consequent escape-mass floor. -/
theorem exists_positiveSocialRewardEscape_of_pos_le_escapeSocialReward
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (M residual : Real) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hresidual : 0 < residual)
    (hresidualLe : residual ≤ account.escapeSocialReward) :
    ∃ terminal,
      0 < quittingTerminalEscapeMass reward selected.laws
          account.mass terminal * ∑ player, reward terminal player ∧
      0 < ∑ player, reward terminal player ∧
      0 < quittingTerminalEscapeMass reward selected.laws
        account.mass terminal ∧
      residual / ((2 ^ Fintype.card ι - 1 : Nat) : Real) ≤
        quittingTerminalEscapeMass reward selected.laws
          account.mass terminal * ∑ player, reward terminal player ∧
      residual / (((2 ^ Fintype.card ι - 1 : Nat) : Real) *
          (Fintype.card ι : Real) * M) ≤
        quittingTerminalEscapeMass reward selected.laws
          account.mass terminal := by
  classical
  let player : ι := Classical.choice (inferInstance : Nonempty ι)
  let witness : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  let indices : Finset {S : Finset ι // S.Nonempty} := Finset.univ
  let mass := fun terminal =>
    quittingTerminalEscapeMass reward selected.laws account.mass terminal
  let social := fun terminal => ∑ player, reward terminal player
  have hindices : indices.Nonempty := ⟨witness, Finset.mem_univ witness⟩
  have hmass : ∀ terminal ∈ indices, 0 ≤ mass terminal := by
    intro terminal _
    exact account.escapeMass_nonneg terminal
  have hsocial : ∀ terminal ∈ indices,
      social terminal ≤ (Fintype.card ι : Real) * M := by
    intro terminal _
    calc
      social terminal ≤ ∑ player : ι, M := by
        apply Finset.sum_le_sum
        intro player _
        exact (le_abs_self _).trans (hreward terminal player)
      _ = (Fintype.card ι : Real) * M := by
        simp [nsmul_eq_mul]
  have hplayerCard : 0 < (Fintype.card ι : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcap : 0 < (Fintype.card ι : Real) * M := mul_pos hplayerCard hM
  have hsum : residual ≤ ∑ terminal ∈ indices,
      mass terminal * social terminal := by
    simpa only [escapeSocialReward, indices, mass, social,
      Finset.sum_filter, Finset.filter_true_of_mem] using hresidualLe
  obtain ⟨terminal, _hterminal, hproduct, hproductPos, hsocialPos, hmassFloor⟩ :=
    Math.FinitePaidCollision.exists_paid_collision_of_nonempty_finset_with_product
      indices hindices mass social residual ((Fintype.card ι : Real) * M)
      hmass hresidual hsum hsocial hcap
  have hcard : indices.card = 2 ^ Fintype.card ι - 1 := by
    rw [show indices.card =
        Fintype.card {S : Finset ι // S.Nonempty} by
      simp [indices]]
    exact Math.FinitePaidCollision.nonemptyCoalitionSubtype_card ι
  have hcardReal : (indices.card : Real) =
      ((2 ^ Fintype.card ι - 1 : Nat) : Real) := by
    exact_mod_cast hcard
  have hmassPos : 0 < mass terminal :=
    pos_of_mul_pos_left hproductPos hsocialPos.le
  refine ⟨terminal, hproductPos, hsocialPos, hmassPos, ?_, ?_⟩
  · simpa only [mass, social, hcardReal] using hproduct
  · have hdenom : (indices.card : Real) *
        ((Fintype.card ι : Real) * M) =
      ((2 ^ Fintype.card ι - 1 : Nat) : Real) *
        (Fintype.card ι : Real) * M := by
      rw [hcardReal]
      ring
    simpa only [mass, hdenom] using hmassFloor

omit [Nontrivial ι] in
/-- Minimum-value nonattainment supplies the positive residual in the
quantitative positive-social-reward escape theorem. -/
theorem exists_positiveSocialRewardEscape_of_minimumValue_not_attained
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (M : Real) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hnotAttained : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≠
        quittingTerminalSemanticDebtSum target) :
    ∃ terminal,
      0 < quittingTerminalEscapeMass reward selected.laws
          account.mass terminal * ∑ player, reward terminal player ∧
      0 < ∑ player, reward terminal player ∧
      0 < quittingTerminalEscapeMass reward selected.laws
        account.mass terminal ∧
      account.reconstructedDebtJump /
          ((2 ^ Fintype.card ι - 1 : Nat) : Real) ≤
        quittingTerminalEscapeMass reward selected.laws
          account.mass terminal * ∑ player, reward terminal player ∧
      account.reconstructedDebtJump /
          (((2 ^ Fintype.card ι - 1 : Nat) : Real) *
            (Fintype.card ι : Real) * M) ≤
        quittingTerminalEscapeMass reward selected.laws
          account.mass terminal := by
  have hjump := account.reconstructedDebtJump_pos_of_minimumValue_not_attained
    hminimum hnotAttained
  have hcap := account.capDropSum_nonneg_and_le_escapeSocialReward_of_minimum
    hminimum hsingleton
  have haccount :=
    account.escapeSocialReward_eq_reconstructedDebtJump_add_capDropSum
  have hjumpLe : account.reconstructedDebtJump ≤ account.escapeSocialReward := by
    linarith [hcap.1]
  exact account.exists_positiveSocialRewardEscape_of_pos_le_escapeSocialReward
    M account.reconstructedDebtJump hM hreward hjump hjumpLe

end QuittingTerminalSemanticEscapeAccount

end GameTheory
