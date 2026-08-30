/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Diagnostics.Quitting.Collision.AtomicSoloLimitConsequences
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.TerminalGapExactRootMarginalCap
import
  UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification
import UniformEquilibrium.Quitting.Root.SimplexCoalitionMass

/-!
# A charged blocker gate away from the four-player minimum fiber

This module treats an arbitrary sequence of actual terminal-semantic carrier
pairs and exact product roots.  A fixed positive absorption charge either
has an eventually positive semantic-debt drop, or a strict subsequence
converges to a positive interior solo root.  At that limit all debt belongs
to the solo owner, and punishment normality exposes a distinct inactive
player with a floor-safe exact indifference threshold.

The output includes the actual source subsequence and its joint limit.  The
updated payoff is only a boxed punishment-floor tail carrying an exact root;
it is not asserted to be the first coordinate of a terminal-semantic carrier
pair, and the newly indifferent player remains inactive.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

/-- The largest absolute terminal reward coordinate, enlarged to be at least
one.  This is the literal finite maximum used by the quantitative marginal
cap, rather than the larger canonical sum bound. -/
def finFourOffMinimumRewardBound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : ℝ :=
  by
    letI : Nonempty {S : Finset (Fin 4) // S.Nonempty} :=
      ⟨quittingSingletonTerminal 0⟩
    exact max 1 <| Finset.univ.sup' Finset.univ_nonempty fun terminal ↦
      Finset.univ.sup' Finset.univ_nonempty fun who ↦ |reward terminal who|

theorem finFourOffMinimumRewardBound_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    0 < finFourOffMinimumRewardBound reward := by
  letI : Nonempty {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨quittingSingletonTerminal 0⟩
  unfold finFourOffMinimumRewardBound
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem abs_reward_le_finFourOffMinimumRewardBound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |reward terminal who| ≤ finFourOffMinimumRewardBound reward := by
  letI : Nonempty {S : Finset (Fin 4) // S.Nonempty} :=
    ⟨quittingSingletonTerminal 0⟩
  unfold finFourOffMinimumRewardBound
  calc
    |reward terminal who| ≤
        Finset.univ.sup' Finset.univ_nonempty fun player ↦
          |reward terminal player| :=
      Finset.le_sup' (fun player ↦ |reward terminal player|)
        (Finset.mem_univ who)
    _ ≤ Finset.univ.sup' Finset.univ_nonempty fun outcome ↦
        Finset.univ.sup' Finset.univ_nonempty fun player ↦
          |reward outcome player| :=
      Finset.le_sup'
        (fun outcome ↦ Finset.univ.sup' Finset.univ_nonempty fun player ↦
          |reward outcome player|) (Finset.mem_univ terminal)
    _ ≤ max 1 _ := le_max_right _ _

/-- Total semantic debt lost by one exact prefix operation. -/
def quittingTerminalSemanticDebtDrop
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota) (root : iota → PMF Bool) : ℝ :=
  quittingTerminalSemanticDebtSum pair -
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root pair)

/-- Every exact prefix of a carrier pair has nonnegative total semantic-debt
drop. -/
theorem quittingTerminalSemanticDebtDrop_nonneg_of_exact
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota) (root : iota → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    0 ≤ quittingTerminalSemanticDebtDrop reward pair root := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hsum := Finset.sum_le_sum fun who (_ : who ∈ Finset.univ) ↦
    quittingTerminalSemanticDebt_prefix_le reward pair root who
      (hdebt who) hnash
  unfold quittingTerminalSemanticDebtDrop quittingTerminalSemanticDebtSum
  linarith

/-- On four literal players, the finite reward maximum bounds every carrier
debt drop.  This supplies the boundedness needed to state the first branch
with the literal real-valued `liminf`. -/
theorem quittingTerminalSemanticDebtDrop_le_eight_mul_rewardBound
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pair : QuittingTerminalSemanticPair (Fin 4))
    (root : Fin 4 → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticDebtDrop reward pair root ≤
      8 * finFourOffMinimumRewardBound reward := by
  let M := finFourOffMinimumRewardBound reward
  have hbox := quittingTerminalSemanticCarrier_mem_box reward pair
    (abs_reward_le_finFourOffMinimumRewardBound reward) hpair
  have hdebtUpper : ∀ who,
      quittingTerminalSemanticDebt pair who ≤ 2 * M := by
    intro who
    unfold quittingTerminalSemanticDebt
    dsimp only [M]
    linarith [hbox.1.1 who, hbox.2.2 who]
  have hsumUpper : quittingTerminalSemanticDebtSum pair ≤ 8 * M := by
    unfold quittingTerminalSemanticDebtSum
    calc
      ∑ who, quittingTerminalSemanticDebt pair who ≤ ∑ _ : Fin 4, 2 * M :=
        Finset.sum_le_sum fun who _ ↦ hdebtUpper who
      _ = 8 * M := by
        norm_num [Finset.sum_const]
        ring
  have hprefix := quittingTerminalSemanticPrefix_mem_carrier
    reward root pair hpair
  have hprefixNonneg : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root pair) := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hprefix who
  unfold quittingTerminalSemanticDebtDrop
  dsimp only [M] at hsumUpper ⊢
  linarith

/-- Collision times any lower bound on the current total debt is paid by the
actual total semantic-debt drop of an exact prefix. -/
theorem lowerDebt_mul_collisionMass_le_debtDrop_of_exact
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota) (root : iota → PMF Bool)
    (lowerDebt : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hlower : lowerDebt ≤ quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    lowerDebt * quittingRootCollisionMass root ≤
      quittingTerminalSemanticDebtDrop reward pair root := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hcollisionNonneg := quittingRootCollisionMass_nonneg root
  have hscaled := mul_le_mul_of_nonneg_right hlower hcollisionNonneg
  have hcollision :=
    quittingRootCollisionMass_mul_sum_le_sum_opponentAbsorptionMass_mul
      root (fun who ↦ quittingTerminalSemanticDebt pair who) hdebt
  have hcharge :=
    sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect
      reward pair root hdebt
  have hzero : quittingRootTotalNashDefect reward pair.1 root = 0 :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward pair.1 root).1 hnash
  rw [hzero, add_zero] at hcharge
  unfold quittingTerminalSemanticDebtDrop
  calc
    lowerDebt * quittingRootCollisionMass root ≤
        quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root := hscaled
    _ = quittingRootCollisionMass root *
        quittingTerminalSemanticDebtSum pair := by ring
    _ ≤ ∑ who, quittingRootOpponentAbsorptionMass root who *
        quittingTerminalSemanticDebt pair who := hcollision
    _ ≤ _ := hcharge

/-- A fixed singleton atom owned by `owner` pays every other coordinate's
debt through that coordinate's exact prefix drift. -/
theorem singletonMass_mul_otherDebt_le_debtDrop_of_exact
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota) (root : iota → PMF Bool)
    (owner other : iota) (hne : other ≠ owner)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingRootCoalitionMass root {owner} *
        quittingTerminalSemanticDebt pair other ≤
      quittingTerminalSemanticDebtDrop reward pair root := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hcoordinate :=
    quittingRootCoalitionMass_mul_debt_le_drift_add_nashDefect
      reward pair root {owner} other owner (hdebt other)
        (by simp) hne.symm
  have hzero : quittingRootCoordinateNashDefect reward pair.1 root other = 0 :=
    (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward pair.1 root).1 hnash other
  rw [hzero, add_zero] at hcoordinate
  have hdriftNonneg : ∀ who, 0 ≤
      quittingTerminalSemanticDebt pair who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who := by
    intro who
    exact sub_nonneg.mpr <|
      quittingTerminalSemanticDebt_prefix_le reward pair root who
        (hdebt who) hnash
  have hdriftLe : quittingTerminalSemanticDebt pair other -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) other ≤
      quittingTerminalSemanticDebtDrop reward pair root := by
    unfold quittingTerminalSemanticDebtDrop
      quittingTerminalSemanticDebtSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.single_le_sum (fun who _ ↦ hdriftNonneg who)
      (Finset.mem_univ other)
  exact hcoordinate.trans hdriftLe

/-- The explicit outsider Quit value against a solo owner of rate `p`. -/
def finFourSoloJoinValue
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner blocker : Fin 4) (p : ℝ) : ℝ :=
  (1 - p) * quittingSoloReward reward blocker blocker +
    p * quittingSingletonCollisionReward reward owner blocker

/-- The outsider's Continue payoff when the solo owner absorbs. -/
def finFourSoloOutsideValue
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner blocker : Fin 4) : ℝ :=
  quittingSoloReward reward owner blocker

/-- An outsider's Quit-minus-Continue gain against a scalar solo-owner row. -/
def finFourSoloJoiningGap
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner blocker : Fin 4) (p : ℝ) : ℝ :=
  finFourSoloJoinValue reward owner blocker p -
    finFourSoloOutsideValue reward owner blocker

/-- The unique continuation coordinate making an inactive outsider
indifferent at a genuinely mixed solo-owner root. -/
def finFourSoloBlockerThreshold
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner blocker : Fin 4) (p : ℝ) : ℝ :=
  (finFourSoloJoinValue reward owner blocker p -
      p * finFourSoloOutsideValue reward owner blocker) / (1 - p)

/-- Payoff obtained by changing only the blocker coordinate to its exact
solo-row indifference threshold. -/
def finFourSoloBlockerTail
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (owner blocker : Fin 4) (p : ℝ) :
    Payoff (Fin 4) :=
  Function.update tail blocker
    (finFourSoloBlockerThreshold reward owner blocker p)

/-- A player's endpoint difference depends on the continuation only through
that player's own coordinate. -/
theorem quittingRootEndpointDifference_continuation_congr
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (first second : Payoff iota) (root : iota → PMF Bool) (who : iota)
    (h : first who = second who) :
    quittingRootEndpointDifference reward first root who =
      quittingRootEndpointDifference reward second root who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_continuation_congr
      reward first second _ who h,
    quittingRootExpectedPayoff_continuation_congr
      reward first second _ who h]

/-- Collision mass is continuous in finite product-root simplex coordinates. -/
theorem continuous_quittingRootCollisionMass_simplex
    {iota : Type} [Fintype iota] [DecidableEq iota] :
    Continuous (fun root : QuittingRootSimplex iota ↦
      quittingRootCollisionMass (quittingRootOfSimplex root)) := by
  have hidentity : (fun root : QuittingRootSimplex iota ↦
      quittingRootCollisionMass (quittingRootOfSimplex root)) =
      fun root ↦ quittingRootAbsorptionMass (quittingRootOfSimplex root) -
        ∑ owner, quittingRootCoalitionMass
          (quittingRootOfSimplex root) {owner} := by
    funext root
    rw [QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass]
    ring
  rw [hidentity]
  exact continuous_quittingRootAbsorptionMass_simplex.sub <|
    continuous_finsetSum _ fun owner _ ↦
      continuous_quittingRootCoalitionMass_simplex {owner}

/-- Elementary scalar alternative used by the main sequence theorem.  The
first branch is the filter formulation of a positive lower limit; otherwise
a strict subsequence tends to zero. -/
theorem exists_eventually_pos_or_strictMono_tendsto_zero
    (value : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ value n) :
    (∃ lower, 0 < lower ∧ ∀ᶠ n in atTop, lower ≤ value n) ∨
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto (value ∘ subseq) atTop (nhds 0) := by
  by_cases hmacro : ∃ lower, 0 < lower ∧
      ∀ᶠ n in atTop, lower ≤ value n
  · exact Or.inl hmacro
  · right
    have hfrequent : ∀ rank : ℕ, ∃ᶠ n in atTop,
        value n < (1 : ℝ) / (rank + 1) := by
      intro rank
      by_contra hnot
      rw [not_frequently] at hnot
      have heventual : ∀ᶠ n in atTop,
          (1 : ℝ) / (rank + 1) ≤ value n := by
        filter_upwards [hnot] with n hn
        exact le_of_not_gt hn
      apply hmacro
      exact ⟨(1 : ℝ) / (rank + 1), by positivity, heventual⟩
    obtain ⟨subseq, hsubseq, hbound⟩ :=
      extraction_forall_of_frequently hfrequent
    refine ⟨subseq, hsubseq, ?_⟩
    have hupper : Tendsto (fun rank : ℕ ↦ (1 : ℝ) / (rank + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun rank ↦ hnonneg (subseq rank)
    · exact Filter.Eventually.of_forall fun rank ↦ (hbound rank).le
    · simpa only [Nat.cast_add, Nat.cast_one] using hupper

/-- Data produced at the zero-drop limit.  The source pair is in the carrier;
the updated blocker tail deliberately has no carrier field. -/
structure FinFourChargedSoloBlockerGate
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (minimumDebt charge : ℝ) (owner blocker : Fin 4) where
  source : QuittingTerminalSemanticPair (Fin 4)
  root : Fin 4 → PMF Bool
  hazard : PMF Bool
  owner_ne_blocker : owner ≠ blocker
  source_mem : source ∈ quittingTerminalSemanticCarrier reward
  exact_root : IsεQuittingRootNash reward source.1 0 root
  floor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who
  root_eq_solo : root = quittingSoloStationaryRoot (ι := Fin 4) owner hazard
  charge_le_rate : charge / 8 ≤ (hazard true).toReal
  rate_le : (hazard true).toReal ≤
    1 - witness.terminalGap / (4 * finFourOffMinimumRewardBound reward)
  other_debt : ∀ who, who ≠ owner →
    quittingTerminalSemanticDebt source who = 0
  owner_debt_eq_sum : quittingTerminalSemanticDebt source owner =
    quittingTerminalSemanticDebtSum source
  minimumDebt_le : minimumDebt ≤ quittingTerminalSemanticDebtSum source
  owner_tail_eq_solo : source.1 owner =
    quittingSoloReward reward owner owner
  outside_lt_join : finFourSoloOutsideValue reward owner blocker <
    finFourSoloJoinValue reward owner blocker (hazard true).toReal
  blocker_maximizes_joining_gap : ∀ other, other ≠ owner →
    finFourSoloJoiningGap reward owner other (hazard true).toReal ≤
      finFourSoloJoiningGap reward owner blocker (hazard true).toReal
  floor_le_join : quittingPunishmentValue reward blocker ≤
    finFourSoloJoinValue reward owner blocker (hazard true).toReal
  join_lt_threshold : finFourSoloJoinValue reward owner blocker
      (hazard true).toReal <
    finFourSoloBlockerThreshold reward owner blocker
      (hazard true).toReal
  threshold_le_tail : finFourSoloBlockerThreshold reward owner blocker
      (hazard true).toReal ≤ source.1 blocker
  blocker_tail_exact : IsεQuittingRootNash reward
    (finFourSoloBlockerTail reward source.1 owner blocker
      (hazard true).toReal) 0 root
  blocker_tail_floor : ∀ who, quittingPunishmentValue reward who ≤
    finFourSoloBlockerTail reward source.1 owner blocker
      (hazard true).toReal who
  blocker_tail_box : finFourSoloBlockerTail reward source.1 owner blocker
      (hazard true).toReal ∈
    Set.Icc (fun _ ↦ -finFourOffMinimumRewardBound reward)
      (fun _ ↦ finFourOffMinimumRewardBound reward)
  absorption_eq_rate : quittingRootAbsorptionMass root =
    (hazard true).toReal

/-- Full provenance of a gate extracted from a supplied sequence. -/
structure FinFourChargedSoloBlockerGateLimit
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (pairs : ℕ → QuittingTerminalSemanticPair (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool)
    (minimumDebt charge : ℝ) (owner blocker : Fin 4) where
  minimum : QuittingTerminalSemanticPair (Fin 4)
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_le : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  minimumDebt_eq : minimumDebt = quittingTerminalSemanticDebtSum minimum
  subseq : ℕ → ℕ
  strictMono_subseq : StrictMono subseq
  gate : FinFourChargedSoloBlockerGate reward witness
    minimumDebt charge owner blocker
  source_tendsto : Tendsto (pairs ∘ subseq) atTop (nhds gate.source)
  root_tendsto : Tendsto
    (fun rank ↦ quittingSimplexOfRoot (roots (subseq rank))) atTop
    (nhds (quittingSimplexOfRoot gate.root))
  debtDrop_tendsto : Tendsto (fun rank ↦
    quittingTerminalSemanticDebtDrop reward (pairs (subseq rank))
      (roots (subseq rank))) atTop (nhds 0)

/-- Limit-level blocker construction.  All source and root objects are
supplied literally; the blocker, threshold tail, and exact threshold root
certificate are produced. -/
theorem exists_finFourChargedSoloBlockerGate_of_solo_limit
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (normal : ∀ who, quittingPunishmentValue reward who ≤
      quittingSoloReward reward who who)
    (minimumDebt charge : ℝ) (hcharge : 0 < charge)
    (source : QuittingTerminalSemanticPair (Fin 4))
    (root : Fin 4 → PMF Bool) (owner : Fin 4)
    (hsource : source ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward source.1 0 root)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ source.1 who)
    (hminimum : minimumDebt ≤ quittingTerminalSemanticDebtSum source)
    (hotherRoot : ∀ other, other ≠ owner →
      root other = PMF.pure false)
    (hotherDebt : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt source other = 0)
    (hrate : charge / 8 ≤ (root owner true).toReal) :
    ∃ blocker, ∃ gate : FinFourChargedSoloBlockerGate reward witness
      minimumDebt charge owner blocker,
        gate.source = source ∧ gate.root = root := by
  let hazard := root owner
  let p := (hazard true).toReal
  let M := finFourOffMinimumRewardBound reward
  have hM : 0 < M := finFourOffMinimumRewardBound_pos reward
  have hp : 0 < p := by
    have hdiv : 0 < charge / 8 := by positivity
    exact hdiv.trans_le hrate
  have hp0 : 0 ≤ p := hp.le
  have hroot : root = quittingSoloStationaryRoot owner hazard := by
    exact eq_quittingSoloStationaryRoot_of_others_continue hotherRoot
  have hreward : ∀ terminal who, |reward terminal who| ≤ M :=
    abs_reward_le_finFourOffMinimumRewardBound reward
  have hsourceBox :=
    quittingTerminalSemanticCarrier_mem_box reward source hreward hsource
  have htailBound : ∀ who, |source.1 who| ≤ M := by
    intro who
    exact abs_le.mpr ⟨hsourceBox.1.1 who, hsourceBox.1.2 who⟩
  have hpUpper : p ≤ 1 - witness.terminalGap / (4 * M) := by
    have hcap :=
      exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul
        reward source.1 root owner witness.terminalGap_pos hreward
          htailBound hfloor witness.terminalExploitability hnash
    simpa only [p, hazard] using hcap
  have hgapDiv : 0 < witness.terminalGap / (4 * M) :=
    div_pos witness.terminalGap_pos (mul_pos (by norm_num) hM)
  have hp1 : p < 1 := hpUpper.trans_lt (sub_lt_self 1 hgapDiv)
  have hpLeOne : p ≤ 1 := hp1.le
  have hfalse : (hazard false).toReal = 1 - p := by
    have hmass := quittingSoloHazardMass_add hazard
    dsimp only [p]
    linarith
  have hfalsePos : 0 < (hazard false).toReal := by
    rw [hfalse]
    linarith
  have hnashEndpoint : IsεQuittingRootEndpointNash reward source.1 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward source.1 root).2 hnash
  have hownerTail : source.1 owner = quittingSoloReward reward owner owner := by
    have hlocal := hnashEndpoint owner
    rw [hroot, quittingRootEndpointDifference,
      quittingRootQuitPayoff_soloStationaryRoot_owner,
      quittingRootContinuePayoff_soloStationaryRoot_owner] at hlocal
    have htrue : ((quittingSoloStationaryRoot owner hazard owner) true).toReal = p := by
      simp [p]
    have hfalse' :
        ((quittingSoloStationaryRoot owner hazard owner) false).toReal =
          (hazard false).toReal := by simp
    rw [htrue, hfalse'] at hlocal
    rcases hlocal with ⟨hle, hge⟩
    have hdiffLe : quittingSoloReward reward owner owner -
        source.1 owner ≤ 0 := by
      nlinarith
    have hdiffGe : 0 ≤ quittingSoloReward reward owner owner -
        source.1 owner := by
      nlinarith
    linarith
  have hnotSolo : ¬ IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard) := by
    intro hsolo
    have hstrict :=
      witness.soloReward_lt_punishmentValue_of_soloEndpointNash
        owner hazard hp hsolo
    exact (not_lt_of_ge (normal owner)) hstrict
  have hnotInactive : ¬ ∀ blocker, blocker ≠ owner →
      (hazard false).toReal * quittingSoloReward reward blocker blocker +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner blocker ≤
        quittingSoloReward reward owner blocker := by
    intro hinactive
    exact hnotSolo <|
      isεQuittingRootEndpointNash_soloStationaryRoot
        reward owner hazard hinactive
  push Not at hnotInactive
  obtain ⟨candidate, hcandidateNe, hstrict⟩ := hnotInactive
  have hcandidateGap : 0 < finFourSoloJoiningGap reward owner candidate p := by
    unfold finFourSoloJoiningGap finFourSoloOutsideValue
      finFourSoloJoinValue
    rw [← hfalse]
    exact sub_pos.mpr hstrict
  have houtsiders : (Finset.univ.erase owner).Nonempty :=
    ⟨candidate, Finset.mem_erase.mpr
      ⟨hcandidateNe, Finset.mem_univ candidate⟩⟩
  obtain ⟨blocker, hblockerMem, hmaxEq⟩ := Finset.exists_mem_eq_sup'
    houtsiders (fun other ↦ finFourSoloJoiningGap reward owner other p)
  have hblockerNe : blocker ≠ owner := (Finset.mem_erase.mp hblockerMem).1
  have hmaximal : ∀ other, other ≠ owner →
      finFourSoloJoiningGap reward owner other p ≤
        finFourSoloJoiningGap reward owner blocker p := by
    intro other hother
    calc
      finFourSoloJoiningGap reward owner other p ≤
          (Finset.univ.erase owner).sup' houtsiders
            (fun player ↦ finFourSoloJoiningGap reward owner player p) :=
        Finset.le_sup'
          (fun player ↦ finFourSoloJoiningGap reward owner player p)
          (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
      _ = finFourSoloJoiningGap reward owner blocker p := hmaxEq
  have houtsideJoin : finFourSoloOutsideValue reward owner blocker <
      finFourSoloJoinValue reward owner blocker p := by
    exact sub_pos.mp <| hcandidateGap.trans_le <| hmaximal candidate hcandidateNe
  have hcurrent := (hnashEndpoint blocker).1
  have hblockerContinue : root blocker = PMF.pure false :=
    hotherRoot blocker hblockerNe
  have hcurrentIneq : finFourSoloJoinValue reward owner blocker p ≤
      p * finFourSoloOutsideValue reward owner blocker +
        (1 - p) * source.1 blocker := by
    rw [hblockerContinue] at hcurrent
    norm_num at hcurrent
    rw [hroot, quittingRootEndpointDifference,
      quittingRootQuitPayoff_soloStationaryRoot_other reward hblockerNe,
      quittingRootContinuePayoff_soloStationaryRoot_other reward
        hblockerNe] at hcurrent
    unfold finFourSoloJoinValue finFourSoloOutsideValue
    rw [← hfalse]
    dsimp only [p]
    linarith
  have hfloorJoin : quittingPunishmentValue reward blocker ≤
      finFourSoloJoinValue reward owner blocker p := by
    have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
      reward blocker root
    rw [hroot, quittingStationaryUnilateralCap_solo_other
      reward hblockerNe hazard hp] at hcap
    have hquit : quittingStationaryFixedOpponentsQuitValue reward
        (quittingSoloStationaryRoot owner hazard) blocker =
          finFourSoloJoinValue reward owner blocker p := by
      rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hblockerNe]
      unfold finFourSoloJoinValue
      rw [← hfalse]
    rw [hquit] at hcap
    change quittingPunishmentValue reward blocker ≤
      max (finFourSoloJoinValue reward owner blocker p)
        (finFourSoloOutsideValue reward owner blocker) at hcap
    rw [max_eq_left houtsideJoin.le] at hcap
    exact hcap
  let threshold := finFourSoloBlockerThreshold reward owner blocker p
  have hthresholdEq : (1 - p) * threshold =
      finFourSoloJoinValue reward owner blocker p -
        p * finFourSoloOutsideValue reward owner blocker := by
    dsimp only [threshold]
    unfold finFourSoloBlockerThreshold
    field_simp [ne_of_gt (sub_pos.mpr hp1)]
  have hjoinThreshold : finFourSoloJoinValue reward owner blocker p <
      threshold := by
    have hpositive : 0 < p *
        (finFourSoloJoinValue reward owner blocker p -
          finFourSoloOutsideValue reward owner blocker) :=
      mul_pos hp (sub_pos.mpr houtsideJoin)
    nlinarith
  have hthresholdTail : threshold ≤ source.1 blocker := by
    nlinarith
  have hjoinLower : -M ≤ finFourSoloJoinValue reward owner blocker p := by
    have hsolo := abs_reward_le_finFourOffMinimumRewardBound reward
      (quittingSingletonTerminal blocker) blocker
    have hcollision := abs_reward_le_finFourOffMinimumRewardBound reward
      ⟨{owner, blocker}, Finset.insert_nonempty owner {blocker}⟩ blocker
    change |quittingSoloReward reward blocker blocker| ≤ M at hsolo
    change |quittingSingletonCollisionReward reward owner blocker| ≤ M
      at hcollision
    have hfirst := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hsolo)
      (sub_nonneg.mpr hpLeOne)
    have hsecond := mul_le_mul_of_nonneg_left
      (neg_le_of_abs_le hcollision) hp0
    calc
      -M = (1 - p) * (-M) + p * (-M) := by ring
      _ ≤ (1 - p) * quittingSoloReward reward blocker blocker +
          p * quittingSingletonCollisionReward reward owner blocker :=
        add_le_add hfirst hsecond
      _ = finFourSoloJoinValue reward owner blocker p := rfl
  have hthresholdLower : -M ≤ threshold :=
    hjoinLower.trans hjoinThreshold.le
  let tail := finFourSoloBlockerTail reward source.1 owner blocker p
  have htailExact : IsεQuittingRootNash reward tail 0 root := by
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).1
    intro who
    by_cases hwho : who = blocker
    · subst who
      have hdiff : quittingRootEndpointDifference reward tail root blocker = 0 := by
        rw [hroot, quittingRootEndpointDifference,
          quittingRootQuitPayoff_soloStationaryRoot_other reward hblockerNe,
          quittingRootContinuePayoff_soloStationaryRoot_other reward
            hblockerNe]
        unfold tail finFourSoloBlockerTail
        rw [Function.update_self]
        rw [hfalse]
        change (1 - p) * quittingSoloReward reward blocker blocker +
              p * quittingSingletonCollisionReward reward owner blocker -
            (p * quittingSoloReward reward owner blocker + (1 - p) *
              finFourSoloBlockerThreshold reward owner blocker p) = 0
        dsimp only [threshold] at hthresholdEq
        unfold finFourSoloJoinValue finFourSoloOutsideValue at hthresholdEq
        linarith
      rw [hdiff]
      constructor <;> simp
    · have hlocal := hnashEndpoint who
      have hcoordinate : tail who = source.1 who := by
        simp only [tail, finFourSoloBlockerTail, Function.update_of_ne hwho]
      rw [quittingRootEndpointDifference_continuation_congr
        reward tail source.1 root who hcoordinate]
      exact hlocal
  have htailFloor : ∀ who, quittingPunishmentValue reward who ≤ tail who := by
    intro who
    by_cases hwho : who = blocker
    · subst who
      rw [show tail blocker = threshold by
        simp [tail, finFourSoloBlockerTail, threshold]]
      exact hfloorJoin.trans hjoinThreshold.le
    · simpa only [tail, finFourSoloBlockerTail,
        Function.update_of_ne hwho] using hfloor who
  have htailBox : tail ∈ Set.Icc (fun _ ↦ -M) (fun _ ↦ M) := by
    constructor
    · intro who
      by_cases hwho : who = blocker
      · subst who
        simpa only [tail, finFourSoloBlockerTail, Function.update_self,
          threshold] using hthresholdLower
      · simpa only [tail, finFourSoloBlockerTail,
          Function.update_of_ne hwho] using hsourceBox.1.1 who
    · intro who
      by_cases hwho : who = blocker
      · subst who
        have hle := hthresholdTail.trans (hsourceBox.1.2 blocker)
        simpa only [tail, finFourSoloBlockerTail, Function.update_self,
          threshold] using hle
      · simpa only [tail, finFourSoloBlockerTail,
          Function.update_of_ne hwho] using hsourceBox.1.2 who
  have hownerDebt : quittingTerminalSemanticDebt source owner =
      quittingTerminalSemanticDebtSum source := by
    unfold quittingTerminalSemanticDebtSum
    symm
    apply Finset.sum_eq_single owner
    · intro other _ hne
      exact hotherDebt other hne
    · simp
  have habsorption : quittingRootAbsorptionMass root = p := by
    rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot]
  refine ⟨blocker, {
    source := source
    root := root
    hazard := hazard
    owner_ne_blocker := hblockerNe.symm
    source_mem := hsource
    exact_root := hnash
    floor := hfloor
    root_eq_solo := hroot
    charge_le_rate := hrate
    rate_le := hpUpper
    other_debt := hotherDebt
    owner_debt_eq_sum := hownerDebt
    minimumDebt_le := hminimum
    owner_tail_eq_solo := hownerTail
    outside_lt_join := houtsideJoin
    blocker_maximizes_joining_gap := hmaximal
    floor_le_join := hfloorJoin
    join_lt_threshold := by simpa only [threshold] using hjoinThreshold
    threshold_le_tail := by simpa only [threshold] using hthresholdTail
    blocker_tail_exact := by simpa only [tail] using htailExact
    blocker_tail_floor := by simpa only [tail] using htailFloor
    blocker_tail_box := by simpa only [tail, M] using htailBox
    absorption_eq_rate := by simpa only [p] using habsorption
  }, rfl, rfl⟩

/-- Vanishing semantic-debt drop along a supplied strict subsequence produces
one further strict subsequence and the complete charged blocker gate. -/
theorem exists_finFourChargedSoloBlockerGateLimit_of_debtDrop_tendsto_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (normal : ∀ who, quittingPunishmentValue reward who ≤
      quittingSoloReward reward who who)
    (pairs : ℕ → QuittingTerminalSemanticPair (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool)
    (charge : ℝ) (hcharge : 0 < charge)
    (hpair : ∀ n, pairs n ∈ quittingTerminalSemanticCarrier reward)
    (hnash : ∀ n, IsεQuittingRootNash reward (pairs n).1 0 (roots n))
    (hfloor : ∀ n who,
      quittingPunishmentValue reward who ≤ (pairs n).1 who)
    (habsorption : ∀ n, charge ≤ quittingRootAbsorptionMass (roots n))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum)
    (initialSubseq : ℕ → ℕ) (hinitialSubseq : StrictMono initialSubseq)
    (hdrop : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtDrop reward (pairs (initialSubseq rank))
        (roots (initialSubseq rank))) atTop (nhds 0)) :
    ∃ owner blocker, Nonempty <|
      FinFourChargedSoloBlockerGateLimit reward witness pairs roots
        (quittingTerminalSemanticDebtSum minimum) charge owner blocker := by
  let collision : ℕ → ℝ := fun rank ↦
    quittingRootCollisionMass (roots (initialSubseq rank))
  have hcollisionLe : ∀ rank, collision rank ≤
      quittingTerminalSemanticDebtDrop reward (pairs (initialSubseq rank))
        (roots (initialSubseq rank)) /
          quittingTerminalSemanticDebtSum minimum := by
    intro rank
    apply (le_div_iff₀ hminimumPos).2
    rw [mul_comm]
    exact lowerDebt_mul_collisionMass_le_debtDrop_of_exact
      reward (pairs (initialSubseq rank)) (roots (initialSubseq rank))
        (quittingTerminalSemanticDebtSum minimum)
        (hpair _) (hminimum _ (hpair _)) (hnash _)
  have hcollision : Tendsto collision atTop (nhds 0) := by
    have hupper := hdrop.div_const
      (quittingTerminalSemanticDebtSum minimum)
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun rank ↦
        quittingRootCollisionMass_nonneg _
    · exact Filter.Eventually.of_forall hcollisionLe
    · simpa only [zero_div] using hupper
  let singletonMass : ℕ → Fin 4 → ℝ := fun rank owner ↦
    quittingRootCoalitionMass (roots (initialSubseq rank)) {owner}
  have hsingletonSum : ∀ rank,
      charge - collision rank ≤ ∑ owner, singletonMass rank owner := by
    intro rank
    have hsplit :=
      QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
        (roots (initialSubseq rank))
    dsimp only [collision, singletonMass]
    linarith [habsorption (initialSubseq rank)]
  obtain ⟨owner, _hownerMem, atomSubseq, hatomSubseq, hownerMass⟩ :=
    Math.exists_fixed_mem_subsequence_of_sum_lower_and_error_tendsto_zero
      (Finset.univ : Finset (Fin 4)) singletonMass collision charge
        hcharge hcollision hsingletonSum
  have hownerMassEight : ∀ rank, charge / 8 ≤
      singletonMass (atomSubseq rank) owner := by
    intro rank
    have hbound := hownerMass rank
    norm_num at hbound ⊢
    exact hbound
  let selectedIndex : ℕ → ℕ := fun rank ↦
    initialSubseq (atomSubseq rank)
  let data : ℕ →
      QuittingTerminalSemanticPair (Fin 4) × QuittingRootSimplex (Fin 4) :=
    fun rank ↦ (pairs (selectedIndex rank),
      quittingSimplexOfRoot (roots (selectedIndex rank)))
  have hdataMem : ∀ rank, data rank ∈
      quittingTerminalSemanticCarrier reward ×ˢ
        (Set.univ : Set (QuittingRootSimplex (Fin 4))) := by
    intro rank
    exact ⟨hpair _, Set.mem_univ _⟩
  obtain ⟨limit, hlimitMem, compactSubseq, hcompactSubseq, hdataTendsto⟩ :=
    ((quittingTerminalSemanticCarrier_isCompact reward).prod
      (isCompact_univ : IsCompact
        (Set.univ : Set (QuittingRootSimplex (Fin 4))))).tendsto_subseq
          hdataMem
  let finalSubseq : ℕ → ℕ := fun rank ↦
    selectedIndex (compactSubseq rank)
  have hfinalSubseq : StrictMono finalSubseq :=
    hinitialSubseq.comp (hatomSubseq.comp hcompactSubseq)
  have hsourceTendsto : Tendsto (pairs ∘ finalSubseq) atTop
      (nhds limit.1) := by
    have h := (continuous_fst.tendsto limit).comp hdataTendsto
    simpa [data, finalSubseq, selectedIndex, Function.comp_def] using h
  have hrootTendsto : Tendsto
      (fun rank ↦ quittingSimplexOfRoot (roots (finalSubseq rank))) atTop
      (nhds limit.2) := by
    have h := (continuous_snd.tendsto limit).comp hdataTendsto
    simpa [data, finalSubseq, selectedIndex, Function.comp_def] using h
  have hdropFinal : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtDrop reward (pairs (finalSubseq rank))
        (roots (finalSubseq rank))) atTop (nhds 0) := by
    have hcomp := hdrop.comp
      (hatomSubseq.comp hcompactSubseq).tendsto_atTop
    simpa [finalSubseq, selectedIndex, Function.comp_def] using hcomp
  have hcollisionFinal : Tendsto (fun rank ↦
      quittingRootCollisionMass (roots (finalSubseq rank))) atTop
      (nhds 0) := by
    have hcomp := hcollision.comp
      (hatomSubseq.comp hcompactSubseq).tendsto_atTop
    simpa [collision, finalSubseq, selectedIndex, Function.comp_def] using hcomp
  have hownerMassFinal : ∀ rank, charge / 8 ≤
      quittingRootCoalitionMass (roots (finalSubseq rank)) {owner} := by
    intro rank
    simpa only [singletonMass, finalSubseq, selectedIndex] using
      hownerMassEight (compactSubseq rank)
  let source := limit.1
  let root := quittingRootOfSimplex limit.2
  have hsource : source ∈ quittingTerminalSemanticCarrier reward :=
    hlimitMem.1
  have hcollisionRoot : quittingRootCollisionMass root = 0 := by
    have hrootLimit : Tendsto (fun rank ↦
        quittingRootCollisionMass (roots (finalSubseq rank))) atTop
        (nhds (quittingRootCollisionMass root)) := by
      have hcontinuous : Tendsto
          (fun simplex : QuittingRootSimplex (Fin 4) ↦
            quittingRootCollisionMass (quittingRootOfSimplex simplex))
          (nhds limit.2)
          (nhds (quittingRootCollisionMass (quittingRootOfSimplex limit.2))) :=
        (continuous_quittingRootCollisionMass_simplex
          (iota := Fin 4)).tendsto limit.2
      have hlimit := hcontinuous.comp hrootTendsto
      apply hlimit.congr'
      exact Filter.Eventually.of_forall fun rank ↦ by
        simp only [Function.comp_apply,
          quittingRootOfSimplex_simplexOfRoot]
    exact tendsto_nhds_unique hrootLimit hcollisionFinal
  have hownerMassLimit : charge / 8 ≤
      quittingRootCoalitionMass root {owner} := by
    have hmassLimit : Tendsto (fun rank ↦
        quittingRootCoalitionMass (roots (finalSubseq rank)) {owner}) atTop
        (nhds (quittingRootCoalitionMass root {owner})) := by
      have hcontinuous : Tendsto
          (fun simplex : QuittingRootSimplex (Fin 4) ↦
            quittingRootCoalitionMass (quittingRootOfSimplex simplex) {owner})
          (nhds limit.2)
          (nhds (quittingRootCoalitionMass
            (quittingRootOfSimplex limit.2) {owner})) :=
        (continuous_quittingRootCoalitionMass_simplex {owner}).tendsto limit.2
      have hlimit := hcontinuous.comp hrootTendsto
      apply hlimit.congr'
      exact Filter.Eventually.of_forall fun rank ↦ by
        simp only [Function.comp_apply,
          quittingRootOfSimplex_simplexOfRoot]
    exact ge_of_tendsto' hmassLimit hownerMassFinal
  have hownerQuit : 0 < (root owner true).toReal := by
    have hpositive : 0 < charge / 8 := by positivity
    have hmassQuit := quittingRootCoalitionMass_le_quitProbability_of_mem
      root {owner} owner (by simp)
    exact hpositive.trans_le (hownerMassLimit.trans hmassQuit)
  have hotherRoot : ∀ other, other ≠ owner →
      root other = PMF.pure false := by
    intro other hother
    have hzero : (root other true).toReal = 0 := by
      have hnonneg : 0 ≤ (root other true).toReal := ENNReal.toReal_nonneg
      apply le_antisymm _ hnonneg
      apply le_of_not_gt
      intro hpositive
      have hcollisionPos :=
        quittingRootCollisionMass_pos_of_two_quitProbability_pos
          root hother.symm hownerQuit hpositive
      rw [hcollisionRoot] at hcollisionPos
      exact (lt_irrefl 0) hcollisionPos
    exact Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      _ hzero
  have hnashRoot : IsεQuittingRootNash reward source.1 0 root := by
    have htailTendsto : Tendsto (fun rank ↦ (pairs (finalSubseq rank)).1)
        atTop (nhds source.1) := by
      exact (continuous_fst.tendsto source).comp hsourceTendsto
    have hendpoint : ∀ᶠ rank in atTop,
        IsεQuittingRootEndpointNash reward (pairs (finalSubseq rank)).1 0
          (quittingRootOfSimplex
            (quittingSimplexOfRoot (roots (finalSubseq rank)))) := by
      filter_upwards with rank
      rw [quittingRootOfSimplex_simplexOfRoot]
      exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward _ _).2 (hnash _)
    have hlimitEndpoint := isεQuittingRootEndpointNash_of_tendsto
      reward (fun _ : ℕ ↦ 0) (fun rank ↦ (pairs (finalSubseq rank)).1)
        (fun rank ↦ quittingSimplexOfRoot (roots (finalSubseq rank)))
        tendsto_const_nhds htailTendsto hrootTendsto hendpoint
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward source.1 root).1 hlimitEndpoint
  have hfloorSource : ∀ who,
      quittingPunishmentValue reward who ≤ source.1 who := by
    intro who
    have hcoordinate : Tendsto (fun rank ↦ (pairs (finalSubseq rank)).1 who)
        atTop (nhds (source.1 who)) :=
      ((continuous_apply who).comp continuous_fst).tendsto source |>.comp
        hsourceTendsto
    exact ge_of_tendsto' hcoordinate fun rank ↦ hfloor _ who
  have hotherDebt : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt source other = 0 := by
    intro other hother
    have hdebtTendsto : Tendsto (fun rank ↦
        quittingTerminalSemanticDebt (pairs (finalSubseq rank)) other)
        atTop (nhds (quittingTerminalSemanticDebt source other)) := by
      have hcontinuous : Tendsto
          (fun pair : QuittingTerminalSemanticPair (Fin 4) ↦
            quittingTerminalSemanticDebt pair other) (nhds source)
          (nhds (quittingTerminalSemanticDebt source other)) :=
        (continuous_quittingTerminalSemanticDebt other).tendsto source
      exact hcontinuous.comp hsourceTendsto
    have hpaid : ∀ rank, charge / 8 *
          quittingTerminalSemanticDebt (pairs (finalSubseq rank)) other ≤
        quittingTerminalSemanticDebtDrop reward (pairs (finalSubseq rank))
          (roots (finalSubseq rank)) := by
      intro rank
      have hdebtNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward (hpair (finalSubseq rank)) other
      have hmassScaled := mul_le_mul_of_nonneg_right
        (hownerMassFinal rank) hdebtNonneg
      exact hmassScaled.trans <|
        singletonMass_mul_otherDebt_le_debtDrop_of_exact
          reward (pairs (finalSubseq rank)) (roots (finalSubseq rank))
            owner other hother (hpair _) (hnash _)
    have hlimit := (hdebtTendsto.const_mul (charge / 8)).sub hdropFinal
    have hnonpos : ∀ rank, charge / 8 *
          quittingTerminalSemanticDebt (pairs (finalSubseq rank)) other -
        quittingTerminalSemanticDebtDrop reward (pairs (finalSubseq rank))
          (roots (finalSubseq rank)) ≤ 0 :=
      fun rank ↦ sub_nonpos.mpr (hpaid rank)
    have hle : charge / 8 *
        quittingTerminalSemanticDebt source other ≤ 0 := by
      simpa only [sub_zero] using le_of_tendsto' hlimit hnonpos
    have hdebtNonneg :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hsource other
    have hratePos : 0 < charge / 8 := by positivity
    nlinarith
  have hminimumSource : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum source := hminimum source hsource
  obtain ⟨blocker, gate, hgateSource, hgateRoot⟩ :=
    exists_finFourChargedSoloBlockerGate_of_solo_limit
      reward witness normal (quittingTerminalSemanticDebtSum minimum) charge
        hcharge source root owner hsource hnashRoot hfloorSource
          hminimumSource hotherRoot hotherDebt <| by
            exact hownerMassLimit.trans <|
              quittingRootCoalitionMass_le_quitProbability_of_mem
                root {owner} owner (by simp)
  have hinverse : quittingSimplexOfRoot root = limit.2 := by
    dsimp only [root]
    funext who
    change (stdSimplexEquiv (α := Bool))
      ((stdSimplexEquiv (α := Bool)).symm (limit.2 who)) = limit.2 who
    exact (stdSimplexEquiv (α := Bool)).apply_symm_apply (limit.2 who)
  refine ⟨owner, blocker, ⟨{
    minimum := minimum
    minimum_mem := hminimumMem
    minimum_le := hminimum
    minimum_pos := hminimumPos
    minimumDebt_eq := rfl
    subseq := finalSubseq
    strictMono_subseq := hfinalSubseq
    gate := gate
    source_tendsto := by simpa only [hgateSource] using hsourceTendsto
    root_tendsto := by
      rw [hgateRoot, hinverse]
      exact hrootTendsto
    debtDrop_tendsto := hdropFinal
  }⟩⟩

/-- **Fixed charge off the four-player minimum fiber.**  For any supplied
sequence of actual carrier pairs and exact punishment-floor roots with one
fixed positive absorption charge, either the total semantic-debt drop is
eventually bounded below by one positive constant, or a strict subsequence
produces the complete quantitative normal blocker gate.

The second branch retains the supplied subsequence as provenance.  Its
updated payoff is not promoted to a carrier point. -/
theorem exists_macroscopicDebtDrop_or_chargedSoloBlockerGate
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (pairs : ℕ → QuittingTerminalSemanticPair (Fin 4))
    (roots : ℕ → Fin 4 → PMF Bool)
    (charge : ℝ) (hcharge : 0 < charge)
    (hpair : ∀ n, pairs n ∈ quittingTerminalSemanticCarrier reward)
    (hnash : ∀ n, IsεQuittingRootNash reward (pairs n).1 0 (roots n))
    (hfloor : ∀ n who,
      quittingPunishmentValue reward who ≤ (pairs n).1 who)
    (habsorption : ∀ n,
      charge ≤ quittingRootAbsorptionMass (roots n)) :
    0 < liminf (fun n ↦
      quittingTerminalSemanticDebtDrop reward (pairs n) (roots n)) atTop ∨
    ∃ owner blocker, Nonempty <|
      FinFourChargedSoloBlockerGateLimit reward witness pairs roots
        (quittingTerminalSemanticDebtSum <|
          Classical.choose <|
            exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
              reward witness.not_exists_uniformEquilibriumPayoff)
        charge owner blocker := by
  let drop : ℕ → ℝ := fun n ↦
    quittingTerminalSemanticDebtDrop reward (pairs n) (roots n)
  have hdropNonneg : ∀ n, 0 ≤ drop n := fun n ↦
    quittingTerminalSemanticDebtDrop_nonneg_of_exact
      reward (pairs n) (roots n) (hpair n) (hnash n)
  rcases exists_eventually_pos_or_strictMono_tendsto_zero
      drop hdropNonneg with hmacro | ⟨subseq, hsubseq, hdrop⟩
  · obtain ⟨lower, hlowerPos, hlower⟩ := hmacro
    left
    change 0 < liminf drop atTop
    have hdropUpper : ∀ n,
        drop n ≤ 8 * finFourOffMinimumRewardBound reward := fun n ↦
      quittingTerminalSemanticDebtDrop_le_eight_mul_rewardBound
        reward (pairs n) (roots n) (hpair n)
    have hdropEventuallyUpper : ∀ᶠ n in atTop,
        drop n ≤ 8 * finFourOffMinimumRewardBound reward :=
      Filter.Eventually.of_forall hdropUpper
    exact hlowerPos.trans_le <| le_liminf_of_le
      (isCoboundedUnder_ge_of_eventually_le atTop hdropEventuallyUpper)
      hlower
  · right
    let minimumData :=
      exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
        reward witness.not_exists_uniformEquilibriumPayoff
    let minimum := Classical.choose minimumData
    have hminimumSpec := Classical.choose_spec minimumData
    obtain ⟨hminimumMem, hminimum, hminimumPos, _hnashMinimum,
      _hfixedMinimum, hnormalMinimum⟩ := hminimumSpec
    have normal : ∀ who, quittingPunishmentValue reward who ≤
        quittingSoloReward reward who who := fun who ↦
      (hnormalMinimum who).1
    have hdrop' : Tendsto (fun rank ↦
        quittingTerminalSemanticDebtDrop reward (pairs (subseq rank))
          (roots (subseq rank))) atTop (nhds 0) := by
      change Tendsto (drop ∘ subseq) atTop (nhds 0)
      exact hdrop
    simpa only [minimumData, minimum] using
      exists_finFourChargedSoloBlockerGateLimit_of_debtDrop_tendsto_zero
        reward witness normal pairs roots charge hcharge hpair hnash hfloor
          habsorption minimum hminimumMem hminimum hminimumPos
            subseq hsubseq hdrop'

end GameTheory
