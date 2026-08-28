/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Topology.CompactFinitePrefixRelation
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.LeaveJoinStationaryTwoDebtorHandoff
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourStrictMinimumPlateauIsolation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonTightMinimumFaceIteration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward
import UniformEquilibrium.Quitting.Boundary.Repair.PunishmentNormalAtomicCollision

/-!
# Four-player solo-wall dispatch

This file isolates the source-native pieces of the reviewed solo-wall
argument.  At one fixed carrier source, compactness of the exact-root set
gives a positive opponent-absorption floor unless an exact root lies on the
owner's solo face.  Any root above that floor gives a literal carrier prefix
whose total semantic debt decreases by a fixed positive amount when the
source has one debtor.

The scalar restart lemma records the other branch: a solo root selected at a
strict blocker wall has a strictly larger owner hazard unless the selected
pair row already has positive premium.  The inverse-limit layer below turns
arbitrarily long outward solo-prefix words into a correctly oriented semantic
spine.  It does not assume that the outward word itself has behavioral-spine
orientation.

The final game-facing adapter from the off-minimum gate remains separate.  In
particular, the gate must select a blocker attaining the uniform maximum at
each restarted hazard; mere positivity of an arbitrary blocker is not that
adapter.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.Topology Set
open QuittingSureSetOwnerRepair
open scoped Topology

/-- Exact simplex roots against one prescribed four-player continuation. -/
def finFourExactRootSet
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) : Set (QuittingRootSimplex (Fin 4)) :=
  {simplex | IsεQuittingRootEndpointNash reward tail 0
    (quittingRootOfSimplex simplex)}

theorem finFourExactRootSet_nonempty
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) :
    (finFourExactRootSet reward tail).Nonempty := by
  obtain ⟨simplex, hnash⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward tail
  exact ⟨simplex, hnash⟩

theorem finFourExactRootSet_isCompact
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) :
    IsCompact (finFourExactRootSet reward tail) := by
  have hcontinuous : Continuous
      (fun simplex : QuittingRootSimplex (Fin 4) ↦
        (tail, simplex)) :=
    continuous_const.prodMk continuous_id
  exact ((isClosed_isZeroQuittingRootEndpointNash_simplex reward).preimage
    hcontinuous).isCompact

/-- If no exact root lies on the owner's solo face, compactness separates all
exact roots from that face by a source-specific positive opponent hazard. -/
theorem exists_pos_exactRootOpponentAbsorptionFloor_of_no_soloExactRoot
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (owner : Fin 4)
    (hnoSolo : ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        ¬ ∀ other, other ≠ owner → root other = PMF.pure false) :
    ∃ omega, 0 < omega ∧ ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        omega ≤ quittingRootOpponentAbsorptionMass root owner := by
  let exactSet := finFourExactRootSet reward tail
  let absorption : QuittingRootSimplex (Fin 4) → ℝ := fun simplex ↦
    quittingRootOpponentAbsorptionMass
      (quittingRootOfSimplex simplex) owner
  obtain ⟨selected, hselected, hminimum⟩ :=
    (finFourExactRootSet_isCompact reward tail).exists_isMinOn
      (finFourExactRootSet_nonempty reward tail)
      (continuous_quittingRootOpponentAbsorptionMass_simplex owner).continuousOn
  have hselectedPos : 0 < absorption selected := by
    have hnonneg := quittingRootOpponentAbsorptionMass_nonneg
      (quittingRootOfSimplex selected) owner
    apply lt_of_le_of_ne hnonneg
    intro hzero
    have habsorption : quittingRootOpponentAbsorptionMass
        (quittingRootOfSimplex selected) owner = 0 := by
      exact hzero.symm
    have hcontinue : quittingRootOpponentContinueMass
        (quittingRootOfSimplex selected) owner = 1 := by
      rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass,
        habsorption]
      norm_num
    have hpure :=
      quittingRoot_opponents_pureContinue_of_opponentContinueMass_eq_one
        (quittingRootOfSimplex selected) owner hcontinue
    have hnash : IsεQuittingRootNash reward tail 0
        (quittingRootOfSimplex selected) :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward tail (quittingRootOfSimplex selected)).mp hselected
    exact hnoSolo (quittingRootOfSimplex selected) hnash hpure
  refine ⟨absorption selected, hselectedPos, ?_⟩
  intro root hnash
  have hmem : quittingSimplexOfRoot root ∈ exactSet := by
    dsimp only [exactSet, finFourExactRootSet]
    change IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex (quittingSimplexOfRoot root))
    rw [quittingRootOfSimplex_simplexOfRoot]
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  have hle := hminimum hmem
  simpa only [Set.mem_setOf_eq, absorption,
    quittingRootOfSimplex_simplexOfRoot] using hle

/-- A unique-debtor exact carrier prefix contracts total semantic debt by the
owner's opponent-absorption hazard.  This is a literal terminal-semantic
prefix, not a stationary-regret proxy. -/
theorem quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (owner : iota)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root)
    (hother : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt pair other = 0) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) ≤
      (1 - quittingRootOpponentAbsorptionMass root owner) *
        quittingTerminalSemanticDebtSum pair := by
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hprefixOther : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) other = 0 := by
    intro other hne
    have hle := quittingTerminalSemanticDebt_prefix_le
      reward pair root other (hdebt other) hnash
    have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward (quittingTerminalSemanticPrefix_mem_carrier
        reward root pair hpair) other
    exact le_antisymm (by simpa [hother other hne] using hle) hnonneg
  have hsum : quittingTerminalSemanticDebtSum pair =
      quittingTerminalSemanticDebt pair owner := by
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.sum_eq_single owner]
    · intro other _ hne
      exact hother other hne
    · simp
  have hprefixSum : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root pair) =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) owner := by
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.sum_eq_single owner]
    · intro other _ hne
      exact hprefixOther other hne
    · simp
  have howner := quittingTerminalSemanticDebt_prefix_eq_blockAct
    reward pair root owner (hdebt owner) hnash
  have hcontract :=
    Math.SurvivalWeightedObstruction.Block.act_le_survival_mul_debt
      (quittingTerminalSemanticDebtBlock reward pair root owner) ()
      (hdebt owner)
  calc
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) owner := hprefixSum
    _ = (quittingTerminalSemanticDebtBlock reward pair root owner).act ()
          (quittingTerminalSemanticDebt pair owner) := howner
    _ ≤ (quittingTerminalSemanticDebtBlock reward pair root owner).survival *
          quittingTerminalSemanticDebt pair owner := hcontract
    _ = (1 - quittingRootOpponentAbsorptionMass root owner) *
          quittingTerminalSemanticDebtSum pair := by
      rw [hsum]
      exact congrArg (fun value ↦
        value * quittingTerminalSemanticDebt pair owner)
        (quittingRootOpponentContinueMass_eq_one_sub_absorptionMass
          root owner)

/-- Source-specific debt-descent arm.  The prefixed pair remains in the same
carrier and its total debt drops by at least `omega * debt`. -/
theorem exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pair : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (omega : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hdebt : 0 < quittingTerminalSemanticDebtSum pair)
    (hother : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt pair other = 0)
    (homega : 0 < omega)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤ pair.1 who)
    (hroot : ∀ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward pair.1 0 root →
        omega ≤ quittingRootOpponentAbsorptionMass root owner) :
    ∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward pair.1 0 root ∧
      quittingTerminalSemanticPrefix reward root pair ∈
        quittingTerminalSemanticCarrier reward ∧
      (∀ who, quittingPunishmentValue reward who ≤
        (quittingTerminalSemanticPrefix reward root pair).1 who) ∧
      omega ≤ quittingRootAbsorptionMass root ∧
      0 < omega * quittingTerminalSemanticDebtSum pair ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) ≤
        quittingTerminalSemanticDebtSum pair -
          omega * quittingTerminalSemanticDebtSum pair := by
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash
    (reward := reward) pair.1
  have hopponent := hroot root hnash
  have habsorption : omega ≤ quittingRootAbsorptionMass root :=
    hopponent.trans (quittingRootOpponentAbsorptionMass_le_absorptionMass
      root owner)
  have hprefixFloor : ∀ who, quittingPunishmentValue reward who ≤
      (quittingTerminalSemanticPrefix reward root pair).1 who := by
    intro who
    exact quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
      reward pair.1 root who (hfloor who) hnash
  refine ⟨root, hnash,
    quittingTerminalSemanticPrefix_mem_carrier reward root pair hpair,
    hprefixFloor, habsorption, mul_pos homega hdebt, ?_⟩
  have hcontract :=
    quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul
      reward pair root owner hpair hnash hother
  have hscaled := mul_le_mul_of_nonneg_right hopponent hdebt.le
  calc
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) ≤
        (1 - quittingRootOpponentAbsorptionMass root owner) *
          quittingTerminalSemanticDebtSum pair := hcontract
    _ ≤ (1 - omega) * quittingTerminalSemanticDebtSum pair := by
      nlinarith
    _ = quittingTerminalSemanticDebtSum pair -
          omega * quittingTerminalSemanticDebtSum pair := by ring

/-- The scalar wall calculation.  If one inactive blocker strictly prefers
Quit at the incoming solo rate but weakly prefers Continue at another exact
solo rate, then either the pair row has positive premium or the new hazard is
strictly larger.  The strict upper bound excludes the `premium = 0`, sure-Quit
endpoint. -/
theorem soloWall_pairPremium_pos_or_rate_strictMono
    {singletonTail pairPremium incomingTail x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy1 : y < 1)
    (hwall : 0 < (1 - x) * (singletonTail - incomingTail) +
      x * pairPremium)
    (hexact : (1 - y) * (singletonTail - incomingTail) +
      y * pairPremium ≤ 0) :
    0 < pairPremium ∨ x < y := by
  by_cases hpremium : 0 < pairPremium
  · exact Or.inl hpremium
  · right
    have hc : pairPremium ≤ 0 := le_of_not_gt hpremium
    have ha : 0 < singletonTail - incomingTail := by
      by_contra hnot
      have haNonpos : singletonTail - incomingTail ≤ 0 := le_of_not_gt hnot
      nlinarith
    have hcStrict : pairPremium < 0 := by
      apply lt_of_le_of_ne hc
      intro hzero
      rw [hzero, mul_zero, add_zero] at hexact
      have hyPos : 0 < 1 - y := sub_pos.mpr hy1
      nlinarith
    by_contra hxy
    have hyx : y ≤ x := le_of_not_gt hxy
    nlinarith

/-! ## Exact solo-prefix preservation at one source -/

/-- An exact solo prefix preserves every semantic-debt coordinate when the
owner is singleton-tight and all outsiders have zero debt.  No global
minimum-fiber hypothesis is needed. -/
theorem quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (owner : iota) (hazard : PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner hazard))
    (htight : pair.1 owner = quittingSoloReward reward owner owner)
    (hother : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt pair other = 0) :
    ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward
            (quittingSoloStationaryRoot owner hazard) pair) who =
        quittingTerminalSemanticDebt pair who := by
  intro who
  have hdebt : ∀ player, 0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  by_cases hwho : who = owner
  · subst who
    have hpure : ∀ other, other ≠ owner →
        quittingSoloStationaryRoot owner hazard other = PMF.pure false := by
      intro other hne
      simp [quittingSoloStationaryRoot, hne]
    have hsurvival : quittingRootOpponentContinueMass
        (quittingSoloStationaryRoot owner hazard) owner = 1 :=
      quittingRootOpponentContinueMass_eq_one_of_others_pureContinue
        (quittingSoloStationaryRoot owner hazard) owner hpure
    have hpremium : quittingRootExercisePremium reward pair.1
        (quittingSoloStationaryRoot owner hazard) owner = 0 := by
      unfold quittingRootExercisePremium quittingRootEndpointDifference
      rw [quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner, htight]
      simp
    rw [quittingTerminalSemanticDebt_prefix_eq_blockAct
      reward pair (quittingSoloStationaryRoot owner hazard) owner
        (hdebt owner) hnash]
    simp [quittingTerminalSemanticDebtBlock,
      Math.SurvivalWeightedObstruction.Block.act, hsurvival, hpremium,
      hdebt owner]
  · have hle := quittingTerminalSemanticDebt_prefix_le
      reward pair (quittingSoloStationaryRoot owner hazard) who
        (hdebt who) hnash
    have hprefixNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward (quittingTerminalSemanticPrefix_mem_carrier reward
        (quittingSoloStationaryRoot owner hazard) pair hpair) who
    exact le_antisymm (by simpa [hother who hwho] using hle)
      (by simpa [hother who hwho] using hprefixNonneg)

/-- The exact solo prefix therefore preserves total semantic debt. -/
theorem quittingTerminalSemanticDebtSum_prefix_solo_eq_of_uniqueDebtor
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (owner : iota) (hazard : PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner hazard))
    (htight : pair.1 owner = quittingSoloReward reward owner owner)
    (hother : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt pair other = 0) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner hazard) pair) =
      quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  apply Finset.sum_congr rfl
  intro who _
  exact quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor
    reward pair owner hazard hpair hnash htight hother who

/-- Reusing one positive solo root must reach a first literal carrier tail at
which an outsider strictly wants to Quit, provided that some outsider has a
strict limiting endpoint gain at the owner's singleton vector. -/
theorem exists_first_soloPrefix_outsiderWall
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pair : QuittingTerminalSemanticPair (Fin 4))
    (owner blocker : Fin 4) (hblocker : blocker ≠ owner)
    (rate : ℝ) (hrate0 : 0 < rate) (hrate1 : rate < 1)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (htight : pair.1 owner = quittingSoloReward reward owner owner)
    (hnash0 : IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner
        (quittingHazardCoin rate hrate0.le hrate1.le)))
    (hlimitingGain : 0 < quittingRootEndpointDifference reward
      (quittingSoloReward reward owner)
      (quittingSoloStationaryRoot owner
        (quittingHazardCoin rate hrate0.le hrate1.le)) blocker) :
    let root := quittingSoloStationaryRoot owner
      (quittingHazardCoin rate hrate0.le hrate1.le)
    let step := quittingTerminalSemanticPrefix reward root
    ∃ wall : ℕ,
      0 < wall ∧
      (∀ time, time < wall →
        IsεQuittingRootNash reward ((step^[time]) pair).1 0 root) ∧
      ((step^[wall]) pair) ∈ quittingTerminalSemanticCarrier reward ∧
      ((step^[wall]) pair).1 owner =
        quittingSoloReward reward owner owner ∧
      ∃ outsider, outsider ≠ owner ∧
        0 < quittingRootEndpointDifference reward
          ((step^[wall]) pair).1 root outsider := by
  classical
  let root := quittingSoloStationaryRoot owner
    (quittingHazardCoin rate hrate0.le hrate1.le)
  let step := quittingTerminalSemanticPrefix reward root
  have htailTendsto : Tendsto (fun time ↦ ((step^[time]) pair).1)
      atTop (nhds (quittingSoloReward reward owner)) := by
    exact tendsto_quittingSoloPrefix_iterate_prescribed
      (reward := reward) pair owner hrate0 hrate1.le
  let simplex := quittingSimplexOfRoot root
  have hdiffContinuous : Continuous (fun tail : Payoff (Fin 4) ↦
      quittingRootEndpointDifference reward tail root blocker) := by
    have hmap : Continuous (fun tail : Payoff (Fin 4) ↦
        (tail, simplex)) := continuous_id.prodMk continuous_const
    have hcontinuous :=
      (continuous_quittingRootEndpointDifference_simplex reward blocker).comp
        hmap
    have heq : (fun tail : Payoff (Fin 4) ↦
        quittingRootEndpointDifference reward tail root blocker) =
        fun tail ↦ quittingRootEndpointDifference reward tail
          (quittingRootOfSimplex simplex) blocker := by
      funext tail
      simp [simplex]
    rw [heq]
    exact hcontinuous
  have hdiffTendsto : Tendsto (fun time ↦
      quittingRootEndpointDifference reward ((step^[time]) pair).1
        root blocker) atTop
      (nhds (quittingRootEndpointDifference reward
        (quittingSoloReward reward owner) root blocker)) :=
    hdiffContinuous.continuousAt.tendsto.comp htailTendsto
  have hexistsFailure : ∃ time,
      ¬ IsεQuittingRootNash reward ((step^[time]) pair).1 0 root := by
    by_contra hnot
    push Not at hnot
    have hnonpos : ∀ time, quittingRootEndpointDifference reward
        ((step^[time]) pair).1 root blocker ≤ 0 := by
      intro time
      have hlocal :=
        (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward ((step^[time]) pair).1 root).mpr (hnot time) blocker
      have hcontinue : (root blocker false).toReal = 1 := by
        simp [root, quittingSoloStationaryRoot, hblocker]
      nlinarith [hlocal.1]
    have hlimitNonpos := le_of_tendsto' hdiffTendsto hnonpos
    exact (not_lt_of_ge hlimitNonpos) hlimitingGain
  let wall := Nat.find hexistsFailure
  have hwallFailure :
      ¬ IsεQuittingRootNash reward ((step^[wall]) pair).1 0 root :=
    Nat.find_spec hexistsFailure
  have hwallPos : 0 < wall := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hwallFailure
    simpa only [hzero, Function.iterate_zero_apply] using hnash0
  have hbefore : ∀ time, time < wall →
      IsεQuittingRootNash reward ((step^[time]) pair).1 0 root := by
    intro time htime
    by_contra hfailure
    exact (Nat.find_min hexistsFailure htime) hfailure
  have hcarrier : ∀ time, ((step^[time]) pair) ∈
      quittingTerminalSemanticCarrier reward := by
    intro time
    induction time with
    | zero => exact hpair
    | succ time ih =>
        rw [Function.iterate_succ_apply']
        exact quittingTerminalSemanticPrefix_mem_carrier
          reward root _ ih
  have htightIterate : ∀ time, ((step^[time]) pair).1 owner =
      quittingSoloReward reward owner owner := by
    intro time
    rw [quittingSoloPrefix_iterate_prescribed_apply
      (reward := reward) pair owner owner hrate0.le hrate1.le]
    rw [htight, sub_self, mul_zero, add_zero]
  have houtside : ∃ outsider, outsider ≠ owner ∧
      0 < quittingRootEndpointDifference reward
        ((step^[wall]) pair).1 root outsider := by
    by_contra hnot
    push Not at hnot
    apply hwallFailure
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward ((step^[wall]) pair).1 root).mp
    intro who
    by_cases hwho : who = owner
    · subst who
      have hdiff : quittingRootEndpointDifference reward
          ((step^[wall]) pair).1 root owner = 0 := by
        rw [quittingRootEndpointDifference,
          quittingRootQuitPayoff_soloStationaryRoot_owner,
          quittingRootContinuePayoff_soloStationaryRoot_owner,
          htightIterate wall]
        ring
      rw [hdiff]
      constructor <;> simp
    · have hdiff : quittingRootEndpointDifference reward
          ((step^[wall]) pair).1 root who ≤ 0 := hnot who hwho
      have hcontinue : (root who false).toReal = 1 := by
        simp [root, quittingSoloStationaryRoot, hwho]
      have hquit : (root who true).toReal = 0 := by
        simp [root, quittingSoloStationaryRoot, hwho]
      constructor
      · simpa only [hcontinue, one_mul] using hdiff
      · rw [hquit, zero_mul]
        norm_num
  exact ⟨wall, hwallPos, hbefore, hcarrier wall,
    htightIterate wall, houtside⟩

/-- Every debt coordinate is unchanged through any finite initial segment on
which the reused solo row remains exact. -/
theorem quittingSoloPrefix_iterate_debt_eq_of_exact_before
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pair : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (rate : ℝ)
    (hrate0 : 0 < rate) (hrate1 : rate < 1)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (htight : pair.1 owner = quittingSoloReward reward owner owner)
    (hother : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt pair other = 0)
    (steps : ℕ)
    (hexact : ∀ time, time < steps →
      IsεQuittingRootNash reward
        (((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0.le hrate1.le)))^[time] pair).1)
        0 (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate0.le hrate1.le))) :
    ∀ who,
      quittingTerminalSemanticDebt
          ((quittingTerminalSemanticPrefix reward
            (quittingSoloStationaryRoot owner
              (quittingHazardCoin rate hrate0.le hrate1.le)))^[steps] pair) who =
        quittingTerminalSemanticDebt pair who := by
  let hazard := quittingHazardCoin rate hrate0.le hrate1.le
  let root := quittingSoloStationaryRoot owner hazard
  let step := quittingTerminalSemanticPrefix reward root
  have hcarrier : ∀ time, (step^[time]) pair ∈
      quittingTerminalSemanticCarrier reward := by
    intro time
    induction time with
    | zero => exact hpair
    | succ time ih =>
        rw [Function.iterate_succ_apply']
        exact quittingTerminalSemanticPrefix_mem_carrier reward root _ ih
  have htightIterate : ∀ time, ((step^[time]) pair).1 owner =
      quittingSoloReward reward owner owner := by
    intro time
    rw [quittingSoloPrefix_iterate_prescribed_apply
      (reward := reward) pair owner owner hrate0.le hrate1.le]
    rw [htight, sub_self, mul_zero, add_zero]
  change ∀ who, quittingTerminalSemanticDebt ((step^[steps]) pair) who =
    quittingTerminalSemanticDebt pair who
  induction steps with
  | zero => simp
  | succ steps ih =>
      intro who
      have hexactPrevious : ∀ time, time < steps →
          IsεQuittingRootNash reward ((step^[time]) pair).1 0 root := by
        intro time htime
        simpa only [step, root, hazard] using
          hexact time (htime.trans (Nat.lt_succ_self steps))
      have ih' : ∀ player,
          quittingTerminalSemanticDebt ((step^[steps]) pair) player =
            quittingTerminalSemanticDebt pair player :=
        ih hexactPrevious
      have hnash : IsεQuittingRootNash reward ((step^[steps]) pair).1 0 root := by
        simpa only [step, root, hazard] using hexact steps (Nat.lt_succ_self steps)
      have hotherCurrent : ∀ other, other ≠ owner →
          quittingTerminalSemanticDebt ((step^[steps]) pair) other = 0 := by
        intro other hne
        rw [ih' other, hother other hne]
      rw [Function.iterate_succ_apply']
      exact (quittingTerminalSemanticDebt_prefix_solo_eq_of_uniqueDebtor
        reward ((step^[steps]) pair) owner hazard (hcarrier steps) hnash
          (htightIterate steps) hotherCurrent who).trans (ih' who)

/-- Hence the total debt at the first reached wall is exactly the source
debt, provided the source starts with one debtor. -/
theorem quittingSoloPrefix_iterate_debtSum_eq_of_exact_before
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pair : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (rate : ℝ)
    (hrate0 : 0 < rate) (hrate1 : rate < 1)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (htight : pair.1 owner = quittingSoloReward reward owner owner)
    (hother : ∀ other, other ≠ owner →
      quittingTerminalSemanticDebt pair other = 0)
    (steps : ℕ)
    (hexact : ∀ time, time < steps →
      IsεQuittingRootNash reward
        (((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0.le hrate1.le)))^[time] pair).1)
        0 (quittingSoloStationaryRoot owner
          (quittingHazardCoin rate hrate0.le hrate1.le))) :
    quittingTerminalSemanticDebtSum
        ((quittingTerminalSemanticPrefix reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0.le hrate1.le)))^[steps] pair) =
      quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  apply Finset.sum_congr rfl
  intro who _
  exact quittingSoloPrefix_iterate_debt_eq_of_exact_before reward pair owner
    rate hrate0 hrate1 hpair htight hother steps hexact who

/-! ## Positive pair premium and the checked stationary handoff -/

private theorem exists_finFour_label_outside_three
    (first second third : Fin 4)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    ∃ fourth, fourth ∉ ({first, second, third} : Finset (Fin 4)) := by
  have hcard : ({first, second, third} : Finset (Fin 4)).card <
      (Finset.univ : Finset (Fin 4)).card := by
    simp [hfirstSecond, hfirstThird, hsecondThird]
  obtain ⟨fourth, _, hfourth⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨fourth, hfourth⟩

/-- A positive premium at the pair `{owner, blocker}` consumes the terminal
toggle.  Either a genuinely third player joins that pair with the full gap,
or punishment normality supplies the complementary singleton join and the
already checked leave--join stationary two-debtor handoff. -/
theorem pairPremium_pairJoin_or_leaveJoinStationaryTwoDebtorHandoff
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (M : ℝ)
    (hbound : ∀ terminal who, |reward terminal who| ≤ M)
    (owner blocker : Fin 4) (hne : owner ≠ blocker)
    (hnormal : IsQuittingNormalPlayer reward blocker)
    (hpremium : quittingSetReward reward {owner} blocker <
      quittingSetReward reward {owner, blocker} blocker) :
    (∃ joiner ∉ ({owner, blocker} : Finset (Fin 4)),
      quittingSetReward reward {owner, blocker} joiner +
          witness.terminalGap ≤
        quittingSetReward reward
          (insert joiner {owner, blocker}) joiner) ∨
      ∃ joiner fourth,
        Nonempty (FinFourLeaveJoinStationaryTwoDebtorHandoff reward
          witness M owner blocker joiner fourth) := by
  rcases witness.exists_leave_or_join_gain
      ({owner, blocker} : Finset (Fin 4)) with hleave | hjoin
  · obtain ⟨member, hmember, hleaveGain⟩ := hleave
    have hmemberCases : member = owner ∨ member = blocker := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmember
    have hmemberOwner : member = owner := by
      rcases hmemberCases with howner | hblocker
      · exact howner
      · subst member
        have herase : ({owner, blocker} : Finset (Fin 4)).erase blocker =
            {owner} := by
          ext who
          simp only [Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton]
          aesop
        rw [herase] at hleaveGain
        exfalso
        linarith [witness.terminalGap_pos]
    subst member
    have herase : ({owner, blocker} : Finset (Fin 4)).erase owner =
        {blocker} := by
      ext who
      simp only [Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton]
      aesop
    rw [herase] at hleaveGain
    obtain ⟨joiner, hjoinerBlocker, hjoinerGain⟩ :=
      witness.exists_atomicCollision_gain_of_normal blocker hnormal
    have hjoinerOwner : joiner ≠ owner := by
      intro heq
      subst joiner
      have hjoinerGain' : quittingSetReward reward {blocker} owner +
          witness.terminalGap ≤
            quittingSetReward reward {owner, blocker} owner := by
        simpa only [quittingSetReward_singleton_eq_soloReward,
          quittingSetReward_pair_left] using hjoinerGain
      linarith [witness.terminalGap_pos]
    obtain ⟨fourth, hfourth⟩ := exists_finFour_label_outside_three
      owner blocker joiner hne hjoinerOwner.symm hjoinerBlocker.symm
    have hfourthNe : fourth ≠ owner ∧ fourth ≠ blocker ∧
        fourth ≠ joiner := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hfourth
    right
    refine ⟨joiner, fourth, ?_⟩
    apply nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff
      witness M hbound owner blocker joiner fourth
    · exact hne
    · exact hjoinerOwner.symm
    · exact hfourthNe.1.symm
    · exact hjoinerBlocker.symm
    · exact hfourthNe.2.1.symm
    · exact hfourthNe.2.2.symm
    · exact hleaveGain
    · simpa only [quittingSetReward_singleton_eq_soloReward,
        quittingSetReward_pair_right] using hjoinerGain
  · exact Or.inl hjoin

/-! ## The pair-base stationary compiler -/

/-- At an induced Nash point over any nonempty persistent base, every free
coordinate realizes its unrestricted stationary cap and lies above its
punishment value.  The existing singleton-base theorem has an additional
owner conclusion; this is its base-size-independent free-coordinate core. -/
theorem persistentBase_inducedNash_free_semantics
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (base free : Finset (Fin 4)) (hbase : base.Nonempty)
    (hdisjoint : Disjoint base free)
    (point : mixedPolytope (quittingBinaryForm free).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward base free) :
    ∀ who ∈ free,
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (quittingPersistentBaseRoot base free point)) who =
        quittingStationaryUnilateralCap reward
          (quittingPersistentBaseRoot base free point) who ∧
      quittingPunishmentValue reward who ≤
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (quittingPersistentBaseRoot base free point)) who := by
  intro who hwho
  let root := quittingPersistentBaseRoot base free point
  let profile := quittingStationaryProfile reward root
  let quitter := Classical.choose hbase
  have hquitter : quitter ∈ base := Classical.choose_spec hbase
  have hquitterRoot : root quitter = PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base
      base free point hquitter
  have hcontinueMass : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hquitterRoot
  have hne : who ≠ quitter := by
    intro heq
    subst who
    exact Finset.disjoint_left.mp hdisjoint hquitter hwho
  have hopponentMass :
      quittingStationaryFixedOpponentsContinueMass root who = 0 :=
    quittingStationaryContinueMass_update_of_sureQuitter
      hne hquitterRoot (PMF.pure false)
  have hpure := quittingPersistentBaseRoot_free_purePayoff_le
    reward base free hbase hdisjoint point hpoint who hwho
  have htarget : quittingTerminalPayoff reward profile who =
      quittingRootAbsorbingContribution reward root who := by
    rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
    · rw [hcontinueMass]
      norm_num
    · rw [hcontinueMass]
      norm_num
  have hsuccessor : quittingRootSuccessorPayoff reward 0 root who =
      quittingRootAbsorbingContribution reward root who := by
    unfold quittingRootSuccessorPayoff
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      hcontinueMass]
    simp
  have hquit : quittingStationaryFixedOpponentsQuitValue reward root who ≤
      quittingTerminalPayoff reward profile who := by
    have hquitEq : quittingRootQuitPayoff reward 0 root who =
        quittingStationaryFixedOpponentsQuitValue reward root who := by
      simpa [quittingStationaryFixedOpponentsQuitValue] using
        (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward (fun _ ↦ root) who 0 0)
    calc
      quittingStationaryFixedOpponentsQuitValue reward root who =
          quittingRootQuitPayoff reward 0 root who := hquitEq.symm
      _ ≤ quittingRootSuccessorPayoff reward 0 root who := hpure.1
      _ = quittingRootAbsorbingContribution reward root who := hsuccessor
      _ = quittingTerminalPayoff reward profile who := htarget.symm
  have hcontinue :
      quittingStationaryFixedOpponentsContinueReward reward root who ≤
        quittingTerminalPayoff reward profile who := by
    have hcontinueEq : quittingRootContinuePayoff reward 0 root who =
        quittingStationaryFixedOpponentsContinueReward reward root who := by
      have hraw := quittingRootContinuePayoff_eq_fixedOpponents
        reward (fun _ ↦ root) who 0 0
      simpa [quittingStationaryFixedOpponentsContinueReward] using hraw
    calc
      quittingStationaryFixedOpponentsContinueReward reward root who =
          quittingRootContinuePayoff reward 0 root who := hcontinueEq.symm
      _ ≤ quittingRootSuccessorPayoff reward 0 root who := hpure.2
      _ = quittingRootAbsorbingContribution reward root who := hsuccessor
      _ = quittingTerminalPayoff reward profile who := htarget.symm
  have hcapUpper : quittingStationaryUnilateralCap reward root who ≤
      quittingTerminalPayoff reward profile who := by
    rw [quittingStationaryUnilateralCap_eq_max_div, hopponentMass]
    norm_num
    exact ⟨hquit, hcontinue⟩
  have hpayoffLower : quittingTerminalPayoff reward profile who ≤
      quittingStationaryUnilateralCap reward root who := by
    rw [← quittingBestReplyValue_stationary]
    have hself := le_quittingBestReplyValue reward profile who (profile who)
    simpa only [Function.update_eq_self] using hself
  have heq := le_antisymm hpayoffLower hcapUpper
  refine ⟨heq, ?_⟩
  rw [heq]
  exact quittingPunishmentValue_le_stationaryUnilateralCap reward who root

/-! ## Backward compactification of finite solo-prefix words -/

/-- A minimum-spine edge constrained to one fixed solo owner and a closed
hazard interval.  The name `minimum` refers only to the reused compact fiber
type: the definition merely fixes the source's total debt. -/
def IsFinFourUniformSoloSpineEdge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner : Fin 4) (alpha beta : ℝ)
    (current tail : QuittingTerminalSemanticSpinePoint (Fin 4)) : Prop :=
  IsQuittingTerminalSemanticMinimumSpineEdge reward current tail ∧
    (∀ other, other ≠ owner →
      current.2 other = stdSimplexEquiv (PMF.pure false)) ∧
    alpha ≤ (quittingRootOfSimplex current.2 owner true).toReal ∧
    (quittingRootOfSimplex current.2 owner true).toReal ≤ beta

/-- The box-restricted uniform solo-edge relation is closed. -/
theorem isClosed_finFourUniformSoloSpineEdgeGraph
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (base : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (alpha beta : ℝ) :
    IsClosed {edge : QuittingTerminalSemanticSpinePoint (Fin 4) ×
        QuittingTerminalSemanticSpinePoint (Fin 4) |
      edge.1 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        edge.2 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        IsFinFourUniformSoloSpineEdge reward owner alpha beta
          edge.1 edge.2} := by
  let baseGraph : Set
      (QuittingTerminalSemanticSpinePoint (Fin 4) ×
        QuittingTerminalSemanticSpinePoint (Fin 4)) :=
    {edge |
      edge.1 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        edge.2 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        IsQuittingTerminalSemanticMinimumSpineEdge reward edge.1 edge.2}
  have hbase : IsClosed baseGraph := by
    exact isClosed_quittingTerminalSemanticMinimumSpineEdgeGraph reward base
  have hpureEach : ∀ other : Fin 4, IsClosed
      {edge : QuittingTerminalSemanticSpinePoint (Fin 4) ×
          QuittingTerminalSemanticSpinePoint (Fin 4) |
        other ≠ owner →
        edge.1.2 other = stdSimplexEquiv (PMF.pure false)} := by
    intro other
    by_cases hne : other ≠ owner
    · rw [show {edge : QuittingTerminalSemanticSpinePoint (Fin 4) ×
            QuittingTerminalSemanticSpinePoint (Fin 4) |
          other ≠ owner →
            edge.1.2 other = stdSimplexEquiv (PMF.pure false)} =
          {edge | edge.1.2 other = stdSimplexEquiv (PMF.pure false)} by
        ext edge
        simp [hne]]
      exact isClosed_eq (by fun_prop) continuous_const
    · have heq : other = owner := not_ne_iff.mp hne
      subst other
      simp
  have hpure : IsClosed
      {edge : QuittingTerminalSemanticSpinePoint (Fin 4) ×
          QuittingTerminalSemanticSpinePoint (Fin 4) | ∀ other,
      other ≠ owner →
        edge.1.2 other = stdSimplexEquiv (PMF.pure false)} := by
    have hall := isClosed_iInter hpureEach
    rw [show {edge : QuittingTerminalSemanticSpinePoint (Fin 4) ×
          QuittingTerminalSemanticSpinePoint (Fin 4) | ∀ other,
        other ≠ owner →
          edge.1.2 other = stdSimplexEquiv (PMF.pure false)} =
        ⋂ other, {edge | other ≠ owner →
          edge.1.2 other = stdSimplexEquiv (PMF.pure false)} by
      ext edge
      simp]
    exact hall
  have hrateContinuous : Continuous (fun edge :
      QuittingTerminalSemanticSpinePoint (Fin 4) ×
        QuittingTerminalSemanticSpinePoint (Fin 4) ↦
      (quittingRootOfSimplex edge.1.2 owner true).toReal) := by
    simp_rw [quittingRootOfSimplex_apply_toReal]
    exact (continuous_apply true).comp
      (continuous_subtype_val.comp
        ((continuous_apply owner).comp
          (continuous_snd.comp continuous_fst)))
  have hlower : IsClosed {edge :
      QuittingTerminalSemanticSpinePoint (Fin 4) ×
        QuittingTerminalSemanticSpinePoint (Fin 4) |
      alpha ≤ (quittingRootOfSimplex edge.1.2 owner true).toReal} :=
    isClosed_Ici.preimage hrateContinuous
  have hupper : IsClosed {edge :
      QuittingTerminalSemanticSpinePoint (Fin 4) ×
        QuittingTerminalSemanticSpinePoint (Fin 4) |
      (quittingRootOfSimplex edge.1.2 owner true).toReal ≤ beta} :=
    isClosed_Iic.preimage hrateContinuous
  have heq : {edge : QuittingTerminalSemanticSpinePoint (Fin 4) ×
        QuittingTerminalSemanticSpinePoint (Fin 4) |
      edge.1 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        edge.2 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        IsFinFourUniformSoloSpineEdge reward owner alpha beta
          edge.1 edge.2} =
      baseGraph ∩
        ({edge | ∀ other, other ≠ owner →
          edge.1.2 other = stdSimplexEquiv (PMF.pure false)} ∩
        ({edge | alpha ≤
          (quittingRootOfSimplex edge.1.2 owner true).toReal} ∩
        {edge | (quittingRootOfSimplex edge.1.2 owner true).toReal ≤ beta})) := by
    ext edge
    simp only [baseGraph, IsFinFourUniformSoloSpineEdge,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    aesop
  rw [heq]
  exact hbase.inter (hpure.inter (hlower.inter hupper))

/-- Arbitrarily long correctly oriented finite windows in one fixed-debt
carrier box compactify to an infinite solo semantic spine.  This is the
inverse-limit formulation of the packet's reversed terminal-window diagonal.
-/
theorem exists_uniformSoloSemanticSpine_of_finitePrefixes
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (base : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (alpha beta : ℝ)
    (hprefix : ∀ horizon,
      (Math.Topology.compactFinitePrefixSolutionSet
        (quittingTerminalSemanticMinimumSpineBox reward base)
        (IsFinFourUniformSoloSpineEdge reward owner alpha beta)
        horizon).Nonempty) :
    ∃ (pair : ℕ → QuittingTerminalSemanticPair (Fin 4))
        (root : ℕ → Fin 4 → PMF Bool),
      (∀ time, pair time ∈ quittingTerminalSemanticCarrier reward) ∧
      (∀ time, quittingTerminalSemanticDebtSum (pair time) =
        quittingTerminalSemanticDebtSum base) ∧
      (∀ time, pair time = quittingTerminalSemanticPrefix reward
        (root time) (pair (time + 1))) ∧
      (∀ time, IsεQuittingRootNash reward (pair (time + 1)).1 0
        (root time)) ∧
      (∀ time other, other ≠ owner →
        root time other = PMF.pure false) ∧
      (∀ time, alpha ≤ (root time owner true).toReal) ∧
      ∀ time, (root time owner true).toReal ≤ beta := by
  obtain ⟨state, hstateBox, hstateEdge⟩ :=
    Math.Topology.exists_infiniteChain_of_finitePrefixes
      (quittingTerminalSemanticMinimumSpineBox reward base)
      (IsFinFourUniformSoloSpineEdge reward owner alpha beta)
      (quittingTerminalSemanticMinimumSpineBox_isCompact reward base)
      (isClosed_finFourUniformSoloSpineEdgeGraph
        reward base owner alpha beta) hprefix
  let pair : ℕ → QuittingTerminalSemanticPair (Fin 4) :=
    fun time ↦ (state time).1
  let root : ℕ → Fin 4 → PMF Bool :=
    fun time ↦ quittingRootOfSimplex (state time).2
  refine ⟨pair, root, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro time
    exact (hstateBox time).1
  · intro time
    exact (hstateBox time).2
  · intro time
    exact (hstateEdge time).1.1
  · intro time
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair (time + 1)).1 (root time)).mp
        (hstateEdge time).1.2
  · intro time other hne
    change (stdSimplexEquiv (α := Bool)).symm ((state time).2 other) =
      PMF.pure false
    rw [(hstateEdge time).2.1 other hne]
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (PMF.pure false)
  · intro time
    exact (hstateEdge time).2.2.1
  · intro time
    exact (hstateEdge time).2.2.2

/-- Reverse one terminal window of an outward prefix chain.  Truncated
subtraction fills all coordinates beyond the terminal window with the zeroth
source, which is harmless because only the first `horizon` edges are tested.
-/
def finFourReverseOutwardSoloPoint
    (pair : ℕ → QuittingTerminalSemanticPair (Fin 4))
    (root : ℕ → Fin 4 → PMF Bool) (horizon time : ℕ) :
    QuittingTerminalSemanticSpinePoint (Fin 4) :=
  (pair (horizon - time),
    quittingSimplexOfRoot (root (horizon - (time + 1))))

/-- An infinite outward literal prefix chain supplies every finite reversed
window required by the compact inverse limit. -/
theorem finitePrefixes_of_outwardUniformSoloCarrierChain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (base : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (alpha beta : ℝ)
    (pair : ℕ → QuittingTerminalSemanticPair (Fin 4))
    (root : ℕ → Fin 4 → PMF Bool)
    (hpair : ∀ time, pair time ∈ quittingTerminalSemanticCarrier reward)
    (hsum : ∀ time, quittingTerminalSemanticDebtSum (pair time) =
      quittingTerminalSemanticDebtSum base)
    (hprefix : ∀ time, pair (time + 1) =
      quittingTerminalSemanticPrefix reward (root time) (pair time))
    (hnash : ∀ time, IsεQuittingRootNash reward (pair time).1 0
      (root time))
    (hpure : ∀ time other, other ≠ owner →
      root time other = PMF.pure false)
    (hlower : ∀ time, alpha ≤ (root time owner true).toReal)
    (hupper : ∀ time, (root time owner true).toReal ≤ beta) :
    ∀ horizon,
      (Math.Topology.compactFinitePrefixSolutionSet
        (quittingTerminalSemanticMinimumSpineBox reward base)
        (IsFinFourUniformSoloSpineEdge reward owner alpha beta)
        horizon).Nonempty := by
  intro horizon
  refine ⟨finFourReverseOutwardSoloPoint pair root horizon, ?_, ?_⟩
  · intro time
    exact ⟨hpair (horizon - time), hsum (horizon - time)⟩
  · intro time
    let index := horizon - ((time : ℕ) + 1)
    have hcurrent : horizon - (time : ℕ) = index + 1 := by
      dsimp only [index]
      omega
    unfold IsFinFourUniformSoloSpineEdge
    refine ⟨?_, ?_, ?_, ?_⟩
    · constructor
      · simp only [finFourReverseOutwardSoloPoint,
          quittingRootOfSimplex_simplexOfRoot]
        rw [hcurrent]
        simpa only [index] using hprefix index
      · simp only [finFourReverseOutwardSoloPoint,
          quittingRootOfSimplex_simplexOfRoot]
        simpa only [index] using
          (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward (pair index).1 (root index)).mpr (hnash index)
    · intro other hne
      simp only [finFourReverseOutwardSoloPoint]
      change stdSimplexEquiv (root index other) =
        stdSimplexEquiv (PMF.pure false)
      rw [hpure index other hne]
    · simp only [finFourReverseOutwardSoloPoint,
        quittingRootOfSimplex_simplexOfRoot]
      simpa only [index] using hlower index
    · simp only [finFourReverseOutwardSoloPoint,
        quittingRootOfSimplex_simplexOfRoot]
      simpa only [index] using hupper index

/-- A uniform positive lower bound on the owner hazard forces the solo-spine
survival product to vanish. -/
theorem tendsto_zero_quittingSoloSemanticSurvival_of_uniform_hazard
    (root : ℕ → Fin 4 → PMF Bool) (owner : Fin 4) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hlower : ∀ time, alpha ≤ (root time owner true).toReal) :
    Tendsto (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0) := by
  have hfactor : ∀ time, (root time owner false).toReal ≤ 1 - alpha := by
    intro time
    have hmass := quittingRoot_continueProbability_add_quitProbability
      (root time) owner
    linarith [hlower time]
  have hbound : ∀ fuel,
      quittingSoloSemanticSurvival root owner 0 fuel ≤ (1 - alpha) ^ fuel := by
    intro fuel
    induction fuel with
    | zero => simp
    | succ fuel ih =>
        rw [quittingSoloSemanticSurvival_succ, pow_succ]
        exact mul_le_mul ih (by simpa using hfactor fuel)
          ENNReal.toReal_nonneg
          (pow_nonneg (sub_nonneg.mpr halpha1) fuel)
  have hpow : Tendsto (fun fuel : ℕ ↦ (1 - alpha) ^ fuel)
      atTop (nhds 0) := by
    apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · exact sub_nonneg.mpr halpha1
    · linarith
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun fuel ↦
      quittingSoloSemanticSurvival_nonneg root owner 0 fuel
  · exact Filter.Eventually.of_forall hbound
  · exact hpow

/-- Punishment normality rules out arbitrarily long finite windows of
uniformly interior fixed-owner solo prefixes in a fixed semantic-debt fiber.
This is the formal finite-termination core of the restart argument. -/
theorem not_arbitrarilyLong_uniformSoloSemanticSpine_of_normal
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (base : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hab : alpha ≤ beta) (hbeta : beta < 1)
    (hnormal : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    ¬ ∀ horizon,
      (Math.Topology.compactFinitePrefixSolutionSet
        (quittingTerminalSemanticMinimumSpineBox reward base)
        (IsFinFourUniformSoloSpineEdge reward owner alpha beta)
        horizon).Nonempty := by
  intro hprefix
  obtain ⟨pair, root, hpair, _hsum, hrelation, hnash, hpure,
      hlower, hupper⟩ :=
    exists_uniformSoloSemanticSpine_of_finitePrefixes
      reward base owner alpha beta hprefix
  have halphaOne : alpha ≤ 1 := hab.trans hbeta.le
  have hsurvival :=
    tendsto_zero_quittingSoloSemanticSurvival_of_uniform_hazard
      root owner halpha halphaOne hlower
  have hquit : 0 < (root 0 owner true).toReal :=
    halpha.trans_le (hlower 0)
  have hcontinue : 0 < (root 0 owner false).toReal := by
    have hmass := quittingRoot_continueProbability_add_quitProbability
      (root 0) owner
    linarith [hupper 0]
  have hstrict :=
    witness.atomic_restrictions_of_soloSemanticSpine_survival_zero
      pair root owner hpair hrelation hnash hpure hquit hcontinue hsurvival
  exact (not_lt_of_ge hnormal) hstrict.2

/-- There is no infinite outward exact carrier chain whose roots all have one
fixed solo owner and hazards in a compact subinterval of `(0,1)`, while total
semantic debt stays fixed.  The proof explicitly reverses finite terminal
windows before applying the occupation theorem. -/
theorem not_exists_outwardUniformSoloCarrierChain_of_normal
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (base : QuittingTerminalSemanticPair (Fin 4))
    (owner : Fin 4) (alpha beta : ℝ)
    (halpha : 0 < alpha) (hab : alpha ≤ beta) (hbeta : beta < 1)
    (hnormal : quittingPunishmentValue reward owner ≤
      quittingSoloReward reward owner owner) :
    ¬ ∃ (pair : ℕ → QuittingTerminalSemanticPair (Fin 4))
        (root : ℕ → Fin 4 → PMF Bool),
      (∀ time, pair time ∈ quittingTerminalSemanticCarrier reward) ∧
      (∀ time, quittingTerminalSemanticDebtSum (pair time) =
        quittingTerminalSemanticDebtSum base) ∧
      (∀ time, pair (time + 1) =
        quittingTerminalSemanticPrefix reward (root time) (pair time)) ∧
      (∀ time, IsεQuittingRootNash reward (pair time).1 0
        (root time)) ∧
      (∀ time other, other ≠ owner →
        root time other = PMF.pure false) ∧
      (∀ time, alpha ≤ (root time owner true).toReal) ∧
      ∀ time, (root time owner true).toReal ≤ beta := by
  rintro ⟨pair, root, hpair, hsum, hprefix, hnash, hpure,
    hlower, hupper⟩
  apply not_arbitrarilyLong_uniformSoloSemanticSpine_of_normal
    reward witness base owner alpha beta halpha hab hbeta hnormal
  exact finitePrefixes_of_outwardUniformSoloCarrierChain
    reward base owner alpha beta pair root hpair hsum hprefix hnash hpure
      hlower hupper

end GameTheory
