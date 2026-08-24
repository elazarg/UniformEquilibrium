/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Frozen.ConditionedRestartBarrier
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityBranchExclusions

/-!
# Strategic meaning of a killed frozen source component

Zero finite survival of an active frozen source marginal means that the
literal source strategy has a sure-Quit live row before the packet endpoint.
It does not produce a sure-exit equilibrium.  Every active mover has strictly
positive debt at the tangent-family base, and convergence of the actual source
semantic pairs keeps a fixed positive fraction of that debt at all late ranks.

Consequently the killed-source residual is a quantitatively exploitable
sure-Quit strategy at the actual frozen source.  The capstone refines the
conditioned restart alternative accordingly: either the packet has the exact
positive-radius conditioned kernel, or one of its two source labels surely
quits before the cutoff while retaining a uniform positive deviation gain.
This rules out dispatching the residual merely by reclassifying the literal
source profile as a sure-exit, instant-punishment, or stationary equilibrium.
Additional strategic inequalities or a different source profile are needed.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability DiscreteHazard
open scoped BigOperators Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- Zero finite survival is witnessed by a literal sure-Quit row before the
cutoff. -/
theorem exists_frozenRadialSource_stop_eq_one_of_survival_eq_zero
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat)
    (hzero :
      (frontier.frozenRadialOuterSourceScalarHazard rank mover).survival
        0 cutoff = 0) :
    ∃ time, time < cutoff ∧
      (frontier.frozenRadialOuterSourceScalarHazard rank mover).stop time = 1 := by
  have hproduct : (Finset.range cutoff).prod (fun time =>
      1 - (frontier.frozenRadialOuterSourceScalarHazard rank mover).stop
        (0 + time)) = 0 := by
    simpa [ScalarHazard.survival, Math.survivalProduct] using hzero
  obtain ⟨time, htime, hstop⟩ := Finset.prod_eq_zero_iff.mp hproduct
  refine ⟨time, Finset.mem_range.mp htime, ?_⟩
  simp only [Nat.zero_add] at hstop
  linarith

/-- The scalar witness is an actual pure-Quit row of the stored frozen source
behavior strategy. -/
theorem exists_frozenRadialSource_liveHazard_eq_pure_true_of_survival_eq_zero
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat)
    (hzero :
      (frontier.frozenRadialOuterSourceScalarHazard rank mover).survival
        0 cutoff = 0) :
    ∃ time, time < cutoff ∧
      quittingBehaviorLiveHazard reward (frontier.source rank mover.1) time =
        PMF.pure true := by
  obtain ⟨time, htime, hstop⟩ :=
    frontier.exists_frozenRadialSource_stop_eq_one_of_survival_eq_zero
      rank mover cutoff hzero
  refine ⟨time, htime, ?_⟩
  unfold frozenRadialOuterSourceScalarHazard frozenRadialOuterSourceHazard
    BooleanHazard.toScalar stopProbability at hstop
  exact Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ hstop

/-- Each active mover's actual frozen source debt is eventually at least half
of its strictly positive base debt. -/
theorem eventually_frozenSource_moverDebt_ge_half_base
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    ∀ᶠ rank in atTop,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (frontier.source rank))
          mover.1 >=
        quittingTerminalSemanticDebt frontier.base mover.1 / 2 := by
  have hbase : 0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
    (frontier.positiveDebtSupport_iff mover.1).mp mover.property
  have htendsto : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (frontier.source rank)) mover.1)
      atTop
      (nhds (quittingTerminalSemanticDebt frontier.base mover.1)) :=
    (continuous_quittingTerminalSemanticDebt mover.1).tendsto frontier.base
      |>.comp frontier.source_tendsto
  have heventually := (tendsto_order.1 htendsto).1
    (quittingTerminalSemanticDebt frontier.base mover.1 / 2) (by linarith)
  filter_upwards [heventually] with rank hrank
  exact hrank.le

/-- A common strictly positive debt floor for two active source labels. -/
def frozenTwoLabelSourceDebtFloor
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (first second : {who // who ∈ frontier.positiveDebtSupport}) : Real :=
  min (quittingTerminalSemanticDebt frontier.base first.1)
    (quittingTerminalSemanticDebt frontier.base second.1) / 2

theorem frozenTwoLabelSourceDebtFloor_pos
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (first second : {who // who ∈ frontier.positiveDebtSupport}) :
    0 < frontier.frozenTwoLabelSourceDebtFloor first second := by
  have hfirst : 0 < quittingTerminalSemanticDebt frontier.base first.1 :=
    (frontier.positiveDebtSupport_iff first.1).mp first.property
  have hsecond : 0 < quittingTerminalSemanticDebt frontier.base second.1 :=
    (frontier.positiveDebtSupport_iff second.1).mp second.property
  exact div_pos (lt_min hfirst hsecond) (by norm_num)

/-- At late ranks both selected labels retain the same positive source-debt
floor. -/
theorem eventually_frozenSource_twoLabelDebt_ge_floor
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (first second : {who // who ∈ frontier.positiveDebtSupport}) :
    ∀ᶠ rank in atTop,
      frontier.frozenTwoLabelSourceDebtFloor first second <=
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (frontier.source rank))
            first.1 ∧
        frontier.frozenTwoLabelSourceDebtFloor first second <=
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (frontier.source rank))
            second.1 := by
  filter_upwards [frontier.eventually_frozenSource_moverDebt_ge_half_base first,
    frontier.eventually_frozenSource_moverDebt_ge_half_base second]
      with rank hfirst hsecond
  constructor
  · exact (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)).trans
      hfirst
  · exact (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)).trans
      hsecond

/-- The killed branch with its actual strategic content exposed. -/
def HasFrozenRadialTwoLabelExploitablyKilledSource
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat) : Prop :=
  ∃ mover : {who // who ∈ frontier.positiveDebtSupport},
    (mover = first ∨ mover = second) ∧
      ∃ time, time < cutoff ∧
        quittingBehaviorLiveHazard reward
            (frontier.source rank mover.1) time = PMF.pure true ∧
        ∃ deviation : (quittingGame reward).BehaviorStrategy mover.1,
          frontier.frozenTwoLabelSourceDebtFloor first second / 2 <=
            quittingTerminalPayoff reward
                (Function.update (frontier.source rank) mover.1 deviation)
                mover.1 -
              quittingTerminalPayoff reward (frontier.source rank) mover.1

/-- A killed source at a rank where both labels retain their debt floor is an
exploitably killed source, with an explicit sure-Quit time. -/
theorem hasExploitablyKilledSource_of_killedSource_of_debtFloor
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : Nat)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (cutoff : Nat)
    (hkilled : HasFrozenRadialTwoLabelKilledSource frontier rank first second cutoff)
    (hdebt : frontier.frozenTwoLabelSourceDebtFloor first second <=
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (frontier.source rank))
            first.1 ∧
        frontier.frozenTwoLabelSourceDebtFloor first second <=
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (frontier.source rank))
            second.1) :
    HasFrozenRadialTwoLabelExploitablyKilledSource frontier rank first second cutoff := by
  rcases hkilled with hfirst | hsecond
  · obtain ⟨time, htime, hstop⟩ :=
      frontier.exists_frozenRadialSource_liveHazard_eq_pure_true_of_survival_eq_zero
        rank first cutoff hfirst
    have hfloor := frontier.frozenTwoLabelSourceDebtFloor_pos first second
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward
        (frontier.source rank) first.1
        (δ := frontier.frozenTwoLabelSourceDebtFloor first second / 2)
        (div_pos hfloor (by norm_num))
    refine ⟨first, Or.inl rfl, time, htime, hstop, deviation, ?_⟩
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hdebt
    linarith
  · obtain ⟨time, htime, hstop⟩ :=
      frontier.exists_frozenRadialSource_liveHazard_eq_pure_true_of_survival_eq_zero
        rank second cutoff hsecond
    have hfloor := frontier.frozenTwoLabelSourceDebtFloor_pos first second
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward
        (frontier.source rank) second.1
        (δ := frontier.frozenTwoLabelSourceDebtFloor first second / 2)
        (div_pos hfloor (by norm_num))
    refine ⟨second, Or.inr rfl, time, htime, hstop, deviation, ?_⟩
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hdebt
    linarith

/-- **The killed-source residual is quantitatively exploitable.**

The exact packet producer can therefore be sharpened without any supplied
restart hypothesis: all sufficiently late packets either have the checked
two-label conditioned kernel or expose an actual source marginal which quits
surely before the cutoff and still has a fixed positive deviation debt. -/
theorem exists_frozenRadialStrictPackets_available_or_exploitablySourceKilled
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.positiveDebtSupport} -> Real,
      ∃ hweight0 : forall mover, 0 <= weight mover,
      ∃ hweightLt : forall mover, weight mover < 1,
      ∃ first second : {who // who ∈ frontier.positiveDebtSupport},
        first ≠ second ∧ 0 < weight first ∧ 0 < weight second ∧
          0 < frontier.frozenTwoLabelSourceDebtFloor first second ∧
          ∃ kappa : Real, 0 < kappa ∧
            ∀ᶠ rank in atTop,
              ∃ packet : QuittingLiteralFiniteProfilePacket reward
                  (frontier.frozenRadialPacketProfile rank weight hweight0
                    (fun mover => (hweightLt mover).le))
                  frontier.positiveDebtSupport first.1 second.1
                  (frontier.scale rank) kappa,
                HasFrozenRadialTwoLabelAvailableConditionedKernel frontier
                    rank weight hweight0 (fun mover => (hweightLt mover).le)
                    first second packet ∨
                  HasFrozenRadialTwoLabelExploitablyKilledSource frontier rank
                    first second packet.length := by
  obtain ⟨weight, hweight0, hweightLt, first, second, hne, hfirst,
      hsecond, kappa, hkappa, hpackets⟩ :=
    frontier.exists_frozenRadialStrictPackets_available_or_sourceKilled
      hcirculation
  refine ⟨weight, hweight0, hweightLt, first, second, hne, hfirst, hsecond,
    frontier.frozenTwoLabelSourceDebtFloor_pos first second,
    kappa, hkappa, ?_⟩
  filter_upwards [hpackets,
    frontier.eventually_frozenSource_twoLabelDebt_ge_floor first second]
      with rank hpacket hdebt
  obtain ⟨packet, havailable | hkilled⟩ := hpacket
  · exact ⟨packet, Or.inl havailable⟩
  · exact ⟨packet, Or.inr
      (frontier.hasExploitablyKilledSource_of_killedSource_of_debtFloor
        rank first second packet.length hkilled hdebt)⟩

end QuittingPositiveMinimumDebtTangentFamily

namespace QuittingTerminalExploitabilityWitness

/-- In the tangent-family regime, the familiar static and generated-profile
branches are unavailable independently of the killed-source observation.
Thus a sure-Quit row inside the actual frozen source cannot be promoted to one
of those branches without additional Nash inequalities. -/
theorem excludes_sureExit_stationary_instant_and_stationarilyGenerated
    (witness : QuittingTerminalExploitabilityWitness reward) :
    (forall S : Finset iota, ¬IsQuittingSureExitSet reward S) ∧
      ¬QuittingStationaryεEquilibriumExistence reward ∧
      ¬QuittingInstantPunishmentεEquilibriumExistence reward ∧
      ¬QuittingStationarilyGeneratedApproximateEquilibria reward := by
  refine ⟨witness.not_isQuittingSureExitSet,
    witness.not_quittingStationaryεEquilibriumExistence,
    witness.not_quittingInstantPunishmentεEquilibriumExistence, ?_⟩
  intro hgenerated
  have happrox :=
    quittingApproximateEquilibriumExistence_of_stationarilyGenerated hgenerated
  have hbehavior :=
    (quittingApproximateEquilibriumExistence_iff_behavior reward).mp happrox
  obtain ⟨profile, hnash⟩ := hbehavior (witness.terminalGap / 2)
    (by linarith [witness.terminalGap_pos])
  exact witness.not_isεAsymptoticNash_of_lt_terminalGap profile
    (by linarith [witness.terminalGap_pos]) hnash

end QuittingTerminalExploitabilityWitness

end GameTheory
