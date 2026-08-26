/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.ProbabilityMassFunction
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.PersistentBaseInducedGame
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# Arbitrary completion around one dominant quitting anchor

One sure-Quit anchor and a mixed Nash point of the complementary finite
binary game give an exact stationary terminal Nash profile when the anchor's
immediate-Quit value is nonnegative and dominates every terminal reward on
the face which excludes it.  All other reward coordinates are unrestricted.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The free complement of one distinguished anchor. -/
def quittingSingleAnchorFree (anchor : ι) : Finset ι :=
  Finset.univ.erase anchor

/-- The ambient stationary row induced by one anchor and one mixed point of
the complementary binary game. -/
def quittingSingleAnchorRoot
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig) : ι → PMF Bool :=
  quittingPersistentBaseRoot {anchor} (quittingSingleAnchorFree anchor) point

/-- The anchor's unconditional immediate-Quit value at the induced root. -/
def quittingSingleAnchorQuitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig) : ℝ :=
  quittingStationaryFixedOpponentsQuitValue reward
    (quittingSingleAnchorRoot anchor point) anchor

/-- The exact singleton-anchor dominance screen.  The terminal inequality is
required only on coalitions which exclude the anchor. -/
def QuittingSingleAnchorInducedDominance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig) : Prop :=
  0 ≤ quittingSingleAnchorQuitValue reward anchor point ∧
    ∀ terminal, anchor ∉ terminal.1 →
      reward terminal anchor ≤ quittingSingleAnchorQuitValue reward anchor point

/-- The anchor coordinate is the literal indicator of anchor membership in the
terminal coalition.  Every other reward coordinate is unrestricted. -/
def QuittingSingleAnchorMembershipReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι) : Prop :=
  ∀ terminal, reward terminal anchor = if anchor ∈ terminal.1 then 1 else 0

@[simp] theorem quittingSingleAnchorRoot_anchor
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig) :
    quittingSingleAnchorRoot anchor point anchor = PMF.pure true := by
  exact quittingPersistentBaseRoot_apply_of_mem_base
    {anchor} (quittingSingleAnchorFree anchor) point (by simp)

theorem quittingSingleAnchorRoot_continueMass_eq_zero
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig) :
    quittingStationaryContinueMass (quittingSingleAnchorRoot anchor point) = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ anchor)
  rw [quittingSingleAnchorRoot_anchor]
  simp

theorem quittingSingleAnchorRoot_fixedOpponentsContinueMass_eq_zero
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig)
    {who : ι} (hwho : who ≠ anchor) :
    quittingStationaryFixedOpponentsContinueMass
      (quittingSingleAnchorRoot anchor point) who = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_zero (Finset.mem_univ anchor)
  change ((Function.update (quittingSingleAnchorRoot anchor point) who
    (PMF.pure false) anchor) false).toReal = 0
  rw [Function.update_of_ne hwho.symm, quittingSingleAnchorRoot_anchor]
  simp

/-- Pointwise dominance on the anchor-excluding face bounds the unconditional
one-stage continuation reward by absorption probability times the Quit value. -/
theorem quittingSingleAnchor_continueReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (anchor : ι) (bound : ℝ)
    (hface : ∀ terminal, anchor ∉ terminal.1 → reward terminal anchor ≤ bound) :
    quittingStationaryFixedOpponentsContinueReward reward root anchor ≤
      (1 - quittingStationaryFixedOpponentsContinueMass root anchor) * bound := by
  let opponentRoot := Function.update root anchor (PMF.pure false)
  let absorbingBound : (ι → Bool) → ℝ := fun action =>
    bound * if (quittingQuitters action).Nonempty then 1 else 0
  have hpoint (action : ι → Bool)
      (haction : action ∈ (pmfPi opponentRoot).support) :
      quittingRootPayoff reward (0 : Payoff ι) action anchor ≤
        absorbingBound action := by
    have hanchor : action anchor = false := by
      exact eq_of_mem_support_pmfPi_update_pure root anchor false haction
    by_cases hquit : (quittingQuitters action).Nonempty
    · rw [show quittingRootPayoff reward (0 : Payoff ι) action anchor =
          reward ⟨quittingQuitters action, hquit⟩ anchor by
        simp [quittingRootPayoff, hquit]]
      rw [show absorbingBound action = bound by
        dsimp [absorbingBound]
        rw [if_pos hquit]
        simp]
      exact hface ⟨quittingQuitters action, hquit⟩ (by
        simp [quittingQuitters, hanchor])
    · rw [show quittingRootPayoff reward (0 : Payoff ι) action anchor = 0 by
          simp [quittingRootPayoff, hquit]]
      rw [show absorbingBound action = 0 by
        dsimp [absorbingBound]
        rw [if_neg hquit]
        simp]
  have hupper : quittingRootAbsorbingContribution reward opponentRoot anchor ≤
      Math.Probability.expect (pmfPi opponentRoot) absorbingBound := by
    unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
    exact Math.ProbabilityMassFunction.expect_mono_on_support
      (pmfPi opponentRoot) _ _ hpoint
  have hexpect : Math.Probability.expect (pmfPi opponentRoot) absorbingBound =
      bound * quittingRootAbsorptionMass opponentRoot := by
    unfold absorbingBound
    rw [Math.Probability.expect_const_mul,
      expect_quittingNonemptyIndicator_eq_absorptionMass]
  rw [hexpect] at hupper
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueMass, quittingRootAbsorptionMass,
    opponentRoot, mul_comm] using hupper

theorem quittingTerminalPayoff_singleAnchorRoot_eq_quitValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingSingleAnchorRoot anchor point))
        anchor =
      quittingSingleAnchorQuitValue reward anchor point := by
  let root := quittingSingleAnchorRoot anchor point
  have hzero : quittingStationaryContinueMass root = 0 :=
    quittingSingleAnchorRoot_continueMass_eq_zero anchor point
  have habsorbs : quittingStationaryContinueMass root < 1 := by
    rw [hzero]
    norm_num
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward root anchor habsorbs, hzero]
  rw [sub_zero, div_one]
  change quittingRootAbsorbingContribution reward root anchor =
    quittingRootAbsorbingContribution reward
      (Function.update root anchor (PMF.pure true)) anchor
  have hupdate : Function.update root anchor (PMF.pure true) = root := by
    rw [← show root anchor = PMF.pure true from
      quittingSingleAnchorRoot_anchor anchor point]
    exact Function.update_eq_self anchor root
  rw [hupdate]

/-- Under a literal membership coordinate, the anchor's immediate-Quit value
is one for every complementary mixed point. -/
theorem quittingSingleAnchorQuitValue_eq_one_of_membership
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig)
    (hmembership : QuittingSingleAnchorMembershipReward reward anchor) :
    quittingSingleAnchorQuitValue reward anchor point = 1 := by
  unfold quittingSingleAnchorQuitValue
    quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
    quittingRootAbsorbingContribution quittingRootExpectedPayoff
  calc
    Math.Probability.expect
        (pmfPi (Function.update (quittingSingleAnchorRoot anchor point)
          anchor (PMF.pure true)))
        (fun action => quittingRootPayoff reward (0 : Payoff ι) action anchor) =
      Math.Probability.expect
        (pmfPi (Function.update (quittingSingleAnchorRoot anchor point)
          anchor (PMF.pure true))) (fun _action => (1 : ℝ)) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro action haction
      have htrue : action anchor = true :=
        eq_of_mem_support_pmfPi_update_pure
          (quittingSingleAnchorRoot anchor point) anchor true haction
      have hquit : (quittingQuitters action).Nonempty := by
        exact ⟨anchor, by simp [quittingQuitters, htrue]⟩
      have hmem : anchor ∈ quittingQuitters action := by
        simp [quittingQuitters, htrue]
      rw [show quittingRootPayoff reward (0 : Payoff ι) action anchor =
          reward ⟨quittingQuitters action, hquit⟩ anchor by
        simp [quittingRootPayoff, hquit]]
      rw [hmembership ⟨quittingQuitters action, hquit⟩, if_pos hmem]
    _ = 1 := Math.Probability.expect_const _ _

/-- Literal anchor membership implies the full singleton-anchor dominance
screen, independently of the complementary induced Nash point. -/
theorem QuittingSingleAnchorMembershipReward.inducedDominance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig)
    (hmembership : QuittingSingleAnchorMembershipReward reward anchor) :
    QuittingSingleAnchorInducedDominance reward anchor point := by
  have hvalue := quittingSingleAnchorQuitValue_eq_one_of_membership
    reward anchor point hmembership
  constructor
  · rw [hvalue]
    norm_num
  · intro terminal hnot
    rw [hmembership terminal, if_neg hnot, hvalue]
    norm_num

/-- The induced singleton-anchor row is exact terminal Nash against every
behavioral unilateral deviation. -/
theorem isZeroAsymptoticNash_of_singleAnchorInducedNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward {anchor}
      (quittingSingleAnchorFree anchor))
    (hdominates : QuittingSingleAnchorInducedDominance reward anchor point) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward (quittingSingleAnchorRoot anchor point)) := by
  let root := quittingSingleAnchorRoot anchor point
  let value : Payoff ι := fun who =>
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who
  have hzero : quittingStationaryContinueMass root = 0 :=
    quittingSingleAnchorRoot_continueMass_eq_zero anchor point
  have hterminalZero : value = quittingRootSuccessorPayoff reward 0 root := by
    funext who
    change quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) who = _
    rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div]
    · rw [quittingRootSuccessorPayoff,
        quittingRootExpectedPayoff_eq_absorbingContribution_add, hzero]
      simp
    · rw [hzero]
      norm_num
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    funext who
    exact quittingTerminalPayoff_stationary_eq_rootExpectedPayoff reward root who
  have hanchorValue : value anchor =
      quittingSingleAnchorQuitValue reward anchor point := by
    exact quittingTerminalPayoff_singleAnchorRoot_eq_quitValue
      reward anchor point
  have hcontinue := quittingSingleAnchor_continueReward_le reward root anchor
    (quittingSingleAnchorQuitValue reward anchor point) hdominates.2
  have hendpoint : IsεQuittingRootEndpointNash reward value 0 root := by
    rw [isεQuittingRootEndpointNash_iff_purePayoff_le]
    intro who
    by_cases hwho : who = anchor
    · subst who
      have hsuccessor :
          quittingRootSuccessorPayoff reward value root anchor = value anchor :=
        (congrFun hfixed anchor).symm
      constructor
      · have hmix := quittingRootSuccessorPayoff_eq_endpointMix
          reward value root anchor
        rw [show root anchor = PMF.pure true by
          exact quittingSingleAnchorRoot_anchor anchor point] at hmix
        simp at hmix
        linarith
      · rw [hsuccessor, add_zero]
        rw [quittingRootContinuePayoff_eq_fixedOpponents
          reward (fun _ => root) anchor value 0]
        change quittingStationaryFixedOpponentsContinueReward reward root anchor +
            quittingStationaryFixedOpponentsContinueMass root anchor * value anchor ≤
          value anchor
        rw [hanchorValue]
        linarith
    · have hfree : who ∈ quittingSingleAnchorFree anchor := by
        simp [quittingSingleAnchorFree, hwho]
      have hpure := quittingPersistentBaseRoot_free_purePayoff_le
        reward {anchor} (quittingSingleAnchorFree anchor)
        (Finset.singleton_nonempty anchor) (by
          simp [quittingSingleAnchorFree]) point hpoint who hfree
      have hmass : quittingStationaryFixedOpponentsContinueMass root who = 0 :=
        quittingSingleAnchorRoot_fixedOpponentsContinueMass_eq_zero
          anchor point hwho
      have hquitEq : quittingRootQuitPayoff reward value root who =
          quittingRootQuitPayoff reward 0 root who := by
        exact (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
          reward (fun _ => root) who value 0).trans
          (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
            reward (fun _ => root) who 0 0).symm
      have hcontinueEq : quittingRootContinuePayoff reward value root who =
          quittingRootContinuePayoff reward 0 root who := by
        rw [quittingRootContinuePayoff_eq_fixedOpponents
            reward (fun _ => root) who value 0,
          quittingRootContinuePayoff_eq_fixedOpponents
            reward (fun _ => root) who 0 0]
        change quittingStationaryFixedOpponentsContinueReward reward root who +
            quittingStationaryFixedOpponentsContinueMass root who * value who =
          quittingStationaryFixedOpponentsContinueReward reward root who +
            quittingStationaryFixedOpponentsContinueMass root who * 0
        rw [hmass]
        simp
      have hzeroValue := congrFun hterminalZero who
      have hfixedValue := congrFun hfixed who
      constructor
      · calc
          quittingRootQuitPayoff reward value root who =
              quittingRootQuitPayoff reward 0 root who := hquitEq
          _ ≤ quittingRootSuccessorPayoff reward 0 root who := by
            simpa [root, quittingSingleAnchorRoot] using hpure.1
          _ = value who := hzeroValue.symm
          _ = quittingRootSuccessorPayoff reward value root who := hfixedValue
          _ ≤ quittingRootSuccessorPayoff reward value root who + 0 := by simp
      · calc
          quittingRootContinuePayoff reward value root who =
              quittingRootContinuePayoff reward 0 root who := hcontinueEq
          _ ≤ quittingRootSuccessorPayoff reward 0 root who := by
            simpa [root, quittingSingleAnchorRoot] using hpure.2
          _ = value who := hzeroValue.symm
          _ = quittingRootSuccessorPayoff reward value root who := hfixedValue
          _ ≤ quittingRootSuccessorPayoff reward value root who + 0 := by simp
  have hboundary : IsQuittingStationaryBoundaryAdmissible reward root value := by
    intro who hmass
    by_cases hwho : who = anchor
    · subst who
      rw [hanchorValue]
      rw [← quittingStationaryFixedOpponentsQuitValue_eq_singleton_of_mass_eq_one
        reward root anchor hmass]
      exact max_le hdominates.1 le_rfl
    · have hmassZero :=
        quittingSingleAnchorRoot_fixedOpponentsContinueMass_eq_zero
          anchor point hwho
      rw [hmassZero] at hmass
      norm_num at hmass
  exact (isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary
    reward root).2 ⟨hendpoint, hboundary⟩

/-- One induced Nash point satisfying the dominance screen produces exact
stationary terminal Nash and its uniform-equilibrium payoff. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (point : mixedPolytope (quittingBinaryForm
      (quittingSingleAnchorFree anchor)).sig)
    (hpoint : point ∈ quittingPersistentBaseNashSet reward {anchor}
      (quittingSingleAnchorFree anchor))
    (hdominates : QuittingSingleAnchorInducedDominance reward anchor point) :
    let root := quittingSingleAnchorRoot anchor point
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingTerminalPayoff reward (quittingStationaryProfile reward root)) := by
  let root := quittingSingleAnchorRoot anchor point
  have hnash := isZeroAsymptoticNash_of_singleAnchorInducedNash
    reward anchor point hpoint hdominates
  exact ⟨hnash, quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward (quittingStationaryProfile reward root) hnash⟩

/-- Source-facing version: it is enough that one point in the nonempty induced
Nash set satisfies the singleton-anchor dominance screen. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_singleAnchor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι)
    (hexists : ∃ point ∈ quittingPersistentBaseNashSet reward {anchor}
      (quittingSingleAnchorFree anchor),
        QuittingSingleAnchorInducedDominance reward anchor point) :
    ∃ point ∈ quittingPersistentBaseNashSet reward {anchor}
        (quittingSingleAnchorFree anchor),
      let root := quittingSingleAnchorRoot anchor point
      (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) 0
          (quittingStationaryProfile reward root) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingTerminalPayoff reward (quittingStationaryProfile reward root)) := by
  obtain ⟨point, hpoint, hdominates⟩ := hexists
  exact ⟨point, hpoint,
    exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint
      reward anchor point hpoint hdominates⟩

/-- **Single-anchor arbitrary-completion escape.**  A literal membership
coordinate at one anchor is enough: all other reward coordinates may be
arbitrary.  The complementary induced game supplies a mixed Nash point, and
the resulting sure-anchor row is exact terminal Nash against unrestricted
behavioral deviations and has a uniform-equilibrium payoff. -/
theorem exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : ι) :
    QuittingSingleAnchorMembershipReward reward anchor →
      ∃ point ∈ quittingPersistentBaseNashSet reward {anchor}
          (quittingSingleAnchorFree anchor),
        let root := quittingSingleAnchorRoot anchor point
        (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) 0
            (quittingStationaryProfile reward root) ∧
          (quittingGame reward).IsUniformEquilibriumPayoff none
            (quittingTerminalPayoff reward
              (quittingStationaryProfile reward root)) := by
  intro hmembership
  obtain ⟨point, hpoint⟩ := quittingPersistentBaseNashSet_nonempty
    reward {anchor} (quittingSingleAnchorFree anchor)
  exact ⟨point, hpoint,
    exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorPoint
      reward anchor point hpoint (hmembership.inducedDominance reward anchor point)⟩

end GameTheory
