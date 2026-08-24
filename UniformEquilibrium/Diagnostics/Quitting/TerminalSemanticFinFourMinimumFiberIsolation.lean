/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourStrictMinimumPlateauIsolation

/-!
# Uniform isolation of the four-player minimum semantic fiber

For a hypothetical `Fin 4` counterexample, every carrier point on the global
minimum-total-debt fiber is uniformly separated above every own singleton
reward.  The whole prescribed projection of that compact fiber therefore lies
in one open set on which all-Continue is the unique exact product root.

Compactness also gives a positive excess-debt moat: every carrier pair whose
prescribed payoff lies outside this open set has debt uniformly above the
global minimum.  Consequently a positively charged exact root against a
carrier tail must pay that excess debt.

The last statement is deliberately tail- and carrier-oriented.  It assigns no
semantic debt to a payoff-only Bellman tail, produces no nonlocal incoming
edge or return, and says nothing about approximate roots.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

/-- The carrier fiber at the total debt of a fixed semantic pair. -/
def quittingTerminalSemanticMinimumFiber
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  {pair | pair ∈ quittingTerminalSemanticCarrier reward ∧
    quittingTerminalSemanticDebtSum pair =
      quittingTerminalSemanticDebtSum base}

theorem quittingTerminalSemanticMinimumFiber_nonempty
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward) :
    (quittingTerminalSemanticMinimumFiber reward base).Nonempty := by
  exact ⟨base, hbase, rfl⟩

theorem quittingTerminalSemanticMinimumFiber_isCompact
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι) :
    IsCompact (quittingTerminalSemanticMinimumFiber reward base) := by
  apply (quittingTerminalSemanticCarrier_isCompact reward).inter_right
  exact isClosed_eq continuous_quittingTerminalSemanticDebtSum continuous_const

/-- The smallest own-singleton gap of a finite-player semantic pair. -/
def quittingTerminalSemanticMinimumSingletonGap
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) : ℝ :=
  Finset.inf' Finset.univ Finset.univ_nonempty
    (fun who => pair.1 who - reward (quittingSingletonTerminal who) who)

theorem continuous_quittingTerminalSemanticMinimumSingletonGap
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (quittingTerminalSemanticMinimumSingletonGap reward) := by
  unfold quittingTerminalSemanticMinimumSingletonGap
  refine Continuous.finset_inf'_apply Finset.univ_nonempty ?_
  intro who _
  exact (continuous_apply who).comp continuous_fst |>.sub continuous_const

theorem quittingTerminalSemanticMinimumSingletonGap_le
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    quittingTerminalSemanticMinimumSingletonGap reward pair ≤
      pair.1 who - reward (quittingSingletonTerminal who) who := by
  exact Finset.inf'_le _ (Finset.mem_univ who)

/-- Same-table punishment normality excludes a singleton-tight coordinate at
every positive global minimum, not only at one selected plateau point. -/
theorem minimumTerminalSemantic_strictSingleton_of_punishmentNormal
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∀ who, reward (quittingSingletonTerminal who) who < pair.1 who := by
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  intro who
  letI : Nonempty ι := ⟨who⟩
  have hdebtLe : quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hpair hminimum hpositive who
  have hsingletonLe :
      reward (quittingSingletonTerminal who) who ≤ pair.1 who := by
    unfold quittingTerminalSemanticDebt at hdebtLe
    linarith
  refine lt_of_le_of_ne hsingletonLe ?_
  intro heq
  have htight : pair.1 who =
      reward (quittingSingletonTerminal who) who := heq.symm
  have hownerDebt :=
    minimumTerminalSemantic_debt_eq_sum_of_singleton_tight
      (reward := reward) pair who hpair hminimum hpositive htight
  have houtside : ∀ other, other ≠ who →
      quittingTerminalSemanticDebt pair other = 0 := by
    intro other hother
    have hsumErase : ∑ player ∈ (Finset.univ.erase who),
        quittingTerminalSemanticDebt pair player = 0 := by
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun player : ι => quittingTerminalSemanticDebt pair player)
        (Finset.mem_univ who)
      change (∑ player ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebt pair player) +
          quittingTerminalSemanticDebt pair who =
        ∑ player ∈ (Finset.univ : Finset ι),
          quittingTerminalSemanticDebt pair player at hsplit
      rw [show (∑ player ∈ (Finset.univ : Finset ι),
          quittingTerminalSemanticDebt pair player) =
        quittingTerminalSemanticDebtSum pair by rfl, hownerDebt] at hsplit
      linarith
    have hotherLe : quittingTerminalSemanticDebt pair other ≤
        ∑ player ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebt pair player := by
      exact Finset.single_le_sum
        (fun player _ => hdebtNonneg player)
        (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)
    rw [hsumErase] at hotherLe
    exact le_antisymm hotherLe (hdebtNonneg other)
  have hface : QuittingSingletonTightMinimumFace reward pair who := {
    mem_carrier := hpair
    minimum := hminimum
    debt_pos := hpositive
    owner_tight := by
      simpa [quittingSoloReward, quittingSingletonTerminal] using htight
    outsider_debt := houtside }
  let gain := quittingSingletonCollisionGainMax reward who
  have hgain : 0 ≤ gain := by
    dsimp only [gain, quittingSingletonCollisionGainMax]
    exact le_trans (by simp)
      (QuittingBoundaryHolonomy.le_finitePlayerMax
        (fun other : ι => if other = who then 0 else
          max 0 (quittingSingletonCollisionReward reward who other -
            quittingSoloReward reward who other)) who)
  have hdenom : 0 < quittingTerminalSemanticDebtSum pair + gain := by
    linarith
  let ratio := quittingTerminalSemanticDebtSum pair /
    (quittingTerminalSemanticDebtSum pair + gain)
  have hratioPos : 0 < ratio := div_pos hpositive hdenom
  have hratioOne : ratio ≤ 1 := (div_le_one hdenom).2 (by linarith)
  let rate := ratio / 2
  have hratePos : 0 < rate := by
    dsimp only [rate]
    linarith
  have hrateOne : rate ≤ 1 := by
    dsimp only [rate]
    linarith
  have hrateBound : rate ≤ quittingTerminalSemanticDebtSum pair /
      (quittingTerminalSemanticDebtSum pair +
        quittingSingletonCollisionGainMax reward who) := by
    change rate ≤ ratio
    dsimp only [rate]
    linarith
  have hcontrolled : QuittingSoloRateControlled reward who pair rate :=
    quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax
      pair who hpositive hratePos hrateOne hrateBound
  have hendpoint : ∀ other, other ≠ who →
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward who other ≤
        quittingSoloReward reward who other := by
    intro other hother
    exact quittingControlledSolo_outsiderEndpoint_le_solo
      pair who other hface hcontrolled hother
  have hsign := singletonTight_soloReward_lt_punishmentValue_and_nonpos
    pair who hface hratePos hrateOne hendpoint
  have hnormalWho := hnormal who
  change quittingPunishmentValue reward who ≤
    quittingSoloReward reward who who at hnormalWho
  exact (not_lt_of_ge hnormalWho hsign.1).elim

/-- Strict singleton separation is uniform on the compact minimum-debt
fiber. -/
theorem exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (base : QuittingTerminalSemanticPair ι)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum base)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base, ∀ who,
        delta ≤ pair.1 who -
          reward (quittingSingletonTerminal who) who := by
  let gap := quittingTerminalSemanticMinimumSingletonGap reward
  have hfiberCompact :=
    quittingTerminalSemanticMinimumFiber_isCompact reward base
  have hfiberNonempty :=
    quittingTerminalSemanticMinimumFiber_nonempty reward base hbase
  obtain ⟨selected, hselected, hselectedMin⟩ :=
    hfiberCompact.exists_isMinOn hfiberNonempty
      (continuous_quittingTerminalSemanticMinimumSingletonGap reward).continuousOn
  have hgapPositive : ∀ pair ∈
      quittingTerminalSemanticMinimumFiber reward base, 0 < gap pair := by
    intro pair hpair
    have hpairMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [hpair.2]
      exact hminimum candidate hcandidate
    have hpairPositive : 0 < quittingTerminalSemanticDebtSum pair := by
      rw [hpair.2]
      exact hpositive
    have hstrict := minimumTerminalSemantic_strictSingleton_of_punishmentNormal
      pair hpair.1 hpairMinimum hpairPositive hnormal
    exact (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun who _ => by
      linarith [hstrict who]
  refine ⟨gap selected, hgapPositive selected hselected, ?_⟩
  intro pair hpair who
  exact (hselectedMin hpair).trans
    (quittingTerminalSemanticMinimumSingletonGap_le reward pair who)

/-- One open set freezes the exact root over the prescribed projection of the
entire positive minimum fiber. -/
theorem exists_open_exactAllContinueTube_minimumFiber
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (base : QuittingTerminalSemanticPair ι)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum base)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∃ (delta : ℝ) (tube : Set (Payoff ι)),
      0 < delta ∧ IsOpen tube ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base, ∀ who,
        delta ≤ pair.1 who -
          reward (quittingSingletonTerminal who) who) ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
        pair.1 ∈ tube) ∧
      ∀ tail ∈ tube,
        IsεQuittingRootNash reward tail 0
            (quittingAllContinueRoot : ι → PMF Bool) ∧
          ∀ root : ι → PMF Bool,
            IsεQuittingRootNash reward tail 0 root →
              root = (quittingAllContinueRoot : ι → PMF Bool) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal
      base hbase hminimum hpositive hnormal
  let exactAllContinue : Set (Payoff ι) :=
    {tail | IsεQuittingRootNash reward tail 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        ∀ root : ι → PMF Bool,
          IsεQuittingRootNash reward tail 0 root →
            root = (quittingAllContinueRoot : ι → PMF Bool)}
  let tube := interior exactAllContinue
  refine ⟨delta, tube, hdelta, isOpen_interior, hgap, ?_, ?_⟩
  · intro pair hpair
    have hpairMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [hpair.2]
      exact hminimum candidate hcandidate
    have hpairPositive : 0 < quittingTerminalSemanticDebtSum pair := by
      rw [hpair.2]
      exact hpositive
    have hstrict : ∀ who,
        reward (quittingSingletonTerminal who) who < pair.1 who := by
      intro who
      linarith [hgap pair hpair who]
    have hunique : ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward pair.1 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool) := by
      intro root hnash
      exact minimumTerminalSemantic_exactNash_eq_allContinue_of_strictSingleton
        pair hpair.1 hpairMinimum hpairPositive hstrict root hnash
    have hnear :=
      eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap
        reward pair.1 (quittingRewardBound_nonneg reward) hdelta
          (abs_reward_le_quittingRewardBound reward) (hgap pair hpair) hunique
    exact mem_interior_iff_mem_nhds.mpr hnear
  · intro tail htail
    have hmem : tail ∈ exactAllContinue := interior_subset htail
    exact hmem

/-- Compactness of the carrier prices escape from the open minimum-fiber
tube by a fixed positive excess in total semantic debt. -/
theorem exists_open_exactAllContinueTube_and_debtMoat_minimumFiber
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (base : QuittingTerminalSemanticPair ι)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum base)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) :
    ∃ (delta epsilon : ℝ) (tube : Set (Payoff ι)),
      0 < delta ∧ 0 < epsilon ∧ IsOpen tube ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base, ∀ who,
        delta ≤ pair.1 who -
          reward (quittingSingletonTerminal who) who) ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
        pair.1 ∈ tube) ∧
      (∀ tail ∈ tube,
        IsεQuittingRootNash reward tail 0
            (quittingAllContinueRoot : ι → PMF Bool) ∧
          ∀ root : ι → PMF Bool,
            IsεQuittingRootNash reward tail 0 root →
              root = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair <
            quittingTerminalSemanticDebtSum base + epsilon →
          pair.1 ∈ tube := by
  obtain ⟨delta, tube, hdelta, htubeOpen, hgap, hfiberTube, hfreeze⟩ :=
    exists_open_exactAllContinueTube_minimumFiber
      base hbase hminimum hpositive hnormal
  let outside : Set (QuittingTerminalSemanticPair ι) :=
    quittingTerminalSemanticCarrier reward ∩
      (Prod.fst : QuittingTerminalSemanticPair ι → Payoff ι) ⁻¹'
        (tubeᶜ : Set (Payoff ι))
  have houtsideCompact : IsCompact outside :=
    (quittingTerminalSemanticCarrier_isCompact reward).inter_right
      (htubeOpen.isClosed_compl.preimage continuous_fst)
  by_cases houtsideNonempty : outside.Nonempty
  · obtain ⟨selected, hselected, hselectedMin⟩ :=
      houtsideCompact.exists_isMinOn houtsideNonempty
        continuous_quittingTerminalSemanticDebtSum.continuousOn
    have hbaseLe : quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum selected :=
      hminimum selected hselected.1
    have hdebtNe : quittingTerminalSemanticDebtSum base ≠
        quittingTerminalSemanticDebtSum selected := by
      intro heq
      have hselectedFiber : selected ∈
          quittingTerminalSemanticMinimumFiber reward base :=
        ⟨hselected.1, heq.symm⟩
      exact hselected.2 (hfiberTube selected hselectedFiber)
    have hdebtLt : quittingTerminalSemanticDebtSum base <
        quittingTerminalSemanticDebtSum selected :=
      lt_of_le_of_ne hbaseLe hdebtNe
    let epsilon := (quittingTerminalSemanticDebtSum selected -
      quittingTerminalSemanticDebtSum base) / 2
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      linarith
    refine ⟨delta, epsilon, tube, hdelta, hepsilon, htubeOpen,
      hgap, hfiberTube, hfreeze, ?_⟩
    intro pair hpair hnear
    by_contra hnotTube
    have hpairOutside : pair ∈ outside := ⟨hpair, hnotTube⟩
    have hselectedLe := hselectedMin hpairOutside
    change quittingTerminalSemanticDebtSum selected ≤
      quittingTerminalSemanticDebtSum pair at hselectedLe
    dsimp only [epsilon] at hnear
    linarith
  · refine ⟨delta, 1, tube, hdelta, by norm_num, htubeOpen,
      hgap, hfiberTube, hfreeze, ?_⟩
    intro pair hpair _hnear
    by_contra hnotTube
    exact houtsideNonempty ⟨pair, hpair, hnotTube⟩

/-- A positively absorbing exact root against a carrier tail cannot lie below
the excess-debt moat of a frozen minimum-fiber tube.  An exact semantic-prefix
edge is an intended consumer once its tail carrier pair is supplied. -/
theorem minimumFiber_debt_add_epsilon_le_of_carrierTail_exactRoot_absorption_pos
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {base tail : QuittingTerminalSemanticPair ι}
    {epsilon : ℝ} {tube : Set (Payoff ι)}
    (hnear : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair <
          quittingTerminalSemanticDebtSum base + epsilon →
        pair.1 ∈ tube)
    (hfreeze : ∀ cap ∈ tube, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail.1 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    quittingTerminalSemanticDebtSum base + epsilon ≤
      quittingTerminalSemanticDebtSum tail := by
  apply le_of_not_gt
  intro htailNear
  have htailTube := hnear tail htail htailNear
  have hroot := hfreeze tail.1 htailTube root hnash
  rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at habsorption
  exact (lt_irrefl 0 habsorption).elim

/-- Literal `Fin 4` no-uniform data supplies uniform isolation of its whole
global-minimum carrier fiber and a positive carrier-tail debt moat. -/
theorem exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (base : QuittingTerminalSemanticPair (Fin 4))
        (delta epsilon : ℝ) (tube : Set (Payoff (Fin 4))),
      base ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum base ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum base ∧
      0 < delta ∧ 0 < epsilon ∧ IsOpen tube ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base, ∀ who,
        quittingPunishmentValue reward who ≤
            reward (quittingSingletonTerminal who) who ∧
          reward (quittingSingletonTerminal who) who < pair.1 who ∧
          delta ≤ pair.1 who -
            reward (quittingSingletonTerminal who) who) ∧
      (∀ pair ∈ quittingTerminalSemanticMinimumFiber reward base,
        pair.1 ∈ tube) ∧
      (∀ tail ∈ tube,
        IsεQuittingRootNash reward tail 0
            (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
          ∀ root : Fin 4 → PMF Bool,
            IsεQuittingRootNash reward tail 0 root →
              root = (quittingAllContinueRoot : Fin 4 → PMF Bool)) ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair <
            quittingTerminalSemanticDebtSum base + epsilon →
          pair.1 ∈ tube := by
  obtain ⟨base, hbase, hminimum, hpositive, _hnash, _hfixed, hbounds⟩ :=
    exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
      reward hno
  have hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who := fun who =>
    (hbounds who).1
  obtain ⟨delta, epsilon, tube, hdelta, hepsilon, htubeOpen,
      hgap, hfiberTube, hfreeze, hnear⟩ :=
    exists_open_exactAllContinueTube_and_debtMoat_minimumFiber
      base hbase hminimum hpositive hnormal
  refine ⟨base, delta, epsilon, tube, hbase, hminimum, hpositive,
    hdelta, hepsilon, htubeOpen, ?_, hfiberTube, hfreeze, hnear⟩
  intro pair hpair who
  exact ⟨hnormal who, by linarith [hgap pair hpair who],
    hgap pair hpair who⟩

end GameTheory
