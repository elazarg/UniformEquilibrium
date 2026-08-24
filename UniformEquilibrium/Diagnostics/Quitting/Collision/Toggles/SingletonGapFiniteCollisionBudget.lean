/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.TerminalGapExactRootMarginalCap
import UniformEquilibrium.Diagnostics.Quitting.TightFaceCollisionSemanticDebt
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption

/-!
# Finite semantic collision budget under a persistent singleton gap

An exact punishment-floor prefix starting from an actual terminal-semantic
carrier point cannot retain one fixed singleton gap indefinitely while also
avoiding a quantitatively interior owner outside that singleton.  In the
remaining rows, a fixed amount of collision mass is forced and pays down the
excess above minimum semantic debt.

This is a literal moving-prefix result: all roots belong to one supplied exact
chronology, and all semantic pairs are recursively prefixed from its actual
source.  It does not independently reset or reselect a semantic endpoint.
-/

noncomputable section

namespace GameTheory

open Math.PMFProduct Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Collision mass contains the event in which a fixed player Quits and at
least one opponent Quits. -/
theorem quitProbability_mul_opponentAbsorptionMass_le_collisionMass
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal * quittingRootOpponentAbsorptionMass root who ≤
      quittingRootCollisionMass root := by
  let rate : ι → ℝ := quittingRootQuitRates root
  let others : Finset ι := Finset.univ.erase who
  have hnot : who ∉ others := by simp [others]
  have huniv : (Finset.univ : Finset ι) = insert who others :=
    (Finset.insert_erase (Finset.mem_univ who)).symm
  have hrate0 : ∀ player, 0 ≤ rate player := fun _ ↦ ENNReal.toReal_nonneg
  have hrate1 : ∀ player, rate player ≤ 1 := fun player ↦
    ENNReal.toReal_mono ENNReal.one_ne_top ((root player).coe_le_one true)
  have hcollisionRest : 0 ≤ collisionMassFormulaOn rate others :=
    collisionMassFormulaOn_nonneg rate others
      (fun player _ ↦ hrate0 player) (fun player _ ↦ hrate1 player)
  have hfactor : 0 ≤ 1 - rate who := sub_nonneg.mpr (hrate1 who)
  rw [quittingRootCollisionMass,
    collisionMass_eq_one_sub_continueMass_sub_singletonMass]
  change (root who true).toReal * quittingRootOpponentAbsorptionMass root who ≤
    collisionMassFormulaOn rate Finset.univ
  rw [huniv, collisionMassFormulaOn_insert rate hnot]
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  change rate who * (1 - ∏ player ∈ others, (1 - rate player)) ≤ _
  nlinarith [mul_nonneg hfactor hcollisionRest]

/-- A uniform Continue floor on every opponent gives the expected deleted
product-survival power bound. -/
theorem pow_card_sub_one_le_one_sub_opponentAbsorptionMass
    [Nonempty ι] (root : ι → PMF Bool) (who : ι) {d : ℝ}
    (hd : 0 ≤ d)
    (hcontinue : ∀ player, d ≤ (root player false).toReal) :
    d ^ (Fintype.card ι - 1) ≤
      1 - quittingRootOpponentAbsorptionMass root who := by
  let others : Finset ι := Finset.univ.erase who
  have hcard : others.card = Fintype.card ι - 1 := by
    simp [others]
  have hproduct : d ^ others.card ≤
      ∏ player ∈ others, (root player false).toReal := by
    have hproduct' : (∏ _player ∈ others, d) ≤
        ∏ player ∈ others, (root player false).toReal :=
      Finset.prod_le_prod (fun _ _ ↦ hd) fun player _ ↦ hcontinue player
    simpa using hproduct'
  rw [quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  have hcoordinate : ∀ player,
      1 - (root player true).toReal = (root player false).toReal := by
    intro player
    have hsum := quittingRoot_continueProbability_add_quitProbability root player
    linarith
  simp_rw [hcoordinate]
  rw [sub_sub_cancel, ← hcard]
  exact hproduct

/-- One exact singleton-gap row either activates a quantitatively interior
distinct owner or carries the fixed collision mass used by the semantic
budget. -/
theorem exactFloorRoot_crossedOwner_or_collisionMass
    [Nontrivial ι]
    (tail : Payoff ι) (root : ι → PMF Bool) (gapOwner : ι)
    {terminalGap M delta : ℝ}
    (hterminalGap : 0 < terminalGap) (hM : 0 < M) (hdelta : 0 < delta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hgap : tail gapOwner ≤
      reward (quittingSingletonTerminal gapOwner) gapOwner - delta)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hupper : ∀ player,
      (root player true).toReal ≤ 1 - terminalGap / (4 * M)) :
    (∃ owner, owner ≠ gapOwner ∧
        delta / (delta + 2 * M) /
            (2 * (Fintype.card ι - 1)) < (root owner true).toReal ∧
        (root owner true).toReal ≤ 1 - terminalGap / (4 * M) ∧
        (root gapOwner true).toReal <
          delta / (delta + 2 * M) / 2) ∨
      delta / (delta + 2 * M) *
          (delta * (terminalGap / (4 * M)) ^ (Fintype.card ι - 1)) /
            (8 * M) ≤ quittingRootCollisionMass root := by
  let d := terminalGap / (4 * M)
  let omega := d ^ (Fintype.card ι - 1)
  let a := delta * omega
  let c := delta / (delta + 2 * M)
  have hd : 0 < d := by dsimp only [d]; positivity
  have homega : 0 < omega := by dsimp only [omega]; positivity
  have ha : 0 < a := mul_pos hdelta homega
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hcardNat : 1 < Fintype.card ι := Fintype.one_lt_card
  have hcardReal : 0 < (Fintype.card ι : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hcardNat)
  have hcontinue : ∀ player, d ≤ (root player false).toReal := by
    intro player
    have hsum := quittingRoot_continueProbability_add_quitProbability root player
    have := hupper player
    dsimp only [d]
    linarith
  have hgapContinue : 0 < (root gapOwner false).toReal :=
    hd.trans_le (hcontinue gapOwner)
  have hendpoint : quittingRootEndpointDifference reward tail root gapOwner ≤ 0 := by
    have hendpointNash : IsεQuittingRootEndpointNash reward tail 0 root :=
      (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward tail 0 root).2 hnash
    have hweighted := (hendpointNash gapOwner).1
    nlinarith [hweighted]
  have hsurvival : omega ≤
      1 - quittingRootOpponentAbsorptionMass root gapOwner := by
    exact pow_card_sub_one_le_one_sub_opponentAbsorptionMass
      root gapOwner hd.le hcontinue
  have hjoining : quittingOutsiderJoiningContribution reward root gapOwner ≤ -a := by
    have hdecomposition :=
      quittingRootEndpointDifference_eq_outsiderNever reward tail root gapOwner
    have hgapSize : delta ≤
        reward (quittingSingletonTerminal gapOwner) gapOwner - tail gapOwner := by
      linarith
    have hsurvivalNonneg :
        0 ≤ 1 - quittingRootOpponentAbsorptionMass root gapOwner := by
      exact quittingRootOpponentContinueMass_nonneg root gapOwner |>.trans_eq
        (quittingRootOpponentContinueMass_eq_one_sub_absorptionMass
          root gapOwner)
    have hweighted' : omega * delta ≤
        (1 - quittingRootOpponentAbsorptionMass root gapOwner) *
          (reward (quittingSingletonTerminal gapOwner) gapOwner - tail gapOwner) := by
      exact (mul_le_mul hsurvival hgapSize hdelta.le hsurvivalNonneg)
    have hweighted : a ≤
        (1 - quittingRootOpponentAbsorptionMass root gapOwner) *
          (reward (quittingSingletonTerminal gapOwner) gapOwner - tail gapOwner) := by
      simpa [a, mul_comm] using hweighted'
    change quittingRootEndpointDifference reward tail root gapOwner =
      (1 - quittingRootOpponentAbsorptionMass root gapOwner) *
          (reward (quittingSingletonTerminal gapOwner) gapOwner - tail gapOwner) +
        quittingOutsiderJoiningContribution reward root gapOwner at hdecomposition
    linarith
  have hopponent : a ≤
      2 * M * quittingRootOpponentAbsorptionMass root gapOwner := by
    have habs :=
      abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
        reward root gapOwner hreward
    have hlower := neg_le_of_abs_le habs
    linarith
  by_cases hownerSmall : (root gapOwner true).toReal < c / 2
  · left
    have habsorption : c ≤ quittingRootAbsorptionMass root := by
      exact gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
        reward tail root gapOwner hdelta hreward hgap
          ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash
            reward tail 0 root).2 hnash)
    have hsum : c ≤ ∑ player, (root player true).toReal :=
      habsorption.trans (quittingRootAbsorptionMass_le_sum_quitRates root)
    let others : Finset ι := Finset.univ.erase gapOwner
    have hsumSplit : (∑ player, (root player true).toReal) =
        (root gapOwner true).toReal +
          ∑ player ∈ others, (root player true).toReal := by
      rw [← Finset.sum_insert (s := others) (f := fun player ↦
        (root player true).toReal) (by simp [others])]
      congr
      exact (Finset.insert_erase (Finset.mem_univ gapOwner)).symm
    have hothers : c / 2 <
        ∑ player ∈ others, (root player true).toReal := by
      rw [hsumSplit] at hsum
      linarith
    have hexists : ∃ owner ∈ others,
        c / (2 * (Fintype.card ι - 1)) < (root owner true).toReal := by
      by_contra hnone
      push Not at hnone
      have hsumUpper :
          (∑ player ∈ others, (root player true).toReal) ≤ c / 2 := by
        calc
          (∑ player ∈ others, (root player true).toReal) ≤
              ∑ _player ∈ others, c / (2 * (Fintype.card ι - 1)) := by
            exact Finset.sum_le_sum fun player hplayer ↦ hnone player hplayer
          _ = c / 2 := by
            have hcard : others.card = Fintype.card ι - 1 := by simp [others]
            rw [Finset.sum_const, nsmul_eq_mul, hcard,
              Nat.cast_sub hcardNat.le]
            norm_num
            field_simp
      exact (not_lt_of_ge hsumUpper) hothers
    obtain ⟨owner, howner, hownerLarge⟩ := hexists
    exact ⟨owner, Finset.ne_of_mem_erase howner, by simpa [c] using hownerLarge,
      hupper owner, by simpa [c] using hownerSmall⟩
  · right
    have hownerLarge : c / 2 ≤ (root gapOwner true).toReal :=
      le_of_not_gt hownerSmall
    have hcollision :=
      quitProbability_mul_opponentAbsorptionMass_le_collisionMass
        root gapOwner
    have hopponent' : a / (2 * M) ≤
        quittingRootOpponentAbsorptionMass root gapOwner := by
      exact (div_le_iff₀ (by positivity : 0 < 2 * M)).2 (by
        nlinarith [hopponent])
    have hproduct : c / 2 * (a / (2 * M)) ≤
        (root gapOwner true).toReal *
          quittingRootOpponentAbsorptionMass root gapOwner := by
      exact mul_le_mul hownerLarge hopponent'
        (by positivity) (by positivity)
    dsimp only [c, a, omega, d] at hproduct ⊢
    calc
      delta / (delta + 2 * M) *
            (delta * (terminalGap / (4 * M)) ^ (Fintype.card ι - 1)) /
          (8 * M) ≤
          delta / (delta + 2 * M) / 2 *
            ((delta * (terminalGap / (4 * M)) ^
              (Fintype.card ι - 1)) / (2 * M)) := by
        field_simp
        norm_num
      _ ≤ (root gapOwner true).toReal *
          quittingRootOpponentAbsorptionMass root gapOwner := hproduct
      _ ≤ quittingRootCollisionMass root := hcollision

/-- The crossed-owner event used by the finite collision budget. -/
def IsQuittingSingletonGapCrossedOwner
    (root : ι → PMF Bool) (gapOwner owner : ι) (c d : ℝ) : Prop :=
  owner ≠ gapOwner ∧
    c / (2 * (Fintype.card ι - 1)) < (root owner true).toReal ∧
    (root owner true).toReal ≤ 1 - d ∧
    (root gapOwner true).toReal < c / 2

/-- **Finite collision-budget escape.**  A literal exact semantic prefix with
a persistent singleton gap must, before exhausting the displayed debt budget,
either move that payoff coordinate by the fixed amount or activate a distinct
quantitatively interior owner.  Both alternatives retain a literal row of
absorption at least `c` in the same supplied prefix. -/
theorem QuittingPunishmentFloorFinitePrefix.singletonGap_finiteCollisionBudget
    [Nontrivial ι]
    (path : QuittingPunishmentFloorFinitePrefix reward)
    (source minimum : QuittingTerminalSemanticPair ι)
    (gapOwner : ι) {terminalGap M delta : ℝ}
    (hterminalGap : 0 < terminalGap) (hM : 0 < M) (hdelta : 0 < delta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexploit : HasTerminalExploitabilityGap reward terminalGap)
    (hsourceCarrier : source ∈ quittingTerminalSemanticCarrier reward)
    (hsourceFst : source.1 = path.value 0)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hsourceGap : source.1 gapOwner ≤
      reward (quittingSingletonTerminal gapOwner) gapOwner - 2 * delta)
    (hhorizon : 0 < path.horizon)
    (hbudget : quittingTerminalSemanticDebtSum source -
        quittingTerminalSemanticDebtSum minimum <
      (path.horizon : ℝ) * quittingTerminalSemanticDebtSum minimum *
        (delta / (delta + 2 * M) *
          (delta * (terminalGap / (4 * M)) ^ (Fintype.card ι - 1)) /
            (8 * M))) :
    (∃ time, 1 ≤ time ∧ time ≤ path.horizon ∧
        reward (quittingSingletonTerminal gapOwner) gapOwner - delta <
          path.value time gapOwner ∧
        delta < path.value time gapOwner - path.value 0 gapOwner ∧
        delta / (delta + 2 * M) ≤
          quittingRootAbsorptionMass (path.roots 0)) ∨
      ∃ time, time < path.horizon ∧ ∃ owner,
        IsQuittingSingletonGapCrossedOwner (path.roots time)
          gapOwner owner (delta / (delta + 2 * M))
            (terminalGap / (4 * M)) ∧
        delta / (delta + 2 * M) ≤
          quittingRootAbsorptionMass (path.roots time) := by
  let c := delta / (delta + 2 * M)
  let d := terminalGap / (4 * M)
  let b := c * (delta * d ^ (Fintype.card ι - 1)) / (8 * M)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hsourceValueGap : path.value 0 gapOwner ≤
      reward (quittingSingletonTerminal gapOwner) gapOwner - 2 * delta := by
    rw [← hsourceFst]
    exact hsourceGap
  have hrootZero : c ≤ quittingRootAbsorptionMass (path.roots 0) := by
    have hgapZero : path.value 0 gapOwner ≤
        reward (quittingSingletonTerminal gapOwner) gapOwner - delta := by
      linarith
    have hnashZero := path.exactNash 0 hhorizon
    exact gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
      reward (path.value 0) (path.roots 0) gapOwner hdelta hreward hgapZero
        ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash
          reward (path.value 0) 0 (path.roots 0)).2 hnashZero)
  by_cases hexcursion : ∃ time, 1 ≤ time ∧ time ≤ path.horizon ∧
      reward (quittingSingletonTerminal gapOwner) gapOwner - delta <
        path.value time gapOwner
  · left
    obtain ⟨time, hone, htime, hhigh⟩ := hexcursion
    refine ⟨time, hone, htime, hhigh, ?_, by simpa [c] using hrootZero⟩
    linarith
  · have hpersistent : ∀ time, time ≤ path.horizon →
        path.value time gapOwner ≤
          reward (quittingSingletonTerminal gapOwner) gapOwner - delta := by
      intro time htime
      by_cases hzero : time = 0
      · subst time
        linarith
      · have hone : 1 ≤ time := Nat.one_le_iff_ne_zero.mpr hzero
        exact le_of_not_gt fun hhigh ↦ hexcursion ⟨time, hone, htime, hhigh⟩
    by_cases hcrossed : ∃ time, time < path.horizon ∧ ∃ owner,
        IsQuittingSingletonGapCrossedOwner (path.roots time)
          gapOwner owner c d
    · right
      obtain ⟨time, htime, owner, hcrossedAt⟩ := hcrossed
      have habsorption : c ≤ quittingRootAbsorptionMass (path.roots time) := by
        exact gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
          reward (path.value time) (path.roots time) gapOwner hdelta hreward
            (hpersistent time htime.le)
            ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash
              reward (path.value time) 0 (path.roots time)).2
                (path.exactNash time htime))
      exact ⟨time, htime, owner, by simpa [c, d] using hcrossedAt,
        by simpa [c] using habsorption⟩
    · have hcollision : ∀ time, time < path.horizon →
          b ≤ quittingRootCollisionMass (path.roots time) := by
        intro time htime
        let pair := path.semanticPrefixPath source time
        have hpairCarrier : pair ∈ quittingTerminalSemanticCarrier reward :=
          path.semanticPrefixPath_mem_carrier source hsourceCarrier time
        have hpairFst : pair.1 = path.value time :=
          path.semanticPrefixPath_fst_eq source hsourceFst time htime.le
        have hbox := quittingTerminalSemanticCarrier_mem_box
          reward pair hreward hpairCarrier
        have htailBound : ∀ player, |path.value time player| ≤ M := by
          intro player
          rw [← hpairFst]
          exact abs_le.mpr ⟨hbox.1.1 player, hbox.1.2 player⟩
        have hfloor : ∀ player,
            quittingPunishmentValue reward player ≤ path.value time player :=
          fun player ↦ quittingPunishmentValue_le_finitePrefixValue
            path time htime.le player
        have hupper : ∀ player,
            ((path.roots time player) true).toReal ≤ 1 - d := by
          intro player
          simpa [d] using
            exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul
              reward (path.value time) (path.roots time) player
                hterminalGap hreward htailBound hfloor hexploit
                  (path.exactNash time htime)
        rcases exactFloorRoot_crossedOwner_or_collisionMass
            (reward := reward) (path.value time) (path.roots time) gapOwner
              hterminalGap hM hdelta hreward (hpersistent time htime.le)
                (path.exactNash time htime) (by simpa [d] using hupper) with
          hcross | hcollisionAt
        · obtain ⟨owner, hne, hlower, hownerUpper, hgapOwnerSmall⟩ := hcross
          exfalso
          apply hcrossed
          refine ⟨time, htime, owner, ?_⟩
          exact ⟨hne, by simpa [c] using hlower, hownerUpper,
            by simpa [c] using hgapOwnerSmall⟩
        · simpa [b, c, d] using hcollisionAt
      have hsumCollision : (path.horizon : ℝ) * b ≤
          ∑ time ∈ Finset.range path.horizon,
            quittingRootCollisionMass (path.roots time) := by
        calc
          (path.horizon : ℝ) * b =
              ∑ _time ∈ Finset.range path.horizon, b := by simp
          _ ≤ ∑ time ∈ Finset.range path.horizon,
              quittingRootCollisionMass (path.roots time) := by
            exact Finset.sum_le_sum fun time htime ↦
              hcollision time (Finset.mem_range.mp htime)
      have hsemantic := path.minimumDebt_mul_collisionMass_le_sourceExcess
        source minimum hsourceCarrier hsourceFst hminimumCarrier hminimum
      have hscaled := mul_le_mul_of_nonneg_left hsumCollision
        hminimumPositive.le
      dsimp only [b, c, d] at hbudget hscaled
      nlinarith [hsemantic, hscaled]

end GameTheory
