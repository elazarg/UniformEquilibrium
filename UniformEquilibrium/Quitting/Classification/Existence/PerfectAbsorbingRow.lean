/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Classification.SoloExitPreference
import UniformEquilibrium.Quitting.RewardBound
import UniformEquilibrium.Quitting.Root.CoordinateMarginalMixture
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Perfect absorbing rows from one-shot perturbation

Proposition 2.2 of Solan and Vieille, *Quitting games*, Math. Oper. Res. 26
(2001), in this development's one-shot vocabulary.  Under unit solo exit and
a low active Quit endpoint at every absorbing root, every continuation vector
inside the canonical reward cube
with some coordinate at most `1` admits, at every rate `δ ∈ (0, 1]`, a product
row that

* is one-stage `4 * quittingRewardBound reward * δ`-perfect against the
  continuation, in the sense of `QuittingRowεPerfect`;
* absorbs with probability at least `δ`; and
* pays some coordinate at most `1` — the perturbed player, whose prescribed
  value equals its selected pure-Quit payoff, at most `1`.

Capped joint exit is a sufficient special case of the root hypothesis.

The construction starts from an exact mixed Nash row of the one-shot
continuation game, supplied by
`exists_isZeroQuittingRootEndpointNash_simplex`, and pushes one player toward
Quit by the rate `δ`.  The perturbed player's endpoint payoffs are untouched,
because every endpoint computation overwrites that player's own marginal; the
player is either exactly indifferent or already at pure Quit, so its clauses
survive exactly.  Every other player's Quit, Continue, and prescribed payoffs
move by at most `2 * quittingRewardBound reward * δ`, by mixture affinity of
the expected payoff in the perturbed coordinate, so the exact Nash clauses
survive at the doubled tolerance.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Capped joint exit caps every pure-Quit payoff -/

/-- Under capped joint exit, quitting purely pays at most `1` against any
opponents' marginals and any continuation: the realized quitter set always
contains the player. -/
theorem quittingRootQuitPayoff_le_one_of_cappedJointExit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcap : QuittingCappedJointExit reward)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward tail root who ≤ 1 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [← pmfPi_bind_update_pure, expect_bind]
  calc
    expect (pmfPi root) (fun sample =>
        expect (PMF.pure (Function.update sample who true)) (fun action =>
          quittingRootPayoff reward tail action who)) ≤
      expect (pmfPi root) (fun _ => 1) := by
        apply expect_mono
        intro sample
        rw [expect_pure]
        have hmem : who ∈ quittingQuitters (Function.update sample who true) := by
          simp [quittingQuitters]
        have hnonempty :
            (quittingQuitters (Function.update sample who true)).Nonempty :=
          ⟨who, hmem⟩
        unfold quittingRootPayoff
        rw [dif_pos hnonempty]
        exact hcap ⟨_, hnonempty⟩ who hmem
    _ = 1 := expect_const _ _

/-! ## Exact endpoint Nash rows are perfect -/

/-- Under exact endpoint Nash, pure Quit never beats the prescribed value. -/
theorem quittingRootQuitPayoff_le_successorPayoff_of_isZeroEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool}
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) (who : ι) :
    quittingRootQuitPayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have hsub := quittingRootQuitPayoff_sub_successorPayoff reward tail root who
  have hclause := (hnash who).1
  linarith

/-- Under exact endpoint Nash, pure Continue never beats the prescribed
value. -/
theorem quittingRootContinuePayoff_le_successorPayoff_of_isZeroEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool}
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) (who : ι) :
    quittingRootContinuePayoff reward tail root who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have hsub := quittingRootContinuePayoff_sub_successorPayoff reward tail root who
  have hclause := (hnash who).2
  linarith

/-- Under exact endpoint Nash, a positive Quit weight makes the prescribed
value exactly the pure-Quit payoff. -/
theorem quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool}
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) (who : ι)
    (hne : root who true ≠ 0) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootQuitPayoff reward tail root who := by
  have hqpos : 0 < (root who true).toReal :=
    ENNReal.toReal_pos hne (PMF.apply_ne_top _ _)
  have hdiff : 0 ≤ quittingRootEndpointDifference reward tail root who :=
    nonneg_of_mul_nonneg_left (by simpa [mul_comm] using (hnash who).2) hqpos
  have hsub := quittingRootQuitPayoff_sub_successorPayoff reward tail root who
  have hclause := (hnash who).1
  have hproduct : 0 ≤ (root who false).toReal *
      quittingRootEndpointDifference reward tail root who :=
    mul_nonneg ENNReal.toReal_nonneg hdiff
  linarith

/-- Under exact endpoint Nash, a positive Continue weight makes the prescribed
value exactly the pure-Continue payoff. -/
theorem quittingRootSuccessorPayoff_eq_continuePayoff_of_isZeroEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool}
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) (who : ι)
    (hne : root who false ≠ 0) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootContinuePayoff reward tail root who := by
  have hcpos : 0 < (root who false).toReal :=
    ENNReal.toReal_pos hne (PMF.apply_ne_top _ _)
  have hdiff : quittingRootEndpointDifference reward tail root who ≤ 0 :=
    nonpos_of_mul_nonpos_left (by simpa [mul_comm] using (hnash who).1) hcpos
  have hsub := quittingRootContinuePayoff_sub_successorPayoff reward tail root who
  have hclause := (hnash who).2
  have hproduct : (root who true).toReal *
      quittingRootEndpointDifference reward tail root who ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hdiff
  linarith

/-- An exact endpoint Nash row is one-stage `ε`-perfect at every `ε ≥ 0`. -/
theorem quittingRowεPerfect_of_isZeroEndpointNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool}
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    {ε : ℝ} (hε : 0 ≤ ε) :
    QuittingRowεPerfect reward tail root ε := by
  intro who
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := quittingRootQuitPayoff_le_successorPayoff_of_isZeroEndpointNash
      hnash who
    linarith
  · have := quittingRootContinuePayoff_le_successorPayoff_of_isZeroEndpointNash
      hnash who
    linarith
  · intro hne
    have := quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
      hnash who hne
    linarith
  · intro hne
    have := quittingRootSuccessorPayoff_eq_continuePayoff_of_isZeroEndpointNash
      hnash who hne
    linarith

/-! ## Detecting a positive-quit player -/

omit [DecidableEq ι] in
/-- A row whose all-continue mass falls short of one has a player with
positive Quit probability. -/
theorem exists_quitProbability_pos_of_continueMass_lt_one
    {root : ι → PMF Bool}
    (hmass : quittingStationaryContinueMass root < 1) :
    ∃ who, 0 < (root who true).toReal := by
  by_contra hnone
  push Not at hnone
  have hone : ∀ who, (root who false).toReal = 1 := by
    intro who
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    have hle := hnone who
    have hge : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
    linarith
  rw [quittingStationaryContinueMass_eq_prod_continueProbability] at hmass
  simp [hone] at hmass

/-! ## The low active Quit endpoint condition -/

/-- Every absorbing product root has an active player whose pure-Quit
endpoint is at most the unit singleton level.  The zero tail is canonical:
pure Quit does not read the continuation annotation. -/
def HasLowActiveQuittingRootQuitPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ root : ι → PMF Bool, 0 < quittingRootAbsorptionMass root →
    ∃ who, 0 < (root who true).toReal ∧
      quittingRootQuitPayoff reward (0 : Payoff ι) root who ≤ 1

/-- Capped joint exit implies the rootwise low-endpoint condition. -/
theorem hasLowActiveQuittingRootQuitPayoff_of_cappedJointExit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcap : QuittingCappedJointExit reward) :
    HasLowActiveQuittingRootQuitPayoff reward := by
  intro root habsorption
  have hmass : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  obtain ⟨who, hwho⟩ :=
    exists_quitProbability_pos_of_continueMass_lt_one hmass
  exact ⟨who, hwho,
    quittingRootQuitPayoff_le_one_of_cappedJointExit hcap 0 root who⟩

/-- The low endpoint can be read against any continuation payoff. -/
theorem HasLowActiveQuittingRootQuitPayoff.exists_for_tail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hlow : HasLowActiveQuittingRootQuitPayoff reward)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    ∃ who, 0 < (root who true).toReal ∧
      quittingRootQuitPayoff reward tail root who ≤ 1 := by
  obtain ⟨who, hactive, hquit⟩ := hlow root habsorption
  refine ⟨who, hactive, ?_⟩
  rw [quittingRootQuitPayoff_continuation_invariant reward tail 0 root who]
  exact hquit

/-! ## The perturbed row -/

/-- **The Solan–Vieille one-shot perturbation** (Solan and Vieille, *Quitting
games*, Math. Oper. Res. 26 (2001), Proposition 2.2).  Under unit solo exit
and the low-active-Quit root condition, every continuation vector inside the
canonical reward cube with some coordinate at most `1` admits, at every rate `δ ∈ (0, 1]`, a
product row that is one-stage `4 * quittingRewardBound reward * δ`-perfect
against the continuation, absorbs with probability at least `δ`, and pays
some coordinate at most `1`. -/
theorem exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hlowRoot : HasLowActiveQuittingRootQuitPayoff reward)
    (tail : Payoff ι)
    (htail : ∀ who, |tail who| ≤ quittingRewardBound reward)
    (hlow : ∃ who, tail who ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ root : ι → PMF Bool,
      QuittingRowεPerfect reward tail root
          (4 * quittingRewardBound reward * δ) ∧
        δ ≤ quittingRootAbsorptionMass root ∧
        ∃ who, quittingRootSuccessorPayoff reward tail root who ≤ 1 := by
  classical
  set R := quittingRewardBound reward with hR
  have hR0 : 0 ≤ R := quittingRewardBound_nonneg reward
  have hrewardR : ∀ terminal player, |reward terminal player| ≤ R :=
    abs_reward_le_quittingRewardBound reward
  obtain ⟨simplexBase, hbaseNash⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward tail
  set base := quittingRootOfSimplex simplexBase with hbase
  -- Select the player to perturb: exactly indifferent, or already at pure Quit.
  have hselect : ∃ who : ι,
      (quittingRootQuitPayoff reward tail base who =
          quittingRootContinuePayoff reward tail base who ∨
        (base who true).toReal = 1) ∧
      quittingRootQuitPayoff reward tail base who ≤ 1 := by
    rcases lt_or_eq_of_le (quittingStationaryContinueMass_le_one base) with
      hlt | heq
    · have habsorption : 0 < quittingRootAbsorptionMass base := by
        unfold quittingRootAbsorptionMass
        linarith
      obtain ⟨who, hpos, hquitLow⟩ :=
        hlowRoot.exists_for_tail tail base habsorption
      have hdiff : 0 ≤ quittingRootEndpointDifference reward tail base who :=
        nonneg_of_mul_nonneg_left
          (by simpa [mul_comm] using (hbaseNash who).2) hpos
      by_cases hzero : (base who false).toReal = 0
      · refine ⟨who, Or.inr ?_, hquitLow⟩
        have hsum := quittingRoot_continueProbability_add_quitProbability base who
        linarith
      · refine ⟨who, Or.inl ?_, hquitLow⟩
        have hcpos : 0 < (base who false).toReal :=
          lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
        have hdiff' : quittingRootEndpointDifference reward tail base who ≤ 0 :=
          nonpos_of_mul_nonpos_left
            (by simpa [mul_comm] using (hbaseNash who).1) hcpos
        have hdiff0 : quittingRootEndpointDifference reward tail base who = 0 :=
          le_antisymm hdiff' hdiff
        unfold quittingRootEndpointDifference at hdiff0
        linarith
    · obtain ⟨who, hwho⟩ := hlow
      have hall : ∀ player, base player = PMF.pure false := fun player =>
        eq_pure_false_of_quittingStationaryContinueMass_eq_one heq player
      have hbaseAll : base = (quittingAllContinueRoot : ι → PMF Bool) :=
        funext fun player => hall player
      have hclause := (hbaseNash who).1
      rw [hbaseAll] at hclause
      rw [quittingRootEndpointDifference_allContinueRoot] at hclause
      have hcontinueWeight :
          ((quittingAllContinueRoot who : PMF Bool) false).toReal = 1 := by
        simp [quittingAllContinueRoot]
      rw [hcontinueWeight, one_mul] at hclause
      have hsolo : reward (quittingSingletonTerminal who) who = 1 := hunit who
      have hquitLow : quittingRootQuitPayoff reward tail base who ≤ 1 := by
        rw [hbaseAll, quittingRootQuitPayoff_allContinueRoot, hsolo]
      refine ⟨who, Or.inl ?_, hquitLow⟩
      rw [hbaseAll, quittingRootQuitPayoff_allContinueRoot,
        quittingRootContinuePayoff_allContinueRoot, hsolo]
      linarith [hsolo ▸ hclause]
  obtain ⟨chosen, hchosen, hchosenLow⟩ := hselect
  set q := (base chosen true).toReal with hqdef
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := by
    have hle := ENNReal.toReal_mono ENNReal.one_ne_top
      ((base chosen).coe_le_one true)
    simpa using hle
  set q' := δ + (1 - δ) * q with hq'def
  have hq'0 : 0 ≤ q' := by nlinarith
  have hq'1 : q' ≤ 1 := by nlinarith
  have hδq' : δ ≤ q' := by nlinarith
  set coin := quittingHazardCoin q' hq'0 hq'1 with hcoindef
  set perturbed := Function.update base chosen coin with hperturbed
  have hperturbed_chosen : perturbed chosen = coin := by
    rw [hperturbed]
    exact Function.update_self chosen coin base
  have hperturbed_other : ∀ who, who ≠ chosen → perturbed who = base who := by
    intro who hne
    rw [hperturbed]
    exact Function.update_of_ne hne coin base
  have hcoin_true : (coin true).toReal = q' := by
    rw [hcoindef]
    exact quittingHazardCoin_true_toReal q' hq'0 hq'1
  have hcoin_false : (coin false).toReal = 1 - q' := by
    rw [hcoindef]
    exact quittingHazardCoin_false_toReal q' hq'0 hq'1
  have hqmove : |(coin true).toReal - (base chosen true).toReal| ≤ δ := by
    rw [hcoin_true, ← hqdef]
    have hgap : q' - q = δ * (1 - q) := by
      rw [hq'def]
      ring
    rw [show q' - q = δ * (1 - q) from hgap, abs_of_nonneg
      (mul_nonneg hδ0.le (by linarith))]
    nlinarith
  -- The chosen player's endpoint payoffs are untouched by the perturbation.
  have hquit_chosen : quittingRootQuitPayoff reward tail perturbed chosen =
      quittingRootQuitPayoff reward tail base chosen := by
    unfold quittingRootQuitPayoff
    rw [hperturbed, Function.update_idem]
  have hcont_chosen : quittingRootContinuePayoff reward tail perturbed chosen =
      quittingRootContinuePayoff reward tail base chosen := by
    unfold quittingRootContinuePayoff
    rw [hperturbed, Function.update_idem]
  have hsucc_chosen : quittingRootSuccessorPayoff reward tail perturbed chosen =
      q' * quittingRootQuitPayoff reward tail base chosen +
        (1 - q') * quittingRootContinuePayoff reward tail base chosen := by
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hperturbed_chosen,
      hcoin_true, hcoin_false, hquit_chosen, hcont_chosen]
  -- In both selection branches the perturbed value is the pure-Quit payoff.
  have hsucc_chosen_quit :
      quittingRootSuccessorPayoff reward tail perturbed chosen =
        quittingRootQuitPayoff reward tail base chosen := by
    rcases hchosen with hind | hpure
    · rw [hsucc_chosen, ← hind]
      ring
    · have hq'one : q' = 1 := by
        rw [hq'def, ← hqdef] at *
        rw [show q = 1 from hpure ▸ rfl] at hq'def ⊢
        rw [hq'def]
        ring
      rw [hsucc_chosen, hq'one]
      ring
  -- Every other player's three payoffs move by at most `2 R δ`.
  have hsuccmove : ∀ who : ι,
      |quittingRootSuccessorPayoff reward tail perturbed who -
        quittingRootSuccessorPayoff reward tail base who| ≤ δ * (2 * R) := by
    intro who
    have h := abs_quittingRootExpectedPayoff_update_coord_sub_self_le reward
      tail base chosen who coin hrewardR htail
    have hmul := mul_le_mul_of_nonneg_right hqmove
      (by linarith : (0 : ℝ) ≤ 2 * R)
    calc |quittingRootSuccessorPayoff reward tail perturbed who -
          quittingRootSuccessorPayoff reward tail base who| =
        |quittingRootExpectedPayoff reward tail
            (Function.update base chosen coin) who -
          quittingRootExpectedPayoff reward tail base who| := by
            rw [hperturbed]
            rfl
      _ ≤ |(coin true).toReal - (base chosen true).toReal| * (2 * R) := h
      _ ≤ δ * (2 * R) := hmul
  have hendpointmove : ∀ (who : ι), who ≠ chosen → ∀ b : Bool,
      |quittingRootExpectedPayoff reward tail
          (Function.update perturbed who (PMF.pure b)) who -
        quittingRootExpectedPayoff reward tail
          (Function.update base who (PMF.pure b)) who| ≤ δ * (2 * R) := by
    intro who hne b
    have hcomm : Function.update perturbed who (PMF.pure b) =
        Function.update (Function.update base who (PMF.pure b)) chosen coin := by
      rw [hperturbed]
      exact Function.update_comm (Ne.symm hne) coin (PMF.pure b) base
    have hcoord : Function.update base who (PMF.pure b) chosen = base chosen :=
      Function.update_of_ne (Ne.symm hne) (PMF.pure b) base
    have h := abs_quittingRootExpectedPayoff_update_coord_sub_self_le reward
      tail (Function.update base who (PMF.pure b)) chosen who coin hrewardR htail
    rw [hcoord] at h
    rw [hcomm]
    calc |quittingRootExpectedPayoff reward tail
            (Function.update (Function.update base who (PMF.pure b))
              chosen coin) who -
          quittingRootExpectedPayoff reward tail
            (Function.update base who (PMF.pure b)) who| ≤
        |(coin true).toReal - (base chosen true).toReal| * (2 * R) := h
      _ ≤ δ * (2 * R) := mul_le_mul_of_nonneg_right hqmove (by linarith)
  have hε0 : 0 ≤ 4 * R * δ :=
    mul_nonneg (mul_nonneg (by norm_num) hR0) hδ0.le
  refine ⟨perturbed, ?_, ?_, ⟨chosen, ?_⟩⟩
  · -- One-stage perfectness at tolerance `4 R δ`.
    intro who
    by_cases hwho : who = chosen
    · subst hwho
      refine ⟨?_, ?_, fun _ => ?_, ?_⟩
      · rw [hquit_chosen, hsucc_chosen_quit]
        linarith
      · rw [hcont_chosen, hsucc_chosen_quit]
        rcases hchosen with hind | hpure
        · rw [← hind]
          linarith
        · have hqpos : 0 < (base who true).toReal := by
            rw [← hqdef, hpure]
            norm_num
          have hdiff : 0 ≤ quittingRootEndpointDifference reward tail base who :=
            nonneg_of_mul_nonneg_left
              (by simpa [mul_comm] using (hbaseNash who).2) hqpos
          unfold quittingRootEndpointDifference at hdiff
          linarith
      · rw [hquit_chosen, hsucc_chosen_quit]
        linarith
      · intro hfalse
        rcases hchosen with hind | hpure
        · rw [hcont_chosen, hsucc_chosen_quit, ← hind]
          linarith
        · exfalso
          apply hfalse
          have hq'one : q' = 1 := by
            rw [hq'def, hpure]
            ring
          rw [hperturbed_chosen, hcoindef]
          unfold quittingHazardCoin
          rw [PMF.ofFintype_apply]
          simp [hq'one]
    · -- An unperturbed player inherits the exact Nash clauses at `4 R δ`.
      have hrootwho : perturbed who = base who := hperturbed_other who hwho
      have hquitmove := hendpointmove who hwho true
      have hcontmove := hendpointmove who hwho false
      have hsuccmovewho := hsuccmove who
      have hquitperturbed : quittingRootQuitPayoff reward tail perturbed who =
          quittingRootExpectedPayoff reward tail
            (Function.update perturbed who (PMF.pure true)) who := rfl
      have hquitbase : quittingRootQuitPayoff reward tail base who =
          quittingRootExpectedPayoff reward tail
            (Function.update base who (PMF.pure true)) who := rfl
      have hcontperturbed :
          quittingRootContinuePayoff reward tail perturbed who =
            quittingRootExpectedPayoff reward tail
              (Function.update perturbed who (PMF.pure false)) who := rfl
      have hcontbase : quittingRootContinuePayoff reward tail base who =
          quittingRootExpectedPayoff reward tail
            (Function.update base who (PMF.pure false)) who := rfl
      have hquitgap : |quittingRootQuitPayoff reward tail perturbed who -
          quittingRootQuitPayoff reward tail base who| ≤ δ * (2 * R) := by
        rw [hquitperturbed, hquitbase]
        exact hquitmove
      have hcontgap : |quittingRootContinuePayoff reward tail perturbed who -
          quittingRootContinuePayoff reward tail base who| ≤ δ * (2 * R) := by
        rw [hcontperturbed, hcontbase]
        exact hcontmove
      have hquitgap' := abs_le.mp hquitgap
      have hcontgap' := abs_le.mp hcontgap
      have hsuccgap' := abs_le.mp hsuccmovewho
      have hquitbase_le :=
        quittingRootQuitPayoff_le_successorPayoff_of_isZeroEndpointNash
          hbaseNash who
      have hcontbase_le :=
        quittingRootContinuePayoff_le_successorPayoff_of_isZeroEndpointNash
          hbaseNash who
      refine ⟨by linarith, by linarith, ?_, ?_⟩
      · intro hne
        rw [hrootwho] at hne
        have heq :=
          quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
            hbaseNash who hne
        linarith
      · intro hne
        rw [hrootwho] at hne
        have heq :=
          quittingRootSuccessorPayoff_eq_continuePayoff_of_isZeroEndpointNash
            hbaseNash who hne
        linarith
  · -- Absorption at least `δ`.
    have hmassle : quittingStationaryContinueMass perturbed ≤
        (perturbed chosen false).toReal :=
      quittingStationaryContinueMass_le_ownContinueProbability perturbed chosen
    have hchosenfalse : (perturbed chosen false).toReal = 1 - q' := by
      rw [hperturbed_chosen]
      exact hcoin_false
    unfold quittingRootAbsorptionMass
    rw [hchosenfalse] at hmassle
    linarith
  · -- The perturbed player's value is its selected low pure-Quit payoff.
    rw [hsucc_chosen_quit]
    exact hchosenLow

/-- Unit solo exit and capped joint rewards imply the one-shot perturbation conclusion. -/
theorem exists_quittingPerfectAbsorbingRow_of_soloExitPreference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward)
    (tail : Payoff ι)
    (htail : ∀ who, |tail who| ≤ quittingRewardBound reward)
    (hlow : ∃ who, tail who ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ root : ι → PMF Bool,
      QuittingRowεPerfect reward tail root
          (4 * quittingRewardBound reward * δ) ∧
        δ ≤ quittingRootAbsorptionMass root ∧
        ∃ who, quittingRootSuccessorPayoff reward tail root who ≤ 1 :=
  exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff hunit
    (hasLowActiveQuittingRootQuitPayoff_of_cappedJointExit hcap)
    tail htail hlow hδ0 hδ1
