/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.CompactQuantitativeAlternatives
import UniformEquilibrium.Quitting.Root.NashDefectContinuity

/-!
# Finite sure-quitter characterization of instant punishment

The instant-punishment branch holds exactly when the finite quitting root game
against the coordinatewise punishment vector has an exact Nash root with a
sure quitter.  The punishment vector is used only as a vector of scalar
min-max values; no joint profile realizing that vector is asserted.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- There is an exact Nash root against the coordinatewise punishment vector,
and one player quits surely at that root. -/
def HasQuittingPunishmentVectorNashRootWithSureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ (quitter : ι) (root : ι → PMF Bool),
    root quitter = PMF.pure true ∧
      ∀ player,
        quittingRootCoordinateNashDefect reward
          (fun who => quittingPunishmentValue reward who) root player = 0

/-- An exact punishment-vector Nash root with a sure quitter produces the
literal constant-row instant-punishment branch. -/
theorem quittingInstantPunishmentεEquilibriumExistence_of_hasPunishmentVectorNashRootWithSureQuitter
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hroot : HasQuittingPunishmentVectorNashRootWithSureQuitter reward) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  obtain ⟨quitter, root, hquit, hdefect⟩ := hroot
  intro ε hε
  have hnash : IsεQuittingRootNash reward
      (fun who => quittingPunishmentValue reward who) 0 root :=
    (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward _ root).2 hdefect
  have hsupport : IsQuittingRootSupportApproxNash reward
      (fun who => quittingPunishmentValue reward who) 0 root :=
    isQuittingRootSupportApproxNash_zero_of_isZeroNash reward _ root hnash
  have hrational : QuittingSimonRationalPayoffAt reward 0
      (fun who => quittingPunishmentValue reward who) := by
    intro who
    simp
  obtain ⟨punishRow, hpunish, hterminal⟩ :=
    exists_oneStagePunishedProfile_of_rational_support_sureQuitter
      reward (fun who => quittingPunishmentValue reward who) root quitter
        (η := 0) (δ := ε) le_rfl hε hrational hsupport hquit
  refine ⟨quitter, root, punishRow, hquit, hpunish, ?_⟩
  simpa using hterminal

/-- The literal instant-punishment branch yields an exact punishment-vector
Nash root with one sure quitter. -/
theorem hasQuittingPunishmentVectorNashRootWithSureQuitter_of_instantPunishmentεEquilibriumExistence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hbranch : QuittingInstantPunishmentεEquilibriumExistence reward) :
    HasQuittingPunishmentVectorNashRootWithSureQuitter reward := by
  let error : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have herrorPos : ∀ n, 0 < error n := by
    intro n
    dsimp only [error]
    positivity
  have herrorTendsto : Tendsto error atTop (nhds 0) := by
    simpa only [error] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hwitness : ∀ n, ∃ (quitter : ι) (root punishRow : ι → PMF Bool),
      root quitter = PMF.pure true ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) (error n)
          (quittingOneStagePunishedProfile reward root punishRow) := by
    intro n
    obtain ⟨quitter, root, punishRow, hquit, _hpunish, hnash⟩ :=
      hbranch (error n) (herrorPos n)
    exact ⟨quitter, root, punishRow, hquit, hnash⟩
  choose quitter root punishRow hquit hnash using hwitness
  letI : Nonempty ι := ⟨quitter 0⟩
  let punishment : Payoff ι :=
    fun who => quittingPunishmentValue reward who
  have hrootNash : ∀ n,
      IsεQuittingRootNash reward punishment (error n) (root n) := by
    intro n
    let continuation := quittingStationaryProfile reward (punishRow n)
    let best := quittingContinuationBestResponse reward continuation
    have hsure : QuittingRootHasSureQuitter (root n) :=
      ⟨quitter n, hquit n⟩
    have hterminal : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (error n)
        (quittingRootThenContinuationProfile reward (root n) continuation) := by
      rw [← quittingOneStagePunishedProfile_eq_rootThenContinuation]
      exact hnash n
    have hbestNash : IsεQuittingRootNash reward best (error n) (root n) :=
      isεQuittingRootNash_of_isεAsymptoticNash_quittingRootThenContinuation
        reward (root n) continuation hsure hterminal
    intro who deviation
    have hpunishmentBest : punishment who ≤ best who := by
      calc
        punishment who = quittingPunishmentValue reward who := rfl
        _ ≤ quittingBestReplyValue reward continuation who :=
          quittingPunishmentValue_le reward who continuation
        _ = best who := by
          dsimp only [best, quittingContinuationBestResponse]
          unfold quittingContinuationBestResponseValue quittingBestReplyValue
          rw [sSup_range]
    have hdeviation := quittingRootExpectedPayoff_continuation_le_add
      reward punishment best (Function.update (root n) who deviation) who
        (δ := 0) le_rfl (by simpa using hpunishmentBest)
    have hprescribed := quittingRootExpectedPayoff_eq_of_hasSureQuitter
      reward (root n) hsure punishment best who
    have hbestBound := hbestNash who deviation
    linarith
  have hdefectBound : ∀ n player,
      quittingRootCoordinateNashDefect reward punishment (root n) player ≤
        error n := by
    intro n player
    exact (isεQuittingRootNash_iff_coordinateNashDefect_le
      reward punishment (error n) (root n)).1 (hrootNash n) player
  obtain ⟨fixed, firstSubsequence, hfirstMono, hfixed⟩ :=
    Math.exists_fixed_label_on_strictMono_subsequence quitter
  let simplexRoot : ℕ → QuittingRootSimplex ι :=
    fun n => quittingSimplexOfRoot (root (firstSubsequence n))
  obtain ⟨limitRoot, secondSubsequence, hsecondMono, hlimitRoot⟩ :=
    CompactSpace.tendsto_subseq simplexRoot
  have hlimitQuitter :
      quittingRootOfSimplex limitRoot fixed = PMF.pure true := by
    have hcoordinate : Tendsto
        (fun n => simplexRoot (secondSubsequence n) fixed) atTop
        (nhds (limitRoot fixed)) :=
      ((continuous_apply fixed).tendsto limitRoot).comp hlimitRoot
    have hconstant : ∀ n,
        simplexRoot (secondSubsequence n) fixed =
          stdSimplexEquiv (PMF.pure true) := by
      intro n
      dsimp only [simplexRoot, quittingSimplexOfRoot]
      rw [← hfixed (secondSubsequence n), hquit]
    have hcoordinateConstant : Tendsto
        (fun n => simplexRoot (secondSubsequence n) fixed) atTop
        (nhds (stdSimplexEquiv (PMF.pure true))) := by
      simpa only [hconstant] using
        (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => stdSimplexEquiv (PMF.pure true)) atTop
          (nhds (stdSimplexEquiv (PMF.pure true))))
    have hlimitCoordinate : limitRoot fixed =
        stdSimplexEquiv (PMF.pure true) :=
      tendsto_nhds_unique hcoordinate hcoordinateConstant
    change (stdSimplexEquiv (α := Bool)).symm (limitRoot fixed) = PMF.pure true
    rw [hlimitCoordinate, Equiv.symm_apply_apply]
  refine ⟨fixed, quittingRootOfSimplex limitRoot, hlimitQuitter, ?_⟩
  intro player
  have hselectedError : Tendsto
      (fun n => error (firstSubsequence (secondSubsequence n))) atTop
      (nhds 0) :=
    herrorTendsto.comp
      (hfirstMono.tendsto_atTop.comp hsecondMono.tendsto_atTop)
  have hselectedDefect : Tendsto
      (fun n => quittingRootCoordinateNashDefect reward punishment
        (root (firstSubsequence (secondSubsequence n))) player) atTop
      (nhds (quittingRootCoordinateNashDefect reward punishment
        (quittingRootOfSimplex limitRoot) player)) := by
    have hpair : Tendsto
        (fun n => (punishment, simplexRoot (secondSubsequence n))) atTop
        (nhds (punishment, limitRoot)) :=
      tendsto_const_nhds.prodMk_nhds hlimitRoot
    have hcontinuous :=
      (continuous_quittingRootCoordinateNashDefect_simplex reward player).tendsto
        (punishment, limitRoot) |>.comp hpair
    change Tendsto
      (fun n => quittingRootCoordinateNashDefect reward punishment
        (quittingRootOfSimplex (simplexRoot (secondSubsequence n))) player)
      atTop (nhds (quittingRootCoordinateNashDefect reward punishment
        (quittingRootOfSimplex limitRoot) player)) at hcontinuous
    simpa only [simplexRoot, quittingRootOfSimplex_simplexOfRoot] using hcontinuous
  have hupper : quittingRootCoordinateNashDefect reward punishment
      (quittingRootOfSimplex limitRoot) player ≤ 0 := by
    apply le_of_tendsto_of_tendsto hselectedDefect hselectedError
    exact Filter.Eventually.of_forall fun n =>
      hdefectBound (firstSubsequence (secondSubsequence n)) player
  exact le_antisymm hupper
    (quittingRootCoordinateNashDefect_nonneg reward punishment
      (quittingRootOfSimplex limitRoot) player)

/-- The literal AKRS S.2 branch is equivalent to the finite exact Nash
condition against the coordinatewise punishment vector. -/
theorem quittingInstantPunishmentεEquilibriumExistence_iff_sureQuitterPunishmentVectorNashRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingInstantPunishmentεEquilibriumExistence reward ↔
      HasQuittingPunishmentVectorNashRootWithSureQuitter reward := by
  exact ⟨
    hasQuittingPunishmentVectorNashRootWithSureQuitter_of_instantPunishmentεEquilibriumExistence,
    quittingInstantPunishmentεEquilibriumExistence_of_hasPunishmentVectorNashRootWithSureQuitter⟩

end GameTheory
