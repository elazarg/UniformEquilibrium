/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportProjectiveQBarResidual
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonTightMinimumFaceIteration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauNashMoat
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Bellman.Finite.AllContinueBasinRigidity
import UniformEquilibrium.Quitting.Root.SimplexCoalitionMass

/-!
# Strict minimum-plateau isolation for four-player quitting games

A literal `Fin 4` counterexample would have a positive minimum
terminal-semantic all-Continue plateau.  Punishment normality on the same
reward table excludes both the fixed-owner solo spine and every
singleton-tight coordinate, so the plateau lies strictly above every own
singleton reward.

At that plateau the exact-root critical-face theorem makes all-Continue the
unique exact root.  A reverse singleton-gap estimate and the existing robust
Nash-defect moat then freeze the exact root on a neighborhood of the plateau
tail.  This is oriented at the continuation/tail: it does not exclude an
incoming edge whose tail is nonlocally outside the neighborhood.

No nonlocal return producer, chronological repayment, or uniform-equilibrium
closure is proved here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

/-- A hypothetical four-player counterexample has a same-table positive
minimum all-Continue plateau which is punishment-normal and strictly above
every own singleton reward. -/
theorem exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ pair : QuittingTerminalSemanticPair (Fin 4),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum pair ∧
      IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair = pair ∧
      ∀ who,
        quittingPunishmentValue reward who ≤
            reward (quittingSingletonTerminal who) who ∧
          reward (quittingSingletonTerminal who) who < pair.1 who := by
  have hresidual : Nonempty
      (FinFourQuantitativeFullSupportHardResidual reward
        (quittingRewardBound reward)) := by
    rcases uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual
        reward (abs_reward_le_quittingRewardBound reward) with hpayoff | hresidual
    · exact (hno hpayoff).elim
    · exact hresidual
  let residual := Classical.choice hresidual
  have hnormal : ∀ who,
      quittingPunishmentValue reward who ≤
        reward (quittingSingletonTerminal who) who := by
    intro who
    simpa [IsQuittingNormalPlayer, quittingSoloSelfPayoff,
      quittingSingletonTerminal] using residual.all_punishmentNormal who
  rcases
      exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff
        reward hno with hplateau | hspine
  · obtain ⟨pair, hpair, hminimum, hcoordinatePositive, hnash, hfixed⟩ :=
      hplateau
    have hdebtNonneg : ∀ who,
        0 ≤ quittingTerminalSemanticDebt pair who :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
    have hsumPositive : 0 < quittingTerminalSemanticDebtSum pair := by
      obtain ⟨who, hwho⟩ := hcoordinatePositive
      unfold quittingTerminalSemanticDebtSum
      exact Finset.sum_pos' (fun player _ => hdebtNonneg player)
        ⟨who, Finset.mem_univ who, hwho⟩
    have hsingletonLe : ∀ who,
        reward (quittingSingletonTerminal who) who ≤ pair.1 who :=
      (isZeroQuittingRootNash_allContinue_iff_singleton_le reward pair.1).mp hnash
    refine ⟨pair, hpair, hminimum, hsumPositive, hnash, hfixed, ?_⟩
    intro who
    refine ⟨hnormal who, lt_of_le_of_ne (hsingletonLe who) ?_⟩
    intro heq
    have htight : pair.1 who =
        reward (quittingSingletonTerminal who) who := heq.symm
    have hownerDebt :=
      minimumTerminalSemantic_debt_eq_sum_of_singleton_tight
        (reward := reward) pair who hpair hminimum hsumPositive htight
    have houtside : ∀ other, other ≠ who →
        quittingTerminalSemanticDebt pair other = 0 := by
      intro other hother
      have hsumErase : ∑ player ∈ (Finset.univ.erase who),
          quittingTerminalSemanticDebt pair player = 0 := by
        have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 4))
          (fun player : Fin 4 => quittingTerminalSemanticDebt pair player)
          (Finset.mem_univ who)
        change (∑ player ∈ Finset.univ.erase who,
              quittingTerminalSemanticDebt pair player +
            quittingTerminalSemanticDebt pair who) =
          ∑ player ∈ (Finset.univ : Finset (Fin 4)),
            quittingTerminalSemanticDebt pair player at hsplit
        rw [show (∑ player ∈ (Finset.univ : Finset (Fin 4)),
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
      debt_pos := hsumPositive
      owner_tight := by
        simpa [quittingSoloReward, quittingSingletonTerminal] using htight
      outsider_debt := houtside }
    let gain := quittingSingletonCollisionGainMax reward who
    have hgain : 0 ≤ gain := by
      dsimp only [gain, quittingSingletonCollisionGainMax]
      exact le_trans (by simp)
        (QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun other : Fin 4 => if other = who then 0 else
            max 0 (quittingSingletonCollisionReward reward who other -
              quittingSoloReward reward who other)) who)
    have hdenom : 0 < quittingTerminalSemanticDebtSum pair + gain := by
      linarith
    let ratio := quittingTerminalSemanticDebtSum pair /
      (quittingTerminalSemanticDebtSum pair + gain)
    have hratioPos : 0 < ratio := by
      exact div_pos hsumPositive hdenom
    have hratioOne : ratio ≤ 1 := by
      exact (div_le_one hdenom).2 (by linarith)
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
        pair who hsumPositive hratePos hrateOne hrateBound
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
  · obtain ⟨pair, root, owner, debt, hdebt, hpair, hminimum, hprefix,
        hnash, _hnotAll, hnoPlateau, _hownerDebt, _houtsiderDebt, hquit,
        hpure, hsoloRoot, _hopponentSurvival, _htight, _hblocker⟩ := hspine
    by_cases hsurvival : Tendsto
        (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0)
    · by_cases hcontinue : (root 0 owner false).toReal = 0
      · have hendpoint := isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero
          (reward := reward) (pair 1).1 (root 0) owner (hnash 0)
            (hpure 0) hcontinue
        have hrootZero := hsoloRoot 0
        rw [hrootZero] at hendpoint
        have hsoloLt :=
          residual.witness.soloReward_lt_punishmentValue_of_soloEndpointNash
            owner (root 0 owner) (hquit 0) hendpoint
        have hnormalOwner := hnormal owner
        change quittingPunishmentValue reward owner ≤
          quittingSoloReward reward owner owner at hnormalOwner
        exact (not_lt_of_ge hnormalOwner hsoloLt).elim
      · have hcontinuePos : 0 < (root 0 owner false).toReal :=
          lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcontinue)
        have hrestriction :=
          residual.witness.atomic_restrictions_of_soloSemanticSpine_survival_zero
            pair root owner hpair hprefix hnash hpure (hquit 0)
              hcontinuePos hsurvival
        have hnormalOwner := hnormal owner
        change quittingPunishmentValue reward owner ≤
          quittingSoloReward reward owner owner at hnormalOwner
        exact (not_lt_of_ge hnormalOwner hrestriction.2).elim
    · obtain ⟨lower, hlower, hsurvivalLower⟩ :=
        exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero
          root owner 0 hsurvival
      have hcandidate :=
        exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower
          (reward := reward) pair root owner hpair hminimum hnash hpure
            hlower hsurvivalLower
      exact (hnoPlateau hcandidate).elim

/-- At a positive minimum plateau strictly above every own singleton reward,
all-Continue is the unique exact root at the plateau tail. -/
theorem minimumTerminalSemantic_exactNash_eq_allContinue_of_strictSingleton
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hstrict : ∀ who,
      reward (quittingSingletonTerminal who) who < pair.1 who)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  apply minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate
    pair root hpair hminimum hpositive hnash
  intro who hgate
  rcases hgate with ⟨hdebt, hslack⟩
  unfold quittingTerminalSemanticDebt at hdebt
  unfold quittingTerminalSemanticSingletonSlack at hslack
  have heq : pair.1 who =
      reward (quittingSingletonTerminal who) who := by
    linarith
  exact (ne_of_gt (hstrict who)) heq

/-- Reverse singleton-gap estimate.  If a player uses Quit with positive
probability while its tail lies strictly above its singleton payoff, exact
Nash can support that action only through a quantitatively positive amount
of opponent absorption. -/
theorem gap_div_le_quittingRootOpponentAbsorptionMass_of_isZeroNash_of_quit_pos
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : gap ≤ tail who -
      reward (quittingSingletonTerminal who) who)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hquit : 0 < (root who true).toReal) :
    gap / (gap + 2 * M) ≤
      quittingRootOpponentAbsorptionMass root who := by
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  let opponentMass := quittingRootOpponentAbsorptionMass root who
  have hmassNonneg : 0 ≤ opponentMass := by
    unfold opponentMass quittingRootOpponentAbsorptionMass
      quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_le_one
      (Function.update root who (PMF.pure false))]
  have hmassLeOne : opponentMass ≤ 1 := by
    unfold opponentMass quittingRootOpponentAbsorptionMass
      quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg
      (Function.update root who (PMF.pure false))]
  have hendpoint : IsεQuittingRootEndpointNash reward tail 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  have hdiffNonneg : 0 ≤
      quittingRootEndpointDifference reward tail root who := by
    have hproduct := (hendpoint who).2
    simp only [neg_zero] at hproduct
    exact nonneg_of_mul_nonneg_left
      (by simpa only [mul_comm] using hproduct) hquit
  have hjoining :=
    abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
      reward root who hreward
  have hjoiningUpper : quittingOutsiderJoiningContribution reward root who ≤
      2 * M * opponentMass := by
    exact (le_abs_self _).trans (by simpa [opponentMass] using hjoining)
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever reward tail root who
  rw [show quittingRootAbsorptionMass
      (Function.update root who (PMF.pure false)) = opponentMass by rfl]
    at hdecomposition
  have hsurvivalNonneg : 0 ≤ 1 - opponentMass := by linarith
  have hweightedGap : (1 - opponentMass) * gap ≤
      (1 - opponentMass) *
        (tail who - reward (quittingSingletonTerminal who) who) :=
    mul_le_mul_of_nonneg_left htail hsurvivalNonneg
  have hcharge : gap ≤ opponentMass * (gap + 2 * M) := by
    nlinarith [hdiffNonneg, hjoiningUpper, hweightedGap]
  have hdenom : 0 < gap + 2 * M := by linarith
  exact (div_le_iff₀ hdenom).2 (by simpa [mul_comm] using hcharge)

/-- The reviewed `delta/(delta+4M)` form of the reverse singleton-gap
estimate. -/
theorem delta_div_le_quittingRootOpponentAbsorptionMass_of_isZeroNash_of_quit_pos
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M delta : ℝ} (hdelta : 0 < delta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (htail : delta / 2 ≤ tail who -
      reward (quittingSingletonTerminal who) who)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hquit : 0 < (root who true).toReal) :
    delta / (delta + 4 * M) ≤
      quittingRootOpponentAbsorptionMass root who := by
  have hM : 0 ≤ M :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hlower :=
    gap_div_le_quittingRootOpponentAbsorptionMass_of_isZeroNash_of_quit_pos
      reward tail root who (by linarith : 0 < delta / 2) hreward
        htail hnash hquit
  have hleft : delta / (delta + 4 * M) =
      (delta / 2) / (delta / 2 + 2 * M) := by
    have hdenom : delta + 4 * M ≠ 0 := by
      have : 0 < delta + 4 * M := by linarith
      exact ne_of_gt this
    have hhalfDenom : delta / 2 + 2 * M ≠ 0 := by
      have : 0 < delta / 2 + 2 * M := by linarith
      exact ne_of_gt this
    field_simp
    ring
  rw [hleft]
  exact hlower

/-- A non-all-Continue product root has a player with positive displayed Quit
probability. -/
theorem exists_quitProbability_pos_of_ne_allContinue
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (root : ι → PMF Bool)
    (hne : root ≠ (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ who, 0 < (root who true).toReal := by
  by_contra hnone
  push Not at hnone
  apply hne
  funext who
  have hzero : (root who true).toReal = 0 :=
    le_antisymm (hnone who) ENNReal.toReal_nonneg
  simpa [quittingAllContinueRoot] using
    Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      (root who) hzero

/-- A unique all-Continue exact root at a strictly singleton-separated tail
persists on a neighborhood.  The proof composes the reverse singleton-gap
absorption estimate with the robust Nash-defect moat. -/
theorem eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : Payoff ι) {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ who, delta ≤ cap who -
      reward (quittingSingletonTerminal who) who)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∀ᶠ nearbyTail in 𝓝 cap,
      IsεQuittingRootNash reward nearbyTail 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        ∀ root : ι → PMF Bool,
          IsεQuittingRootNash reward nearbyTail 0 root →
            root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let M := quittingRewardBound reward
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hreward : ∀ S player, |reward S player| ≤ M :=
    abs_reward_le_quittingRewardBound reward
  let eta := delta / (delta + 4 * M)
  have heta : 0 < eta := by
    dsimp only [eta]
    exact div_pos hdelta (by linarith)
  have hnearGap : ∀ᶠ nearbyTail in 𝓝 cap,
      ∀ who, delta / 2 < nearbyTail who -
        reward (quittingSingletonTerminal who) who := by
    apply Filter.eventually_all.mpr
    intro who
    have htendsto : Tendsto
        (fun tail : Payoff ι => tail who -
          reward (quittingSingletonTerminal who) who)
        (𝓝 cap) (𝓝 (cap who -
          reward (quittingSingletonTerminal who) who)) :=
      (continuous_apply who).sub continuous_const |>.continuousAt
    exact htendsto.eventually
      (Ioi_mem_nhds (by linarith [hgap who]))
  have hnearMoat : ∀ᶠ nearbyTail in 𝓝 cap,
      ∀ owner root,
        eta ≤ quittingRootOpponentAbsorptionMass
          (quittingRootOfSimplex root) owner →
        0 < quittingRootTotalNashDefect reward nearbyTail
          (quittingRootOfSimplex root) := by
    apply Filter.eventually_all.mpr
    intro owner
    obtain ⟨moat, hmoat, hnear⟩ :=
      exists_eventually_totalNashDefect_moat_of_unique_allContinue_opponentAbsorption
        (reward := reward) cap owner eta heta hunique
    filter_upwards [hnear] with nearbyTail hnearby root hincidence
    exact hmoat.trans_le (hnearby root hincidence)
  filter_upwards [hnearGap, hnearMoat] with nearbyTail hnearGap hnearMoat
  constructor
  · apply (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward nearbyTail).mpr
    intro who
    linarith [hnearGap who, hdelta]
  · intro root hnash
    by_contra hroot
    obtain ⟨owner, hquit⟩ :=
      exists_quitProbability_pos_of_ne_allContinue root hroot
    have hopponent : eta ≤
        quittingRootOpponentAbsorptionMass root owner := by
      apply delta_div_le_quittingRootOpponentAbsorptionMass_of_isZeroNash_of_quit_pos
        reward nearbyTail root owner hdelta hreward
          (le_of_lt (hnearGap owner)) hnash hquit
    let simplexRoot : QuittingRootSimplex ι :=
      fun player => stdSimplexEquiv (root player)
    have hsimplexRoot : quittingRootOfSimplex simplexRoot = root := by
      funext player
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root player)
    have hpositive := hnearMoat owner simplexRoot (by
      simpa [hsimplexRoot] using hopponent)
    have hzero :=
      (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
        reward nearbyTail root).mp hnash
    rw [hsimplexRoot, hzero] at hpositive
    exact (lt_irrefl 0 hpositive).elim

/-- The envelope-to-prescribed debt homotopy of a terminal-semantic pair. -/
def quittingTerminalSemanticDebtHomotopy
    {ι : Type} (pair : QuittingTerminalSemanticPair ι) (t : ℝ) : Payoff ι :=
  pair.2 - fun who => t * quittingTerminalSemanticDebt pair who

@[simp] theorem quittingTerminalSemanticDebtHomotopy_one
    {ι : Type} (pair : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticDebtHomotopy pair 1 = pair.1 := by
  funext who
  simp [quittingTerminalSemanticDebtHomotopy,
    quittingTerminalSemanticDebt]

/-- Every point of the closed debt segment of a strictly separated positive
minimum plateau has all-Continue as its unique exact root. -/
theorem minimumTerminalSemantic_debtHomotopy_closed_eq_allContinue
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hstrict : ∀ who,
      reward (quittingSingletonTerminal who) who < pair.1 who)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward
      (quittingTerminalSemanticDebtHomotopy pair t) 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  by_cases ht : t < 1
  · exact minimumTerminalSemantic_debtHomotopy_eq_allContinue
      pair root hpair hminimum hpositive ht0 ht (by
        simpa [quittingTerminalSemanticDebtHomotopy] using hnash)
  · have htEq : t = 1 := le_antisymm ht1 (le_of_not_gt ht)
    subst t
    apply minimumTerminalSemantic_exactNash_eq_allContinue_of_strictSingleton
      pair hpair hminimum hpositive hstrict root
    simpa using hnash

/-- The singleton separation at the prescribed endpoint persists with the
same lower bound on the whole closed debt homotopy. -/
theorem singletonGap_le_quittingTerminalSemanticDebtHomotopy
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    {delta t : ℝ} (hdelta : ∀ who,
      delta ≤ pair.1 who - reward (quittingSingletonTerminal who) who)
    (ht1 : t ≤ 1) (who : ι) :
    delta ≤ quittingTerminalSemanticDebtHomotopy pair t who -
      reward (quittingSingletonTerminal who) who := by
  have hdebt : 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  unfold quittingTerminalSemanticDebtHomotopy
  change delta ≤ pair.2 who -
      t * quittingTerminalSemanticDebt pair who -
        reward (quittingSingletonTerminal who) who
  unfold quittingTerminalSemanticDebt at hdebt
  unfold quittingTerminalSemanticDebt
  have hscale : 0 ≤ (1 - t) * (pair.2 who - pair.1 who) :=
    mul_nonneg (sub_nonneg.mpr ht1) hdebt
  nlinarith [hdelta who, hscale]

/-- One open tube freezes the exact root on the whole closed debt segment.
The statement is tail-oriented and gives no incoming edge from outside. -/
theorem exists_open_exactAllContinueTube_debtHomotopy
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ who, delta ≤ pair.1 who -
      reward (quittingSingletonTerminal who) who) :
    ∃ tube : Set (Payoff ι),
      IsOpen tube ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        quittingTerminalSemanticDebtHomotopy pair t ∈ tube) ∧
      ∀ tail ∈ tube,
        IsεQuittingRootNash reward tail 0
            (quittingAllContinueRoot : ι → PMF Bool) ∧
          ∀ root : ι → PMF Bool,
            IsεQuittingRootNash reward tail 0 root →
              root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let exactAllContinue : Set (Payoff ι) :=
    {tail | IsεQuittingRootNash reward tail 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        ∀ root : ι → PMF Bool,
          IsεQuittingRootNash reward tail 0 root →
            root = (quittingAllContinueRoot : ι → PMF Bool)}
  let tube := interior exactAllContinue
  refine ⟨tube, isOpen_interior, ?_, ?_⟩
  · intro t ht
    have hunique : ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward
            (quittingTerminalSemanticDebtHomotopy pair t) 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool) := by
      intro root hnash
      exact minimumTerminalSemantic_debtHomotopy_closed_eq_allContinue
        pair hpair hminimum hpositive
          (fun who => by linarith [hdelta, hgap who]) ht.1 ht.2 root hnash
    have hnear :=
      eventually_exactRoot_eq_allContinue_of_unique_of_singletonGap
        reward (quittingTerminalSemanticDebtHomotopy pair t) hdelta
          (singletonGap_le_quittingTerminalSemanticDebtHomotopy
            pair hpair hgap ht.2) hunique
    apply mem_interior_iff_mem_nhds.mpr
    exact hnear
  · intro tail htail
    have hmem : tail ∈ exactAllContinue := interior_subset htail
    exact hmem

/-- For every fixed positive total-opponent-incidence floor, one open tube
around the whole debt segment carries one uniform positive Nash-defect moat.
The theorem deliberately fixes the incidence floor; it gives no separation
for approximate roots whose incidence tends to zero. -/
theorem exists_open_totalNashDefect_moat_debtHomotopy
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hstrict : ∀ who,
      reward (quittingSingletonTerminal who) who < pair.1 who)
    (owner : ι) {eta : ℝ} (heta : 0 < eta) :
    ∃ (tube : Set (Payoff ι)) (moat : ℝ),
      IsOpen tube ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        quittingTerminalSemanticDebtHomotopy pair t ∈ tube) ∧
      0 < moat ∧
      ∀ tail ∈ tube, ∀ root : QuittingRootSimplex ι,
        eta ≤ quittingRootTotalOpponentIncidenceMass owner
            (quittingRootOfSimplex root) →
          moat ≤ quittingRootTotalNashDefect reward tail
            (quittingRootOfSimplex root) := by
  let segment : Set (Payoff ι) :=
    quittingTerminalSemanticDebtHomotopy pair '' Set.Icc (0 : ℝ) 1
  have hhomotopyContinuous : Continuous
      (quittingTerminalSemanticDebtHomotopy pair) := by
    rw [continuous_pi_iff]
    intro who
    exact continuous_const.sub
      (continuous_id.mul continuous_const)
  have hsegmentCompact : IsCompact segment :=
    isCompact_Icc.image hhomotopyContinuous
  have hsegmentNonempty : segment.Nonempty := by
    exact ⟨quittingTerminalSemanticDebtHomotopy pair 0,
      ⟨0, by simp, rfl⟩⟩
  let highIncidence : Set (QuittingRootSimplex ι) :=
    {root | eta ≤ quittingRootTotalOpponentIncidenceMass owner
      (quittingRootOfSimplex root)}
  have hhighClosed : IsClosed highIncidence :=
    isClosed_Ici.preimage
      (continuous_quittingRootTotalOpponentIncidenceMass_simplex owner)
  have hhighCompact : IsCompact highIncidence := hhighClosed.isCompact
  by_cases hhighNonempty : highIncidence.Nonempty
  · let domain : Set (Payoff ι × QuittingRootSimplex ι) :=
      segment ×ˢ highIncidence
    have hdomainCompact : IsCompact domain :=
      hsegmentCompact.prod hhighCompact
    have hdomainNonempty : domain.Nonempty :=
      hsegmentNonempty.prod hhighNonempty
    let defect : Payoff ι × QuittingRootSimplex ι → ℝ := fun point =>
      quittingRootTotalNashDefect reward point.1
        (quittingRootOfSimplex point.2)
    have hdefectContinuous : Continuous defect :=
      continuous_quittingRootTotalNashDefect_simplex reward
    obtain ⟨selected, hselectedDomain, hselectedMin⟩ :=
      hdomainCompact.exists_isMinOn hdomainNonempty
        hdefectContinuous.continuousOn
    have hselectedNonneg : 0 ≤ defect selected :=
      quittingRootTotalNashDefect_nonneg reward selected.1
        (quittingRootOfSimplex selected.2)
    have hselectedPositive : 0 < defect selected := by
      apply lt_of_le_of_ne hselectedNonneg
      intro hzero
      obtain ⟨t, ht, htail⟩ := hselectedDomain.1
      have hnash : IsεQuittingRootNash reward selected.1 0
          (quittingRootOfSimplex selected.2) :=
        (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
          reward selected.1 (quittingRootOfSimplex selected.2)).2 hzero.symm
      have hroot : quittingRootOfSimplex selected.2 =
          (quittingAllContinueRoot : ι → PMF Bool) := by
        rw [← htail] at hnash
        exact minimumTerminalSemantic_debtHomotopy_closed_eq_allContinue
          pair hpair hminimum hpositive hstrict ht.1 ht.2
            (quittingRootOfSimplex selected.2) hnash
      have hincidenceZero : quittingRootTotalOpponentIncidenceMass owner
          (quittingRootOfSimplex selected.2) = 0 := by
        rw [hroot]
        exact quittingRootTotalOpponentIncidenceMass_allContinueRoot owner
      have hselectedHigh := hselectedDomain.2
      change eta ≤ quittingRootTotalOpponentIncidenceMass owner
        (quittingRootOfSimplex selected.2) at hselectedHigh
      rw [hincidenceZero] at hselectedHigh
      linarith
    let moat := defect selected / 2
    let bad : Set (Payoff ι × QuittingRootSimplex ι) :=
      {point | eta ≤ quittingRootTotalOpponentIncidenceMass owner
            (quittingRootOfSimplex point.2) ∧
        quittingRootTotalNashDefect reward point.1
            (quittingRootOfSimplex point.2) ≤ moat}
    have hbadClosed : IsClosed bad := by
      exact (isClosed_le continuous_const
        ((continuous_quittingRootTotalOpponentIncidenceMass_simplex owner).comp
          continuous_snd)).inter
        (isClosed_le (continuous_quittingRootTotalNashDefect_simplex reward)
          continuous_const)
    have hprojectionClosed : IsClosed (Prod.fst '' bad) :=
      isClosedMap_fst_of_compactSpace bad hbadClosed
    let tube : Set (Payoff ι) := (Prod.fst '' bad)ᶜ
    refine ⟨tube, moat, hprojectionClosed.isOpen_compl, ?_,
      by dsimp only [moat]; linarith, ?_⟩
    · intro t ht
      have htailSegment : quittingTerminalSemanticDebtHomotopy pair t ∈
          segment := ⟨t, ht, rfl⟩
      change quittingTerminalSemanticDebtHomotopy pair t ∉ Prod.fst '' bad
      rintro ⟨⟨_tail, root⟩, hrootBad, rfl⟩
      have hlower := hselectedMin ⟨htailSegment, hrootBad.1⟩
      change defect selected ≤
        quittingRootTotalNashDefect reward
          (quittingTerminalSemanticDebtHomotopy pair t)
          (quittingRootOfSimplex root) at hlower
      have hupper : quittingRootTotalNashDefect reward
          (quittingTerminalSemanticDebtHomotopy pair t)
            (quittingRootOfSimplex root) ≤ defect selected / 2 := by
        simpa only [moat] using hrootBad.2
      linarith
    · intro tail htail root hincidence
      apply le_of_not_gt
      intro hsmall
      exact htail ⟨(tail, root), ⟨hincidence, hsmall.le⟩, rfl⟩
  · refine ⟨Set.univ, 1, isOpen_univ, ?_, by norm_num, ?_⟩
    · exact fun _ _ => Set.mem_univ _
    · intro tail _ root hroot
      exact False.elim (hhighNonempty ⟨root, hroot⟩)

/-- Inside an exact all-Continue tube, an exact Bellman row is the
zero-absorption identity row.  The hypothesis is on the continuation/tail,
not on the head. -/
theorem exactBellmanEdge_eq_identity_of_mem_exactAllContinueTube
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tube : Set (Payoff ι))
    (htube : ∀ tail ∈ tube,
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward tail 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool))
    (tail : Payoff ι) (htail : tail ∈ tube) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingRootSuccessorPayoff reward tail root = tail ∧
      quittingRootAbsorptionMass root = 0 := by
  have hroot := htube tail htail root hnash
  subst root
  exact ⟨rfl, quittingRootSuccessorPayoff_allContinueRoot_eq reward tail,
    quittingRootAbsorptionMass_allContinueRoot⟩

/-- The exact all-Continue tube excludes every absorbing cyclic continuation
anchored at one of its tails. -/
theorem not_isQuittingCyclicContinuation_of_mem_exactAllContinueTube
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tube : Set (Payoff ι))
    (htube : ∀ tail ∈ tube,
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward tail 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool))
    (terminal : Payoff ι) (hterminal : terminal ∈ tube) :
    ¬ IsQuittingCyclicContinuation reward terminal := by
  apply not_isQuittingCyclicContinuation_of_unique_allContinue
    reward tube _ terminal hterminal
  intro tail htail root hnash
  exact htube tail htail root
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mp hnash)

/-- Literal `Fin 4` capstone: nonexistence forces a wholly separated minimum
plateau whose complete debt segment lies in one open exact all-Continue tube.
This packages the same-table reduction and its local consumer without adding
any nonlocal return producer. -/
theorem exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hno : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (pair : QuittingTerminalSemanticPair (Fin 4)) (delta : ℝ)
        (tube : Set (Payoff (Fin 4))),
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum pair ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair = pair ∧
      0 < delta ∧
      (∀ who,
        quittingPunishmentValue reward who ≤
            reward (quittingSingletonTerminal who) who ∧
          delta ≤ pair.1 who -
            reward (quittingSingletonTerminal who) who) ∧
      IsOpen tube ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        quittingTerminalSemanticDebtHomotopy pair t ∈ tube) ∧
      ∀ tail ∈ tube,
        IsεQuittingRootNash reward tail 0
            (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
          ∀ root : Fin 4 → PMF Bool,
            IsεQuittingRootNash reward tail 0 root →
              root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  obtain ⟨pair, hpair, hminimum, hpositive, _hnash, hfixed, hseparated⟩ :=
    exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
      reward hno
  let gaps : Finset ℝ := (Finset.univ : Finset (Fin 4)).image
    (fun who => pair.1 who -
      reward (quittingSingletonTerminal who) who)
  have hgaps : gaps.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let delta := gaps.min' hgaps
  have hdeltaMem : delta ∈ gaps := Finset.min'_mem gaps hgaps
  obtain ⟨selected, _hselected, hselectedGap⟩ :=
    Finset.mem_image.mp hdeltaMem
  have hdelta : 0 < delta := by
    rw [← hselectedGap]
    linarith [(hseparated selected).2]
  have hgap : ∀ who, delta ≤ pair.1 who -
      reward (quittingSingletonTerminal who) who := by
    intro who
    exact Finset.min'_le gaps
      (pair.1 who - reward (quittingSingletonTerminal who) who)
      (Finset.mem_image.mpr ⟨who, Finset.mem_univ who, rfl⟩)
  obtain ⟨tube, htubeOpen, hsegment, htube⟩ :=
    exists_open_exactAllContinueTube_debtHomotopy
      pair hpair hminimum hpositive hdelta hgap
  exact ⟨pair, delta, tube, hpair, hminimum, hpositive, hfixed, hdelta,
    fun who => ⟨(hseparated who).1, hgap who⟩,
    htubeOpen, hsegment, htube⟩

end GameTheory
