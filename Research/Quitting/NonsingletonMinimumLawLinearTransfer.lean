/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiveWeightedCollisionTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonsingletonAntiDiffusion

/-!
# Linear transfer from a nonsingleton minimum-law atom

This Research module composes an actual minimum-law causal suffix atom with
the live-weighted collision transfer.  Its final conclusion is deliberately
branchwise: either tail escape recurs along a strict subsequence, or a strict
subsequence carries one fixed endpoint mover, action, routed coalition, and
distinct debt recipient.

The theorem does not assert that both branches occur, that the selected row
is a cap--Nash prefix row, or that either branch yields a return or a uniform
payoff.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingNonsingletonMinimumLawTransfer

def prefixedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (roots n) (profiles n)

def shiftedStage (roots : ℕ → List (ι → PMF Bool))
    (mark : ℕ → ℕ) (n : ℕ) : ℕ :=
  (roots n).length + mark n

def sourcePair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (n : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward (prefixedProfile reward profiles roots n)

def tailPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (mark : ℕ → ℕ) (n : ℕ) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward
      (prefixedProfile reward profiles roots n) (shiftedStage roots mark n + 1))

def liveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (mark : ℕ → ℕ) (n : ℕ) :
    ι → PMF Bool :=
  quittingProfileLiveRoot reward (prefixedProfile reward profiles roots n)
    (shiftedStage roots mark n)

def bestAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (mark : ℕ → ℕ)
    (n : ℕ) (who : ι) : Bool :=
  quittingRootBestEndpointAction reward
    (tailPair reward profiles roots mark n).1
    (liveRoot reward profiles roots mark n) who

def targetProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (mark : ℕ → ℕ)
    (n : ℕ) (who : ι) : (quittingGame reward).BehaviorProfile :=
  Function.update (prefixedProfile reward profiles roots n) who
    (quittingStagePureEndpointBehaviorDeviation reward
      (prefixedProfile reward profiles roots n) who
      (shiftedStage roots mark n) (bestAction reward profiles roots mark n who))

def targetPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (mark : ℕ → ℕ)
    (n : ℕ) (who : ι) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (targetProfile reward profiles roots mark n who)

def endpointGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (mark : ℕ → ℕ)
    (n : ℕ) (who : ι) : ℝ :=
  quittingTerminalPayoff reward (targetProfile reward profiles roots mark n who) who -
    quittingTerminalPayoff reward (prefixedProfile reward profiles roots n) who

def sourceExcess
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool)) (n : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum (sourcePair reward profiles roots n) -
    quittingTerminalSemanticDebtSum minimum

def routedCoalition (terminal : {S : Finset ι // S.Nonempty})
    (who : ι) (action : Bool) : Finset ι :=
  quittingPureEndpointRoutedCoalition terminal.val who action

omit [Nonempty ι] in
/-- Exact cap-stack debt scaling and common positive limiting debt force the
displayed stack survival products to converge to one. -/
theorem tendsto_capNashStackContinueProduct_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → List (ι → PMF Bool))
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hprofiles : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds point))
    (hstack : ∀ n, IsQuittingCapNashRootStack reward (roots n) (profiles n))
    (hprefix : Tendsto (fun n ↦ quittingTerminalDebtSum reward
      (prefixedProfile reward profiles roots n))
      atTop (nhds (quittingTerminalDebtSumInf reward))) :
    Tendsto (fun n ↦ quittingCapNashStackContinueProduct (roots n))
      atTop (nhds 1) := by
  have hsemantic : Tendsto (fun n ↦
      quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds point.1) :=
    continuous_fst.tendsto point |>.comp hprofiles
  have hsuffix : Tendsto (fun n ↦ quittingTerminalDebtSum reward (profiles n))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) := by
    have hsum := continuous_quittingTerminalSemanticDebtSum.tendsto point.1 |>.comp
      hsemantic
    change Tendsto (fun n ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (profiles n))) atTop
        (nhds (quittingTerminalSemanticDebtSum point.1)) at hsum
    simpa only [quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using hsum
  have hcarrier : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hinf := quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    (reward := reward) point.1 hcarrier hminimum
  have hprefix' : Tendsto (fun n ↦ quittingTerminalDebtSum reward
      (prefixedProfile reward profiles roots n))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) := by
    simpa only [hinf] using hprefix
  have hratio := hprefix'.div hsuffix (ne_of_gt hpositive)
  have hratioOne : Tendsto (fun n ↦
      quittingTerminalDebtSum reward (prefixedProfile reward profiles roots n) /
        quittingTerminalDebtSum reward (profiles n)) atTop (nhds 1) := by
    change Tendsto (fun n ↦
      quittingTerminalDebtSum reward (prefixedProfile reward profiles roots n) /
        quittingTerminalDebtSum reward (profiles n)) atTop
      (nhds (quittingTerminalSemanticDebtSum point.1 /
        quittingTerminalSemanticDebtSum point.1)) at hratio
    simpa only [div_self (ne_of_gt hpositive)] using hratio
  apply hratioOne.congr'
  filter_upwards with n
  have hsuffixPositive : 0 < quittingTerminalDebtSum reward (profiles n) := by
    have hinfPositive : 0 < quittingTerminalDebtSumInf reward := by
      rw [hinf]
      exact hpositive
    exact hinfPositive.trans_le
      (quittingTerminalDebtSumInf_le (reward := reward) (profiles n))
  have hscale := quittingTerminalDebtSum_capNashRootStack_eq
    (reward := reward) (roots n) (profiles n) (hstack n)
  dsimp only [prefixedProfile]
  rw [hscale, mul_div_cancel_right₀ _ hsuffixPositive.ne']

/-- One globally reselected chronological row in every literal suffix.  The
profiles and exact cap stacks are the causal atom's original source data; only
the marked suffix date is reselected by the sharp anti-diffusion theorem. -/
structure SelectedRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point) where
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  cutoff : ℕ → ℕ
  roots : ℕ → List (ι → PMF Bool)
  mark : ℕ → ℕ
  collision : 1 < atom.terminal.val.card
  profiles_tendsto : Tendsto (fun n ↦
    (quittingTerminalSemanticPair reward (profiles n),
      quittingTerminalOutcomeMass reward (profiles n)))
    atTop (nhds point)
  roots_length : ∀ n, (roots n).length = n + 1
  roots_nash : ∀ n, IsQuittingCapNashRootStack reward (roots n) (profiles n)
  prefix_debt_tendsto : Tendsto (fun n ↦ quittingTerminalDebtSum reward
    (prefixedProfile reward profiles roots n))
    atTop (nhds (quittingTerminalDebtSumInf reward))
  source_window : ∀ᶠ n in atTop,
    point.2 (some atom.terminal) / 2 <
      ∑ time ∈ Finset.range (cutoff n),
        quittingStageCoalitionMass reward (profiles n) time atom.terminal
  suffix_stage_sharp : ∀ n,
    (∑' time, quittingStageCoalitionMass reward
        (profiles n) time atom.terminal) ^
          ((atom.terminal.val.card : ℝ) /
            ((atom.terminal.val.card : ℝ) - 1)) ≤
      quittingStageCoalitionMass reward (profiles n) (mark n) atom.terminal
  shifted_stage_exact : ∀ n,
    quittingStageCoalitionMass reward
        (prefixedProfile reward profiles roots n)
        (shiftedStage roots mark n) atom.terminal =
      quittingCapNashStackContinueProduct (roots n) *
        quittingStageCoalitionMass reward (profiles n) (mark n) atom.terminal
  continueProduct_tendsto_one :
    Tendsto (fun n ↦ quittingCapNashStackContinueProduct (roots n))
      atTop (nhds 1)
  sharp_retention : ∀ lambda,
    lambda < point.2 (some atom.terminal) ^
        ((atom.terminal.val.card : ℝ) /
          ((atom.terminal.val.card : ℝ) - 1)) →
      ∀ᶠ n in atTop, lambda <
        quittingStageCoalitionMass reward
          (prefixedProfile reward profiles roots n)
          (shiftedStage roots mark n) atom.terminal

omit [Nonempty ι] in
/-- The actual causal suffix chronology admits one sharp anti-diffusion mark
per suffix, while retaining its roots, exact-stack proof, length, source
window, and prefixed debt convergence literally. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hcollision : 1 < atom.terminal.val.card) :
    Nonempty (SelectedRows reward point atom) := by
  obtain ⟨profiles, cutoff, _oldMark, roots, hprofiles, hlength,
      hnash, hprefix, hcausal⟩ := atom.chronology
  have hcard : 2 ≤ atom.terminal.val.card := by omega
  have hmark : ∀ n, ∃ peak,
      (∑' time, quittingStageCoalitionMass reward
          (profiles n) time atom.terminal) ^
            ((atom.terminal.val.card : ℝ) /
              ((atom.terminal.val.card : ℝ) - 1)) ≤
        quittingStageCoalitionMass reward (profiles n) peak atom.terminal := by
    intro n
    exact exists_quittingStageCoalitionMass_ge_tsum_rpow
      (profiles n) atom.terminal hcard
  choose mark hmarkSharp using hmark
  have hproduct := tendsto_capNashStackContinueProduct_one
    reward point profiles roots hpoint hminimum hpositive hprofiles hnash hprefix
  let exponent : ℝ := (atom.terminal.val.card : ℝ) /
    ((atom.terminal.val.card : ℝ) - 1)
  have hmass : Tendsto (fun n ↦
      ∑' time, quittingStageCoalitionMass reward
        (profiles n) time atom.terminal)
      atTop (nhds (point.2 (some atom.terminal))) := by
    have hcoordinate : Tendsto (fun n ↦
        quittingTerminalOutcomeMass reward (profiles n) (some atom.terminal))
        atTop (nhds (point.2 (some atom.terminal))) :=
      ((continuous_apply (some atom.terminal)).comp continuous_snd).tendsto point
        |>.comp hprofiles
    simpa only [quittingTerminalOutcomeMass_eq_timeDisintegration] using hcoordinate
  have hexponentPos : 0 < exponent := by
    dsimp only [exponent]
    have hk2 : (2 : ℝ) ≤ atom.terminal.val.card := by exact_mod_cast hcard
    have hk0 : (0 : ℝ) < atom.terminal.val.card :=
      lt_of_lt_of_le zero_lt_two hk2
    have hk1 : (0 : ℝ) < atom.terminal.val.card - 1 := by linarith
    exact div_pos hk0 hk1
  have hmassPow : Tendsto (fun n ↦
      (∑' time, quittingStageCoalitionMass reward
        (profiles n) time atom.terminal) ^ exponent)
      atTop (nhds (point.2 (some atom.terminal) ^ exponent)) := by
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hexponentPos.le)).tendsto.comp
      hmass
  have hlower : Tendsto (fun n ↦
      quittingCapNashStackContinueProduct (roots n) *
        (∑' time, quittingStageCoalitionMass reward
          (profiles n) time atom.terminal) ^ exponent)
      atTop (nhds (point.2 (some atom.terminal) ^ exponent)) := by
    have hmul := hproduct.mul hmassPow
    simpa only [one_mul] using hmul
  refine ⟨{
    profiles := profiles
    cutoff := cutoff
    roots := roots
    mark := mark
    collision := hcollision
    profiles_tendsto := hprofiles
    roots_length := hlength
    roots_nash := hnash
    prefix_debt_tendsto := hprefix
    source_window := hcausal.mono fun _ hn ↦ hn.1
    suffix_stage_sharp := hmarkSharp
    shifted_stage_exact := fun n ↦
      quittingStageCoalitionMass_literalRootStack_add_length
        reward (roots n) (profiles n) (mark n) atom.terminal
    continueProduct_tendsto_one := hproduct
    sharp_retention := ?_ }⟩
  intro lambda hlambda
  have hlambda' : lambda < point.2 (some atom.terminal) ^ exponent := by
    simpa only [exponent] using hlambda
  have hevent := hlower.eventually (Ioi_mem_nhds hlambda')
  filter_upwards [hevent] with n hn
  have hscaled := mul_le_mul_of_nonneg_left (hmarkSharp n)
    (quittingCapNashStackContinueProduct_nonneg (roots n))
  calc
    lambda < quittingCapNashStackContinueProduct (roots n) *
        (∑' time, quittingStageCoalitionMass reward
          (profiles n) time atom.terminal) ^ exponent := hn
    _ ≤ quittingCapNashStackContinueProduct (roots n) *
        quittingStageCoalitionMass reward (profiles n) (mark n) atom.terminal := by
      simpa only [exponent] using hscaled
    _ = quittingStageCoalitionMass reward
        (prefixedProfile reward profiles roots n)
        (shiftedStage roots mark n) atom.terminal := by
      exact (quittingStageCoalitionMass_literalRootStack_add_length
        reward (roots n) (profiles n) (mark n) atom.terminal).symm

def selectedStageMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {point : QuittingTerminalSemanticLawPoint ι}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (rows : SelectedRows reward point atom) (n : ℕ) : ℝ :=
  quittingStageCoalitionMass reward
    (prefixedProfile reward rows.profiles rows.roots n)
    (shiftedStage rows.roots rows.mark n) atom.terminal

def selectedTailExcess
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {point : QuittingTerminalSemanticLawPoint ι}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (rows : SelectedRows reward point atom) (n : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum
      (tailPair reward rows.profiles rows.roots rows.mark n) -
    quittingTerminalSemanticDebtSum point.1

def selectedTargetStageMass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {point : QuittingTerminalSemanticLawPoint ι}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (rows : SelectedRows reward point atom) (n : ℕ) (who : ι) : ℝ :=
  let action := bestAction reward rows.profiles rows.roots rows.mark n who
  let routed := routedCoalition atom.terminal who action
  quittingStageCoalitionMass reward
    (targetProfile reward rows.profiles rows.roots rows.mark n who)
    (shiftedStage rows.roots rows.mark n)
    ⟨routed, quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
      atom.terminal.val who action rows.collision⟩

omit [Nonempty ι] in
/-- The sharp anti-diffusion mark is eventually larger than the convenient
quadratic floor used by the linear-transfer constants. -/
theorem SelectedRows.eventually_stageMass_gt_square_div_eight
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {point : QuittingTerminalSemanticLawPoint ι}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (rows : SelectedRows reward point atom)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    ∀ᶠ n in atTop,
      point.2 (some atom.terminal) ^ 2 / 8 < selectedStageMass rows n := by
  let mass := point.2 (some atom.terminal)
  let exponent : ℝ := (atom.terminal.val.card : ℝ) /
    ((atom.terminal.val.card : ℝ) - 1)
  have hmassPos : 0 < mass := atom.terminalMass_pos
  have hsimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex point hpoint
  have hmassLeOne : mass ≤ 1 := by
    have hle : point.2 (some atom.terminal) ≤ ∑ outcome, point.2 outcome := by
      exact Finset.single_le_sum
        (fun outcome _ ↦ hsimplex.1 outcome) (Finset.mem_univ _)
    simpa only [mass, hsimplex.2] using hle
  have hcardTwo : (2 : ℝ) ≤ atom.terminal.val.card := by
    exact_mod_cast rows.collision
  have hexponentLeTwo : exponent ≤ 2 := by
    dsimp only [exponent]
    have hdenPos : 0 < (atom.terminal.val.card : ℝ) - 1 := by linarith
    apply (div_le_iff₀ hdenPos).2
    linarith
  have hsquareLePower : mass ^ (2 : ℝ) ≤ mass ^ exponent :=
    Real.rpow_le_rpow_of_exponent_ge hmassPos hmassLeOne hexponentLeTwo
  have hpowTwo : mass ^ 2 = mass ^ (2 : ℝ) := by
    rw [Real.rpow_two]
  have hlambda : mass ^ 2 / 8 < mass ^ exponent := by
    calc
      mass ^ 2 / 8 < mass ^ 2 := by
        have hsquarePos : 0 < mass ^ 2 := sq_pos_of_pos hmassPos
        linarith
      _ = mass ^ (2 : ℝ) := hpowTwo
      _ ≤ mass ^ exponent := hsquareLePower
  simpa only [mass, exponent, selectedStageMass] using
    rows.sharp_retention (mass ^ 2 / 8) hlambda

private structure TailRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (rows : SelectedRows reward point atom) (n : ℕ) : Prop where
  stage_mass_floor :
    point.2 (some atom.terminal) ^ 2 / 8 < selectedStageMass rows n
  tail_excess_floor :
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 / 16 ≤
      selectedTailExcess rows n

private structure TransferRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (rows : SelectedRows reward point atom) (n : ℕ)
    (who other : ι) : Prop where
  recipient_mem : other ∈ Finset.univ.erase who
  stage_mass_floor :
    point.2 (some atom.terminal) ^ 2 / 8 < selectedStageMass rows n
  gain_formula :
    endpointGain reward rows.profiles rows.roots rows.mark n who =
      quittingLiveMass reward
          (prefixedProfile reward rows.profiles rows.roots n)
          (shiftedStage rows.roots rows.mark n) *
        quittingRootCoordinateNashDefect reward
          (tailPair reward rows.profiles rows.roots rows.mark n).1
          (liveRoot reward rows.profiles rows.roots rows.mark n) who
  gain_pos : 0 < endpointGain reward rows.profiles rows.roots rows.mark n who
  gain_floor :
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 /
            (16 * (Fintype.card ι : ℝ)) ≤
      endpointGain reward rows.profiles rows.roots rows.mark n who
  target_mem :
    targetPair reward rows.profiles rows.roots rows.mark n who ∈
      quittingTerminalSemanticCarrier reward
  mover_debt_exact :
    quittingTerminalSemanticDebt
        (targetPair reward rows.profiles rows.roots rows.mark n who) who =
      quittingTerminalSemanticDebt
          (sourcePair reward rows.profiles rows.roots n) who -
        endpointGain reward rows.profiles rows.roots rows.mark n who
  aggregate_transfer :
    endpointGain reward rows.profiles rows.roots rows.mark n who -
          sourceExcess reward point.1 rows.profiles rows.roots n ≤
      ∑ player ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange
          (sourcePair reward rows.profiles rows.roots n)
          (targetPair reward rows.profiles rows.roots rows.mark n who) player
  recipient_floor :
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 /
            (32 * (Fintype.card ι : ℝ) *
              ((Fintype.card ι : ℝ) - 1)) ≤
      quittingTerminalSemanticDebtChange
        (sourcePair reward rows.profiles rows.roots n)
        (targetPair reward rows.profiles rows.roots rows.mark n who) other
  routed_no_loss :
    selectedStageMass rows n ≤ selectedTargetStageMass rows n who

/-- Every sufficiently late sharp row admits the exact live-weighted
collision dispatch.  The source error is the actual prefixed total-debt
excess over the fixed minimum point. -/
private theorem SelectedRows.eventually_tailRow_or_transferRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {point : QuittingTerminalSemanticLawPoint ι}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (rows : SelectedRows reward point atom)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1) :
    ∀ᶠ n in atTop,
      TailRow reward point atom rows n ∨
        ∃ who other, TransferRow reward point atom rows n who other := by
  have hminimumCarrier : point.1 ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier point hpoint
  have hinf := quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
    (reward := reward) point.1 hminimumCarrier hminimum
  have hsourceDebt : Tendsto (fun n ↦
      quittingTerminalSemanticDebtSum
        (sourcePair reward rows.profiles rows.roots n))
      atTop (nhds (quittingTerminalSemanticDebtSum point.1)) := by
    have hprefix := rows.prefix_debt_tendsto
    rw [hinf] at hprefix
    simpa only [sourcePair,
      quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using hprefix
  have hexcess : Tendsto (fun n ↦
      sourceExcess reward point.1 rows.profiles rows.roots n)
      atTop (nhds 0) := by
    have hsub := hsourceDebt.sub_const
      (quittingTerminalSemanticDebtSum point.1)
    simpa only [sourceExcess, sub_self] using hsub
  have hstage := rows.eventually_stageMass_gt_square_div_eight hpoint
  have hmassPos : 0 < point.2 (some atom.terminal) := atom.terminalMass_pos
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by positivity
  have hcardOne : (1 : ℝ) < Fintype.card ι := by
    have hle := Finset.card_le_univ atom.terminal.val
    exact_mod_cast (lt_of_lt_of_le rows.collision hle)
  have hfacePos : 0 < (Fintype.card ι : ℝ) - 1 := sub_pos.mpr hcardOne
  let threshold := point.2 (some atom.terminal) ^ 2 *
    quittingTerminalSemanticDebtSum point.1 /
      (32 * (Fintype.card ι : ℝ))
  have hthresholdPos : 0 < threshold := by
    dsimp only [threshold]
    positivity
  have hepsilon : ∀ᶠ n in atTop,
      sourceExcess reward point.1 rows.profiles rows.roots n ≤ threshold :=
    (hexcess.eventually_lt_const hthresholdPos).mono fun _ hn ↦ hn.le
  filter_upwards [hstage, hepsilon] with n hstageN hepsilonN
  have hstagePos : 0 < selectedStageMass rows n :=
    (by positivity : 0 < point.2 (some atom.terminal) ^ 2 / 8).trans hstageN
  have hthresholdLe : threshold ≤
      selectedStageMass rows n * quittingTerminalSemanticDebtSum point.1 /
        (4 * (Fintype.card ι : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right hstageN hpositive
    have hdiv := div_lt_div_of_pos_right hmul
      (show 0 < 4 * (Fintype.card ι : ℝ) by positivity)
    calc
      threshold = (point.2 (some atom.terminal) ^ 2 / 8 *
          quittingTerminalSemanticDebtSum point.1) /
            (4 * (Fintype.card ι : ℝ)) := by
        dsimp only [threshold]
        ring
      _ ≤ _ := hdiv.le
  have hnear : quittingTerminalSemanticDebtSum
        (sourcePair reward rows.profiles rows.roots n) ≤
      quittingTerminalSemanticDebtSum point.1 +
        sourceExcess reward point.1 rows.profiles rows.roots n := by
    dsimp only [sourceExcess]
    linarith
  have hdispatch :=
    quittingLiveWeightedCollisionTransfer_tailEscape_or_routedTransfer
      reward point.1 (prefixedProfile reward rows.profiles rows.roots n)
      (shiftedStage rows.roots rows.mark n) atom.terminal
      (sourceExcess reward point.1 rows.profiles rows.roots n)
      hminimumCarrier hminimum hpositive rows.collision hstagePos hnear
      (hepsilonN.trans hthresholdLe)
  rcases hdispatch with hescape | htransfer
  · left
    refine ⟨hstageN, ?_⟩
    have htailNonneg : 0 ≤ selectedTailExcess rows n := by
      have htailCarrier : tailPair reward rows.profiles rows.roots rows.mark n ∈
          quittingTerminalSemanticCarrier reward :=
        quittingTerminalSemanticPair_mem_carrier reward _
      dsimp only [selectedTailExcess]
      exact sub_nonneg.mpr (hminimum _ htailCarrier)
    have hliveLe := quittingLiveMass_le_one reward
      (prefixedProfile reward rows.profiles rows.roots n)
      (shiftedStage rows.roots rows.mark n)
    have hremoveLive :
        quittingLiveMass reward
              (prefixedProfile reward rows.profiles rows.roots n)
              (shiftedStage rows.roots rows.mark n) *
            selectedTailExcess rows n ≤ selectedTailExcess rows n := by
      nlinarith
    have hscaled : point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 / 16 <
        selectedStageMass rows n *
          quittingTerminalSemanticDebtSum point.1 / 2 := by
      have hmul := mul_lt_mul_of_pos_right hstageN hpositive
      linarith
    have hescape' :
        selectedStageMass rows n * quittingTerminalSemanticDebtSum point.1 / 2 ≤
          quittingLiveMass reward
              (prefixedProfile reward rows.profiles rows.roots n)
              (shiftedStage rows.roots rows.mark n) *
            selectedTailExcess rows n := by
      simpa only [selectedStageMass, selectedTailExcess, tailPair,
        quittingSpineDebtExcess] using hescape
    exact hscaled.le.trans (hescape'.trans hremoveLive)
  · obtain ⟨who, hformula, hgainPos, hgain, htarget, hmover,
        haggregate, ⟨other, hother, hrecipient⟩,
        ⟨_hroutedNonempty, hrouted⟩⟩ := htransfer
    right
    refine ⟨who, other, {
      recipient_mem := hother
      stage_mass_floor := hstageN
      gain_formula := ?_
      gain_pos := ?_
      gain_floor := ?_
      target_mem := ?_
      mover_debt_exact := ?_
      aggregate_transfer := ?_
      recipient_floor := ?_
      routed_no_loss := ?_ }⟩
    · simpa only [endpointGain, targetProfile, tailPair, liveRoot,
        prefixedProfile, bestAction] using hformula
    · simpa only [endpointGain, targetProfile, prefixedProfile, bestAction,
        tailPair, liveRoot] using hgainPos
    · have hmul := mul_lt_mul_of_pos_right hstageN hpositive
      have hdiv := div_lt_div_of_pos_right hmul
        (show 0 < 2 * (Fintype.card ι : ℝ) by positivity)
      have hfloor : point.2 (some atom.terminal) ^ 2 *
            quittingTerminalSemanticDebtSum point.1 /
              (16 * (Fintype.card ι : ℝ)) ≤
          selectedStageMass rows n *
            quittingTerminalSemanticDebtSum point.1 /
              (2 * (Fintype.card ι : ℝ)) := by
        calc
          point.2 (some atom.terminal) ^ 2 *
                quittingTerminalSemanticDebtSum point.1 /
                  (16 * (Fintype.card ι : ℝ)) =
              (point.2 (some atom.terminal) ^ 2 / 8 *
                quittingTerminalSemanticDebtSum point.1) /
                  (2 * (Fintype.card ι : ℝ)) := by ring
          _ ≤ _ := hdiv.le
      exact hfloor.trans (by
        simpa only [endpointGain, targetProfile, prefixedProfile,
          selectedStageMass, bestAction, tailPair, liveRoot] using hgain)
    · simpa only [targetPair, targetProfile, bestAction, tailPair, liveRoot]
        using htarget
    · simpa only [targetPair, sourcePair, endpointGain, targetProfile,
        prefixedProfile, bestAction, tailPair, liveRoot] using hmover
    · simpa only [targetPair, sourcePair, endpointGain, sourceExcess,
        targetProfile, prefixedProfile, bestAction, tailPair, liveRoot]
        using haggregate
    · have hmul := mul_lt_mul_of_pos_right hstageN hpositive
      have hdenPos : 0 < 4 * (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) - 1) := by positivity
      have hdiv := div_lt_div_of_pos_right hmul hdenPos
      have hfloor : point.2 (some atom.terminal) ^ 2 *
            quittingTerminalSemanticDebtSum point.1 /
              (32 * (Fintype.card ι : ℝ) *
                ((Fintype.card ι : ℝ) - 1)) ≤
          selectedStageMass rows n *
            quittingTerminalSemanticDebtSum point.1 /
              (4 * (Fintype.card ι : ℝ) *
                ((Fintype.card ι : ℝ) - 1)) := by
        calc
          point.2 (some atom.terminal) ^ 2 *
                quittingTerminalSemanticDebtSum point.1 /
                  (32 * (Fintype.card ι : ℝ) *
                    ((Fintype.card ι : ℝ) - 1)) =
              (point.2 (some atom.terminal) ^ 2 / 8 *
                quittingTerminalSemanticDebtSum point.1) /
                  (4 * (Fintype.card ι : ℝ) *
                    ((Fintype.card ι : ℝ) - 1)) := by
            field_simp [ne_of_gt hcardPos, ne_of_gt hfacePos]
            ring
          _ ≤ _ := hdiv.le
      exact hfloor.trans (by
        simpa only [targetPair, sourcePair, targetProfile, prefixedProfile,
          selectedStageMass, bestAction, tailPair, liveRoot] using hrecipient)
    · have hrouted' : selectedStageMass rows n ≤
          selectedTargetStageMass rows n who := by
        simpa only [selectedStageMass, selectedTargetStageMass, targetProfile,
          prefixedProfile, bestAction, routedCoalition, tailPair, liveRoot]
          using hrouted
      exact hrouted'

/-- A cofinal subsequence on which the shifted tails stay a fixed positive
distance above the global minimum debt.  All source chronology and sharp
stage-mass provenance remains in `rows`. -/
structure TailEscapeSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point) where
  rows : SelectedRows reward point atom
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  stage_mass_floor : ∀ rank,
    point.2 (some atom.terminal) ^ 2 / 8 <
      selectedStageMass rows (subseq rank)
  tail_excess_floor : ∀ rank,
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 / 16 ≤
      selectedTailExcess rows (subseq rank)

/-- A cofinal gain subsequence with one fixed mover, recipient, endpoint
action, and routed coalition.  The recipient is distinct from the mover; no
incidence relation between it and the routed coalition is asserted. -/
structure RoutedTransferSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point) where
  rows : SelectedRows reward point atom
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  mover : ι
  recipient : ι
  action : Bool
  routed : {S : Finset ι // S.Nonempty}
  recipient_mem : recipient ∈ Finset.univ.erase mover
  action_fixed : ∀ rank,
    bestAction reward rows.profiles rows.roots rows.mark (subseq rank) mover =
      action
  routed_fixed : routed.val = routedCoalition atom.terminal mover action
  stage_mass_floor : ∀ rank,
    point.2 (some atom.terminal) ^ 2 / 8 <
      selectedStageMass rows (subseq rank)
  gain_formula : ∀ rank,
    endpointGain reward rows.profiles rows.roots rows.mark (subseq rank) mover =
      quittingLiveMass reward
          (prefixedProfile reward rows.profiles rows.roots (subseq rank))
          (shiftedStage rows.roots rows.mark (subseq rank)) *
        quittingRootCoordinateNashDefect reward
          (tailPair reward rows.profiles rows.roots rows.mark (subseq rank)).1
          (liveRoot reward rows.profiles rows.roots rows.mark (subseq rank)) mover
  gain_pos : ∀ rank, 0 <
    endpointGain reward rows.profiles rows.roots rows.mark (subseq rank) mover
  gain_floor : ∀ rank,
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 /
            (16 * (Fintype.card ι : ℝ)) ≤
      endpointGain reward rows.profiles rows.roots rows.mark (subseq rank) mover
  target_mem : ∀ rank,
    targetPair reward rows.profiles rows.roots rows.mark (subseq rank) mover ∈
      quittingTerminalSemanticCarrier reward
  mover_debt_exact : ∀ rank,
    quittingTerminalSemanticDebt
        (targetPair reward rows.profiles rows.roots rows.mark
          (subseq rank) mover) mover =
      quittingTerminalSemanticDebt
          (sourcePair reward rows.profiles rows.roots (subseq rank)) mover -
        endpointGain reward rows.profiles rows.roots rows.mark
          (subseq rank) mover
  aggregate_transfer : ∀ rank,
    endpointGain reward rows.profiles rows.roots rows.mark (subseq rank) mover -
          sourceExcess reward point.1 rows.profiles rows.roots (subseq rank) ≤
      ∑ other ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange
          (sourcePair reward rows.profiles rows.roots (subseq rank))
          (targetPair reward rows.profiles rows.roots rows.mark
            (subseq rank) mover) other
  recipient_floor : ∀ rank,
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 /
            (32 * (Fintype.card ι : ℝ) *
              ((Fintype.card ι : ℝ) - 1)) ≤
      quittingTerminalSemanticDebtChange
        (sourcePair reward rows.profiles rows.roots (subseq rank))
        (targetPair reward rows.profiles rows.roots rows.mark
          (subseq rank) mover) recipient
  routed_no_loss : ∀ rank,
    selectedStageMass rows (subseq rank) ≤
      quittingStageCoalitionMass reward
        (targetProfile reward rows.profiles rows.roots rows.mark
          (subseq rank) mover)
        (shiftedStage rows.roots rows.mark (subseq rank)) routed

omit [Nonempty ι] in
/-- The fixed routed atom retains the displayed positive stage-mass floor on
every selected gain row. -/
theorem RoutedTransferSubsequence.routed_stage_mass_floor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {point : QuittingTerminalSemanticLawPoint ι}
    {atom : QuittingMinimumLawCausalSuffixAtom reward point}
    (transfer : RoutedTransferSubsequence reward point atom) (rank : ℕ) :
    point.2 (some atom.terminal) ^ 2 / 8 <
      quittingStageCoalitionMass reward
        (targetProfile reward transfer.rows.profiles transfer.rows.roots
          transfer.rows.mark (transfer.subseq rank) transfer.mover)
        (shiftedStage transfer.rows.roots transfer.rows.mark
          (transfer.subseq rank)) transfer.routed :=
  (transfer.stage_mass_floor rank).trans_le (transfer.routed_no_loss rank)

/-- The corrected deep composition: the same causal chronology and the same
nonsingleton atom admit either a cofinal tail-escape subsequence, or a cofinal
transfer subsequence on which the mover, endpoint action, routed coalition,
and distinct recipient are all fixed. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_tailEscape_or_routedTransferSubsequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hcollision : 1 < atom.terminal.val.card) :
    Nonempty (TailEscapeSubsequence reward point atom) ∨
      Nonempty (RoutedTransferSubsequence reward point atom) := by
  obtain ⟨rows⟩ := QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
    reward point atom hpoint hminimum hpositive hcollision
  have hrows := rows.eventually_tailRow_or_transferRow hpoint hminimum hpositive
  by_cases htail : ∃ᶠ n in atTop, TailRow reward point atom rows n
  · obtain ⟨subseq, hsubseq, htailSubseq⟩ :=
      extraction_of_frequently_atTop htail
    left
    exact ⟨{
      rows := rows
      subseq := subseq
      subseq_strictMono := hsubseq
      stage_mass_floor := fun rank ↦ (htailSubseq rank).stage_mass_floor
      tail_excess_floor := fun rank ↦ (htailSubseq rank).tail_excess_floor }⟩
  · have hnotTail : ∀ᶠ n in atTop, ¬ TailRow reward point atom rows n :=
      not_frequently.mp htail
    have htransfer : ∀ᶠ n in atTop,
        ∃ who other, TransferRow reward point atom rows n who other := by
      filter_upwards [hrows, hnotTail] with n hrow hn
      exact hrow.resolve_left hn
    have htransferFrequently : ∃ᶠ n in atTop,
        ∃ who other, TransferRow reward point atom rows n who other :=
      htransfer.frequently
    rw [Filter.frequently_exists] at htransferFrequently
    obtain ⟨mover, hmover⟩ := htransferFrequently
    rw [Filter.frequently_exists] at hmover
    obtain ⟨recipient, hrecipient⟩ := hmover
    have hactionFrequently : ∃ᶠ n in atTop, ∃ action,
        TransferRow reward point atom rows n mover recipient ∧
          bestAction reward rows.profiles rows.roots rows.mark n mover = action := by
      apply hrecipient.mono
      intro n hn
      exact ⟨bestAction reward rows.profiles rows.roots rows.mark n mover,
        hn, rfl⟩
    rw [Filter.frequently_exists] at hactionFrequently
    obtain ⟨action, hfixed⟩ := hactionFrequently
    obtain ⟨subseq, hsubseq, hfixedSubseq⟩ :=
      extraction_of_frequently_atTop hfixed
    let routed : {S : Finset ι // S.Nonempty} :=
      ⟨routedCoalition atom.terminal mover action,
        quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
          atom.terminal.val mover action rows.collision⟩
    right
    exact ⟨{
      rows := rows
      subseq := subseq
      subseq_strictMono := hsubseq
      mover := mover
      recipient := recipient
      action := action
      routed := routed
      recipient_mem := (hfixedSubseq 0).1.recipient_mem
      action_fixed := fun rank ↦ (hfixedSubseq rank).2
      routed_fixed := rfl
      stage_mass_floor := fun rank ↦
        (hfixedSubseq rank).1.stage_mass_floor
      gain_formula := fun rank ↦ (hfixedSubseq rank).1.gain_formula
      gain_pos := fun rank ↦ (hfixedSubseq rank).1.gain_pos
      gain_floor := fun rank ↦ (hfixedSubseq rank).1.gain_floor
      target_mem := fun rank ↦ (hfixedSubseq rank).1.target_mem
      mover_debt_exact := fun rank ↦
        (hfixedSubseq rank).1.mover_debt_exact
      aggregate_transfer := fun rank ↦
        (hfixedSubseq rank).1.aggregate_transfer
      recipient_floor := fun rank ↦
        (hfixedSubseq rank).1.recipient_floor
      routed_no_loss := fun rank ↦ by
        simpa only [selectedTargetStageMass, routed,
          (hfixedSubseq rank).2] using
            (hfixedSubseq rank).1.routed_no_loss }⟩

/-- The gain arm of the four-player specialization, retaining the general
source and routing certificate while exposing the packet's literal
`mu^2 D_*/64` and `mu^2 D_*/384` floors. -/
structure FinFourRoutedTransferSubsequence
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (atom : QuittingMinimumLawCausalSuffixAtom reward point) where
  transfer : RoutedTransferSubsequence reward point atom
  gain_floor_finFour : ∀ rank,
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 / 64 ≤
      endpointGain reward transfer.rows.profiles transfer.rows.roots
        transfer.rows.mark (transfer.subseq rank) transfer.mover
  recipient_floor_finFour : ∀ rank,
    point.2 (some atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum point.1 / 384 ≤
      quittingTerminalSemanticDebtChange
        (sourcePair reward transfer.rows.profiles transfer.rows.roots
          (transfer.subseq rank))
        (targetPair reward transfer.rows.profiles transfer.rows.roots
          transfer.rows.mark (transfer.subseq rank) transfer.mover)
        transfer.recipient

/-- Literal four-player form of the corrected deep composition.  The first
arm has the same `mu^2 D_*/16` tail floor as the general theorem; the second
arm exposes the exact `/64` mover and `/384` recipient floors. -/
theorem QuittingMinimumLawCausalSuffixAtom.nonempty_finFourTailEscape_or_routedTransfer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (atom : QuittingMinimumLawCausalSuffixAtom reward point)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum point.1)
    (hcollision : 1 < atom.terminal.val.card) :
    Nonempty (TailEscapeSubsequence reward point atom) ∨
      Nonempty (FinFourRoutedTransferSubsequence reward point atom) := by
  have hgeneral :=
    QuittingMinimumLawCausalSuffixAtom.nonempty_tailEscape_or_routedTransferSubsequence
      reward point atom hpoint hminimum hpositive hcollision
  rcases hgeneral with htail | htransfer
  · exact Or.inl htail
  · right
    obtain ⟨transfer⟩ := htransfer
    refine ⟨⟨transfer, ?_, ?_⟩⟩
    · intro rank
      have hfloor := transfer.gain_floor rank
      norm_num at hfloor ⊢
      exact hfloor
    · intro rank
      have hfloor := transfer.recipient_floor rank
      norm_num at hfloor ⊢
      exact hfloor

end QuittingNonsingletonMinimumLawTransfer

end GameTheory
