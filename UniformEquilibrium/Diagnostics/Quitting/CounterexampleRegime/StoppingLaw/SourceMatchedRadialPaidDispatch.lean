/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.FreshSquareExtraction
import MathUE.Topology.FiniteLabelLiminfExtraction
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedRadialResetCube
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreementOrientation

/-!
# Paid temporal dispatch for a source-matched radial cap square

A negative square of the source-matched radial best-response cap is first
localized to two fresh active coordinates.  The fixed-witness `O(lambda^2)`
bound then produces an oriented pure-time witness switch.  Unlike a
Prop-valued Quit/Continue comparison, the carrier below retains the square,
the literal source and receiving profiles, the ordered witnesses, and the
exact reached live mass.

Temporal orientation consumes the carrier in two ways.  A later receiving
witness is already a legal owner deviation.  An earlier receiving witness,
together with the terminal exploitability barrier and a sharp approximation
budget, reaches a legal outsider endpoint.  The latter is a connection to
the live atomic leaf; it is not an elimination of that leaf or a reset-chord
re-entry theorem.
-/

noncomputable section

namespace GameTheory

open Math.Finset.CubicalResetIntegrability Math.Optimization

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-- Full data retained after localizing and consuming one negative radial cap
square.  `diagonal` records which of the two literal receiving diagonals was
selected by the oriented supremum switch. -/
structure QuittingSourceMatchedRadialPaidSquare
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold charge eta : ℝ) where
  base : Finset {who // who ∈ frontier.active}
  first : {who // who ∈ frontier.active}
  second : {who // who ∈ frontier.active}
  first_fresh : first ∉ base
  second_fresh : second ∉ base
  distinct : first ≠ second
  negativeSquare : threshold < square
    (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
      hweight1 observer face) base first second
  source : (quittingGame reward).BehaviorProfile
  receiving : (quittingGame reward).BehaviorProfile
  diagonal :
    let data := frontier.sourceMatchedRadialResetCubeData rank weight
      hweight0 hweight1
    (source = data.profile
          (frontier.sourceMatchedRadialActiveFace
            (insert second (insert first base))) ∧
        receiving = data.profile
          (frontier.sourceMatchedRadialActiveFace base)) ∨
      (source = data.profile
          (frontier.sourceMatchedRadialActiveFace (insert first base)) ∧
        receiving = data.profile
          (frontier.sourceMatchedRadialActiveFace (insert second base)))
  certificate : QuittingPureTimeWitnessSwitchCertificate reward source receiving
    observer charge eta
  row : QuittingPaidFirstDisagreementRow reward receiving observer (charge + eta)
  row_source : row.sourceWitness = certificate.switch.sourceWitness
  row_receiving : row.receivingWitness = certificate.switch.receivingWitness

/-- A localized negative cap square above the fixed-witness quadratic budget
produces a data-bearing paid first-disagreement carrier. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_radialPaidSquare_of_negativeSquare
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hbudget : charge +
        4 * quittingRewardBound reward * frontier.lambda (frontier.subseq rank) *
          frontier.lambda (frontier.subseq rank) + 3 * eta ≤ threshold)
    (hnegative : HasSquareAboveAlong
      (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
        hweight1 observer face) threshold ∅
      (Finset.univ : Finset {who // who ∈ frontier.active}).toList) :
    Nonempty (QuittingSourceMatchedRadialPaidSquare frontier rank weight
      hweight0 hweight1 observer threshold charge eta) := by
  let activeWord :=
    (Finset.univ : Finset {who // who ∈ frontier.active}).toList
  have hwordNodup : activeWord.Nodup :=
    (Finset.univ : Finset {who // who ∈ frontier.active}).nodup_toList
  have hwordDisjoint : Disjoint activeWord.toFinset
      (∅ : Finset {who // who ∈ frontier.active}) := by simp
  obtain ⟨base, first, second, hfirst, hsecond, hne, hsquare⟩ :=
    exists_fresh_square_of_hasSquareAboveAlong
      (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
        hweight1 observer face) threshold ∅ activeWord hwordNodup
          hwordDisjoint (by simpa only [activeWord] using hnegative)
  let cap := frontier.sourceMatchedRadialFaceCap rank weight hweight0 hweight1
    observer
  have hnegSquareEq :
      square (fun face ↦ -cap face) base first second =
        -square cap base first second := by
    simp [square, edge]
    ring
  have hsquare' : threshold < -square cap base first second := by
    rw [← hnegSquareEq]
    simpa only [cap] using hsquare
  let q := 4 * quittingRewardBound reward *
    frontier.lambda (frontier.subseq rank) *
      frontier.lambda (frontier.subseq rank)
  have hcapSquareNegative : square cap base first second < 0 := by
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (quittingRewardBound_nonneg reward))
          (frontier.lambda_pos (frontier.subseq rank)).le)
        (frontier.lambda_pos (frontier.subseq rank)).le
    nlinarith
  have hcurvature : charge + q + 3 * eta ≤
      |square cap base first second| := by
    rw [abs_of_neg hcapSquareNegative]
    dsimp only [q]
    linarith
  let data := frontier.sourceMatchedRadialResetCubeData rank weight
    hweight0 hweight1
  let x00 := data.profile (frontier.sourceMatchedRadialActiveFace base)
  let x10 := data.profile
    (frontier.sourceMatchedRadialActiveFace (insert first base))
  let x01 := data.profile
    (frontier.sourceMatchedRadialActiveFace (insert second base))
  let x11 := data.profile
    (frontier.sourceMatchedRadialActiveFace (insert second (insert first base)))
  have hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q := by
    intro quitTime
    have hfixed := frontier.abs_sourceMatchedRadialFacePayoff_square_le
      rank weight hweight0 hweight1 observer quitTime base first second hfirst
        hsecond (by simpa using hne) (quittingRewardBound reward)
          (quittingRewardBound_nonneg reward)
            (abs_reward_le_quittingRewardBound reward)
    convert hfixed using 1
    all_goals
      simp only [square, edge, sourceMatchedRadialFacePayoff, data, x00, x10,
        x01, x11]
      ring_nf
  have hcurvature' : charge + q + 3 * eta ≤
      |quittingContinuationBestResponseValue reward x11 observer -
          quittingContinuationBestResponseValue reward x10 observer -
          quittingContinuationBestResponseValue reward x01 observer +
          quittingContinuationBestResponseValue reward x00 observer| := by
    convert hcurvature using 1
    all_goals
      simp only [cap, square, edge, sourceMatchedRadialFaceCap, data, x00, x10,
        x01, x11]
      ring_nf
  have hswitch :=
    exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature reward
      x00 x10 x01 x11 observer q charge eta hcharge heta hface hcurvature'
  have hpositive : 0 < charge + eta := add_pos hcharge heta
  rcases hswitch with hcertificate | hcertificate
  · obtain ⟨certificate⟩ := hcertificate
    obtain ⟨row, hrowSource, hrowReceiving⟩ :=
      certificate.exists_paidFirstDisagreementRow hpositive
    exact ⟨{
      base := base
      first := first
      second := second
      first_fresh := hfirst
      second_fresh := hsecond
      distinct := hne
      negativeSquare := hsquare
      source := x11
      receiving := x00
      diagonal := Or.inl ⟨rfl, rfl⟩
      certificate := certificate
      row := row
      row_source := hrowSource
      row_receiving := hrowReceiving
    }⟩
  · obtain ⟨certificate⟩ := hcertificate
    obtain ⟨row, hrowSource, hrowReceiving⟩ :=
      certificate.exists_paidFirstDisagreementRow hpositive
    exact ⟨{
      base := base
      first := first
      second := second
      first_fresh := hfirst
      second_fresh := hsecond
      distinct := hne
      negativeSquare := hsquare
      source := x10
      receiving := x01
      diagonal := Or.inr ⟨rfl, rfl⟩
      certificate := certificate
      row := row
      row_source := hrowSource
      row_receiving := hrowReceiving
    }⟩

/-- Strategic orientation of one localized radial paid square.  The owner
branch stores a full legal behavior deviation of size `charge + eta`.  The
outsider branch stores both the reached endpoint gain and its full behavior
splice at the exact first-disagreement history. -/
inductive QuittingSourceMatchedRadialStrategicDispatch
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {rank : ℕ} {weight : {who // who ∈ frontier.active} → ℝ}
    {hweight0 : ∀ mover, 0 ≤ weight mover}
    {hweight1 : ∀ mover, weight mover ≤ 1}
    {observer : ι} {threshold charge eta gamma : ℝ}
    (carrier : QuittingSourceMatchedRadialPaidSquare frontier rank weight
      hweight0 hweight1 observer threshold charge eta) : Type
  | owner
      (hlater : carrier.row.receivingEarlier = false)
      (deviation : (quittingGame reward).BehaviorStrategy observer)
      (gain_le :
        let profile := Function.update carrier.receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            carrier.row.sourceWitness)
        quittingTerminalPayoff reward profile observer + (charge + eta) ≤
          quittingTerminalPayoff reward
            (Function.update profile observer deviation) observer) :
      QuittingSourceMatchedRadialStrategicDispatch carrier
  | outsider
      (hearlier : carrier.row.receivingEarlier = true)
      (who : ι) (hwho : who ≠ observer) (action : Bool)
      (endpoint_gain :
        let profile := Function.update carrier.receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            carrier.row.receivingWitness)
        gamma * (charge + eta) / (2 * quittingRewardBound reward) ≤
          carrier.row.liveMass *
            (quittingRootExpectedPayoff reward 0
                (Function.update
                  (quittingProfileLiveRoot reward profile carrier.row.start)
                  who (PMF.pure action)) who -
              quittingRootExpectedPayoff reward 0
                (quittingProfileLiveRoot reward profile carrier.row.start) who))
      (behavior_gain :
        let profile := Function.update carrier.receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            carrier.row.receivingWitness)
        let deviation := quittingStagePureEndpointBehaviorDeviation reward
          profile who carrier.row.start action
        gamma * (charge + eta) / (2 * quittingRewardBound reward) ≤
          quittingTerminalPayoff reward
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward profile who) :
      QuittingSourceMatchedRadialStrategicDispatch carrier

/-- **Finite-scale radial temporal dispatch.**  A negative cap square above
the exact fixed-witness `4 M lambda^2` budget produces a literal paid square
and consumes its temporal orientation.  The earlier-receiving branch uses
the counterexample regime's global terminal gap; the displayed strict error
budget is exactly the hypothesis needed by the atomic barrier argument. -/
theorem QuittingCounterexampleStoppingLawFrontier.exists_radialStrategicDispatch_of_negativeSquare
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hbudget : charge +
        4 * quittingRewardBound reward * frontier.lambda (frontier.subseq rank) *
          frontier.lambda (frontier.subseq rank) + 3 * eta ≤ threshold)
    (hsmall : eta < regime.terminalGap * (charge + eta) /
      (2 * quittingRewardBound reward))
    (hnegative : HasSquareAboveAlong
      (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
        hweight1 observer face) threshold ∅
      (Finset.univ : Finset {who // who ∈ frontier.active}).toList) :
    ∃ carrier : QuittingSourceMatchedRadialPaidSquare frontier rank weight
        hweight0 hweight1 observer threshold charge eta,
      Nonempty (QuittingSourceMatchedRadialStrategicDispatch
        (gamma := regime.terminalGap) carrier) := by
  obtain ⟨carrier⟩ := frontier.exists_radialPaidSquare_of_negativeSquare
    rank weight hweight0 hweight1 observer threshold charge eta hcharge heta
      hbudget hnegative
  have hpositive : 0 < charge + eta := add_pos hcharge heta
  have happrox :
      quittingContinuationBestResponseValue reward carrier.receiving observer -
          eta ≤
        quittingPureTimeDeviationPayoff reward carrier.receiving observer
          carrier.row.receivingWitness := by
    rw [carrier.row_receiving]
    simpa only [
      quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
      using carrier.certificate.switch.receiving_approx
  cases htime : carrier.row.receivingEarlier with
  | false =>
      obtain ⟨deviation, hdeviation⟩ :=
        carrier.row.exists_ownerDeviation_of_receivingLater htime
      exact ⟨carrier, ⟨.owner htime deviation hdeviation⟩⟩
  | true =>
      obtain ⟨who, hwho, action, hendpoint, hbehavior⟩ :=
        carrier.row.exists_outsiderDeviation_of_receivingEarlier htime hpositive
          regime.terminalGap_pos regime.terminalExploitability happrox hsmall
      exact ⟨carrier, ⟨.outsider htime who hwho action hendpoint hbehavior⟩⟩

/-- Cap nonadditivity is either within the triangular square budget or is
consumed by the data-bearing temporal strategic dispatch. -/
theorem QuittingCounterexampleStoppingLawFrontier.radialCapNonadditivity_le_or_strategicDispatch
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hbudget : charge +
        4 * quittingRewardBound reward * frontier.lambda (frontier.subseq rank) *
          frontier.lambda (frontier.subseq rank) + 3 * eta ≤ threshold)
    (hsmall : eta < regime.terminalGap * (charge + eta) /
      (2 * quittingRewardBound reward)) :
    finiteCubeCapNonadditivity
          (frontier.sourceMatchedRadialFaceCap rank weight hweight0 hweight1
            observer) ≤
        (squareCount
          (Finset.univ : Finset {who // who ∈ frontier.active}).toList : ℝ) *
          threshold ∨
      ∃ carrier : QuittingSourceMatchedRadialPaidSquare frontier rank weight
          hweight0 hweight1 observer threshold charge eta,
        Nonempty (QuittingSourceMatchedRadialStrategicDispatch
          (gamma := regime.terminalGap) carrier) := by
  rcases frontier.sourceMatchedRadialFaceCapNonadditivity_le_or_hasNegativeSquare
      rank weight hweight0 hweight1 observer threshold with hnear | hnegative
  · exact Or.inl hnear
  · exact Or.inr
      (frontier.exists_radialStrategicDispatch_of_negativeSquare rank weight
        hweight0 hweight1 observer threshold charge eta hcharge heta hbudget
          hsmall hnegative)

/-- The finite strategic label retained by a radial temporal dispatch.  The
owner branch has one common label; an outsider branch remembers the actual
outsider. -/
def QuittingSourceMatchedRadialStrategicDispatch.label
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {rank : ℕ} {weight : {who // who ∈ frontier.active} → ℝ}
    {hweight0 : ∀ mover, 0 ≤ weight mover}
    {hweight1 : ∀ mover, weight mover ≤ 1}
    {observer : ι} {threshold charge eta gamma : ℝ}
    {carrier : QuittingSourceMatchedRadialPaidSquare frontier rank weight
      hweight0 hweight1 observer threshold charge eta}
    (dispatch : QuittingSourceMatchedRadialStrategicDispatch
      (gamma := gamma) carrier) : Sum Unit ι :=
  match dispatch with
  | .owner .. => Sum.inl ()
  | .outsider _ who .. => Sum.inr who

/-- The legal source-unit gain certified by a radial temporal dispatch. -/
def QuittingSourceMatchedRadialStrategicDispatch.gain
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {rank : ℕ} {weight : {who // who ∈ frontier.active} → ℝ}
    {hweight0 : ∀ mover, 0 ≤ weight mover}
    {hweight1 : ∀ mover, weight mover ≤ 1}
    {observer : ι} {threshold charge eta gamma : ℝ}
    {carrier : QuittingSourceMatchedRadialPaidSquare frontier rank weight
      hweight0 hweight1 observer threshold charge eta}
    (dispatch : QuittingSourceMatchedRadialStrategicDispatch
      (gamma := gamma) carrier) : ℝ :=
  match dispatch with
  | .owner .. => charge + eta
  | .outsider .. => gamma * (charge + eta) /
      (2 * quittingRewardBound reward)

/-- Every temporal branch retains at least the smaller of the owner factor
`1` and the outsider factor `gamma / (2M)` times the paid receiving edge. -/
theorem QuittingSourceMatchedRadialStrategicDispatch.min_factor_mul_le_gain
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    {rank : ℕ} {weight : {who // who ∈ frontier.active} → ℝ}
    {hweight0 : ∀ mover, 0 ≤ weight mover}
    {hweight1 : ∀ mover, weight mover ≤ 1}
    {observer : ι} {threshold charge eta gamma : ℝ}
    {carrier : QuittingSourceMatchedRadialPaidSquare frontier rank weight
      hweight0 hweight1 observer threshold charge eta}
    (dispatch : QuittingSourceMatchedRadialStrategicDispatch
      (gamma := gamma) carrier)
    (hpaid : 0 < charge + eta) (hgamma : 0 < gamma) :
    min 1 (gamma / (2 * quittingRewardBound reward)) * (charge + eta) ≤
      dispatch.gain := by
  have hlive0 : 0 ≤ carrier.row.liveMass := by
    rw [carrier.row.liveMass_eq]
    exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
  have hbound : 0 < quittingRewardBound reward := by
    nlinarith [carrier.row.gain_le_liveMass]
  cases dispatch with
  | owner =>
      simp only [QuittingSourceMatchedRadialStrategicDispatch.gain]
      have hmin : min 1 (gamma / (2 * quittingRewardBound reward)) ≤ 1 :=
        min_le_left _ _
      nlinarith
  | outsider =>
      simp only [QuittingSourceMatchedRadialStrategicDispatch.gain]
      have hmin : min 1 (gamma / (2 * quittingRewardBound reward)) ≤
          gamma / (2 * quittingRewardBound reward) := min_le_right _ _
      have hfactor0 : 0 < gamma / (2 * quittingRewardBound reward) := by
        positivity
      calc
        min 1 (gamma / (2 * quittingRewardBound reward)) * (charge + eta) ≤
            (gamma / (2 * quittingRewardBound reward)) * (charge + eta) :=
          mul_le_mul_of_nonneg_right hmin hpaid.le
        _ = gamma * (charge + eta) /
            (2 * quittingRewardBound reward) := by ring

/-- **Asymptotic fixed-label consequence.**  For any sequence of localized
radial paid squares and their strategic dispatches, a first-order lower bound
for `(charge + eta) / lambda` yields, after a strict subsequence, one fixed
owner/outsider label with lower bound

`kappa * min 1 (gamma / (2M))`.

This statement permits the first-disagreement dates to diverge: their exact
live masses have already been incorporated into each dispatch's legal gain. -/
theorem exists_fixed_radialStrategicLabel_of_scaleNormalizedLiminfLower
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ → ℕ)
    (weight : ℕ → {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ n mover, 0 ≤ weight n mover)
    (hweight1 : ∀ n mover, weight n mover ≤ 1)
    (observer : ι) (threshold charge eta scale : ℕ → ℝ)
    (carrier : ∀ n, QuittingSourceMatchedRadialPaidSquare frontier (rank n)
      (weight n) (hweight0 n) (hweight1 n) observer (threshold n)
        (charge n) (eta n))
    (dispatch : ∀ n, QuittingSourceMatchedRadialStrategicDispatch
      (gamma := regime.terminalGap) (carrier n))
    (hscale : ∀ n, 0 < scale n)
    (hpaid : ∀ n, 0 < charge n + eta n)
    (kappa : ℝ)
    (hlower : Math.HasScaleNormalizedLiminfLower
      (fun n ↦ charge n + eta n) scale kappa) :
    ∃ fixed : Sum Unit ι, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧
        (∀ n, (dispatch (subseq n)).label = fixed) ∧
        Math.HasScaleNormalizedLiminfLower
          ((fun n ↦ (dispatch n).gain) ∘ subseq)
          (scale ∘ subseq)
          (min 1 (regime.terminalGap /
              (2 * quittingRewardBound reward)) * kappa) := by
  let factor := min 1
    (regime.terminalGap / (2 * quittingRewardBound reward))
  have hbound : 0 < quittingRewardBound reward := by
    have hlive0 : 0 ≤ (carrier 0).row.liveMass := by
      rw [(carrier 0).row.liveMass_eq]
      exact quittingOpponentSurvivalWeight_nonneg _ _ _ _
    nlinarith [(carrier 0).row.gain_le_liveMass, hpaid 0]
  have hfactor : 0 < factor := by
    dsimp only [factor]
    exact lt_min (by norm_num)
      (div_pos regime.terminalGap_pos (mul_pos (by norm_num) hbound))
  have hdispatchLower : ∀ n,
      factor * (charge n + eta n) ≤ (dispatch n).gain := by
    intro n
    exact (dispatch n).min_factor_mul_le_gain (hpaid n)
      regime.terminalGap_pos
  have hgainLower : Math.HasScaleNormalizedLiminfLower
      (fun n ↦ (dispatch n).gain) scale (factor * kappa) :=
    hlower.of_factor_le hfactor hscale hdispatchLower
  obtain ⟨fixed, subseq, hsubseq, hfixed, hfinal⟩ :=
    Math.exists_fixedLabel_subsequence_of_scaleNormalizedLiminfLower
      (fun n ↦ (dispatch n).label) (fun n ↦ (dispatch n).gain) scale
        (factor * kappa) hgainLower
  exact ⟨fixed, subseq, hsubseq, hfixed, by
    simpa only [factor] using hfinal⟩

end GameTheory
