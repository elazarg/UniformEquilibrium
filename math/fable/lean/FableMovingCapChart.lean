/-
Moving cap-chart cocycle and a conditional finite-forward-packet lift.

Two horizontal operations occur in a literal paid quitting chain: prefix the
current actual profile by an exact cap--Nash product root, and replace one
player's whole behavioral strategy, using the literal target as the next
source.  This file records the exact vector cocycle relating the caps of the
moving actual sources to the abstract Bellman chart advanced by the same
selected roots, and compiles the uniform smallness of that cocycle into the
repository's finite forward packet interface.

The continuation vector of a product root is read at exactly one outcome, all
Continue.  Hence the successor map is affine with slope the all-Continue mass,
which is the checked difference identity
`quittingRootSuccessorPayoff_sub_eq_continueMass_mul`.  Against an exact
cap--Nash root the literal root-then-continuation profile has cap the Bellman
successor of the source cap, so the chart error obeys
`e (m + 1) = c (q m) * e m + leakage m`, with `leakage m` the signed cap
displacement caused by the one-player replacement.  That leakage vanishes at
the mover coordinate, because the unrestricted cap of a player is invariant
under replacing that same player's own strategy.

Uniform coordinatewise smallness of the chart error transports the exact root
at the actual cap to a support-approximately-Nash root at the chart value, and
the chart then lies in one compact payoff box fixed by the reward bound alone.
The packet's charge field is the cumulative exact-root absorption.

Nothing here produces such chains.  The smallness hypothesis is carried, not
discharged; the file is a consumer interface for it.
-/
import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso
import UniformEquilibrium.Quitting.Projective.Lasso
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorForward
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 2: the two exact one-step identities -/

omit [DecidableEq ι] in
/-- **(2.1) Successor difference identity.**  A product root reads its
continuation vector only on the all-Continue outcome, so the Bellman successor
map is affine in each coordinate with slope the all-Continue mass.  This is the
production identity, restated under the moving-chart name. -/
theorem quittingMovingCapSuccessor_sub_eq_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward first root who -
        quittingRootSuccessorPayoff reward second root who =
      quittingStationaryContinueMass root * (first who - second who) :=
  quittingRootSuccessorPayoff_sub_eq_continueMass_mul reward first second root who

/-- **(2.2) Exact cap-prefix identity.**  If a product root is exactly Nash
against the unrestricted behavioral cap of a continuation profile, then the
literal root-then-continuation profile has cap the Bellman successor of that
cap. -/
theorem quittingContinuationBestResponse_rootThenContinuation_of_capNash
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (hnash : IsεQuittingRootNash reward
      (quittingContinuationBestResponse reward continuation) 0 root) :
    quittingContinuationBestResponse reward
        (quittingRootThenContinuationProfile reward root continuation) =
      quittingRootSuccessorPayoff reward
        (quittingContinuationBestResponse reward continuation) root := by
  have hpair := quittingTerminalSemanticPair_rootThenContinuation
    reward root continuation
  have henvelope :=
    quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
      (reward := reward) (quittingTerminalSemanticPair reward continuation)
      root hnash
  show (quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation)).2 = _
  rw [hpair, henvelope]
  rfl

/-- The behavioral punishment value is a lower bound for every literal
profile's unrestricted cap: the cap is one particular best-reply value, and the
punishment value is the infimum of those. -/
theorem quittingPunishmentValue_le_continuationBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingPunishmentValue reward who ≤
      quittingContinuationBestResponseValue reward profile who := by
  have hfloor := quittingPunishmentValue_le reward who profile
  simpa [quittingBestReplyValue, iSup,
    quittingContinuationBestResponseValue] using hfloor

/-! ## Section 3: the moving Bellman chart -/

/-- The abstract Bellman chart of a root word, started at a prescribed payoff
vector and advanced by the phase-varying roots. -/
def quittingMovingCapChart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : Payoff ι) : ℕ → Payoff ι
  | 0 => start
  | step + 1 =>
      quittingRootSuccessorPayoff reward
        (quittingMovingCapChart reward roots start step) (roots step)

omit [DecidableEq ι] in
@[simp] theorem quittingMovingCapChart_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : Payoff ι) :
    quittingMovingCapChart reward roots start 0 = start := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingMovingCapChart_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : Payoff ι) (step : ℕ) :
    quittingMovingCapChart reward roots start (step + 1) =
      quittingRootSuccessorPayoff reward
        (quittingMovingCapChart reward roots start step) (roots step) := rfl

/-- One compact payoff box, fixed by the reward bound alone: the reward box
enlarged by one.  It does not depend on the horizon, the charge target, or the
chart tolerance below one. -/
def quittingMovingCapChartCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Set (Payoff ι) :=
  Set.Icc (fun _ : ι => -(quittingRewardBound reward + 1))
    (fun _ : ι => quittingRewardBound reward + 1)

omit [DecidableEq ι] in
theorem quittingMovingCapChartCarrier_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingMovingCapChartCarrier reward) :=
  isCompact_Icc

/-- **Literal moving cap chain data.**  Actual behavioral profiles, one exact
cap--Nash product root per step, and one literal single-player behavioral
replacement per step whose target is the next source.  Only the prefix
`step < horizon` is constrained. -/
structure QuittingMovingCapChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (horizon : ℕ) where
  /-- The actual behavioral sources `P m`. -/
  profile : ℕ → (quittingGame reward).BehaviorProfile
  /-- The selected product roots `q m`. -/
  root : ℕ → ι → PMF Bool
  /-- The player replaced at each step. -/
  mover : ℕ → ι
  /-- The replacing behavioral strategy at each step. -/
  response : ∀ step : ℕ, (quittingGame reward).BehaviorStrategy (mover step)
  /-- `q m` is exactly Nash against the unrestricted cap of `P m`. -/
  capNash : ∀ step : ℕ, step < horizon →
    IsεQuittingRootNash reward
      (quittingContinuationBestResponse reward (profile step)) 0 (root step)
  /-- `P (m + 1)` is a literal one-player replacement of `q m ⋆ P m`. -/
  moverUpdate : ∀ step : ℕ, step < horizon →
    profile (step + 1) =
      Function.update
        (quittingRootThenContinuationProfile reward (root step) (profile step))
        (mover step) (response step)

namespace QuittingMovingCapChain

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {horizon : ℕ}
variable (chain : QuittingMovingCapChain reward horizon)

/-- The actual source cap `B (P m)`. -/
def sourceCap (step : ℕ) : Payoff ι :=
  quittingContinuationBestResponse reward (chain.profile step)

/-- The literal prefix profile `S (m + 1) = q m ⋆ P m`. -/
def prefixProfile (step : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (chain.root step) (chain.profile step)

/-- The moving Bellman chart `v m`, started at the initial actual cap. -/
def chart (step : ℕ) : Payoff ι :=
  quittingMovingCapChart reward chain.root (chain.sourceCap 0) step

/-- **(2.3) Signed cap leakage.**  Indexed by its source step: `capLeakage m`
is the note's `ℓ (m + 1) = B (P (m + 1)) - B (S (m + 1))`. -/
def capLeakage (step : ℕ) : Payoff ι :=
  fun who => chain.sourceCap (step + 1) who -
    quittingContinuationBestResponse reward (chain.prefixProfile step) who

/-- **(3.2) Chart error** `e m = B (P m) - v m`. -/
def chartError (step : ℕ) : Payoff ι :=
  fun who => chain.sourceCap step who - chain.chart step who

theorem chartError_eq (step : ℕ) (who : ι) :
    chain.chartError step who =
      chain.sourceCap step who - chain.chart step who := rfl

theorem capLeakage_eq (step : ℕ) (who : ι) :
    chain.capLeakage step who =
      chain.sourceCap (step + 1) who -
        quittingContinuationBestResponse reward (chain.prefixProfile step) who := rfl

@[simp] theorem chart_zero : chain.chart 0 = chain.sourceCap 0 := rfl

theorem chart_succ (step : ℕ) :
    chain.chart (step + 1) =
      quittingRootSuccessorPayoff reward (chain.chart step) (chain.root step) := rfl

/-- **(2.2) on the chain.**  The cap of the literal prefix profile is the
Bellman successor of the source cap. -/
theorem prefixProfile_cap (step : ℕ) (hstep : step < horizon) :
    quittingContinuationBestResponse reward (chain.prefixProfile step) =
      quittingRootSuccessorPayoff reward (chain.sourceCap step) (chain.root step) :=
  quittingContinuationBestResponse_rootThenContinuation_of_capNash
    (chain.root step) (chain.profile step) (chain.capNash step hstep)

/-- **(2.4) Mover zero leakage.**  The unrestricted cap of the moving player is
unchanged by replacing that same player's own strategy. -/
theorem capLeakage_mover (step : ℕ) (hstep : step < horizon) :
    chain.capLeakage step (chain.mover step) = 0 := by
  have hself := quittingContinuationBestResponseValue_update_self reward
    (chain.prefixProfile step) (chain.mover step) (chain.response step)
  have hsource : chain.sourceCap (step + 1) (chain.mover step) =
      quittingContinuationBestResponse reward (chain.prefixProfile step)
        (chain.mover step) := by
    show quittingContinuationBestResponseValue reward
      (chain.profile (step + 1)) (chain.mover step) = _
    rw [chain.moverUpdate step hstep]
    exact hself
  rw [chain.capLeakage_eq step (chain.mover step), hsource, sub_self]

theorem chartError_zero (who : ι) : chain.chartError 0 who = 0 := by
  rw [chain.chartError_eq 0 who, chain.chart_zero, sub_self]

/-- **(3.3) The exact cocycle.**  The chart error is transported by the
all-Continue mass of the step's exact root and displaced by that step's signed
cap leakage. -/
theorem chartError_succ (step : ℕ) (hstep : step < horizon) (who : ι) :
    chain.chartError (step + 1) who =
      quittingStationaryContinueMass (chain.root step) * chain.chartError step who +
        chain.capLeakage step who := by
  have hcap := congrFun (chain.prefixProfile_cap step hstep) who
  have hdiff := quittingMovingCapSuccessor_sub_eq_continueMass_mul
    reward (chain.sourceCap step) (chain.chart step) (chain.root step) who
  rw [chain.chartError_eq (step + 1) who, chain.chartError_eq step who,
    chain.capLeakage_eq step who, chain.chart_succ step, hcap]
  linarith

/-- **(3.4) The unfolded cocycle.**  Since the chart starts at the actual cap,
the error at every step is the survival-transported signed prefix sum of the
leakages, with the empty transport product equal to one. -/
theorem chartError_eq_sum (step : ℕ) (hstep : step ≤ horizon) (who : ι) :
    chain.chartError step who =
      ∑ index ∈ Finset.range step,
        (∏ later ∈ Finset.Ico (index + 1) step,
          quittingStationaryContinueMass (chain.root later)) *
          chain.capLeakage index who := by
  induction step with
  | zero => simpa using chain.chartError_zero who
  | succ step ih =>
      have hstepLt : step < horizon := Nat.lt_of_lt_of_le (Nat.lt_succ_self step) hstep
      rw [chain.chartError_succ step hstepLt who, ih (le_of_lt hstepLt),
        Finset.sum_range_succ, Finset.mul_sum]
      have hlast : (∏ later ∈ Finset.Ico (step + 1) (step + 1),
          quittingStationaryContinueMass (chain.root later)) = 1 := by
        simp
      have hshift : ∀ index ∈ Finset.range step,
          quittingStationaryContinueMass (chain.root step) *
              ((∏ later ∈ Finset.Ico (index + 1) step,
                quittingStationaryContinueMass (chain.root later)) *
                chain.capLeakage index who) =
            (∏ later ∈ Finset.Ico (index + 1) (step + 1),
              quittingStationaryContinueMass (chain.root later)) *
              chain.capLeakage index who := by
        intro index hindex
        have hle : index + 1 ≤ step := Finset.mem_range.mp hindex
        rw [Finset.prod_Ico_succ_top hle]
        ring
      rw [Finset.sum_congr rfl hshift, hlast, one_mul]

/-! ## Section 4: support transport from the actual cap to the chart -/

theorem abs_sourceCap_le (step : ℕ) (who : ι) :
    |chain.sourceCap step who| ≤ quittingRewardBound reward :=
  abs_quittingContinuationBestResponseValue_le reward (chain.profile step) who
    (abs_reward_le_quittingRewardBound reward)

theorem punishmentValue_le_sourceCap (step : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤ chain.sourceCap step who :=
  quittingPunishmentValue_le_continuationBestResponseValue reward
    (chain.profile step) who

/-- **Section 4 stability.**  An exact root at the actual cap is a
support-`ε` Nash root at the chart value whenever the chart error is at most
`ε` coordinatewise. -/
theorem chart_isQuittingRootSupportApproxNash {ε : ℝ} {step : ℕ}
    (hstep : step < horizon)
    (hclose : ∀ who, |chain.chartError step who| ≤ ε) :
    IsQuittingRootSupportApproxNash reward (chain.chart step) ε (chain.root step) := by
  have hexact := isQuittingRootSupportApproxNash_zero_of_isZeroNash
    reward (chain.sourceCap step) (chain.root step) (chain.capNash step hstep)
  have hdistance : ∀ who,
      |chain.chart step who - chain.sourceCap step who| ≤ ε := by
    intro who
    have hnegate : chain.chart step who - chain.sourceCap step who =
        -(chain.chartError step who) := by
      rw [chain.chartError_eq step who]
      ring
    rw [hnegate, abs_neg]
    exact hclose who
  have htransport := isQuittingRootSupportApproxNash_of_tail_close
    reward (chain.root step) (chain.sourceCap step) (chain.chart step)
    hexact hdistance
  rw [zero_add] at htransport
  exact htransport

/-- Under a chart tolerance below one, every chart value lies in the compact
box fixed by the reward bound. -/
theorem chart_mem_carrier {ε : ℝ} (hε1 : ε ≤ 1) {step : ℕ}
    (hclose : ∀ who, |chain.chartError step who| ≤ ε) :
    chain.chart step ∈ quittingMovingCapChartCarrier reward := by
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · intro who
    have hcap := abs_le.mp (chain.abs_sourceCap_le step who)
    have herror := abs_le.mp (hclose who)
    rw [chain.chartError_eq step who] at herror
    show -(quittingRewardBound reward + 1) ≤ chain.chart step who
    linarith [herror.1, herror.2, hcap.1]
  · intro who
    have hcap := abs_le.mp (chain.abs_sourceCap_le step who)
    have herror := abs_le.mp (hclose who)
    rw [chain.chartError_eq step who] at herror
    show chain.chart step who ≤ quittingRewardBound reward + 1
    linarith [herror.1, herror.2, hcap.2]

/-! ## Section 5: the conditional finite-forward-packet lift -/

/-- **Theorem 5.1, packaged.**  A moving cap chain whose chart error stays
within `ε ≤ 1` up to the horizon, and whose cumulative exact-root absorption
reaches `chargeTarget`, is a finite forward Bellman packet at any support
tolerance at least `ε`, inside the fixed reward box enlarged by one. -/
def toForwardPacket {ε supportError chargeTarget : ℝ}
    (hε1 : ε ≤ 1) (hsupportError : ε ≤ supportError)
    (hchart : ∀ step, step ≤ horizon → ∀ who, |chain.chartError step who| ≤ ε)
    (hcharge : chargeTarget ≤
      ∑ step ∈ Finset.range horizon,
        (1 - quittingStationaryContinueMass (chain.root step))) :
    QuittingFiniteForwardPacket reward
      (quittingMovingCapChartCarrier reward) supportError chargeTarget where
  roots := chain.root
  value := chain.chart
  horizon := horizon
  value_mem := fun step hstep => chain.chart_mem_carrier hε1 (hchart step hstep)
  policy := fun step _ => chain.chart_succ step
  support := by
    intro step hstep who
    have hsupport := chain.chart_isQuittingRootSupportApproxNash hstep
      (hchart step (le_of_lt hstep))
    refine ⟨fun hquit => ?_, fun hcontinue => ?_⟩
    · have hbound := (hsupport who).1 hquit
      linarith
    · have hbound := (hsupport who).2 hcontinue
      linarith
  rational := by
    intro target step hstep
    have hfloor := chain.punishmentValue_le_sourceCap step target
    have herror := abs_le.mp (hchart step hstep target)
    rw [chain.chartError_eq step target] at herror
    linarith [herror.1, herror.2]
  chargeTarget_le := by
    refine hcharge.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun step _ => rfl

/-- **Theorem 5.1.**  The literal statement at support error `ε`. -/
theorem nonempty_forwardPacket {ε chargeTarget : ℝ}
    (_hε : 0 < ε) (hε1 : ε ≤ 1)
    (hchart : ∀ step, step ≤ horizon → ∀ who, |chain.chartError step who| ≤ ε)
    (hcharge : chargeTarget ≤
      ∑ step ∈ Finset.range horizon,
        (1 - quittingStationaryContinueMass (chain.root step))) :
    Nonempty (QuittingFiniteForwardPacket reward
      (quittingMovingCapChartCarrier reward) ε chargeTarget) :=
  ⟨chain.toForwardPacket hε1 le_rfl hchart hcharge⟩

/-! ## Section 7: the two-row form -/

/-- **(7.1) first row.**  `e 1 = ℓ 1`. -/
theorem chartError_one (hhorizon : 0 < horizon) (who : ι) :
    chain.chartError 1 who = chain.capLeakage 0 who := by
  have hstep := chain.chartError_succ 0 hhorizon who
  rw [show (1 : ℕ) = 0 + 1 from rfl, hstep, chain.chartError_zero who]
  ring

/-- **(7.1) second row.**  `e 2 = c (q 1) * ℓ 1 + ℓ 2`. -/
theorem chartError_two (hhorizon : 1 < horizon) (who : ι) :
    chain.chartError 2 who =
      quittingStationaryContinueMass (chain.root 1) * chain.capLeakage 0 who +
        chain.capLeakage 1 who := by
  have hstep := chain.chartError_succ 1 hhorizon who
  rw [show (2 : ℕ) = 1 + 1 from rfl, hstep,
    chain.chartError_one (Nat.lt_of_succ_lt hhorizon) who]

/-- **(7.2)**  The two displayed inequalities are exactly the two-row chart
hypothesis. -/
theorem twoRow_chartError_le {ε : ℝ} (hε : 0 ≤ ε) (hhorizon : 1 < horizon)
    (hfirst : ∀ who, |chain.capLeakage 0 who| ≤ ε)
    (hsecond : ∀ who,
      |quittingStationaryContinueMass (chain.root 1) * chain.capLeakage 0 who +
        chain.capLeakage 1 who| ≤ ε) :
    ∀ step, step ≤ 2 → ∀ who, |chain.chartError step who| ≤ ε := by
  intro step hstep who
  interval_cases step
  · rw [chain.chartError_zero who, abs_zero]
    exact hε
  · rw [chain.chartError_one (Nat.lt_of_succ_lt hhorizon) who]
    exact hfirst who
  · rw [chain.chartError_two hhorizon who]
    exact hsecond who

end QuittingMovingCapChain

/-- **(7.2) packaged.**  Two literal paid responses whose first leakage and
whose transported second leakage are both within `ε ≤ 1` form a two-row
forward packet.  Exact full-cap neutrality is sufficient but stronger than
needed: the second leakage may cancel the transported first one. -/
def quittingMovingCapTwoRowForwardPacket
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (chain : QuittingMovingCapChain reward 2) {ε chargeTarget : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfirst : ∀ who, |chain.capLeakage 0 who| ≤ ε)
    (hsecond : ∀ who,
      |quittingStationaryContinueMass (chain.root 1) * chain.capLeakage 0 who +
        chain.capLeakage 1 who| ≤ ε)
    (hcharge : chargeTarget ≤
      ∑ step ∈ Finset.range 2,
        (1 - quittingStationaryContinueMass (chain.root step))) :
    QuittingFiniteForwardPacket reward
      (quittingMovingCapChartCarrier reward) ε chargeTarget :=
  chain.toForwardPacket hε1 le_rfl
    (chain.twoRow_chartError_le hε one_lt_two hfirst hsecond) hcharge

/-- **Corollary 5.2.**  Moving cap chains with uniformly small chart error at
every tolerance and every charge target yield a uniform-equilibrium payoff,
through the checked finite-forward-packet compiler. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_movingCapChains
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproducer : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
      ∃ horizon : ℕ, ∃ chain : QuittingMovingCapChain reward horizon,
        (∀ step, step ≤ horizon → ∀ who, |chain.chartError step who| ≤ ε) ∧
          chargeTarget ≤ ∑ step ∈ Finset.range horizon,
            (1 - quittingStationaryContinueMass (chain.root step))) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
    reward (quittingMovingCapChartCarrier reward)
    (quittingMovingCapChartCarrier_isCompact reward)
  intro supportError hsupportError chargeTarget hchargeTarget
  have hpositive : 0 < min supportError 1 := lt_min hsupportError one_pos
  obtain ⟨horizon, chain, hchart, hcharge⟩ :=
    hproducer (min supportError 1) hpositive (min_le_right _ _)
      chargeTarget hchargeTarget
  exact ⟨chain.toForwardPacket (min_le_right _ _) (min_le_left _ _) hchart hcharge⟩

end GameTheory
