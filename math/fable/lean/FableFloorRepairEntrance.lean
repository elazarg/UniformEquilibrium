/-
Sequence-level entrance of the unique-debtor minimum-floor repair.

This file formalizes section 2 and the sequence-level part of section 3 of the
note `SOCIAL_WEIGHT_REVIEW__MINIMUM_FLOOR_REPAIR_TO_EXACT_PORT_AND_STRICT_CURL_NOGO`,
in the scope confirmed by its `CODEX_DESCENDANT` review.

Section 2 is a purely finite-dimensional carrier computation.  At a positive
global minimum `z = (U, B)` of terminal-semantic debt, the checked singleton
margin `D_* ≤ B_i - s_i` and the identity `d_i = B_i - U_i` give the payoff
margin `D_* - d_i ≤ U_i - s_i`, whose left-hand side is the tail debt sum
`∑_{k ≠ i} d_k`.  Carrier debts are nonnegative, so punishment normality
`Pun_i ≤ s_i` transfers to the all-player carrier floor `Pun_i ≤ U_i`, and two
distinct positive debt coordinates make every tail sum strictly positive.

Section 3 supplies actual profiles.  Nothing here re-derives the per-profile
softening semantics: the mover payoff affinity, the exactly frozen mover cap,
the uniform `2 M θ` observer control, and the retained paid pure-time pair all
come from `FableFloorRepairSoftening`.  What is added is the passage to a
sequence:

* the mover's pure-time gain `a_n` is eventually at least `D_* / 2`;
* every vanishing-debt observer's floor survives an arbitrary vanishing
  `2 M θ_n` loss, eventually;
* the note's weights `θ_n = 2 f_n / a_n`, clamped to `[0, 1]`, exist, vanish,
  and eventually satisfy the mover repair inequality; and
* the resulting softened sequence eventually meets every player's punishment
  floor while retaining a paid pure-time pair of gap at least `D_* / 2`, and
  its prescribed payoffs and caps still converge to the incoming minimum.

Everything sequence-level is stated for supplied coordinatewise semantic
convergence.  No profile sequence is constructed here, and no exact-port
consumer is invoked.
-/
import FableFloorRepairSoftening
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Stationary.MinMax

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability Math.ProbabilityMassFunction

open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## M1: the section 2 minimum inequalities -/

/-- The tail debt sum off one coordinate is total debt minus that coordinate.
This is `∑_{k ≠ i} d_k = D_* - d_i`. -/
theorem fableFloorRepair_sum_debt_erase_eq
    (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    ∑ other ∈ Finset.univ.erase who, quittingTerminalSemanticDebt pair other =
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_erase_eq_sub (Finset.mem_univ who)

/-- **M1(a), (2.1).**  At a positive global minimum of terminal-semantic debt,
every player's prescribed payoff exceeds its own singleton reward by at least
the debt of the other players. -/
theorem fableFloorRepair_minimum_payoff_margin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who ≤
      pair.1 who - reward (quittingSingletonTerminal who) who := by
  have hmargin := minimumTerminalSemantic_singletonMargin
    (reward := reward) pair hpair hminimum hpositive who
  unfold quittingTerminalSemanticDebt
  linarith

/-- **M1(a), tail-sum form.**  The same inequality with its left-hand side
written as the literal sum over the other players. -/
theorem fableFloorRepair_minimum_payoff_margin_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) (who : ι) :
    ∑ other ∈ Finset.univ.erase who, quittingTerminalSemanticDebt pair other ≤
      pair.1 who - reward (quittingSingletonTerminal who) who := by
  rw [fableFloorRepair_sum_debt_erase_eq]
  exact fableFloorRepair_minimum_payoff_margin reward pair hpair hminimum
    hpositive who

/-- A carrier point's tail debt sum off any coordinate is nonnegative. -/
theorem fableFloorRepair_carrier_debt_le_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) (who : ι) :
    quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.single_le_sum
    (fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player)
    (Finset.mem_univ who)

/-- **M1(b), (2.3).**  Punishment normality transfers along the minimum payoff
margin: at a positive global minimum, every player's punishment value is below
its own prescribed payoff. -/
theorem fableFloorRepair_minimum_punishmentFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) (who : ι) :
    quittingPunishmentValue reward who ≤ pair.1 who := by
  have hmargin := fableFloorRepair_minimum_payoff_margin reward pair hpair
    hminimum hpositive who
  have htail := fableFloorRepair_carrier_debt_le_debtSum reward hpair who
  linarith [hnormal who]

/-- **M1(c), (2.4).**  Two distinct positive debt coordinates make every tail
debt sum strictly positive.  Only carrier membership is used: minimality and
positivity of the total are not needed for this step. -/
theorem fableFloorRepair_twoDebtor_tail_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < quittingTerminalSemanticDebt pair first)
    (hsecond : 0 < quittingTerminalSemanticDebt pair second) (who : ι) :
    0 < quittingTerminalSemanticDebtSum pair -
      quittingTerminalSemanticDebt pair who := by
  have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  obtain ⟨other, hother, hpos⟩ :
      ∃ other, other ≠ who ∧ 0 < quittingTerminalSemanticDebt pair other := by
    by_cases hwho : who = first
    · exact ⟨second, by simpa [hwho] using (Ne.symm hne), hsecond⟩
    · exact ⟨first, fun hcontra => hwho hcontra.symm, hfirst⟩
  rw [← fableFloorRepair_sum_debt_erase_eq]
  refine lt_of_lt_of_le hpos ?_
  exact Finset.single_le_sum (fun player _ => hnonneg player)
    (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩)

/-- **M1(b), quantitative form.**  The carrier punishment floor holds with the
tail debt sum as an explicit margin. -/
theorem fableFloorRepair_minimum_punishmentFloor_margin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who) (who : ι) :
    quittingPunishmentValue reward who +
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) ≤ pair.1 who := by
  have hmargin := fableFloorRepair_minimum_payoff_margin reward pair hpair
    hminimum hpositive who
  linarith [hnormal who]

/-- **M1(c), floor form.**  With two distinct positive debt coordinates the
carrier punishment floor of every player is strict. -/
theorem fableFloorRepair_twoDebtor_strict_punishmentFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < quittingTerminalSemanticDebt pair first)
    (hsecond : 0 < quittingTerminalSemanticDebt pair second) (who : ι) :
    quittingPunishmentValue reward who < pair.1 who := by
  have hmargin := fableFloorRepair_minimum_punishmentFloor_margin reward pair
    hpair hminimum hpositive hnormal who
  have htail := fableFloorRepair_twoDebtor_tail_pos reward hpair hne hfirst
    hsecond who
  linarith

/-! ## The softened sequence -/

/-- The floor-repair softening applied along a sequence of actual profiles,
with an index-dependent target and softening weight. -/
def fableFloorRepairSoftenedSequence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (thetas : ℕ → ℝ)
    (hthetas0 : ∀ n, 0 ≤ thetas n) (hthetas1 : ∀ n, thetas n ≤ 1) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  fableFloorRepairSoftenedProfile reward (sigmas n) mover (targets n)
    (thetas n) (hthetas0 n) (hthetas1 n)

theorem fableFloorRepairSoftenedSequence_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (thetas : ℕ → ℝ)
    (hthetas0 : ∀ n, 0 ≤ thetas n) (hthetas1 : ∀ n, thetas n ≤ 1) (n : ℕ) :
    fableFloorRepairSoftenedSequence reward sigmas mover targets thetas
        hthetas0 hthetas1 n =
      fableFloorRepairSoftenedProfile reward (sigmas n) mover (targets n)
        (thetas n) (hthetas0 n) (hthetas1 n) := rfl

/-- A vanishing uniform control transfers convergence from a base sequence to
a perturbed one. -/
theorem fableFloorRepair_tendsto_of_abs_sub_le
    (perturbed base control : ℕ → ℝ) (limit : ℝ)
    (hbound : ∀ n, |perturbed n - base n| ≤ control n)
    (hcontrol : Tendsto control atTop (𝓝 0))
    (hbase : Tendsto base atTop (𝓝 limit)) :
    Tendsto perturbed atTop (𝓝 limit) := by
  have hdiff : Tendsto (fun n => perturbed n - base n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hcontrol
    rw [Real.norm_eq_abs]
    exact hbound n
  have hsum := hdiff.add hbase
  simpa using hsum

/-! ## M2a: the eventual mover gain floor -/

/-- **M2a, (3.3).**  If the mover's plans are asymptotically cap-optimal and
the mover carries the whole limiting debt, then its pure-time gain over its
own prescribed payoff is eventually at least half the total minimum debt. -/
theorem fableFloorRepair_eventually_mover_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hdebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) mover) atTop (𝓝 (pair.1 mover)))
    (hcap : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) mover) atTop
      (𝓝 (pair.2 mover)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n)) :
    ∀ᶠ n in atTop, quittingTerminalSemanticDebtSum pair / 2 ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n) -
        quittingTerminalPayoff reward (sigmas n) mover := by
  have hvalue : pair.2 mover - pair.1 mover - 0 =
      quittingTerminalSemanticDebtSum pair := by
    rw [← hdebt]
    unfold quittingTerminalSemanticDebt
    ring
  have hlimit : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        quittingTerminalPayoff reward (sigmas n) mover - epsilons n) atTop
      (𝓝 (quittingTerminalSemanticDebtSum pair)) := by
    have hraw := (hcap.sub hpayoff).sub hepsilons
    rwa [hvalue] at hraw
  have hhalf : quittingTerminalSemanticDebtSum pair / 2 <
      quittingTerminalSemanticDebtSum pair := by linarith
  filter_upwards [hlimit.eventually_const_lt hhalf] with n hn
  linarith [htargets n]

/-! ## M2b: the eventual nonmover floor margins -/

/-- **M2b, (3.2).**  A player whose limiting debt vanishes has a strict
limiting floor margin `D_*`, so its floor survives an arbitrary vanishing
`2 M θ` loss for all late indices.  No relation between `θ` and the softening
is used here: only `θ → 0`. -/
theorem fableFloorRepair_eventually_observer_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (thetas : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hdebt : quittingTerminalSemanticDebt pair observer = 0)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop
      (𝓝 (pair.1 observer)))
    (hthetas : Tendsto thetas atTop (𝓝 0)) :
    ∀ᶠ n in atTop, quittingPunishmentValue reward observer ≤
      quittingTerminalPayoff reward (sigmas n) observer -
        2 * quittingRewardBound reward * thetas n := by
  have hmargin := fableFloorRepair_minimum_punishmentFloor_margin reward pair
    hpair hminimum hpositive hnormal observer
  rw [hdebt] at hmargin
  have hstrict : quittingPunishmentValue reward observer < pair.1 observer := by
    linarith
  have hlimit : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer -
        2 * quittingRewardBound reward * thetas n) atTop
      (𝓝 (pair.1 observer)) := by
    have hraw := hpayoff.sub
      (hthetas.const_mul (2 * quittingRewardBound reward))
    simpa using hraw
  filter_upwards [hlimit.eventually_const_lt hstrict] with n hn
  exact hn.le

/-! ## M2c: the eventual all-player floor at the softened profiles -/

/-- **M2c, (3.5)--(3.6).**  With the mover repair inequality supplied as a
hypothesis, the softened profiles eventually meet every player's punishment
floor.  The mover's floor is met by the exact affine gain of `K6`; every other
player's by the strict limiting margin against the uniform `2 M θ` loss. -/
theorem fableFloorRepair_eventually_punishmentFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (thetas : ℕ → ℝ)
    (hthetas0 : ∀ n, 0 ≤ thetas n) (hthetas1 : ∀ n, thetas n ≤ 1)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hdebt : ∀ observer, observer ≠ mover →
      quittingTerminalSemanticDebt pair observer = 0)
    (hpayoff : ∀ observer, Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop
      (𝓝 (pair.1 observer)))
    (hthetas : Tendsto thetas atTop (𝓝 0))
    (hrepair : ∀ᶠ n in atTop,
      quittingPunishmentValue reward mover -
          quittingTerminalPayoff reward (sigmas n) mover ≤
        thetas n *
          (quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n) -
            quittingTerminalPayoff reward (sigmas n) mover)) :
    ∀ᶠ n in atTop, ∀ observer,
      quittingPunishmentValue reward observer ≤
        quittingTerminalPayoff reward
          (fableFloorRepairSoftenedSequence reward sigmas mover targets thetas
            hthetas0 hthetas1 n) observer := by
  have hothers : ∀ᶠ n in atTop, ∀ observer, observer ≠ mover →
      quittingPunishmentValue reward observer ≤
        quittingTerminalPayoff reward (sigmas n) observer -
          2 * quittingRewardBound reward * thetas n := by
    refine Filter.eventually_all.mpr fun observer => ?_
    by_cases hobserver : observer = mover
    · exact Filter.Eventually.of_forall fun n hcontra => absurd hobserver hcontra
    · filter_upwards [fableFloorRepair_eventually_observer_floor reward sigmas
        observer thetas pair hpair hminimum hpositive hnormal
        (hdebt observer hobserver) (hpayoff observer) hthetas] with n hn
      exact fun _ => hn
  filter_upwards [hrepair, hothers] with n hn hnothers
  exact fableFloorRepair_punishmentFloor reward (sigmas n) mover (targets n)
    (thetas n) (hthetas0 n) (hthetas1 n) (quittingPunishmentValue reward)
    (by linarith) hnothers

/-! ## The note's weights `θ_n = 2 f_n / a_n`, clamped to `[0, 1]` -/

/-- The mover's floor deficit `f_n = (Pun_p - U^n_p)_+`. -/
def fableFloorRepairDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (n : ℕ) : ℝ :=
  max 0 (quittingPunishmentValue reward mover -
    quittingTerminalPayoff reward (sigmas n) mover)

/-- The mover's pure-time gain `a_n = V^n_p(q_n^+) - U^n_p`. -/
def fableFloorRepairGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (n : ℕ) : ℝ :=
  quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n) -
    quittingTerminalPayoff reward (sigmas n) mover

/-- **(3.4), clamped.**  The note's softening weight `θ_n = 2 f_n / a_n`, cut
down to `[0, 1]` so that it is a legal mixing weight at every index.  The
clamp is inactive for all late `n`. -/
def fableFloorRepairWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (n : ℕ) : ℝ :=
  max 0 (min 1 (2 * fableFloorRepairDeficit reward sigmas mover n /
    fableFloorRepairGain reward sigmas mover targets n))

theorem fableFloorRepairDeficit_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (n : ℕ) :
    0 ≤ fableFloorRepairDeficit reward sigmas mover n :=
  le_max_left _ _

theorem fableFloorRepairDeficit_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (n : ℕ) :
    quittingPunishmentValue reward mover -
        quittingTerminalPayoff reward (sigmas n) mover ≤
      fableFloorRepairDeficit reward sigmas mover n :=
  le_max_right _ _

theorem fableFloorRepairWeight_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (n : ℕ) :
    0 ≤ fableFloorRepairWeight reward sigmas mover targets n :=
  le_max_left _ _

theorem fableFloorRepairWeight_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (n : ℕ) :
    fableFloorRepairWeight reward sigmas mover targets n ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

/-- **M2a, gain form.**  The eventual mover gain floor `a_n ≥ D_* / 2`. -/
theorem fableFloorRepair_eventually_gain_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hdebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) mover) atTop (𝓝 (pair.1 mover)))
    (hcap : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) mover) atTop
      (𝓝 (pair.2 mover)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n)) :
    ∀ᶠ n in atTop, quittingTerminalSemanticDebtSum pair / 2 ≤
      fableFloorRepairGain reward sigmas mover targets n :=
  fableFloorRepair_eventually_mover_gain reward sigmas mover targets epsilons
    pair hdebt hpositive hpayoff hcap hepsilons htargets

/-- The mover's floor deficit vanishes: the carrier floor `Pun_p ≤ U_p` makes
the limit of `(Pun_p - U^n_p)_+` zero. -/
theorem fableFloorRepairDeficit_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (pair : QuittingTerminalSemanticPair ι)
    (hfloor : quittingPunishmentValue reward mover ≤ pair.1 mover)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) mover) atTop
      (𝓝 (pair.1 mover))) :
    Tendsto (fableFloorRepairDeficit reward sigmas mover) atTop (𝓝 0) := by
  unfold fableFloorRepairDeficit
  have hraw : Tendsto (fun n => max 0 (quittingPunishmentValue reward mover -
      quittingTerminalPayoff reward (sigmas n) mover)) atTop
      (𝓝 (max 0 (quittingPunishmentValue reward mover - pair.1 mover))) :=
    tendsto_const_nhds.max (tendsto_const_nhds.sub hpayoff)
  rwa [max_eq_left (show quittingPunishmentValue reward mover - pair.1 mover ≤ 0
    by linarith)] at hraw

/-- The clamped note weights vanish.  Eventually `a_n ≥ D_* / 2 > 0`, so the
weight is squeezed between `0` and `4 f_n / D_*`. -/
theorem fableFloorRepairWeight_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hdebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) mover) atTop (𝓝 (pair.1 mover)))
    (hcap : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) mover) atTop
      (𝓝 (pair.2 mover)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n)) :
    Tendsto (fableFloorRepairWeight reward sigmas mover targets) atTop (𝓝 0) := by
  have hfloor := fableFloorRepair_minimum_punishmentFloor reward pair hpair
    hminimum hpositive hnormal mover
  have hdeficit := fableFloorRepairDeficit_tendsto_zero reward sigmas mover pair
    hfloor hpayoff
  have hgain := fableFloorRepair_eventually_gain_ge reward sigmas mover targets
    epsilons pair hdebt hpositive hpayoff hcap hepsilons htargets
  refine squeeze_zero'
    (g := fun n => 4 * fableFloorRepairDeficit reward sigmas mover n /
      quittingTerminalSemanticDebtSum pair)
    (Filter.Eventually.of_forall
      (fableFloorRepairWeight_nonneg reward sigmas mover targets)) ?_ ?_
  · filter_upwards [hgain] with n hn
    have hgpos : 0 < fableFloorRepairGain reward sigmas mover targets n := by
      linarith
    have hdnonneg := fableFloorRepairDeficit_nonneg reward sigmas mover n
    have hratio0 : 0 ≤ 2 * fableFloorRepairDeficit reward sigmas mover n /
        fableFloorRepairGain reward sigmas mover targets n :=
      div_nonneg (by linarith) hgpos.le
    calc fableFloorRepairWeight reward sigmas mover targets n
        ≤ 2 * fableFloorRepairDeficit reward sigmas mover n /
            fableFloorRepairGain reward sigmas mover targets n := by
          unfold fableFloorRepairWeight
          exact max_le hratio0 (min_le_right _ _)
      _ ≤ 4 * fableFloorRepairDeficit reward sigmas mover n /
            quittingTerminalSemanticDebtSum pair := by
          rw [div_le_div_iff₀ hgpos hpositive]
          nlinarith
  · have hraw := (hdeficit.const_mul (4 : ℝ)).div_const
      (quittingTerminalSemanticDebtSum pair)
    simpa using hraw

/-- **(3.4), repair inequality.**  For all late `n` the clamp is inactive and
the weight is exactly `2 f_n / a_n`, so the softened mover payoff clears its
punishment floor. -/
theorem fableFloorRepair_eventually_weight_repair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hdebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) mover) atTop (𝓝 (pair.1 mover)))
    (hcap : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) mover) atTop
      (𝓝 (pair.2 mover)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n)) :
    ∀ᶠ n in atTop,
      quittingPunishmentValue reward mover -
          quittingTerminalPayoff reward (sigmas n) mover ≤
        fableFloorRepairWeight reward sigmas mover targets n *
          (quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n) -
            quittingTerminalPayoff reward (sigmas n) mover) := by
  have hfloor := fableFloorRepair_minimum_punishmentFloor reward pair hpair
    hminimum hpositive hnormal mover
  have hdeficit := fableFloorRepairDeficit_tendsto_zero reward sigmas mover pair
    hfloor hpayoff
  have hgain := fableFloorRepair_eventually_gain_ge reward sigmas mover targets
    epsilons pair hdebt hpositive hpayoff hcap hepsilons htargets
  have hsmall : ∀ᶠ n in atTop, fableFloorRepairDeficit reward sigmas mover n <
      quittingTerminalSemanticDebtSum pair / 4 :=
    hdeficit.eventually_lt_const (by linarith)
  filter_upwards [hgain, hsmall] with n hgn hdn
  have hgpos : 0 < fableFloorRepairGain reward sigmas mover targets n := by
    linarith
  have hdnonneg := fableFloorRepairDeficit_nonneg reward sigmas mover n
  have hratio : 2 * fableFloorRepairDeficit reward sigmas mover n /
      fableFloorRepairGain reward sigmas mover targets n ≤ 1 := by
    rw [div_le_one hgpos]
    linarith
  have hratio0 : 0 ≤ 2 * fableFloorRepairDeficit reward sigmas mover n /
      fableFloorRepairGain reward sigmas mover targets n :=
    div_nonneg (by linarith) hgpos.le
  have hweight : fableFloorRepairWeight reward sigmas mover targets n =
      2 * fableFloorRepairDeficit reward sigmas mover n /
        fableFloorRepairGain reward sigmas mover targets n := by
    unfold fableFloorRepairWeight
    rw [min_eq_right hratio, max_eq_right hratio0]
  have hgainEq :
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n) -
          quittingTerminalPayoff reward (sigmas n) mover =
        fableFloorRepairGain reward sigmas mover targets n := rfl
  rw [hweight, hgainEq, div_mul_cancel₀ _ hgpos.ne']
  linarith [fableFloorRepairDeficit_le reward sigmas mover n]

/-! ## Retention of the incoming semantic packet along the sequence -/

/-- **(3.7)--(3.8), payoff form.**  Every observer's prescribed payoff at the
softened profiles keeps the limit of the source payoffs, because `K3` controls
the shift by `2 M θ_n`. -/
theorem fableFloorRepair_softenedSequence_tendsto_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (thetas : ℕ → ℝ)
    (hthetas0 : ∀ n, 0 ≤ thetas n) (hthetas1 : ∀ n, thetas n ≤ 1)
    (observer : ι) (limit : ℝ)
    (hthetas : Tendsto thetas atTop (𝓝 0))
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop (𝓝 limit)) :
    Tendsto (fun n => quittingTerminalPayoff reward
      (fableFloorRepairSoftenedSequence reward sigmas mover targets thetas
        hthetas0 hthetas1 n) observer) atTop (𝓝 limit) := by
  refine fableFloorRepair_tendsto_of_abs_sub_le _ _
    (fun n => 2 * quittingRewardBound reward * thetas n) limit (fun n => ?_) ?_
    hpayoff
  · exact fableFloorRepair_abs_payoff_sub_le reward (sigmas n) mover observer
      (targets n) (thetas n) (hthetas0 n) (hthetas1 n)
  · simpa using hthetas.const_mul (2 * quittingRewardBound reward)

/-- **(3.8)--(3.9).**  Every observer's cap at the softened profiles keeps the
limit of the source caps: the mover's cap is frozen exactly by `K2`, and every
nonmover's cap moves by at most `2 M θ_n` by `K3`. -/
theorem fableFloorRepair_softenedSequence_tendsto_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (thetas : ℕ → ℝ)
    (hthetas0 : ∀ n, 0 ≤ thetas n) (hthetas1 : ∀ n, thetas n ≤ 1)
    (observer : ι) (limit : ℝ)
    (hthetas : Tendsto thetas atTop (𝓝 0))
    (hcap : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) observer) atTop
      (𝓝 limit)) :
    Tendsto (fun n => quittingContinuationBestResponseValue reward
      (fableFloorRepairSoftenedSequence reward sigmas mover targets thetas
        hthetas0 hthetas1 n) observer) atTop (𝓝 limit) := by
  by_cases hobserver : observer = mover
  · have hfrozen : ∀ n, quittingContinuationBestResponseValue reward
        (fableFloorRepairSoftenedSequence reward sigmas mover targets thetas
          hthetas0 hthetas1 n) observer =
        quittingContinuationBestResponseValue reward (sigmas n) observer := by
      intro n
      rw [hobserver, fableFloorRepairSoftenedSequence_apply]
      exact fableFloorRepair_mover_cap_eq reward (sigmas n) mover (targets n)
        (thetas n) (hthetas0 n) (hthetas1 n)
    simp only [hfrozen]
    exact hcap
  · refine fableFloorRepair_tendsto_of_abs_sub_le _ _
      (fun n => 2 * quittingRewardBound reward * thetas n) limit (fun n => ?_) ?_
      hcap
    · exact fableFloorRepair_abs_cap_sub_le reward (sigmas n) mover observer
        (targets n) (thetas n) (hthetas0 n) (hthetas1 n) hobserver
    · simpa using hthetas.const_mul (2 * quittingRewardBound reward)

/-- **(3.10).**  The retained paid pure-time pair of `K5`, with the eventual
gain floor `D_* / 2` of `M2a` substituted for the mover's pure-time gain. -/
theorem fableFloorRepair_eventually_retained_paidPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ) (thetas : ℕ → ℝ)
    (hthetas0 : ∀ n, 0 ≤ thetas n) (hthetas1 : ∀ n, thetas n ≤ 1)
    (pair : QuittingTerminalSemanticPair ι)
    (hdebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hpayoff : Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) mover) atTop (𝓝 (pair.1 mover)))
    (hcap : Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) mover) atTop
      (𝓝 (pair.2 mover)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n)) :
    ∀ᶠ n in atTop,
      ∃ source ∈ (quittingBehaviorStoppingLaw reward (sigmas n mover)).support,
        quittingPureTimeDeviationPayoff reward (sigmas n) mover source ≤
            quittingTerminalPayoff reward (sigmas n) mover ∧
          quittingTerminalSemanticDebtSum pair / 2 ≤
            quittingPureTimeDeviationPayoff reward
                (fableFloorRepairSoftenedSequence reward sigmas mover targets
                  thetas hthetas0 hthetas1 n) mover (targets n) -
              quittingPureTimeDeviationPayoff reward
                (fableFloorRepairSoftenedSequence reward sigmas mover targets
                  thetas hthetas0 hthetas1 n) mover source := by
  filter_upwards [fableFloorRepair_eventually_mover_gain reward sigmas mover
    targets epsilons pair hdebt hpositive hpayoff hcap hepsilons htargets]
    with n hn
  obtain ⟨source, hsource, hle, hspread⟩ :=
    fableFloorRepair_exists_retained_paidPair reward (sigmas n) mover
      (targets n) (thetas n) (hthetas0 n) (hthetas1 n)
  refine ⟨source, hsource, hle, ?_⟩
  rw [fableFloorRepairSoftenedSequence_apply]
  linarith

/-! ## M2d: the packaged sequence-level entrance -/

/-- The floor-repair entrance profiles: the softened sequence carried by the
note's own clamped weights `θ_n = 2 f_n / a_n`. -/
def fableFloorRepairEntranceProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  fableFloorRepairSoftenedSequence reward sigmas mover targets
    (fableFloorRepairWeight reward sigmas mover targets)
    (fableFloorRepairWeight_nonneg reward sigmas mover targets)
    (fableFloorRepairWeight_le_one reward sigmas mover targets) n

/-- **M2d, the unique-debtor entrance.**  Let actual profiles have
coordinatewise semantic convergence to a positive global minimum `pair` whose
debt is carried by `mover` alone, let the hard residual be punishment normal,
and let the mover's plans be asymptotically cap-optimal with vanishing error.
Then the entrance profiles, softened by the note's own vanishing weights,

* eventually meet every player's punishment floor;
* eventually retain a paid pure-time pair of the mover with gap at least
  `D_* / 2`, whose source witness sits in the support of the mover's original
  stopping law;
* retain the mover's approximate cap optimality at every index; and
* still converge coordinatewise, in prescribed payoff and in cap, to the same
  incoming minimum `pair`.

No profile sequence is constructed here, and no exact-port consumer is
invoked: this is the entrance data, not its consumption. -/
theorem fableFloorRepair_entrance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hmoverDebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hotherDebt : ∀ observer, observer ≠ mover →
      quittingTerminalSemanticDebt pair observer = 0)
    (hpayoff : ∀ observer, Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop
      (𝓝 (pair.1 observer)))
    (hcap : ∀ observer, Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) observer) atTop
      (𝓝 (pair.2 observer)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n)) :
    Tendsto (fableFloorRepairWeight reward sigmas mover targets) atTop (𝓝 0) ∧
      (∀ observer, Tendsto (fun n => quittingTerminalPayoff reward
        (fableFloorRepairEntranceProfile reward sigmas mover targets n) observer)
        atTop (𝓝 (pair.1 observer))) ∧
      (∀ observer, Tendsto (fun n =>
        quittingContinuationBestResponseValue reward
          (fableFloorRepairEntranceProfile reward sigmas mover targets n)
          observer) atTop (𝓝 (pair.2 observer))) ∧
      (∀ n, quittingContinuationBestResponseValue reward
            (fableFloorRepairEntranceProfile reward sigmas mover targets n)
            mover - epsilons n ≤
          quittingPureTimeDeviationPayoff reward
            (fableFloorRepairEntranceProfile reward sigmas mover targets n)
            mover (targets n)) ∧
      (∀ᶠ n in atTop, (∀ observer,
          quittingPunishmentValue reward observer ≤ quittingTerminalPayoff reward
            (fableFloorRepairEntranceProfile reward sigmas mover targets n)
            observer) ∧
        ∃ source ∈ (quittingBehaviorStoppingLaw reward (sigmas n mover)).support,
          quittingPureTimeDeviationPayoff reward (sigmas n) mover source ≤
              quittingTerminalPayoff reward (sigmas n) mover ∧
            quittingTerminalSemanticDebtSum pair / 2 ≤
              quittingPureTimeDeviationPayoff reward
                  (fableFloorRepairEntranceProfile reward sigmas mover targets n)
                  mover (targets n) -
                quittingPureTimeDeviationPayoff reward
                  (fableFloorRepairEntranceProfile reward sigmas mover targets n)
                  mover source) := by
  have hweightTendsto := fableFloorRepairWeight_tendsto_zero reward sigmas mover
    targets epsilons pair hpair hminimum hpositive hnormal hmoverDebt
    (hpayoff mover) (hcap mover) hepsilons htargets
  refine ⟨hweightTendsto, fun observer => ?_, fun observer => ?_, fun n => ?_, ?_⟩
  · exact fableFloorRepair_softenedSequence_tendsto_payoff reward sigmas mover
      targets _ _ _ observer _ hweightTendsto (hpayoff observer)
  · exact fableFloorRepair_softenedSequence_tendsto_cap reward sigmas mover
      targets _ _ _ observer _ hweightTendsto (hcap observer)
  · exact fableFloorRepair_retained_cap_optimality reward (sigmas n) mover
      (targets n) _ _ _ (epsilons n) (htargets n)
  · have hfloors := fableFloorRepair_eventually_punishmentFloor reward sigmas
      mover targets (fableFloorRepairWeight reward sigmas mover targets)
      (fableFloorRepairWeight_nonneg reward sigmas mover targets)
      (fableFloorRepairWeight_le_one reward sigmas mover targets) pair hpair
      hminimum hpositive hnormal hotherDebt hpayoff hweightTendsto
      (fableFloorRepair_eventually_weight_repair reward sigmas mover targets
        epsilons pair hpair hminimum hpositive hnormal hmoverDebt
        (hpayoff mover) (hcap mover) hepsilons htargets)
    have hpaid := fableFloorRepair_eventually_retained_paidPair reward sigmas
      mover targets epsilons (fableFloorRepairWeight reward sigmas mover targets)
      (fableFloorRepairWeight_nonneg reward sigmas mover targets)
      (fableFloorRepairWeight_le_one reward sigmas mover targets) pair hmoverDebt
      hpositive (hpayoff mover) (hcap mover) hepsilons htargets
    filter_upwards [hfloors, hpaid] with n hn hpaidn
    exact ⟨hn, hpaidn⟩

end GameTheory
