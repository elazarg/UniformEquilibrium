import UniformEquilibrium.Quitting.Cycles.ApproximateCyclicCensor
import UniformEquilibrium.Quitting.Cycles.CyclicFiniteMenu
import UniformEquilibrium.Quitting.Root.TruncatedStoppingLaw
import UniformEquilibrium.Quitting.Stationary.Root
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineSignedHorizonError

/-! # Sharp finite censoring of actual stationary terminal approximate Nash

A period-one specialization of the canonical periodic censor estimates retains
the same root and its exact independent date-or-Never laws. The regret bound
uses deleted-opponent survival, not a sum of individual stopping-law tails.
No unilateral cap is supplied: it is derived from actual terminal approximate Nash.
The zero-error interfaces are projections of the same construction.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The same stationary root for exactly the first `deadline` dates, then Continue. -/
def quittingStationaryFiniteCensorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicFiniteProfile reward (fun _ : Fin 1 => root) 0 deadline

/-- The maximum deleted-opponent survival, with zero inserted for an empty player type. -/
def quittingStationaryDeletedSurvivalMax (root : ι → PMF Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun player : Option ι =>
      player.elim 0 (quittingStationaryFixedOpponentsContinueMass root))

theorem quittingStationaryDeletedSurvivalMax_nonneg (root : ι → PMF Bool) :
    0 ≤ quittingStationaryDeletedSurvivalMax root := by
  unfold quittingStationaryDeletedSurvivalMax
  exact Finset.le_sup'
    (fun player : Option ι =>
      player.elim (0 : ℝ) (quittingStationaryFixedOpponentsContinueMass root))
    (Finset.mem_univ (none : Option ι))

theorem quittingStationaryFixedOpponentsContinueMass_le_max
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass root who ≤
      quittingStationaryDeletedSurvivalMax root := by
  unfold quittingStationaryDeletedSurvivalMax
  exact Finset.le_sup'
    (fun player : Option ι =>
      player.elim (0 : ℝ) (quittingStationaryFixedOpponentsContinueMass root))
    (Finset.mem_univ (some who))

theorem quittingStationaryDeletedSurvivalMax_lt_one
    (root : ι → PMF Bool)
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryDeletedSurvivalMax root < 1 := by
  unfold quittingStationaryDeletedSurvivalMax
  apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
  intro player _
  cases player with
  | none => norm_num
  | some who => exact hcontracts who

omit [DecidableEq ι] in
private theorem periodOne_profile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingCyclicBehaviorProfile reward (fun _ : Fin 1 => root) 0 =
      quittingStationaryProfile reward root := rfl

omit [DecidableEq ι] in
private theorem periodOne_value
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingCyclicTerminalValue reward (fun _ : Fin 1 => root) 0 =
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) := rfl

omit [DecidableEq ι] in
/-- Exact prescribed payoff of the literal stationary censor, including signed rewards. -/
theorem quittingTerminalPayoff_stationaryFiniteCensorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (who : ι) :
    quittingTerminalPayoff reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who =
      (1 - quittingStationaryContinueMass root ^ deadline) *
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who := by
  simpa only [Nat.mul_one, Fin.prod_univ_one, periodOne_value,
    quittingStationaryFiniteCensorProfile] using
    quittingTerminalPayoff_cyclicFiniteProfile_mul_card reward
      (fun _ : Fin 1 => root) 0 deadline who

/-- The full behavioral cap adds censor cost to the actual source terminal Nash error. -/
theorem quittingContinuationBestResponseValue_stationaryFiniteCensorProfile_le_of_approximateNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (who : ι) {M error : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
      (quittingStationaryProfile reward root)) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who + error +
        2 * M * quittingStationaryFixedOpponentsContinueMass root who ^ deadline := by
  have hcap : quittingContinuationBestResponseValue reward
      (quittingStationaryProfile reward root) who ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who + error := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, (quittingStationaryProfile reward root) who, rfl⟩
    · rintro value ⟨deviation, rfl⟩
      exact hnash who deviation
  have h := quittingContinuationBestResponseValue_cyclicFiniteProfile_le_of_full_cap
    reward (fun _ : Fin 1 => root) 0 deadline who (error := error) hreward
      (by simpa only [periodOne_profile, periodOne_value] using hcap)
  simpa only [Nat.mul_one, Fin.prod_univ_one, periodOne_value,
    quittingStationaryFiniteCensorProfile] using h

/-- The full behavioral cap censor cost, derived from actual stationary terminal Nash. -/
theorem quittingContinuationBestResponseValue_stationaryFiniteCensorProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root)) :
    quittingContinuationBestResponseValue reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who ≤
      quittingTerminalPayoff reward (quittingStationaryProfile reward root) who +
        2 * M * quittingStationaryFixedOpponentsContinueMass root who ^ deadline := by
  simpa only [add_zero] using
    quittingContinuationBestResponseValue_stationaryFiniteCensorProfile_le_of_approximateNash
      reward root deadline who (error := 0) hreward hnash

omit [DecidableEq ι] in
/-- Joint survival gives the prescribed terminal delivery error. -/
theorem abs_quittingTerminalPayoff_stationaryFiniteCensorProfile_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (quittingStationaryFiniteCensorProfile reward root deadline) who -
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
      M * quittingStationaryContinueMass root ^ deadline := by
  simpa only [Nat.mul_one, Fin.prod_univ_one, periodOne_value,
    quittingStationaryFiniteCensorProfile] using
    abs_quittingTerminalPayoff_cyclicFiniteProfile_sub_le reward
      (fun _ : Fin 1 => root) 0 deadline who hreward

/-- Censoring adds `3M` times deleted-opponent survival to the initial Nash error. -/
theorem quittingTerminalDeviationDebt_stationaryFiniteCensorProfile_le_of_approximateNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (who : ι) {M error : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
      (quittingStationaryProfile reward root)) :
    quittingTerminalDeviationDebt reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who ≤
      error + 3 * M * quittingStationaryFixedOpponentsContinueMass root who ^ deadline := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hcap :=
    quittingContinuationBestResponseValue_stationaryFiniteCensorProfile_le_of_approximateNash
      reward root deadline who hreward hnash
  have hdelivery := neg_le_of_abs_le
    (abs_quittingTerminalPayoff_stationaryFiniteCensorProfile_sub_le
      reward root deadline who hreward)
  have hpower := pow_le_pow_left₀ (quittingStationaryContinueMass_nonneg root)
    (quittingStationaryContinueMass_le_fixedOpponentsContinueMass root who) deadline
  have hscaled := mul_le_mul_of_nonneg_left hpower hM
  unfold quittingTerminalDeviationDebt
  linarith

/-- The sharp playerwise bound is `3M` times DELETED-opponent survival to the cut. -/
theorem quittingTerminalDeviationDebt_stationaryFiniteCensorProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root)) :
    quittingTerminalDeviationDebt reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who ≤
      3 * M * quittingStationaryFixedOpponentsContinueMass root who ^ deadline := by
  simpa only [zero_add] using
    quittingTerminalDeviationDebt_stationaryFiniteCensorProfile_le_of_approximateNash
      reward root deadline who (error := 0) hreward hnash

omit [DecidableEq ι] in
/-- This censor independently sends precisely the later private stopping dates to Never. -/
theorem quittingBehaviorStoppingLaw_stationaryFiniteCensor_eq_censor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (hdeadline : 0 < deadline) (who : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingStationaryFiniteCensorProfile reward root deadline who) =
      censorLateFiniteStoppingLaw
        (quittingBehaviorStoppingLaw reward (quittingStationaryProfile reward root who))
        (deadline - 1) := by
  unfold quittingStationaryFiniteCensorProfile
  rw [quittingCyclicFiniteProfile_eq_truncatedRootProfile]
  exact quittingBehaviorStoppingLaw_truncatedRoots_eq_censor reward _ _ hdeadline who

omit [DecidableEq ι] in
/-- Every retained finite atom has the literal geometric mass of the same root. -/
theorem quittingBehaviorStoppingLaw_stationaryFiniteCensor_some_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline time : ℕ) (htime : time < deadline) (who : ι) :
    (quittingBehaviorStoppingLaw reward
        (quittingStationaryFiniteCensorProfile reward root deadline who)
        (some time)).toReal =
      (root who true).toReal * (root who false).toReal ^ time := by
  unfold quittingStationaryFiniteCensorProfile
  rw [quittingCyclicFiniteProfile_eq_truncatedRootProfile,
    quittingBehaviorStoppingLaw_truncatedRoots_some_eq_of_lt reward _ _ _ htime]
  rw [quittingBehaviorStoppingLaw_some_toReal,
    quittingHazardStopMass_eq_survival_mul_stop, quittingHazardSurvival_eq_prod]
  simp only [quittingBehaviorLiveHazard, quittingRootSequenceProfile,
    quittingCyclicRootSequence, Finset.prod_const, Finset.card_range]
  ring

omit [DecidableEq ι] in
/-- The Never mass is own survival through all retained dates. -/
theorem quittingBehaviorStoppingLaw_stationaryFiniteCensor_none_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (hdeadline : 0 < deadline) (who : ι) :
    (quittingBehaviorStoppingLaw reward
        (quittingStationaryFiniteCensorProfile reward root deadline who) none).toReal =
      (root who false).toReal ^ deadline := by
  unfold quittingStationaryFiniteCensorProfile
  rw [quittingCyclicFiniteProfile_eq_truncatedRootProfile,
    quittingBehaviorStoppingLaw_truncatedRoots_none_toReal reward _ _ hdeadline]
  simp only [quittingCyclicRootSequence, Finset.prod_const, Finset.card_range]

/-- One actual independent finite family retains the exact censored laws and full
semantic pair. The initial terminal Nash error is retained in the terminal and signed
horizon regret bounds. Delivery is to this source root's actual payoff, not a target
shared with independently selected roots at other accuracies. -/
theorem exists_stationaryFiniteCensorTimingProfile_of_approximateNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (hdeadline : 0 < deadline) {M error : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
      (quittingStationaryProfile reward root))
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryDeletedSurvivalMax root < 1 ∧
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw
          (quittingBehaviorStoppingLaw reward (quittingStationaryProfile reward root who))
          (deadline - 1)) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalSemanticPair reward
          (quittingStationaryFiniteCensorProfile reward root deadline) ∧
      (∀ who time, time < deadline →
        ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF (some time)).toReal =
          (root who true).toReal * (root who false).toReal ^ time) ∧
      (∀ who, (mixed who none).toReal = (root who false).toReal ^ deadline) ∧
      (∀ who, quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
        (1 - quittingStationaryContinueMass root ^ deadline) *
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (error + 3 * M * quittingStationaryDeletedSurvivalMax root ^ deadline)
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
      (∀ who, |quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
          M * quittingStationaryDeletedSurvivalMax root ^ deadline) ∧
      ∀ horizon, 0 < horizon →
        (quittingGame reward).IsεHorizonNash none horizon
          (error + 3 * M * quittingStationaryDeletedSurvivalMax root ^ deadline +
            2 * M * (deadline + 1) / horizon)
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
            M * quittingStationaryDeletedSurvivalMax root ^ deadline +
              M * (deadline + 1) / horizon := by
  obtain ⟨mixed, hlaws, hpair, _⟩ :=
    exists_finiteDeadlineTimingProfile_cyclicFinite_exact reward
      (fun _ : Fin 1 => root) 0 deadline
  change quittingTerminalSemanticPair reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
    quittingTerminalSemanticPair reward
      (quittingStationaryFiniteCensorProfile reward root deadline) at hpair
  have hpay (who : ι) : quittingTerminalPayoff reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
      quittingTerminalPayoff reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who :=
    congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.1 who) hpair
  have hcap (who : ι) : quittingContinuationBestResponseValue reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
      quittingContinuationBestResponseValue reward
        (quittingStationaryFiniteCensorProfile reward root deadline) who :=
    congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.2 who) hpair
  change ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
    quittingBehaviorStoppingLaw reward
      (quittingStationaryFiniteCensorProfile reward root deadline who) at hlaws
  have hdelivery (who : ι) :
      |quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
      M * quittingStationaryDeletedSurvivalMax root ^ deadline := by
    rw [hpay who]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
    have hpower := pow_le_pow_left₀ (quittingStationaryContinueMass_nonneg root)
      ((quittingStationaryContinueMass_le_fixedOpponentsContinueMass root who).trans
        (quittingStationaryFixedOpponentsContinueMass_le_max root who)) deadline
    exact (abs_quittingTerminalPayoff_stationaryFiniteCensorProfile_sub_le
      reward root deadline who hreward).trans (mul_le_mul_of_nonneg_left hpower hM)
  have hterminal : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (error + 3 * M * quittingStationaryDeletedSurvivalMax root ^ deadline)
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
    intro who deviation
    have hdebt := quittingTerminalDeviationDebt_stationaryFiniteCensorProfile_le_of_approximateNash
      reward root deadline who hreward hnash
    have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
    have hpower := pow_le_pow_left₀
      (quittingStationaryFixedOpponentsContinueMass_nonneg root who)
      (quittingStationaryFixedOpponentsContinueMass_le_max root who) deadline
    have hscaled := mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 3 * M)
    have hdeviation := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation
    unfold quittingTerminalDeviationDebt at hdebt
    rw [hcap who] at hdeviation
    rw [hpay who]
    linarith
  refine ⟨quittingStationaryDeletedSurvivalMax_lt_one root hcontracts,
    mixed, ?_, hpair, ?_, ?_, ?_, hterminal, hdelivery, ?_⟩
  · intro who
    rw [hlaws who]
    exact quittingBehaviorStoppingLaw_stationaryFiniteCensor_eq_censor
      reward root deadline hdeadline who
  · intro who time htime
    rw [hlaws who]
    exact quittingBehaviorStoppingLaw_stationaryFiniteCensor_some_toReal
      reward root deadline time htime who
  · intro who
    rw [← quittingFiniteDeadlineTimingLaw_none, hlaws who]
    exact quittingBehaviorStoppingLaw_stationaryFiniteCensor_none_toReal
      reward root deadline hdeadline who
  · intro who
    exact (hpay who).trans
      (quittingTerminalPayoff_stationaryFiniteCensorProfile reward root deadline who)
  · intro horizon hhorizon
    refine ⟨isHorizonNash_finiteDeadline_of_terminalNash_add_one_signed
      reward deadline horizon mixed hterminal hreward hhorizon, ?_⟩
    intro who
    have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
    have hboundary :=
      abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
        reward deadline horizon mixed who (fun terminal => hreward terminal who) hhorizon
    have hboundary' : M * deadline / horizon ≤ M * (deadline + 1) / horizon := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by norm_num : (deadline : ℝ) ≤ deadline + 1) hM
    calc
      _ ≤ |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
          quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who| +
        |quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| :=
        abs_sub_le _ _ _
      _ ≤ M * deadline / horizon +
          M * quittingStationaryDeletedSurvivalMax root ^ deadline :=
        add_le_add hboundary (hdelivery who)
      _ ≤ _ := by linarith

/-- One actual independent finite family retains the exact censored laws and full
semantic pair. The same family has sharp terminal bounds and the printed signed
horizon bounds against every behavioral deviation, including Never. -/
theorem exists_stationaryFiniteCensorTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (deadline : ℕ) (hdeadline : 0 < deadline) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root))
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryDeletedSurvivalMax root < 1 ∧
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        censorLateFiniteStoppingLaw
          (quittingBehaviorStoppingLaw reward (quittingStationaryProfile reward root who))
          (deadline - 1)) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalSemanticPair reward
          (quittingStationaryFiniteCensorProfile reward root deadline) ∧
      (∀ who time, time < deadline →
        ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF (some time)).toReal =
          (root who true).toReal * (root who false).toReal ^ time) ∧
      (∀ who, (mixed who none).toReal = (root who false).toReal ^ deadline) ∧
      (∀ who, quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
        (1 - quittingStationaryContinueMass root ^ deadline) *
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
        (3 * M * quittingStationaryDeletedSurvivalMax root ^ deadline)
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
      (∀ who, |quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
        quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
          M * quittingStationaryDeletedSurvivalMax root ^ deadline) ∧
      ∀ horizon, 0 < horizon →
        (quittingGame reward).IsεHorizonNash none horizon
          (3 * M * quittingStationaryDeletedSurvivalMax root ^ deadline +
            2 * M * (deadline + 1) / horizon)
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
          quittingTerminalPayoff reward (quittingStationaryProfile reward root) who| ≤
            M * quittingStationaryDeletedSurvivalMax root ^ deadline +
              M * (deadline + 1) / horizon := by
  simpa only [zero_add] using
    exists_stationaryFiniteCensorTimingProfile_of_approximateNash
      reward root deadline hdeadline (error := 0) hreward hnash hcontracts

end GameTheory
