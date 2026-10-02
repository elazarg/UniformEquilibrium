/-
Upper semicontinuity of quitting caps, and the social sign of the timing bubble.

Building on the pure-time continuity groundwork, three facts are proved here
about a sequence of behavior profiles whose live rows converge coordinatewise
at every date to the live rows of a limit profile.

* **Cap upper semicontinuity.**  When the deviator's solo reward is
  nonnegative, the limit profile's continuation best-response value is at most
  the `liminf` of the sequence's best-response values.
* **Payoff decomposition through escape.**  If every terminal outcome mass
  converges along the sequence, then the limit profile's outcome masses are
  bounded by those limits (Fatou), and the sequence's terminal payoffs
  converge to the limit profile's payoff plus the reward moment of the escaped
  mass.
* **The bubble is socially nonnegative.**  Along a debt-minimizing sequence
  with nonnegative solos, the escaped mass carries nonnegative aggregate
  social value, and the limit profile's total debt is at most the infimum plus
  that value.  For socially nonpositive tables the infimum is attained.
-/
import FablePureTimeContinuity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

noncomputable section

namespace GameTheory

open StochasticGame Filter _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A pigeonhole for the deleted absorption masses -/

/-- Beyond every cutoff some row deletes at most `ε` of the opponents'
absorption mass.  Otherwise finitely many rows would already delete more mass
than the total available. -/
theorem fable_exists_small_deletedStopMass
    (roots : ℕ → ι → PMF Bool) (who : ι) {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    ∃ t, T ≤ t ∧ fableDeletedStopMass roots who t ≤ ε := by
  by_cases hex : ∃ t, T ≤ t ∧ fableDeletedStopMass roots who t ≤ ε
  · exact hex
  exfalso
  have hcon : ∀ t, T ≤ t → ε < fableDeletedStopMass roots who t := by
    intro t ht
    by_contra hle
    exact hex ⟨t, ht, not_lt.mp hle⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
  have hsub : Finset.Ico T (T + K) ⊆ Finset.range (T + K) := by
    intro t ht
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2
  have hlow : (K : ℝ) * ε ≤
      ∑ t ∈ Finset.Ico T (T + K), fableDeletedStopMass roots who t := by
    have hcard : (Finset.Ico T (T + K)).card = K := by simp
    have hpt : ∀ t ∈ Finset.Ico T (T + K), ε ≤ fableDeletedStopMass roots who t := by
      intro t ht
      exact (hcon t (Finset.mem_Ico.mp ht).1).le
    have := Finset.card_nsmul_le_sum (Finset.Ico T (T + K))
      (fun t => fableDeletedStopMass roots who t) ε hpt
    rwa [hcard, nsmul_eq_mul] at this
  have hmid : ∑ t ∈ Finset.Ico T (T + K), fableDeletedStopMass roots who t ≤
      ∑ t ∈ Finset.range (T + K), fableDeletedStopMass roots who t :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun t _ _ => fableDeletedStopMass_nonneg roots who t)
  have htotal := sum_fableDeletedStopMass roots who (T + K)
  have hW := quittingOpponentSurvivalWeight_nonneg roots who 0 (T + K)
  have hle : (K : ℝ) * ε ≤ 1 := by
    rw [htotal] at hmid
    linarith
  have hgt : 1 < (K : ℝ) * ε := by
    have := (div_lt_iff₀ hε).mp hK
    linarith
  linarith

/-! ## The pure-time approximation of the `Never` value -/

/-- Against a fixed root sequence with nonnegative solo reward, some finite
quit date recovers the `Never` value up to `4Mε`. -/
theorem fable_exists_pureTimeValue_ge_never_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t, quittingRootSequencePureTimeTerminalValue reward roots who none -
        4 * M * ε ≤
      quittingRootSequencePureTimeTerminalValue reward roots who (some t) := by
  have hM : 0 ≤ M :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hbdd : BddBelow
      (Set.range (quittingOpponentSurvivalWeight roots who 0)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact quittingOpponentSurvivalWeight_nonneg roots who 0 n
  obtain ⟨T, hT⟩ := exists_lt_of_ciInf_lt
    (show (⨅ T', quittingOpponentSurvivalWeight roots who 0 T') <
      (⨅ T', quittingOpponentSurvivalWeight roots who 0 T') + ε by linarith)
  obtain ⟨t, htT, htmass⟩ := fable_exists_small_deletedStopMass roots who hε T
  have hinfle : ∀ k, (⨅ T', quittingOpponentSurvivalWeight roots who 0 T') ≤
      quittingOpponentSurvivalWeight roots who 0 k := fun k => ciInf_le hbdd k
  have hnever := fable_neverValue_tail_bound reward hreward roots who T
  have hrow := fable_pureTimeValue_row_estimate reward hreward roots who t
  have hgap := fable_abs_neverCollect_sub_le reward roots who hM
    (fun S => hreward S who) T t htT
  have hWt := quittingOpponentSurvivalWeight_nonneg roots who 0 t
  refine ⟨t, ?_⟩
  have hneverle : |quittingRootSequencePureTimeTerminalValue reward roots who none -
      fableNeverCollect reward roots who T| ≤ M * ε := by
    refine hnever.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hinfle T]) hM
  have hgaple : |fableNeverCollect reward roots who t -
      fableNeverCollect reward roots who T| ≤ M * ε := by
    refine hgap.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hinfle t]) hM
  have hrowle : |quittingRootSequencePureTimeTerminalValue reward roots who (some t) -
      (fableNeverCollect reward roots who t +
        quittingOpponentSurvivalWeight roots who 0 t *
          reward (quittingSingletonTerminal who) who)| ≤ 2 * M * ε := by
    refine hrow.trans ?_
    have : quittingOpponentSurvivalWeight roots who 0 t -
        quittingOpponentSurvivalWeight roots who 0 (t + 1) ≤ ε := htmass
    nlinarith [this]
  have hsoloterm : 0 ≤ quittingOpponentSurvivalWeight roots who 0 t *
      reward (quittingSingletonTerminal who) who := mul_nonneg hWt hsolo
  have h1 := abs_le.mp hneverle
  have h2 := abs_le.mp hgaple
  have h3 := abs_le.mp hrowle
  linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-! ## Profile-level bridge -/

/-- The profile-level pure-time deviation payoff is the root-sequence
pure-time value read at the profile's live rows. -/
theorem fable_pureTimeDeviationPayoff_eq_rootValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (quitTime : Option ℕ) :
    quittingPureTimeDeviationPayoff reward profile observer quitTime =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward profile) observer quitTime := by
  unfold quittingPureTimeDeviationPayoff
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]

/-! ## Target 1: caps cannot jump up -/

/-- **Cap upper semicontinuity.**  If the live rows converge coordinatewise at
every date and the observer's solo reward is nonnegative, the limit profile's
continuation best-response value is at most the `liminf` of the sequence's
best-response values. -/
theorem fable_bestResponse_usc
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hreward : ∀ S player, |reward S player| ≤ M)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile) (observer : ι)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t))
    (hsolo : 0 ≤ reward (quittingSingletonTerminal observer) observer) :
    quittingContinuationBestResponseValue reward limit observer ≤
      liminf (fun n =>
        quittingContinuationBestResponseValue reward (profiles n) observer)
        atTop := by
  have hM : 0 ≤ M :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal observer) observer)
  set cap : ℕ → ℝ := fun n =>
    quittingContinuationBestResponseValue reward (profiles n) observer with hcap
  have hcapabs : ∀ n, |cap n| ≤ M := fun n =>
    abs_quittingContinuationBestResponseValue_le reward (profiles n) observer hreward
  have hbddU : IsBoundedUnder (· ≤ ·) atTop cap :=
    isBoundedUnder_of ⟨M, fun n => (le_abs_self _).trans (hcapabs n)⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop cap := hbddU.isCoboundedUnder_ge
  have hfinite : ∀ t : ℕ,
      quittingPureTimeDeviationPayoff reward limit observer (some t) ≤
        liminf cap atTop := by
    intro t
    have htend := fable_pureTimeDeviationPayoff_tendsto reward profiles limit
      observer t (fun s _ => hconv s)
    have hle : ∀ n,
        quittingPureTimeDeviationPayoff reward (profiles n) observer (some t) ≤
          cap n := by
      intro n
      unfold quittingPureTimeDeviationPayoff
      exact quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward (profiles n) observer _
    have hbddseq : IsBoundedUnder (· ≥ ·) atTop
        (fun n =>
          quittingPureTimeDeviationPayoff reward (profiles n) observer (some t)) := by
      refine isBoundedUnder_of ⟨-M, fun n => ?_⟩
      refine neg_le_of_abs_le ?_
      unfold quittingPureTimeDeviationPayoff
      exact abs_quittingTerminalPayoff_le reward _ observer hreward
    calc quittingPureTimeDeviationPayoff reward limit observer (some t)
        = liminf (fun n => quittingPureTimeDeviationPayoff reward (profiles n)
            observer (some t)) atTop := htend.liminf_eq.symm
      _ ≤ liminf cap atTop :=
          liminf_le_liminf (Eventually.of_forall hle) hbddseq hcobdd
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  refine csSup_le ⟨_, Set.mem_range_self none⟩ ?_
  rintro value ⟨quitTime, rfl⟩
  match quitTime with
  | some t => exact hfinite t
  | none =>
      refine le_of_forall_pos_le_add ?_
      intro delta hdelta
      set eps : ℝ := delta / (4 * M + 1) with heps
      have hpos : (0 : ℝ) < 4 * M + 1 := by linarith
      have heps0 : 0 < eps := div_pos hdelta hpos
      have hcancel : 4 * M * eps + eps = delta := by
        have hmul : (4 * M + 1) * eps = delta := by
          rw [heps]
          field_simp
        linear_combination hmul
      obtain ⟨t, ht⟩ := fable_exists_pureTimeValue_ge_never_sub reward hreward
        (quittingProfileLiveRoot reward limit) observer hsolo heps0
      have hbridgeNone := fable_pureTimeDeviationPayoff_eq_rootValue reward limit
        observer none
      have hbridgeSome := fable_pureTimeDeviationPayoff_eq_rootValue reward limit
        observer (some t)
      have hsome := hfinite t
      rw [hbridgeSome] at hsome
      rw [hbridgeNone]
      linarith [ht, hsome, heps0]

/-! ## Continuity of the finite-horizon absorption law -/

omit [DecidableEq ι] in
/-- The conditional all-continue mass is continuous in the live rows. -/
theorem fable_jointContinueMass_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t)) (t : ℕ) :
    Tendsto (fun n => quittingJointContinueMass reward (profiles n) t) atTop
      (nhds (quittingJointContinueMass reward limit t)) := by
  have hrw : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingJointContinueMass reward profile t =
        (pmfPi (quittingProfileLiveRoot reward profile t)
          (quittingAllContinueAction : ι → Bool)).toReal := fun _ => rfl
  simp only [hrw]
  exact fable_pmfPi_toReal_tendsto (hconv t) _

/-- The conditional coalition mass at a live row is continuous in the live
rows. -/
theorem fable_liveRowCoalitionMass_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t)) (t : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun n => quittingLiveRowCoalitionMass reward (profiles n) t terminal)
      atTop (nhds (quittingLiveRowCoalitionMass reward limit t terminal)) := by
  have hrw : ∀ profile : (quittingGame reward).BehaviorProfile,
      quittingLiveRowCoalitionMass reward profile t terminal =
        (pmfPi (quittingProfileLiveRoot reward profile t)
          (quittingTerminalCoalitionAction terminal)).toReal := fun _ => rfl
  simp only [hrw]
  exact fable_pmfPi_toReal_tendsto (hconv t) _

omit [DecidableEq ι] in
/-- The live mass at a finite date is the product of the all-continue masses
of the earlier rows. -/
theorem fable_liveMass_eq_prod
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (T : ℕ) :
    quittingLiveMass reward profile T =
      ∏ t ∈ Finset.range T, quittingJointContinueMass reward profile t := by
  induction T with
  | zero => simp
  | succ T ih => rw [quittingLiveMass_succ, ih, Finset.prod_range_succ]

omit [DecidableEq ι] in
/-- The live mass at a finite date is continuous in the live rows. -/
theorem fable_liveMass_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t)) (T : ℕ) :
    Tendsto (fun n => quittingLiveMass reward (profiles n) T) atTop
      (nhds (quittingLiveMass reward limit T)) := by
  simp only [fable_liveMass_eq_prod]
  exact tendsto_finsetProd _ fun t _ =>
    fable_jointContinueMass_tendsto reward profiles limit hconv t

/-- Each chronological stage atom is continuous in the live rows. -/
theorem fable_stageCoalitionMass_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t)) (t : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun n => quittingStageCoalitionMass reward (profiles n) t terminal)
      atTop (nhds (quittingStageCoalitionMass reward limit t terminal)) := by
  unfold quittingStageCoalitionMass
  exact (fable_liveMass_tendsto reward profiles limit hconv t).mul
    (fable_liveRowCoalitionMass_tendsto reward profiles limit hconv t terminal)

/-- Every finite-horizon absorption mass is continuous in the live rows. -/
theorem fable_absorbedMass_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t)) (T : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun n => quittingAbsorbedMass reward (profiles n) T terminal)
      atTop (nhds (quittingAbsorbedMass reward limit T terminal)) := by
  simp only [quittingAbsorbedMass_eq_sum_stageCoalitionMass]
  exact tendsto_finsetSum _ fun t _ =>
    fable_stageCoalitionMass_tendsto reward profiles limit hconv t terminal

omit [DecidableEq ι] in
/-- The terminal payoff is the reward moment of the terminal outcome law. -/
theorem fable_terminalPayoff_eq_sum_outcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward profile who =
      ∑ S, quittingTerminalOutcomeMass reward profile (some S) * reward S who :=
  rfl

/-! ## Target 2: payoff decomposition through escape -/

/-- **Payoff decomposition through escape.**  If the live rows converge at
every date and every terminal outcome mass converges along the sequence, then
the limit profile's outcome masses are bounded by those limits, and the
sequence's terminal payoffs converge to the limit profile's payoff plus the
reward moment of the escaped mass. -/
theorem fable_payoff_escape_decomposition
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t))
    (tau : {S : Finset ι // S.Nonempty} → ℝ)
    (htau : ∀ S, Tendsto (fun n =>
        quittingTerminalOutcomeMass reward (profiles n) (some S))
      atTop (nhds (tau S))) :
    (∀ S, quittingTerminalOutcomeMass reward limit (some S) ≤ tau S) ∧
      ∀ who, Tendsto (fun n => quittingTerminalPayoff reward (profiles n) who)
        atTop (nhds (quittingTerminalPayoff reward limit who +
          ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
            reward S who)) := by
  refine ⟨fun S => ?_, fun who => ?_⟩
  · show quittingAbsorbedMassLimit reward limit S ≤ tau S
    unfold quittingAbsorbedMassLimit
    refine ciSup_le fun T => ?_
    refine le_of_tendsto_of_tendsto
      (fable_absorbedMass_tendsto reward profiles limit hconv T S) (htau S) ?_
    exact Eventually.of_forall fun n =>
      quittingAbsorbedMass_le_limit reward (profiles n) T S
  · have hsum : Tendsto (fun n => ∑ S,
        quittingTerminalOutcomeMass reward (profiles n) (some S) * reward S who)
        atTop (nhds (∑ S, tau S * reward S who)) :=
      tendsto_finsetSum _ fun S _ => (htau S).mul_const (reward S who)
    have hrhs : quittingTerminalPayoff reward limit who +
        ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
          reward S who = ∑ S, tau S * reward S who := by
      rw [fable_terminalPayoff_eq_sum_outcomeMass reward limit who,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun S _ => by ring
    rw [hrhs]
    simpa only [fable_terminalPayoff_eq_sum_outcomeMass] using hsum

/-! ## Finite superadditivity of `liminf` -/

omit [DecidableEq ι] in
/-- If the coordinate sums converge, the sum of the coordinatewise `liminf`s
is at most that limit. -/
theorem fable_sum_liminf_le_of_tendsto
    {a : ℕ → ι → ℝ} {C : ℝ}
    (hbdd : ∀ who, IsBoundedUnder (· ≥ ·) atTop (fun n => a n who))
    (htotal : Tendsto (fun n => ∑ who, a n who) atTop (nhds C)) :
    ∑ who, liminf (fun n => a n who) atTop ≤ C := by
  refine le_of_forall_pos_le_add ?_
  intro delta hdelta
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) + 1 := by positivity
  set eps : ℝ := delta / ((Fintype.card ι : ℝ) + 1) with hepsdef
  have heps0 : 0 < eps := div_pos hdelta hcardpos
  have hmul : ((Fintype.card ι : ℝ) + 1) * eps = delta := by
    rw [hepsdef]
    field_simp
  have hcard : (Fintype.card ι : ℝ) * eps ≤ delta := by nlinarith [heps0]
  have hev : ∀ᶠ n in atTop, ∀ who,
      liminf (fun m => a m who) atTop - eps < a n who := by
    refine eventually_all.2 fun who => ?_
    exact eventually_lt_of_lt_liminf (by linarith) (hbdd who)
  have hevsum : ∀ᶠ n in atTop,
      (∑ who, liminf (fun m => a m who) atTop) -
        (Fintype.card ι : ℝ) * eps ≤ ∑ who, a n who := by
    filter_upwards [hev] with n hn
    have hstep : ∑ who, (liminf (fun m => a m who) atTop - eps) ≤
        ∑ who, a n who :=
      Finset.sum_le_sum fun who _ => (hn who).le
    rwa [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ] at hstep
  have hlim := ge_of_tendsto htotal hevsum
  linarith

/-! ## Target 3: the social sign of the timing bubble -/

/-- **The bubble is socially nonnegative.**  Along a sequence whose live rows
converge at every date, whose outcome masses converge, and whose total debt
tends to the actual-profile infimum, the escaped mass carries nonnegative
aggregate social value, and the limit profile's total debt is at most the
infimum plus that value. -/
theorem fable_bubble_social_sign
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hreward : ∀ S player, |reward S player| ≤ M)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t))
    (tau : {S : Finset ι // S.Nonempty} → ℝ)
    (htau : ∀ S, Tendsto (fun n =>
        quittingTerminalOutcomeMass reward (profiles n) (some S))
      atTop (nhds (tau S)))
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hmin : Tendsto (fun n => quittingTerminalDebtSum reward (profiles n))
      atTop (nhds (quittingTerminalDebtSumInf reward))) :
    0 ≤ (∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
        (∑ who, reward S who)) ∧
      quittingTerminalDebtSum reward limit ≤ quittingTerminalDebtSumInf reward +
        ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
          (∑ who, reward S who) := by
  obtain ⟨-, hdecomp⟩ :=
    fable_payoff_escape_decomposition reward profiles limit hconv tau htau
  -- the escaped social value splits playerwise
  have hEsum : ∑ who, (∑ S,
        (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
          reward S who) =
      ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
        (∑ who, reward S who) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => (Finset.mul_sum _ _ _).symm
  -- playerwise payoff limits
  have hpaysum : Tendsto (fun n =>
      ∑ who, quittingTerminalPayoff reward (profiles n) who) atTop
      (nhds (∑ who, (quittingTerminalPayoff reward limit who +
        ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
          reward S who))) :=
    tendsto_finsetSum _ fun who _ => hdecomp who
  -- the cap sums converge
  have hcapsum : ∀ n, ∑ who,
      quittingContinuationBestResponseValue reward (profiles n) who =
      quittingTerminalDebtSum reward (profiles n) +
        ∑ who, quittingTerminalPayoff reward (profiles n) who := by
    intro n
    unfold quittingTerminalDebtSum quittingTerminalDeviationDebt
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun who _ => by ring
  have hcaptend : Tendsto (fun n => ∑ who,
      quittingContinuationBestResponseValue reward (profiles n) who) atTop
      (nhds (quittingTerminalDebtSumInf reward +
        ∑ who, (quittingTerminalPayoff reward limit who +
          ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
            reward S who))) := by
    simp only [hcapsum]
    exact hmin.add hpaysum
  -- coordinatewise liminf superadditivity
  have hbdd : ∀ who, IsBoundedUnder (· ≥ ·) atTop
      (fun n => quittingContinuationBestResponseValue reward (profiles n) who) := by
    intro who
    refine isBoundedUnder_of ⟨-M, fun n => ?_⟩
    exact neg_le_of_abs_le
      (abs_quittingContinuationBestResponseValue_le reward (profiles n) who hreward)
  have hsuper := fable_sum_liminf_le_of_tendsto hbdd hcaptend
  -- upper semicontinuity of every coordinate cap
  have husc : ∀ who, quittingContinuationBestResponseValue reward limit who ≤
      liminf (fun n =>
        quittingContinuationBestResponseValue reward (profiles n) who) atTop :=
    fun who => fable_bestResponse_usc reward hreward profiles limit who hconv
      (hsolo who)
  have hcapLe : ∑ who, quittingContinuationBestResponseValue reward limit who ≤
      ∑ who, liminf (fun n =>
        quittingContinuationBestResponseValue reward (profiles n) who) atTop :=
    Finset.sum_le_sum fun who _ => husc who
  have hsplit : ∑ who, (quittingTerminalPayoff reward limit who +
      ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
        reward S who) =
      (∑ who, quittingTerminalPayoff reward limit who) +
        ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
          (∑ who, reward S who) := by
    rw [Finset.sum_add_distrib, hEsum]
  have hdebtEq : quittingTerminalDebtSum reward limit =
      (∑ who, quittingContinuationBestResponseValue reward limit who) -
        ∑ who, quittingTerminalPayoff reward limit who := by
    unfold quittingTerminalDebtSum quittingTerminalDeviationDebt
    rw [Finset.sum_sub_distrib]
  rw [hsplit] at hsuper
  have hupper : quittingTerminalDebtSum reward limit ≤
      quittingTerminalDebtSumInf reward +
        ∑ S, (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
          (∑ who, reward S who) := by
    rw [hdebtEq]
    linarith
  refine ⟨?_, hupper⟩
  have hlower := quittingTerminalDebtSumInf_le (reward := reward) limit
  linarith

/-- **Attainment for socially nonpositive quitting.**  If every coalition has
nonpositive social value, the escaped social value is zero and the limit
profile attains the total-debt infimum. -/
theorem fable_bubble_attainment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hreward : ∀ S player, |reward S player| ≤ M)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limit : (quittingGame reward).BehaviorProfile)
    (hconv : ∀ t, FableRowTendsto
      (fun n => quittingProfileLiveRoot reward (profiles n) t)
      (quittingProfileLiveRoot reward limit t))
    (tau : {S : Finset ι // S.Nonempty} → ℝ)
    (htau : ∀ S, Tendsto (fun n =>
        quittingTerminalOutcomeMass reward (profiles n) (some S))
      atTop (nhds (tau S)))
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hmin : Tendsto (fun n => quittingTerminalDebtSum reward (profiles n))
      atTop (nhds (quittingTerminalDebtSumInf reward)))
    (hsocial : ∀ S, (∑ who, reward S who) ≤ 0) :
    quittingTerminalDebtSum reward limit = quittingTerminalDebtSumInf reward := by
  obtain ⟨hfatou, -⟩ :=
    fable_payoff_escape_decomposition reward profiles limit hconv tau htau
  obtain ⟨hsign, hupper⟩ := fable_bubble_social_sign reward hreward profiles
    limit hconv tau htau hsolo hmin
  have hnonpos : (∑ S,
      (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
        (∑ who, reward S who)) ≤ 0 := by
    refine Finset.sum_nonpos fun S _ => ?_
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hfatou S]) (hsocial S)
  have hzero : (∑ S,
      (tau S - quittingTerminalOutcomeMass reward limit (some S)) *
        (∑ who, reward S who)) = 0 := le_antisymm hnonpos hsign
  have hlower := quittingTerminalDebtSumInf_le (reward := reward) limit
  rw [hzero] at hupper
  linarith

end GameTheory
