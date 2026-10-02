/-
Common-prefix clause of the profitable stopping-law fork.

The profitable fork transports the observer's own `Δ / 2`-bad stopping mass
onto one `Δ / 4`-approximate maximizer of the pure-time deviation payoff.
Because the selected source is the earliest supported bad date and the
receiver is not earlier than the paid row's start date, that transport does
not move any mass strictly below the start date.  Hence the forked law and
the observer's actual live-spine stopping law have a common prefix: equal
finite masses, equal survival, equal reconstructed conditional hazards, and
therefore literally equal realized behavior strategies before the start date.
-/
import FableStoppingSelection
import FableDebtActualReach
import FableProfitableFork
import MathUE.Probability.StoppingLawReconstruction

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open _root_.Math.Probability.DiscreteHazard

/-! ### Generic law agreement below a cut -/

/-- Redirecting a bad set which is null strictly below the cut onto a receiver
which is not strictly below the cut leaves every stopping mass strictly below
the cut unchanged. -/
theorem stoppingLawFork_apply_eq_of_lt_cut
    (nu : PMF (Option ℕ)) (bad : Option ℕ → Prop) [DecidablePred bad]
    (receiver : Option ℕ) (cut : ℕ)
    (hnull : ∀ u, u < cut → bad (some u) → nu (some u) = 0)
    (hrec : ∀ u, u < cut → receiver ≠ some u)
    (u : ℕ) (hu : u < cut) :
    (PMF.map (fun q => if bad q then receiver else q) nu) (some u) = nu (some u) := by
  rw [PMF.map_apply]
  refine Eq.trans (tsum_congr (fun q => ?_))
    (tsum_ite_eq (some u) (fun _ => nu (some u)))
  · by_cases hq : bad q
    · rw [if_pos hq, if_neg (fun h : some u = receiver => hrec u hu h.symm)]
      by_cases hqu : q = some u
      · subst hqu
        rw [if_pos rfl]
        exact (hnull u hu hq).symm
      · rw [if_neg hqu]
    · rw [if_neg hq]
      by_cases hqu : q = some u
      · subst hqu
        simp
      · rw [if_neg hqu, if_neg (fun h : some u = q => hqu h.symm)]

/-- The transported law has the same finite masses strictly below the cut. -/
theorem stoppingLawFork_finiteMass_eq_of_lt_cut
    (nu : PMF (Option ℕ)) (bad : Option ℕ → Prop) [DecidablePred bad]
    (receiver : Option ℕ) (cut : ℕ)
    (hnull : ∀ u, u < cut → bad (some u) → nu (some u) = 0)
    (hrec : ∀ u, u < cut → receiver ≠ some u)
    (u : ℕ) (hu : u < cut) :
    StoppingLaw.finiteMass (PMF.map (fun q => if bad q then receiver else q) nu) u
      = StoppingLaw.finiteMass nu u := by
  unfold StoppingLaw.finiteMass
  rw [stoppingLawFork_apply_eq_of_lt_cut nu bad receiver cut hnull hrec u hu]

/-- The transported law has the same survival at every date up to the cut. -/
theorem stoppingLawFork_survival_eq_of_le_cut
    (nu : PMF (Option ℕ)) (bad : Option ℕ → Prop) [DecidablePred bad]
    (receiver : Option ℕ) (cut : ℕ)
    (hnull : ∀ u, u < cut → bad (some u) → nu (some u) = 0)
    (hrec : ∀ u, u < cut → receiver ≠ some u)
    (u : ℕ) (hu : u ≤ cut) :
    StoppingLaw.survival (PMF.map (fun q => if bad q then receiver else q) nu) u
      = StoppingLaw.survival nu u := by
  unfold StoppingLaw.survival
  refine congrArg (fun s => 1 - s) (Finset.sum_congr rfl ?_)
  intro time htime
  rw [Finset.mem_range] at htime
  exact stoppingLawFork_finiteMass_eq_of_lt_cut nu bad receiver cut hnull hrec time
    (lt_of_lt_of_le htime hu)

/-- The reconstructed conditional hazards agree strictly below the cut. -/
theorem stoppingLawFork_stop_eq_of_lt_cut
    (nu : PMF (Option ℕ)) (bad : Option ℕ → Prop) [DecidablePred bad]
    (receiver : Option ℕ) (cut : ℕ)
    (hnull : ∀ u, u < cut → bad (some u) → nu (some u) = 0)
    (hrec : ∀ u, u < cut → receiver ≠ some u)
    (u : ℕ) (hu : u < cut) :
    (StoppingLaw.toScalarHazard
        (PMF.map (fun q => if bad q then receiver else q) nu)).stop u
      = (StoppingLaw.toScalarHazard nu).stop u := by
  have hsurv := stoppingLawFork_survival_eq_of_le_cut nu bad receiver cut hnull hrec u hu.le
  have hmass := stoppingLawFork_finiteMass_eq_of_lt_cut nu bad receiver cut hnull hrec u hu
  simp only [StoppingLaw.toScalarHazard, hsurv, hmass]

/-- Boolean coins are determined by their stop probability. -/
private theorem booleanCoin_congr (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h : p = q) :
    booleanCoin p hp0 hp1 = booleanCoin q hq0 hq1 := by
  subst h
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The realized behavior strategies of the transported law and of the source
law are literally equal at every date strictly below the cut. -/
theorem stoppingLawFork_behaviorStrategy_eq_of_lt_cut
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (observer : ι)
    (nu : PMF (Option ℕ)) (bad : Option ℕ → Prop) [DecidablePred bad]
    (receiver : Option ℕ) (cut : ℕ)
    (hnull : ∀ u, u < cut → bad (some u) → nu (some u) = 0)
    (hrec : ∀ u, u < cut → receiver ≠ some u)
    (u : ℕ) (hu : u < cut) :
    ∀ history,
      quittingStoppingLawBehaviorStrategy reward observer
          (PMF.map (fun q => if bad q then receiver else q) nu) u history =
        quittingStoppingLawBehaviorStrategy reward observer nu u history := by
  intro history
  have hstop := stoppingLawFork_stop_eq_of_lt_cut nu bad receiver cut hnull hrec u hu
  unfold quittingStoppingLawBehaviorStrategy ScalarHazard.toBoolean
  exact booleanCoin_congr _ _ _ _ _ _ hstop

/-! ### The fork gain with an explicit transported law -/

/-- The abstract profitable fork with the transported law exposed.  This is the
statement of `exists_fork_gain_of_badMass` with the existential witness spelled
out, which is what the common-prefix clause needs. -/
theorem fork_gain_of_badMass
    (nu : PMF (Option ℕ)) (value : Option ℕ → ℝ) (C M Δ : ℝ) (receiver : Option ℕ)
    (hval : ∀ choice, |value choice| ≤ M) (hΔ : 0 < Δ)
    (hrec : C - Δ / 4 < value receiver)
    (hbad : Δ ≤ 4 * M *
      expect nu (fun choice => if Δ / 2 ≤ C - value choice then 1 else 0)) :
    Δ * Δ ≤ 16 * M *
      (expect (PMF.map
          (fun choice => if Δ / 2 ≤ C - value choice then receiver else choice) nu)
        value - expect nu value) := by
  set ind : Option ℕ → ℝ :=
    fun choice => if Δ / 2 ≤ C - value choice then 1 else 0 with hind
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hval receiver)
  have hind_nonneg : ∀ q, 0 ≤ ind q := by
    intro q
    simp only [hind]
    split <;> norm_num
  have hind_le_one : ∀ q, ind q ≤ 1 := by
    intro q
    simp only [hind]
    split <;> norm_num
  rw [expect_map (fun choice => if Δ / 2 ≤ C - value choice then receiver else choice) nu value]
  set forkValue : Option ℕ → ℝ :=
    fun choice => value (if Δ / 2 ≤ C - value choice then receiver else choice) with hforkValue
  have hforkBound : ∀ q, |forkValue q| ≤ Δ / 4 + M := by
    intro q
    have h := hval (if Δ / 2 ≤ C - value q then receiver else q)
    have hq : |forkValue q| ≤ M := by
      simp only [hforkValue]
      exact h
    linarith
  have hlinBound : ∀ q, |Δ / 4 * ind q + value q| ≤ Δ / 4 + M := by
    intro q
    have h1 : 0 ≤ Δ / 4 * ind q := mul_nonneg (by linarith) (hind_nonneg q)
    have h2 : Δ / 4 * ind q ≤ Δ / 4 := by
      have := mul_le_mul_of_nonneg_left (hind_le_one q) (by linarith : (0:ℝ) ≤ Δ / 4)
      linarith
    have h3 := abs_le.1 (hval q)
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hpointwise : ∀ q, Δ / 4 * ind q + value q ≤ forkValue q := by
    intro q
    by_cases hq : Δ / 2 ≤ C - value q
    · have h1 : ind q = 1 := by
        simp only [hind]
        simp [hq]
      have h2 : forkValue q = value receiver := by
        simp only [hforkValue]
        simp [hq]
      rw [h1, h2]
      linarith
    · have h1 : ind q = 0 := by
        simp only [hind]
        simp [hq]
      have h2 : forkValue q = value q := by
        simp only [hforkValue]
        simp [hq]
      rw [h1, h2]
      linarith
  have hindBound : ∀ q, |Δ / 4 * ind q| ≤ Δ / 4 := by
    intro q
    rw [abs_of_nonneg (mul_nonneg (by linarith) (hind_nonneg q))]
    have := mul_le_mul_of_nonneg_left (hind_le_one q) (by linarith : (0:ℝ) ≤ Δ / 4)
    linarith
  have hs1 : Summable (fun q => (nu q).toReal * (Δ / 4 * ind q)) :=
    expect_summable_of_bounded nu _ hindBound
  have hs2 : Summable (fun q => (nu q).toReal * value q) :=
    expect_summable_of_bounded nu _ hval
  have hadd : expect nu (fun q => Δ / 4 * ind q + value q)
      = expect nu (fun q => Δ / 4 * ind q) + expect nu value :=
    expect_add_of_summable nu (fun q => Δ / 4 * ind q) value hs1 hs2
  have hconst : expect nu (fun q => Δ / 4 * ind q) = Δ / 4 * expect nu ind :=
    expect_const_mul nu (Δ / 4) ind
  have hmono : expect nu (fun q => Δ / 4 * ind q + value q) ≤ expect nu forkValue :=
    expect_mono_of_bounded nu (fun q => Δ / 4 * ind q + value q) forkValue
      hlinBound hforkBound hpointwise
  rw [hadd, hconst] at hmono
  have hgain : Δ / 4 * expect nu ind ≤ expect nu forkValue - expect nu value := by
    linarith
  have h1 : Δ * Δ ≤ 4 * M * expect nu ind * Δ := mul_le_mul_of_nonneg_right hbad hΔ.le
  have h2 : 16 * M * (Δ / 4 * expect nu ind)
      ≤ 16 * M * (expect nu forkValue - expect nu value) :=
    mul_le_mul_of_nonneg_left hgain (by linarith)
  linarith

/-! ### Selection with a null prefix -/

/-- A vanishing quitting stop mass is a vanishing stopping-law atom. -/
private theorem quittingHazardStoppingLaw_apply_eq_zero_of_stopMass
    (hazard : ℕ → PMF Bool) (time : ℕ)
    (hzero : quittingHazardStopMass hazard time = 0) :
    quittingHazardStoppingLaw hazard (some time) = 0 := by
  have htoReal : (quittingHazardStoppingLaw hazard (some time)).toReal = 0 := by
    rw [quittingHazardStoppingLaw_some_toReal, hzero]
  rcases (ENNReal.toReal_eq_zero_iff _).1 htoReal with h | htop
  · exact h
  · exact absurd htop (PMF.apply_ne_top _ _)

/-- Selection of a bad source choice together with two properties valid at
every start date the selected source does not strictly precede: a survival
floor, and nullity of the whole bad set strictly below that start date. -/
private theorem quittingStoppingLaw_positiveGap_sourcePackage
    (hazard : ℕ → PMF Bool) (value : Option ℕ → ℝ) (C M Δ : ℝ)
    (hval : ∀ choice, |value choice| ≤ M)
    (hC : ∀ choice, value choice ≤ C) (hCM : C ≤ M) (hΔ : 0 < Δ)
    (hgap : Δ ≤ C - expect (quittingHazardStoppingLaw hazard) value) :
    ∃ source : Option ℕ, Δ / 2 ≤ C - value source ∧
      (∀ start : ℕ, (∀ n, source = some n → start ≤ n) →
        Δ ≤ 4 * M * quittingHazardSurvival hazard start) ∧
      (∀ start : ℕ, (∀ n, source = some n → start ≤ n) →
        ∀ u, u < start → Δ / 2 ≤ C - value (some u) →
          quittingHazardStoppingLaw hazard (some u) = 0) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hval none)
  have h4M : (0:ℝ) ≤ 4 * M := by linarith
  have hbad := quittingStoppingLaw_badMass_lowerBound hazard value C M Δ hval hC hCM hgap
  rcases quittingStoppingLaw_exists_leastBad_survival_lowerBound hazard
      (fun q => Δ / 2 ≤ C - value q) with ⟨-, hzero⟩ | ⟨n, hPn, -, hmin, hsurv⟩
  · refine ⟨none, ?_, ?_, ?_⟩
    · by_contra hnone
      have habs : ∀ q, |(if Δ / 2 ≤ C - value q then (1:ℝ) else 0)| ≤ 1 := by
        intro q
        split <;> norm_num
      have hexp := quittingHazardStoppingLaw_expect hazard
        (fun q => if Δ / 2 ≤ C - value q then (1:ℝ) else 0) habs
      have hterm : ∀ t : ℕ, quittingHazardStopMass hazard t *
          (if Δ / 2 ≤ C - value (some t) then (1:ℝ) else 0) = 0 := by
        intro t
        by_cases ht : Δ / 2 ≤ C - value (some t)
        · rw [hzero t ht]; ring
        · rw [if_neg ht]; ring
      rw [if_neg hnone, tsum_congr hterm, tsum_zero] at hexp
      rw [hexp] at hbad
      simp only [mul_zero, add_zero] at hbad
      linarith
    · intro start _
      have hle := quittingStoppingLaw_badMass_le_survival_of_noFiniteBad hazard
        (fun q => Δ / 2 ≤ C - value q) hzero start
      linarith [mul_le_mul_of_nonneg_left hle h4M]
    · intro start _ u _ hu
      exact quittingHazardStoppingLaw_apply_eq_zero_of_stopMass hazard u (hzero u hu)
  · refine ⟨some n, hPn, ?_, ?_⟩
    · intro start hstart
      have hmono := antitone_quittingHazardSurvival hazard (hstart n rfl)
      linarith [mul_le_mul_of_nonneg_left hsurv h4M,
        mul_le_mul_of_nonneg_left hmono h4M]
    · intro start hstart u hlt hu
      refine quittingHazardStoppingLaw_apply_eq_zero_of_stopMass hazard u ?_
      exact hmin u (lt_of_lt_of_le hlt (hstart n rfl)) hu

/-! ### The packaged common-prefix fork -/

/-- A positive continuation debt for one observer is realized by a single
complete stopping law which is a strictly profitable unilateral deviation,
which is genuinely reached — with a division-free floor both on the
observer's own live-spine survival through the paid row's start date and on
the opponents' live mass at that date — and which agrees with the observer's
actual behavior at every date strictly before that start date. -/
theorem positiveDebt_exists_commonPrefix_profitableStoppingLawFork
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ row : QuittingPaidFirstDisagreementRow reward profile observer (Δ / 4),
      ∃ law : PMF (Option ℕ),
        (Δ * Δ ≤ 16 * quittingRewardBound reward *
          (quittingTerminalPayoff reward
              (Function.update profile observer
                (quittingStoppingLawBehaviorStrategy reward observer law)) observer -
            quittingTerminalPayoff reward profile observer)) ∧
        (Δ ≤ 4 * quittingRewardBound reward *
          quittingHazardSurvival
            (quittingBehaviorLiveHazard reward (profile observer)) row.start) ∧
        (Δ ≤ 8 * quittingRewardBound reward * row.liveMass) ∧
        (∀ u, u < row.start → ∀ history,
          quittingStoppingLawBehaviorStrategy reward observer law u history =
          quittingStoppingLawBehaviorStrategy reward observer
            (quittingBehaviorStoppingLaw reward (profile observer)) u history) := by
  have hval : ∀ q, |quittingPureTimeDeviationPayoff reward profile observer q|
      ≤ quittingRewardBound reward := by
    intro q
    rw [quittingPureTimeDeviationPayoff]
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ observer
  have hCbound : ∀ q, quittingPureTimeDeviationPayoff reward profile observer q
      ≤ quittingContinuationBestResponseValue reward profile observer := by
    intro q
    rw [quittingPureTimeDeviationPayoff]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer _
  have hCM : quittingContinuationBestResponseValue reward profile observer
      ≤ quittingRewardBound reward :=
    le_trans (le_abs_self _)
      (abs_quittingContinuationBestResponseValue_le reward profile observer
        (abs_reward_le_quittingRewardBound reward))
  have hnu : quittingBehaviorStoppingLaw reward (profile observer)
      = quittingHazardStoppingLaw
          (quittingBehaviorLiveHazard reward (profile observer)) := rfl
  have hU : quittingTerminalPayoff reward profile observer
      = expect (quittingBehaviorStoppingLaw reward (profile observer))
          (quittingPureTimeDeviationPayoff reward profile observer) :=
    quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
      reward profile observer observer
  have hgap : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
      expect (quittingHazardStoppingLaw
          (quittingBehaviorLiveHazard reward (profile observer)))
        (quittingPureTimeDeviationPayoff reward profile observer) := by
    rw [← hnu, ← hU]
    exact hdebt
  obtain ⟨source, hsource, hfloor, hnullsel⟩ :=
    quittingStoppingLaw_positiveGap_sourcePackage
      (quittingBehaviorLiveHazard reward (profile observer))
      (quittingPureTimeDeviationPayoff reward profile observer)
      (quittingContinuationBestResponseValue reward profile observer)
      (quittingRewardBound reward) Δ hval hCbound hCM hΔ hgap
  obtain ⟨recv, hrecv⟩ :
      ∃ recv, quittingContinuationBestResponseValue reward profile observer - Δ / 4
        < quittingPureTimeDeviationPayoff reward profile observer recv := by
    have hne : (Set.range
        (quittingPureTimeDeviationPayoff reward profile observer)).Nonempty :=
      ⟨_, ⟨none, rfl⟩⟩
    have hlt : quittingContinuationBestResponseValue reward profile observer - Δ / 4
        < sSup (Set.range
            (quittingPureTimeDeviationPayoff reward profile observer)) := by
      rw [← quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
      linarith
    obtain ⟨v, hv, hvlt⟩ := exists_lt_of_lt_csSup hne hlt
    obtain ⟨q, rfl⟩ := hv
    exact ⟨q, hvlt⟩
  have hedge : Δ / 4 ≤ quittingPureTimeDeviationPayoff reward profile observer recv -
      quittingPureTimeDeviationPayoff reward profile observer source := by linarith
  obtain ⟨row, hrowSrc, hrowRecv⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward profile observer source recv (Δ / 4) (by linarith) hedge
  have hstartSrc : ∀ n, source = some n → row.start ≤ n := by
    intro n hn
    have hsw : row.sourceWitness = some n := hrowSrc.trans hn
    have hchr := row.chronology
    by_cases hre : row.receivingEarlier = true
    · rw [if_pos hre] at hchr
      have h2 := hchr.2
      rw [hsw] at h2
      cases hlater : row.later with
      | none =>
          rw [hlater] at h2
          simp [quittingAbsolutePureTime] at h2
      | some d =>
          rw [hlater] at h2
          simp [quittingAbsolutePureTime] at h2
          omega
    · rw [if_neg hre] at hchr
      have h1 := hchr.1
      rw [hsw] at h1
      simp only [Option.some.injEq] at h1
      omega
  have hstartRecv : ∀ k, recv = some k → row.start ≤ k := by
    intro k hk
    have hrw : row.receivingWitness = some k := hrowRecv.trans hk
    have hchr := row.chronology
    by_cases hre : row.receivingEarlier = true
    · rw [if_pos hre] at hchr
      have h1 := hchr.1
      rw [hrw] at h1
      simp only [Option.some.injEq] at h1
      omega
    · rw [if_neg hre] at hchr
      have h2 := hchr.2
      rw [hrw] at h2
      cases hlater : row.later with
      | none =>
          rw [hlater] at h2
          simp [quittingAbsolutePureTime] at h2
      | some d =>
          rw [hlater] at h2
          simp [quittingAbsolutePureTime] at h2
          omega
  refine ⟨row, PMF.map (fun choice => if Δ / 2 ≤
        quittingContinuationBestResponseValue reward profile observer -
          quittingPureTimeDeviationPayoff reward profile observer choice
      then recv else choice)
    (quittingHazardStoppingLaw (quittingBehaviorLiveHazard reward (profile observer))),
    ?_, ?_, ?_, ?_⟩
  · have hbad := quittingStoppingLaw_badMass_lowerBound
      (quittingBehaviorLiveHazard reward (profile observer))
      (quittingPureTimeDeviationPayoff reward profile observer)
      (quittingContinuationBestResponseValue reward profile observer)
      (quittingRewardBound reward) Δ hval hCbound hCM hgap
    have hgain := fork_gain_of_badMass
      (quittingHazardStoppingLaw (quittingBehaviorLiveHazard reward (profile observer)))
      (quittingPureTimeDeviationPayoff reward profile observer)
      (quittingContinuationBestResponseValue reward profile observer)
      (quittingRewardBound reward) Δ recv hval hΔ hrecv hbad
    rw [quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect,
      hU, hnu]
    exact hgain
  · exact hfloor row.start hstartSrc
  · have hlive := row.gain_le_liveMass
    linarith
  · intro u hu
    rw [hnu]
    refine stoppingLawFork_behaviorStrategy_eq_of_lt_cut reward observer
      (quittingHazardStoppingLaw (quittingBehaviorLiveHazard reward (profile observer)))
      (fun choice => Δ / 2 ≤
        quittingContinuationBestResponseValue reward profile observer -
          quittingPureTimeDeviationPayoff reward profile observer choice)
      recv row.start (hnullsel row.start hstartSrc) (fun w hw heq => ?_) u hu
    exact absurd (hstartRecv w heq) (not_le.2 hw)

end GameTheory
