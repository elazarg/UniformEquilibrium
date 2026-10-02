import UniformEquilibrium.Quitting.Punishment.NonnegativeSoloUniformization
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineFullReplyCap

/-! # Explicit finite-horizon error for profiles quiet after a deadline

The canonical estimates apply to actual profiles whose live roots Continue
after the cutoff. Finite timing-menu declarations are projections of this API.
Terminal rewards may be signed; only the comparison of a deviation with its
own terminal payoff uses a nonnegative own-singleton reward.
-/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem quittingLiveMass_eq_limit_of_jointContinue_one_from
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ)
    (hjoint : ∀ later, deadline ≤ later →
      quittingJointContinueMass reward profile later = 1)
    {time : ℕ} (htime : deadline ≤ time) :
    quittingLiveMass reward profile time = quittingLiveMassLimit reward profile := by
  have hconstant : ∀ offset : ℕ,
      quittingLiveMass reward profile (deadline + offset) =
        quittingLiveMass reward profile deadline := by
    intro offset
    induction offset with
    | zero => simp
    | succ offset ih =>
        rw [Nat.add_succ, quittingLiveMass_succ, hjoint (deadline + offset) (by omega),
          mul_one, ih]
  have heventually : ∀ᶠ later : ℕ in Filter.atTop,
      quittingLiveMass reward profile later = quittingLiveMass reward profile deadline := by
    filter_upwards [Filter.eventually_ge_atTop deadline] with later hlater
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlater
    exact hconstant offset
  have hlimit : quittingLiveMassLimit reward profile =
      quittingLiveMass reward profile deadline := by
    apply tendsto_nhds_unique (tendsto_quittingLiveMass reward profile)
    have hreverse : ∀ᶠ later : ℕ in Filter.atTop,
        quittingLiveMass reward profile deadline = quittingLiveMass reward profile later :=
      heventually.mono fun _ hlater => hlater.symm
    exact tendsto_const_nhds.congr' hreverse
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le htime
  rw [hconstant offset, hlimit]

omit [DecidableEq ι] in
theorem quittingLiveMass_eq_limit_of_quietAfterDeadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot)
    {time : ℕ} (htime : deadline ≤ time) :
    quittingLiveMass reward profile time = quittingLiveMassLimit reward profile := by
  have hjoint (later : ℕ) (hlater : deadline ≤ later) :
      quittingJointContinueMass reward profile later = 1 := by
    rw [quittingJointContinueMass_eq_product]
    apply Finset.prod_eq_one
    intro player _
    have hroot := congrFun (hquiet later hlater) player
    change profile player later (quittingLiveHist reward later) = PMF.pure false at hroot
    have hprob := congrArg (fun law : PMF Bool => (law false).toReal) hroot
    calc
      _ = ((PMF.pure false : PMF Bool) false).toReal := hprob
      _ = 1 := by norm_num [PMF.pure_apply]
  exact quittingLiveMass_eq_limit_of_jointContinue_one_from
    reward profile deadline hjoint htime

omit [DecidableEq ι] in
/-- A profile quiet after the deadline has at most `deadline`
nonzero terms, each at most one. -/
theorem sum_liveTail_quietAfterDeadline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot) :
    (∑ time ∈ Finset.range horizon,
        (quittingLiveMass reward profile time - quittingLiveMassLimit reward profile)) ≤
      deadline := by
  calc
    (∑ time ∈ Finset.range horizon,
        (quittingLiveMass reward profile time - quittingLiveMassLimit reward profile)) ≤
        ∑ time ∈ Finset.range horizon, if time < deadline then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro time htime
      by_cases hbefore : time < deadline
      · rw [ite_eq_left hbefore]
        have hone := quittingLiveMass_le_one reward profile time
        have hlimit := quittingLiveMassLimit_nonneg reward profile
        linarith
      · rw [ite_eq_right hbefore]
        have hflat := quittingLiveMass_eq_limit_of_quietAfterDeadline
          reward deadline profile hquiet (Nat.le_of_not_gt hbefore)
        simpa only [hflat, sub_self] using (le_refl (0 : ℝ))
    _ ≤ deadline := by
      calc
        (∑ time ∈ Finset.range horizon, if time < deadline then (1 : ℝ) else 0) =
            ((Finset.range horizon).filter fun time => time < deadline).card := by simp
        _ ≤ deadline := by
          simpa using Finset.card_le_card
            (show (Finset.range horizon).filter (fun time => time < deadline) ⊆
                Finset.range deadline by
              intro time htime
              simpa only [Finset.mem_range] using (Finset.mem_filter.mp htime).2)

omit [DecidableEq ι] in
theorem sum_liveTail_finiteDeadline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (∑ time ∈ Finset.range horizon,
        (quittingLiveMass reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) time -
          quittingLiveMassLimit reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed))) ≤ deadline :=
  sum_liveTail_quietAfterDeadline_le reward deadline horizon _
    (fun _ htime => quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
      reward deadline mixed htime)

/-- Replacing one player by perpetual Continue preserves the quiet deadline. -/
theorem quittingOpponentOnlyProfile_quietAfterDeadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot) (who : ι) :
    ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward (quittingOpponentOnlyProfile reward profile who) later =
        quittingAllContinueRoot := by
  intro later hlater
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingProfileLiveRoot, quittingOpponentOnlyProfile,
      quittingAlwaysContinueStrategy, quittingAllContinueRoot]
    rfl
  · have hroot := congrFun (hquiet later hlater) player
    simpa [quittingProfileLiveRoot, quittingOpponentOnlyProfile, hplayer,
      quittingAllContinueRoot] using hroot

/-- A quiet-after-deadline profile's opponent-only live-tail clock has at most
`deadline` nonzero terms, each at most one. -/
theorem sum_opponentLiveTail_quietAfterDeadline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot) (who : ι) :
    (∑ time ∈ Finset.range horizon,
        (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward profile who))) ≤
      deadline :=
  sum_liveTail_quietAfterDeadline_le reward deadline horizon _
    (quittingOpponentOnlyProfile_quietAfterDeadline reward deadline profile hquiet who)

theorem sum_opponentLiveTail_finiteDeadline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) (who : ι) :
    (∑ time ∈ Finset.range horizon,
        (quittingLiveMass reward
            (quittingOpponentOnlyProfile reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who) time -
          quittingLiveMassLimit reward
            (quittingOpponentOnlyProfile reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who))) ≤ deadline :=
  sum_opponentLiveTail_quietAfterDeadline_le reward deadline horizon _
    (fun _ htime => quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
      reward deadline mixed htime) who

omit [DecidableEq ι] in
/-- Prescribed finite-horizon payoff differs from the terminal payoff by at most the
displayed finite-word boundary charge. -/
theorem abs_finiteAveragePayoff_sub_terminal_quietAfterDeadline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot)
    (who : ι) {M : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
          profile who - quittingTerminalPayoff reward profile who| ≤
      M * deadline / horizon := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who))
  let : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  let : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  let initial : (quittingGame reward).State := none
  change |(quittingGame reward).finiteAveragePayoff initial horizon profile who -
      quittingTerminalPayoff reward profile who| ≤ M * deadline / horizon
  rw [(quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff]
  have hhorizonReal : (horizon : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hhorizon
  have hrewrite :
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          (quittingGame reward).expectedStagePayoff profile none time who -
        quittingTerminalPayoff reward profile who =
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        ((quittingGame reward).expectedStagePayoff profile none time who -
          quittingTerminalPayoff reward profile who) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hrewrite, abs_mul, abs_of_nonneg (by positivity)]
  calc
    (horizon : ℝ)⁻¹ *
        |∑ time ∈ Finset.range horizon,
          ((quittingGame reward).expectedStagePayoff profile none time who -
            quittingTerminalPayoff reward profile who)| ≤
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        |(quittingGame reward).expectedStagePayoff profile none time who -
          quittingTerminalPayoff reward profile who| := by
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        M * (quittingLiveMass reward profile time -
          quittingLiveMassLimit reward profile) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro time _
      simpa only [abs_sub_comm] using
        abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
          reward profile time who M hreward
    _ ≤ (horizon : ℝ)⁻¹ * (M * deadline) := by
      rw [← Finset.mul_sum]
      have hsum := mul_le_mul_of_nonneg_left
        (sum_liveTail_quietAfterDeadline_le reward deadline horizon profile hquiet) hM
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = M * deadline / horizon := by
      rw [div_eq_mul_inv]
      ring

omit [DecidableEq ι] in
theorem abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) {M : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who -
        quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who| ≤
      M * deadline / horizon :=
  abs_finiteAveragePayoff_sub_terminal_quietAfterDeadline_le reward deadline horizon _
    (fun _ htime => quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
      reward deadline mixed htime) who hreward hhorizon

/-- Every unilateral finite-horizon payoff is below its terminal payoff by at most the
same displayed boundary charge when singleton rewards are nonnegative. -/
theorem finiteAveragePayoff_update_quietAfterDeadline_le_terminal_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (profile : (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ later, deadline ≤ later →
      quittingProfileLiveRoot reward profile later = quittingAllContinueRoot)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) who ≤
      quittingTerminalPayoff reward
          (Function.update profile who deviation) who +
        M * deadline / horizon := by
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who))
  have hraw := finiteAveragePayoff_update_le_terminal_add_opponentLiveTailCesaro_of_solo_nonneg
    reward profile who deviation horizon hhorizon M hM hreward hsolo
  have hclock := sum_opponentLiveTail_quietAfterDeadline_le
    reward deadline horizon profile hquiet who
  have hinv : 0 ≤ (horizon : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hclock hinv) hM
  have hboundary : M * ((horizon : ℝ)⁻¹ * (deadline : ℝ)) =
      M * deadline / horizon := by rw [div_eq_mul_inv]; ring
  rw [hboundary] at hscaled
  exact hraw.trans (_root_.add_le_add le_rfl hscaled)

theorem finiteAveragePayoff_update_finiteDeadline_le_terminal_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who ≤
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who +
        M * deadline / horizon :=
  finiteAveragePayoff_update_quietAfterDeadline_le_terminal_add reward deadline horizon _
    (fun _ htime => quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
      reward deadline mixed htime) who deviation hreward hsolo hhorizon

/-- A terminal `D`-Nash finite timing profile is a finite-horizon
`D + 2M*deadline/horizon`-Nash profile. -/
theorem isHorizonNash_finiteDeadline_of_terminalNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {D M : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) D
      (quittingFiniteDeadlineTimingProfile reward deadline mixed))
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon
      (D + 2 * M * deadline / horizon)
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  intro who deviation
  have hterminal := hnash who deviation
  have hon := abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
    reward deadline horizon mixed who (fun terminal => hreward terminal who) hhorizon
  have hdev := finiteAveragePayoff_update_finiteDeadline_le_terminal_add
    reward deadline horizon mixed who deviation (fun terminal => hreward terminal who)
      (hsolo who) hhorizon
  have hlower := (abs_le.mp hon).1
  let boundary := M * deadline / horizon
  change _ ≤ _ + boundary at hdev
  change -boundary ≤ _ - _ at hlower
  calc
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who ≤
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who +
        boundary := hdev
    _ ≤ quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who + D + boundary := by
      linarith
    _ ≤ (quittingGame reward).finiteAveragePayoff none horizon
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        boundary + D + boundary := by
      linarith
    _ = (quittingGame reward).finiteAveragePayoff none horizon
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        (D + 2 * M * deadline / horizon) := by
      dsimp only [boundary]
      ring

/-- A consequence of the exact deadline estimate using the
`deadline + 1` boundary convention. -/
theorem isHorizonNash_finiteDeadline_of_terminalNash_add_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {D M : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) D
      (quittingFiniteDeadlineTimingProfile reward deadline mixed))
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon
      (D + 2 * M * (deadline + 1) / horizon)
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  intro who deviation
  have hexact := isHorizonNash_finiteDeadline_of_terminalNash
    reward deadline horizon mixed hnash hreward hsolo hhorizon who deviation
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal who) who)
  have hhorizonReal : (0 : ℝ) < horizon := by exact_mod_cast hhorizon
  calc
    _ ≤ (quittingGame reward).finiteAveragePayoff none horizon
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        (D + 2 * M * deadline / horizon) := hexact
    _ ≤ (quittingGame reward).finiteAveragePayoff none horizon
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        (D + 2 * M * (deadline + 1) / horizon) := by
      apply add_le_add_right
      have hdeadline : (deadline : ℝ) ≤ deadline + 1 := by norm_num
      exact add_le_add_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeadline (by positivity : 0 ≤ 2 * M))
          hhorizonReal.le) D

end GameTheory
