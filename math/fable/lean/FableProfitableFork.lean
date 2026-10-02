/-
Profitable stopping-law forks from a positive continuation debt.

If an observer's continuation best-response value exceeds the observer's own
terminal payoff by at least `Δ`, then a single complete stopping law realizes a
strictly profitable unilateral deviation whose gain is bounded below by
`Δ * Δ / (16 * quittingRewardBound reward)`, stated division-free.

The construction transports all of the observer's own `Δ / 2`-bad stopping mass
onto one `Δ / 4`-approximate maximizer of the pure-time deviation payoff.
-/
import FableStoppingSelection
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

noncomputable section

namespace GameTheory

open _root_.Math.Probability

/-! ### Bounded-integrand expectation helpers -/

/-- `expect` is monotone on uniformly bounded integrands. The finiteness-free
counterpart of `Math.Probability.expect_mono`. -/
theorem expect_mono_of_bounded {Ω : Type*} (d : PMF Ω) (g h : Ω → ℝ) {K : ℝ}
    (hg : ∀ ω, |g ω| ≤ K) (hh : ∀ ω, |h ω| ≤ K) (hle : ∀ ω, g ω ≤ h ω) :
    expect d g ≤ expect d h := by
  have hs := expect_summable_of_bounded d g hg
  have ht := expect_summable_of_bounded d h hh
  simp only [expect]
  exact hs.tsum_le_tsum
    (fun ω => mul_le_mul_of_nonneg_left (hle ω) ENNReal.toReal_nonneg) ht

/-! ### The abstract fork -/

/-- Abstract profitable fork on the space of complete stopping laws.

Given a lower bound on the mass that `nu` places on choices losing at least
`Δ / 2` against the ceiling `C`, and one receiver within `Δ / 4` of `C`,
redirecting the bad mass to the receiver produces a law whose expectation
gain over `nu` is at least `Δ * Δ / (16 * M)`, stated division-free. -/
theorem exists_fork_gain_of_badMass
    (nu : PMF (Option ℕ)) (value : Option ℕ → ℝ) (C M Δ : ℝ) (receiver : Option ℕ)
    (hval : ∀ choice, |value choice| ≤ M) (hΔ : 0 < Δ)
    (hrec : C - Δ / 4 < value receiver)
    (hbad : Δ ≤ 4 * M *
      expect nu (fun choice => if Δ / 2 ≤ C - value choice then 1 else 0)) :
    ∃ law : PMF (Option ℕ),
      Δ * Δ ≤ 16 * M * (expect law value - expect nu value) := by
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
  refine ⟨PMF.map (fun choice => if Δ / 2 ≤ C - value choice then receiver else choice) nu, ?_⟩
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

/-! ### The game-semantic fork -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive continuation debt for one observer is realized by a single
complete stopping law: reconstructing that law as the observer's own behavior
strategy strictly increases the observer's terminal payoff, quadratically in
the debt and inversely in the canonical reward bound. -/
theorem positiveDebt_exists_profitableStoppingLawFork
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hdebt : Δ ≤ quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) :
    ∃ law : PMF (Option ℕ),
      Δ * Δ ≤ 16 * quittingRewardBound reward *
        (quittingTerminalPayoff reward
            (Function.update profile observer
              (quittingStoppingLawBehaviorStrategy reward observer law)) observer -
          quittingTerminalPayoff reward profile observer) := by
  have hval : ∀ choice,
      |quittingPureTimeDeviationPayoff reward profile observer choice|
        ≤ quittingRewardBound reward := by
    intro choice
    unfold quittingPureTimeDeviationPayoff
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ observer
  have hC : ∀ choice, quittingPureTimeDeviationPayoff reward profile observer choice
      ≤ quittingContinuationBestResponseValue reward profile observer := by
    intro choice
    unfold quittingPureTimeDeviationPayoff
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
  have hbad := quittingStoppingLaw_badMass_lowerBound
    (quittingBehaviorLiveHazard reward (profile observer))
    (quittingPureTimeDeviationPayoff reward profile observer)
    (quittingContinuationBestResponseValue reward profile observer)
    (quittingRewardBound reward) Δ hval hC hCM hgap
  obtain ⟨receiver, hrec⟩ :
      ∃ receiver, quittingContinuationBestResponseValue reward profile observer - Δ / 4
        < quittingPureTimeDeviationPayoff reward profile observer receiver := by
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
  obtain ⟨law, hlaw⟩ := exists_fork_gain_of_badMass
    (quittingHazardStoppingLaw (quittingBehaviorLiveHazard reward (profile observer)))
    (quittingPureTimeDeviationPayoff reward profile observer)
    (quittingContinuationBestResponseValue reward profile observer)
    (quittingRewardBound reward) Δ receiver hval hΔ hrec hbad
  refine ⟨law, ?_⟩
  have hpayoff : quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingStoppingLawBehaviorStrategy reward observer law)) observer
      = expect law (quittingPureTimeDeviationPayoff reward profile observer) :=
    quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect
      reward profile observer observer law
  rw [hpayoff, hU, hnu]
  exact hlaw

end GameTheory
