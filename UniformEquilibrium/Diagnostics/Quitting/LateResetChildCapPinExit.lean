import UniformEquilibrium.Diagnostics.Quitting.FixedCapPinCoordinateDebtDrop
import UniformEquilibrium.Quitting.Root.NestedImmediateQuitCapExactPrefixExit

/-! # Quantitative exact-root exit at literal late-reset children -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {player : Type} [Fintype player] [DecidableEq player]

/-- At a literal child, an attained immediate-Quit cap is exactly the Quit
endpoint of the root which generated that child. -/
theorem childSemanticCap_eq_generatingRootQuitPayoff
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (children : ℕ → (quittingGame reward).BehaviorProfile)
    (generatingRoot : ℕ → player → PMF Bool) (observer : player)
    (hnested : ∀ index, children (index + 1) =
      quittingRootThenContinuationProfile reward (generatingRoot index)
        (children index))
    {index : ℕ}
    (hcap : ImmediateQuitAttainsTerminalCap reward
      (children (index + 1)) observer) :
    (quittingTerminalSemanticPair reward (children (index + 1))).2 observer =
      quittingRootQuitPayoff reward
        (fun who ↦ quittingTerminalPayoff reward (children index) who)
        (generatingRoot index) observer := by
  change quittingContinuationBestResponseValue reward
      (children (index + 1)) observer = _
  rw [hcap.symm, hnested index]
  exact quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff
    reward (generatingRoot index) (children index) observer

/-- Vanishing opponent absorption in the generating rows pins the complete
cap of every sufficiently late literal reset child to the singleton reward.
The conclusion remains conditional on that child's actual reset event. -/
theorem eventually_resetChild_semanticCap_close_singleton
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (children : ℕ → (quittingGame reward).BehaviorProfile)
    (generatingRoot : ℕ → player → PMF Bool) (observer : player)
    {M delta : ℝ} (hdelta : 0 < delta)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hnested : ∀ index, children (index + 1) =
      quittingRootThenContinuationProfile reward (generatingRoot index)
        (children index))
    (hopponentAbsorptionZero : Tendsto (fun index ↦
      quittingRootOpponentAbsorptionMass (generatingRoot index) observer)
        atTop (nhds 0)) :
    ∀ᶠ index in atTop,
      ImmediateQuitAttainsTerminalCap reward (children (index + 1)) observer →
        |(quittingTerminalSemanticPair reward
              (children (index + 1))).2 observer -
            reward (quittingSingletonTerminal observer) observer| ≤ delta / 4 := by
  have hscaled : Tendsto (fun index ↦
      2 * M * quittingRootOpponentAbsorptionMass
        (generatingRoot index) observer) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hopponentAbsorptionZero : Tendsto (fun index ↦
        (2 * M) * quittingRootOpponentAbsorptionMass
          (generatingRoot index) observer) atTop (nhds ((2 * M) * 0)))
  have hsmall : ∀ᶠ index in atTop,
      2 * M * quittingRootOpponentAbsorptionMass
        (generatingRoot index) observer < delta / 4 :=
    hscaled.eventually (Iio_mem_nhds (div_pos hdelta (by norm_num)))
  filter_upwards [hsmall] with index hsmallIndex
  intro hcap
  rw [childSemanticCap_eq_generatingRootQuitPayoff
    reward children generatingRoot observer hnested hcap]
  exact (abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
    reward _ (generatingRoot index) observer M hreward).trans hsmallIndex.le

/-- One actual child cap pin, kept together with the literal child profile
whose semantic payoff and unrestricted cap are being used. -/
structure LateResetChildCapPin
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (child : (quittingGame reward).BehaviorProfile)
    (observer : player) (delta : ℝ) : Prop where
  debtFloor : delta ≤ quittingTerminalDeviationDebt reward child observer
  capPin : |(quittingTerminalSemanticPair reward child).2 observer -
    reward (quittingSingletonTerminal observer) observer| ≤ delta / 4

theorem LateResetChildCapPin.payoff_le_singleton_sub_three_quarters
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {child : (quittingGame reward).BehaviorProfile}
    {observer : player} {delta : ℝ}
    (pin : LateResetChildCapPin reward child observer delta) :
    quittingTerminalPayoff reward child observer ≤
      reward (quittingSingletonTerminal observer) observer - 3 * delta / 4 := by
  have hcapUpper := (abs_le.mp pin.capPin).2
  have hdebt := pin.debtFloor
  change delta ≤
    (quittingTerminalSemanticPair reward child).2 observer -
      quittingTerminalPayoff reward child observer at hdebt
  linarith

/-- The selected observer's literal behavioral debt spends the canonical
fixed-cap amount under every exact root against this actual child. -/
theorem LateResetChildCapPin.everyExactRoot_coordinateDebtDrop
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {child : (quittingGame reward).BehaviorProfile}
    {observer : player} {M delta : ℝ}
    (pin : LateResetChildCapPin reward child observer delta)
    (hM : 0 < M) (hdelta : 0 < delta)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (exactRoot : player → PMF Bool)
    (hnash : IsεQuittingRootNash reward
      (fun who ↦ quittingTerminalPayoff reward child who) 0 exactRoot) :
    min (delta / 2) (delta ^ 2 / (16 * M)) ≤
      quittingTerminalDeviationDebt reward child observer -
        quittingTerminalDeviationDebt reward
          (quittingRootThenContinuationProfile reward exactRoot child)
          observer := by
  let pair := quittingTerminalSemanticPair reward child
  have hvalue : |pair.1 observer| ≤ M :=
    abs_quittingTerminalPayoff_le reward child observer hreward
  have hdrop := fixedCapPin_coordinateDebtDrop reward pair exactRoot observer
    hM hdelta hreward hvalue pin.debtFloor pin.capPin hnash
  change min (delta / 2) (delta ^ 2 / (16 * M)) ≤
    quittingTerminalSemanticDebt pair observer -
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward exactRoot child)) observer
  rw [quittingTerminalSemanticPair_rootThenContinuation]
  exact hdrop

/-- Every exact product root against the literal payoff of the pinned child
spends the fixed-cap debt amount and has the requested absorption floor. The
successor is the actual root-then-child behavioral profile. -/
theorem LateResetChildCapPin.everyExactRoot_debtDrop_and_absorptionFloor
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {child : (quittingGame reward).BehaviorProfile}
    {observer : player} {M delta : ℝ}
    (pin : LateResetChildCapPin reward child observer delta)
    (hM : 0 < M) (hdelta : 0 < delta)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (exactRoot : player → PMF Bool)
    (hnash : IsεQuittingRootNash reward
      (fun who ↦ quittingTerminalPayoff reward child who) 0 exactRoot) :
    min (delta / 2) (delta ^ 2 / (16 * M)) ≤
        quittingTerminalDebtSum reward child -
          quittingTerminalDebtSum reward
            (quittingRootThenContinuationProfile reward exactRoot child) ∧
      min 1 (delta / (16 * M)) ≤
        quittingRootAbsorptionMass exactRoot := by
  let pair := quittingTerminalSemanticPair reward child
  have hvalue : |pair.1 observer| ≤ M := by
    exact abs_quittingTerminalPayoff_le reward child observer hreward
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who := by
    intro who
    exact quittingTerminalDeviationDebt_nonneg reward child who
  have hdrop := fixedCapPin_totalDebtDrop reward pair exactRoot observer
    hM hdelta hreward hvalue hdebtNonneg pin.debtFloor pin.capPin hnash
  have hdropLiteral : min (delta / 2) (delta ^ 2 / (16 * M)) ≤
      quittingTerminalDebtSum reward child -
        quittingTerminalDebtSum reward
          (quittingRootThenContinuationProfile reward exactRoot child) := by
    change min (delta / 2) (delta ^ 2 / (16 * M)) ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward exactRoot child))
    rw [quittingTerminalSemanticPair_rootThenContinuation]
    exact hdrop
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨child, rfl⟩
  have hexit :=
    quittingTerminalSemanticPrefix_debtDrop_and_minAbsorption_of_carrier
      reward pair exactRoot observer hpair
        (show 0 < 3 * delta / 4 by positivity) hreward hvalue
        pin.debtFloor pin.payoff_le_singleton_sub_three_quarters hnash
  have hratio : delta / (16 * M) ≤ (3 * delta / 4) / (8 * M) := by
    have hdenominator : 0 < 32 * M := mul_pos (by norm_num) hM
    rw [show delta / (16 * M) = (2 * delta) / (32 * M) by
      field_simp; ring]
    rw [show (3 * delta / 4) / (8 * M) =
      (3 * delta) / (32 * M) by field_simp; ring]
    exact div_le_div_of_nonneg_right (by linarith) hdenominator.le
  have habsorption : min 1 (delta / (16 * M)) ≤
      quittingRootAbsorptionMass exactRoot := by
    exact (min_le_min le_rfl hratio).trans hexit.2.2
  exact ⟨hdropLiteral, habsorption⟩

/-- Child-source sequence adapter. Once the generating opponent hazards are
small, every actual reset child is itself a fixed cap pin. Every exact root
against that same child's literal payoff then spends the fixed amount of
total debt and absorbs at the stated rate. -/
theorem eventually_resetChild_everyExactRoot_debtDrop_and_absorptionFloor
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (children : ℕ → (quittingGame reward).BehaviorProfile)
    (generatingRoot : ℕ → player → PMF Bool) (observer : player)
    {M delta : ℝ} (hM : 0 < M) (hdelta : 0 < delta)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hnested : ∀ index, children (index + 1) =
      quittingRootThenContinuationProfile reward (generatingRoot index)
        (children index))
    (hopponentAbsorptionZero : Tendsto (fun index ↦
      quittingRootOpponentAbsorptionMass (generatingRoot index) observer)
        atTop (nhds 0))
    (hdebt : ∀ᶠ index in atTop,
      delta ≤ quittingTerminalDeviationDebt reward
        (children (index + 1)) observer) :
    ∀ᶠ index in atTop,
      ImmediateQuitAttainsTerminalCap reward (children (index + 1)) observer →
        LateResetChildCapPin reward (children (index + 1)) observer delta ∧
          quittingTerminalPayoff reward (children (index + 1)) observer ≤
            reward (quittingSingletonTerminal observer) observer -
              3 * delta / 4 ∧
          ∀ exactRoot : player → PMF Bool,
            IsεQuittingRootNash reward
                (fun who ↦ quittingTerminalPayoff reward
                  (children (index + 1)) who) 0 exactRoot →
              min (delta / 2) (delta ^ 2 / (16 * M)) ≤
                  quittingTerminalDebtSum reward (children (index + 1)) -
                    quittingTerminalDebtSum reward
                      (quittingRootThenContinuationProfile reward exactRoot
                        (children (index + 1))) ∧
                min 1 (delta / (16 * M)) ≤
                  quittingRootAbsorptionMass exactRoot := by
  have hcapClose := eventually_resetChild_semanticCap_close_singleton
    reward children generatingRoot observer hdelta hreward hnested
      hopponentAbsorptionZero
  filter_upwards [hcapClose, hdebt] with index hcapCloseIndex hdebtIndex
  intro hreset
  let pin : LateResetChildCapPin reward
      (children (index + 1)) observer delta :=
    ⟨hdebtIndex, hcapCloseIndex hreset⟩
  refine ⟨pin, pin.payoff_le_singleton_sub_three_quarters, ?_⟩
  intro exactRoot hnash
  exact pin.everyExactRoot_debtDrop_and_absorptionFloor
    hM hdelta hreward exactRoot hnash

end GameTheory
