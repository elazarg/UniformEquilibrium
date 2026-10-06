import UniformEquilibrium.Quitting.Classification.BoxedQuittingNashChargeReturn
import UniformEquilibrium.Quitting.Classification.QuittingPremiumTrapNeighborhood

/-! # Strict raw boxed-charge tests persist on full reward-table neighborhoods

The fixed positive coefficient scalars and a strictly larger coordinate bound
are kept throughout the neighborhood. Actual participant signs preserve the
trap inventory; no root or strategic witness is assumed.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def QuittingTrapChargeCoefficients.Strict
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {active : Finset ι}
    (coefficients : QuittingTrapChargeCoefficients reward active) : Prop :=
  (∀ (coalition : Finset ι) (hne : coalition.Nonempty),
    coalition ⊂ active → coalition.card = 1 →
      quittingTrapInsertedPremiumSum reward active coalition < -coefficients.delta ∧
        quittingTrapLeaveSum reward active ⟨coalition, hne⟩ < -coefficients.gap) ∧
  (∀ (coalition : Finset ι) (hne : coalition.Nonempty),
    coalition ⊂ active → 2 ≤ coalition.card → coalition.card ≤ active.card - 2 →
      quittingTrapInsertedPremiumSum reward active coalition < 0 ∧
        quittingTrapLeaveSum reward active ⟨coalition, hne⟩ < 0) ∧
  ∀ (coalition : Finset ι) (hne : coalition.Nonempty),
    coalition ⊂ active → coalition.card = active.card - 1 →
      quittingTrapInsertedPremiumSum reward active coalition < coefficients.tau ∧
        quittingTrapLeaveSum reward active ⟨coalition, hne⟩ < -coefficients.loss

def HasStrictBoxedQuittingNashCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Prop :=
  ∀ active, IsQuittingPremiumTrap reward active →
    ∃ coefficients : QuittingTrapChargeCoefficients reward active,
      coefficients.Strict ∧
        (∑ player ∈ active, reward (quittingSingletonTerminal player) player) +
          (active.card : ℝ) * bound < coefficients.threshold

omit [Fintype ι] in
theorem continuous_quittingTrapInsertedPremiumSum (active coalition : Finset ι) :
    Continuous (fun reward : {S : Finset ι // S.Nonempty} → Payoff ι =>
      quittingTrapInsertedPremiumSum reward active coalition) := by
  unfold quittingTrapInsertedPremiumSum
  fun_prop

omit [Fintype ι] in
theorem continuous_quittingTrapLeaveSum (active : Finset ι)
    (coalition : {S : Finset ι // S.Nonempty}) :
    Continuous (fun reward : {S : Finset ι // S.Nonempty} → Payoff ι =>
      quittingTrapLeaveSum reward active coalition) := by
  unfold quittingTrapLeaveSum quittingWeightedLeaveSum
  fun_prop

private theorem eventually_strict_coefficient_tests
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (active : Finset ι)
    (coefficients : QuittingTrapChargeCoefficients reward active)
    (hstrict : coefficients.Strict) :
    ∀ᶠ nearby in 𝓝 reward,
      ∀ coalition : {S : Finset ι // S.Nonempty}, coalition.val ⊂ active →
        (coalition.val.card = 1 →
          quittingTrapInsertedPremiumSum nearby active coalition.val < -coefficients.delta ∧
            quittingTrapLeaveSum nearby active coalition < -coefficients.gap) ∧
        (2 ≤ coalition.val.card → coalition.val.card ≤ active.card - 2 →
          quittingTrapInsertedPremiumSum nearby active coalition.val < 0 ∧
            quittingTrapLeaveSum nearby active coalition < 0) ∧
        (coalition.val.card = active.card - 1 →
          quittingTrapInsertedPremiumSum nearby active coalition.val < coefficients.tau ∧
            quittingTrapLeaveSum nearby active coalition < -coefficients.loss) := by
  rw [Filter.eventually_all]
  intro coalition
  have hpremiumContinuous :=
    (continuous_quittingTrapInsertedPremiumSum active coalition.val).continuousAt (x := reward)
  have hleaveContinuous :=
    (continuous_quittingTrapLeaveSum active coalition).continuousAt (x := reward)
  by_cases hproper : coalition.val ⊂ active
  · have hsingle : ∀ᶠ nearby in 𝓝 reward, coalition.val.card = 1 →
        quittingTrapInsertedPremiumSum nearby active coalition.val < -coefficients.delta ∧
          quittingTrapLeaveSum nearby active coalition < -coefficients.gap := by
      by_cases hcard : coalition.val.card = 1
      · obtain ⟨hpremium, hleave⟩ := hstrict.1 coalition.val coalition.property hproper hcard
        filter_upwards
          [hpremiumContinuous.eventually_lt_const hpremium,
          hleaveContinuous.eventually_lt_const hleave] with nearby hfirst hsecond _
        exact ⟨hfirst, hsecond⟩
      · exact Filter.Eventually.of_forall fun _ h => False.elim (hcard h)
    have hmiddle : ∀ᶠ nearby in 𝓝 reward, 2 ≤ coalition.val.card →
        coalition.val.card ≤ active.card - 2 →
          quittingTrapInsertedPremiumSum nearby active coalition.val < 0 ∧
            quittingTrapLeaveSum nearby active coalition < 0 := by
      by_cases hlow : 2 ≤ coalition.val.card
      · by_cases hhigh : coalition.val.card ≤ active.card - 2
        · obtain ⟨hpremium, hleave⟩ :=
            hstrict.2.1 coalition.val coalition.property hproper hlow hhigh
          filter_upwards
            [hpremiumContinuous.eventually_lt_const hpremium,
            hleaveContinuous.eventually_lt_const hleave] with nearby hfirst hsecond _ _
          exact ⟨hfirst, hsecond⟩
        · exact Filter.Eventually.of_forall fun _ _ h => False.elim (hhigh h)
      · exact Filter.Eventually.of_forall fun _ h _ => False.elim (hlow h)
    have hlast : ∀ᶠ nearby in 𝓝 reward, coalition.val.card = active.card - 1 →
        quittingTrapInsertedPremiumSum nearby active coalition.val < coefficients.tau ∧
          quittingTrapLeaveSum nearby active coalition < -coefficients.loss := by
      by_cases hcard : coalition.val.card = active.card - 1
      · obtain ⟨hpremium, hleave⟩ := hstrict.2.2 coalition.val coalition.property hproper hcard
        filter_upwards
          [hpremiumContinuous.eventually_lt_const hpremium,
          hleaveContinuous.eventually_lt_const hleave] with nearby hfirst hsecond _
        exact ⟨hfirst, hsecond⟩
      · exact Filter.Eventually.of_forall fun _ h => False.elim (hcard h)
    filter_upwards [hsingle, hmiddle, hlast] with nearby hsingle hmiddle hlast _
    exact ⟨hsingle, hmiddle, hlast⟩
  · exact Filter.Eventually.of_forall fun _ h => False.elim (hproper h)

theorem eventually_boxedQuittingNashCharges_of_strict_tests
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (hgaps : ∀ (terminal : {S : Finset ι // S.Nonempty}) (player : ι),
      player ∈ terminal.val → 2 ≤ terminal.val.card →
        reward terminal player - reward (quittingSingletonTerminal player) player ≠ 0)
    (hstrict : HasStrictBoxedQuittingNashCharges reward bound) :
    ∀ᶠ nearby in 𝓝 reward, HasBoxedQuittingNashCharges nearby bound := by
  have htests : ∀ᶠ nearby in 𝓝 reward, ∀ active,
      IsQuittingPremiumTrap reward active →
        ∃ coefficients : QuittingTrapChargeCoefficients nearby active,
          (∑ player ∈ active, nearby (quittingSingletonTerminal player) player) +
            (active.card : ℝ) * bound < coefficients.threshold := by
    rw [Filter.eventually_all]
    intro active
    by_cases htrap : IsQuittingPremiumTrap reward active
    · obtain ⟨coefficients, hcoefficients, hmargin⟩ := hstrict active htrap
      have hcontinuous : Continuous
          (fun nearby : {S : Finset ι // S.Nonempty} → Payoff ι =>
            (∑ player ∈ active, nearby (quittingSingletonTerminal player) player) +
              (active.card : ℝ) * bound) := by fun_prop
      filter_upwards [eventually_strict_coefficient_tests reward active coefficients hcoefficients,
        hcontinuous.continuousAt.eventually_lt_const hmargin] with nearby hnear hmargin _
      let other : QuittingTrapChargeCoefficients nearby active := {
        delta := coefficients.delta
        tau := coefficients.tau
        gap := coefficients.gap
        loss := coefficients.loss
        delta_pos := coefficients.delta_pos
        tau_pos := coefficients.tau_pos
        gap_pos := coefficients.gap_pos
        loss_pos := coefficients.loss_pos
        card_ge_three := coefficients.card_ge_three
        singleton := fun coalition hne hproper hcard =>
          ⟨((hnear ⟨coalition, hne⟩ hproper).1 hcard).1.le,
            ((hnear ⟨coalition, hne⟩ hproper).1 hcard).2.le⟩
        middle := fun coalition hne hproper hlow hhigh =>
          ⟨((hnear ⟨coalition, hne⟩ hproper).2.1 hlow hhigh).1.le,
            ((hnear ⟨coalition, hne⟩ hproper).2.1 hlow hhigh).2.le⟩
        penultimate := fun coalition hne hproper hcard =>
          ⟨((hnear ⟨coalition, hne⟩ hproper).2.2 hcard).1.le,
            ((hnear ⟨coalition, hne⟩ hproper).2.2 hcard).2.le⟩ }
      exact ⟨other, hmargin⟩
    · exact Filter.Eventually.of_forall fun _ h => False.elim (htrap h)
  filter_upwards [htests,
    eventually_premiumTraps_iff_of_nonsingleton_gaps_ne_zero reward hgaps]
    with nearby hnear htraps active htrap
  exact hnear active ((htraps active).mp htrap)

omit [DecidableEq ι] in
theorem eventually_reward_abs_lt_of_strict_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (hbound : ∀ terminal player, |reward terminal player| < bound) :
    ∀ᶠ nearby in 𝓝 reward, ∀ terminal player, |nearby terminal player| < bound := by
  rw [Filter.eventually_all]
  intro terminal
  rw [Filter.eventually_all]
  intro player
  have hcontinuous : Continuous
      (fun nearby : {S : Finset ι // S.Nonempty} → Payoff ι => |nearby terminal player|) :=
    ((continuous_apply player).comp (continuous_apply terminal)).abs
  exact hcontinuous.continuousAt.eventually_lt_const (hbound terminal player)

end GameTheory
