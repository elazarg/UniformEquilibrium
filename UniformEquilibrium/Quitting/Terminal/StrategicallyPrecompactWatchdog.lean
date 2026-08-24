/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.FiniteIndependentMixture
import UniformEquilibrium.Quitting.Paths.FiniteStoppingLawMixture
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Strategically precompact watchdog classes

Finite mixtures of complete quitting strategies are realized by ordinary
behavioral hazards.  Nash's theorem on finite menus therefore supplies a
profile safe against every strategy in those menus.  A finite strategic net
extends this safety to any strategically totally bounded family.

The strategy space and every deviation below are the unrestricted ordinary
behavioral ones.  Total boundedness is measured by uniform terminal-payoff
closeness against every behavioral opponent profile.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Realize every marginal finite law over complete behavioral strategies by
one ordinary stopping-law mixture behavior. -/
def quittingFiniteMixtureBehaviorProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : (who : ι) →
      FinDist ((quittingGame reward).BehaviorStrategy who)) :
    (quittingGame reward).BehaviorProfile :=
  fun who =>
    quittingFiniteStoppingLawMixtureBehaviorStrategy reward who (laws who)

/-- Independent finite mixing of complete behavioral strategies is realized
exactly by the profile of reconstructed marginal hazards. -/
theorem quittingTerminalPayoff_finiteMixtureBehaviorProfile_eq_expect_pi
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : (who : ι) →
      FinDist ((quittingGame reward).BehaviorStrategy who))
    (observer : ι) :
    quittingTerminalPayoff reward
        (quittingFiniteMixtureBehaviorProfile reward laws) observer =
      (FinDist.pi laws).expect fun profile =>
        quittingTerminalPayoff reward profile observer := by
  change quittingTerminalPayoff reward
      (fun who => quittingFiniteStoppingLawMixtureBehaviorStrategy
        reward who (laws who)) observer = _
  apply FinDist.expect_pi_eq_of_separatelyAffine
    (fun who mixture =>
      quittingFiniteStoppingLawMixtureBehaviorStrategy reward who mixture)
    (fun profile => quittingTerminalPayoff reward profile observer)
    laws
  intro mixer profile mixture
  exact quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect
    reward profile mixer observer mixture

/-- The finite strategic form whose pure strategies are supplied behavioral
menus and whose outcome records the selected pure profile. -/
abbrev quittingBehaviorMenuForm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (menu : (who : ι) → Set ((quittingGame reward).BehaviorStrategy who)) :
    GameForm ι :=
  GameForm.deterministic
    { Strategy := fun who => {strategy // strategy ∈ menu who}
      Outcome := (who : ι) → {strategy // strategy ∈ menu who} }
    id

/-- Utility of a pure finite-menu profile is its original quitting-game
terminal payoff. -/
def quittingBehaviorMenuUtility
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (menu : (who : ι) → Set ((quittingGame reward).BehaviorStrategy who)) :
    (quittingBehaviorMenuForm reward menu).sig.Outcome → ι → ℝ :=
  fun profile observer =>
    quittingTerminalPayoff reward (fun who => (profile who).1) observer

omit [DecidableEq ι] in
/-- Expected utility in the mixed finite-menu game is expectation over the
independent law of the underlying quitting strategies. -/
theorem expectedUtility_quittingBehaviorMenu_mixed_eq_expect_pi
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (menu : (who : ι) → Set ((quittingGame reward).BehaviorStrategy who))
    (mixed : Profile (quittingBehaviorMenuForm reward menu).sig.mixed)
    (observer : ι) :
    expectedUtility (quittingBehaviorMenuUtility reward menu) observer
        ((quittingBehaviorMenuForm reward menu).mixed.play mixed) =
      (FinDist.pi (fun who => (mixed who).map Subtype.val)).expect
        fun profile => quittingTerminalPayoff reward profile observer := by
  rw [GameForm.mixed_play, expectedUtility_bind]
  simp only [expectedUtility_pure]
  rw [FinDist.pi_map, FinDist.expect_map]
  rfl

/-- **Finite-watchdog impossibility.** Every player-dependent finite nonempty
menu of complete behavioral deviations has one ordinary behavioral profile
safe against every strategy in every menu. -/
theorem exists_quittingBehaviorProfile_forall_mem_finiteMenu_payoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (menu : (who : ι) → Set ((quittingGame reward).BehaviorStrategy who))
    (hfinite : ∀ who, (menu who).Finite)
    (hnonempty : ∀ who, (menu who).Nonempty) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      ∀ who strategy, strategy ∈ menu who →
        quittingTerminalPayoff reward
            (Function.update profile who strategy) who ≤
          quittingTerminalPayoff reward profile who := by
  letI : ∀ who,
      Fintype ((quittingBehaviorMenuForm reward menu).sig.Strategy who) :=
    fun who => (hfinite who).fintype
  letI : ∀ who,
      Nonempty ((quittingBehaviorMenuForm reward menu).sig.Strategy who) :=
    fun who => (hnonempty who).to_subtype
  obtain ⟨mixed, hnash⟩ := exists_isNash_mixed
    (F := quittingBehaviorMenuForm reward menu)
    (quittingBehaviorMenuUtility reward menu)
  let laws : (who : ι) →
      FinDist ((quittingGame reward).BehaviorStrategy who) :=
    fun who => (mixed who).map Subtype.val
  let profile := quittingFiniteMixtureBehaviorProfile reward laws
  refine ⟨profile, fun who strategy hstrategy => ?_⟩
  let action : {strategy // strategy ∈ menu who} := ⟨strategy, hstrategy⟩
  have hnashPure := (isNash_mixed_iff mixed).1 hnash who action
  have hrhs :
      expectedUtility (quittingBehaviorMenuUtility reward menu) who
          ((quittingBehaviorMenuForm reward menu).mixed.play mixed) =
        quittingTerminalPayoff reward profile who := by
    rw [quittingTerminalPayoff_finiteMixtureBehaviorProfile_eq_expect_pi]
    simpa only [laws] using
      expectedUtility_quittingBehaviorMenu_mixed_eq_expect_pi
        reward menu mixed who
  let updatedMixed := Profile.update mixed who (FinDist.pure action)
  let updatedLaws : (player : ι) →
      FinDist ((quittingGame reward).BehaviorStrategy player) :=
    fun player => (updatedMixed player).map Subtype.val
  have hpureAction :
      (FinDist.pure action).map Subtype.val = FinDist.pure strategy := by
    rw [FinDist.map_pure]
  have hlhs :
      expectedUtility (quittingBehaviorMenuUtility reward menu) who
          ((quittingBehaviorMenuForm reward menu).mixed.play updatedMixed) =
        quittingTerminalPayoff reward
          (Function.update profile who strategy) who := by
    have hproduct :=
      quittingTerminalPayoff_finiteMixtureBehaviorProfile_eq_expect_pi
        reward updatedLaws who
    have hprofileUpdate :
        quittingFiniteMixtureBehaviorProfile reward updatedLaws =
          Function.update profile who
            (quittingFiniteStoppingLawMixtureBehaviorStrategy reward who
              (FinDist.pure strategy)) := by
      funext player
      by_cases hp : player = who
      · subst player
        change quittingFiniteStoppingLawMixtureBehaviorStrategy reward who
            ((Profile.update mixed who (FinDist.pure action) who).map
              Subtype.val) = _
        rw [Profile.update_same, hpureAction, Function.update_self]
      · simp [updatedLaws, updatedMixed, laws, profile,
          quittingFiniteMixtureBehaviorProfile, hp]
    have hpure :=
      quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect
        reward profile who who (FinDist.pure strategy)
    simp only [FinDist.expect_pure] at hpure
    rw [hprofileUpdate, hpure] at hproduct
    calc
      expectedUtility (quittingBehaviorMenuUtility reward menu) who
          ((quittingBehaviorMenuForm reward menu).mixed.play updatedMixed) =
          (FinDist.pi updatedLaws).expect fun candidate =>
            quittingTerminalPayoff reward candidate who := by
        simpa only [updatedLaws] using
          expectedUtility_quittingBehaviorMenu_mixed_eq_expect_pi
            reward menu updatedMixed who
      _ = quittingTerminalPayoff reward
          (Function.update profile who strategy) who := hproduct.symm
  rw [hlhs, hrhs] at hnashPure
  exact hnashPure

/-- Uniform strategic payoff closeness of two deviations for one player. -/
def QuittingStrategicallyWithin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (error : ℝ)
    (first second : (quittingGame reward).BehaviorStrategy who) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    |quittingTerminalPayoff reward
          (Function.update profile who first) who -
        quittingTerminalPayoff reward
          (Function.update profile who second) who| < error

/-- Total boundedness in the strategic payoff pseudometric, stated directly
by finite nets whose centers remain inside the family. -/
def IsQuittingStrategicallyTotallyBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι)
    (family : Set ((quittingGame reward).BehaviorStrategy who)) : Prop :=
  ∀ error : ℝ, 0 < error →
    ∃ net : Set ((quittingGame reward).BehaviorStrategy who),
      net.Finite ∧ net ⊆ family ∧
        ∀ strategy ∈ family, ∃ center ∈ net,
          QuittingStrategicallyWithin reward who error strategy center

/-- **Precompact-watchdog impossibility.** Strategically totally bounded
nonempty families cannot force a positive gap: at every positive accuracy one
ordinary behavioral profile is safe against every member of every family. -/
theorem exists_quittingBehaviorProfile_forall_mem_totallyBounded_payoff_le_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : (who : ι) →
      Set ((quittingGame reward).BehaviorStrategy who))
    (hnonempty : ∀ who, (family who).Nonempty)
    (htotallyBounded : ∀ who,
      IsQuittingStrategicallyTotallyBounded reward who (family who))
    {error : ℝ} (herror : 0 < error) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      ∀ who strategy, strategy ∈ family who →
        quittingTerminalPayoff reward
            (Function.update profile who strategy) who ≤
          quittingTerminalPayoff reward profile who + error := by
  choose net hnetFinite hnetSubset hnetCover using fun who =>
    htotallyBounded who error herror
  have hnetNonempty : ∀ who, (net who).Nonempty := by
    intro who
    obtain ⟨strategy, hstrategy⟩ := hnonempty who
    obtain ⟨center, hcenter, -⟩ := hnetCover who strategy hstrategy
    exact ⟨center, hcenter⟩
  obtain ⟨profile, hsafe⟩ :=
    exists_quittingBehaviorProfile_forall_mem_finiteMenu_payoff_le
      reward net hnetFinite hnetNonempty
  refine ⟨profile, fun who strategy hstrategy => ?_⟩
  obtain ⟨center, hcenter, hclose⟩ :=
    hnetCover who strategy hstrategy
  have hcenterSafe := hsafe who center hcenter
  have hdistance := hclose profile
  rw [abs_lt] at hdistance
  linarith

/-- Pointwise unrestricted best-response completeness of a deviation family.
This epsilon-density form is equivalent to equality of the two best-response
suprema and avoids any assertion that a supremum is attained. -/
def IsQuittingBestResponseComplete
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι)
    (family : Set ((quittingGame reward).BehaviorStrategy who)) : Prop :=
  ∀ profile (deviation : (quittingGame reward).BehaviorStrategy who)
      (error : ℝ), 0 < error →
    ∃ reply ∈ family,
      quittingTerminalPayoff reward
          (Function.update profile who deviation) who ≤
        quittingTerminalPayoff reward
            (Function.update profile who reply) who + error

/-- Complete strategically precompact reply classes give unrestricted
terminal approximate Nash profiles at every positive error. -/
theorem exists_terminalNash_of_complete_strategicallyTotallyBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : (who : ι) →
      Set ((quittingGame reward).BehaviorStrategy who))
    (hnonempty : ∀ who, (family who).Nonempty)
    (htotallyBounded : ∀ who,
      IsQuittingStrategicallyTotallyBounded reward who (family who))
    (hcomplete : ∀ who,
      IsQuittingBestResponseComplete reward who (family who))
    {error : ℝ} (herror : 0 < error) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) error profile := by
  have hhalf : 0 < error / 2 := by linarith
  obtain ⟨profile, hsafe⟩ :=
    exists_quittingBehaviorProfile_forall_mem_totallyBounded_payoff_le_add
      reward family hnonempty htotallyBounded hhalf
  refine ⟨profile, fun who deviation => ?_⟩
  obtain ⟨reply, hreply, happrox⟩ :=
    hcomplete who profile deviation (error / 2) hhalf
  have hsafeReply := hsafe who reply hreply
  linarith

/-- **Complete-precompact-class consumer.** If unrestricted best responses are
captured by strategically totally bounded families, then the quitting game
has a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_complete_strategicallyTotallyBounded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (family : (who : ι) →
      Set ((quittingGame reward).BehaviorStrategy who))
    (hnonempty : ∀ who, (family who).Nonempty)
    (htotallyBounded : ∀ who,
      IsQuittingStrategicallyTotallyBounded reward who (family who))
    (hcomplete : ∀ who,
      IsQuittingBestResponseComplete reward who (family who)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro error herror
  exact exists_terminalNash_of_complete_strategicallyTotallyBounded
    reward family hnonempty htotallyBounded hcomplete herror

end GameTheory
