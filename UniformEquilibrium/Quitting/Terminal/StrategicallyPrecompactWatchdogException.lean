/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.MetricSpace.ProperSpace
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogEscape

/-!
# One arbitrary watchdog range

After every nonexceptional player has been reduced to a finite strategic net,
an arbitrary exceptional family is seen only through a bounded vector of
payoffs on the finite product of those nets.  A finite sup-norm net of these
vectors therefore completes the finite-game construction.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open GameTheory.Math.Probability

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Updating one coordinate after realizing independent finite mixtures is
the expectation of updating that coordinate in every independently drawn
pure profile. -/
theorem quittingTerminalPayoff_update_finiteMixtureBehaviorProfile_eq_expect_pi
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (laws : (who : iota) ->
      FinDist ((quittingGame reward).BehaviorStrategy who))
    (who : iota) (strategy : (quittingGame reward).BehaviorStrategy who)
    (observer : iota) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingFiniteMixtureBehaviorProfile reward laws) who strategy)
        observer =
      (FinDist.pi laws).expect fun profile =>
        quittingTerminalPayoff reward
          (Function.update profile who strategy) observer := by
  let realize := fun player mixture =>
    quittingFiniteStoppingLawMixtureBehaviorStrategy reward player mixture
  change quittingTerminalPayoff reward
      (Function.update (fun player => realize player (laws player)) who strategy)
      observer = _
  apply FinDist.expect_pi_eq_of_separatelyAffine realize
    (fun profile => quittingTerminalPayoff reward
      (Function.update profile who strategy) observer)
    laws
  intro mixer profile mixture
  by_cases hmixer : mixer = who
  · subst mixer
    simp [realize]
  · have haffine :=
      quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect
        reward (Function.update profile who strategy) mixer observer mixture
    simpa only [realize, Function.update_comm hmixer] using haffine

/-- A mixed Nash equilibrium of a finite behavioral menu remains safe after
its independent marginal mixtures are realized as ordinary hazards. -/
theorem quittingFiniteMixtureBehaviorProfile_payoff_le_of_isNash_mixed
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (menu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (mixed : Profile (quittingBehaviorMenuForm reward menu).sig.mixed)
    (hnash : IsNash (quittingBehaviorMenuForm reward menu).mixed
      (euPreference (quittingBehaviorMenuUtility reward menu)) mixed) :
    ∀ who strategy, strategy ∈ menu who ->
      quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteMixtureBehaviorProfile reward
              (fun player => (mixed player).map Subtype.val))
            who strategy) who <=
        quittingTerminalPayoff reward
          (quittingFiniteMixtureBehaviorProfile reward
            (fun player => (mixed player).map Subtype.val)) who := by
  intro who strategy hstrategy
  let laws : (player : iota) ->
      FinDist ((quittingGame reward).BehaviorStrategy player) :=
    fun player => (mixed player).map Subtype.val
  let profile := quittingFiniteMixtureBehaviorProfile reward laws
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
  let updatedLaws : (player : iota) ->
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

/-- Pure opponent profiles in a finite behavioral menu. -/
abbrev QuittingBehaviorOpponentMenuProfile
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (menu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (exception : iota) :=
  (who : {who : iota // who ≠ exception}) ->
    {strategy // strategy ∈ menu who.1}

/-- The exceptional player's payoff vector on one finite menu product.  Its
own menu coordinate is overwritten, so only the opponents matter. -/
def quittingExceptionalEvaluation
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (menu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (exception : iota)
    (strategy : (quittingGame reward).BehaviorStrategy exception) :
    QuittingBehaviorOpponentMenuProfile reward menu exception -> Real :=
  fun profile => quittingTerminalPayoff reward (fun who =>
    if hwho : who = exception then hwho ▸ strategy
    else (profile ⟨who, hwho⟩).1) exception

/-- Every arbitrary exceptional family has a finite payoff-vector net on a
fixed finite menu product. Centers remain inside that family. -/
theorem exists_finite_exceptionalEvaluationNet
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (menu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (exception : iota)
    (hmenuFinite : ∀ who, who ≠ exception -> (menu who).Finite)
    (_hmenuNonempty : ∀ who, who ≠ exception -> (menu who).Nonempty)
    (family : Set ((quittingGame reward).BehaviorStrategy exception))
    (hfamilyNonempty : family.Nonempty)
    {error : Real} (herror : 0 < error) :
    ∃ net : Set ((quittingGame reward).BehaviorStrategy exception),
      net.Finite ∧ net ⊆ family ∧ net.Nonempty ∧
        ∀ strategy ∈ family, ∃ center ∈ net,
          ∀ profile : QuittingBehaviorOpponentMenuProfile reward menu exception,
            |quittingExceptionalEvaluation reward menu exception strategy profile -
                quittingExceptionalEvaluation reward menu exception center profile| <
              error := by
  classical
  letI : ∀ who : {who : iota // who ≠ exception},
      Fintype {strategy // strategy ∈ menu who.1} :=
    fun who => (hmenuFinite who.1 who.2).fintype
  letI : ∀ who : {who : iota // who ≠ exception},
      Nonempty {strategy // strategy ∈ menu who.1} :=
    fun who => (_hmenuNonempty who.1 who.2).to_subtype
  let bound : Real := max 1 (quittingRewardBound reward)
  have hbound : 0 < bound := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let vectors : Set
      (QuittingBehaviorOpponentMenuProfile reward menu exception -> Real) :=
    Metric.closedBall 0 bound
  have hvectorsCompact : IsCompact vectors := isCompact_closedBall 0 bound
  obtain ⟨centers, hcentersFinite, hcentersCover⟩ :=
    (Metric.totallyBounded_iff.mp hvectorsCompact.totallyBounded)
      (error / 2) (by linarith)
  let evaluation := quittingExceptionalEvaluation reward menu exception
  have hevaluationMem : forall strategy,
      evaluation strategy ∈ vectors := by
    intro strategy
    rw [Metric.mem_closedBall, dist_pi_le_iff hbound.le]
    intro profile
    rw [Pi.zero_apply, Real.dist_eq, sub_zero]
    exact (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ exception).trans
      (le_max_right _ _)
  have hcenterExists : ∀ strategy ∈ family,
      ∃ center ∈ centers,
        dist (evaluation strategy) center < error / 2 := by
    intro strategy hstrategy
    have hmem := hcentersCover (hevaluationMem strategy)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hmem
    obtain ⟨center, hcenter, hclose⟩ := hmem
    exact ⟨center, hcenter, hclose⟩
  choose center hcenterMem hcenterClose using hcenterExists
  have hfamilySubtype : Nonempty {strategy // strategy ∈ family} :=
    hfamilyNonempty.to_subtype
  letI : Nonempty {strategy // strategy ∈ family} := hfamilySubtype
  letI : Fintype {point // point ∈ centers} := hcentersFinite.fintype
  let indexedCenter : {strategy // strategy ∈ family} ->
      {point // point ∈ centers} := fun strategy =>
    ⟨center strategy strategy.property, hcenterMem strategy strategy.property⟩
  let representative : {point // point ∈ centers} ->
      {strategy // strategy ∈ family} := Function.invFun indexedCenter
  let net : Set ((quittingGame reward).BehaviorStrategy exception) :=
    Set.range (Subtype.val ∘ representative)
  have hnetFinite : net.Finite := Set.finite_range _
  have hnetSubset : net ⊆ family := by
    rintro strategy ⟨point, rfl⟩
    exact (representative point).property
  have hnetNonempty : net.Nonempty := by
    obtain ⟨strategy, hstrategy⟩ := hfamilyNonempty
    let source : {strategy // strategy ∈ family} := ⟨strategy, hstrategy⟩
    exact ⟨representative (indexedCenter source),
      ⟨indexedCenter source, rfl⟩⟩
  refine ⟨net, hnetFinite, hnetSubset, hnetNonempty,
    fun strategy hstrategy => ?_⟩
  let source : {strategy // strategy ∈ family} := ⟨strategy, hstrategy⟩
  let point := indexedCenter source
  let selected := representative point
  have hpoint : indexedCenter selected = point := by
    dsimp only [selected, representative, point]
    exact Function.invFun_eq ⟨source, rfl⟩
  have hsameCenter : center selected selected.property =
      center strategy hstrategy := Subtype.ext_iff.mp hpoint
  refine ⟨selected, ⟨point, rfl⟩, fun profile => ?_⟩
  have hsourceClose := hcenterClose strategy hstrategy
  have hselectedClose := hcenterClose selected selected.property
  have hsourceCoordinate :=
    (dist_pi_lt_iff (show 0 < error / 2 by linarith)).mp hsourceClose profile
  have hselectedCoordinate :=
    (dist_pi_lt_iff (show 0 < error / 2 by linarith)).mp hselectedClose profile
  rw [hsameCenter] at hselectedCoordinate
  calc
    |evaluation strategy profile - evaluation selected profile| <=
        dist (evaluation strategy profile) (center strategy hstrategy profile) +
          dist (evaluation selected profile) (center strategy hstrategy profile) := by
      rw [← Real.dist_eq]
      exact dist_triangle_right _ _ _
    _ < error / 2 + error / 2 := add_lt_add hsourceCoordinate hselectedCoordinate
    _ = error := by ring

/-- Sup-norm closeness of two exceptional payoff vectors controls their
payoffs against the independently mixed opponents from the same finite
menu. -/
theorem abs_quittingTerminalPayoff_update_finiteMixture_le_of_exceptionalEvaluation
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (menu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (mixed : (who : iota) ->
      FinDist {strategy // strategy ∈ menu who})
    (exception : iota)
    (first second : (quittingGame reward).BehaviorStrategy exception)
    {error : Real}
    (hclose : ∀ opponentProfile :
        QuittingBehaviorOpponentMenuProfile reward menu exception,
      |quittingExceptionalEvaluation reward menu exception first opponentProfile -
          quittingExceptionalEvaluation reward menu exception second opponentProfile| <=
        error) :
    |quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteMixtureBehaviorProfile reward
              (fun who => (mixed who).map Subtype.val)) exception first)
          exception -
        quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteMixtureBehaviorProfile reward
              (fun who => (mixed who).map Subtype.val)) exception second)
          exception| <= error := by
  let laws : (who : iota) ->
      FinDist ((quittingGame reward).BehaviorStrategy who) :=
    fun who => (mixed who).map Subtype.val
  have hfirst :=
    quittingTerminalPayoff_update_finiteMixtureBehaviorProfile_eq_expect_pi
      reward laws exception first exception
  have hsecond :=
    quittingTerminalPayoff_update_finiteMixtureBehaviorProfile_eq_expect_pi
      reward laws exception second exception
  rw [FinDist.pi_map, FinDist.expect_map] at hfirst hsecond
  rw [hfirst, hsecond, ← FinDist.expect_sub]
  apply FinDist.abs_expect_le_of_abs_bound
  intro pureProfile _hpureProfile
  let opponentProfile :
      QuittingBehaviorOpponentMenuProfile reward menu exception :=
    fun who => pureProfile who.1
  have hevaluation (strategy :
      (quittingGame reward).BehaviorStrategy exception) :
      quittingExceptionalEvaluation reward menu exception strategy
          opponentProfile =
        quittingTerminalPayoff reward
          (Function.update (fun who => (pureProfile who).1)
            exception strategy) exception := by
    apply congrArg (fun profile =>
      quittingTerminalPayoff reward profile exception)
    funext who
    by_cases hwho : who = exception
    · subst who
      simp
    · simp [opponentProfile, hwho]
  simpa only [hevaluation] using hclose opponentProfile

/-- **One-exception watchdog impossibility.** One arbitrary nonempty family
is harmless when every other player's family is nonempty and strategically
totally bounded. -/
theorem exists_quittingBehaviorProfile_forall_mem_oneException_payoff_le_add
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (family : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (hnonempty : ∀ who, (family who).Nonempty)
    (exception : iota)
    (htotallyBounded : ∀ who, who ≠ exception ->
      IsQuittingStrategicallyTotallyBounded reward who (family who))
    {error : Real} (herror : 0 < error) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      ∀ who strategy, strategy ∈ family who ->
        quittingTerminalPayoff reward
            (Function.update profile who strategy) who <=
          quittingTerminalPayoff reward profile who + error := by
  classical
  choose ordinaryNet hordinaryFinite hordinarySubset hordinaryCover using
    fun who : {who : iota // who ≠ exception} =>
      htotallyBounded who.1 who.2 error herror
  let fallback : (who : iota) ->
      (quittingGame reward).BehaviorStrategy who :=
    fun who => quittingPureTimeBehaviorStrategy reward who none
  let baseMenu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who) := fun who =>
    if hwho : who = exception then {fallback who}
    else ordinaryNet ⟨who, hwho⟩
  have hbaseFinite : ∀ who, (baseMenu who).Finite := by
    intro who
    by_cases hwho : who = exception
    · simp [baseMenu, hwho]
    · simpa [baseMenu, hwho] using hordinaryFinite ⟨who, hwho⟩
  have hbaseNonempty : ∀ who, (baseMenu who).Nonempty := by
    intro who
    by_cases hwho : who = exception
    · simp [baseMenu, hwho]
    · obtain ⟨strategy, hstrategy⟩ := hnonempty who
      obtain ⟨center, hcenter, _hclose⟩ :=
        hordinaryCover ⟨who, hwho⟩ strategy hstrategy
      exact ⟨center, by simpa [baseMenu, hwho] using hcenter⟩
  obtain ⟨exceptionNet, hexceptionFinite, hexceptionSubset,
      hexceptionNonempty, hexceptionCover⟩ :=
    exists_finite_exceptionalEvaluationNet reward baseMenu exception
      (fun who _hwho => hbaseFinite who)
      (fun who _hwho => hbaseNonempty who)
      (family exception) (hnonempty exception) herror
  let menu : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who) := fun who =>
    if hwho : exception = who then hwho ▸ exceptionNet
    else ordinaryNet ⟨who, Ne.symm hwho⟩
  have hmenuFinite : ∀ who, (menu who).Finite := by
    intro who
    by_cases hwho : exception = who
    · subst who
      simpa [menu] using hexceptionFinite
    · simpa [menu, hwho] using hordinaryFinite ⟨who, Ne.symm hwho⟩
  have hmenuNonempty : ∀ who, (menu who).Nonempty := by
    intro who
    by_cases hwho : exception = who
    · subst who
      simpa [menu] using hexceptionNonempty
    · obtain ⟨strategy, hstrategy⟩ := hnonempty who
      obtain ⟨center, hcenter, _hclose⟩ :=
        hordinaryCover ⟨who, Ne.symm hwho⟩ strategy hstrategy
      exact ⟨center, by simpa [menu, hwho] using hcenter⟩
  letI : ∀ who,
      Fintype ((quittingBehaviorMenuForm reward menu).sig.Strategy who) :=
    fun who => (hmenuFinite who).fintype
  letI : ∀ who,
      Nonempty ((quittingBehaviorMenuForm reward menu).sig.Strategy who) :=
    fun who => (hmenuNonempty who).to_subtype
  obtain ⟨mixed, hnash⟩ := exists_isNash_mixed
    (F := quittingBehaviorMenuForm reward menu)
    (quittingBehaviorMenuUtility reward menu)
  let laws : (who : iota) ->
      FinDist ((quittingGame reward).BehaviorStrategy who) :=
    fun who => (mixed who).map Subtype.val
  let profile := quittingFiniteMixtureBehaviorProfile reward laws
  have hsafe : ∀ who strategy, strategy ∈ menu who ->
      quittingTerminalPayoff reward
          (Function.update profile who strategy) who <=
        quittingTerminalPayoff reward profile who := by
    intro who strategy hstrategy
    exact quittingFiniteMixtureBehaviorProfile_payoff_le_of_isNash_mixed
      reward menu mixed hnash who strategy hstrategy
  refine ⟨profile, fun who strategy hstrategy => ?_⟩
  by_cases hwho : who = exception
  · subst who
    obtain ⟨center, hcenter, hclose⟩ :=
      hexceptionCover strategy hstrategy
    have hcenterMenu : center ∈ menu exception := by
      simpa [menu] using hcenter
    have hcenterSafe := hsafe exception center hcenterMenu
    have hcloseMenu : ∀ opponentProfile :
        QuittingBehaviorOpponentMenuProfile reward menu exception,
        |quittingExceptionalEvaluation reward menu exception strategy
              opponentProfile -
            quittingExceptionalEvaluation reward menu exception center
              opponentProfile| <= error := by
      intro opponentProfile
      let baseOpponentProfile :
          QuittingBehaviorOpponentMenuProfile reward baseMenu exception :=
        fun player => ⟨(opponentProfile player).1, by
          have hplayer : exception ≠ player.1 := Ne.symm player.2
          simpa [baseMenu, menu, player.2, hplayer] using
            (opponentProfile player).2⟩
      have hvector := (hclose baseOpponentProfile).le
      simpa [quittingExceptionalEvaluation, baseOpponentProfile] using hvector
    have hdistance :=
      abs_quittingTerminalPayoff_update_finiteMixture_le_of_exceptionalEvaluation
        reward menu mixed exception strategy center hcloseMenu
    change _ <= quittingTerminalPayoff reward profile exception + error
    rw [abs_le] at hdistance
    linarith
  · obtain ⟨center, hcenter, hclose⟩ :=
      hordinaryCover ⟨who, hwho⟩ strategy hstrategy
    have hcenterMenu : center ∈ menu who := by
      have hexceptionWho : exception ≠ who := Ne.symm hwho
      simpa [menu, hexceptionWho] using hcenter
    have hcenterSafe := hsafe who center hcenterMenu
    have hdistance := hclose profile
    rw [abs_lt] at hdistance
    linarith

/-- Best-response complete reply families which are strategically totally
bounded away from one identity give terminal approximate Nash profiles. -/
theorem exists_terminalNash_of_complete_oneException_strategicallyTotallyBounded
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (family : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (hnonempty : ∀ who, (family who).Nonempty)
    (exception : iota)
    (htotallyBounded : ∀ who, who ≠ exception ->
      IsQuittingStrategicallyTotallyBounded reward who (family who))
    (hcomplete : ∀ who,
      IsQuittingBestResponseComplete reward who (family who))
    {error : Real} (herror : 0 < error) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) error profile := by
  have hhalf : 0 < error / 2 := by linarith
  obtain ⟨profile, hsafe⟩ :=
    exists_quittingBehaviorProfile_forall_mem_oneException_payoff_le_add
      reward family hnonempty exception htotallyBounded hhalf
  refine ⟨profile, fun who deviation => ?_⟩
  obtain ⟨reply, hreply, happrox⟩ :=
    hcomplete who profile deviation (error / 2) hhalf
  have hsafeReply := hsafe who reply hreply
  linarith

/-- Complete reply classes which are strategically totally bounded away from
at most one identity imply a uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_complete_oneException
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (family : (who : iota) ->
      Set ((quittingGame reward).BehaviorStrategy who))
    (hnonempty : ∀ who, (family who).Nonempty)
    (exception : iota)
    (htotallyBounded : ∀ who, who ≠ exception ->
      IsQuittingStrategicallyTotallyBounded reward who (family who))
    (hcomplete : ∀ who,
      IsQuittingBestResponseComplete reward who (family who)) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro error herror
  exact exists_terminalNash_of_complete_oneException_strategicallyTotallyBounded
    reward family hnonempty exception htotallyBounded hcomplete herror

end GameTheory
