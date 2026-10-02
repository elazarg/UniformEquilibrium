/-
Tight coordinates price pre-mark opponent absorption.

Along the all-Continue spine of an actual behavior profile, the semantic pair
at each date is the one-root semantic prefix of the next date's pair by the
live root of that date.  Dropping the prefix envelope to its Continue arm and
splitting the opponents' expectation gives a one-step affine floor: the
envelope coordinate at a date is at least the opponents' survival mass times
the next date's envelope coordinate, minus the reward bound times the absorbed
mass.  These affine maps compose, so the floor telescopes over any live word.

A coordinate that is *tight* at the whole profile — its envelope equals the
player's own solo quitting reward — while its post-shift spine tail clears
that solo reward by `gamma`, therefore forces the pre-mark live word to absorb
a fixed fraction of the opponents' joint mass: the surviving product is at
most `2 * M / (2 * M + gamma)`.

The headline statement is the approximate one, with tightness relaxed to a
slack `sigma`: the surviving product is then at most
`(2 * M + sigma) / (2 * M + gamma)`.  This is what a limit-point consumer can
supply, since tightness there holds only up to a vanishing row slack; exact
tightness is the `sigma = 0` case.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Debt.Marked.TimeAdvance
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Stationary.SnellCap

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Naming bridge for the opponent survival mass -/

/-- The repository's two names for the opponents-of-`who` all-Continue mass at
a root denote the same quantity: both unfold to the root's all-continue mass
after forcing `who` to Continue.  Stated so that consumers phrased in either
vocabulary can use the floors below. -/
theorem fable_quittingRootOpponentContinueMass_eq_stationaryFixedOpponents
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentContinueMass root who =
      quittingStationaryFixedOpponentsContinueMass root who := rfl

/-! ## The one-step Continue-arm floor -/

/-- Composition of two affine survival floors.  If `x ↦ -(M(1-a)) + a x`
carries the tail value below `y`, and `x ↦ -(M(1-P)) + P x` carries `y` below
`c`, then the composite floor with mass `P * a` carries the tail below `c`. -/
private theorem fable_affine_survival_compose {M a P x y c : ℝ} (hP : 0 ≤ P)
    (hstep : -(M * (1 - a)) + a * x ≤ y)
    (hprevious : -(M * (1 - P)) + P * y ≤ c) :
    -(M * (1 - P * a)) + P * a * x ≤ c := by
  have hmul : P * (-(M * (1 - a)) + a * x) ≤ P * y :=
    mul_le_mul_of_nonneg_left hstep hP
  linarith

/-- **One-step Continue-arm floor.**  The envelope coordinate of a one-root
semantic prefix is at least the opponents' all-Continue survival mass times the
tail envelope coordinate, minus the reward bound times the absorbed mass.

The envelope coordinate is a maximum over the two pure endpoints; the bound
comes from the Continue arm alone.  That arm splits into the one-stage
absorbing contribution — bounded in absolute value by `M` times the
opponent-absorption mass — plus opponent survival times the updated tail
coordinate, which is exactly `pair.2 who`. -/
theorem fable_semanticPrefix_envelope_ge_opponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    -(M * (1 - quittingStationaryFixedOpponentsContinueMass root who)) +
        quittingStationaryFixedOpponentsContinueMass root who * pair.2 who ≤
      (quittingTerminalSemanticPrefix reward root pair).2 who := by
  have hcontinue : quittingRootContinuePayoff reward
      (Function.update pair.1 who (pair.2 who)) root who =
      quittingRootAbsorbingContribution reward
          (Function.update root who (PMF.pure false)) who +
        quittingStationaryFixedOpponentsContinueMass root who * pair.2 who := by
    have hexpand := quittingRootExpectedPayoff_eq_absorbingContribution_add
      reward (Function.update pair.1 who (pair.2 who))
      (Function.update root who (PMF.pure false)) who
    rw [Function.update_self] at hexpand
    exact hexpand
  have habsorb := abs_quittingRootAbsorbingContribution_le reward
    (Function.update root who (PMF.pure false)) who M hreward
  have hmass : quittingRootAbsorptionMass
      (Function.update root who (PMF.pure false)) =
      1 - quittingStationaryFixedOpponentsContinueMass root who := rfl
  rw [hmass] at habsorb
  have hneg := neg_abs_le (quittingRootAbsorbingContribution reward
    (Function.update root who (PMF.pure false)) who)
  have harm : -(M * (1 - quittingStationaryFixedOpponentsContinueMass root who)) +
      quittingStationaryFixedOpponentsContinueMass root who * pair.2 who ≤
      quittingRootContinuePayoff reward
        (Function.update pair.1 who (pair.2 who)) root who := by
    rw [hcontinue]
    linarith
  have hsnd : (quittingTerminalSemanticPrefix reward root pair).2 who =
      max (quittingRootQuitPayoff reward pair.1 root who)
        (quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who) := rfl
  rw [hsnd]
  exact harm.trans (le_max_right _ _)

/-! ## Telescoping over the live word -/

/-- **Live-word survival floor.**  Iterating the one-step floor along the
all-Continue spine: the envelope coordinate of the whole profile is at least
the product of the opponents' all-Continue masses over the live word
`0, …, m` times the envelope coordinate of the shifted spine, minus the reward
bound times the absorbed mass. -/
theorem fable_envelope_ge_liveWord_opponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (m : ℕ) :
    -(M * (1 - ∏ t ∈ Finset.range (m + 1),
          quittingStationaryFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward profile t) who)) +
        (∏ t ∈ Finset.range (m + 1),
          quittingStationaryFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward profile t) who) *
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (m + 1))).2 who ≤
      (quittingTerminalSemanticPair reward profile).2 who := by
  induction m with
  | zero =>
      have hstep := fable_semanticPrefix_envelope_ge_opponentSurvival
        reward hreward (quittingProfileLiveRoot reward profile 0)
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile 1)) who
      rw [← quittingTerminalSemanticPair_spine_eq_prefix reward profile 0] at hstep
      have hword : (∏ t ∈ Finset.range (0 + 1),
          quittingStationaryFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward profile t) who) =
          quittingStationaryFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward profile 0) who := by
        simp
      rw [hword]
      exact hstep
  | succ m ih =>
      have hstep := fable_semanticPrefix_envelope_ge_opponentSurvival
        reward hreward (quittingProfileLiveRoot reward profile (m + 1))
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (m + 1 + 1))) who
      rw [← quittingTerminalSemanticPair_spine_eq_prefix reward profile (m + 1)]
        at hstep
      have hnonneg : (0 : ℝ) ≤ ∏ t ∈ Finset.range (m + 1),
          quittingStationaryFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward profile t) who :=
        Finset.prod_nonneg fun t _ =>
          quittingStationaryFixedOpponentsContinueMass_nonneg _ _
      rw [Finset.prod_range_succ]
      exact fable_affine_survival_compose hnonneg hstep ih

/-! ## The pre-mark absorption floor -/

/-- **Pre-mark absorption floor, approximate form.**  Suppose player `who`'s
best-response envelope at the whole profile exceeds their solo quitting reward
by at most `sigma`, while the envelope of the `m+1`-fold all-Continue spine
shift clears that solo reward by `gamma > 0`.  Then the opponents of `who`
must already have absorbed a fixed fraction of their joint mass over the live
word `0, …, m`: their joint survival product is at most
`(2 * M + sigma) / (2 * M + gamma)`.

This is the form the limit-point consumer needs, where tightness of the
coordinate holds only up to a slack vanishing along the selection.  No sign
condition on `sigma` is required: the rearrangement is a single linear
combination that never reads `sigma`'s sign, so at `sigma < 0` both hypothesis
and conclusion simply strengthen together. -/
theorem fable_nearTight_coordinate_premark_opponentAbsorption_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M gamma sigma : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (m : ℕ) (hgamma : 0 < gamma)
    (hclose : (quittingTerminalSemanticPair reward profile).2 who ≤
      reward (quittingSingletonTerminal who) who + sigma)
    (hmargin : reward (quittingSingletonTerminal who) who + gamma ≤
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (m + 1))).2 who) :
    (∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who) ≤
      (2 * M + sigma) / (2 * M + gamma) := by
  have hsolo : |reward (quittingSingletonTerminal who) who| ≤ M := hreward _ _
  have hM : (0 : ℝ) ≤ M := (abs_nonneg _).trans hsolo
  have hupper : reward (quittingSingletonTerminal who) who ≤ M :=
    (le_abs_self _).trans hsolo
  have hnonneg : (0 : ℝ) ≤ ∏ t ∈ Finset.range (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile t) who :=
    Finset.prod_nonneg fun t _ =>
      quittingStationaryFixedOpponentsContinueMass_nonneg _ _
  have hle_one : (∏ t ∈ Finset.range (m + 1),
      quittingStationaryFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile t) who) ≤ 1 :=
    Finset.prod_le_one
      (fun t _ => quittingStationaryFixedOpponentsContinueMass_nonneg _ _)
      (fun t _ => quittingStationaryFixedOpponentsContinueMass_le_one _ _)
  have htelescope :=
    fable_envelope_ge_liveWord_opponentSurvival reward hreward profile who m
  have hmargin_scaled : (∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who) *
        (reward (quittingSingletonTerminal who) who + gamma) ≤
      (∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who) *
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (m + 1))).2 who :=
    mul_le_mul_of_nonneg_left hmargin hnonneg
  have hslack : (∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who) *
        (M - reward (quittingSingletonTerminal who) who) ≤
      M - reward (quittingSingletonTerminal who) who :=
    mul_le_of_le_one_left (by linarith) hle_one
  have hpositive : (0 : ℝ) < 2 * M + gamma := by linarith
  rw [le_div_iff₀ hpositive]
  linarith

/-- **Pre-mark absorption floor.**  The exact-tightness specialization: when
player `who`'s best-response envelope at the whole profile *equals* their solo
quitting reward, the pre-mark opponent survival product is at most
`2 * M / (2 * M + gamma)`. -/
theorem fable_tight_coordinate_premark_opponentAbsorption_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M gamma : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (m : ℕ) (hgamma : 0 < gamma)
    (htight : reward (quittingSingletonTerminal who) who =
      (quittingTerminalSemanticPair reward profile).2 who)
    (hmargin : reward (quittingSingletonTerminal who) who + gamma ≤
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (m + 1))).2 who) :
    (∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who) ≤
      2 * M / (2 * M + gamma) := by
  have hclose : (quittingTerminalSemanticPair reward profile).2 who ≤
      reward (quittingSingletonTerminal who) who + 0 := by
    rw [add_zero]
    exact htight.ge
  have hgeneral := fable_nearTight_coordinate_premark_opponentAbsorption_floor
    reward hreward profile who m hgamma hclose hmargin
  rwa [add_zero] at hgeneral

end GameTheory
