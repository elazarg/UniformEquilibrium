/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingPayoff

/-!
# Finite witness passports along a stopping-law segment

Every fixed deviation payoff is affine along a complete one-player
stopping-law mixture.  Uniform reward bounds therefore give a common slope
bound.  The best-response supremum inherits the same Lipschitz modulus.

This turns any finite grid of the mixture interval into a finite strategic
passport: choose one approximately optimal pure quit time at every grid
point.  The resulting finite set uniformly approximates the full behavioral
best-response envelope at every mixture weight.  No truncation of the game
horizon and no best-response attainment are assumed.

NOTE: The passport is an epsilon-net statement for the supremum envelope; it
does not supply an exactly active deviation at every weight, nor a globally
flat tangent when the active witness switches. Any tangent-integration use
must separately provide a common endpoint witness (or pay the witness-switch
error).
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.ProbabilityMassFunction
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Prescribed terminal payoff is `2M`-Lipschitz in the complete stopping-law
mixture weight. -/
theorem abs_quittingTerminalPayoff_stoppingLawMixture_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda mu : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              mu hmu0 hmu1)) observer| ≤
      2 * M * |lambda - mu| := by
  have hlambda := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0 hlambda1
  have hmu := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target mu hmu0 hmu1
  let sourcePayoff := quittingTerminalPayoff reward
    (Function.update profile mover source) observer
  let targetPayoff := quittingTerminalPayoff reward
    (Function.update profile mover target) observer
  have hsource : |sourcePayoff| ≤ M := by
    exact abs_quittingTerminalPayoff_le reward _ observer hreward
  have htarget : |targetPayoff| ≤ M := by
    exact abs_quittingTerminalPayoff_le reward _ observer hreward
  have hendpoint : |targetPayoff - sourcePayoff| ≤ 2 * M := by
    calc
      |targetPayoff - sourcePayoff| ≤ |targetPayoff| + |sourcePayoff| :=
        abs_sub _ _
      _ ≤ M + M := add_le_add htarget hsource
      _ = 2 * M := by ring
  have hfactor :
      quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1)) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                mu hmu0 hmu1)) observer =
        (lambda - mu) * (targetPayoff - sourcePayoff) := by
    dsimp only [sourcePayoff, targetPayoff]
    rw [hlambda, hmu]
    ring
  rw [hfactor, abs_mul]
  calc
    |lambda - mu| * |targetPayoff - sourcePayoff| ≤
        |lambda - mu| * (2 * M) :=
      mul_le_mul_of_nonneg_left hendpoint (abs_nonneg _)
    _ = 2 * M * |lambda - mu| := by ring

/-- The payoff of one fixed deviation by an observer different from the
mover has the same `2M` Lipschitz modulus. -/
theorem abs_quittingTerminalPayoff_update_stoppingLawMixture_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda mu : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1)) observer deviation) observer -
        quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                mu hmu0 hmu1)) observer deviation) observer| ≤
      2 * M * |lambda - mu| := by
  have hbound := abs_quittingTerminalPayoff_stoppingLawMixture_sub_le
    reward (Function.update profile observer deviation) mover observer
      source target lambda mu hlambda0 hlambda1 hmu0 hmu1 hreward
  have hlambdaCommute :
      Function.update (Function.update profile observer deviation) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1) =
        Function.update
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer deviation :=
    Function.update_comm hne deviation _ profile
  have hmuCommute :
      Function.update (Function.update profile observer deviation) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            mu hmu0 hmu1) =
        Function.update
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              mu hmu0 hmu1)) observer deviation :=
    Function.update_comm hne deviation _ profile
  rwa [hlambdaCommute, hmuCommute] at hbound

/-- Every player's behavioral best-response envelope is `2M`-Lipschitz along
a complete stopping-law mixture segment.  For the mover it is constant;
for every other player it is the supremum of uniformly `2M`-Lipschitz affine
deviation payoffs. -/
theorem abs_quittingContinuationBestResponseValue_stoppingLawMixture_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda mu : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1)) observer -
        quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              mu hmu0 hmu1)) observer| ≤
      2 * M * |lambda - mu| := by
  by_cases hsame : observer = mover
  · subst observer
    rw [quittingContinuationBestResponseValue_update_self,
      quittingContinuationBestResponseValue_update_self]
    simp only [sub_self, abs_zero]
    positivity
  · let lambdaProfile := Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
        lambda hlambda0 hlambda1)
    let muProfile := Function.update profile mover
      (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
        mu hmu0 hmu1)
    let error := 2 * M * |lambda - mu|
    have hforward : quittingContinuationBestResponseValue reward lambdaProfile observer ≤
        quittingContinuationBestResponseValue reward muProfile observer + error := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact Set.range_nonempty _
      rintro payoff ⟨deviation, rfl⟩
      have hpoint :=
        abs_quittingTerminalPayoff_update_stoppingLawMixture_sub_le
          reward profile mover observer hsame source target deviation lambda mu
            hlambda0 hlambda1 hmu0 hmu1 hreward
      have hdeviation :=
        quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward muProfile observer deviation
      unfold quittingContinuationBestResponseValue at hdeviation
      dsimp only [lambdaProfile, muProfile, error] at hpoint hdeviation ⊢
      linarith [le_abs_self
        (quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  lambda hlambda0 hlambda1)) observer deviation) observer -
          quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  mu hmu0 hmu1)) observer deviation) observer)]
    have hbackward : quittingContinuationBestResponseValue reward muProfile observer ≤
        quittingContinuationBestResponseValue reward lambdaProfile observer + error := by
      unfold quittingContinuationBestResponseValue
      apply csSup_le
      · exact Set.range_nonempty _
      rintro payoff ⟨deviation, rfl⟩
      have hpoint :=
        abs_quittingTerminalPayoff_update_stoppingLawMixture_sub_le
          reward profile mover observer hsame source target deviation mu lambda
            hmu0 hmu1 hlambda0 hlambda1 hreward
      have hdeviation :=
        quittingTerminalPayoff_update_le_continuationBestResponseValue
          reward lambdaProfile observer deviation
      unfold quittingContinuationBestResponseValue at hdeviation
      dsimp only [lambdaProfile, muProfile, error] at hpoint hdeviation ⊢
      rw [abs_sub_comm mu lambda] at hpoint
      linarith [le_abs_self
        (quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  mu hmu0 hmu1)) observer deviation) observer -
          quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  lambda hlambda0 hlambda1)) observer deviation) observer)]
    dsimp only [lambdaProfile, muProfile, error] at hforward hbackward ⊢
    rw [abs_le]
    constructor <;> linarith

/-- The behavioral best-response supremum can be approximated from below by
one pure deterministic quit time (including `Never`).  This combines
approximate attainment of the behavioral supremum with pure-time
extremality; exact attainment is not asserted. -/
theorem exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ choice : Option ℕ,
      quittingContinuationBestResponseValue reward profile observer - epsilon ≤
        quittingTerminalPayoff reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer choice)) observer := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile observer hhalf
  obtain ⟨choice, hchoice⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile observer deviation hhalf
  refine ⟨choice, ?_⟩
  linarith

/-- The unilateral gain from replacing one player's behavior by a pure quit
time.  For a fixed choice this will be one affine chart for semantic debt. -/
def quittingPureTimeDeviationGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) : ℝ :=
  quittingTerminalPayoff reward
      (Function.update profile observer
        (quittingPureTimeBehaviorStrategy reward observer choice)) observer -
    quittingTerminalPayoff reward profile observer

/-- Error of one pure-time affine chart relative to literal semantic debt. -/
def quittingPureTimeDebtAtlasGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) : ℝ :=
  quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer -
    quittingPureTimeDeviationGain reward profile observer choice

/-- Every pure-time deviation-gain chart is exactly affine along a complete
stopping-law mixture of another player. -/
theorem quittingPureTimeDeviationGain_stoppingLawMixture_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (choice : Option ℕ)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingPureTimeDeviationGain reward
        (Function.update profile mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
            lambda hlambda0 hlambda1)) observer choice =
      (1 - lambda) * quittingPureTimeDeviationGain reward
          (Function.update profile mover source) observer choice +
        lambda * quittingPureTimeDeviationGain reward
          (Function.update profile mover target) observer choice := by
  let deviation := quittingPureTimeBehaviorStrategy reward observer choice
  let mixed := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0 hlambda1
  have hdeviation := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile observer deviation) mover observer
      source target lambda hlambda0 hlambda1
  have hprescribed := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0 hlambda1
  have hcommuteSource :
      Function.update (Function.update profile observer deviation) mover source =
        Function.update (Function.update profile mover source) observer deviation :=
    Function.update_comm hne deviation source profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover target =
        Function.update (Function.update profile mover target) observer deviation :=
    Function.update_comm hne deviation target profile
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover mixed =
        Function.update (Function.update profile mover mixed) observer deviation :=
    Function.update_comm hne deviation mixed profile
  dsimp only [mixed] at hcommuteMixed
  rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at hdeviation
  unfold quittingPureTimeDeviationGain
  dsimp only [deviation] at hdeviation
  rw [hdeviation, hprescribed]
  ring

/-- **Finite pure-time witness passport.**

Let `grid` be any finite `rho`-net of the legal mixture interval.  There is a
finite set of pure quit times, one selected near each grid point, such that at
every mixture weight the best payoff among those witnesses is within
`epsilon + 4 M rho` of the full behavioral best-response value.

The conclusion is existential in the nearby grid point rather than phrased
as a finite maximum, so it needs no nonempty-passport convention. -/
theorem exists_finitePureTimeWitnessPassport_stoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (grid : Finset ℝ) (rho epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hgridBounds : ∀ q ∈ grid, 0 ≤ q ∧ q ≤ 1)
    (hcover : ∀ lambda, 0 ≤ lambda → lambda ≤ 1 →
      ∃ q ∈ grid, |lambda - q| ≤ rho)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ passport : Finset (Option ℕ),
      passport.card ≤ grid.card ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
        ∃ choice ∈ passport,
          quittingContinuationBestResponseValue reward
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover
                  source target lambda hlambda0 hlambda1)) observer ≤
            quittingTerminalPayoff reward
                (Function.update
                  (Function.update profile mover
                    (quittingStoppingLawMixtureBehaviorStrategy reward mover
                      source target lambda hlambda0 hlambda1)) observer
                  (quittingPureTimeBehaviorStrategy reward observer choice)) observer +
              epsilon + 4 * M * rho := by
  let chosen : (q : {x // x ∈ grid}) → Option ℕ := fun q =>
    Classical.choose
      (exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub
        reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              q.1 (hgridBounds q.1 q.2).1 (hgridBounds q.1 q.2).2))
          observer epsilon hepsilon)
  let passport : Finset (Option ℕ) := grid.attach.image chosen
  refine ⟨passport, ?_, ?_⟩
  · dsimp only [passport]
    simpa using (Finset.card_image_le : (grid.attach.image chosen).card ≤ grid.attach.card)
  intro lambda hlambda0 hlambda1
  obtain ⟨q, hq, hdistance⟩ := hcover lambda hlambda0 hlambda1
  let qpoint : {x // x ∈ grid} := ⟨q, hq⟩
  let hq0 : 0 ≤ q := (hgridBounds q hq).1
  let hq1 : q ≤ 1 := (hgridBounds q hq).2
  refine ⟨chosen qpoint, ?_, ?_⟩
  · dsimp only [passport]
    apply Finset.mem_image.mpr
    exact ⟨qpoint, Finset.mem_attach grid qpoint, rfl⟩
  · have hchosen := Classical.choose_spec
        (exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub
          reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                q (hgridBounds q hq).1 (hgridBounds q hq).2))
            observer epsilon hepsilon)
    change quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              q hq0 hq1)) observer - epsilon ≤
        quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                q hq0 hq1)) observer
            (quittingPureTimeBehaviorStrategy reward observer (chosen qpoint))) observer
      at hchosen
    have henvelope :=
      abs_quittingContinuationBestResponseValue_stoppingLawMixture_sub_le
        reward profile mover observer source target lambda q
          hlambda0 hlambda1 hq0 hq1 hM hreward
    have hwitness :=
      abs_quittingTerminalPayoff_update_stoppingLawMixture_sub_le
        reward profile mover observer hne source target
          (quittingPureTimeBehaviorStrategy reward observer (chosen qpoint))
          lambda q hlambda0 hlambda1 hq0 hq1 hreward
    have hscale : 2 * M * |lambda - q| ≤ 2 * M * rho := by
      exact mul_le_mul_of_nonneg_left hdistance (by positivity)
    have henvelopeMove :
        quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1)) observer ≤
          quittingContinuationBestResponseValue reward
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  q hq0 hq1)) observer + 2 * M * rho := by
      linarith [le_abs_self
        (quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                lambda hlambda0 hlambda1)) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                q hq0 hq1)) observer)]
    have hwitnessMove :
        quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  q hq0 hq1)) observer
              (quittingPureTimeBehaviorStrategy reward observer
                (chosen qpoint))) observer ≤
          quittingTerminalPayoff reward
              (Function.update
                (Function.update profile mover
                  (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                    lambda hlambda0 hlambda1)) observer
                (quittingPureTimeBehaviorStrategy reward observer
                  (chosen qpoint))) observer + 2 * M * rho := by
      linarith [neg_le_abs
        (quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  lambda hlambda0 hlambda1)) observer
              (quittingPureTimeBehaviorStrategy reward observer
                (chosen qpoint))) observer -
          quittingTerminalPayoff reward
            (Function.update
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
                  q hq0 hq1)) observer
              (quittingPureTimeBehaviorStrategy reward observer
                (chosen qpoint))) observer)]
    nlinarith

/-! ## A canonical finite grid -/

/-- The uniform grid `{0, 1/N, ..., N/N}` on the unit interval. -/
def quittingStoppingLawMixtureUnitGrid (N : ℕ) : Finset ℝ :=
  (Finset.range (N + 1)).image fun k : ℕ => (k : ℝ) / (N : ℝ)

/-- Every point of the positive-denominator uniform grid lies in `[0,1]`. -/
theorem quittingStoppingLawMixtureUnitGrid_mem_bounds
    (N : ℕ) (hN : 0 < N) {q : ℝ}
    (hq : q ∈ quittingStoppingLawMixtureUnitGrid N) :
    0 ≤ q ∧ q ≤ 1 := by
  rw [quittingStoppingLawMixtureUnitGrid, Finset.mem_image] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  have hkN : k ≤ N := Nat.lt_succ_iff.mp (by simpa using hk)
  constructor
  · positivity
  · exact (div_le_one (by exact_mod_cast hN)).2 (by exact_mod_cast hkN)

/-- The uniform `N`-grid has at most `N+1` points. -/
theorem quittingStoppingLawMixtureUnitGrid_card_le (N : ℕ) :
    (quittingStoppingLawMixtureUnitGrid N).card ≤ N + 1 := by
  unfold quittingStoppingLawMixtureUnitGrid
  simpa using (Finset.card_image_le :
    ((Finset.range (N + 1)).image fun k : ℕ => (k : ℝ) / (N : ℝ)).card ≤
      (Finset.range (N + 1)).card)

/-- The positive-denominator uniform grid is a `1/N`-net of `[0,1]`. -/
theorem quittingStoppingLawMixtureUnitGrid_cover
    (N : ℕ) (hN : 0 < N) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    ∃ q ∈ quittingStoppingLawMixtureUnitGrid N,
      |lambda - q| ≤ 1 / (N : ℝ) := by
  let k : ℕ := ⌊(N : ℝ) * lambda⌋₊
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hproduct0 : 0 ≤ (N : ℝ) * lambda := mul_nonneg hNreal.le hlambda0
  have hkProduct : (k : ℝ) ≤ (N : ℝ) * lambda := by
    exact Nat.floor_le hproduct0
  have hproductN : (N : ℝ) * lambda ≤ (N : ℝ) := by
    nlinarith
  have hkN : k ≤ N := by
    exact_mod_cast hkProduct.trans hproductN
  let q : ℝ := (k : ℝ) / (N : ℝ)
  refine ⟨q, ?_, ?_⟩
  · unfold quittingStoppingLawMixtureUnitGrid
    apply Finset.mem_image.mpr
    exact ⟨k, by simpa using Nat.lt_succ_of_le hkN, rfl⟩
  · have hqLambda : q ≤ lambda := by
      apply (div_le_iff₀ hNreal).2
      simpa [q, mul_comm] using hkProduct
    have hproductLt : (N : ℝ) * lambda < ((k + 1 : ℕ) : ℝ) := by
      simpa only [k, Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one ((N : ℝ) * lambda)
    have hlambdaLt : lambda < ((k + 1 : ℕ) : ℝ) / (N : ℝ) := by
      apply (lt_div_iff₀ hNreal).2
      simpa [mul_comm] using hproductLt
    have hsplit : ((k + 1 : ℕ) : ℝ) / (N : ℝ) = q + 1 / (N : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one, q]
      ring
    rw [abs_of_nonneg (sub_nonneg.mpr hqLambda)]
    rw [hsplit] at hlambdaLt
    linarith

/-- **Explicit finite passport.**  With an `N`-mesh, at most `N+1` pure
quit times uniformly approximate the full infinite-horizon behavioral
best-response envelope along the entire stopping-law segment, with error
`epsilon + 4M/N`. -/
theorem exists_boundedPureTimeWitnessPassport_stoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (N : ℕ) (hN : 0 < N) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ passport : Finset (Option ℕ),
      passport.card ≤ N + 1 ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
        ∃ choice ∈ passport,
          quittingContinuationBestResponseValue reward
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover
                  source target lambda hlambda0 hlambda1)) observer ≤
            quittingTerminalPayoff reward
                (Function.update
                  (Function.update profile mover
                    (quittingStoppingLawMixtureBehaviorStrategy reward mover
                      source target lambda hlambda0 hlambda1)) observer
                  (quittingPureTimeBehaviorStrategy reward observer choice)) observer +
              epsilon + 4 * M / (N : ℝ) := by
  obtain ⟨passport, hcard, hpassport⟩ :=
    exists_finitePureTimeWitnessPassport_stoppingLawMixture
      reward profile mover observer hne source target
        (quittingStoppingLawMixtureUnitGrid N) (1 / (N : ℝ)) epsilon hepsilon
        (fun _ hq => quittingStoppingLawMixtureUnitGrid_mem_bounds N hN hq)
        (quittingStoppingLawMixtureUnitGrid_cover N hN)
        hM hreward
  refine ⟨passport,
    hcard.trans (quittingStoppingLawMixtureUnitGrid_card_le N), ?_⟩
  intro lambda hlambda0 hlambda1
  obtain ⟨choice, hchoice, hpayoff⟩ := hpassport lambda hlambda0 hlambda1
  refine ⟨choice, hchoice, ?_⟩
  convert hpayoff using 1
  ring

/-- **Accuracy-form finite passport.**  For every target mesh error `delta`,
the full behavioral best-response envelope along a stopping-law segment is
uniformly witnessed, up to `epsilon + delta`, by at most
`floor(4M/delta) + 2` pure quit times.  The bound is independent of the
horizon, the profile, and the two endpoint stopping laws. -/
theorem exists_accuracyPureTimeWitnessPassport_stoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ passport : Finset (Option ℕ),
      passport.card ≤ ⌊4 * M / delta⌋₊ + 2 ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
        ∃ choice ∈ passport,
          quittingContinuationBestResponseValue reward
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover
                  source target lambda hlambda0 hlambda1)) observer ≤
            quittingTerminalPayoff reward
                (Function.update
                  (Function.update profile mover
                    (quittingStoppingLawMixtureBehaviorStrategy reward mover
                      source target lambda hlambda0 hlambda1)) observer
                  (quittingPureTimeBehaviorStrategy reward observer choice)) observer +
              epsilon + delta := by
  let N : ℕ := ⌊4 * M / delta⌋₊ + 1
  have hN : 0 < N := by
    dsimp only [N]
    omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hratioLt : 4 * M / delta < (N : ℝ) := by
    dsimp only [N]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (4 * M / delta)
  have hmesh : 4 * M / (N : ℝ) < delta := by
    have hscaled : 4 * M < (N : ℝ) * delta := by
      have := (div_lt_iff₀ hdelta).mp hratioLt
      nlinarith
    exact (div_lt_iff₀ hNreal).2 (by nlinarith)
  obtain ⟨passport, hcard, hpassport⟩ :=
    exists_boundedPureTimeWitnessPassport_stoppingLawMixture
      reward profile mover observer hne source target N hN epsilon hepsilon hM hreward
  refine ⟨passport, ?_, ?_⟩
  · dsimp only [N] at hcard
    omega
  · intro lambda hlambda0 hlambda1
    obtain ⟨choice, hchoice, hpayoff⟩ := hpassport lambda hlambda0 hlambda1
    refine ⟨choice, hchoice, ?_⟩
    linarith

/-- **Finite affine debt atlas.**  The same bounded passport supplies affine
deviation-gain charts which approximate the observer's actual semantic debt
from below, uniformly over the whole segment.  The gap between semantic debt
and one selected chart lies in `[0, epsilon + delta]`. -/
theorem exists_accuracyPureTimeDebtAtlas_stoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ passport : Finset (Option ℕ),
      passport.card ≤ ⌊4 * M / delta⌋₊ + 2 ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
        ∃ choice ∈ passport,
          0 ≤
              quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward
                    (Function.update profile mover
                      (quittingStoppingLawMixtureBehaviorStrategy reward mover
                        source target lambda hlambda0 hlambda1))) observer -
                quittingPureTimeDeviationGain reward
                  (Function.update profile mover
                    (quittingStoppingLawMixtureBehaviorStrategy reward mover
                      source target lambda hlambda0 hlambda1)) observer choice ∧
          quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward
                    (Function.update profile mover
                      (quittingStoppingLawMixtureBehaviorStrategy reward mover
                        source target lambda hlambda0 hlambda1))) observer -
                quittingPureTimeDeviationGain reward
                  (Function.update profile mover
                    (quittingStoppingLawMixtureBehaviorStrategy reward mover
                      source target lambda hlambda0 hlambda1)) observer choice ≤
            epsilon + delta := by
  obtain ⟨passport, hcard, hpassport⟩ :=
    exists_accuracyPureTimeWitnessPassport_stoppingLawMixture
      reward profile mover observer hne source target delta epsilon
        hdelta hepsilon hM hreward
  refine ⟨passport, hcard, ?_⟩
  intro lambda hlambda0 hlambda1
  obtain ⟨choice, hchoice, hupper⟩ := hpassport lambda hlambda0 hlambda1
  let mixed := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0 hlambda1
  have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (Function.update profile mover mixed) observer
      (quittingPureTimeBehaviorStrategy reward observer choice)
  refine ⟨choice, hchoice, ?_, ?_⟩
  · dsimp only [mixed] at hlower
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      quittingPureTimeDeviationGain
    dsimp only
    linarith
  · unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      quittingPureTimeDeviationGain
    dsimp only
    linarith

/-- **Simultaneous finite affine debt atlas.**  One finite passport is chosen
for every player other than the mover.  All playerwise semantic debts are
then uniformly approximated along the same mixture segment by their
respective affine pure-time charts.  The total number of stored charts is at
most the number of observers times the one-player accuracy bound. -/
theorem exists_accuracyJointPureTimeDebtAtlas_stoppingLawMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (delta epsilon : ℝ) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ passports : {observer : ι // observer ≠ mover} → Finset (Option ℕ),
      (∑ observer, (passports observer).card) ≤
          Fintype.card {observer : ι // observer ≠ mover} *
            (⌊4 * M / delta⌋₊ + 2) ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
        (observer : {observer : ι // observer ≠ mover}),
        ∃ choice ∈ passports observer,
          0 ≤ quittingPureTimeDebtAtlasGap reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                source target lambda hlambda0 hlambda1)) observer.1 choice ∧
          quittingPureTimeDebtAtlasGap reward
              (Function.update profile mover
                (quittingStoppingLawMixtureBehaviorStrategy reward mover
                  source target lambda hlambda0 hlambda1)) observer.1 choice ≤
            epsilon + delta := by
  let witness (observer : {observer : ι // observer ≠ mover}) :=
    exists_accuracyPureTimeDebtAtlas_stoppingLawMixture
      reward profile mover observer.1 observer.2 source target delta epsilon
        hdelta hepsilon hM hreward
  let passports : {observer : ι // observer ≠ mover} → Finset (Option ℕ) :=
    fun observer => Classical.choose (witness observer)
  refine ⟨passports, ?_, ?_⟩
  · calc
      (∑ observer, (passports observer).card) ≤
          ∑ _observer : {observer : ι // observer ≠ mover},
            (⌊4 * M / delta⌋₊ + 2) := by
        apply Finset.sum_le_sum
        intro observer _hobserver
        exact (Classical.choose_spec (witness observer)).1
      _ = Fintype.card {observer : ι // observer ≠ mover} *
          (⌊4 * M / delta⌋₊ + 2) := by simp
  · intro lambda hlambda0 hlambda1 observer
    obtain ⟨choice, hchoice, hlower, hupper⟩ :=
      (Classical.choose_spec (witness observer)).2
        lambda hlambda0 hlambda1
    refine ⟨choice, hchoice, ?_, ?_⟩
    · simpa only [quittingPureTimeDebtAtlasGap] using hlower
    · simpa only [quittingPureTimeDebtAtlasGap] using hupper

end GameTheory
