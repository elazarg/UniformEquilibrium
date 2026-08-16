import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Paths.OpponentLiveMass
import UniformEquilibrium.Quitting.Paths.NonSoloMass
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted

/-!
# Proof-mining experiment: closing longer quitting paths

This file demonstrates four kernels suggested by the recent root and live-mass
proofs.

1. Finite hazard mass plus the surviving/no-divergence atom is exactly one,
   and deterministic-anchor first divergence is an exact positive mixture.
2. A local Bellman residual propagates only through opponent survival.  The
   finite recursive telescope is the path version of the sure-`First` proof.
3. Non-solo absorption under a unilateral deviation is an exact Duhamel sum
   on the opponent-only hazard clock and is bounded by that clock's mass.
4. If the opponents absorb when one player always continues, the terminal
   payoff approximation is uniform over every deviation by that player.

The file is intentionally outside the production import root.  It uses only
landed definitions and contains no axioms or placeholders.
-/


noncomputable section

namespace Research.QuittingPathClosure

open GameTheory GameTheory.StochasticGame Filter

/-! ## Abstract survival-weighted Bellman telescope -/

/-- Accumulated local residual over `horizon` stages, with every later
residual discounted by the preceding survival factors. -/
def survivalResidualCost (survival residual : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, horizon + 1 =>
      residual start + survival start *
        survivalResidualCost survival residual (start + 1) horizon

/-- Product of the successive survival factors, in recursive form. -/
def survivalWeight (survival : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | start, horizon + 1 =>
      survival start * survivalWeight survival (start + 1) horizon

/-- Finite hazard mass plus the terminal nondivergence atom is exactly one.
No almost-sure absorption or finite-mean assumption is used. -/
theorem survivalHazardCost_add_terminalWeight
    (survival : ℕ → ℝ) : ∀ start horizon,
    survivalResidualCost survival (fun time => 1 - survival time)
        start horizon +
      survivalWeight survival start horizon = 1 := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simp [survivalResidualCost, survivalWeight]
  | succ horizon ih =>
      simp only [survivalResidualCost, survivalWeight]
      calc
        1 - survival start +
              survival start * survivalResidualCost survival
                (fun time => 1 - survival time) (start + 1) horizon +
              survival start * survivalWeight survival (start + 1) horizon =
            1 - survival start + survival start *
              (survivalResidualCost survival
                  (fun time => 1 - survival time) (start + 1) horizon +
                survivalWeight survival (start + 1) horizon) := by ring
        _ = 1 := by rw [ih (start + 1)]; ring

/-- Equivalently, the finite first-divergence mass is the complement of the
surviving tail mass.  A positive limiting tail should therefore be represented
by an atom at infinity, not discarded by normalization. -/
theorem survivalHazardCost_eq_one_sub_terminalWeight
    (survival : ℕ → ℝ) (start horizon : ℕ) :
    survivalResidualCost survival (fun time => 1 - survival time)
        start horizon =
      1 - survivalWeight survival start horizon := by
  linarith [survivalHazardCost_add_terminalWeight survival start horizon]

/-- Finite anchored first-divergence disintegration.  At each stage the path
either diverges and receives `divergenceValue`, or survives to the next stage;
after `horizon` survivals it receives the supplied tail value. -/
def anchoredFirstDivergenceValue
    (survival divergenceValue tailValue : ℕ → ℝ) : ℕ → ℕ → ℝ
  | start, 0 => tailValue start
  | start, horizon + 1 =>
      (1 - survival start) * divergenceValue start +
        survival start * anchoredFirstDivergenceValue survival
          divergenceValue tailValue (start + 1) horizon

/-- The anchored disintegration is exactly hazard-weighted divergence payoff
plus the terminal nondivergence atom. -/
theorem anchoredFirstDivergenceValue_eq_cost_add_tail
    (survival divergenceValue tailValue : ℕ → ℝ) :
    ∀ start horizon,
      anchoredFirstDivergenceValue survival divergenceValue tailValue
          start horizon =
        survivalResidualCost survival
            (fun time => (1 - survival time) * divergenceValue time)
            start horizon +
          survivalWeight survival start horizon *
            tailValue (start + horizon) := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simp [anchoredFirstDivergenceValue, survivalResidualCost,
      survivalWeight]
  | succ horizon ih =>
      simp only [anchoredFirstDivergenceValue, survivalResidualCost,
        survivalWeight]
      rw [ih (start + 1)]
      rw [show (start + 1) + horizon = start + (horizon + 1) by omega]
      ring

/-- The first-divergence weights preserve constants exactly.  This is the
finite positive-mixture normalization behind pure quit-time reduction on a
deterministic live line. -/
theorem anchoredFirstDivergenceValue_const
    (survival : ℕ → ℝ) (constant : ℝ) : ∀ start horizon,
    anchoredFirstDivergenceValue survival (fun _ => constant)
      (fun _ => constant) start horizon = constant := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simp [anchoredFirstDivergenceValue]
  | succ horizon ih =>
      simp only [anchoredFirstDivergenceValue, ih (start + 1)]
      ring

/-- With survival factors in `[0,1]`, anchored first-divergence
disintegration is a positive mixture: a common interval containing every
divergence and tail value also contains the disintegrated value. -/
theorem anchoredFirstDivergenceValue_mem_interval
    (survival divergenceValue tailValue : ℕ → ℝ)
    (lower upper : ℝ)
    (hsurvival_nonneg : ∀ time, 0 ≤ survival time)
    (hsurvival_le_one : ∀ time, survival time ≤ 1)
    (hdivergence : ∀ time,
      lower ≤ divergenceValue time ∧ divergenceValue time ≤ upper)
    (htail : ∀ time,
      lower ≤ tailValue time ∧ tailValue time ≤ upper) :
    ∀ start horizon,
      lower ≤ anchoredFirstDivergenceValue survival divergenceValue
          tailValue start horizon ∧
        anchoredFirstDivergenceValue survival divergenceValue
          tailValue start horizon ≤ upper := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simpa [anchoredFirstDivergenceValue] using htail start
  | succ horizon ih =>
      have hhazard : 0 ≤ 1 - survival start :=
        sub_nonneg.mpr (hsurvival_le_one start)
      have hnext := ih (start + 1)
      have hdiv := hdivergence start
      have hdivLower :=
        mul_le_mul_of_nonneg_left hdiv.1 hhazard
      have hdivUpper :=
        mul_le_mul_of_nonneg_left hdiv.2 hhazard
      have hnextLower :=
        mul_le_mul_of_nonneg_left hnext.1 (hsurvival_nonneg start)
      have hnextUpper :=
        mul_le_mul_of_nonneg_left hnext.2 (hsurvival_nonneg start)
      simp only [anchoredFirstDivergenceValue]
      constructor <;> nlinarith

/-- An ordinary normalized direction erases a second-order hazard.  For
hazards `(scale, scale²)`, the second coordinate's normalized share is at most
`scale`; retaining its order therefore needs an iterated/tangent mark rather
than one ordinary simplex-valued Young measure. -/
theorem secondOrderHazard_normalizedShare_le_scale
    {scale : ℝ} (hscale : 0 < scale) :
    scale ^ 2 / (scale + scale ^ 2) ≤ scale := by
  have hden : 0 < 1 + scale := by linarith
  have hrewrite :
      scale ^ 2 / (scale + scale ^ 2) = scale / (1 + scale) := by
    field_simp
  rw [hrewrite]
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg scale]

/-- Iterating a one-step Bellman residual closes every finite path. -/
theorem bellmanResidual_le_cost_add_weighted_tail
    (survival residual regret : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hstep : ∀ time,
      regret time ≤ residual time + survival time * regret (time + 1)) :
    ∀ start horizon,
      regret start ≤
        survivalResidualCost survival residual start horizon +
          survivalWeight survival start horizon * regret (start + horizon) := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simp [survivalResidualCost, survivalWeight]
  | succ horizon ih =>
      calc
        regret start ≤
            residual start + survival start * regret (start + 1) :=
          hstep start
        _ ≤ residual start + survival start *
              (survivalResidualCost survival residual (start + 1) horizon +
                survivalWeight survival (start + 1) horizon *
                  regret ((start + 1) + horizon)) := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left (ih (start + 1))
                (hsurvival start)) _
        _ = survivalResidualCost survival residual start (horizon + 1) +
              survivalWeight survival start (horizon + 1) *
                regret (start + (horizon + 1)) := by
            simp only [survivalResidualCost, survivalWeight]
            rw [show (start + 1) + horizon = start + (horizon + 1) by omega]
            ring

/-- Nonnegative one-step survival factors have a nonnegative finite survival
weight. -/
theorem survivalWeight_nonneg
    (survival : ℕ → ℝ) (hsurvival : ∀ time, 0 ≤ survival time) :
    ∀ start horizon, 0 ≤ survivalWeight survival start horizon := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simp [survivalWeight]
  | succ horizon ih =>
      simp only [survivalWeight]
      exact mul_nonneg (hsurvival start) (ih (start + 1))

/-- Residuals billed in proportion to the current absorption hazard telescope
to `error * (1 - surviving weight)` instead of accumulating once per stage. -/
theorem survivalResidualCost_le_error_mul_one_sub_weight
    (survival residual : ℕ → ℝ) (error : ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hresidual : ∀ time,
      residual time ≤ error * (1 - survival time)) :
    ∀ start horizon,
      survivalResidualCost survival residual start horizon ≤
        error * (1 - survivalWeight survival start horizon) := by
  intro start horizon
  induction horizon generalizing start with
  | zero => simp [survivalResidualCost, survivalWeight]
  | succ horizon ih =>
      calc
        survivalResidualCost survival residual start (horizon + 1) =
            residual start + survival start *
              survivalResidualCost survival residual (start + 1) horizon := rfl
        _ ≤ error * (1 - survival start) + survival start *
              (error * (1 -
                survivalWeight survival (start + 1) horizon)) := by
            exact add_le_add (hresidual start)
              (mul_le_mul_of_nonneg_left (ih (start + 1))
                (hsurvival start))
        _ = error * (1 - survivalWeight survival start (horizon + 1)) := by
            simp only [survivalWeight]
            ring

/-- Hazard-scaled local regret plus a dead surviving tail costs at most one
copy of the error budget over an arbitrarily long finite path. -/
theorem bellmanResidual_le_error_of_hazard_scaled_residual
    (survival residual regret : ℕ → ℝ) (error : ℝ)
    (herror : 0 ≤ error)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hresidual : ∀ time,
      residual time ≤ error * (1 - survival time))
    (hstep : ∀ time,
      regret time ≤ residual time + survival time * regret (time + 1))
    {horizon : ℕ}
    (htail : survivalWeight survival 0 horizon * regret horizon ≤ 0) :
    regret 0 ≤ error := by
  have hcostRaw := survivalResidualCost_le_error_mul_one_sub_weight
    survival residual error hsurvival hresidual 0 horizon
  have hweight := survivalWeight_nonneg survival hsurvival 0 horizon
  have hcost : survivalResidualCost survival residual 0 horizon ≤ error := by
    calc
      survivalResidualCost survival residual 0 horizon ≤
          error * (1 - survivalWeight survival 0 horizon) := hcostRaw
      _ ≤ error := by nlinarith [mul_nonneg herror hweight]
  have hiterate := bellmanResidual_le_cost_add_weighted_tail
    survival residual regret hsurvival hstep 0 horizon
  have hiterate' :
      regret 0 ≤ survivalResidualCost survival residual 0 horizon +
        survivalWeight survival 0 horizon * regret horizon := by
    simpa using hiterate
  linarith

/-- If the accumulated local bill is at most `error` and the surviving tail
is nonpositive, the root regret is at most `error`. -/
theorem bellmanResidual_le_of_cost_le_of_tail_nonpos
    (survival residual regret : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hstep : ∀ time,
      regret time ≤ residual time + survival time * regret (time + 1))
    {horizon : ℕ} {error : ℝ}
    (hcost : survivalResidualCost survival residual 0 horizon ≤ error)
    (htail : survivalWeight survival 0 horizon * regret horizon ≤ 0) :
    regret 0 ≤ error := by
  have hiterate := bellmanResidual_le_cost_add_weighted_tail
    survival residual regret hsurvival hstep 0 horizon
  have hclose :
      survivalResidualCost survival residual 0 horizon +
          survivalWeight survival 0 horizon * regret horizon ≤ error := by
    linarith
  have hiterate' :
      regret 0 ≤ survivalResidualCost survival residual 0 horizon +
        survivalWeight survival 0 horizon * regret horizon := by
    simpa using hiterate
  exact hiterate'.trans hclose

/-- Stationary strict survival contraction turns a local Bellman residual
into a global fixed-point bound. -/
theorem stationary_regret_le_residual_div_one_sub_survival
    {survival residual regret : ℝ}
    (hstrict : survival < 1)
    (hstep : regret ≤ residual + survival * regret) :
    regret ≤ residual / (1 - survival) := by
  have hden : 0 < 1 - survival := sub_pos.mpr hstrict
  apply (le_div_iff₀ hden).2
  nlinarith

/-! ## Forward Duhamel telescope for perturbations and edits -/

/-- Product of survival coefficients in forward-recursive form. -/
def forwardSurvivalWeight (survival : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | start, horizon + 1 =>
      survival (start + horizon) *
        forwardSurvivalWeight survival start horizon

/-- Forward accumulation of injected errors.  Each old error is propagated
through every later survival coefficient before the newest injection is
added. -/
def forwardResidualCost (survival residual : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, horizon + 1 =>
      survival (start + horizon) *
          forwardResidualCost survival residual start horizon +
        residual (start + horizon)

/-- Variable-coefficient forward Duhamel inequality.  This is the scalar
kernel shared by live-law perturbations, hybrid edit telescopes, and switched
error recurrences. -/
theorem forwardError_le_weighted_initial_add_cost
    (survival residual error : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hstep : ∀ time,
      error (time + 1) ≤ survival time * error time + residual time) :
    ∀ start horizon,
      error (start + horizon) ≤
        forwardSurvivalWeight survival start horizon * error start +
          forwardResidualCost survival residual start horizon := by
  intro start horizon
  induction horizon with
  | zero => simp [forwardSurvivalWeight, forwardResidualCost]
  | succ horizon ih =>
      calc
        error (start + (horizon + 1)) =
            error ((start + horizon) + 1) :=
          congrArg error (Nat.add_assoc start horizon 1).symm
        _ ≤ survival (start + horizon) * error (start + horizon) +
              residual (start + horizon) := hstep (start + horizon)
        _ ≤ survival (start + horizon) *
              (forwardSurvivalWeight survival start horizon * error start +
                forwardResidualCost survival residual start horizon) +
              residual (start + horizon) := by
            exact add_le_add_left
              (mul_le_mul_of_nonneg_left ih
                (hsurvival (start + horizon))) _
        _ = forwardSurvivalWeight survival start (horizon + 1) *
              error start +
            forwardResidualCost survival residual start (horizon + 1) := by
          simp only [forwardSurvivalWeight, forwardResidualCost]
          ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The opponent hazard clock inside quitting games -/

/-- Non-solo absorption under a unilateral deviation is exactly the Duhamel
sum of deviating live mass against the deviation-invariant opponent hazard.
This is the precise clock identity: it tracks absorption involving an
opponent, not absorption caused by the deviator alone. -/
theorem quittingNonSoloMass_update_eq_opponentHazardSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    ∀ horizon,
      quittingNonSoloMass reward
          (Function.update profile who deviation) who horizon =
        ∑ time ∈ Finset.range horizon,
          quittingLiveMass reward
              (Function.update profile who deviation) time *
            (1 - quittingJointContinueMass reward
              (quittingOpponentOnlyProfile reward profile who) time) := by
  intro horizon
  induction horizon with
  | zero =>
      simp [quittingNonSoloMass, StochasticGame.expectedStateValue,
        quittingNonSoloIndicator, StochasticGame.emptyHist]
  | succ horizon ih =>
      rw [quittingNonSoloMass_update_succ, Finset.sum_range_succ, ih]

/-- The common opponent clock is an envelope, not the deviator's total
absorption clock: absorption involving an opponent is bounded by the loss of
opponent-only live mass.  Solo absorption by the deviator is intentionally
absent from both sides. -/
theorem quittingNonSoloMass_update_le_one_sub_opponentLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    ∀ horizon,
      quittingNonSoloMass reward
          (Function.update profile who deviation) who horizon ≤
        1 - quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) horizon := by
  intro horizon
  induction horizon with
  | zero =>
      simp [quittingNonSoloMass, StochasticGame.expectedStateValue,
        quittingNonSoloIndicator, StochasticGame.emptyHist]
  | succ horizon ih =>
      rw [quittingNonSoloMass_update_succ, quittingLiveMass_succ]
      have hlive := quittingLiveMass_update_le_opponentOnly
        reward profile who deviation horizon
      have hhazard :
          0 ≤ 1 - quittingJointContinueMass reward
            (quittingOpponentOnlyProfile reward profile who) horizon :=
        sub_nonneg.mpr (quittingJointContinueMass_le_one reward
          (quittingOpponentOnlyProfile reward profile who) horizon)
      calc
        quittingNonSoloMass reward
              (Function.update profile who deviation) who horizon +
            quittingLiveMass reward
                (Function.update profile who deviation) horizon *
              (1 - quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile who) horizon) ≤
          (1 - quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) horizon) +
            quittingLiveMass reward
                (quittingOpponentOnlyProfile reward profile who) horizon *
              (1 - quittingJointContinueMass reward
                (quittingOpponentOnlyProfile reward profile who) horizon) := by
            exact add_le_add ih
              (mul_le_mul_of_nonneg_right hlive hhazard)
        _ = 1 - quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) horizon *
            quittingJointContinueMass reward
              (quittingOpponentOnlyProfile reward profile who) horizon := by
          ring

/-! ## Cesàro averaging of pointwise terminal-tail bounds -/

omit [DecidableEq ι] in
/-- A pointwise bound between expected stage payoff and a target payoff
averages to the corresponding finite-horizon bound. -/
theorem abs_finiteAveragePayoff_sub_target_le
    (G : StochasticGame ι) [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (initial : G.State) (profile : G.BehaviorProfile) (who : ι)
    (target : ℝ) (envelope : ℕ → ℝ) (horizon : ℕ)
    (hpositive : 0 < horizon)
    (henvelope : ∀ time,
      |G.expectedStagePayoff profile initial time who - target| ≤
        envelope time) :
    |G.finiteAveragePayoff initial horizon profile who - target| ≤
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon, envelope time := by
  have hcast : (horizon : ℝ) ≠ 0 := by positivity
  have hrearrange :
      G.finiteAveragePayoff initial horizon profile who - target =
        (horizon : ℝ)⁻¹ *
          ∑ time ∈ Finset.range horizon,
            (G.expectedStagePayoff profile initial time who - target) := by
    rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff,
      Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hrearrange, abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  calc
    |∑ time ∈ Finset.range horizon,
        (G.expectedStagePayoff profile initial time who - target)| ≤
        ∑ time ∈ Finset.range horizon,
          |G.expectedStagePayoff profile initial time who - target| := by
            simpa using Finset.abs_sum_le_sum_abs
              (fun time =>
                G.expectedStagePayoff profile initial time who - target)
              (Finset.range horizon)
    _ ≤ ∑ time ∈ Finset.range horizon, envelope time := by
      exact Finset.sum_le_sum fun time _ => henvelope time

/-- Uniform deviation-tail estimate under opponent-only absorption.

The right side is independent of `deviation`.  If opponent-only live mass
tends to zero, its Cesàro average does too, so this finite bound is the exact
input needed for a deviation-uniform asymptotic estimate. -/
theorem abs_finiteAveragePayoff_update_sub_terminal_le_opponentLiveAverage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) (hpositive : 0 < horizon)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound) :
    |(quittingGame reward).finiteAveragePayoff none horizon
          (Function.update profile who deviation) who -
        quittingTerminalPayoff reward
          (Function.update profile who deviation) who| ≤
      bound * ((horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon,
          quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time) := by
  let deviated := Function.update profile who deviation
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  have havg := abs_finiteAveragePayoff_sub_target_le
    (quittingGame reward) none deviated who
      (quittingTerminalPayoff reward deviated who)
      (fun time => bound * quittingLiveMass reward
        (quittingOpponentOnlyProfile reward profile who) time)
      horizon hpositive (by
        intro time
        rw [abs_sub_comm]
        have htail :=
          abs_quittingTerminalPayoff_sub_expectedStagePayoff_le_liveTail
            reward deviated time who bound hreward
        have hlive := quittingLiveMass_update_le_opponentOnly
          reward profile who deviation time
        have hlimitNonneg := quittingLiveMassLimit_nonneg reward deviated
        have htailLe :
            quittingLiveMass reward deviated time -
                quittingLiveMassLimit reward deviated ≤
              quittingLiveMass reward
                (quittingOpponentOnlyProfile reward profile who) time := by
          linarith
        exact htail.trans
          (mul_le_mul_of_nonneg_left htailLe hbound))
  calc
    |(quittingGame reward).finiteAveragePayoff none horizon deviated who -
        quittingTerminalPayoff reward deviated who| ≤
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        bound * quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time := havg
    _ = bound * ((horizon : ℝ)⁻¹ *
        ∑ time ∈ Finset.range horizon,
          quittingLiveMass reward
            (quittingOpponentOnlyProfile reward profile who) time) := by
      rw [← Finset.mul_sum]
      ring

/-- Almost-sure opponent absorption upgrades the common finite estimate to
absolute terminal-payoff approximation, uniformly over all deviations.  The
production theorem needs only the one-sided half; this experiment records the
stronger symmetric conclusion exposed by the same proof. -/
theorem eventually_abs_finiteAveragePayoff_update_sub_terminal_lt_of_opponentsAbsorb
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ S, |reward S who| ≤ bound)
    (habsorbs : quittingLiveMassLimit reward
      (quittingOpponentOnlyProfile reward profile who) = 0)
    (error : ℝ) (herror : 0 < error) :
    ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
      ∀ deviation : (quittingGame reward).BehaviorStrategy who,
        |(quittingGame reward).finiteAveragePayoff none horizon
              (Function.update profile who deviation) who -
            quittingTerminalPayoff reward
              (Function.update profile who deviation) who| < error := by
  have hscaled : Tendsto (fun horizon : ℕ =>
      bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time))
      atTop (nhds 0) := by
    have hlive := tendsto_quittingLiveMass reward
      (quittingOpponentOnlyProfile reward profile who)
    rw [habsorbs] at hlive
    simpa using Filter.Tendsto.const_mul bound
      hlive.cesaro
  have heventually : ∀ᶠ horizon : ℕ in atTop,
      bound * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        quittingLiveMass reward
          (quittingOpponentOnlyProfile reward profile who) time) < error :=
    (tendsto_order.1 hscaled).2 error herror
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨max 1 threshold, fun horizon hhorizon deviation => ?_⟩
  have hpositive : 0 < horizon :=
    lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (Nat.le_max_left 1 threshold) hhorizon)
  exact lt_of_le_of_lt
    (abs_finiteAveragePayoff_update_sub_terminal_le_opponentLiveAverage
      reward profile who deviation horizon hpositive bound hbound hreward)
    (hthreshold horizon
      (le_trans (Nat.le_max_right 1 threshold) hhorizon))

end Research.QuittingPathClosure
