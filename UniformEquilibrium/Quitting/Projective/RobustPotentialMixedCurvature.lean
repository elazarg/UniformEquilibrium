import MathUE.Analysis.MixedCurvatureSupBound
import UniformEquilibrium.Quitting.Projective.FinFourAmbientQSimplex
import UniformEquilibrium.Quitting.Projective.RobustPotentialSingletonFaceDrift
import UniformEquilibrium.Quitting.Projective.SingletonBoxTranslation

/-! # Actual robust-potential signed mixed-curvature restrictions

The same real reward table produces its analytic simplex via bare Fin4
no-UE. Its robust relation produces the positive gain. Every full-box
minimum is retained, and compactness produces the off-diagonal maximum.
-/

noncomputable section

namespace GameTheory

open Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
/-- The literal receiver-row normalized matrix in the lower multiplier term. -/
theorem quitting_lowerBoundaryMatrixContribution_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (minimum : Payoff ι)
    (weight : ι → ℝ) (potential : Payoff ι → ℝ) :
    Math.lowerBoundaryMatrixContribution (fun who => quittingSoloReward reward who who)
        minimum (quittingSoloReward reward) weight potential =
      ∑ receiver,
        Math.lowerBoundaryMultiplier (fun who => quittingSoloReward reward who who)
          minimum potential receiver *
          ∑ owner, quittingProjectiveLCPMatrix reward receiver owner * weight owner := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The packet's common width W bounds both reset lengths and every payoff
coefficient, including coefficients at upper-face intersections. -/
theorem quittingSingletonBox_mixedCurvature_width_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (0 < 2 * bound + 1) ∧
    (∀ who, bound + 1 - quittingSoloReward reward who who ≤ 2 * bound + 1) ∧
    (∀ point ∈ quittingSingletonBox reward bound, ∀ owner receiver,
      |point receiver - quittingSoloReward reward owner receiver| ≤ 2 * bound + 1) := by
  classical
  let player : ι := Classical.choice inferInstance
  have hbound : 0 ≤ bound := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal player) player)
  refine ⟨by linarith, ?_, ?_⟩
  · intro who
    have hsolo := neg_le_of_abs_le (hreward (quittingSingletonTerminal who) who)
    change -bound ≤ quittingSoloReward reward who who at hsolo
    linarith
  · intro point hpoint owner receiver
    have hown := abs_le.mp (hreward (quittingSingletonTerminal receiver) receiver)
    have hsolo := abs_le.mp (hreward (quittingSingletonTerminal owner) receiver)
    change -bound ≤ quittingSoloReward reward receiver receiver ∧
      quittingSoloReward reward receiver receiver ≤ bound at hown
    change -bound ≤ quittingSoloReward reward owner receiver ∧
      quittingSoloReward reward owner receiver ≤ bound at hsolo
    exact abs_le.mpr ⟨by linarith [hpoint.1 receiver], by linarith [hpoint.2 receiver]⟩

omit [Nonempty ι] in
/-- The literal actual-box reset identity, including zero-length intervals.
No equilibrium or matrix hypothesis is required for this calculus identity. -/
theorem quittingSingletonBox_coordinatePartial_reset_eq_sub_integral
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (potential : Payoff ι → ℝ) (domain : Set (Payoff ι)) (hopen : IsOpen domain)
    (hbox : quittingSingletonBox reward bound ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (minimum : Payoff ι) (hminimum : minimum ∈ quittingSingletonBox reward bound)
    (owner receiver : ι) :
    Math.coordinatePartial potential
        (Function.update minimum owner (quittingSoloReward reward owner owner)) receiver =
      Math.coordinatePartial potential minimum receiver -
        ∫ value in (quittingSoloReward reward owner owner)..(minimum owner),
          Math.coordinateMixedPartial potential (Function.update minimum owner value)
            owner receiver :=
  Math.coordinatePartial_reset_eq_sub_integral
    (fun who => quittingSoloReward reward who who) (fun _ => bound + 1) minimum potential
    domain hopen hbox hsmooth hminimum owner receiver

/-- Bare actual Fin4 no-UE produces z internally. The signed account holds
for every actual full-box minimum, with the same z, function and reward table.
The final supremum is attained at an internally produced distinct-coordinate
mixed partial. No reward rationality or favorable minimum is an input. -/
theorem quittingRobustPotential_finFour_mixedCurvature_restrictions
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound tolerance : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (htolerance0 : 0 < tolerance) (htolerance1 : tolerance ≤ 1 / 4)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (potential : Payoff (Fin 4) → ℝ) (domain : Set (Payoff (Fin 4)))
    (hopen : IsOpen domain) (hbox : quittingSingletonBox reward bound ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain)
    (hpotential :
      (quittingFloorFreeRobustChargedRelation reward tolerance (bound + 2)).IsPotential
        (fun state => potential state.1)) :
    (0 < (2 * bound + 1) / (2 * bound + 1 - tolerance)) ∧
    ∃ weight : Convexity.StdSimplex ℝ (Fin 4),
      (∀ receiver, 0 < ∑ owner, weight.weights owner *
        quittingProjectiveLCPMatrix reward receiver owner) ∧
      (∀ minimum ∈ quittingSingletonBox reward bound,
        IsMinOn potential (quittingSingletonBox reward bound) minimum →
        (∀ receiver, 0 ≤ Math.lowerBoundaryMultiplier
          (fun who => quittingSoloReward reward who who) minimum potential receiver) ∧
        (2 * bound + 1) / (2 * bound + 1 - tolerance) +
            Math.lowerBoundaryMatrixContribution (fun who => quittingSoloReward reward who who)
              minimum (quittingSoloReward reward) weight.weights potential ≤
          Math.signedMixedCurvatureAccount (fun who => quittingSoloReward reward who who)
            minimum (quittingSoloReward reward) weight.weights potential ∧
        (2 * bound + 1) / (2 * bound + 1 - tolerance) ≤
          (2 * bound + 1) / (2 * bound + 1 - tolerance) +
            Math.lowerBoundaryMatrixContribution (fun who => quittingSoloReward reward who who)
              minimum (quittingSoloReward reward) weight.weights potential) ∧
      ∃ point ∈ quittingSingletonBox reward bound, ∃ owner receiver, owner ≠ receiver ∧
        ((2 * bound + 1) / (2 * bound + 1 - tolerance)) /
            (3 * (2 * bound + 1) ^ 2) ≤
          |Math.coordinateMixedPartial potential point owner receiver| ∧
        Math.boxMixedCurvatureSup potential (quittingSingletonBox reward bound) =
          |Math.coordinateMixedPartial potential point owner receiver| := by
  classical
  let lower := fun who => quittingSoloReward reward who who
  let upper : Payoff (Fin 4) := fun _ => bound + 1
  let gain := (2 * bound + 1) / (2 * bound + 1 - tolerance)
  have hbound : 0 ≤ bound := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal (0 : Fin 4)) 0)
  have hdenominator : 0 < 2 * bound + 1 - tolerance := by linarith
  have hgain : 0 < gain := div_pos (by linarith) hdenominator
  obtain ⟨weight, hpositive⟩ :=
    exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff reward hnot
  have hwidth : ∀ who, lower who < upper who := by
    intro who
    have h := quittingSingletonBoxWidth_pos reward hreward who
    change 0 < bound + 1 - quittingSoloReward reward who who at h
    exact sub_pos.mp h
  have hupper : ∀ owner receiver, quittingSoloReward reward owner receiver ≤ upper receiver := by
    intro owner receiver
    have h := (le_abs_self _).trans (hreward (quittingSingletonTerminal owner) receiver)
    change quittingSoloReward reward owner receiver ≤ bound at h
    exact h.trans (by dsimp [upper]; linarith)
  have himage : ∀ receiver, 0 ≤ ∑ owner,
      (quittingSoloReward reward owner receiver - lower receiver) * weight.weights owner := by
    intro receiver
    simpa only [lower, quittingProjectiveLCPMatrix, quittingSoloReward,
      quittingProjectiveSingletonTerminal, quittingSingletonTerminal, mul_comm] using
      (hpositive receiver).le
  have hdrift : ∀ point ∈ Icc lower upper, ∀ owner, point owner = lower owner →
      gain ≤ fderiv ℝ potential point (point - quittingSoloReward reward owner) := by
    intro point hpoint owner howner
    have hdiff : DifferentiableAt ℝ potential point :=
      (hsmooth.differentiableOn (by norm_num) point (hbox hpoint)).differentiableAt
        (hopen.mem_nhds (hbox hpoint))
    exact (quittingRobustPotential_singletonFace_fderiv_bounds reward hreward
      htolerance0 htolerance1 potential hpotential point owner
      (fun who => ⟨hpoint.1 who, hpoint.2 who⟩) howner hdiff).2.2
  have haccount := Math.signedMixedCurvatureAccount_at_every_box_minimum lower upper
    (quittingSoloReward reward) weight.weights potential domain gain hwidth (fun _ => rfl)
    hupper weight.weights_nonneg weight.total_of_fintype himage hopen hbox hsmooth hdrift
  have hparameters := quittingSingletonBox_mixedCurvature_width_bounds reward hreward
  have hmaximum := Math.exists_box_mixed_curvature_max_ge_of_face_drift lower upper
    (quittingSoloReward reward) weight.weights potential domain gain (2 * bound + 1)
    hwidth (fun _ => rfl) hupper weight.weights_nonneg weight.total_of_fintype himage
    hopen hbox hsmooth hparameters.1 hparameters.2.1 hparameters.2.2 hdrift
  refine ⟨hgain, weight, hpositive, haccount, ?_⟩
  simpa only [gain, lower, upper, quittingSingletonBox, Fintype.card_fin,
    Nat.reduceSub, Nat.cast_ofNat] using hmaximum

end GameTheory
