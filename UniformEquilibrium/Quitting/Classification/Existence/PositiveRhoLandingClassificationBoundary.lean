/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.CorrectedPointwiseSourceBoundary
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.PositiveRhoSourceTerminalConsumer
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic

/-!
# Classification boundary of a positive-rho landing family

A positive-rho landing family selects an actual uniform-payoff target, but
that semantic fact alone does not put its profiles in one of the AKRS
classes.  Compactifying the reached row gives a sharper classification
split.  Zero limiting absorption is stationary exactly on the zero-solo
side; otherwise it leaves the nonzero all-Continue phantom.  Positive
limiting absorption is stationary when the temporal value recurs and the
saturated-opponent boundary packet holds.  Exact rationality makes that
boundary packet automatic when punishment values are nonnegative, so the
positive-absorption residual is now temporal nonrecurrence or an explicit
negative punishment coordinate.  The other source arm, a positive-survival
support--Bellman spine, is stationary throughout the nonpositive-singleton
regime.  Its only residual includes an actual positive singleton and a
persistent unrestricted deviation gap on executable late suffixes.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Zero-solo tables lie in the pointwise stationary branch, witnessed by
the exact all-Continue profile. -/
theorem quittingStationaryεEquilibriumAt_of_zeroSolo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hzero : IsQuittingZeroSolo reward) {δ : ℝ} (hδ : 0 ≤ δ) :
    QuittingStationaryεEquilibriumAt reward δ := by
  refine ⟨quittingAllContinueRoot, ?_⟩
  exact
    (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero).mono hδ

/-- At zero limiting absorption, failure of zero-solo yields the precise
nonzero all-Continue phantom. -/
theorem QuittingLowSurvivalPositiveRhoCompactLimit.phantom_of_zeroAbsorption
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex limit.root) = 0)
    (hnotZeroSolo : ¬IsQuittingZeroSolo reward) :
    Nonempty (QuittingLowSurvivalAllContinuePhantom reward) := by
  have hroot := limit.root_eq_allContinue_of_absorption_eq_zero habsorption
  have hvalueNe : limit.actualTail ≠ 0 := by
    intro hzero
    apply hnotZeroSolo
    intro who
    have hendpoint := limit.exactEndpointNash who
    rw [limit.clippedTail_eq_actual, hzero, hroot] at hendpoint
    simpa [quittingAllContinueRoot] using hendpoint.1
  refine ⟨{
    value := limit.actualTail
    value_ne_zero := hvalueNe
    notZeroSolo := hnotZeroSolo
    value_mem := limit.actualTail_mem
    rational := limit.actualTail_rational
    support := ?_ }⟩
  rw [← limit.clippedTail_eq_actual, ← hroot]
  exact limit.exactSupport

/-- The all-Continue residual with its actual landing family and compact
source limit retained.  Unlike `QuittingLowSurvivalAllContinuePhantom`, this
object remembers the source whose reached suffixes realize `base.actualTail`.
-/
structure QuittingLowSurvivalPositiveRhoAllContinueSourceResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (u : ℝ) where
  landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u
  base : QuittingLowSurvivalPositiveRhoCompactLimit landing
  absorption_zero : quittingRootAbsorptionMass
    (quittingRootOfSimplex base.root) = 0
  notZeroSolo : ¬IsQuittingZeroSolo reward

/-- Forgetting the actual source recovers the finite-dimensional phantom. -/
theorem QuittingLowSurvivalPositiveRhoAllContinueSourceResidual.nonempty_phantom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (residual :
      QuittingLowSurvivalPositiveRhoAllContinueSourceResidual reward u) :
    Nonempty (QuittingLowSurvivalAllContinuePhantom reward) :=
  residual.base.phantom_of_zeroAbsorption residual.absorption_zero
    residual.notZeroSolo

/-- The retained source suffixes realize the phantom annotation as an actual
uniform-payoff target.  This is semantic delivery, not an AKRS classified
form. -/
theorem
    QuittingLowSurvivalPositiveRhoAllContinueSourceResidual.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (residual :
      QuittingLowSurvivalPositiveRhoAllContinueSourceResidual reward u) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      residual.base.actualTail :=
  residual.base.isUniformEquilibriumPayoff_actualTail

/-- Recurrence and the exact boundary packet turn the reached positive-
absorption row into an exact stationary equilibrium, hence into the
pointwise stationary branch at every nonnegative tolerance. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.stationaryAt_of_recurrence_boundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (habsorption : 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex limit.root))
    (hrecurrence : limit.predecessorValue = limit.actualTail)
    (hboundary : IsQuittingStationaryBoundaryAdmissible reward
      (quittingRootOfSimplex limit.root) limit.actualTail)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    QuittingStationaryεEquilibriumAt reward δ := by
  let root := quittingRootOfSimplex limit.root
  have hcontinue : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hfixed : limit.actualTail = quittingRootSuccessorPayoff reward
      limit.actualTail root := by
    rw [← limit.predecessorValue_bellman]
    exact hrecurrence.symm
  have hendpoint : IsεQuittingRootEndpointNash reward limit.actualTail 0 root := by
    rw [← limit.clippedTail_eq_actual]
    exact limit.exactEndpointNash
  have hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) :=
    (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
      reward root limit.actualTail hcontinue hfixed hendpoint).mpr hboundary
  exact ⟨root, hnash.mono hδ⟩

/-- At a recurrent compact landing row, nonnegative punishment values force
the saturated-opponent boundary inequalities.  Endpoint Nash prices quitting
now, while exact individual rationality prices never quitting. -/
theorem
    QuittingLowSurvivalPositiveRhoCompactLimit.boundary_of_recurrence_of_nonnegativePunishment
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    {landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u}
    (limit : QuittingLowSurvivalPositiveRhoCompactLimit landing)
    (hrecurrence : limit.predecessorValue = limit.actualTail)
    (hpunishment : ∀ who, 0 ≤ quittingPunishmentValue reward who) :
    IsQuittingStationaryBoundaryAdmissible reward
      (quittingRootOfSimplex limit.root) limit.actualTail := by
  let root := quittingRootOfSimplex limit.root
  have hfixed : limit.actualTail =
      quittingRootSuccessorPayoff reward limit.actualTail root := by
    rw [← limit.predecessorValue_bellman]
    exact hrecurrence.symm
  have hendpoint : IsεQuittingRootEndpointNash reward
      limit.actualTail 0 root := by
    rw [← limit.clippedTail_eq_actual]
    exact limit.exactEndpointNash
  have hpure :=
    (isεQuittingRootEndpointNash_iff_purePayoff_le
      reward limit.actualTail 0 root).mp hendpoint
  intro who hmass
  have hnonnegative : 0 ≤ limit.actualTail who := by
    have hrational := limit.actualTail_rational who
    change quittingPunishmentValue reward who - 0 ≤
      limit.actualTail who at hrational
    linarith [hpunishment who]
  apply max_le hnonnegative
  have hquit := (hpure who).1
  have hopponents :=
    opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root who hmass
  have hupdate : Function.update root who (PMF.pure true) =
      Function.update (quittingAllContinueRoot : ι → PMF Bool)
        who (PMF.pure true) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · rw [Function.update_of_ne hplayer,
        Function.update_of_ne hplayer, hopponents player hplayer]
      rfl
  have hquitEq : quittingRootQuitPayoff reward limit.actualTail root who =
      reward (quittingSingletonTerminal who) who := by
    unfold quittingRootQuitPayoff
    rw [hupdate,
      quittingRootExpectedPayoff_allContinue_update_true]
  rw [hquitEq, ← congrFun hfixed who] at hquit
  simpa using hquit

/-- The positive-absorption attachment seam after using individual
rationality at a recurrent row.  Failure is now either temporal
nonrecurrence or an explicit negative punishment value; a bare stationary
boundary failure is no longer retained. -/
structure QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (u : ℝ) where
  landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u
  base : QuittingLowSurvivalPositiveRhoCompactLimit landing
  consecutive : QuittingLowSurvivalPositiveRhoConsecutiveLimit base
  absorption_pos : 0 < quittingRootAbsorptionMass
    (quittingRootOfSimplex base.root)
  obstruction : base.predecessorValue ≠ base.actualTail ∨
    ∃ who, quittingPunishmentValue reward who < 0

/-- **Strict landing-to-classification reduction.**  A literal positive-rho
landing family either yields the full AKRS stationary branch, or leaves one
of two already identified source-derived seams:
the nonzero all-Continue phantom or the positive-absorption two-edge
attachment residual, whose obstruction is now nonrecurrence or a negative
punishment coordinate. -/
theorem
    QuittingLowSurvivalPositiveRhoLandingFamily.stationaryExistence_or_sourcePhantom_or_attachment
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u) :
    QuittingStationaryεEquilibriumExistence reward ∨
      Nonempty
        (QuittingLowSurvivalPositiveRhoAllContinueSourceResidual reward u) ∨
        Nonempty
          (QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
            reward u) := by
  obtain ⟨base⟩ := exists_quittingLowSurvivalPositiveRhoCompactLimit landing
  obtain ⟨consecutive⟩ :=
    exists_quittingLowSurvivalPositiveRhoConsecutiveLimit base
  by_cases habsorption : quittingRootAbsorptionMass
      (quittingRootOfSimplex base.root) = 0
  · by_cases hzeroSolo : IsQuittingZeroSolo reward
    · left
      intro δ hδ
      exact quittingStationaryεEquilibriumAt_of_zeroSolo
        reward hzeroSolo hδ.le
    · exact Or.inr (Or.inl ⟨{
        landing := landing
        base := base
        absorption_zero := habsorption
        notZeroSolo := hzeroSolo }⟩)
  · have habsorptionPos : 0 < quittingRootAbsorptionMass
        (quittingRootOfSimplex base.root) :=
      lt_of_le_of_ne
        (quittingRootAbsorptionMass_nonneg
          (quittingRootOfSimplex base.root)) (Ne.symm habsorption)
    by_cases hrecurrence : base.predecessorValue = base.actualTail
    · by_cases hboundary : IsQuittingStationaryBoundaryAdmissible reward
          (quittingRootOfSimplex base.root) base.actualTail
      · left
        intro δ hδ
        exact base.stationaryAt_of_recurrence_boundary
          habsorptionPos hrecurrence hboundary hδ.le
      · exact Or.inr (Or.inr ⟨{
          landing := landing
          base := base
          consecutive := consecutive
          absorption_pos := habsorptionPos
          obstruction := Or.inr (by
            have hnotNonnegative : ¬∀ who,
                0 ≤ quittingPunishmentValue reward who := by
              intro hnonnegative
              exact hboundary
                (base.boundary_of_recurrence_of_nonnegativePunishment
                  hrecurrence hnonnegative)
            simpa only [not_forall, not_le] using hnotNonnegative) }⟩)
    · exact Or.inr (Or.inr ⟨{
        landing := landing
        base := base
        consecutive := consecutive
        absorption_pos := habsorptionPos
        obstruction := Or.inl hrecurrence }⟩)

/-- Pointwise form of
`stationaryExistence_or_sourcePhantom_or_attachment`, with the source phantom
projected to its finite-dimensional certificate. -/
theorem QuittingLowSurvivalPositiveRhoLandingFamily.stationaryAt_or_phantom_or_attachment
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u δ : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (hδ : 0 < δ) :
    QuittingStationaryεEquilibriumAt reward δ ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom reward) ∨
        Nonempty
          (QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
            reward u) := by
  rcases landing.stationaryExistence_or_sourcePhantom_or_attachment with
    hstationary | hsourcePhantom | hattachment
  · exact Or.inl (hstationary δ hδ)
  · obtain ⟨sourcePhantom⟩ := hsourcePhantom
    exact Or.inr (Or.inl sourcePhantom.nonempty_phantom)
  · exact Or.inr (Or.inr hattachment)

/-- A positive-survival support--Bellman boundary with the actual persistent
positive-singleton suffix defect retained. -/
structure QuittingSupportBellmanPositiveSingletonDefectResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) where
  boundary : QuittingSupportBellmanPositiveSurvivalBoundary reward δ
  defect : boundary.PositiveSingletonSuffixDefect

/-- A positive-survival support--Bellman boundary is stationary when every
singleton self-reward is nonpositive.  Otherwise it retains an actual
positive singleton and the resulting persistent unrestricted suffix-
deviation defect. -/
theorem QuittingSupportBellmanPositiveSurvivalBoundary.stationary_or_defect
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ : ℝ}
    (boundary : QuittingSupportBellmanPositiveSurvivalBoundary reward δ) :
    QuittingStationaryεEquilibriumExistence reward ∨
      Nonempty
        (QuittingSupportBellmanPositiveSingletonDefectResidual reward δ) := by
  by_cases hzero : IsQuittingZeroSolo reward
  · left
    intro error herror
    exact quittingStationaryεEquilibriumAt_of_zeroSolo
      reward hzero herror.le
  · right
    have hpositive : ∃ who,
        0 < reward (quittingSingletonTerminal who) who := by
      simpa only [IsQuittingZeroSolo, not_forall, not_le] using hzero
    obtain ⟨who, hwho⟩ := hpositive
    exact ⟨{
      boundary := boundary
      defect := boundary.positiveSingletonSuffixDefectOf who hwho }⟩

/-- The refined residual after consuming the classifiable part of both
positive-rho and positive-survival source arms.  Its last arm now carries an
actual unrestricted suffix-deviation gap, not merely a phantom Bellman
annotation. -/
def QuittingCorrectedPointwiseRefinedSourceResidualAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) : Prop :=
  Nonempty
      (QuittingLowSurvivalPositiveRhoAllContinueSourceResidual reward (1 / 2)) ∨
    Nonempty
      (QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual
        reward (1 / 2)) ∨
      Nonempty
        (QuittingSupportBellmanPositiveSingletonDefectResidual reward δ)

namespace QuittingLCPClassification

/-- Dependency A now reaches the corrected four-way alternative unless one
of three explicit source-derived seams survives.  In particular, neither a
raw positive-rho landing family nor a nonpositive-singleton support--Bellman
boundary remains a residual. -/
theorem
    QuittingPayoffTable.correctedPointwiseAlternative_or_refinedSourceResidualAt
    [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ : ℝ) (hδ : 0 < δ) :
    QuittingStationaryεEquilibriumAt table.zeroNeverReward δ ∨
      QuittingInstantPunishmentεEquilibriumAt table.zeroNeverReward δ ∨
        QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward δ ∨
          QuittingStationarilyGeneratedApproximateEquilibriaAt
            table.zeroNeverReward δ ∨
            QuittingCorrectedPointwiseRefinedSourceResidualAt
              table.zeroNeverReward δ := by
  rcases table.correctedPointwiseAlternative_or_sourceResidualAt
      hequilibrium δ hδ with
    hstationary | hinstant | hwellSupported | hgenerated | hresidual
  · exact Or.inl hstationary
  · exact Or.inr (Or.inl hinstant)
  · exact Or.inr (Or.inr (Or.inl hwellSupported))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hgenerated)))
  · rcases hresidual with hlanding | hboundary
    · obtain ⟨landing⟩ := hlanding
      rcases landing.stationaryExistence_or_sourcePhantom_or_attachment with
        hstationary | hsourcePhantom | hattachment
      · exact Or.inl (hstationary δ hδ)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsourcePhantom))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hattachment)))))
    · obtain ⟨boundary⟩ := hboundary
      rcases boundary.stationary_or_defect with
        hstationary | hdefect
      · exact Or.inl (hstationary δ hδ)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hdefect)))))

/-- Excluding the three refined source residuals at every positive scale
closes Dependency A.  The premise is strictly weaker than excluding every
raw positive-rho landing family or positive-survival boundary, because the
stationary cases above have already been consumed. -/
theorem
    QuittingPayoffTable.hasCorrectedPointwiseFourWayExtraction_of_noRefinedSourceResidual
    (table : QuittingPayoffTable ι)
    (hnoResidual : ∀ δ : ℝ, 0 < δ →
      ¬QuittingCorrectedPointwiseRefinedSourceResidualAt
        table.zeroNeverReward δ) :
    table.HasCorrectedPointwiseFourWayExtraction := by
  intro hequilibrium δ hδ
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      left
      refine ⟨fun who => hempty.elim who, ?_⟩
      intro who
      exact hempty.elim who
  | inr hnonempty =>
      letI := hnonempty
      rcases table.correctedPointwiseAlternative_or_refinedSourceResidualAt
          hequilibrium δ hδ with
        hstationary | hinstant | hwellSupported | hgenerated | hresidual
      · exact Or.inl hstationary
      · exact Or.inr (Or.inl hinstant)
      · exact Or.inr (Or.inr (Or.inl hwellSupported))
      · exact Or.inr (Or.inr (Or.inr hgenerated))
      · exact False.elim (hnoResidual δ hδ hresidual)

end QuittingLCPClassification
end GameTheory
