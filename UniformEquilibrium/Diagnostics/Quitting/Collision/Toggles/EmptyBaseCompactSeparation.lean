/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PMFProduct.Bool
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.EmptyBaseSemanticDispatch
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SemanticCompactGap
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Exact compact-interior defect for the empty-base strict-toggle face

This is the literal `W` screen: active coordinates contribute the absolute
`H` residual, while passive coordinates contribute the positive part of the
cleared `P` residual.  Its zero set is exactly the stationary feasibility
system, and exclusion of that zero set gives quantitative separation on every
nonempty compact interior box.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The active residual in compact simplex coordinates. -/
def quittingEmptyBaseSimplexActiveResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : QuittingRootSimplex ι) (who : ι) : ℝ :=
  quittingEmptyBaseActiveResidual reward (quittingRootOfSimplex root) who

/-- The passive cleared residual in compact simplex coordinates. -/
def quittingEmptyBaseSimplexPassiveResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : QuittingRootSimplex ι) (who : ι) : ℝ :=
  quittingEmptyBasePassiveResidual reward (quittingRootOfSimplex root) who

/-- The literal nonnegative coordinate defect used in `W`. -/
def quittingEmptyBaseSimplexCoordinateDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : QuittingRootSimplex ι) (who : ι) : ℝ :=
  if who ∈ active then
    |quittingEmptyBaseSimplexActiveResidual reward root who|
  else max (quittingEmptyBaseSimplexPassiveResidual reward root who) 0

/-- The exact finite maximum `W` from the empty-base packet. -/
def quittingEmptyBaseSimplexDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : QuittingRootSimplex ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingEmptyBaseSimplexCoordinateDefect reward active root)

/-- Closed compact-interior box with active hazards in
`[rho, 1-rho]` and all passive hazards zero. -/
def quittingEmptyBaseRhoBox (active : Finset ι) (rho : ℝ) :
    Set (QuittingRootSimplex ι) :=
  {root | (∀ who ∈ active, rho ≤ root who true ∧ root who true ≤ 1 - rho) ∧
    ∀ who ∉ active, root who true = 0}

/-- Exact strictly interior empty-base feasibility system, including the
pure-Continue restriction on every passive coordinate. -/
def IsQuittingEmptyBaseSimplexInteriorSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : QuittingRootSimplex ι) : Prop :=
  (∀ who ∈ active, 0 < root who true ∧ root who true < 1) ∧
    (∀ who ∈ active,
      quittingEmptyBaseSimplexActiveResidual reward root who = 0) ∧
    ∀ who ∉ active, root who true = 0 ∧
      quittingEmptyBaseSimplexPassiveResidual reward root who ≤ 0

omit [Nonempty ι] in
/-- The fixed-opponent Continue mass is continuous in simplex coordinates. -/
theorem continuous_quittingStationaryFixedOpponentsContinueMass_simplex
    (who : ι) :
    Continuous fun root : QuittingRootSimplex ι =>
      quittingStationaryFixedOpponentsContinueMass
        (quittingRootOfSimplex root) who := by
  simp only [quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  apply continuous_finsetProd
  intro player _
  by_cases hplayer : player = who
  · subst player
    simpa using (continuous_const : Continuous
      (fun _ : QuittingRootSimplex ι => (1 : ℝ)))
  · have hcoordinate : Continuous
        (fun root : QuittingRootSimplex ι => root player false) :=
      (continuous_apply false).comp
        (continuous_subtype_val.comp (continuous_apply player))
    convert hcoordinate using 1
    funext root
    simp [Function.update_of_ne hplayer,
      quittingRootOfSimplex_apply_toReal]

omit [DecidableEq ι] [Nonempty ι] in
/-- The all-Continue mass is continuous in simplex coordinates. -/
theorem continuous_quittingStationaryContinueMass_simplex_local :
    Continuous fun root : QuittingRootSimplex ι =>
      quittingStationaryContinueMass (quittingRootOfSimplex root) := by
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingRootOfSimplex_apply_toReal]
  exact continuous_finsetProd _ fun player _ =>
    (continuous_apply false).comp
      (continuous_subtype_val.comp (continuous_apply player))

omit [Nonempty ι] in
/-- `H` is a continuous polynomial on the root simplex. -/
theorem continuous_quittingEmptyBaseSimplexActiveResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous fun root : QuittingRootSimplex ι =>
      quittingEmptyBaseSimplexActiveResidual reward root who := by
  have hquit : Continuous fun root : QuittingRootSimplex ι =>
      quittingStationaryFixedOpponentsQuitValue reward
        (quittingRootOfSimplex root) who := by
    have h := (continuous_quittingRootQuitPayoff_simplex reward who).comp
      ((continuous_const : Continuous
        (fun _ : QuittingRootSimplex ι => (0 : Payoff ι))).prodMk continuous_id)
    convert h using 1
    funext root
    simp only [Function.comp_apply]
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => quittingRootOfSimplex root) who 0 0).symm
  have hcontinue : Continuous fun root : QuittingRootSimplex ι =>
      quittingStationaryFixedOpponentsContinueReward reward
        (quittingRootOfSimplex root) who := by
    have h := (continuous_quittingRootContinuePayoff_simplex reward who).comp
      ((continuous_const : Continuous
        (fun _ : QuittingRootSimplex ι => (0 : Payoff ι))).prodMk continuous_id)
    convert h using 1
    funext root
    simp only [Function.comp_apply]
    have heq := quittingRootContinuePayoff_eq_fixedOpponents
      reward (fun _ => quittingRootOfSimplex root) who 0 0
    simpa [quittingStationaryFixedOpponentsContinueReward,
      quittingStationaryFixedOpponentsContinueMass] using heq.symm
  exact ((continuous_const.sub
    (continuous_quittingStationaryFixedOpponentsContinueMass_simplex who)).mul
      hquit).sub hcontinue

omit [Nonempty ι] in
/-- `P` is a continuous polynomial on the root simplex. -/
theorem continuous_quittingEmptyBaseSimplexPassiveResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous fun root : QuittingRootSimplex ι =>
      quittingEmptyBaseSimplexPassiveResidual reward root who := by
  have hquit : Continuous fun root : QuittingRootSimplex ι =>
      quittingStationaryFixedOpponentsQuitValue reward
        (quittingRootOfSimplex root) who := by
    have h := (continuous_quittingRootQuitPayoff_simplex reward who).comp
      ((continuous_const : Continuous
        (fun _ : QuittingRootSimplex ι => (0 : Payoff ι))).prodMk continuous_id)
    convert h using 1
    funext root
    simp only [Function.comp_apply]
    simpa [quittingStationaryFixedOpponentsQuitValue] using
      (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
        reward (fun _ => quittingRootOfSimplex root) who 0 0).symm
  have habsorb : Continuous fun root : QuittingRootSimplex ι =>
      quittingRootAbsorbingContribution reward
        (quittingRootOfSimplex root) who := by
    have h := (continuous_quittingRootExpectedPayoff_simplex reward who).comp
      ((continuous_const : Continuous
        (fun _ : QuittingRootSimplex ι => (0 : Payoff ι))).prodMk continuous_id)
    convert h using 1
    funext root
    rfl
  exact ((continuous_const.sub continuous_quittingStationaryContinueMass_simplex_local).mul
    hquit).sub habsorb

omit [Nonempty ι] in
/-- Every coordinate defect is continuous. -/
theorem continuous_quittingEmptyBaseSimplexCoordinateDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (who : ι) :
    Continuous fun root : QuittingRootSimplex ι =>
      quittingEmptyBaseSimplexCoordinateDefect reward active root who := by
  by_cases hwho : who ∈ active
  · simpa [quittingEmptyBaseSimplexCoordinateDefect, hwho] using
      (continuous_quittingEmptyBaseSimplexActiveResidual reward who).abs
  · simpa [quittingEmptyBaseSimplexCoordinateDefect, hwho] using
      (continuous_quittingEmptyBaseSimplexPassiveResidual reward who).max
        continuous_const

/-- The finite maximum `W` is continuous. -/
theorem continuous_quittingEmptyBaseSimplexDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) :
    Continuous (quittingEmptyBaseSimplexDefect reward active) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun who _ =>
    continuous_quittingEmptyBaseSimplexCoordinateDefect reward active who

/-- Every coordinate defect lies below `W`. -/
theorem quittingEmptyBaseSimplexCoordinateDefect_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : QuittingRootSimplex ι) (who : ι) :
    quittingEmptyBaseSimplexCoordinateDefect reward active root who ≤
      quittingEmptyBaseSimplexDefect reward active root := by
  exact Finset.le_sup' (f :=
    quittingEmptyBaseSimplexCoordinateDefect reward active root)
    (Finset.mem_univ who)

/-- **Exact zero-set adapter.**  `W = 0` is precisely all active `H`
equalities together with all passive cleared inequalities. -/
theorem quittingEmptyBaseSimplexDefect_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : QuittingRootSimplex ι) :
    quittingEmptyBaseSimplexDefect reward active root = 0 ↔
      (∀ who ∈ active,
        quittingEmptyBaseSimplexActiveResidual reward root who = 0) ∧
      ∀ who ∉ active,
        quittingEmptyBaseSimplexPassiveResidual reward root who ≤ 0 := by
  constructor
  · intro hzero
    constructor
    · intro who hwho
      have hle := quittingEmptyBaseSimplexCoordinateDefect_le
        reward active root who
      rw [hzero] at hle
      simpa [quittingEmptyBaseSimplexCoordinateDefect, hwho,
        abs_nonpos_iff] using hle
    · intro who hwho
      have hle := quittingEmptyBaseSimplexCoordinateDefect_le
        reward active root who
      rw [hzero] at hle
      simpa [quittingEmptyBaseSimplexCoordinateDefect, hwho] using hle
  · rintro ⟨hactive, hpassive⟩
    apply le_antisymm
    · apply Finset.sup'_le
      intro who _
      by_cases hwho : who ∈ active
      · simp [quittingEmptyBaseSimplexCoordinateDefect, hwho, hactive who hwho]
      · simp [quittingEmptyBaseSimplexCoordinateDefect, hwho,
          hpassive who hwho]
    · obtain ⟨who⟩ := ‹Nonempty ι›
      have hnonneg : 0 ≤
          quittingEmptyBaseSimplexCoordinateDefect reward active root who := by
        by_cases hwho : who ∈ active
        · simp [quittingEmptyBaseSimplexCoordinateDefect, hwho]
        · simp [quittingEmptyBaseSimplexCoordinateDefect, hwho]
      exact hnonneg.trans
        (quittingEmptyBaseSimplexCoordinateDefect_le reward active root who)

omit [DecidableEq ι] [Nonempty ι] in
/-- The `rho`-interior face box is closed. -/
theorem isClosed_quittingEmptyBaseRhoBox (active : Finset ι) (rho : ℝ) :
    IsClosed (quittingEmptyBaseRhoBox active rho) := by
  rw [show quittingEmptyBaseRhoBox active rho =
      (⋂ who, ⋂ _hwho : who ∈ active,
        {root : QuittingRootSimplex ι |
          rho ≤ root who true ∧ root who true ≤ 1 - rho}) ∩
      ⋂ who, ⋂ _hwho : who ∉ active,
        {root : QuittingRootSimplex ι | root who true = 0} by
    ext root
    simp [quittingEmptyBaseRhoBox]]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro who
    apply isClosed_iInter
    intro _hwho
    have hcoordinate : Continuous
        (fun root : QuittingRootSimplex ι => root who true) :=
      (continuous_apply true).comp
        (continuous_subtype_val.comp (continuous_apply who))
    exact (isClosed_le continuous_const hcoordinate).inter
      (isClosed_le hcoordinate continuous_const)
  · apply isClosed_iInter
    intro who
    apply isClosed_iInter
    intro _hwho
    have hcoordinate : Continuous
        (fun root : QuittingRootSimplex ι => root who true) :=
      (continuous_apply true).comp
        (continuous_subtype_val.comp (continuous_apply who))
    exact isClosed_eq hcoordinate continuous_const

omit [DecidableEq ι] [Nonempty ι] in
/-- The `rho`-interior face box is compact. -/
theorem isCompact_quittingEmptyBaseRhoBox (active : Finset ι) (rho : ℝ) :
    IsCompact (quittingEmptyBaseRhoBox active rho) :=
  (isClosed_quittingEmptyBaseRhoBox active rho).isCompact

omit [Nonempty ι] in
/-- Every valid interior box is nonempty (the active coordinates may all use
the fair Boolean law). -/
theorem quittingEmptyBaseRhoBox_nonempty
    (active : Finset ι) {rho : ℝ} (hrhoHalf : rho ≤ 1 / 2) :
    (quittingEmptyBaseRhoBox active rho).Nonempty := by
  let root : QuittingRootSimplex ι := fun who =>
    if who ∈ active then stdSimplexEquiv (PMF.uniformOfFintype Bool)
    else stdSimplexEquiv (PMF.pure false)
  refine ⟨root, ?_⟩
  constructor
  · intro who hwho
    have hhalf : root who true = 1 / 2 := by
      norm_num [root, hwho, coe_stdSimplexEquiv_apply, toVector,
        PMF.uniformOfFintype_apply]
    rw [hhalf]
    constructor
    · exact hrhoHalf
    · linarith
  · intro who hwho
    simp [root, hwho, coe_stdSimplexEquiv_apply, toVector]

/-- The defect `W` is nonnegative. -/
theorem quittingEmptyBaseSimplexDefect_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (root : QuittingRootSimplex ι) :
    0 ≤ quittingEmptyBaseSimplexDefect reward active root := by
  obtain ⟨who⟩ := ‹Nonempty ι›
  have hcoordinate : 0 ≤
      quittingEmptyBaseSimplexCoordinateDefect reward active root who := by
    by_cases hwho : who ∈ active
    · simp [quittingEmptyBaseSimplexCoordinateDefect, hwho]
    · simp [quittingEmptyBaseSimplexCoordinateDefect, hwho]
  exact hcoordinate.trans
    (quittingEmptyBaseSimplexCoordinateDefect_le reward active root who)

/-- **Compact `rho`-box separation.**  If the empty-base feasibility system
has no strictly interior face solution, the exact `W` defect has an attained
strictly positive lower bound on every compact interior box. -/
theorem exists_quittingEmptyBaseRhoBox_pos_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) {rho : ℝ} (hrho0 : 0 < rho)
    (hrhoHalf : rho < 1 / 2)
    (hnoInterior : ¬ ∃ root : QuittingRootSimplex ι,
      IsQuittingEmptyBaseSimplexInteriorSolution reward active root) :
    ∃ gamma : ℝ, 0 < gamma ∧
      ∀ root ∈ quittingEmptyBaseRhoBox active rho,
        gamma ≤ quittingEmptyBaseSimplexDefect reward active root := by
  apply exists_pos_compactGap_of_pos
    (quittingEmptyBaseRhoBox active rho)
    (isCompact_quittingEmptyBaseRhoBox active rho)
    (quittingEmptyBaseRhoBox_nonempty active hrhoHalf.le)
    (quittingEmptyBaseSimplexDefect reward active)
    (continuous_quittingEmptyBaseSimplexDefect reward active).continuousOn
  intro root hroot
  have hne : quittingEmptyBaseSimplexDefect reward active root ≠ 0 := by
    intro hzero
    apply hnoInterior
    refine ⟨root, ?_, (quittingEmptyBaseSimplexDefect_eq_zero_iff
      reward active root).mp hzero |>.1, ?_⟩
    · intro who hwho
      have hbounds := hroot.1 who hwho
      constructor
      · exact hrho0.trans_le hbounds.1
      · linarith [hbounds.2, hrhoHalf]
    · intro who hwho
      exact ⟨hroot.2 who hwho,
        ((quittingEmptyBaseSimplexDefect_eq_zero_iff
          reward active root).mp hzero).2 who hwho⟩
  exact lt_of_le_of_ne
    (quittingEmptyBaseSimplexDefect_nonneg reward active root) (Ne.symm hne)

/-- A vanishing-`W` sequence cannot remain in any fixed compact interior
box when the interior feasibility system is empty. -/
theorem eventually_not_mem_quittingEmptyBaseRhoBox_of_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) {index : Type} {filter : Filter index}
    (roots : index → QuittingRootSimplex ι)
    (hnoInterior : ¬ ∃ root : QuittingRootSimplex ι,
      IsQuittingEmptyBaseSimplexInteriorSolution reward active root)
    (htendsto : Filter.Tendsto
      (fun n => quittingEmptyBaseSimplexDefect reward active (roots n))
      filter (nhds 0))
    {rho : ℝ} (hrho0 : 0 < rho) (hrhoHalf : rho < 1 / 2) :
    ∀ᶠ n in filter, roots n ∉ quittingEmptyBaseRhoBox active rho := by
  obtain ⟨gamma, hgamma, hgap⟩ := exists_quittingEmptyBaseRhoBox_pos_gap
    reward active hrho0 hrhoHalf hnoInterior
  exact eventually_not_mem_of_tendsto_zero_of_pos_gap
    (quittingEmptyBaseRhoBox active rho)
    (quittingEmptyBaseSimplexDefect reward active) roots
    hgamma hgap htendsto

/-- On the exact empty-base face, leaving every fixed `rho` box means that
some active hazard is quantitatively near zero or one. -/
theorem eventually_exists_active_boundary_of_tendsto_emptyBaseDefect_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) {index : Type} {filter : Filter index}
    (roots : index → QuittingRootSimplex ι)
    (hface : ∀ n who, who ∉ active → roots n who true = 0)
    (hnoInterior : ¬ ∃ root : QuittingRootSimplex ι,
      IsQuittingEmptyBaseSimplexInteriorSolution reward active root)
    (htendsto : Filter.Tendsto
      (fun n => quittingEmptyBaseSimplexDefect reward active (roots n))
      filter (nhds 0))
    {rho : ℝ} (hrho0 : 0 < rho) (hrhoHalf : rho < 1 / 2) :
    ∀ᶠ n in filter, ∃ who ∈ active,
      roots n who true < rho ∨ 1 - rho < roots n who true := by
  filter_upwards [eventually_not_mem_quittingEmptyBaseRhoBox_of_tendsto_zero
    reward active roots hnoInterior htendsto hrho0 hrhoHalf] with n hn
  by_contra hboundary
  push Not at hboundary
  apply hn
  exact ⟨fun who hwho => hboundary who hwho, hface n⟩

omit [Nonempty ι] in
/-- An exact simplex solution is precisely the finite data consumed by the
all-behavior empty-base stationary compiler. -/
theorem nonempty_quittingEmptyBaseInteriorCertificate_of_simplexSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (htwo : 2 ≤ active.card)
    (root : QuittingRootSimplex ι)
    (hroot : IsQuittingEmptyBaseSimplexInteriorSolution reward active root) :
    Nonempty (QuittingEmptyBaseInteriorCertificate reward active
      (quittingRootOfSimplex root)) := by
  refine ⟨{
    two_le_card := htwo
    active_quit_pos := ?_
    active_continue_pos := ?_
    inactive_continue := ?_
    active_residual_eq_zero := hroot.2.1
    passive_residual_nonpos := fun who hwho => (hroot.2.2 who hwho).2 }⟩
  · intro who hwho
    simpa [quittingRootOfSimplex_apply_toReal] using (hroot.1 who hwho).1
  · intro who hwho
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (quittingRootOfSimplex root) who
    have hquit := (hroot.1 who hwho).2
    rw [quittingRootOfSimplex_apply_toReal,
      quittingRootOfSimplex_apply_toReal] at hsum
    rw [quittingRootOfSimplex_apply_toReal]
    linarith
  · intro who hwho
    apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
    simpa [quittingRootOfSimplex_apply_toReal] using (hroot.2.2 who hwho).1

omit [Nonempty ι] in
/-- The finite simplex system and the stationary semantic certificate are
equivalent at the represented root. -/
theorem isQuittingEmptyBaseSimplexInteriorSolution_iff_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (htwo : 2 ≤ active.card)
    (root : QuittingRootSimplex ι) :
    IsQuittingEmptyBaseSimplexInteriorSolution reward active root ↔
      Nonempty (QuittingEmptyBaseInteriorCertificate reward active
        (quittingRootOfSimplex root)) := by
  constructor
  · exact nonempty_quittingEmptyBaseInteriorCertificate_of_simplexSolution
      reward active htwo root
  · rintro ⟨certificate⟩
    refine ⟨?_, certificate.active_residual_eq_zero, ?_⟩
    · intro who hwho
      have hquit := certificate.active_quit_pos who hwho
      have hcontinue := certificate.active_continue_pos who hwho
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (quittingRootOfSimplex root) who
      rw [quittingRootOfSimplex_apply_toReal] at hquit hcontinue
      rw [quittingRootOfSimplex_apply_toReal,
        quittingRootOfSimplex_apply_toReal] at hsum
      exact ⟨hquit, by linarith⟩
    · intro who hwho
      have hinactive := certificate.inactive_continue who hwho
      have hzero : root who true = 0 := by
        rw [← quittingRootOfSimplex_apply_toReal]
        simp [hinactive]
      exact ⟨hzero, certificate.passive_residual_nonpos who hwho⟩

omit [Nonempty ι] in
/-- A feasible empty-base simplex point produces an actual fixed uniform
payoff, with no restriction on the deviator's behavioral stopping rule. -/
theorem exists_uniformPayoff_of_quittingEmptyBaseSimplexSolution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (htwo : 2 ≤ active.card)
    (root : QuittingRootSimplex ι)
    (hroot : IsQuittingEmptyBaseSimplexInteriorSolution reward active root) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨certificate⟩ :=
    nonempty_quittingEmptyBaseInteriorCertificate_of_simplexSolution
      reward active htwo root hroot
  exact ⟨fun who => quittingTerminalPayoff reward
      (quittingStationaryProfile reward (quittingRootOfSimplex root)) who,
    certificate.isUniformEquilibriumPayoff⟩

/-- **Exact empty-base ordered alternative.**  Either the finite stationary
system has a solution and the all-behavior compiler closes it, or the system
is empty and the literal `W` screen has a positive attained gap on every
compact interior box. -/
theorem exists_uniformPayoff_or_emptyBase_noSolution_with_rhoGaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (htwo : 2 ≤ active.card) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      (¬ ∃ root : QuittingRootSimplex ι,
          IsQuittingEmptyBaseSimplexInteriorSolution reward active root) ∧
        ∀ rho : ℝ, 0 < rho → rho < 1 / 2 →
          ∃ gamma : ℝ, 0 < gamma ∧
            ∀ root ∈ quittingEmptyBaseRhoBox active rho,
              gamma ≤ quittingEmptyBaseSimplexDefect reward active root := by
  classical
  by_cases hsolution : ∃ root : QuittingRootSimplex ι,
      IsQuittingEmptyBaseSimplexInteriorSolution reward active root
  · left
    obtain ⟨root, hroot⟩ := hsolution
    exact exists_uniformPayoff_of_quittingEmptyBaseSimplexSolution
      reward active htwo root hroot
  · right
    refine ⟨hsolution, ?_⟩
    intro rho hrho0 hrhoHalf
    exact exists_quittingEmptyBaseRhoBox_pos_gap
      reward active hrho0 hrhoHalf hsolution

end GameTheory
