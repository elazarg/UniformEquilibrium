/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockMassPath
import UniformEquilibrium.Quitting.AbsorptionPath.SingletonContinuousPath

/-!
# Principal-Q clock paths as continuous absorption paths

The principal-Q clock runs forward from a small positive clock to one,
whereas absorption time runs in the opposite direction from zero to one.
This module reverses the constructed cumulative control and fills the final
short interval by an arbitrary simplex direction.  The result has exact total
mass equal to absorption time and therefore delegates to the generic
continuous-singleton adapter.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Finset Math Math.LinearProgramming Set unitInterval
open GameTheory.QuittingAbsorptionPath
open scoped unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Reverse accumulated clock mass into cumulative absorption mass. -/
def PrincipalQClockMassPath.absorptionPrefixPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) :
    Path (0 : ι → ℝ) (path.mass 1) where
  toFun parameter := path.mass 1 - path.toPath.symm parameter
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.absorptionPrefixPath_apply
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (parameter : unitInterval) :
    path.absorptionPrefixPath parameter =
      path.mass 1 - path.mass (unitInterval.symm parameter) :=
  rfl

omit [DecidableEq ι] in
/-- Reversing a coordinatewise monotone clock path gives a coordinatewise
monotone absorption prefix. -/
theorem PrincipalQClockMassPath.monotone_absorptionPrefixPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node) (who : ι) :
    Monotone fun parameter => path.absorptionPrefixPath parameter who := by
  intro first second hle
  change path.absorptionPrefixPath first who ≤
    path.absorptionPrefixPath second who
  rw [path.absorptionPrefixPath_apply,
    path.absorptionPrefixPath_apply]
  exact sub_le_sub_left
    (path.coordinate_monotone who (unitInterval.symm_le_symm.mpr hle)) _

omit [DecidableEq ι] in
/-- Total absorption mass in the reversed prefix is elapsed clock duration
times the normalized absorption parameter. -/
theorem PrincipalQClockMassPath.sum_absorptionPrefixPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (parameter : unitInterval) :
    ∑ who, path.absorptionPrefixPath parameter who =
      (parameter : ℝ) * principalQClockDuration initial node := by
  rw [path.absorptionPrefixPath_apply]
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib,
    path.total_mass, path.total_mass]
  simp only [unitInterval.coe_symm_eq]
  norm_num
  ring

/-- Linear filler for the last short absorption-time interval. -/
def PrincipalQClockMassPath.absorptionFillerPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι) :
    Path (path.mass 1)
      (path.mass 1 + initial.time • (weight : ι → ℝ)) where
  toFun parameter := path.mass 1 +
    (parameter : ℝ) • (initial.time • (weight : ι → ℝ))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

omit [DecidableEq ι] in
@[simp] theorem PrincipalQClockMassPath.absorptionFillerPath_apply
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι) (parameter : unitInterval) :
    path.absorptionFillerPath weight parameter = path.mass 1 +
      (parameter : ℝ) • (initial.time • (weight : ι → ℝ)) :=
  rfl

omit [DecidableEq ι] in
/-- The filler increases every player's cumulative mass. -/
theorem PrincipalQClockMassPath.monotone_absorptionFillerPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι) (who : ι) :
    Monotone fun parameter => path.absorptionFillerPath weight parameter who := by
  intro first second hle
  simp only [path.absorptionFillerPath_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right
      (show (first : ℝ) ≤ (second : ℝ) from hle)
      (mul_nonneg initial.time_pos.le (stdSimplex.zero_le weight who)))
    (path.mass 1 who)

omit [DecidableEq ι] in
/-- Total filler mass is the clock-path duration plus the chosen fraction of
the initial clock mass. -/
theorem PrincipalQClockMassPath.sum_absorptionFillerPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι) (parameter : unitInterval) :
    ∑ who, path.absorptionFillerPath weight parameter who =
      principalQClockDuration initial node +
        (parameter : ℝ) * initial.time := by
  simp only [path.absorptionFillerPath_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, path.total_mass]
  rw [← Finset.mul_sum, ← Finset.mul_sum, stdSimplex.sum_eq_one]
  norm_num

/-- Append an arbitrary simplex filler over the missing initial clock mass.
The hypotheses say that the clock path runs from `initial.time` to one. -/
def PrincipalQClockMassPath.absorptionPlayerPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1) :
    Path (0 : ι → ℝ) (path.mass 1 + initial.time • (weight : ι → ℝ)) :=
  path.absorptionPrefixPath.transAt
    (path.absorptionFillerPath weight)
    (1 - initial.time) (sub_pos.mpr hinitialOne) (by linarith [initial.time_pos])

omit [DecidableEq ι] in
/-- The reversed-and-filled player path is coordinatewise monotone. -/
theorem PrincipalQClockMassPath.monotone_absorptionPlayerPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1) (who : ι) :
    Monotone fun parameter =>
      path.absorptionPlayerPath weight hinitialOne parameter who := by
  have hprefix : Monotone path.absorptionPrefixPath := by
    intro first second hle owner
    exact path.monotone_absorptionPrefixPath owner hle
  have hfiller : Monotone (path.absorptionFillerPath weight) := by
    intro first second hle owner
    exact path.monotone_absorptionFillerPath weight owner hle
  intro first second hle
  exact (Path.monotone_transAt path.absorptionPrefixPath
    (path.absorptionFillerPath weight) (sub_pos.mpr hinitialOne)
    (by linarith [initial.time_pos]) hprefix hfiller hle) who

omit [DecidableEq ι] in
/-- When the clock path ends at one, the reversed prefix and filler have
total player mass exactly equal to absorption time. -/
theorem PrincipalQClockMassPath.sum_absorptionPlayerPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1) (hnodeTime : node.time = 1)
    (parameter : unitInterval) :
    ∑ who, path.absorptionPlayerPath weight hinitialOne parameter who =
      (parameter : ℝ) := by
  let split : ℝ := 1 - initial.time
  have hsplitPos : 0 < split := sub_pos.mpr hinitialOne
  have hsplitOne : split < 1 := by dsimp [split]; linarith [initial.time_pos]
  by_cases hparameter : (parameter : ℝ) ≤ split
  · rw [PrincipalQClockMassPath.absorptionPlayerPath,
      Path.transAt_apply_leftParameter _ _ hsplitPos hsplitOne
        parameter hparameter,
      path.sum_absorptionPrefixPath]
    change ((parameter : ℝ) / split) *
        principalQClockDuration initial node = (parameter : ℝ)
    have hduration : principalQClockDuration initial node = split := by
      simp only [principalQClockDuration, hnodeTime, split]
    rw [hduration, div_mul_cancel₀ _ hsplitPos.ne']
  · have hparameter' : split < (parameter : ℝ) :=
      lt_of_not_ge hparameter
    rw [PrincipalQClockMassPath.absorptionPlayerPath,
      Path.transAt_apply_rightParameter _ _ hsplitPos hsplitOne
        parameter hparameter',
      path.sum_absorptionFillerPath]
    change principalQClockDuration initial node +
        (((parameter : ℝ) - split) / (1 - split)) * initial.time =
      (parameter : ℝ)
    have hduration : principalQClockDuration initial node = split := by
      simp only [principalQClockDuration, hnodeTime, split]
    have hdenom : 1 - split = initial.time := by simp [split]
    rw [hduration, hdenom, div_mul_cancel₀ _ initial.time_pos.ne']
    ring

omit [DecidableEq ι] in
/-- Reversal carries clock mesh support into the absorption prefix: whenever
a player's absorption mass increases before the filler interval, some point
of that interval has scaled continuation state within the mesh error. -/
theorem PrincipalQClockMassPath.exists_absorptionPrefix_meshSupport_witness
    {M : ι → ι → ℝ} {stepBound : ℝ}
    {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1) (hnodeTime : node.time = 1)
    (hsupported : path.IsMeshSupported stepBound)
    (who : ι) (first second : unitInterval) (hle : first ≤ second)
    (hsecond : (second : ℝ) ≤ 1 - initial.time)
    (hincrease : path.absorptionPlayerPath weight hinitialOne first who <
      path.absorptionPlayerPath weight hinitialOne second who) :
    ∃ witness ∈ Set.Icc first second,
      (principalQClockScaledState initial +
          principalQMassImage M
            (path.mass 1 -
              path.absorptionPlayerPath weight hinitialOne witness)) who ≤
        principalQMatrixSpeedBound M * (1 - (witness : ℝ)) * stepBound := by
  let split := 1 - initial.time
  have hsplitPos : 0 < split := sub_pos.mpr hinitialOne
  have hsplitOne : split < 1 := by
    dsimp [split]
    linarith [initial.time_pos]
  have hfirst : (first : ℝ) ≤ split :=
    (show (first : ℝ) ≤ (second : ℝ) from hle).trans hsecond
  let first' := Path.transAtLeftParameter hsplitPos first hfirst
  let second' := Path.transAtLeftParameter hsplitPos second hsecond
  have hleftFirst :
      path.absorptionPlayerPath weight hinitialOne first =
        path.absorptionPrefixPath first' := by
    exact Path.transAt_apply_leftParameter _ _ hsplitPos hsplitOne first hfirst
  have hleftSecond :
      path.absorptionPlayerPath weight hinitialOne second =
        path.absorptionPrefixPath second' := by
    exact Path.transAt_apply_leftParameter _ _ hsplitPos hsplitOne second hsecond
  have hclockIncrease :
      path.mass (unitInterval.symm second') who <
        path.mass (unitInterval.symm first') who := by
    rw [hleftFirst, hleftSecond,
      path.absorptionPrefixPath_apply,
      path.absorptionPrefixPath_apply] at hincrease
    simp only [Pi.sub_apply] at hincrease
    linarith
  have hclockOrder : unitInterval.symm second' ≤ unitInterval.symm first' := by
    apply unitInterval.symm_le_symm.mpr
    exact div_le_div_of_nonneg_right
      (show (first : ℝ) ≤ (second : ℝ) from hle) hsplitPos.le
  obtain ⟨clockWitness, hclockWitness, hclockBound⟩ :=
    hsupported who (unitInterval.symm second')
      (unitInterval.symm first') hclockOrder hclockIncrease
  let witness : unitInterval :=
    ⟨split * (1 - (clockWitness : ℝ)), by
      constructor
      · exact mul_nonneg hsplitPos.le
          (sub_nonneg.mpr clockWitness.property.2)
      · nlinarith [clockWitness.property.1,
          clockWitness.property.2, hsplitOne.le]⟩
  have hwitnessLeSplit : (witness : ℝ) ≤ split := by
    dsimp [witness]
    nlinarith [clockWitness.property.1, hsplitPos.le]
  have hwitnessParam :
      Path.transAtLeftParameter hsplitPos witness hwitnessLeSplit =
        unitInterval.symm clockWitness := by
    apply Subtype.ext
    dsimp [witness, Path.transAtLeftParameter]
    rw [mul_div_cancel_left₀ _ hsplitPos.ne']
  have habsorptionWitness :
      path.absorptionPlayerPath weight hinitialOne witness =
        path.mass 1 - path.mass clockWitness := by
    rw [PrincipalQClockMassPath.absorptionPlayerPath,
      Path.transAt_apply_leftParameter _ _ hsplitPos hsplitOne witness
        hwitnessLeSplit,
      path.absorptionPrefixPath_apply, hwitnessParam]
    congr 2
    exact unitInterval.symm_symm clockWitness
  refine ⟨witness, ?_, ?_⟩
  · constructor
    · have := hclockWitness.2
      dsimp [first', Path.transAtLeftParameter] at this
      change (clockWitness : ℝ) ≤ 1 - (first : ℝ) / split at this
      change (first : ℝ) ≤ split * (1 - (clockWitness : ℝ))
      have hmul := mul_le_mul_of_nonneg_left this hsplitPos.le
      field_simp [hsplitPos.ne'] at hmul
      nlinarith
    · have := hclockWitness.1
      dsimp [second', Path.transAtLeftParameter] at this
      change 1 - (second : ℝ) / split ≤ (clockWitness : ℝ) at this
      change split * (1 - (clockWitness : ℝ)) ≤ (second : ℝ)
      have hmul := mul_le_mul_of_nonneg_left this hsplitPos.le
      field_simp [hsplitPos.ne'] at hmul
      nlinarith
  · rw [habsorptionWitness]
    have hmassRemaining :
        path.mass 1 - (path.mass 1 - path.mass clockWitness) =
          path.mass clockWitness := by
      abel
    rw [hmassRemaining]
    have hclock : principalQNormalizedClock initial node clockWitness =
        1 - (witness : ℝ) := by
      unfold principalQNormalizedClock principalQClockDuration
      rw [hnodeTime]
      dsimp [witness, split]
      ring
    rw [hclock] at hclockBound
    exact hclockBound

/-- Bundle the reversed clock mass and terminal filler as a continuous
singleton absorption path. -/
def PrincipalQClockMassPath.toContinuousAbsorptionPath
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1) (hnodeTime : node.time = 1) :
    AbsorptionPath (ι := ι) :=
  singletonAbsorptionPathOfPlayerPath
    (path.absorptionPlayerPath weight hinitialOne)
    (path.monotone_absorptionPlayerPath weight hinitialOne)
    (path.sum_absorptionPlayerPath weight hinitialOne hnodeTime)

/-- The absorption path compiled from a principal-Q clock mass path is
continuous. -/
theorem PrincipalQClockMassPath.toContinuousAbsorptionPath_continuous
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1) (hnodeTime : node.time = 1) :
    IsContinuousAbsorptionPath
      (path.toContinuousAbsorptionPath weight hinitialOne hnodeTime) :=
  singletonAbsorptionPathOfPlayerPath_continuous _ _ _

/-- Every positive subunit initial clock has a principal-Q continuous
absorption-path approximation ending at clock one. -/
theorem exists_principalQContinuousAbsorptionPath
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound start : ℝ}
    (hstepBound : 0 < stepBound) (hstart : 0 < start) (hstartOne : start < 1)
    (initialState : ι → ℝ)
    (hinitialState : initialState ∈ nonnegativeBoundary)
    (weight : stdSimplex ℝ ι) :
  ∃ path : AbsorptionPath (ι := ι),
      IsContinuousAbsorptionPath path := by
  have hscaledInitial : start • initialState ∈ nonnegativeBoundary := by
    constructor
    · intro who
      exact mul_nonneg hstart.le (hinitialState.1 who)
    · obtain ⟨who, hwho⟩ := hinitialState.2
      exact ⟨who, by simp [hwho]⟩
  let initial := principalQClockNodeOfScaledState start hstart
    (start • initialState) hscaledInitial
  obtain ⟨node, hnodeTime, mass⟩ :=
    exists_principalQClockMassPath_at_time M hdiag hQ hstepBound
      initial 1 (by simp [initial, hstartOne.le])
  obtain ⟨mass⟩ := mass
  exact ⟨mass.toContinuousAbsorptionPath weight (by simpa [initial]) hnodeTime,
    PrincipalQClockMassPath.toContinuousAbsorptionPath_continuous mass weight
      (by simpa [initial]) hnodeTime⟩

end GameTheory.QuittingLCPClassification
