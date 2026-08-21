/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockMassPath
import UniformEquilibrium.Quitting.AbsorptionPath.SingletonContinuousPath
import UniformEquilibrium.Quitting.Classification.LCP.Normalization

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

open Filter Finset Math Math.LinearProgramming Set unitInterval
open GameTheory.QuittingAbsorptionPath
open scoped unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The zero scaled state at a positive paper clock. -/
def zeroPrincipalQClockNode [Nonempty ι] (start : ℝ) (hstart : 0 < start) :
    PrincipalQClockNode ι :=
  principalQClockNodeOfScaledState start hstart 0 ⟨by simp, by
    exact ⟨Classical.choice inferInstance, by simp⟩⟩

omit [DecidableEq ι] in
@[simp] theorem zeroPrincipalQClockNode_time [Nonempty ι]
    (start : ℝ) (hstart : 0 < start) :
    (zeroPrincipalQClockNode start hstart : PrincipalQClockNode ι).time = start :=
  rfl

omit [DecidableEq ι] in
@[simp] theorem zeroPrincipalQClockNode_scaledState [Nonempty ι]
    (start : ℝ) (hstart : 0 < start) :
    principalQClockScaledState
      (zeroPrincipalQClockNode start hstart : PrincipalQClockNode ι) = 0 := by
  exact principalQClockNodeOfScaledState_scaledState _ _ _ _

/-- One exact principal-Q approximation, retaining the clock mass path and
its mesh-support certificate for later compact passage. -/
structure PrincipalQAbsorptionApproximation [Nonempty ι]
    (M : ι → ι → ℝ) (start mesh : ℝ) where
  start_pos : 0 < start
  start_lt_one : start < 1
  mesh_pos : 0 < mesh
  node : PrincipalQClockNode ι
  node_time : node.time = 1
  mass : PrincipalQClockMassPath M (zeroPrincipalQClockNode start start_pos) node
  mesh_supported : mass.IsMeshSupported mesh

omit [DecidableEq ι] in
/-- Projective-Q viability supplies one exact mesh-supported approximation at
every positive subunit starting clock and every positive mesh. -/
theorem exists_principalQAbsorptionApproximation [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M)
    (start mesh : ℝ) (hstart : 0 < start) (hstartOne : start < 1)
    (hmesh : 0 < mesh) :
    Nonempty (PrincipalQAbsorptionApproximation M start mesh) := by
  let initial : PrincipalQClockNode ι := zeroPrincipalQClockNode start hstart
  obtain ⟨node, hnodeTime, mass, hsupported⟩ :=
    exists_principalQClockMassPath_at_time_isMeshSupported M hdiag hQ hmesh
      initial 1 (by simpa [initial] using hstartOne.le)
  exact ⟨{
    start_pos := hstart
    start_lt_one := hstartOne
    mesh_pos := hmesh
    node := node
    node_time := hnodeTime
    mass := mass
    mesh_supported := hsupported }⟩

/-- Canonical simultaneous start and mesh scale for the compact passage. -/
def principalQVanishingScale (n : ℕ) : ℝ :=
  1 / (n + 2 : ℝ)

theorem principalQVanishingScale_pos (n : ℕ) :
    0 < principalQVanishingScale n := by
  apply one_div_pos.mpr
  positivity

theorem principalQVanishingScale_lt_one (n : ℕ) :
    principalQVanishingScale n < 1 := by
  rw [principalQVanishingScale]
  apply (div_lt_one (by positivity)).2
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem tendsto_principalQVanishingScale :
    Tendsto principalQVanishingScale atTop (nhds 0) := by
  have hsucc : StrictMono Nat.succ := fun _ _ h => Nat.succ_lt_succ h
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    hsucc.tendsto_atTop
  convert h using 1
  funext n
  simp only [principalQVanishingScale, Function.comp_apply, Nat.cast_succ,
    one_div]
  congr 1
  ring

/-- A chosen principal-Q approximation at the canonical vanishing scale. -/
noncomputable def principalQVanishingApproximation [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (n : ℕ) :
    PrincipalQAbsorptionApproximation M
      (principalQVanishingScale n) (principalQVanishingScale n) :=
  Classical.choice (exists_principalQAbsorptionApproximation M hdiag hQ
    (principalQVanishingScale n) (principalQVanishingScale n)
    (principalQVanishingScale_pos n) (principalQVanishingScale_lt_one n)
    (principalQVanishingScale_pos n))

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

/-- The normalized reversed player-mass path of the canonical approximation. -/
noncomputable def principalQVanishingPlayerPath [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (weight : stdSimplex ℝ ι) (n : ℕ) :
    Path (0 : ι → ℝ)
      ((principalQVanishingApproximation M hdiag hQ n).mass.mass 1 +
        principalQVanishingScale n • (weight : ι → ℝ)) :=
  (principalQVanishingApproximation M hdiag hQ n).mass.absorptionPlayerPath
    weight (principalQVanishingApproximation M hdiag hQ n).start_lt_one

omit [DecidableEq ι] in
/-- The reversed player-mass paths at vanishing start and mesh have a
uniformly convergent subsequence with normalized monotone limit. -/
theorem exists_tendsto_subsequence_principalQAbsorptionPlayerPath
    [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (weight : stdSimplex ℝ ι) :
    ∃ limit : BoundedContinuousFunction unitInterval (ι → ℝ),
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (fun n => boundedFunctionOfPath
          (principalQVanishingPlayerPath M hdiag hQ weight (subsequence n)))
            atTop (nhds limit) ∧
        limit 0 = 0 ∧
        (∀ who, Monotone fun time => limit time who) ∧
        ∀ time, ∑ who, limit time who = (time : ℝ) := by
  let terminal : ℕ → ι → ℝ := fun n =>
    (principalQVanishingApproximation M hdiag hQ n).mass.mass 1 +
      principalQVanishingScale n • (weight : ι → ℝ)
  let playerPath : ∀ n, Path (0 : ι → ℝ) (terminal n) := fun n =>
    principalQVanishingPlayerPath M hdiag hQ weight n
  have hmono (n : ℕ) (who : ι) :
      Monotone fun time => playerPath n time who :=
    by
      dsimp only [playerPath]
      unfold principalQVanishingPlayerPath
      exact (principalQVanishingApproximation M hdiag hQ n).mass
        |>.monotone_absorptionPlayerPath weight
          (principalQVanishingApproximation M hdiag hQ n).start_lt_one who
  have htotal (n : ℕ) (time : unitInterval) :
      ∑ who, playerPath n time who = (time : ℝ) :=
    by
      dsimp only [playerPath]
      unfold principalQVanishingPlayerPath
      exact (principalQVanishingApproximation M hdiag hQ n).mass
        |>.sum_absorptionPlayerPath weight
          (principalQVanishingApproximation M hdiag hQ n).start_lt_one
          (principalQVanishingApproximation M hdiag hQ n).node_time time
  simpa only [playerPath, terminal] using
    exists_tendsto_subsequence_monotone_playerMass terminal playerPath
      hmono htotal

omit [DecidableEq ι] in
/-- The compact limit of canonical principal-Q approximations is an ordinary
normalized monotone player-mass path, while retaining its constructing
subsequence. -/
theorem exists_principalQAbsorptionPlayerPath_limit [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (weight : stdSimplex ℝ ι) :
    ∃ terminal : ι → ℝ, ∃ limitPath : Path (0 : ι → ℝ) terminal,
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (fun n => boundedFunctionOfPath
          (principalQVanishingPlayerPath M hdiag hQ weight (subsequence n)))
            atTop (nhds (boundedFunctionOfPath limitPath)) ∧
        (∀ who, Monotone fun time => limitPath time who) ∧
        ∀ time, ∑ who, limitPath time who = (time : ℝ) := by
  obtain ⟨limit, subsequence, hsubsequence, htendsto, hzero, hmono, htotal⟩ :=
    exists_tendsto_subsequence_principalQAbsorptionPlayerPath
      M hdiag hQ weight
  let limitPath : Path (0 : ι → ℝ) (limit 1) := {
    toContinuousMap := limit.toContinuousMap
    source' := hzero
    target' := rfl }
  have hbounded : boundedFunctionOfPath limitPath = limit := by
    ext time who
    rfl
  refine ⟨limit 1, limitPath, subsequence, hsubsequence, ?_, ?_, ?_⟩
  · rw [hbounded]
    exact htendsto
  · exact hmono
  · exact htotal

omit [DecidableEq ι] in
/-- With zero initial scaled state, the matrix image of the clock-generated
mass remaining before the filler is coordinatewise nonnegative. -/
theorem PrincipalQClockMassPath.principalQMassImage_remaining_nonneg
    {M : ι → ι → ℝ} {initial node : PrincipalQClockNode ι}
    (path : PrincipalQClockMassPath M initial node)
    (weight : stdSimplex ℝ ι)
    (hinitialOne : initial.time < 1)
    (hscaledInitial : principalQClockScaledState initial = 0)
    (who : ι) (time : unitInterval)
    (htime : (time : ℝ) ≤ 1 - initial.time) :
    0 ≤ principalQMassImage M
      (path.mass 1 - path.absorptionPlayerPath weight hinitialOne time) who := by
  let split := 1 - initial.time
  have hsplitPos : 0 < split := sub_pos.mpr hinitialOne
  have hsplitOne : split < 1 := by
    dsimp [split]
    linarith [initial.time_pos]
  let clock := unitInterval.symm
    (Path.transAtLeftParameter hsplitPos time htime)
  have hremaining :
      path.mass 1 - path.absorptionPlayerPath weight hinitialOne time =
        path.mass clock := by
    rw [PrincipalQClockMassPath.absorptionPlayerPath,
      Path.transAt_apply_leftParameter _ _ hsplitPos hsplitOne time htime,
      path.absorptionPrefixPath_apply]
    dsimp [clock]
    have hcancel : path.mass 1 -
        (path.mass 1 - path.mass
          (unitInterval.symm
            (Path.transAtLeftParameter hsplitPos time htime))) =
          path.mass
            (unitInterval.symm
              (Path.transAtLeftParameter hsplitPos time htime)) := by
      abel
    exact hcancel
  rw [hremaining]
  have hstate := path.scaledState_mem clock |>.1 who
  rw [hscaledInitial, zero_add] at hstate
  exact hstate

omit [DecidableEq ι] in
/-- A compact limit of the canonical approximations has nonnegative
singleton-matrix residual at every time.  The only approximation error is
the vanishing terminal filler. -/
theorem exists_principalQAbsorptionPlayerPath_limit_residual_nonneg
    [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (weight : stdSimplex ℝ ι) :
    ∃ terminal : ι → ℝ, ∃ limitPath : Path (0 : ι → ℝ) terminal,
      (∀ who, Monotone fun time => limitPath time who) ∧
      (∀ time, ∑ who, limitPath time who = (time : ℝ)) ∧
      ∀ time who,
        0 ≤ ∑ owner, (limitPath 1 owner - limitPath time owner) * M who owner := by
  obtain ⟨terminal, limitPath, subsequence, hsubsequence, htendsto,
      hmono, htotal⟩ :=
    exists_principalQAbsorptionPlayerPath_limit M hdiag hQ weight
  refine ⟨terminal, limitPath, hmono, htotal, ?_⟩
  intro time who
  by_cases htimeOne : time = 1
  · subst time
    simp
  have htimeLt : (time : ℝ) < 1 :=
    lt_of_le_of_ne time.property.2 fun heq => htimeOne (Subtype.ext heq)
  have hmassAt (parameter : unitInterval) : Tendsto
      (fun n => principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence n) parameter) atTop
      (nhds (limitPath parameter)) := by
    exact ((BoundedContinuousFunction.lipschitz_eval_const parameter).continuous
      |>.tendsto (boundedFunctionOfPath limitPath)).comp htendsto
  have hresidual : Tendsto
      (fun n => ∑ owner,
        (principalQVanishingPlayerPath M hdiag hQ weight (subsequence n) 1 owner -
          principalQVanishingPlayerPath M hdiag hQ weight
            (subsequence n) time owner) * M who owner) atTop
      (nhds (∑ owner,
        (limitPath 1 owner - limitPath time owner) * M who owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact ((((continuous_apply owner).tendsto _).comp (hmassAt 1)).sub
      (((continuous_apply owner).tendsto _).comp (hmassAt time))).mul_const _
  have hscale : Tendsto
      (fun n => principalQVanishingScale (subsequence n)) atTop (nhds 0) :=
    tendsto_principalQVanishingScale.comp hsubsequence.tendsto_atTop
  have hscaleError : Tendsto
      (fun n => principalQVanishingScale (subsequence n) *
        principalQMassImage M (weight : ι → ℝ) who) atTop (nhds 0) := by
    simpa using hscale.mul_const (principalQMassImage M (weight : ι → ℝ) who)
  have heventuallyPrefix : ∀ᶠ n in atTop,
      (time : ℝ) ≤ 1 - principalQVanishingScale (subsequence n) := by
    have hsmall := hscale.eventually_lt_const (sub_pos.mpr htimeLt)
    filter_upwards [hsmall] with n hn
    linarith
  have heventuallyBound : ∀ᶠ n in atTop,
      principalQVanishingScale (subsequence n) *
          principalQMassImage M (weight : ι → ℝ) who ≤
        ∑ owner,
          (principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence n) 1 owner -
            principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence n) time owner) * M who owner := by
    filter_upwards [heventuallyPrefix] with n hprefix
    let approximation :=
      principalQVanishingApproximation M hdiag hQ (subsequence n)
    have hnonneg := approximation.mass.principalQMassImage_remaining_nonneg
      weight approximation.start_lt_one
      (zeroPrincipalQClockNode_scaledState _ _) who time hprefix
    have hdecompose :
        ∑ owner,
          (principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence n) 1 owner -
            principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence n) time owner) * M who owner =
          principalQMassImage M
              (approximation.mass.mass 1 -
                approximation.mass.absorptionPlayerPath weight
                  approximation.start_lt_one time) who +
            principalQVanishingScale (subsequence n) *
              principalQMassImage M (weight : ι → ℝ) who := by
      rw [(principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence n)).target]
      change (∑ owner,
        ((approximation.mass.mass 1 +
            principalQVanishingScale (subsequence n) • (weight : ι → ℝ)) owner -
          approximation.mass.absorptionPlayerPath weight
            approximation.start_lt_one time owner) * M who owner) = _
      unfold principalQMassImage
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro owner _
      ring
    rw [hdecompose]
    exact le_add_of_nonneg_left hnonneg
  exact le_of_tendsto_of_tendsto hscaleError hresidual heventuallyBound

/-- Projective-Q-bar compactification supplies a continuous singleton path
satisfying the lower continuous sequential-perfection inequality SP.2(a). -/
theorem exists_continuousAbsorptionPath_sp2a_of_projectiveQBar
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hQ : IsProjectiveQBarMatrix (normalizedSoloMatrix reward)) :
    ∃ path : AbsorptionPath (ι := ι),
      IsContinuousAbsorptionPath path ∧
      ∀ who t, t ∈ pathTimes path.1 → t ≠ 1 →
        reward (quittingProjectiveSingletonTerminal who) who ≤
          absorptionPathPayoff reward path t who := by
  let owner : ι := Classical.choice inferInstance
  let weight : stdSimplex ℝ ι := stdSimplex.pure owner
  obtain ⟨terminal, limitPath, hmono, htotal, hresidual⟩ :=
    exists_principalQAbsorptionPlayerPath_limit_residual_nonneg
      (normalizedSoloMatrix reward) (normalizedSoloMatrix_diagonal reward)
      hQ weight
  let path : AbsorptionPath (ι := ι) :=
    singletonAbsorptionPathOfPlayerPath limitPath hmono htotal
  refine ⟨path,
    singletonAbsorptionPathOfPlayerPath_continuous limitPath hmono htotal,
    ?_⟩
  intro who t ht htOne
  have htIcc : t ∈ Icc (0 : ℝ) 1 := by
    rw [← pathTimes_singletonCadlagPathOfPlayerPath limitPath hmono htotal]
    exact ht
  let time : unitInterval := ⟨t, htIcc⟩
  have htimeOne : time ≠ 1 := by
    intro heq
    apply htOne
    exact congrArg Subtype.val heq
  have hres := hresidual time who
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at hres
  have hidentity := one_sub_mul_absorptionPathPayoff_sub_solo
    limitPath hmono htotal reward time htimeOne who
  change reward (quittingProjectiveSingletonTerminal who) who ≤
    absorptionPathPayoff reward path (time : ℝ) who
  change (1 - (time : ℝ)) *
      (absorptionPathPayoff reward path (time : ℝ) who -
        reward (quittingProjectiveSingletonTerminal who) who) = _ at hidentity
  have hdenom : 0 < 1 - (time : ℝ) := by
    exact sub_pos.mpr (lt_of_le_of_ne time.property.2 fun heq =>
      htimeOne (Subtype.ext heq))
  rw [← hidentity] at hres
  nlinarith

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

omit [DecidableEq ι] in
/-- A strict player-mass increase on a subterminal interval of a compact
limit has an in-interval point where that player's limiting singleton-matrix
residual is nonpositive. -/
theorem exists_limit_residual_nonpos_of_playerMass_increase
    [Nonempty ι]
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (weight : stdSimplex ℝ ι)
    {terminal : ι → ℝ} (limitPath : Path (0 : ι → ℝ) terminal)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (htendsto : Tendsto (fun n => boundedFunctionOfPath
      (principalQVanishingPlayerPath M hdiag hQ weight (subsequence n)))
        atTop (nhds (boundedFunctionOfPath limitPath)))
    (who : ι) (first second : unitInterval) (hle : first ≤ second)
    (hsecondOne : (second : ℝ) < 1)
    (hincrease : limitPath first who < limitPath second who) :
    ∃ witness ∈ Icc first second,
      ∑ owner, (limitPath 1 owner - limitPath witness owner) * M who owner ≤ 0 := by
  have hmassAt (parameter : unitInterval) : Tendsto
      (fun n => principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence n) parameter) atTop
      (nhds (limitPath parameter)) := by
    exact ((BoundedContinuousFunction.lipschitz_eval_const parameter).continuous
      |>.tendsto (boundedFunctionOfPath limitPath)).comp htendsto
  have hfirst : Tendsto
      (fun n => principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence n) first who) atTop (nhds (limitPath first who)) :=
    ((continuous_apply who).tendsto _).comp (hmassAt first)
  have hsecond : Tendsto
      (fun n => principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence n) second who) atTop (nhds (limitPath second who)) :=
    ((continuous_apply who).tendsto _).comp (hmassAt second)
  have hscale : Tendsto
      (fun n => principalQVanishingScale (subsequence n)) atTop (nhds 0) :=
    tendsto_principalQVanishingScale.comp hsubsequence.tendsto_atTop
  have heventuallyPrefix : ∀ᶠ n in atTop,
      (second : ℝ) ≤ 1 - principalQVanishingScale (subsequence n) := by
    have hsmall := hscale.eventually_lt_const (sub_pos.mpr hsecondOne)
    filter_upwards [hsmall] with n hn
    linarith
  have heventuallyIncrease : ∀ᶠ n in atTop,
      principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence n) first who <
        principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence n) second who :=
    hfirst.eventually_lt hsecond hincrease
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    (heventuallyPrefix.and heventuallyIncrease)
  let tailIndex : ℕ → ℕ := fun n => start + n
  have htailIndex : StrictMono tailIndex := by
    intro a b hab
    dsimp [tailIndex]
    omega
  have hprefix (n : ℕ) : (second : ℝ) ≤
      1 - principalQVanishingScale (subsequence (tailIndex n)) :=
    (hstart (tailIndex n) (by simp [tailIndex])).1
  have hincreaseApprox (n : ℕ) :
      principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence (tailIndex n)) first who <
        principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence (tailIndex n)) second who :=
    (hstart (tailIndex n) (by simp [tailIndex])).2
  let approximation (n : ℕ) :=
    principalQVanishingApproximation M hdiag hQ (subsequence (tailIndex n))
  choose witness hwitnessInterval hwitnessBound using fun n =>
    (approximation n).mass.exists_absorptionPrefix_meshSupport_witness
      weight (approximation n).start_lt_one (approximation n).node_time
      (approximation n).mesh_supported who first second hle (hprefix n)
      (hincreaseApprox n)
  obtain ⟨witnessLimit, witnessSubsequence, hwitnessSubsequence,
      hwitnessTendsto⟩ := CompactSpace.tendsto_subseq witness
  let index : ℕ → ℕ := fun n => tailIndex (witnessSubsequence n)
  have hindex : StrictMono index := htailIndex.comp hwitnessSubsequence
  have hmassIndex : Tendsto
      (fun n => boundedFunctionOfPath
        (principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence (index n)))) atTop
      (nhds (boundedFunctionOfPath limitPath)) :=
    htendsto.comp hindex.tendsto_atTop
  have hmassWitness : Tendsto
      (fun n => principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence (index n)) (witness (witnessSubsequence n))) atTop
      (nhds (limitPath witnessLimit)) := by
    have hpair : Tendsto
        (fun n => (boundedFunctionOfPath
            (principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence (index n))),
          witness (witnessSubsequence n))) atTop
        (nhds (boundedFunctionOfPath limitPath, witnessLimit)) := by
      rw [nhds_prod_eq]
      exact hmassIndex.prodMk hwitnessTendsto
    have := (continuous_eval.tendsto
      (boundedFunctionOfPath limitPath, witnessLimit)).comp hpair
    change Tendsto
      (fun n => boundedFunctionOfPath
        (principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence (index n))) (witness (witnessSubsequence n))) atTop
      (nhds (boundedFunctionOfPath limitPath witnessLimit))
    simpa only [Function.comp_def] using this
  have hresidual : Tendsto
      (fun n => ∑ owner,
        (principalQVanishingPlayerPath M hdiag hQ weight
            (subsequence (index n)) 1 owner -
          principalQVanishingPlayerPath M hdiag hQ weight
            (subsequence (index n))
              (witness (witnessSubsequence n)) owner) * M who owner) atTop
      (nhds (∑ owner,
        (limitPath 1 owner - limitPath witnessLimit owner) * M who owner)) := by
    have hmassOne : Tendsto
        (fun n => principalQVanishingPlayerPath M hdiag hQ weight
          (subsequence (index n)) 1) atTop (nhds (limitPath 1)) := by
      exact ((BoundedContinuousFunction.lipschitz_eval_const 1).continuous
        |>.tendsto (boundedFunctionOfPath limitPath)).comp hmassIndex
    apply tendsto_finsetSum
    intro owner _
    exact ((((continuous_apply owner).tendsto _).comp hmassOne).sub
      (((continuous_apply owner).tendsto _).comp hmassWitness)).mul_const _
  have hscaleIndex : Tendsto
      (fun n => principalQVanishingScale (subsequence (index n))) atTop
      (nhds 0) :=
    tendsto_principalQVanishingScale.comp
      (hsubsequence.comp hindex).tendsto_atTop
  have hwitnessReal : Tendsto
      (fun n => (witness (witnessSubsequence n) : ℝ)) atTop
      (nhds (witnessLimit : ℝ)) :=
    (continuous_subtype_val.tendsto witnessLimit).comp hwitnessTendsto
  let error (n : ℕ) :=
    principalQMatrixSpeedBound M *
        (1 - (witness (witnessSubsequence n) : ℝ)) *
          principalQVanishingScale (subsequence (index n)) +
      principalQVanishingScale (subsequence (index n)) *
        principalQMassImage M (weight : ι → ℝ) who
  have herror : Tendsto error atTop (nhds 0) := by
    dsimp [error]
    convert ((tendsto_const_nhds.mul
      (tendsto_const_nhds.sub hwitnessReal)).mul hscaleIndex).add
        (hscaleIndex.mul_const
          (principalQMassImage M (weight : ι → ℝ) who)) using 1
    ring_nf
  have hbound (n : ℕ) :
      (∑ owner,
        (principalQVanishingPlayerPath M hdiag hQ weight
            (subsequence (index n)) 1 owner -
          principalQVanishingPlayerPath M hdiag hQ weight
            (subsequence (index n))
              (witness (witnessSubsequence n)) owner) * M who owner) ≤
        error n := by
    have hs := hwitnessBound (witnessSubsequence n)
    rw [zeroPrincipalQClockNode_scaledState, zero_add] at hs
    have hdecompose :
        ∑ owner,
          (principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence (index n)) 1 owner -
            principalQVanishingPlayerPath M hdiag hQ weight
              (subsequence (index n))
                (witness (witnessSubsequence n)) owner) * M who owner =
          principalQMassImage M
              ((approximation (witnessSubsequence n)).mass.mass 1 -
                (approximation (witnessSubsequence n)).mass.absorptionPlayerPath
                  weight (approximation (witnessSubsequence n)).start_lt_one
                  (witness (witnessSubsequence n))) who +
            principalQVanishingScale (subsequence (index n)) *
              principalQMassImage M (weight : ι → ℝ) who := by
      rw [(principalQVanishingPlayerPath M hdiag hQ weight
        (subsequence (index n))).target]
      change (∑ owner,
        (((approximation (witnessSubsequence n)).mass.mass 1 +
            principalQVanishingScale (subsequence (index n)) •
              (weight : ι → ℝ)) owner -
          (approximation (witnessSubsequence n)).mass.absorptionPlayerPath
            weight (approximation (witnessSubsequence n)).start_lt_one
            (witness (witnessSubsequence n)) owner) * M who owner) = _
      unfold principalQMassImage
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro owner _
      ring
    let base :=
      principalQMassImage M
        ((approximation (witnessSubsequence n)).mass.mass 1 -
          (approximation (witnessSubsequence n)).mass.absorptionPlayerPath
            weight (approximation (witnessSubsequence n)).start_lt_one
            (witness (witnessSubsequence n))) who
    let filler := principalQVanishingScale (subsequence (index n)) *
      principalQMassImage M (weight : ι → ℝ) who
    have hs' :
        base ≤
          principalQMatrixSpeedBound M *
            (1 - (witness (witnessSubsequence n) : ℝ)) *
              principalQVanishingScale (subsequence (index n)) := by
      simpa only [base, approximation, index] using hs
    calc
      _ = base + filler := by simpa only [base, filler] using hdecompose
      _ = filler + base := add_comm _ _
      _ ≤ filler + principalQMatrixSpeedBound M *
          (1 - (witness (witnessSubsequence n) : ℝ)) *
            principalQVanishingScale (subsequence (index n)) :=
        add_le_add_right hs' filler
      _ = error n := by dsimp [error, filler]; ring
  refine ⟨witnessLimit, ?_, ?_⟩
  · exact isClosed_Icc.mem_of_tendsto hwitnessTendsto
      (Eventually.of_forall fun n => hwitnessInterval (witnessSubsequence n))
  · exact le_of_tendsto_of_tendsto' hresidual herror hbound

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
