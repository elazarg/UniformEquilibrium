/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Convex.PathConnected
import UniformEquilibrium.Quitting.AbsorptionPath.ContinuousPath
import UniformEquilibrium.Quitting.Projective.SingletonLCP

/-!
# Continuous singleton absorption paths

A coordinatewise monotone path of player masses whose total is the clock
canonically defines a continuous absorption path supported on singleton
quitting coalitions.  This is the reusable semantic adapter from cumulative
player controls to absorption paths.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Finset Set unitInterval
open GameTheory
open scoped Topology unitInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Push an arbitrary player-mass vector onto singleton quitting coalitions. -/
def singletonCoalitionMass (mass : ι → ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ owner, if coalition = quittingProjectiveSingletonTerminal owner then
    mass owner else 0

@[simp] theorem singletonCoalitionMass_singleton
    (mass : ι → ℝ) (who : ι) :
    singletonCoalitionMass mass (quittingProjectiveSingletonTerminal who) =
      mass who := by
  unfold singletonCoalitionMass
  rw [Finset.sum_eq_single who]
  · simp
  · intro owner _ hne
    have hcoalition : quittingProjectiveSingletonTerminal who ≠
        quittingProjectiveSingletonTerminal owner := by
      intro heq
      apply hne
      have heq' : who = owner := by
        simpa [quittingProjectiveSingletonTerminal] using
          congrArg (fun S => S.1) heq
      exact heq'.symm
    simp [hcoalition]
  · simp

theorem singletonCoalitionMass_eq_zero_of_card_ne_one
    (mass : ι → ℝ) (coalition : {S : Finset ι // S.Nonempty})
    (hcard : coalition.1.card ≠ 1) :
    singletonCoalitionMass mass coalition = 0 := by
  unfold singletonCoalitionMass
  apply Finset.sum_eq_zero
  intro owner _
  have hne : coalition ≠ quittingProjectiveSingletonTerminal owner := by
    intro heq
    apply hcard
    rw [congrArg (fun S => S.1.card) heq]
    simp [quittingProjectiveSingletonTerminal]
  simp [hne]

theorem sum_singletonCoalitionMass (mass : ι → ℝ) :
    ∑ coalition, singletonCoalitionMass mass coalition = ∑ who, mass who := by
  simp only [singletonCoalitionMass]
  rw [Finset.sum_comm]
  simp

/-- Extend a player-mass path to real time and place every coordinate on its
singleton quitting coalition. -/
def singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    CadlagPath (ι := ι) where
  value time coalition := singletonCoalitionMass (mass.extend time) coalition
  leftValue time coalition :=
    singletonCoalitionMass (mass.extend time) coalition
  value_mem := by
    intro time htime coalition
    let clock : unitInterval := ⟨time, htime⟩
    have hnonneg (who : ι) : 0 ≤ mass.extend time who := by
      rw [show mass.extend time = mass clock from Path.extend_apply mass htime]
      simpa only [mass.source, Pi.zero_apply] using
        hmono who (show (0 : unitInterval) ≤ clock from clock.property.1)
    constructor
    · unfold singletonCoalitionMass
      exact Finset.sum_nonneg fun who _ => by
        split <;> simp_all
    · by_cases hcard : coalition.1.card = 1
      · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hcard
        have hcoalition : coalition =
            quittingProjectiveSingletonTerminal owner := by
          apply Subtype.ext
          simpa [quittingProjectiveSingletonTerminal] using howner
        rw [hcoalition, singletonCoalitionMass_singleton]
        calc
          mass.extend time owner ≤ ∑ who, mass.extend time who :=
            Finset.single_le_sum (fun who _ => hnonneg who)
              (Finset.mem_univ owner)
          _ = time := by
            rw [show mass.extend time = mass clock from
              Path.extend_apply mass htime, htotal]
          _ ≤ 1 := htime.2
      · rw [singletonCoalitionMass_eq_zero_of_card_ne_one _ coalition hcard]
        exact zero_le_one
  monotone := by
    intro coalition first hfirst second hsecond hle
    let firstClock : unitInterval := ⟨first, hfirst⟩
    let secondClock : unitInterval := ⟨second, hsecond⟩
    unfold singletonCoalitionMass
    apply Finset.sum_le_sum
    intro who _
    split_ifs
    · rw [show mass.extend first = mass firstClock from
          Path.extend_apply mass hfirst,
        show mass.extend second = mass secondClock from
          Path.extend_apply mass hsecond]
      exact hmono who hle
    · exact le_rfl
  right_continuous := by
    intro coalition time _
    have hcontinuous : Continuous
        (fun s => singletonCoalitionMass (mass.extend s) coalition) := by
      unfold singletonCoalitionMass
      apply continuous_finsetSum
      intro owner _
      split_ifs <;> fun_prop
    exact hcontinuous.continuousAt.tendsto.mono_left inf_le_left
  left_limit := by
    intro coalition time _
    have hcontinuous : Continuous
        (fun s => singletonCoalitionMass (mass.extend s) coalition) := by
      unfold singletonCoalitionMass
      apply continuous_finsetSum
      intro owner _
      split_ifs <;> fun_prop
    exact hcontinuous.continuousAt.tendsto.mono_left inf_le_left
  left_zero := by
    simp [singletonCoalitionMass]

@[simp] theorem pathTotal_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    {time : ℝ} (htime : time ∈ Icc (0 : ℝ) 1) :
    pathTotal (singletonCadlagPathOfPlayerPath mass hmono htotal) time =
      time := by
  let clock : unitInterval := ⟨time, htime⟩
  rw [pathTotal]
  change ∑ coalition, singletonCoalitionMass (mass.extend time) coalition = _
  rw [sum_singletonCoalitionMass,
    show mass.extend time = mass clock from Path.extend_apply mass htime,
    htotal]

@[simp] theorem pathJump_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    (time : ℝ) (coalition : {S : Finset ι // S.Nonempty}) :
    pathJump (singletonCadlagPathOfPlayerPath mass hmono htotal)
      time coalition = 0 := by
  simp [pathJump, singletonCadlagPathOfPlayerPath]

theorem pathTimes_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    pathTimes (singletonCadlagPathOfPlayerPath mass hmono htotal) =
      Set.Icc 0 1 := by
  ext time
  simp only [pathTimes, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.1
  · intro htime
    exact ⟨htime,
      pathTotal_singletonCadlagPathOfPlayerPath mass hmono htotal htime⟩

theorem pathJumps_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    pathJumps (singletonCadlagPathOfPlayerPath mass hmono htotal) = ∅ := by
  ext time
  simp [pathJumps]

private theorem pathRightDerivative_singletonCadlagPathOfPlayerPath_eq_zero
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ))
    {time : ℝ} (htime : time < 1)
    (coalition : {S : Finset ι // S.Nonempty})
    (hcard : coalition.1.card ≠ 1) :
    pathRightDerivative
        (singletonCadlagPathOfPlayerPath mass hmono htotal)
        time coalition = 0 := by
  letI : NeBot (nhdsWithin time (Set.Ioo time 1)) :=
    left_nhdsWithin_Ioo_neBot htime
  unfold pathRightDerivative
  have hzero (s : ℝ) :
      (singletonCadlagPathOfPlayerPath mass hmono htotal).value
        s coalition = 0 :=
    singletonCoalitionMass_eq_zero_of_card_ne_one _ coalition hcard
  simp_rw [hzero]
  simp only [sub_self, zero_div]
  exact Filter.liminf_const (f := nhdsWithin time (Set.Ioo time 1)) 0

/-- A monotone player-mass path with total equal to time satisfies all four
absorption-path axioms. -/
theorem isAbsorptionPath_singletonCadlagPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    IsAbsorptionPath
      (singletonCadlagPathOfPlayerPath mass hmono htotal) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro time htime
    rw [pathTotal_singletonCadlagPathOfPlayerPath mass hmono htotal htime]
  · intro time htime
    have hpathTime : time ∈ pathTimes
        (singletonCadlagPathOfPlayerPath mass hmono htotal) := by
      rw [pathTimes_singletonCadlagPathOfPlayerPath mass hmono htotal]
      exact htime.1
    exact (htime.2 (Or.inr hpathTime)).elim
  · intro time htime
    rw [pathJumps_singletonCadlagPathOfPlayerPath mass hmono htotal] at htime
    exact htime.elim
  · intro time htime hneOne coalition hderivative
    by_contra hcard
    apply hderivative
    exact pathRightDerivative_singletonCadlagPathOfPlayerPath_eq_zero
      mass hmono htotal (lt_of_le_of_ne htime.1.2 hneOne)
      coalition hcard

/-- The bundled continuous singleton absorption path associated with a
player-mass path. -/
def singletonAbsorptionPathOfPlayerPath
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    AbsorptionPath (ι := ι) :=
  ⟨singletonCadlagPathOfPlayerPath mass hmono htotal,
    isAbsorptionPath_singletonCadlagPathOfPlayerPath mass hmono htotal⟩

/-- The singleton absorption path induced by a player-mass path is
continuous. -/
theorem singletonAbsorptionPathOfPlayerPath_continuous
    {terminal : ι → ℝ} (mass : Path (0 : ι → ℝ) terminal)
    (hmono : ∀ who, Monotone fun time => mass time who)
    (htotal : ∀ time, ∑ who, mass time who = (time : ℝ)) :
    IsContinuousAbsorptionPath
      (singletonAbsorptionPathOfPlayerPath mass hmono htotal) :=
  pathTimes_singletonCadlagPathOfPlayerPath mass hmono htotal

end GameTheory.QuittingAbsorptionPath
