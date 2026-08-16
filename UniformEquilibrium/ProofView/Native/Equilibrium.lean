/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Stochastic.Uniform
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Uniform
import UniformEquilibrium.ProofView.Native.Semantics

/-!
# Uniform-equilibrium equivalence with native GameTheory

For finite states and actions, the PMF proof view and GameTheory's canonical
finite-support Protocol runner have exactly the same finite-horizon Nash and
uniform-payoff predicates. Arbitrary native unilateral behavioral policies are
included through the lossless public-policy equivalence.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

namespace StochasticGame.NativeBridge

variable {ι : Type} (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

omit [Fintype ι] in
/-- Updating a proof-view profile and then compiling it is pointwise the
native public-profile update. -/
theorem toNativePublicProfile_update
    (initial : G.State) (profile : G.BehaviorProfile) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    toNativePublicProfile G initial (Function.update profile who deviation) =
      Profile.update (toNativePublicProfile G initial profile) who
        (toNativePublicPolicy G initial deviation) := by
  funext i
  by_cases hi : i = who
  · subst i
    simp [toNativePublicProfile]
  · simp [toNativePublicProfile, Function.update_of_ne,
      Profile.update_of_ne, hi]

omit [Fintype ι] in
/-- A native profile update agrees on coherent histories with the compiled
update of its decoded proof-view profile. -/
theorem toNativePublicProfile_update_ofNative_agrees
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    (who : ι) (deviation : G.toNative.PublicPolicy who) :
    ∀ i history, IsCoherentPublicHistory G initial history →
      toNativePublicProfile G initial
          (Function.update (ofNativePublicProfile G initial profile) who
            (ofNativePublicPolicy G deviation)) i history =
        Profile.update profile who deviation i history := by
  intro i history hcoherent
  by_cases hi : i = who
  · subst i
    simp only [toNativePublicProfile, Profile.update,
      Function.update_self]
    exact toNativePublicPolicy_ofNativePublicPolicy_of_coherent
      G initial deviation history hcoherent
  · simp only [toNativePublicProfile, Profile.update,
      Function.update_of_ne hi]
    exact toNativePublicProfile_ofNativePublicProfile_of_coherent
      G initial profile i history hcoherent

omit [Fintype ι] in
/-- Replacing one proof-view strategy by a decoded native deviation and
recompiling agrees with replacing the corresponding native policy on coherent
histories. -/
theorem toNativePublicProfile_update_ofNativeDeviation_agrees
    (initial : G.State) (profile : G.BehaviorProfile)
    (who : ι) (deviation : G.toNative.PublicPolicy who) :
    ∀ i history, IsCoherentPublicHistory G initial history →
      toNativePublicProfile G initial
          (Function.update profile who (ofNativePublicPolicy G deviation))
          i history =
        Profile.update (toNativePublicProfile G initial profile) who deviation
          i history := by
  intro i history hcoherent
  by_cases hi : i = who
  · subst i
    simp only [toNativePublicProfile, Function.update_self,
      Profile.update_same]
    exact toNativePublicPolicy_ofNativePublicPolicy_of_coherent
      G initial deviation history hcoherent
  · simp [toNativePublicProfile, Function.update_of_ne, Profile.update_of_ne,
      hi]

omit [Fintype ι] in
/-- Replacing one decoded native policy by a proof-view deviation and
recompiling agrees with the corresponding native update on coherent
histories. -/
theorem toNativePublicProfile_update_ofProofViewDeviation_agrees
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    ∀ i history, IsCoherentPublicHistory G initial history →
      toNativePublicProfile G initial
          (Function.update (ofNativePublicProfile G initial profile) who
            deviation) i history =
        Profile.update profile who (toNativePublicPolicy G initial deviation)
          i history := by
  intro i history hcoherent
  by_cases hi : i = who
  · subst i
    simp [toNativePublicProfile]
  · simp only [toNativePublicProfile, Profile.update,
      Function.update_of_ne hi]
    exact toNativePublicProfile_ofNativePublicProfile_of_coherent
      G initial profile i history hcoherent

omit [Fintype ι] in
/-- The native behavioral update corresponding to a proof-view deviation is
the compiled public-profile update. -/
theorem toNativeBehaviorProfile_update
    (initial : G.State) (profile : G.BehaviorProfile) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    Profile.update (toNativeBehaviorProfile G initial profile) who
        (G.toNative.toBehavioralPolicy initial
          (toNativePublicPolicy G initial deviation)) =
      G.toNative.toBehaviorProfile initial
        (Profile.update (toNativePublicProfile G initial profile) who
          (toNativePublicPolicy G initial deviation)) := by
  change Profile.update
      (G.toNative.toBehaviorProfile initial
        (toNativePublicProfile G initial profile)) who
      (G.toNative.toBehavioralPolicy initial
        (toNativePublicPolicy G initial deviation)) = _
  rw [← G.toNative.toBehaviorProfile_update]

/-- Native approximate Nash for public policies is exactly approximate Nash
for their decoded proof view. -/
theorem isεHorizonNash_publicProfile_iff
    (initial : G.State) (horizon : ℕ) (epsilon : ℝ)
    (profile : G.toNative.PublicProfile initial) :
    G.toNative.IsεHorizonNash initial horizon epsilon
        (G.toNative.toBehaviorProfile initial profile) ↔
      G.IsεHorizonNash initial horizon epsilon
        (ofNativePublicProfile G initial profile) := by
  constructor
  · intro hnative who deviation
    let publicDeviation := toNativePublicPolicy G initial deviation
    have hbound := (G.toNative.isεHorizonNash_iff initial horizon epsilon
      (G.toNative.toBehaviorProfile initial profile)).mp hnative who
        (G.toNative.toBehavioralPolicy initial publicDeviation)
    have hagree := toNativePublicProfile_update_ofProofViewDeviation_agrees
      G initial profile who deviation
    rw [← G.toNative.toBehaviorProfile_update,
      native_finiteAveragePayoff_eq_of_coherent G initial
        (Function.update (ofNativePublicProfile G initial profile) who
          deviation)
        (Profile.update profile who publicDeviation) hagree horizon who,
      native_finiteAveragePayoff_eq_of_publicProfile G initial profile
        horizon who] at hbound
    exact hbound
  · intro hold
    rw [G.toNative.isεHorizonNash_iff]
    intro who nativeDeviation
    let publicDeviation :=
      G.toNative.ofBehavioralPolicy initial nativeDeviation
    let proofDeviation := ofNativePublicPolicy G publicDeviation
    have hbehavioral :
        Profile.update (G.toNative.toBehaviorProfile initial profile) who
            nativeDeviation =
          G.toNative.toBehaviorProfile initial
            (Profile.update profile who publicDeviation) := by
      simpa [publicDeviation] using
        (G.toNative.toBehaviorProfile_update initial profile who
          publicDeviation).symm
    have hagree := toNativePublicProfile_update_ofNative_agrees
      G initial profile who publicDeviation
    have holdBound := hold who proofDeviation
    rw [hbehavioral,
      native_finiteAveragePayoff_eq_of_coherent G initial
        (Function.update (ofNativePublicProfile G initial profile) who
          proofDeviation)
        (Profile.update profile who publicDeviation) hagree horizon who,
      native_finiteAveragePayoff_eq_of_publicProfile G initial profile
        horizon who]
    exact holdBound

/-- Finite-horizon approximate Nash is invariant under native compilation. -/
theorem isεHorizonNash_toNative_iff
    (initial : G.State) (horizon : ℕ) (epsilon : ℝ)
    (profile : G.BehaviorProfile) :
    G.toNative.IsεHorizonNash initial horizon epsilon
        (toNativeBehaviorProfile G initial profile) ↔
      G.IsεHorizonNash initial horizon epsilon profile := by
  constructor
  · intro hnative who deviation
    let publicDeviation := toNativePublicPolicy G initial deviation
    have hbound := (G.toNative.isεHorizonNash_iff initial horizon epsilon
      (toNativeBehaviorProfile G initial profile)).mp hnative who
        (G.toNative.toBehavioralPolicy initial publicDeviation)
    have hagree : ∀ i history,
        IsCoherentPublicHistory G initial history →
        toNativePublicProfile G initial
            (Function.update profile who deviation) i history =
          Profile.update (toNativePublicProfile G initial profile) who
            publicDeviation i history := by
      intro i history _
      rw [toNativePublicProfile_update]
    rw [toNativeBehaviorProfile_update G initial profile who deviation,
      native_finiteAveragePayoff_eq_of_coherent G initial
        (Function.update profile who deviation)
        (Profile.update (toNativePublicProfile G initial profile) who
          publicDeviation) hagree horizon who,
      native_finiteAveragePayoff_eq G profile initial horizon who] at hbound
    exact hbound
  · intro hold
    rw [G.toNative.isεHorizonNash_iff]
    intro who nativeDeviation
    let publicProfile := toNativePublicProfile G initial profile
    let publicDeviation :=
      G.toNative.ofBehavioralPolicy initial nativeDeviation
    let proofDeviation := ofNativePublicPolicy G publicDeviation
    have hbehavioral :
        Profile.update (toNativeBehaviorProfile G initial profile) who
            nativeDeviation =
          G.toNative.toBehaviorProfile initial
            (Profile.update publicProfile who publicDeviation) := by
      simpa [toNativeBehaviorProfile, publicProfile, publicDeviation] using
        (G.toNative.toBehaviorProfile_update initial publicProfile who
          publicDeviation).symm
    have hagree := toNativePublicProfile_update_ofNativeDeviation_agrees
      G initial profile who publicDeviation
    have holdBound := hold who proofDeviation
    rw [hbehavioral,
      native_finiteAveragePayoff_eq_of_coherent G initial
        (Function.update profile who proofDeviation)
        (Profile.update publicProfile who publicDeviation) hagree horizon who,
      native_finiteAveragePayoff_eq G profile initial horizon who]
    exact holdBound

/-- The native and proof-view definitions of a uniform-equilibrium payoff are
exactly equivalent. -/
theorem isUniformEquilibriumPayoff_toNative_iff
    (initial : G.State) (value : ι → ℝ) :
    G.toNative.IsUniformEquilibriumPayoff initial value ↔
      G.IsUniformEquilibriumPayoff initial value := by
  constructor
  · intro hnative epsilon hepsilon
    obtain ⟨nativeProfile, threshold, hprofile⟩ :=
      hnative epsilon hepsilon
    let publicProfile :=
      G.toNative.ofBehaviorProfile initial nativeProfile
    let proofProfile := ofNativePublicProfile G initial publicProfile
    refine ⟨proofProfile, threshold, fun horizon hhorizon => ?_⟩
    obtain ⟨hnash, hpayoff⟩ := hprofile horizon hhorizon
    have hroundtrip :
        G.toNative.toBehaviorProfile initial publicProfile = nativeProfile := by
      exact G.toNative.toBehaviorProfile_ofBehaviorProfile initial nativeProfile
    constructor
    · apply (isεHorizonNash_publicProfile_iff G initial horizon epsilon
        publicProfile).mp
      rwa [hroundtrip]
    · intro who
      rw [← native_finiteAveragePayoff_eq_of_publicProfile G initial
        publicProfile horizon who, hroundtrip]
      exact hpayoff who
  · intro hold epsilon hepsilon
    obtain ⟨profile, threshold, hprofile⟩ := hold epsilon hepsilon
    refine ⟨toNativeBehaviorProfile G initial profile, threshold,
      fun horizon hhorizon => ?_⟩
    obtain ⟨hnash, hpayoff⟩ := hprofile horizon hhorizon
    constructor
    · exact (isεHorizonNash_toNative_iff G initial horizon epsilon
        profile).mpr hnash
    · intro who
      rw [native_finiteAveragePayoff_eq G profile initial horizon who]
      exact hpayoff who

end StochasticGame.NativeBridge

end GameTheory
