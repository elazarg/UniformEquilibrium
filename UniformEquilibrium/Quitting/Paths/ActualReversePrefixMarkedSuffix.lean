import UniformEquilibrium.Quitting.Paths.LiveRootSurvival
import UniformEquilibrium.Quitting.Paths.ReversePrefixStoppingLaw
import UniformEquilibrium.Quitting.Root.NestedCapChildFixedDebtor

/-!
# Literal suffix preservation under reverse prefixes

The complete continuation profile and its live roots are unchanged after the
prefix. Their entry and later live masses acquire the exact prefix survival factor.
-/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem quittingAllContinueProfileSpine_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (first second : ℕ) :
    quittingAllContinueProfileSpine reward profile (first + second) =
      quittingAllContinueProfileSpine reward
        (quittingAllContinueProfileSpine reward profile first) second := by
  induction second with
  | zero => simp [quittingAllContinueProfileSpine]
  | succ second ih =>
      rw [Nat.add_succ]
      simp only [quittingAllContinueProfileSpine]
      rw [ih]

omit [DecidableEq ι] in
/-- Conditional on surviving the entire literal reverse prefix, the complete
continuation profile is exactly the original marked suffix. -/
theorem quittingAllContinueProfileSpine_reversePrefixProfile_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    quittingAllContinueProfileSpine reward
        (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
        depth = tail := by
  unfold quittingReversePrefixProfile
  simpa using
    quittingAllContinueProfileSpine_literalRootStackProfile_length
      reward (quittingReversePrefixRootStack roots depth) tail

omit [DecidableEq ι] in
/-- The probability of entering the original suffix is exactly the same
chronological finite joint-survival product used to define the infinite
survival floor. -/
theorem quittingLiveMass_reversePrefixProfile_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile) (depth : ℕ) :
    quittingLiveMass reward
        (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
        depth =
      ∏ time ∈ Finset.range depth,
        quittingStationaryContinueMass (roots time) := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingJointSurvivalWeight_eq_prod]
  have hroot : ∀ offset ∈ Finset.range depth,
      quittingProfileLiveRoot reward
          (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
          (0 + offset) = roots (depth - offset - 1) := by
    intro offset hoffset
    simpa only [Nat.zero_add] using
      quittingProfileLiveRoot_reversePrefixProfile_eq reward roots
        (fun _ => tail) depth offset (Finset.mem_range.mp hoffset)
  apply Finset.prod_bij (fun offset _ => depth - offset - 1)
  · intro offset hoffset
    have hoffset' := Finset.mem_range.mp hoffset
    exact Finset.mem_range.mpr (by omega)
  · intro first hfirst second hsecond heq
    have hfirst' := Finset.mem_range.mp hfirst
    have hsecond' := Finset.mem_range.mp hsecond
    omega
  · intro index hindex
    have hindex' := Finset.mem_range.mp hindex
    refine ⟨depth - index - 1, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro offset hoffset
    exact congrArg quittingStationaryContinueMass (hroot offset hoffset)

omit [DecidableEq ι] in
/-- Every live root inside the marked suffix is unchanged after shifting its
date by the length of the literal reverse prefix. -/
theorem quittingProfileLiveRoot_reversePrefixProfile_suffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile) (depth time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
        (depth + time) =
      quittingProfileLiveRoot reward tail time := by
  rw [← quittingProfileSpineRoot_eq_profileLiveRoot,
    show quittingProfileSpineRoot reward
        (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
        (depth + time) = quittingProfileRoot reward
          (quittingAllContinueProfileSpine reward
            (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
            (depth + time)) by rfl,
    quittingAllContinueProfileSpine_add,
    quittingAllContinueProfileSpine_reversePrefixProfile_length]
  exact congrFun (quittingProfileSpineRoot_eq_profileLiveRoot reward tail) time

omit [DecidableEq ι] in
/-- A marked suffix row keeps its conditional root data, while its total live
mass is multiplied by the exact probability of entering the suffix. -/
theorem quittingLiveMass_reversePrefixProfile_suffix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile) (depth time : ℕ) :
    quittingLiveMass reward
        (quittingReversePrefixProfile reward roots (fun _ => tail) depth)
        (depth + time) =
      (∏ stage ∈ Finset.range depth,
        quittingStationaryContinueMass (roots stage)) *
        quittingLiveMass reward tail time := by
  let prefixed :=
    quittingReversePrefixProfile reward roots (fun _ => tail) depth
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingJointSurvivalWeight_eq_survivalProduct,
    Math.survivalProduct_add]
  have hfront : Math.survivalProduct
      (fun stage => quittingStationaryContinueMass
        (quittingProfileLiveRoot reward prefixed stage)) 0 depth =
      quittingLiveMass reward prefixed depth := by
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
      quittingJointSurvivalWeight_eq_survivalProduct]
  rw [hfront, quittingLiveMass_reversePrefixProfile_length]
  congr 1
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingJointSurvivalWeight_eq_survivalProduct]
  unfold Math.survivalProduct
  apply Finset.prod_congr rfl
  intro offset _
  simp only [Nat.zero_add]
  change quittingStationaryContinueMass
      (quittingProfileLiveRoot reward prefixed (depth + offset)) =
    quittingStationaryContinueMass (quittingProfileLiveRoot reward tail offset)
  exact congrArg quittingStationaryContinueMass
    (quittingProfileLiveRoot_reversePrefixProfile_suffix
      reward roots tail depth offset)

end GameTheory
