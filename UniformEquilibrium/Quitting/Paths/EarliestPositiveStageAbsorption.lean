import UniformEquilibrium.Quitting.Paths.StageCoalitionStoppingLaw

/-! # Earliest positive absorption stage -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Unconditional absorption mass at one stage of an actual profile. -/
def quittingStageAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) : ℝ :=
  quittingLiveMass reward profile time *
    (1 - quittingJointContinueMass reward profile time)

omit [DecidableEq ι] in
theorem quittingStageAbsorptionMass_eq_liveMass_sub_succ
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingStageAbsorptionMass profile time =
      quittingLiveMass reward profile time -
        quittingLiveMass reward profile (time + 1) := by
  rw [quittingLiveMass_succ]
  unfold quittingStageAbsorptionMass
  ring

/-- Stage absorption is the sum of the exact nonempty coalition atoms. -/
theorem sum_quittingStageCoalitionMass_eq_stageAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    (∑ terminal : {S : Finset ι // S.Nonempty},
      quittingStageCoalitionMass reward profile time terminal) =
        quittingStageAbsorptionMass profile time := by
  classical
  rw [show (∑ terminal : {S : Finset ι // S.Nonempty},
      quittingStageCoalitionMass reward profile time terminal) =
      quittingLiveMass reward profile time *
        ∑ terminal : {S : Finset ι // S.Nonempty},
          quittingRootCoalitionMass
            (quittingProfileLiveRoot reward profile time) terminal.1 by
    simp_rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      Finset.mul_sum]]
  rw [show (∑ terminal : {S : Finset ι // S.Nonempty},
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) terminal.1) =
      ∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
        quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) coalition by
    symm
    apply Finset.sum_bij (fun coalition hcoalition =>
      ⟨coalition, Finset.nonempty_iff_ne_empty.mpr
        (Finset.mem_erase.mp hcoalition).1⟩)
    all_goals simp [Finset.nonempty_iff_ne_empty]]
  rw [show (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
      quittingRootCoalitionMass
        (quittingProfileLiveRoot reward profile time) coalition) =
      1 - quittingJointContinueMass reward profile time by
    rw [quittingJointContinueMass_eq_product]
    have hcontinue :
        (∏ player, ((profile player time
          (quittingLiveHist reward time)) false).toReal) =
          Math.PMFProduct.continueMass
            (quittingRootQuitRates
              (quittingProfileLiveRoot reward profile time)) := by
      unfold Math.PMFProduct.continueMass quittingRootQuitRates
        quittingProfileLiveRoot
      apply Finset.prod_congr rfl
      intro who _
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (quittingProfileLiveRoot reward profile time) who
      simp only [quittingProfileLiveRoot] at hsum
      rw [← hsum]
      ring_nf
      rfl
    rw [hcontinue]
    simpa [quittingRootCoalitionMass] using
      Math.PMFProduct.sum_coalitionMass_nonempty
        (quittingRootQuitRates (quittingProfileLiveRoot reward profile time))]
  rfl

omit [DecidableEq ι] in
/-- Before the first positive absorption stage, the live mass remains exactly
one; no positivity or eventual-absorption assumption beyond existence of that
stage is stored. -/
theorem exists_earliestPositiveStageAbsorption_liveMass_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (hexists : ∃ time, 0 < quittingStageAbsorptionMass profile time) :
    ∃ first,
      0 < quittingStageAbsorptionMass profile first ∧
        (∀ time < first, quittingStageAbsorptionMass profile time = 0) ∧
        quittingLiveMass reward profile first = 1 := by
  let first := Nat.find hexists
  have hfirst : 0 < quittingStageAbsorptionMass profile first := Nat.find_spec hexists
  have hbefore : ∀ time < first, quittingStageAbsorptionMass profile time = 0 := by
    intro time htime
    have hnot : ¬ 0 < quittingStageAbsorptionMass profile time := by
      intro hpositive
      exact (Nat.not_le_of_gt htime) (Nat.find_min' hexists hpositive)
    have hnonneg : 0 ≤ quittingStageAbsorptionMass profile time := by
      rw [quittingStageAbsorptionMass_eq_liveMass_sub_succ]
      exact sub_nonneg.mpr (quittingLiveMass_antitone reward profile
        (Nat.le_add_right time 1))
    linarith
  have hlive : ∀ time ≤ first, quittingLiveMass reward profile time = 1 := by
    intro time htime
    induction time with
    | zero => exact quittingLiveMass_zero reward profile
    | succ time ih =>
        have htimeLt : time < first := Nat.lt_of_succ_le htime
        have hzero := hbefore time htimeLt
        rw [quittingStageAbsorptionMass_eq_liveMass_sub_succ] at hzero
        have hprevious := ih (Nat.le_trans (Nat.le_succ time) htime)
        linarith
  exact ⟨first, hfirst, hbefore, hlive first (le_refl first)⟩

end GameTheory
