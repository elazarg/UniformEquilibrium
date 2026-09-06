import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-! # Support purification of a quitting root -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Quit is strictly inferior by more than `β`. -/
def IsQuittingRootBadQuitAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι) : Prop :=
  quittingRootQuitPayoff reward tail root who <
    quittingRootContinuePayoff reward tail root who - β

/-- Continue is strictly inferior by more than `β`. -/
def IsQuittingRootBadContinueAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι) : Prop :=
  quittingRootContinuePayoff reward tail root who <
    quittingRootQuitPayoff reward tail root who - β

/-- Delete each action which is inferior by more than `β`, transferring its
mass to the other action. -/
def quittingSupportPurifiedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) : ι → PMF Bool := by
  classical
  exact fun who =>
    if IsQuittingRootBadQuitAt reward tail β root who then PMF.pure false
    else if IsQuittingRootBadContinueAt reward tail β root who then PMF.pure true
    else root who

@[simp] theorem quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι)
    (hbad : IsQuittingRootBadQuitAt reward tail β root who) :
    quittingSupportPurifiedRoot reward tail β root who = PMF.pure false := by
  simp [quittingSupportPurifiedRoot, hbad]

@[simp] theorem quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι)
    (hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail β root who)
    (hbad : IsQuittingRootBadContinueAt reward tail β root who) :
    quittingSupportPurifiedRoot reward tail β root who = PMF.pure true := by
  simp [quittingSupportPurifiedRoot, hnotBadQuit, hbad]

@[simp] theorem quittingSupportPurifiedRoot_eq_self_of_not_bad
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β : ℝ) (root : ι → PMF Bool) (who : ι)
    (hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail β root who)
    (hnotBadContinue : ¬IsQuittingRootBadContinueAt reward tail β root who) :
    quittingSupportPurifiedRoot reward tail β root who = root who := by
  simp [quittingSupportPurifiedRoot, hnotBadQuit, hnotBadContinue]

/-- With nonnegative separation, Quit and Continue cannot both be strictly
inferior at the same coordinate. -/
theorem not_badContinue_of_badQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {β : ℝ} (hβ : 0 ≤ β)
    (root : ι → PMF Bool) (who : ι)
    (hbad : IsQuittingRootBadQuitAt reward tail β root who) :
    ¬IsQuittingRootBadContinueAt reward tail β root who := by
  intro hbadContinue
  dsimp only [IsQuittingRootBadQuitAt] at hbad
  dsimp only [IsQuittingRootBadContinueAt] at hbadContinue
  linarith

/-- Small masses of every deleted action imply coordinatewise closeness of
the simultaneously purified root. -/
theorem supportPurifiedRoot_coordinate_close_of_badAction_small
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (β d : ℝ) (root : ι → PMF Bool) (hd : 0 < d)
    (hbadQuit : ∀ who, IsQuittingRootBadQuitAt reward tail β root who →
      (root who true).toReal < d)
    (hbadContinue : ∀ who,
      IsQuittingRootBadContinueAt reward tail β root who →
        (root who false).toReal < d) :
    ∀ who,
      |(quittingSupportPurifiedRoot reward tail β root who true).toReal -
          (root who true).toReal| < d := by
  classical
  intro who
  by_cases hq : IsQuittingRootBadQuitAt reward tail β root who
  · rw [quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
      reward tail β root who hq]
    simpa [abs_of_nonneg ENNReal.toReal_nonneg] using hbadQuit who hq
  · by_cases hc : IsQuittingRootBadContinueAt reward tail β root who
    · rw [quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
        reward tail β root who hq hc]
      simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
      have hsum := quittingRoot_continueProbability_add_quitProbability root who
      have hquitLe : (root who true).toReal ≤ 1 := by
        have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hquitLe)]
      linarith [hbadContinue who hc]
    · rw [quittingSupportPurifiedRoot_eq_self_of_not_bad
        reward tail β root who hq hc]
      simpa using hd

end GameTheory
