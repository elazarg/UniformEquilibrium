import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.PositiveNeverTwoRelease
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction

/-!
# A fresh release row after a finite stopping-law calendar

A stopping-law profile whose finite atoms lie strictly below `clockBound` is
all Continue at and after that date.  Its live mass there is exactly the
product of its marginal Never masses.  Hence any two distinct Fin4 players
give the exact two-release packet at that fresh row.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.Probability.DiscreteHazard

/-- Beyond all finite support, stopping-law survival is exactly Never mass. -/
theorem stoppingLaw_survival_eq_none_of_isFiniteClock
    {clockBound : ℕ} {law : PMF (Option ℕ)}
    (hlaw : IsFiniteClockStoppingLaw clockBound law) :
    StoppingLaw.survival law clockBound = (law none).toReal := by
  have htail : ∀ time, clockBound ≤ time →
      StoppingLaw.finiteMass law time = 0 := by
    intro time htime
    unfold StoppingLaw.finiteMass
    have hzero : law (some time) = 0 := by
      by_contra hne
      rcases hlaw (some time) hne with hnever | ⟨other, hother, heq⟩
      · cases hnever
      · simp only [Option.some.injEq] at heq
        subst other
        omega
    rw [hzero]
    rfl
  have hsum : (∑' time, StoppingLaw.finiteMass law time) =
      ∑ time ∈ Finset.range clockBound, StoppingLaw.finiteMass law time := by
    rw [tsum_eq_sum (s := Finset.range clockBound)]
    intro time htime
    exact htail time (Nat.le_of_not_gt (by simpa using htime))
  have htotal := StoppingLaw.none_add_tsum_finiteMass law
  rw [hsum] at htotal
  unfold StoppingLaw.survival
  linarith

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A finite stopping-law reconstruction reaches its last fresh row with
exactly the product of the marginal Never masses. -/
theorem quittingLiveMass_stoppingLawProfile_eq_prod_none_of_isFiniteClock
    (clockBound : ℕ) (laws : ι → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clockBound (laws who)) :
    quittingLiveMass reward (quittingStoppingLawProfile reward laws) clockBound =
      ∏ who, (laws who none).toReal := by
  rw [quittingLiveMass_eq_prod_behaviorHazardSurvival]
  apply Finset.prod_congr rfl
  intro who _
  unfold quittingBehaviorLiveHazard quittingStoppingLawProfile
    quittingStoppingLawBehaviorStrategy
  rw [show quittingHazardSurvival
      (StoppingLaw.toScalarHazard (laws who)).toBoolean clockBound =
        (StoppingLaw.toScalarHazard (laws who)).survival 0 clockBound by
    unfold quittingHazardSurvival ScalarHazard.survival
    congr 1
    funext time
    simp [ScalarHazard.toBoolean, booleanCoin_false_toReal]]
  rw [StoppingLaw.toScalarHazard_survival,
    stoppingLaw_survival_eq_none_of_isFiniteClock (hlaws who)]

omit [DecidableEq ι] in
/-- After the fresh row, the reconstructed finite clock is literally the
all-Continue profile. -/
theorem quittingAllContinueProfileSpine_stoppingLawProfile_eq_alwaysContinue
    (clockBound : ℕ) (laws : ι → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clockBound (laws who)) :
    quittingAllContinueProfileSpine reward
        (quittingStoppingLawProfile reward laws) (clockBound + 1) =
      quittingAlwaysContinueProfile reward := by
  have heq := quittingAllContinueProfileSpine_eq_of_eq_from reward
    (quittingStoppingLawProfile reward laws)
    (quittingAlwaysContinueProfile reward) (clockBound + 1) (by
      intro who time history htime
      have hroot := congrFun
        (quittingStoppingLawProfile_liveHazard_eq_allContinue_of_le
          reward clockBound laws hlaws (show clockBound ≤ time by omega)) who
      unfold quittingProfileLiveRoot quittingStoppingLawProfile at hroot
      unfold quittingStoppingLawProfile quittingStoppingLawBehaviorStrategy
        quittingAlwaysContinueProfile StochasticGame.stationaryBehaviorProfile
      change (StoppingLaw.toScalarHazard (laws who)).toBoolean time =
        (PMF.pure false : PMF Bool)
      exact hroot)
  have hfixed : quittingAllContinueProfileSpine reward
      (quittingAlwaysContinueProfile reward) (clockBound + 1) =
        quittingAlwaysContinueProfile reward := by
    induction clockBound + 1 with
    | zero => rfl
    | succ count ih =>
        rw [quittingAllContinueProfileSpine_succ_eq]
        have hstep : quittingProfileAllContinueContinuation reward
            (quittingAlwaysContinueProfile reward) =
              quittingAlwaysContinueProfile reward := by
          funext player time history
          rfl
        rw [hstep, ih]
  exact heq.trans hfixed

/-- Construct the literal two-release packet at the first date beyond every
finite clock. -/
def quittingPositiveNeverTwoRelease_of_isFiniteClock
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (laws : Fin 4 → PMF (Option ℕ)) (clockBound : ℕ)
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clockBound (laws who))
    (owner outsider : Fin 4) (hne : outsider ≠ owner) :
    QuittingPositiveNeverTwoRelease reward where
  sourceProfile := quittingStoppingLawProfile reward laws
  mark := clockBound
  owner := owner
  outsider := outsider
  outsider_ne_owner := hne
  source_root_eq :=
    quittingStoppingLawProfile_liveHazard_eq_allContinue_of_le
      reward clockBound laws hlaws le_rfl
  source_tail_eq :=
    quittingAllContinueProfileSpine_stoppingLawProfile_eq_alwaysContinue
      clockBound laws hlaws

end GameTheory
