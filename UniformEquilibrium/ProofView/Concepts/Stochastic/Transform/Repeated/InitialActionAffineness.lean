import MathUE.PMFProduct.Update
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Repeated.RealizedActionRepeatedAdapter

/-!
# Initial-action affineness in realized-action repetition

Fixing all continuation behavior, a finite repeated payoff is affine in one
player's initial behavioral randomization.  The proof exposes the initial
product law, pins one coordinate to a pure action, and applies PMF Fubini.
-/

noncomputable section

namespace GameTheory.KernelGame

open Math.Probability

variable {ι : Type}

/-- The mixed stage profile prescribed at the empty public history. -/
def realizedActionInitialMixedProfile (G : KernelGame ι)
    (profile : G.realizedActionStochasticGame.BehaviorProfile) :
    ∀ who, PMF (G.Strategy who) :=
  fun who => profile who 0
    (G.realizedActionStochasticGame.emptyHist PUnit.unit)

/-- Replace one player's initial randomization by a pure action and retain all
continuation behavior. -/
def pinRealizedActionInitialAction (G : KernelGame ι)
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) (action : G.Strategy who) :
    G.realizedActionStochasticGame.BehaviorStrategy who :=
  fun time history =>
    if time = 0 then PMF.pure action else profile who time history

/-- A realized-action stage utility is the mixed-extension utility prescribed
at the current public history. -/
theorem realizedAction_stageEUAt_eq_mixedExtension_eu
    (G : KernelGame ι) [Fintype ι] [Finite G.Outcome]
    [∀ who, Fintype (G.Strategy who)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    {time : ℕ} (history : G.realizedActionStochasticGame.Hist time)
    (who : ι) :
    G.realizedActionStochasticGame.stageEUAt profile history who =
      G.mixedExtension.eu
        (fun player => profile player time history) who := by
  unfold StochasticGame.stageEUAt StochasticGame.stageActionDist
  rw [G.mixedExtension_eu]
  rfl

/-- Once the initial joint action is fixed, pinning its selected coordinate
does not alter the continuation profile. -/
theorem realizedAction_shiftProfile_update_pinInitialAction
    (G : KernelGame ι) [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) (action : G.Strategy who) (joint : Profile G) :
    G.realizedActionStochasticGame.shiftProfile
        (Function.update profile who
          (G.pinRealizedActionInitialAction profile who action))
        (PUnit.unit, joint) =
      G.realizedActionStochasticGame.shiftProfile
        profile (PUnit.unit, joint) := by
  funext player time history
  unfold StochasticGame.shiftProfile
  by_cases hplayer : player = who
  · subst player
    simp [pinRealizedActionInitialAction]
  · simp [Function.update_of_ne hplayer]

/-- Pinning one initial action replaces exactly that coordinate in the initial
independent product law. -/
theorem realizedAction_stageActionDist_update_pinInitialAction
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) (action : G.Strategy who) :
    G.realizedActionStochasticGame.stageActionDist
        (Function.update profile who
          (G.pinRealizedActionInitialAction profile who action))
        (G.realizedActionStochasticGame.emptyHist PUnit.unit) =
      Math.PMFProduct.pmfPi
        (Function.update (G.realizedActionInitialMixedProfile profile)
          who (PMF.pure action)) := by
  unfold StochasticGame.stageActionDist
  congr 1
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [pinRealizedActionInitialAction]
    rfl
  · simp [Function.update_of_ne hplayer,
      realizedActionInitialMixedProfile]

/-- Mixed-extension utility is affine in one player's own mixed strategy. -/
theorem mixedExtension_eu_eq_expect_pure_update
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι] [Finite G.Outcome]
    [∀ who, Fintype (G.Strategy who)]
    (mixed : ∀ who, PMF (G.Strategy who)) (who : ι) :
    G.mixedExtension.eu mixed who =
      expect (mixed who) (fun action =>
        G.mixedExtension.eu
          (Function.update mixed who (PMF.pure action)) who) := by
  simpa only [Function.update_eq_self] using
    (G.mixedExtension_eu_update mixed who (mixed who))

/-- Every stage expectation is affine in one player's initial behavioral
randomization when continuation behavior is fixed. -/
theorem realizedAction_expectedStagePayoff_eq_expect_pinInitialAction
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι] [Finite G.Outcome]
    [∀ who, Fintype (G.Strategy who)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) (time : ℕ) :
    G.realizedActionStochasticGame.expectedStagePayoff
        profile PUnit.unit time who =
      expect (G.realizedActionInitialMixedProfile profile who)
        (fun action =>
          G.realizedActionStochasticGame.expectedStagePayoff
            (Function.update profile who
              (G.pinRealizedActionInitialAction profile who action))
            PUnit.unit time who) := by
  letI (player : ι) : Finite
      (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  letI : Finite (∀ player, G.Strategy player) := Finite.of_fintype _
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  let root := G.realizedActionInitialMixedProfile profile
  change G.realizedActionStochasticGame.expectedStagePayoff
      profile PUnit.unit time who =
    expect (root who) (fun action =>
      G.realizedActionStochasticGame.expectedStagePayoff
        (Function.update profile who
          (G.pinRealizedActionInitialAction profile who action))
        PUnit.unit time who)
  cases time with
  | zero =>
      rw [G.realizedActionStochasticGame.expectedStagePayoff_zero]
      simp_rw [G.realizedActionStochasticGame.expectedStagePayoff_zero]
      rw [G.realizedAction_stageEUAt_eq_mixedExtension_eu]
      simp_rw [G.realizedAction_stageEUAt_eq_mixedExtension_eu]
      have hroot :
          (fun player => profile player 0
            (G.realizedActionStochasticGame.emptyHist PUnit.unit)) =
            root := rfl
      have hpinned (action : G.Strategy who) :
          (fun player => Function.update profile who
            (G.pinRealizedActionInitialAction profile who action) player 0
              (G.realizedActionStochasticGame.emptyHist PUnit.unit)) =
            Function.update root who (PMF.pure action) := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [pinRealizedActionInitialAction]
          rfl
        · simp [Function.update_of_ne hplayer]
          rfl
      rw [hroot]
      simp_rw [hpinned]
      exact G.mixedExtension_eu_eq_expect_pure_update root who
  | succ time =>
      rw [G.realizedActionStochasticGame.expectedStagePayoff_succ_shift]
      simp_rw [G.realizedActionStochasticGame.expectedStagePayoff_succ_shift]
      rw [show G.realizedActionStochasticGame.stageActionDist profile
          (G.realizedActionStochasticGame.emptyHist PUnit.unit) =
          Math.PMFProduct.pmfPi root by rfl]
      simp_rw [G.realizedAction_stageActionDist_update_pinInitialAction]
      simp_rw [realizedActionStochasticGame_transition]
      change expect (Math.PMFProduct.pmfPi root)
          (fun joint : Profile G => expect
            (PMF.pure PUnit.unit : PMF PUnit) (fun state =>
              G.realizedActionStochasticGame.expectedStagePayoff
                (G.realizedActionStochasticGame.shiftProfile profile
                  (PUnit.unit, joint)) state time who)) =
        expect (root who) (fun action =>
          expect (Math.PMFProduct.pmfPi
              (Function.update root who (PMF.pure action)))
            (fun joint : Profile G => expect
              (PMF.pure PUnit.unit : PMF PUnit) (fun state =>
                G.realizedActionStochasticGame.expectedStagePayoff
                  (G.realizedActionStochasticGame.shiftProfile
                    (Function.update profile who
                      (G.pinRealizedActionInitialAction
                        profile who action))
                    (PUnit.unit, joint)) state time who)))
      simp_rw [expect_pure,
        G.realizedAction_shiftProfile_update_pinInitialAction]
      let value : Profile G → ℝ := fun joint =>
        G.realizedActionStochasticGame.expectedStagePayoff
          (G.realizedActionStochasticGame.shiftProfile
            profile (PUnit.unit, joint)) PUnit.unit time who
      change expect (Math.PMFProduct.pmfPi root) value =
        expect (root who) (fun action =>
          expect (Math.PMFProduct.pmfPi
            (Function.update root who (PMF.pure action))) value)
      have hproduct := congrArg (fun law => expect law value)
        (Math.PMFProduct.pmfPi_update_bind root who (root who))
      rw [Function.update_eq_self] at hproduct
      exact hproduct.trans (expect_bind (root who)
        (fun action => Math.PMFProduct.pmfPi
          (Function.update root who (PMF.pure action))) value)

/-- Finite-average payoff is affine in one player's initial behavioral
randomization when continuation behavior is fixed. -/
theorem realizedAction_finiteAveragePayoff_eq_expect_pinInitialAction
    (G : KernelGame ι) [Fintype ι] [DecidableEq ι] [Finite G.Outcome]
    [∀ who, Fintype (G.Strategy who)]
    (horizon : ℕ)
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) :
    G.realizedActionStochasticGame.finiteAveragePayoff
        PUnit.unit horizon profile who =
      expect (G.realizedActionInitialMixedProfile profile who)
        (fun action =>
          G.realizedActionStochasticGame.finiteAveragePayoff
            PUnit.unit horizon
            (Function.update profile who
              (G.pinRealizedActionInitialAction profile who action)) who) := by
  letI (player : ι) : Finite
      (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  letI : Finite (G.Strategy who) := Finite.of_fintype _
  letI : Finite (∀ player, G.Strategy player) := Finite.of_fintype _
  letI : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  rw [G.realizedActionStochasticGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp_rw [G.realizedActionStochasticGame.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  rw [show (∑ time ∈ Finset.range horizon,
        G.realizedActionStochasticGame.expectedStagePayoff
          profile PUnit.unit time who) =
      ∑ time ∈ Finset.range horizon,
        expect (G.realizedActionInitialMixedProfile profile who)
          (fun action =>
            G.realizedActionStochasticGame.expectedStagePayoff
              (Function.update profile who
                (G.pinRealizedActionInitialAction profile who action))
              PUnit.unit time who) by
    apply Finset.sum_congr rfl
    intro time _
    exact G.realizedAction_expectedStagePayoff_eq_expect_pinInitialAction
      profile who time]
  rw [Math.Probability.sum_expect_range_comm,
    ← expect_const_mul]

end GameTheory.KernelGame
