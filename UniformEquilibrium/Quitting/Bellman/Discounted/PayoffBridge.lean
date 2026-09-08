import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted.Fink
import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.RootContinuation

/-!

# Discounted auxiliary payoffs of quitting games

Finite quitting-game instances and exact live/absorbed-state payoff bridges.
These identities do not depend on analytic germ existence or curve selection.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

instance instFintypeStateQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Fintype (quittingGame reward).State :=
  inferInstanceAs (Fintype (Option {S : Finset ι // S.Nonempty}))

instance instFintypeActQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i : ι) :
    Fintype ((quittingGame reward).Act i) :=
  inferInstanceAs (Fintype Bool)

instance instDecidableEqActQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i : ι) :
    DecidableEq ((quittingGame reward).Act i) :=
  inferInstanceAs (DecidableEq Bool)

instance instNonemptyActQuittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (i : ι) :
    Nonempty ((quittingGame reward).Act i) :=
  inferInstanceAs (Nonempty Bool)

variable (reward : {S : Finset ι // S.Nonempty} → Payoff ι)

omit [DecidableEq ι] in
/-- At an absorbed state the auxiliary discounted payoff is the one-step
mixture of the repeated terminal reward and the continuation value; no action
influences it. -/
theorem discountedAuxEU_quittingGame_some (β : ℝ)
    (V : (quittingGame reward).State → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) (m : ι → PMF Bool) (who : ι) :
    (quittingGame reward).discountedAuxEU β V (some S) m who =
      (1 - β) * reward S who + β * V (some S) who := by
  have key : ∀ a : ι → Bool,
      (quittingGame reward).discountedAuxPayoff β V (some S) a who =
        (1 - β) * reward S who + β * V (some S) who := by
    intro a
    have htrans : (quittingGame reward).transition (some S) a =
        PMF.pure (show (quittingGame reward).State from some S) := rfl
    have hstage : (quittingGame reward).stagePayoff (some S) a who =
        reward S who := rfl
    rw [StochasticGame.discountedAuxPayoff, htrans, hstage, expect_pure]
  calc (quittingGame reward).discountedAuxEU β V (some S) m who
      = expect (pmfPi m)
          (fun a => (quittingGame reward).discountedAuxPayoff β V (some S) a who) := rfl
    _ = expect (pmfPi m) (fun _ => (1 - β) * reward S who + β * V (some S) who) := by
        simp_rw [key]
    _ = (1 - β) * reward S who + β * V (some S) who := expect_const _ _

omit [DecidableEq ι] in
/-- The one-stage transition expectation at the active state is exactly the
quitting layer's one-stage root payoff, read against the value vector. -/
theorem expect_transition_quittingGame_none
    (V : (quittingGame reward).State → Payoff ι) (action : ι → Bool) (who : ι) :
    expect ((quittingGame reward).transition none action) (fun s' => V s' who) =
      quittingRootPayoff (fun S => V (some S)) (fun j => V none j) action who := by
  rw [quittingGame_transition_none]
  unfold quittingRootPayoff quittingQuitters
  by_cases h : ({j | action j = true} : Finset ι).Nonempty
  · rw [dif_pos h, dif_pos h, expect_pure]
  · rw [dif_neg h, dif_neg h, expect_pure]

omit [DecidableEq ι] in
/-- **The active state carries no stage payoff.**  Hence the auxiliary
discounted payoff at the active state is the discount factor times the
quitting layer's one-stage root expectation. -/
theorem discountedAuxEU_quittingGame_none (β : ℝ)
    (V : (quittingGame reward).State → Payoff ι) (m : ι → PMF Bool) (who : ι) :
    (quittingGame reward).discountedAuxEU β V none m who =
      β * quittingRootExpectedPayoff (fun S => V (some S)) (fun j => V none j) m who := by
  have key : ∀ a : ι → Bool,
      (quittingGame reward).discountedAuxPayoff β V none a who =
        β * quittingRootPayoff (fun S => V (some S)) (fun j => V none j) a who := by
    intro a
    have hstage : (quittingGame reward).stagePayoff none a who = 0 := rfl
    rw [StochasticGame.discountedAuxPayoff, hstage,
      expect_transition_quittingGame_none reward V a who]
    ring
  calc (quittingGame reward).discountedAuxEU β V none m who
      = expect (pmfPi m)
          (fun a => (quittingGame reward).discountedAuxPayoff β V none a who) := rfl
    _ = expect (pmfPi m)
          (fun a => β * quittingRootPayoff (fun S => V (some S))
            (fun j => V none j) a who) := by simp_rw [key]
    _ = β * expect (pmfPi m)
          (fun a => quittingRootPayoff (fun S => V (some S))
            (fun j => V none j) a who) := expect_const_mul _ _ _
    _ = β * quittingRootExpectedPayoff (fun S => V (some S))
          (fun j => V none j) m who := rfl

end GameTheory
