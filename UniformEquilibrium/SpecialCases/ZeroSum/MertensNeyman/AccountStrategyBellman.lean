/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.SpecialCases.ZeroSum.MertensNeyman.Account
import UniformEquilibrium.SpecialCases.ZeroSum.MertensNeyman.Criterion
import UniformEquilibrium.Certificates.Adaptive.Certificate
import UniformEquilibrium.ProofView.Concepts.Stochastic.ZeroSum.DiscountedShapleyAlgebraic
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Payoff.AffinePayoff

/-!
# Bellman and security interfaces for the Mertens--Neyman account controller

This module connects the account kernel to the discounted zero-sum Bellman
inequality. The main bridge rewrites a fixed-discount Bellman lower bound in
the exact outer-outcome form consumed by
`expect_correctedValuePotential_drift_ge_of_accountUpdate`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Filter Math.Probability Math.PMFProduct Topology

/-- Joint action and successor state under a statewise mixed profile. -/
def stateActionOutcome
    {ι : Type} (G : StochasticGame ι) [Fintype ι]
    (s : G.State) (m : ∀ i, PMF (G.Act i)) :
    PMF (G.JointAct × G.State) :=
  (pmfPi m).bind fun a =>
    (G.transition s a).bind fun s' =>
      PMF.pure (a, s')

theorem expect_stateActionOutcome
    {ι : Type} {G : StochasticGame ι} [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s : G.State) (m : ∀ i, PMF (G.Act i))
    (f : G.JointAct → G.State → ℝ) :
    expect (stateActionOutcome G s m) (fun o => f o.1 o.2) =
      expect (pmfPi m) (fun a =>
        expect (G.transition s a) (fun s' => f a s')) := by
  unfold stateActionOutcome
  rw [expect_bind]
  apply congrArg (expect (pmfPi m))
  funext a
  rw [expect_bind]
  apply congrArg (expect (G.transition s a))
  funext s'
  rw [expect_pure]

/-- A discounted Bellman lower bound is equivalent to the account proof's
outer-outcome inequality: old successor value minus current value, plus
`lam` times payoff minus old successor value. -/
theorem account_bellman_ge_of_discounted_bellman_ge
    {Ω : Type*} [Finite Ω] (d : PMF Ω)
    {lam oldCurrent : ℝ} (payoff oldNext : Ω → ℝ)
    (hbellman :
      oldCurrent ≤
        lam * expect d payoff +
          (1 - lam) * expect d oldNext) :
    0 ≤ expect d oldNext - oldCurrent +
      lam * expect d (fun ω => payoff ω - oldNext ω) := by
  rw [expect_sub]
  linarith

/-- A discounted stationary family protects one player's value coordinate
when that player's selected mixed action is fixed and every other coordinate
of the mixed profile is arbitrary. This is the symmetric Bellman interface
consumed by an account controller. -/
def IsDiscountedStationarySecurityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (who : Fin 2) (x : ℝ → G.StationaryMixedProfile)
    (v : ℝ → G.State → Payoff (Fin 2)) : Prop :=
  ∀ lam, 0 < lam → lam ≤ 1 → ∀ z (m : ∀ i, PMF (G.Act i)),
    m who = x lam z who →
      v lam z who ≤
        G.discountedAuxEU (1 - lam) (v lam) z m who

/-- The maximizing coordinate of a zero-sum discounted Bellman family has
the symmetric stationary-security property. -/
theorem isDiscountedStationarySecurityFamily_zero
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0) :
    IsDiscountedStationarySecurityFamily (G := G) 0 x v := by
  intro lam hlam hlam1 z m hm
  have hrow :=
    (hF lam hlam hlam1).row_discountedAuxEU_ge
      hzs (hVzs lam) z (m 1)
  have hprofile :
      Function.update (x lam z) 1 (m 1) = m := by
    funext i
    fin_cases i <;> simp [hm]
  simpa [hprofile] using hrow

/-- The minimizing coordinate of a zero-sum discounted Bellman family has
the same stationary-security property for its own (negated) payoff. -/
theorem isDiscountedStationarySecurityFamily_one
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0) :
    IsDiscountedStationarySecurityFamily (G := G) 1 x v := by
  intro lam hlam hlam1 z m hm
  have hcol :=
    (hF lam hlam hlam1).col_discountedAuxEU_ge
      hzs (hVzs lam) z (m 0)
  have hprofile :
      Function.update (x lam z) 0 (m 0) = m := by
    funext i
    fin_cases i <;> simp [hm]
  simpa [hprofile] using hcol

/-- The symmetric stationary-security property, rewritten in the exact
successor-value/payoff-gap form used by the account update. -/
theorem account_bellman_ge_of_securityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (s : G.State)
    (m : ∀ i, PMF (G.Act i))
    (hm : m who = x lam s who) :
    0 ≤
      expect (stateActionOutcome G s m)
          (fun o => v lam o.2 who) -
        v lam s who +
      lam * expect (stateActionOutcome G s m)
        (fun o => G.stagePayoff s o.1 who - v lam o.2 who) := by
  have hsecure := hsecurity lam hlam hlam1 s m hm
  rw [G.discountedAuxEU_eq] at hsecure
  have hpay :
      expect (stateActionOutcome G s m)
          (fun o => G.stagePayoff s o.1 who) =
        expect (pmfPi m)
          (fun a => G.stagePayoff s a who) := by
    simpa using
      expect_stateActionOutcome s m
        (fun a _ => G.stagePayoff s a who)
  have hnext :
      expect (stateActionOutcome G s m)
          (fun o => v lam o.2 who) =
        expect (pmfPi m)
          (fun a =>
            expect (G.transition s a) (fun s' => v lam s' who)) := by
    simpa using
      expect_stateActionOutcome s m
        (fun _ s' => v lam s' who)
  apply account_bellman_ge_of_discounted_bellman_ge
    (stateActionOutcome G s m)
    (fun o => G.stagePayoff s o.1 who)
    (fun o => v lam o.2 who)
  rw [hpay, hnext]
  convert hsecure using 1
  all_goals ring

/-- A controller outcome kernel is the state/action outcome law obtained by
replacing the selected player's component of the opposing profile. -/
theorem outcomeKernel_eq_stateActionOutcome_selected
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} (C : G.MemoryController who)
    (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (x : G.StationaryMixedProfile)
    (hselect : C.select t h m = x h.2 who) :
    C.outcomeKernel opp h m =
      stateActionOutcome G h.2
        (Function.update (fun i => opp i t h) who (x h.2 who)) := by
  letI : Fintype (Fin 2) := inferInstance
  letI : DecidableEq (Fin 2) := inferInstance
  unfold MemoryController.outcomeKernel stateActionOutcome stageActionDist
  have hprofile :
      (fun i =>
        (Function.update opp who
          (fun _ _ => C.select t h m)) i t h) =
        Function.update (fun i => opp i t h) who (x h.2 who) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [hselect]
    · simp [hi]
  rw [hprofile]

/-- Fixed-memory account Bellman premise for either secured player against an
arbitrary opposing behavior profile. -/
theorem controller_account_bellman_ge_of_securityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lam : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (hselect : C.select t h m = x lam h.2 who) :
    0 ≤
      expect (C.outcomeKernel opp h m) (fun o => v lam o.2 who) -
        v lam h.2 who +
      lam * expect (C.outcomeKernel opp h m)
        (fun o => G.stagePayoff h.2 o.1 who - v lam o.2 who) := by
  let profile : ∀ i, PMF (G.Act i) :=
    Function.update (fun i => opp i t h) who (x lam h.2 who)
  have hprofileWho : profile who = x lam h.2 who := by
    simp [profile]
  rw [outcomeKernel_eq_stateActionOutcome_selected
    C opp h m (x lam) hselect]
  exact account_bellman_ge_of_securityFamily
    hsecurity hlam hlam1 h.2 profile hprofileWho

/-- Positive corrected-potential drift for either secured player on an
arbitrary unit payoff/value interval. The interval's lower endpoint cancels
from every account gap; only its width is used. -/
theorem controller_correctedValuePotential_drift_ge_of_securityFamily
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M s ε : ℝ}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {x : ℝ → G.StationaryMixedProfile}
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (C : G.MemoryController who) (opp : G.BehaviorProfile)
    {t : ℕ} (hmem : G.Hist t) (m : C.Mem t)
    (hselect :
      C.select t hmem m =
        x (discountRate s) hmem.2 who)
    (hscale : IsValidScale γ s) (hMs : M ≤ s) (hs1 : 1 < s)
    (hrateUpper : discountRate s ≤ 1)
    (hε : 0 ≤ ε)
    (hpayLower :
      ∀ a, lower ≤ G.stagePayoff hmem.2 a who)
    (hpayUpper :
      ∀ a, G.stagePayoff hmem.2 a who ≤ lower + 1)
    (hvalueLower :
      ∀ z, lower ≤ v (discountRate s) z who)
    (hvalueUpper :
      ∀ z, v (discountRate s) z who ≤ lower + 1)
    (hε2 : ε ≤ 2)
    (hsecant : ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ o : G.JointAct × G.State,
      switchBudget γ M s
          (G.stagePayoff hmem.2 o.1 who -
            v (discountRate s) o.2 who + ε / 2)
          (fun u => v (discountRate u) o.2 who) ≤
        ε * discountRate s / 16) :
    ε * discountRate s / 8 ≤
      expect (C.outcomeKernel opp hmem m) (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff hmem.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower o.1, hvalueUpper o.2])
              (by
                nlinarith [hpayUpper o.1, hvalueLower o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who)) -
        v (discountRate s) hmem.2 who +
      expect (C.outcomeKernel opp hmem m) (fun o =>
        expect
          (updatePMF γ M s
            (G.stagePayoff hmem.2 o.1 who -
              v (discountRate s) o.2 who + ε / 2)
            hscale
            (by
              nlinarith [hpayLower o.1, hvalueUpper o.2])
            (by
              nlinarith [hpayUpper o.1, hvalueLower o.2]))
          (fun move =>
            logCorrector s -
              logCorrector (nextAccount γ s move))) := by
  let d := C.outcomeKernel opp hmem m
  let y : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff hmem.2 o.1 who -
      v (discountRate s) o.2 who + ε / 2
  let W : (G.JointAct × G.State) → ℝ → ℝ := fun o u =>
    v (discountRate u) o.2 who
  have hyLower : ∀ o, -1 ≤ y o := by
    intro o
    dsimp [y]
    nlinarith [hpayLower o.1, hvalueUpper o.2]
  have hyUpper : ∀ o, y o ≤ 2 := by
    intro o
    dsimp [y]
    nlinarith [hpayUpper o.1, hvalueLower o.2]
  have hbellman :
      0 ≤ expect d (fun o => W o s) -
          v (discountRate s) hmem.2 who +
        discountRate s * expect d (fun o => y o - ε / 2) := by
    simpa [d, W, y] using
      controller_account_bellman_ge_of_securityFamily
        hsecurity (discountRate_pos hs1) hrateUpper
        C opp hmem m hselect
  exact expect_correctedValuePotential_drift_ge_of_accountUpdate
    d y W hscale hMs hs1 hyLower hyUpper hε hsecant
    (by simpa [y, W] using hbudget) hbellman

/-- The zero-sum discounted stationary Bellman equilibrium supplies the exact
outer-outcome account Bellman premise against an arbitrary column mixed
action. -/
theorem row_account_bellman_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {lam : ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq (1 - lam) x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (s : G.State) (d : PMF (G.Act 1)) :
    0 ≤
      expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => V o.2 0) -
        V s 0 +
      lam *
        expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => G.stagePayoff s o.1 0 - V o.2 0) := by
  letI : Fintype (Fin 2) := inferInstance
  have hrow :=
    hF.row_discountedAuxEU_ge hzs hVzs s d
  rw [G.discountedAuxEU_eq] at hrow
  have hpay :
      expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => G.stagePayoff s o.1 0) =
        expect (pmfPi (Function.update (x s) 1 d))
          (fun a => G.stagePayoff s a 0) := by
    simpa using
      expect_stateActionOutcome s (Function.update (x s) 1 d)
        (fun a _ => G.stagePayoff s a 0)
  have hnext :
      expect
          (stateActionOutcome G s (Function.update (x s) 1 d))
          (fun o => V o.2 0) =
        expect (pmfPi (Function.update (x s) 1 d))
          (fun a => expect (G.transition s a) (fun s' => V s' 0)) := by
    simpa using
      expect_stateActionOutcome s (Function.update (x s) 1 d)
        (fun _ s' => V s' 0)
  apply account_bellman_ge_of_discounted_bellman_ge
    (stateActionOutcome G s (Function.update (x s) 1 d))
    (fun o => G.stagePayoff s o.1 0) (fun o => V o.2 0)
  rw [hpay, hnext]
  convert hrow using 1
  all_goals ring

/-- For the row player, a controller outcome kernel whose selected action is
the row component of `x` is the state-action outcome law of `x` against the
current column mixed action. -/
theorem outcomeKernel_eq_stateActionOutcome_row
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (C : G.MemoryController 0) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (x : G.StationaryMixedProfile)
    (hselect : C.select t h m = x h.2 0) :
    C.outcomeKernel opp h m =
      stateActionOutcome G h.2
        (Function.update (x h.2) 1 (opp 1 t h)) := by
  letI : Fintype (Fin 2) := inferInstance
  letI : DecidableEq (Fin 2) := inferInstance
  unfold MemoryController.outcomeKernel stateActionOutcome stageActionDist
  have hprofile :
      (fun i =>
        (Function.update opp 0 (fun _ _ => C.select t h m)) i t h) =
        Function.update (x h.2) 1 (opp 1 t h) := by
    funext i
    fin_cases i
    · simp [hselect]
    · simp
  rw [hprofile]

/-- Fixed-memory Bellman premise for the row account controller against an
arbitrary opposing behavior profile. -/
theorem row_controller_account_bellman_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {lam : ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff (Fin 2)}
    (hF : G.IsDiscountedStationaryBellmanEq (1 - lam) x V)
    (hzs : G.IsZeroSum) (hVzs : ∀ s, V s 1 = -V s 0)
    (C : G.MemoryController 0) (opp : G.BehaviorProfile)
    {t : ℕ} (h : G.Hist t) (m : C.Mem t)
    (hselect : C.select t h m = x h.2 0) :
    0 ≤
      expect (C.outcomeKernel opp h m) (fun o => V o.2 0) -
        V h.2 0 +
      lam * expect (C.outcomeKernel opp h m)
        (fun o => G.stagePayoff h.2 o.1 0 - V o.2 0) := by
  rw [outcomeKernel_eq_stateActionOutcome_row C opp h m x hselect]
  exact row_account_bellman_ge hF hzs hVzs h.2 (opp 1 t h)

/-- Positive corrected-potential drift at a fixed controller memory. This
combines the zero-sum discounted Bellman inequality with the nested account
coin estimate; the only analytic premise left in the statement is the
probability-weighted value-switch budget for each successor state. -/
theorem row_controller_correctedValuePotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M s ε : ℝ} {v : ℝ → G.State → Payoff (Fin 2)}
    {x : G.StationaryMixedProfile}
    (hF : G.IsDiscountedStationaryBellmanEq
      (1 - discountRate s) x (v (discountRate s)))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ z, v (discountRate s) z 1 =
      -v (discountRate s) z 0)
    (C : G.MemoryController 0) (opp : G.BehaviorProfile)
    {t : ℕ} (hmem : G.Hist t) (m : C.Mem t)
    (hselect : C.select t hmem m = x hmem.2 0)
    (hscale : IsValidScale γ s) (hMs : M ≤ s) (hs1 : 1 < s)
    (hε : 0 ≤ ε)
    (hpayLower : ∀ a, 0 ≤ G.stagePayoff hmem.2 a 0)
    (hpayUpper : ∀ a, G.stagePayoff hmem.2 a 0 ≤ 1)
    (hvalueLower : ∀ z, 0 ≤ v (discountRate s) z 0)
    (hvalueUpper : ∀ z, v (discountRate s) z 0 ≤ 1)
    (hε2 : ε ≤ 2)
    (hsecant : ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ o : G.JointAct × G.State,
      switchBudget γ M s
          (G.stagePayoff hmem.2 o.1 0 -
            v (discountRate s) o.2 0 + ε / 2)
          (fun u => v (discountRate u) o.2 0) ≤
        ε * discountRate s / 16) :
    ε * discountRate s / 8 ≤
      expect (C.outcomeKernel opp hmem m) (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff hmem.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower o.1, hvalueUpper o.2])
              (by
                nlinarith [hpayUpper o.1, hvalueLower o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0)) -
        v (discountRate s) hmem.2 0 +
      expect (C.outcomeKernel opp hmem m) (fun o =>
        expect
          (updatePMF γ M s
            (G.stagePayoff hmem.2 o.1 0 -
              v (discountRate s) o.2 0 + ε / 2)
            hscale
            (by
              nlinarith [hpayLower o.1, hvalueUpper o.2])
            (by
              nlinarith [hpayUpper o.1, hvalueLower o.2]))
          (fun move =>
            logCorrector s -
              logCorrector (nextAccount γ s move))) := by
  let d := C.outcomeKernel opp hmem m
  let y : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff hmem.2 o.1 0 -
      v (discountRate s) o.2 0 + ε / 2
  let W : (G.JointAct × G.State) → ℝ → ℝ := fun o u =>
    v (discountRate u) o.2 0
  have hyLower : ∀ o, -1 ≤ y o := by
    intro o
    dsimp [y]
    nlinarith [hpayLower o.1, hvalueUpper o.2]
  have hyUpper : ∀ o, y o ≤ 2 := by
    intro o
    dsimp [y]
    nlinarith [hpayUpper o.1, hvalueLower o.2]
  have hbellman :
      0 ≤ expect d (fun o => W o s) -
          v (discountRate s) hmem.2 0 +
        discountRate s * expect d (fun o => y o - ε / 2) := by
    simpa [d, W, y] using
      row_controller_account_bellman_ge
        hF hzs hVzs C opp hmem m hselect
  exact expect_correctedValuePotential_drift_ge_of_accountUpdate
    d y W hscale hMs hs1 hyLower hyUpper hε hsecant
    (by simpa [y, W] using hbudget) hbellman

end MertensNeymanAccount
end StochasticGame
end GameTheory
