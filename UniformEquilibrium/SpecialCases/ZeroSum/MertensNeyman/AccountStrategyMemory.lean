/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.ZeroSum.MertensNeyman.AccountStrategyBellman

/-!
# Memory potentials and occupation bounds for the account controller

This module develops finite reachable-memory potentials, their drift bounds,
and the resulting floor-occupation estimates.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Filter Math.Probability Math.PMFProduct Topology

def rowAccountValueMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 0

/-- The real account represented by a finite reachable exponent memory. -/
def accountLevelMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (t : ℕ) (_h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  accountAtLevel γ M k

/-- Either secured player's discounted value on the finite reachable account
memory. -/
def accountValueMemoryPotential
    {G : StochasticGame (Fin 2)} (who : Fin 2)
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 who

/-- Either secured player's discounted value minus the logarithmic account
corrector on finite reachable memory. -/
def accountCorrectedMemoryPotential
    {G : StochasticGame (Fin 2)} (who : Fin 2)
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 who -
    logCorrector (accountAtLevel γ M k)

/-- The row discounted value minus the logarithmic account corrector, viewed
as a potential on the finite reachable memory of the account controller. -/
def rowAccountCorrectedMemoryPotential
    {G : StochasticGame (Fin 2)}
    (γ M : ℝ) (v : ℝ → G.State → Payoff (Fin 2))
    (t : ℕ) (h : G.Hist t) (k : Fin (t + 1)) : ℝ :=
  v (discountRate (accountAtLevel γ M k)) h.2 0 -
    logCorrector (accountAtLevel γ M k)

/-- The published payoff/account step for the concrete finite-memory
controller at a fixed memory state. Both the next real account and the switched
discounted value are transported through the mapped exponent update. -/
theorem row_accountMemoryController_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z 0) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryController γ M ε
      (fun lam z => x lam z 0)
      (fun lam z => v lam z 0)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    (-9 * ε / 16 +
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              accountLevelMemoryPotential γ M
                (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          accountLevelMemoryPotential γ M t h k -
          accountFloorIndicator k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          G.stagePayoff h.2 o.1 0) -
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountValueMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))) := by
  dsimp only
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) := C.outcomeKernel opp h k
  let s := accountAtLevel γ M k
  change -9 * ε / 16 +
        expect d (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        accountLevelMemoryPotential γ M t h k -
        accountFloorIndicator k ≤
      expect d (fun o => G.stagePayoff h.2 o.1 0) -
      expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          rowAccountValueMemoryPotential γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hyLower : ∀ o : G.JointAct × G.State,
      -1 ≤ G.stagePayoff h.2 o.1 0 -
        v (discountRate s) o.2 0 + ε / 2 := by
    intro o
    nlinarith [hpayLower h.2 o.1,
      hvalueUpper (discountRate s) o.2]
  have hyUpper : ∀ o : G.JointAct × G.State,
      G.stagePayoff h.2 o.1 0 -
        v (discountRate s) o.2 0 + ε / 2 ≤ 2 := by
    intro o
    nlinarith [hpayUpper h.2 o.1,
      hvalueLower (discountRate s) o.2]
  have hfloorEq :
      (if s = M then (1 : ℝ) else 0) =
        accountFloorIndicator k := by
    simp [s, accountFloorIndicator,
      accountAtLevel_eq_floor_iff hfloor]
  have hpoint : ∀ o : G.JointAct × G.State,
      -9 * ε / 16 +
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move - s) -
          accountFloorIndicator k ≤
        G.stagePayoff h.2 o.1 0 -
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0) := by
    intro o
    rw [← hfloorEq]
    exact payoff_sub_expectedNextValue_ge
      (ε := ε) (lam := discountRate s)
      (payoff := G.stagePayoff h.2 o.1 0)
      (V := fun u => v (discountRate u) o.2 0)
      hscale hMs hε (hrateUpper s hMs)
      (hyLower o) (hyUpper o)
      (hbudget o.2 s
        (G.stagePayoff h.2 o.1 0 -
          v (discountRate s) o.2 0 + ε / 2)
        hMs hscale (hyLower o) (hyUpper o))
  have haccountUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move) := by
    intro o
    simpa [C, s, accountMemoryController,
      accountLevelMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o) (fun u => u)
  have hvalueUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountValueMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0) := by
    intro o
    simpa [C, s, accountMemoryController,
      rowAccountValueMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o)
        (fun u => v (discountRate u) o.2 0)
  simp_rw [haccountUpdate, hvalueUpdate]
  rw [show accountLevelMemoryPotential γ M t h k = s by rfl]
  have hmean := expect_mono d _ _ hpoint
  have hnextSub : ∀ o : G.JointAct × G.State,
      expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 0 -
              v (discountRate s) o.2 0 + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move - s) =
        expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 0 -
              v (discountRate s) o.2 0 + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move) - s := by
    intro o
    rw [expect_sub, expect_const]
  simp_rw [hnextSub] at hmean
  let A : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 0 -
          v (discountRate s) o.2 0 + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move => nextAccount γ s move)
  let B : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 0 -
          v (discountRate s) o.2 0 + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move =>
        v (discountRate (nextAccount γ s move)) o.2 0)
  let P : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff h.2 o.1 0
  change -9 * ε / 16 + expect d A - s -
      accountFloorIndicator k ≤ expect d P - expect d B
  change expect d (fun o =>
      -9 * ε / 16 + (A o - s) - accountFloorIndicator k) ≤
    expect d (fun o => P o - B o) at hmean
  rw [expect_sub, expect_add, expect_const, expect_sub, expect_const,
    expect_sub] at hmean
  rw [expect_const] at hmean
  linarith

/-- The payoff/account step for either secured player on an arbitrary unit
payoff/value interval. -/
theorem accountMemoryControllerOnUnitInterval_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    (-9 * ε / 16 +
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              accountLevelMemoryPotential γ M
                (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          accountLevelMemoryPotential γ M t h k -
          accountFloorIndicator k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          G.stagePayoff h.2 o.1 who) -
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountValueMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))) := by
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) := C.outcomeKernel opp h k
  let s := accountAtLevel γ M k
  change -9 * ε / 16 +
        expect d (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        accountLevelMemoryPotential γ M t h k -
        accountFloorIndicator k ≤
      expect d (fun o => G.stagePayoff h.2 o.1 who) -
      expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          accountValueMemoryPotential who γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k'))
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hyLower : ∀ o : G.JointAct × G.State,
      -1 ≤ G.stagePayoff h.2 o.1 who -
        v (discountRate s) o.2 who + ε / 2 := by
    intro o
    nlinarith [hpayLower h.2 o.1,
      hvalueUpper (discountRate s) o.2]
  have hyUpper : ∀ o : G.JointAct × G.State,
      G.stagePayoff h.2 o.1 who -
        v (discountRate s) o.2 who + ε / 2 ≤ 2 := by
    intro o
    nlinarith [hpayUpper h.2 o.1,
      hvalueLower (discountRate s) o.2]
  have hfloorEq :
      (if s = M then (1 : ℝ) else 0) =
        accountFloorIndicator k := by
    simp [s, accountFloorIndicator,
      accountAtLevel_eq_floor_iff hfloor]
  have hpoint : ∀ o : G.JointAct × G.State,
      -9 * ε / 16 +
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move - s) -
          accountFloorIndicator k ≤
        G.stagePayoff h.2 o.1 who -
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who) := by
    intro o
    rw [← hfloorEq]
    exact payoff_sub_expectedNextValue_ge
      (ε := ε) (lam := discountRate s)
      (payoff := G.stagePayoff h.2 o.1 who)
      (V := fun u => v (discountRate u) o.2 who)
      hscale hMs hε (hrateUpper s hMs)
      (hyLower o) (hyUpper o)
      (hbudget o.2 s
        (G.stagePayoff h.2 o.1 who -
          v (discountRate s) o.2 who + ε / 2)
        hMs hscale (hyLower o) (hyUpper o))
  have haccountUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountLevelMemoryPotential γ M
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move => nextAccount γ s move) := by
    intro o
    simpa [C, s, accountMemoryControllerOnUnitInterval,
      accountLevelMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o) (fun u => u)
  have hvalueUpdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountValueMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale (hyLower o) (hyUpper o))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who) := by
    intro o
    simpa [C, s, accountMemoryControllerOnUnitInterval,
      accountValueMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale (hyLower o) (hyUpper o)
        (fun u => v (discountRate u) o.2 who)
  simp_rw [haccountUpdate, hvalueUpdate]
  rw [show accountLevelMemoryPotential γ M t h k = s by rfl]
  have hmean := expect_mono d _ _ hpoint
  have hnextSub : ∀ o : G.JointAct × G.State,
      expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 who -
              v (discountRate s) o.2 who + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move - s) =
        expect
          (updatePMF γ M s
            (G.stagePayoff h.2 o.1 who -
              v (discountRate s) o.2 who + ε / 2)
            hscale (hyLower o) (hyUpper o))
          (fun move => nextAccount γ s move) - s := by
    intro o
    rw [expect_sub, expect_const]
  simp_rw [hnextSub] at hmean
  let A : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 who -
          v (discountRate s) o.2 who + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move => nextAccount γ s move)
  let B : G.JointAct × G.State → ℝ := fun o =>
    expect
      (updatePMF γ M s
        (G.stagePayoff h.2 o.1 who -
          v (discountRate s) o.2 who + ε / 2)
        hscale (hyLower o) (hyUpper o))
      (fun move =>
        v (discountRate (nextAccount γ s move)) o.2 who)
  let P : G.JointAct × G.State → ℝ := fun o =>
    G.stagePayoff h.2 o.1 who
  change -9 * ε / 16 + expect d A - s -
      accountFloorIndicator k ≤ expect d P - expect d B
  change expect d (fun o =>
      -9 * ε / 16 + (A o - s) - accountFloorIndicator k) ≤
    expect d (fun o => P o - B o) at hmean
  rw [expect_sub, expect_add, expect_const, expect_sub, expect_const,
    expect_sub] at hmean
  rw [expect_const] at hmean
  linarith

/-- Averaging the fixed-memory payoff/account step under the controller belief
gives the exact historywise inequality for the induced behavioral strategy. -/
theorem row_accountMemoryController_history_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z 0) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryController γ M ε
      (fun lam z => x lam z 0)
      (fun lam z => v lam z 0)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k => accountLevelMemoryPotential γ M n hmem k
    let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k => rowAccountValueMemoryPotential γ M v n hmem k
    let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun _ _ k => accountFloorIndicator
        (show Fin (_ + 1) from k)
    (-9 * ε / 16 +
          G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential A) h -
          C.beliefPotential A t h -
          C.beliefPotential F t h ≤
        G.stageEUAt
            (Function.update opp 0 C.behaviorStrategy) h 0 -
          G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential V) h) := by
  dsimp only
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k => accountLevelMemoryPotential γ M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k => rowAccountValueMemoryPotential γ M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k => accountFloorIndicator
      (show Fin (n + 1) from k)
  change -9 * ε / 16 +
        G.historyContinuationEU
          (Function.update opp 0 C.behaviorStrategy)
          (C.beliefPotential A) h -
        C.beliefPotential A t h -
        C.beliefPotential F t h ≤
      G.stageEUAt
          (Function.update opp 0 C.behaviorStrategy) h 0 -
        G.historyContinuationEU
          (Function.update opp 0 C.behaviorStrategy)
          (C.beliefPotential V) h
  have hfixed : ∀ k : C.Mem t,
      -9 * ε / 16 +
            expect (C.outcomeKernel opp h k) (fun o =>
              expect (C.update t h o.1 o.2 k) (fun k' =>
                A (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
            A t h k - F t h k ≤
          expect (C.outcomeKernel opp h k) (fun o =>
            G.stagePayoff h.2 o.1 0) -
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              V (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) := by
    intro k
    simpa [C, A, V, F] using
      row_accountMemoryController_payoff_step
        hfloor hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hrateUpper hbudget opp h k
  letI : Fintype (C.Mem t) := C.finiteMem t
  have hmean := expect_mono (C.belief t h) _ _ hfixed
  have hA :=
    C.historyContinuationEU_beliefPotential opp A h
  have hV :=
    C.historyContinuationEU_beliefPotential opp V h
  have hstage := C.stageEUAt_behaviorStrategy opp h
  unfold MemoryController.beliefPotential at hmean hA hV ⊢
  simp only [expect_sub, expect_add, expect_const] at hmean
  rw [hA, hV, hstage]
  exact hmean

/-- Posterior averaging of the symmetric payoff/account step gives the
historywise inequality for the induced behavioral strategy. -/
theorem accountMemoryControllerOnUnitInterval_history_payoff_step
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k => accountLevelMemoryPotential γ M n hmem k
    let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k =>
        accountValueMemoryPotential who γ M v n hmem k
    let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun _ _ k => accountFloorIndicator
        (show Fin (_ + 1) from k)
    (-9 * ε / 16 +
          G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential A) h -
          C.beliefPotential A t h -
          C.beliefPotential F t h ≤
        G.stageEUAt
            (Function.update opp who C.behaviorStrategy) h who -
          G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential V) h) := by
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k => accountLevelMemoryPotential γ M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountValueMemoryPotential who γ M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k => accountFloorIndicator
      (show Fin (n + 1) from k)
  change -9 * ε / 16 +
        G.historyContinuationEU
          (Function.update opp who C.behaviorStrategy)
          (C.beliefPotential A) h -
        C.beliefPotential A t h -
        C.beliefPotential F t h ≤
      G.stageEUAt
          (Function.update opp who C.behaviorStrategy) h who -
        G.historyContinuationEU
          (Function.update opp who C.behaviorStrategy)
          (C.beliefPotential V) h
  have hfixed : ∀ k : C.Mem t,
      -9 * ε / 16 +
            expect (C.outcomeKernel opp h k) (fun o =>
              expect (C.update t h o.1 o.2 k) (fun k' =>
                A (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
            A t h k - F t h k ≤
          expect (C.outcomeKernel opp h k) (fun o =>
            G.stagePayoff h.2 o.1 who) -
          expect (C.outcomeKernel opp h k) (fun o =>
            expect (C.update t h o.1 o.2 k) (fun k' =>
              V (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) := by
    intro k
    simpa [C, A, V, F] using
      accountMemoryControllerOnUnitInterval_payoff_step
        hfloor hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hrateUpper hbudget opp h k
  letI : Fintype (C.Mem t) := C.finiteMem t
  have hmean := expect_mono (C.belief t h) _ _ hfixed
  have hA :=
    C.historyContinuationEU_beliefPotential opp A h
  have hV :=
    C.historyContinuationEU_beliefPotential opp V h
  have hstage := C.stageEUAt_behaviorStrategy opp h
  unfold MemoryController.beliefPotential at hmean hA hV ⊢
  simp only [expect_sub, expect_add, expect_const] at hmean
  rw [hA, hV, hstage]
  exact hmean

/-- The fixed-memory corrected drift for the concrete account controller.
This theorem performs the change of variables from the real three-point
account coin to the finite exponent update used by `MemoryController`. -/
theorem row_accountMemoryController_correctedPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ s, M ≤ s →
      G.IsDiscountedStationaryBellmanEq
        (1 - discountRate s) (x (discountRate s))
          (v (discountRate s)))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ s z, v (discountRate s) z 1 =
      -v (discountRate s) z 0)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z 0) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryController γ M ε
      (fun lam z => x lam z 0)
      (fun lam z => v lam z 0)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    ε * discountRate (accountAtLevel γ M k) / 8 ≤
      expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountCorrectedMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        rowAccountCorrectedMemoryPotential γ M v t h k := by
  dsimp only
  let s := accountAtLevel γ M k
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) :=
    C.outcomeKernel opp h k
  change ε * discountRate (accountAtLevel γ M k) / 8 ≤
    expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          rowAccountCorrectedMemoryPotential γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
      rowAccountCorrectedMemoryPotential γ M v t h k
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hs1 : 1 < s := hM1.trans_le hMs
  have hbase :=
    row_controller_correctedValuePotential_drift_ge
      (hF s hMs) hzs (hVzs s) C opp h k
      (by rfl) hscale hMs hs1 hε
      (hpayLower h.2) (hpayUpper h.2)
      (hvalueLower (discountRate s))
      (hvalueUpper (discountRate s)) hε2
      (hsecant s hMs)
      (by
        intro o
        apply hbudget o.2 s
          (G.stagePayoff h.2 o.1 0 -
            v (discountRate s) o.2 0 + ε / 2)
          hMs hscale
        · nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2]
        · nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
  have hupdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            rowAccountCorrectedMemoryPotential γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0 -
                logCorrector (nextAccount γ s move)) := by
    intro o
    simpa [C, s, accountMemoryController,
      rowAccountCorrectedMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale
        (by
          nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2])
        (by
          nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
        (fun u =>
          v (discountRate u) o.2 0 - logCorrector u)
  rw [show accountAtLevel γ M k = s by rfl]
  rw [show
    rowAccountCorrectedMemoryPotential γ M v t h k =
      v (discountRate s) h.2 0 - logCorrector s by
        rfl]
  simp_rw [hupdate]
  calc
    ε * discountRate s / 8 ≤
        expect d (fun o =>
            expect
              (updatePMF γ M s
                (G.stagePayoff h.2 o.1 0 -
                  v (discountRate s) o.2 0 + ε / 2)
                hscale
                (by
                  nlinarith [hpayLower h.2 o.1,
                    hvalueUpper (discountRate s) o.2])
                (by
                  nlinarith [hpayUpper h.2 o.1,
                    hvalueLower (discountRate s) o.2]))
              (fun move =>
                v (discountRate (nextAccount γ s move)) o.2 0)) -
          v (discountRate s) h.2 0 +
        expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              logCorrector s -
                logCorrector (nextAccount γ s move))) := by
          simpa [d] using hbase
    _ = expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 0 -
                v (discountRate s) o.2 0 + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 0 -
                logCorrector (nextAccount γ s move))) -
          (v (discountRate s) h.2 0 - logCorrector s) := by
      simp_rw [expect_sub, expect_const]
      ring

/-- Averaging the concrete fixed-memory account estimate under the controller
posterior gives a historywise drift for the induced behavioral strategy. -/
theorem row_accountMemoryController_beliefPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ s, M ≤ s →
      G.IsDiscountedStationaryBellmanEq
        (1 - discountRate s) (x (discountRate s))
          (v (discountRate s)))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ s z, v (discountRate s) z 1 =
      -v (discountRate s) z 0)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z 0) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryController γ M ε
      (fun lam z => x lam z 0)
      (fun lam z => v lam z 0)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k =>
        rowAccountCorrectedMemoryPotential γ M v n hmem k
    ε / 8 *
        expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel γ M
            ((show Fin (t + 1) from k) : ℕ))) ≤
      G.historyContinuationEU
          (Function.update opp 0 C.behaviorStrategy)
          (C.beliefPotential φ) h -
        C.beliefPotential φ t h := by
  dsimp only
  let C := accountMemoryController γ M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountCorrectedMemoryPotential γ M v n hmem k
  let r : C.Mem t → ℝ := fun k =>
    ε / 8 * discountRate (accountAtLevel γ M
      ((show Fin (t + 1) from k) : ℕ))
  change ε / 8 *
      expect (C.belief t h) (fun k =>
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ))) ≤
    G.historyContinuationEU
        (Function.update opp 0 C.behaviorStrategy)
        (C.beliefPotential φ) h -
      C.beliefPotential φ t h
  have hstep : ∀ k : C.Mem t,
      r k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            φ (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          φ t h k := by
    intro k
    change ε / 8 *
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ)) ≤
      expect (C.outcomeKernel opp h k) (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          φ (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        φ t h k
    rw [show ε / 8 *
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ)) =
      ε * discountRate (accountAtLevel γ M
        ((show Fin (t + 1) from k) : ℕ)) / 8 by ring]
    simpa [C, φ] using
      row_accountMemoryController_correctedPotential_drift_ge
        hfloor hM1 hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hF hzs hVzs hsecant hbudget
        opp h k
  have hlift :=
    C.beliefPotential_drift_ge opp φ h r hstep
  simpa [r, expect_const_mul] using hlift

/-- The symmetric fixed-memory corrected drift for the account controller on
an arbitrary unit payoff/value interval. -/
theorem accountMemoryControllerOnUnitInterval_correctedPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t)
    (k : Fin (t + 1)) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    ε * discountRate (accountAtLevel γ M k) / 8 ≤
      expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            accountCorrectedMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        accountCorrectedMemoryPotential who γ M v t h k := by
  dsimp only
  let s := accountAtLevel γ M k
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let d : PMF (G.JointAct × G.State) :=
    C.outcomeKernel opp h k
  change ε * discountRate (accountAtLevel γ M k) / 8 ≤
    expect d (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          accountCorrectedMemoryPotential who γ M v
            (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
      accountCorrectedMemoryPotential who γ M v t h k
  have hMs : M ≤ s := floor_le_accountAtLevel hfloor k
  have hscale : IsValidScale γ s :=
    isValidScale_accountAtLevel hfloor k
  have hs1 : 1 < s := hM1.trans_le hMs
  have hbase :=
    controller_correctedValuePotential_drift_ge_of_securityFamily
      hsecurity C opp h k (by rfl) hscale hMs hs1
      (hrateUpper s hMs) hε
      (hpayLower h.2) (hpayUpper h.2)
      (hvalueLower (discountRate s))
      (hvalueUpper (discountRate s)) hε2
      (hsecant s hMs)
      (by
        intro o
        apply hbudget o.2 s
          (G.stagePayoff h.2 o.1 who -
            v (discountRate s) o.2 who + ε / 2)
          hMs hscale
        · nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2]
        · nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
  have hupdate :
      ∀ o : G.JointAct × G.State,
        expect (C.update t h o.1 o.2 k) (fun k' =>
            accountCorrectedMemoryPotential who γ M v
              (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k') =
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who -
                logCorrector (nextAccount γ s move)) := by
    intro o
    simpa [C, s, accountMemoryControllerOnUnitInterval,
      accountCorrectedMemoryPotential] using
      expect_map_nextAccountLevel_accountPotential
        k hscale
        (by
          nlinarith [hpayLower h.2 o.1,
            hvalueUpper (discountRate s) o.2])
        (by
          nlinarith [hpayUpper h.2 o.1,
            hvalueLower (discountRate s) o.2])
        (fun u =>
          v (discountRate u) o.2 who - logCorrector u)
  rw [show accountAtLevel γ M k = s by rfl]
  rw [show
    accountCorrectedMemoryPotential who γ M v t h k =
      v (discountRate s) h.2 who - logCorrector s by
        rfl]
  simp_rw [hupdate]
  calc
    ε * discountRate s / 8 ≤
        expect d (fun o =>
            expect
              (updatePMF γ M s
                (G.stagePayoff h.2 o.1 who -
                  v (discountRate s) o.2 who + ε / 2)
                hscale
                (by
                  nlinarith [hpayLower h.2 o.1,
                    hvalueUpper (discountRate s) o.2])
                (by
                  nlinarith [hpayUpper h.2 o.1,
                    hvalueLower (discountRate s) o.2]))
              (fun move =>
                v (discountRate (nextAccount γ s move)) o.2 who)) -
          v (discountRate s) h.2 who +
        expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              logCorrector s -
                logCorrector (nextAccount γ s move))) := by
          simpa [d] using hbase
    _ = expect d (fun o =>
          expect
            (updatePMF γ M s
              (G.stagePayoff h.2 o.1 who -
                v (discountRate s) o.2 who + ε / 2)
              hscale
              (by
                nlinarith [hpayLower h.2 o.1,
                  hvalueUpper (discountRate s) o.2])
              (by
                nlinarith [hpayUpper h.2 o.1,
                  hvalueLower (discountRate s) o.2]))
            (fun move =>
              v (discountRate (nextAccount γ s move)) o.2 who -
                logCorrector (nextAccount γ s move))) -
          (v (discountRate s) h.2 who - logCorrector s) := by
      simp_rw [expect_sub, expect_const]
      ring

/-- Posterior averaging lifts the symmetric fixed-memory account drift to the
behavioral history law. -/
theorem accountMemoryControllerOnUnitInterval_beliefPotential_drift_ge
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower γ M ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hε : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hpayLower :
      ∀ z a, lower ≤ G.stagePayoff z a who)
    (hpayUpper :
      ∀ z a, G.stagePayoff z a who ≤ lower + 1)
    (hvalueLower :
      ∀ lam z, lower ≤ v lam z who)
    (hvalueUpper :
      ∀ lam z, v lam z who ≤ lower + 1)
    (hsecurity :
      IsDiscountedStationarySecurityFamily (G := G) who x v)
    (hrateUpper : ∀ s, M ≤ s → discountRate s ≤ 1)
    (hsecant : ∀ s, M ≤ s → ∀ s',
      γ⁻¹ * s ≤ s' → s' ≤ γ * s →
      discountRate s *
          (s' - s - ε * |s' - s| / 8) ≤
        logCorrector s - logCorrector s')
    (hbudget : ∀ z s y, M ≤ s → IsValidScale γ s →
      -1 ≤ y → y ≤ 2 →
      switchBudget γ M s y
          (fun u => v (discountRate u) z who) ≤
        ε * discountRate s / 16)
    (opp : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    let C := accountMemoryControllerOnUnitInterval
      lower γ M ε
      (fun lam z => x lam z who)
      (fun lam z => v lam z who)
      hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
    let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
      fun n hmem k =>
        accountCorrectedMemoryPotential who γ M v n hmem k
    ε / 8 *
        expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel γ M
            ((show Fin (t + 1) from k) : ℕ))) ≤
      G.historyContinuationEU
          (Function.update opp who C.behaviorStrategy)
          (C.beliefPotential φ) h -
        C.beliefPotential φ t h := by
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower γ M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε hε2
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountCorrectedMemoryPotential who γ M v n hmem k
  let r : C.Mem t → ℝ := fun k =>
    ε / 8 * discountRate (accountAtLevel γ M
      ((show Fin (t + 1) from k) : ℕ))
  change ε / 8 *
      expect (C.belief t h) (fun k =>
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ))) ≤
    G.historyContinuationEU
        (Function.update opp who C.behaviorStrategy)
        (C.beliefPotential φ) h -
      C.beliefPotential φ t h
  have hstep : ∀ k : C.Mem t,
      r k ≤
        expect (C.outcomeKernel opp h k) (fun o =>
          expect (C.update t h o.1 o.2 k) (fun k' =>
            φ (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
          φ t h k := by
    intro k
    change ε / 8 *
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ)) ≤
      expect (C.outcomeKernel opp h k) (fun o =>
        expect (C.update t h o.1 o.2 k) (fun k' =>
          φ (t + 1) (Fin.snoc h.1 (h.2, o.1), o.2) k')) -
        φ t h k
    rw [show ε / 8 *
        discountRate (accountAtLevel γ M
          ((show Fin (t + 1) from k) : ℕ)) =
      ε * discountRate (accountAtLevel γ M
        ((show Fin (t + 1) from k) : ℕ)) / 8 by ring]
    simpa [C, φ] using
      accountMemoryControllerOnUnitInterval_correctedPotential_drift_ge
        hfloor hM1 hε hε2 hpayLower hpayUpper
        hvalueLower hvalueUpper hsecurity hrateUpper hsecant hbudget
        opp h k
  have hlift :=
    C.beliefPotential_drift_ge opp φ h r hstep
  simpa [r, expect_const_mul] using hlift

/-- The translated corrected account potential is bounded below by the lower
endpoint minus the floor corrector. -/
theorem accountCorrectedMemoryPotential_lower
    {G : StochasticGame (Fin 2)}
    {who : Fin 2} {lower γ M ε : ℝ}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hcorrector : logCorrector M ≤ ε / 8)
    (hvalueLower : ∀ lam z, lower ≤ v lam z who)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    lower - ε / 8 ≤
      accountCorrectedMemoryPotential who γ M v t h k := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hlog :
      logCorrector (accountAtLevel γ M k) ≤ logCorrector M :=
    logCorrector_le_of_le hM1 hMs
  unfold accountCorrectedMemoryPotential
  nlinarith [hvalueLower
    (discountRate (accountAtLevel γ M k)) h.2]

/-- The translated corrected account potential is bounded above by the upper
endpoint of its unit interval. -/
theorem accountCorrectedMemoryPotential_upper
    {G : StochasticGame (Fin 2)}
    {who : Fin 2} {lower γ M : ℝ}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hvalueUpper : ∀ lam z, v lam z who ≤ lower + 1)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    accountCorrectedMemoryPotential who γ M v t h k ≤
      lower + 1 := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hs1 : 1 < accountAtLevel γ M k := hM1.trans_le hMs
  have hlog := (logCorrector_pos hs1).le
  unfold accountCorrectedMemoryPotential
  nlinarith [hvalueUpper
    (discountRate (accountAtLevel γ M k)) h.2]

/-- The corrected account potential is bounded below once the floor makes the
logarithmic corrector at most `ε/8`. -/
theorem rowAccountCorrectedMemoryPotential_lower
    {G : StochasticGame (Fin 2)}
    {γ M ε : ℝ} {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hcorrector : logCorrector M ≤ ε / 8)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    -ε / 8 ≤ rowAccountCorrectedMemoryPotential γ M v t h k := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hlog :
      logCorrector (accountAtLevel γ M k) ≤ logCorrector M :=
    logCorrector_le_of_le hM1 hMs
  unfold rowAccountCorrectedMemoryPotential
  nlinarith [hvalueLower
    (discountRate (accountAtLevel γ M k)) h.2]

/-- The corrected account potential is at most one under normalized discounted
values. -/
theorem rowAccountCorrectedMemoryPotential_upper
    {G : StochasticGame (Fin 2)}
    {γ M : ℝ} {v : ℝ → G.State → Payoff (Fin 2)}
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    {t : ℕ} (h : G.Hist t) (k : Fin (t + 1)) :
    rowAccountCorrectedMemoryPotential γ M v t h k ≤ 1 := by
  have hMs : M ≤ accountAtLevel γ M k :=
    floor_le_accountAtLevel hfloor k
  have hs1 : 1 < accountAtLevel γ M k := hM1.trans_le hMs
  have hlog := (logCorrector_pos hs1).le
  unfold rowAccountCorrectedMemoryPotential
  nlinarith [hvalueUpper
    (discountRate (accountAtLevel γ M k)) h.2]

/-- A posterior potential in any translated unit interval, with account-rate
drift, controls total expected floor occupation under the actual history law.
The controller and secured player are abstract. -/
theorem sum_expected_belief_floorOccupation_le_on_interval
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {γ M ε : ℝ}
    (lower : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (C : G.MemoryController who)
    (level : ∀ t, C.Mem t → Fin (t + 1))
    (φ : (t : ℕ) → G.Hist t → C.Mem t → ℝ)
    (hpotentialLower : ∀ t (h : G.Hist t),
      lower - ε / 8 ≤ C.beliefPotential φ t h)
    (hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ lower + 1)
    (opp : G.BehaviorProfile) (s₀ : G.State)
    (hdrift : ∀ t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun m =>
            discountRate (accountAtLevel γ M (level t m))) ≤
        G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.expectedHistoryValue
          (Function.update opp who C.behaviorStrategy) s₀
          (C.beliefPotential (fun n _ m =>
            accountFloorIndicator (level n m))) t ≤
      9 / (ε * discountRate M) := by
  let σ : G.BehaviorProfile :=
    Function.update opp who C.behaviorStrategy
  let rateMemory : (t : ℕ) → G.Hist t → C.Mem t → ℝ :=
    fun t _ m => discountRate (accountAtLevel γ M (level t m))
  let floorMemory : (t : ℕ) → G.Hist t → C.Mem t → ℝ :=
    fun t _ m => accountFloorIndicator (level t m)
  let rate : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential rateMemory) t
  let potential : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t
  let floorLoss : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential floorMemory) t
  have hfloorHistory : ∀ t (h : G.Hist t),
      discountRate M *
          C.beliefPotential floorMemory t h ≤
        C.beliefPotential rateMemory t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    rw [← expect_const_mul]
    exact expect_mono _ _ _ fun m =>
      discountRate_mul_accountFloorIndicator_le
        hfloor hM1 (level t m)
  have hfloorRate : ∀ t,
      discountRate M * floorLoss t ≤ rate t := by
    intro t
    unfold floorLoss rate expectedHistoryValue
    rw [← expect_const_mul]
    exact expect_mono _ _ _ (hfloorHistory t)
  have hdriftExpected : ∀ t,
      ε * rate t / 8 ≤ potential (t + 1) - potential t := by
    intro t
    have hpoint : ∀ n (h : G.Hist n),
        ε / 8 * C.beliefPotential rateMemory n h ≤
          G.historyContinuationEU σ (C.beliefPotential φ) h -
            C.beliefPotential φ n h := by
      intro n h
      simpa [σ, rateMemory,
        MemoryController.beliefPotential] using hdrift n h
    have hmean :=
      G.expectedHistoryValue_drift_ge σ s₀
        (fun n h => ε / 8 *
          C.beliefPotential rateMemory n h)
        (C.beliefPotential φ) hpoint t
    unfold rate potential
    unfold expectedHistoryValue at hmean ⊢
    rw [expect_const_mul] at hmean
    nlinarith
  have hpotential0 : lower - ε / 8 ≤ potential 0 := by
    unfold potential expectedHistoryValue
    calc
      lower - ε / 8 =
          expect (G.histDist σ s₀ 0)
            (fun _ => lower - ε / 8) := by
            rw [expect_const]
      _ ≤ expect (G.histDist σ s₀ 0)
          (C.beliefPotential φ 0) :=
        expect_mono _ _ _ (hpotentialLower 0)
  have hpotentialT : potential T ≤ lower + 1 := by
    unfold potential expectedHistoryValue
    calc
      expect (G.histDist σ s₀ T)
          (C.beliefPotential φ T) ≤
          expect (G.histDist σ s₀ T) (fun _ => lower + 1) :=
        expect_mono _ _ _ (hpotentialUpper T)
      _ = lower + 1 := expect_const _ _
  have hsum :=
    sum_floorLoss_le_of_potential_drift_on_interval
      hε hε1 (discountRate_pos hM1) lower
      rate potential floorLoss hfloorRate hdriftExpected
      hpotential0 hpotentialT
  simpa [σ, floorLoss, floorMemory] using hsum

/-- Zero-based row specialization of
`sum_expected_belief_floorOccupation_le_on_interval`. -/
theorem sum_expected_belief_floorOccupation_le
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {γ M ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hfloor : IsValidScale γ M) (hM1 : 1 < M)
    (C : G.MemoryController 0)
    (level : ∀ t, C.Mem t → Fin (t + 1))
    (φ : (t : ℕ) → G.Hist t → C.Mem t → ℝ)
    (hpotentialLower : ∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h)
    (hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1)
    (opp : G.BehaviorProfile) (s₀ : G.State)
    (hdrift : ∀ t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun m =>
            discountRate (accountAtLevel γ M (level t m))) ≤
        G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h)
    (T : ℕ) :
    ∑ t ∈ Finset.range T,
        G.expectedHistoryValue
          (Function.update opp 0 C.behaviorStrategy) s₀
          (C.beliefPotential (fun n _ m =>
            accountFloorIndicator (level n m))) t ≤
      9 / (ε * discountRate M) := by
  simpa using
    sum_expected_belief_floorOccupation_le_on_interval
      0 hε hε1 hfloor hM1 C level φ
      (fun t h => by
        have hbound := hpotentialLower t h
        linarith)
      (fun t h => by simpa using hpotentialUpper t h)
      opp s₀ hdrift T

end MertensNeymanAccount
end StochasticGame
end GameTheory
