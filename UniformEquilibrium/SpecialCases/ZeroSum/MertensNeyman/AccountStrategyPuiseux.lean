/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.ZeroSum.MertensNeyman.AccountStrategyMemory

/-!
# Puiseux account controllers and one-sided guarantee assembly

This module turns finite-state derivative envelopes into account controllers,
payoff guarantees, and one-sided guarantee certificates.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Filter Math.Probability Math.PMFProduct Topology

theorem exists_accountControllerOnUnitInterval_bounded_beliefPotential_drift_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (Sextra : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
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
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      let C := accountMemoryControllerOnUnitInterval
        lower (1 + ε / 9) M ε
        (fun lam z => x lam z who)
        (fun lam z => v lam z who)
        hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountCorrectedMemoryPotential
            who (1 + ε / 9) M v n hmem k
      let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountLevelMemoryPotential (1 + ε / 9) M n hmem k
      let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountValueMemoryPotential
            who (1 + ε / 9) M v n hmem k
      let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n _ k =>
          accountFloorIndicator (show Fin (n + 1) from k)
      Sextra ≤ M ∧
      Real.exp 1 ≤ M ∧
      1 < M ∧
      logCorrector M ≤ ε / 8 ∧
      (∀ t (h : G.Hist t),
        lower - ε / 8 ≤ C.beliefPotential φ t h) ∧
      (∀ t (h : G.Hist t),
        C.beliefPotential φ t h ≤ lower + 1) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        ε / 8 *
            expect (C.belief t h) (fun k =>
              discountRate (accountAtLevel (1 + ε / 9) M
                ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential φ) h -
            C.beliefPotential φ t h) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        -9 * ε / 16 +
              G.historyContinuationEU
                (Function.update opp who C.behaviorStrategy)
                (C.beliefPotential A) h -
              C.beliefPotential A t h -
              C.beliefPotential F t h ≤
            G.stageEUAt
                (Function.update opp who C.behaviorStrategy) h who -
              G.historyContinuationEU
                (Function.update opp who C.behaviorStrategy)
                (C.beliefPotential V) h) ∧
      (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        ∑ t ∈ Finset.range T,
            G.expectedHistoryValue
              (Function.update opp who C.behaviorStrategy) s₀
              (C.beliefPotential F) t ≤
          9 / (ε * discountRate M)) := by
  obtain ⟨M, hSM, hfloor, hexpM, hM1, hcorrector,
      hsecant, hbudget⟩ :=
    exists_commonAccountFloor_above_of_puiseux_deriv_bound
      Sextra hε hε1 hεquarter hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, ?_⟩
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower (1 + ε / 9) M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountCorrectedMemoryPotential
        who (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountValueMemoryPotential who (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  change Sextra ≤ M ∧
    Real.exp 1 ≤ M ∧
    1 < M ∧
    logCorrector M ≤ ε / 8 ∧
    (∀ t (h : G.Hist t),
      lower - ε / 8 ≤ C.beliefPotential φ t h) ∧
    (∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ lower + 1) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp who C.behaviorStrategy) h who -
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential V) h) ∧
    (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp who C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M))
  have hpotentialLower : ∀ t (h : G.Hist t),
      lower - ε / 8 ≤ C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      lower - ε / 8 =
          expect (C.belief t h) (fun _ => lower - ε / 8) := by
            rw [expect_const]
      _ ≤ expect (C.belief t h) (φ t h) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          accountCorrectedMemoryPotential_lower
            hfloor hM1 hcorrector hvalueLower h k
  have hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ lower + 1 := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      expect (C.belief t h) (φ t h) ≤
          expect (C.belief t h) (fun _ => lower + 1) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          accountCorrectedMemoryPotential_upper
            hfloor hM1 hvalueUpper h k
      _ = lower + 1 := expect_const _ _
  have hdrift : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro opp t h
    simpa [C, φ] using
      accountMemoryControllerOnUnitInterval_beliefPotential_drift_ge
        hfloor hM1 hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        hsecurity
        (fun s hs =>
          discountRate_le_one_of_exp_one_le
            (hexpM.trans hs))
        hsecant
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  have hpayoffStep : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp who C.behaviorStrategy) h who -
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential V) h := by
    intro opp t h
    simpa [C, A, V, F] using
      accountMemoryControllerOnUnitInterval_history_payoff_step
        hfloor hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          discountRate_le_one_of_exp_one_le
            (hexpM.trans hs))
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  refine ⟨hSM, hexpM, hM1, hcorrector, hpotentialLower,
    hpotentialUpper, hdrift, hpayoffStep, ?_⟩
  intro opp s₀ T
  simpa [C, φ, F] using
    sum_expected_belief_floorOccupation_le_on_interval
      lower hε hε1 hfloor hM1 C
      (fun t k => show Fin (t + 1) from k)
      φ hpotentialLower hpotentialUpper opp s₀ (hdrift opp) T

/-- A finite-state Puiseux derivative envelope produces a concrete account
controller whose posterior corrected potential is uniformly bounded and has
positive historywise drift against every opposing behavior profile. This is
the conditional zero-sum account certificate immediately upstream of the
floor-occupation telescope. -/
theorem exists_rowAccountController_bounded_beliefPotential_drift_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (Sextra : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      let C := accountMemoryController (1 + ε / 9) M ε
        (fun lam z => x lam z 0)
        (fun lam z => v lam z 0)
        hfloor
        hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          rowAccountCorrectedMemoryPotential (1 + ε / 9) M v n hmem k
      let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          accountLevelMemoryPotential (1 + ε / 9) M n hmem k
      let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n hmem k =>
          rowAccountValueMemoryPotential (1 + ε / 9) M v n hmem k
      let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
        fun n _ k =>
          accountFloorIndicator (show Fin (n + 1) from k)
      Sextra ≤ M ∧
      Real.exp 1 ≤ M ∧
      1 < M ∧
      logCorrector M ≤ ε / 8 ∧
      (∀ t (h : G.Hist t),
        -ε / 8 ≤ C.beliefPotential φ t h) ∧
      (∀ t (h : G.Hist t),
        C.beliefPotential φ t h ≤ 1) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        ε / 8 *
            expect (C.belief t h) (fun k =>
              discountRate (accountAtLevel (1 + ε / 9) M
                ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential φ) h -
            C.beliefPotential φ t h) ∧
      (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
        -9 * ε / 16 +
              G.historyContinuationEU
                (Function.update opp 0 C.behaviorStrategy)
                (C.beliefPotential A) h -
              C.beliefPotential A t h -
              C.beliefPotential F t h ≤
            G.stageEUAt
                (Function.update opp 0 C.behaviorStrategy) h 0 -
              G.historyContinuationEU
                (Function.update opp 0 C.behaviorStrategy)
                (C.beliefPotential V) h) ∧
      (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        ∑ t ∈ Finset.range T,
            G.expectedHistoryValue
              (Function.update opp 0 C.behaviorStrategy) s₀
              (C.beliefPotential F) t ≤
          9 / (ε * discountRate M)) := by
  obtain ⟨M, hSM, hfloor, hexpM, hM1, hcorrector, hsecant, hbudget⟩ :=
    exists_commonAccountFloor_above_of_puiseux_deriv_bound
      Sextra hε hε1 hεquarter hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, ?_⟩
  dsimp only
  let C := accountMemoryController (1 + ε / 9) M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountCorrectedMemoryPotential (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountValueMemoryPotential (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  change Sextra ≤ M ∧
    Real.exp 1 ≤ M ∧
    1 < M ∧
    logCorrector M ≤ ε / 8 ∧
    (∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h) ∧
    (∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h) ∧
    (∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp 0 C.behaviorStrategy) h 0 -
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential V) h) ∧
    (∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp 0 C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M))
  have hpotentialLower : ∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      -ε / 8 =
          expect (C.belief t h) (fun _ => -ε / 8) := by
            rw [expect_const]
      _ ≤ expect (C.belief t h) (φ t h) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          rowAccountCorrectedMemoryPotential_lower
            hfloor hM1 hcorrector hvalueLower h k
  have hpotentialUpper : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1 := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      expect (C.belief t h) (φ t h) ≤
          expect (C.belief t h) (fun _ => 1) := by
        apply expect_mono
        intro k
        simpa [C, φ] using
          rowAccountCorrectedMemoryPotential_upper
            hfloor hM1 hvalueUpper h k
      _ = 1 := expect_const _ _
  have hdrift : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
        G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro opp t h
    simpa [C, φ] using
      row_accountMemoryController_beliefPotential_drift_ge
        hfloor hM1 hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          hF (discountRate s)
            (discountRate_pos (hM1.trans_le hs))
            (discountRate_le_one_of_exp_one_le
              (hexpM.trans hs)))
        hzs (fun s => hVzs (discountRate s))
        hsecant
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  have hpayoffStep : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp 0 C.behaviorStrategy) h 0 -
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential V) h := by
    intro opp t h
    simpa [C, A, V, F] using
      row_accountMemoryController_history_payoff_step
        hfloor hε.le (by linarith)
        hpayLower hpayUpper hvalueLower hvalueUpper
        (fun s hs =>
          discountRate_le_one_of_exp_one_le
            (hexpM.trans (hs)))
        (fun z s y hs hscale hyLower hyUpper =>
          hbudget z s hs M y hscale hyLower hyUpper)
        opp h
  refine ⟨hSM, hexpM, hM1, hcorrector, hpotentialLower,
    hpotentialUpper, hdrift, hpayoffStep, ?_⟩
  intro opp s₀ T
  simpa [C, φ, F] using
    sum_expected_belief_floorOccupation_le
      hε hε1 hfloor hM1 C
      (fun t k => show Fin (t + 1) from k)
      φ hpotentialLower hpotentialUpper opp s₀ (hdrift opp) T

/-- Conditional fixed-precision payoff guarantee for either secured player on
an arbitrary unit interval. -/
theorem exists_accountControllerOnUnitInterval_finiteAveragePayoff_ge_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
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
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z who - logCorrector s) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      Real.exp 1 ≤ M ∧
      let C := accountMemoryControllerOnUnitInterval
        lower (1 + ε / 9) M ε
        (fun lam z => x lam z who)
        (fun lam z => v lam z who)
        hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      ∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        0 < T →
        72 ≤ (T : ℝ) * ε ^ 2 * discountRate M →
        target s₀ - ε ≤
          G.finiteAveragePayoff s₀ T
            (Function.update opp who C.behaviorStrategy) who := by
  obtain ⟨M, hfloor, hSM, hexpM, hM1, _hcorrector,
      _hpotentialLower, _hpotentialUpper, hdrift,
      hpayoffStep, hfloorSum⟩ :=
    exists_accountControllerOnUnitInterval_bounded_beliefPotential_drift_of_puiseux
      Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hsecurity hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, hexpM, ?_⟩
  dsimp only
  let C := accountMemoryControllerOnUnitInterval
    lower (1 + ε / 9) M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountCorrectedMemoryPotential
        who (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountValueMemoryPotential who (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  have hdrift' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
            (Function.update opp who C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    exact hdrift
  have hpayoffStep' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp who C.behaviorStrategy) h who -
            G.historyContinuationEU
              (Function.update opp who C.behaviorStrategy)
              (C.beliefPotential V) h := by
    exact hpayoffStep
  have hfloorSum' : ∀ (opp : G.BehaviorProfile)
      (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp who C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M) := by
    exact hfloorSum
  intro opp s₀ T hT hhorizon
  let σ : G.BehaviorProfile :=
    Function.update opp who C.behaviorStrategy
  let payoff : ℕ → ℝ := fun t =>
    G.expectedStagePayoff σ s₀ t who
  let nextValue : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1)
  let account : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential A) t
  let floorLoss : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential F) t
  have hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) -
          floorLoss t ≤ payoff t - nextValue t := by
    intro t
    simpa [σ, payoff, nextValue, account, floorLoss] using
      G.expectedHistoryValue_payoff_step σ s₀ who
        (-9 * ε / 16)
        (C.beliefPotential A) (C.beliefPotential F)
        (C.beliefPotential V) (hpayoffStep' opp) t
  have haccountLower : ∀ t (h : G.Hist t),
      M ≤ C.beliefPotential A t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      M = expect (C.belief t h) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (C.belief t h) (A t h) := by
        apply expect_mono
        intro k
        simpa [C, A, accountLevelMemoryPotential] using
          floor_le_accountAtLevel hfloor
            (show Fin (t + 1) from k)
  have haccount0 : account 0 = M := by
    unfold account expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, A, MemoryController.belief,
      accountMemoryControllerOnUnitInterval,
      accountLevelMemoryPotential]
  have haccountT : M ≤ account T := by
    unfold account expectedHistoryValue
    calc
      M = expect (G.histDist σ s₀ T) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (G.histDist σ s₀ T)
          (C.beliefPotential A T) :=
        expect_mono _ _ _ (haccountLower T)
  have hcorrectedDriftNonneg : ∀ t (h : G.Hist t),
      0 ≤
        G.historyContinuationEU σ (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    have hrate :
        0 ≤ expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel (1 + ε / 9) M
            ((show Fin (t + 1) from k) : ℕ))) := by
      apply expect_nonneg
      intro k
      have hMk : M ≤ accountAtLevel (1 + ε / 9) M
          (show Fin (t + 1) from k) :=
        floor_le_accountAtLevel hfloor _
      exact (discountRate_pos (hM1.trans_le hMk)).le
    have hd := hdrift' opp t h
    dsimp [σ]
    nlinarith
  have hcorrectedMono : ∀ t,
      G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) (t + 1) := by
    intro t
    have hmean :=
      G.expectedHistoryValue_drift_ge σ s₀
        (fun _ _ => 0) (C.beliefPotential φ)
        (fun n h => hcorrectedDriftNonneg n h) t
    simpa [expectedHistoryValue] using hmean
  have hcorrectedMonotone :
      Monotone (fun t =>
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t) :=
    monotone_nat_of_le_succ hcorrectedMono
  have hcorrected_le_value : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ C.beliefPotential V t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    apply expect_mono
    intro k
    have hMk : M ≤ accountAtLevel (1 + ε / 9) M
        (show Fin (t + 1) from k) :=
      floor_le_accountAtLevel hfloor _
    have hlog := (logCorrector_pos (hM1.trans_le hMk)).le
    simp [C, φ, V, accountCorrectedMemoryPotential,
      accountValueMemoryPotential]
    linarith
  have hinitialCorrected :
      target s₀ - ε / 8 ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) 0 := by
    unfold expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, φ, MemoryController.belief,
      accountMemoryControllerOnUnitInterval,
      accountCorrectedMemoryPotential]
    simpa [emptyHist] using htarget s₀ M hSM
  have hnextValueLower : ∀ t,
      target s₀ - ε / 8 ≤ nextValue t := by
    intro t
    have hmono := hcorrectedMonotone (Nat.zero_le (t + 1))
    have hvalue :
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) (t + 1) ≤
          G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1) := by
      unfold expectedHistoryValue
      exact expect_mono _ _ _ (hcorrected_le_value (t + 1))
    unfold nextValue
    exact hinitialCorrected.trans (hmono.trans hvalue)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hvalueAverage :
      target s₀ - ε / 8 ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nextValue t := by
    have hsum :
        ∑ _t ∈ Finset.range T, (target s₀ - ε / 8) ≤
          ∑ t ∈ Finset.range T, nextValue t :=
      Finset.sum_le_sum fun t _ => hnextValueLower t
    have hscaled :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    have hconst :
        (T : ℝ)⁻¹ *
            (∑ _t ∈ Finset.range T, (target s₀ - ε / 8)) =
          target s₀ - ε / 8 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hTreal]
    rw [← hconst]
    exact hscaled
  have hfloorBound := hfloorSum' opp s₀ T
  have hfloorAverage :
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, floorLoss t ≤ ε / 8 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hfloorBound
        (inv_nonneg.mpr hTreal.le)
    have hrateM : 0 < discountRate M := discountRate_pos hM1
    change (T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T,
          G.expectedHistoryValue σ s₀
            (C.beliefPotential F) t) ≤ ε / 8
    calc
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T,
            G.expectedHistoryValue σ s₀
              (C.beliefPotential F) t) ≤
          (T : ℝ)⁻¹ * (9 / (ε * discountRate M)) := hscaled
      _ = 9 / ((T : ℝ) * ε * discountRate M) := by
        field_simp
      _ ≤ ε / 8 := by
        rw [div_le_div_iff₀
          (mul_pos (mul_pos hTreal hε) hrateM) (by norm_num)]
        nlinarith [sq_nonneg ε]
  have hresult :=
    average_payoff_ge_target_sub_epsilon_of_account_bounds
      hε.le payoff nextValue account floorLoss hstep hT
      (by rw [haccount0]; exact haccountT)
      hvalueAverage hfloorAverage
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simpa [payoff, σ] using hresult

/-- Conditional fixed-precision one-sided payoff guarantee. A Puiseux
derivative envelope and a tail lower bound for the initial corrected value
produce one behavioral strategy that secures the target against every opponent
at every horizon satisfying the explicit occupation threshold. -/
theorem exists_rowAccountController_finiteAveragePayoff_ge_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z 0 - logCorrector s) :
    ∃ M : ℝ,
      ∃ hfloor : IsValidScale (1 + ε / 9) M,
      Real.exp 1 ≤ M ∧
      let C := accountMemoryController (1 + ε / 9) M ε
        (fun lam z => x lam z 0)
        (fun lam z => v lam z 0)
        hfloor
        hpayLower hpayUpper hvalueLower hvalueUpper hε.le
        (by linarith)
      ∀ (opp : G.BehaviorProfile) (s₀ : G.State) (T : ℕ),
        0 < T →
        72 ≤ (T : ℝ) * ε ^ 2 * discountRate M →
        target s₀ - ε ≤
          G.finiteAveragePayoff s₀ T
            (Function.update opp 0 C.behaviorStrategy) 0 := by
  obtain ⟨M, hfloor, hSM, hexpM, hM1, hcorrector,
      hpotentialLower, hpotentialUpper, hdrift,
      hpayoffStep, hfloorSum⟩ :=
    exists_rowAccountController_bounded_beliefPotential_drift_of_puiseux
      Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound
  refine ⟨M, hfloor, hexpM, ?_⟩
  dsimp only
  let C := accountMemoryController (1 + ε / 9) M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  let φ : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountCorrectedMemoryPotential (1 + ε / 9) M v n hmem k
  let A : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      accountLevelMemoryPotential (1 + ε / 9) M n hmem k
  let V : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n hmem k =>
      rowAccountValueMemoryPotential (1 + ε / 9) M v n hmem k
  let F : (n : ℕ) → G.Hist n → C.Mem n → ℝ :=
    fun n _ k =>
      accountFloorIndicator (show Fin (n + 1) from k)
  have hpotentialLower' : ∀ t (h : G.Hist t),
      -ε / 8 ≤ C.beliefPotential φ t h := by
    simpa [C, φ] using hpotentialLower
  have hpotentialUpper' : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ 1 := by
    simpa [C, φ] using hpotentialUpper
  have hdrift' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      ε / 8 *
          expect (C.belief t h) (fun k =>
            discountRate (accountAtLevel (1 + ε / 9) M
              ((show Fin (t + 1) from k) : ℕ))) ≤
          G.historyContinuationEU
            (Function.update opp 0 C.behaviorStrategy)
            (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    exact hdrift
  have hpayoffStep' : ∀ (opp : G.BehaviorProfile) t (h : G.Hist t),
      -9 * ε / 16 +
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential A) h -
            C.beliefPotential A t h -
            C.beliefPotential F t h ≤
          G.stageEUAt
              (Function.update opp 0 C.behaviorStrategy) h 0 -
            G.historyContinuationEU
              (Function.update opp 0 C.behaviorStrategy)
              (C.beliefPotential V) h := by
    exact hpayoffStep
  have hfloorSum' : ∀ (opp : G.BehaviorProfile)
      (s₀ : G.State) (T : ℕ),
      ∑ t ∈ Finset.range T,
          G.expectedHistoryValue
            (Function.update opp 0 C.behaviorStrategy) s₀
            (C.beliefPotential F) t ≤
        9 / (ε * discountRate M) := by
    exact hfloorSum
  intro opp s₀ T hT hhorizon
  let σ : G.BehaviorProfile :=
    Function.update opp 0 C.behaviorStrategy
  let payoff : ℕ → ℝ := fun t =>
    G.expectedStagePayoff σ s₀ t 0
  let nextValue : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1)
  let account : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential A) t
  let floorLoss : ℕ → ℝ := fun t =>
    G.expectedHistoryValue σ s₀ (C.beliefPotential F) t
  have hstep : ∀ t,
      -9 * ε / 16 + (account (t + 1) - account t) -
          floorLoss t ≤ payoff t - nextValue t := by
    intro t
    simpa [σ, payoff, nextValue, account, floorLoss] using
      G.expectedHistoryValue_payoff_step σ s₀ 0
        (-9 * ε / 16)
        (C.beliefPotential A) (C.beliefPotential F)
        (C.beliefPotential V) (hpayoffStep' opp) t
  have haccountLower : ∀ t (h : G.Hist t),
      M ≤ C.beliefPotential A t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    calc
      M = expect (C.belief t h) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (C.belief t h) (A t h) := by
        apply expect_mono
        intro k
        simpa [C, A, accountLevelMemoryPotential] using
          floor_le_accountAtLevel hfloor
            (show Fin (t + 1) from k)
  have haccount0 : account 0 = M := by
    unfold account expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, A, MemoryController.belief,
      accountMemoryController, accountLevelMemoryPotential]
  have haccountT : M ≤ account T := by
    unfold account expectedHistoryValue
    calc
      M = expect (G.histDist σ s₀ T) (fun _ => M) := by
        rw [expect_const]
      _ ≤ expect (G.histDist σ s₀ T)
          (C.beliefPotential A T) :=
        expect_mono _ _ _ (haccountLower T)
  have hcorrectedDriftNonneg : ∀ t (h : G.Hist t),
      0 ≤
        G.historyContinuationEU σ (C.beliefPotential φ) h -
          C.beliefPotential φ t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    have hrate :
        0 ≤ expect (C.belief t h) (fun k =>
          discountRate (accountAtLevel (1 + ε / 9) M
            ((show Fin (t + 1) from k) : ℕ))) := by
      apply expect_nonneg
      intro k
      have hMk : M ≤ accountAtLevel (1 + ε / 9) M
          (show Fin (t + 1) from k) :=
        floor_le_accountAtLevel hfloor _
      exact (discountRate_pos (hM1.trans_le hMk)).le
    have hd := hdrift' opp t h
    dsimp [σ]
    nlinarith
  have hcorrectedMono : ∀ t,
      G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) (t + 1) := by
    intro t
    have hmean :=
      G.expectedHistoryValue_drift_ge σ s₀
        (fun _ _ => 0) (C.beliefPotential φ)
        (fun n h => hcorrectedDriftNonneg n h) t
    simpa [expectedHistoryValue] using hmean
  have hcorrectedMonotone :
      Monotone (fun t =>
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) t) :=
    monotone_nat_of_le_succ hcorrectedMono
  have hcorrected_le_value : ∀ t (h : G.Hist t),
      C.beliefPotential φ t h ≤ C.beliefPotential V t h := by
    intro t h
    letI : Fintype (C.Mem t) := C.finiteMem t
    unfold MemoryController.beliefPotential
    apply expect_mono
    intro k
    have hMk : M ≤ accountAtLevel (1 + ε / 9) M
        (show Fin (t + 1) from k) :=
      floor_le_accountAtLevel hfloor _
    have hlog := (logCorrector_pos (hM1.trans_le hMk)).le
    simp [C, φ, V, rowAccountCorrectedMemoryPotential,
      rowAccountValueMemoryPotential]
    linarith
  have hinitialCorrected :
      target s₀ - ε / 8 ≤
        G.expectedHistoryValue σ s₀
          (C.beliefPotential φ) 0 := by
    unfold expectedHistoryValue MemoryController.beliefPotential
    rw [G.histDist_zero, expect_pure]
    simp [C, φ, MemoryController.belief,
      accountMemoryController, rowAccountCorrectedMemoryPotential]
    simpa [emptyHist] using htarget s₀ M hSM
  have hnextValueLower : ∀ t,
      target s₀ - ε / 8 ≤ nextValue t := by
    intro t
    have hmono := hcorrectedMonotone (Nat.zero_le (t + 1))
    have hvalue :
        G.expectedHistoryValue σ s₀ (C.beliefPotential φ) (t + 1) ≤
          G.expectedHistoryValue σ s₀ (C.beliefPotential V) (t + 1) := by
      unfold expectedHistoryValue
      exact expect_mono _ _ _ (hcorrected_le_value (t + 1))
    unfold nextValue
    exact hinitialCorrected.trans (hmono.trans hvalue)
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hvalueAverage :
      target s₀ - ε / 8 ≤
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, nextValue t := by
    have hsum :
        ∑ _t ∈ Finset.range T, (target s₀ - ε / 8) ≤
          ∑ t ∈ Finset.range T, nextValue t :=
      Finset.sum_le_sum fun t _ => hnextValueLower t
    have hscaled :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
    have hconst :
        (T : ℝ)⁻¹ *
            (∑ _t ∈ Finset.range T, (target s₀ - ε / 8)) =
          target s₀ - ε / 8 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hTreal]
    rw [← hconst]
    exact hscaled
  have hfloorBound := hfloorSum' opp s₀ T
  have hfloorAverage :
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, floorLoss t ≤ ε / 8 := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hfloorBound
        (inv_nonneg.mpr hTreal.le)
    have hrateM : 0 < discountRate M := discountRate_pos hM1
    change (T : ℝ)⁻¹ *
        (∑ t ∈ Finset.range T,
          G.expectedHistoryValue σ s₀
            (C.beliefPotential F) t) ≤ ε / 8
    calc
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T,
            G.expectedHistoryValue σ s₀
              (C.beliefPotential F) t) ≤
          (T : ℝ)⁻¹ * (9 / (ε * discountRate M)) := hscaled
      _ = 9 / ((T : ℝ) * ε * discountRate M) := by
        field_simp
      _ ≤ ε / 8 := by
        rw [div_le_div_iff₀
          (mul_pos (mul_pos hTreal hε) hrateM) (by norm_num)]
        nlinarith [sq_nonneg ε]
  have hresult :=
    average_payoff_ge_target_sub_epsilon_of_account_bounds
      hε.le payoff nextValue account floorLoss hstep hT
      (by rw [haccount0]; exact haccountT)
      hvalueAverage hfloorAverage
  rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simpa [payoff, σ] using hresult

/-- Certificate-facing symmetric account theorem at one fixed precision. -/
theorem account_isOneSidedGuaranteeCertificateAt_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ) (s₀ : G.State)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
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
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z who - logCorrector s) :
    G.IsOneSidedGuaranteeCertificateAt
      s₀ who (target s₀) ε := by
  obtain ⟨M, hfloor, hexpM, hsecure⟩ :=
    exists_accountControllerOnUnitInterval_finiteAveragePayoff_ge_of_puiseux
      target Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hsecurity hβ hlam0 hderiv hbound htarget
  let C := accountMemoryControllerOnUnitInterval
    lower (1 + ε / 9) M ε
    (fun lam z => x lam z who)
    (fun lam z => v lam z who)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  have hrateM : 0 < discountRate M :=
    discountRate_pos
      ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hexpM)
  have hcoef : 0 < ε ^ 2 * discountRate M :=
    mul_pos (sq_pos_of_pos hε) hrateM
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (72 / (ε ^ 2 * discountRate M))
  let T₀ := max 2 (N + 1)
  refine ⟨C.behaviorStrategy, T₀, le_max_left _ _, ?_⟩
  intro opp T hT
  have hNsucc : N + 1 ≤ T :=
    (le_max_right 2 (N + 1)).trans hT
  have hTpos : 0 < T :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 2 (N + 1)).trans hT)
  have hNT : (N : ℝ) < (T : ℝ) := by
    exact_mod_cast (show N < T by omega)
  have hquot : 72 / (ε ^ 2 * discountRate M) < (T : ℝ) :=
    hN.trans hNT
  have hhorizonStrict :
      72 < (T : ℝ) * (ε ^ 2 * discountRate M) :=
    (div_lt_iff₀ hcoef).mp hquot
  have hhorizon :
      72 ≤ (T : ℝ) * ε ^ 2 * discountRate M := by
    nlinarith
  simpa [C] using hsecure opp s₀ T hTpos hhorizon

/-- Certificate-facing form of the conditional account theorem at one fixed
precision. The securing controller and horizon threshold are chosen before the
opponent profile. -/
theorem rowAccount_isOneSidedGuaranteeCertificateAt_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {ε : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (Starget : ℝ) (s₀ : G.State)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεquarter : ε < 1 / 4)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ z s, Starget ≤ s →
      target z - ε / 8 ≤
        v (discountRate s) z 0 - logCorrector s) :
    G.IsOneSidedGuaranteeCertificateAt s₀ 0 (target s₀) ε := by
  obtain ⟨M, hfloor, hexpM, hsecure⟩ :=
    exists_rowAccountController_finiteAveragePayoff_ge_of_puiseux
      target Starget hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound htarget
  let C := accountMemoryController (1 + ε / 9) M ε
    (fun lam z => x lam z 0)
    (fun lam z => v lam z 0)
    hfloor hpayLower hpayUpper hvalueLower hvalueUpper hε.le
      (by linarith)
  have hrateM : 0 < discountRate M :=
    discountRate_pos
      ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hexpM)
  have hcoef : 0 < ε ^ 2 * discountRate M :=
    mul_pos (sq_pos_of_pos hε) hrateM
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (72 / (ε ^ 2 * discountRate M))
  let T₀ := max 2 (N + 1)
  refine ⟨C.behaviorStrategy, T₀, le_max_left _ _, ?_⟩
  intro opp T hT
  have hNsucc : N + 1 ≤ T :=
    (le_max_right 2 (N + 1)).trans hT
  have hTpos : 0 < T :=
    lt_of_lt_of_le (by norm_num) ((le_max_left 2 (N + 1)).trans hT)
  have hNT : (N : ℝ) < (T : ℝ) := by
    exact_mod_cast (show N < T by omega)
  have hquot : 72 / (ε ^ 2 * discountRate M) < (T : ℝ) :=
    hN.trans hNT
  have hhorizonStrict :
      72 < (T : ℝ) * (ε ^ 2 * discountRate M) :=
    (div_lt_iff₀ hcoef).mp hquot
  have hhorizon :
      72 ≤ (T : ℝ) * ε ^ 2 * discountRate M := by
    nlinarith
  simpa [C] using hsecure opp s₀ T hTpos hhorizon

/-- Right-convergence of either player's discounted value coordinate gives the
corrected-value tail required by the account construction, uniformly over the
finite state space. -/
theorem exists_tail_correctedValue_lower_of_tendsto_for
    {G : StochasticGame (Fin 2)}
    [Finite G.State] {who : Fin 2}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (target : G.State → ℝ)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z who)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z)))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z who - logCorrector s := by
  have hrate :
      Tendsto discountRate atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_discountRate_atTop, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact discountRate_pos hs
  have hvalue : ∀ z,
      ∀ᶠ s : ℝ in atTop,
        target z - η / 16 <
          v (discountRate s) z who := by
    intro z
    exact (tendsto_order.1 ((hlimit z).comp hrate)).1
      (target z - η / 16) (by linarith)
  have hvalues :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 16 <
          v (discountRate s) z who := by
    rw [Filter.eventually_all]
    exact hvalue
  have hcorrector :
      ∀ᶠ s : ℝ in atTop, logCorrector s < η / 16 :=
    (tendsto_order.1 tendsto_logCorrector_atTop).2
      (η / 16) (by linarith)
  have htail :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 8 ≤
          v (discountRate s) z who - logCorrector s := by
    filter_upwards [hvalues, hcorrector] with s hs hlog
    intro z
    have hz := hs z
    linarith
  rcases eventually_atTop.1 htail with ⟨S, hS⟩
  exact ⟨S, fun z s hs => hS s hs z⟩

/-- Convergence of the discounted values from positive discount rates gives
the corrected-value tail required by the account construction. Finiteness of
the state space makes the convergence threshold uniform in the state. -/
theorem exists_tail_correctedValue_lower_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State]
    {v : ℝ → G.State → Payoff (Fin 2)}
    (target : G.State → ℝ)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z)))
    {η : ℝ} (hη : 0 < η) :
    ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z 0 - logCorrector s := by
  have hrate :
      Tendsto discountRate atTop
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_discountRate_atTop, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact discountRate_pos hs
  have hvalue : ∀ z,
      ∀ᶠ s : ℝ in atTop,
        target z - η / 16 <
          v (discountRate s) z 0 := by
    intro z
    exact (tendsto_order.1 ((hlimit z).comp hrate)).1
      (target z - η / 16) (by linarith)
  have hvalues :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 16 <
          v (discountRate s) z 0 := by
    rw [Filter.eventually_all]
    exact hvalue
  have hcorrector :
      ∀ᶠ s : ℝ in atTop, logCorrector s < η / 16 :=
    (tendsto_order.1 tendsto_logCorrector_atTop).2
      (η / 16) (by linarith)
  have htail :
      ∀ᶠ s : ℝ in atTop, ∀ z,
        target z - η / 8 ≤
          v (discountRate s) z 0 - logCorrector s := by
    filter_upwards [hvalues, hcorrector] with s hs hlog
    intro z
    have hz := hs z
    linarith
  rcases eventually_atTop.1 htail with ⟨S, hS⟩
  exact ⟨S, fun z s hs => hS s hs z⟩

/-- Full conditional one-sided securing certificate for either player on an
arbitrary unit payoff/value interval. -/
theorem account_isOneSidedGuaranteeCertificate_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
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
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ η : ℝ, 0 < η → ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z who - logCorrector s) :
    G.IsOneSidedGuaranteeCertificate s₀ who (target s₀) := by
  intro δ hδ
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hεquarter : ε < 1 / 4 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ < 1 / 4 := by norm_num
  have hεδ : ε ≤ δ := by
    calc
      ε ≤ δ / 2 := min_le_left _ _
      _ ≤ δ := by linarith
  obtain ⟨S, hS⟩ := htarget ε hε
  obtain ⟨σwho, T₀, hT₀, hsecure⟩ :=
    account_isOneSidedGuaranteeCertificateAt_of_puiseux
      target S s₀ hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hsecurity hβ hlam0 hderiv hbound hS
  refine ⟨σwho, T₀, hT₀, ?_⟩
  intro opp T hT
  have hbase := hsecure opp T hT
  linarith

/-- Symmetric one-sided account certificate from a Puiseux derivative
envelope and right-convergence of the secured discounted-value coordinate. -/
theorem account_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {who : Fin 2} {lower : ℝ}
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
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
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z who) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z who)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsOneSidedGuaranteeCertificate s₀ who (target s₀) := by
  apply account_isOneSidedGuaranteeCertificate_of_puiseux
    target s₀ hpayLower hpayUpper hvalueLower hvalueUpper
    hsecurity hβ hlam0 hderiv hbound
  intro η hη
  exact exists_tail_correctedValue_lower_of_tendsto_for
    target hlimit hη

/-- The column account certificate in the natural zero-sum normalization:
player one's own payoff and value lie in `[-1,0]`. -/
theorem colAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, -1 ≤ G.stagePayoff z a 1)
    (hpayUpper : ∀ z a, G.stagePayoff z a 1 ≤ 0)
    (hvalueLower : ∀ lam z, -1 ≤ v lam z 1)
    (hvalueUpper : ∀ lam z, v lam z 1 ≤ 0)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 1) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsOneSidedGuaranteeCertificate s₀ 1 (target s₀) := by
  apply account_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    (who := (1 : Fin 2)) (lower := (-1 : ℝ))
    target s₀ hpayLower
    (fun z a => by simpa using hpayUpper z a)
    hvalueLower
    (fun lam z => by simpa using hvalueUpper lam z)
    (isDiscountedStationarySecurityFamily_one hF hzs hVzs)
    hβ hlam0 hderiv hbound hlimit

/-- A player-zero one-sided certificate is a mechanism-neutral row tracking
certificate. -/
theorem isRowTrackingCertificate_of_oneSidedGuarantee
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {w : ℝ}
    (h : G.IsOneSidedGuaranteeCertificate s₀ 0 w) :
    G.IsRowTrackingCertificate w s₀ := by
  intro ε hε
  obtain ⟨σ, T₀, _hT₀, hsecure⟩ := h ε hε
  refine ⟨σ, T₀, ?_⟩
  intro dev T hT
  simpa using hsecure (G.pairBehaviorProfile σ dev) T hT

/-- A player-one one-sided certificate at value `-w` is the
mechanism-neutral column securing certificate. -/
theorem securesCol_of_oneSidedGuarantee
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {w : ℝ}
    (h : G.IsOneSidedGuaranteeCertificate s₀ 1 (-w)) :
    G.SecuresCol w s₀ := by
  intro ε hε
  obtain ⟨σ, T₀, _hT₀, hsecure⟩ := h ε hε
  refine ⟨σ, T₀, ?_⟩
  intro dev T hT
  simpa using hsecure (G.pairBehaviorProfile dev σ) T hT

/-- Finite-index two-player counterpart of the Bool one-sided-certificate
wrapper: two security certificates assemble into a zero-sum uniform
equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_of_oneSidedGuarantees
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (hzs : G.IsZeroSum) (s₀ : G.State) (w : ℝ)
    (hrow : G.IsOneSidedGuaranteeCertificate s₀ 0 w)
    (hcol : G.IsOneSidedGuaranteeCertificate s₀ 1 (-w)) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then w else -w) := by
  exact G.uniformValue_of_rowColumnTrackingCertificates
    hzs w s₀
    (isRowTrackingCertificate_of_oneSidedGuarantee hrow)
    (securesCol_of_oneSidedGuarantee hcol)

/-- Full conditional one-sided securing certificate. The Puiseux envelope is
fixed for the discounted-value family, while the corrected-value tail
threshold may depend on the requested precision. -/
theorem rowAccount_isOneSidedGuaranteeCertificate_of_puiseux
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (htarget : ∀ η : ℝ, 0 < η → ∃ S : ℝ, ∀ z s, S ≤ s →
      target z - η / 8 ≤
        v (discountRate s) z 0 - logCorrector s) :
    G.IsOneSidedGuaranteeCertificate s₀ 0 (target s₀) := by
  intro δ hδ
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hεquarter : ε < 1 / 4 := by
    calc
      ε ≤ 1 / 8 := min_le_right _ _
      _ < 1 / 4 := by norm_num
  have hεδ : ε ≤ δ := by
    calc
      ε ≤ δ / 2 := min_le_left _ _
      _ ≤ δ := by linarith
  obtain ⟨S, hS⟩ := htarget ε hε
  obtain ⟨σwho, T₀, hT₀, hsecure⟩ :=
    rowAccount_isOneSidedGuaranteeCertificateAt_of_puiseux
      target S s₀ hε hε1 hεquarter
      hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound hS
  refine ⟨σwho, T₀, hT₀, ?_⟩
  intro opp T hT
  have hbase := hsecure opp T hT
  linarith

/-- The one-sided account certificate from the standard analytic inputs:
a Puiseux derivative envelope and convergence of the discounted values from
positive discount rates. -/
theorem rowAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsOneSidedGuaranteeCertificate s₀ 0 (target s₀) := by
  apply rowAccount_isOneSidedGuaranteeCertificate_of_puiseux
    target s₀ hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs hVzs hβ hlam0 hderiv hbound
  intro η hη
  exact exists_tail_correctedValue_lower_of_tendsto
    target hlimit hη

end MertensNeymanAccount
end StochasticGame
end GameTheory
