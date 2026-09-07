import UniformEquilibrium.Finite.RationalBooleanRootGrid
import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-! # Exact rational payoff and response-cap evaluation of finite quitting words -/

namespace GameTheory

open GameTheory.Finite
open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {players : ℕ}

/-- A rational terminal reward table for a finite quitting game. -/
abbrev RationalQuittingReward (players : ℕ) :=
  {S : Finset (Fin players) // S.Nonempty} → Fin players → ℚ

/-- A rational product root, including the proofs needed to compile each
coordinate to an actual Boolean probability law. -/
structure RationalQuittingRoot (players : ℕ) where
  probability : Fin players → ℚ
  nonnegative : ∀ who, 0 ≤ probability who
  le_one : ∀ who, probability who ≤ 1

/-- Compile a rational terminal table to the real quitting-game semantics. -/
def rationalQuittingRewardToReal
    (reward : RationalQuittingReward players) :
    {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players) :=
  fun terminal who => (reward terminal who : ℝ)

/-- Compile a rational product root to the actual `PMF Bool` root interface. -/
noncomputable def RationalQuittingRoot.toPMF
    (root : RationalQuittingRoot players) : Fin players → PMF Bool :=
  fun who => bernoulliBool (root.probability who : ℝ)
    (by exact_mod_cast root.nonnegative who)
    (by exact_mod_cast root.le_one who)

@[simp] theorem RationalQuittingRoot.toPMF_true_toReal
    (root : RationalQuittingRoot players) (who : Fin players) :
    (root.toPMF who true).toReal = (root.probability who : ℝ) := by
  simp [RationalQuittingRoot.toPMF]

@[simp] theorem RationalQuittingRoot.toPMF_false_toReal
    (root : RationalQuittingRoot players) (who : Fin players) :
    (root.toPMF who false).toReal = 1 - (root.probability who : ℝ) := by
  simp [RationalQuittingRoot.toPMF]

/-- Rational one-stage payoff, with `tail` used only at the all-Continue
profile. -/
def rationalQuittingRootPayoff
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (action : Fin players → Bool) (who : Fin players) : ℚ :=
  if h : (quittingQuitters action).Nonempty then
    reward ⟨quittingQuitters action, h⟩ who
  else tail who

/-- The Boolean normal-form table at a rational quitting row. -/
def rationalQuittingBooleanPayoff
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ) :
    RationalBooleanPayoff players :=
  rationalQuittingRootPayoff reward tail

/-- Exact rational expected payoff at one product root. -/
def rationalQuittingRootExpectedPayoff
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (root : RationalQuittingRoot players) (who : Fin players) : ℚ :=
  rationalBooleanExpectedPayoff (rationalQuittingBooleanPayoff reward tail)
    root.probability who

/-- Rational payoff from forcing one endpoint at a product root. -/
def rationalQuittingRootPurePayoff
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (root : RationalQuittingRoot players) (who : Fin players) (action : Bool) : ℚ :=
  rationalBooleanPurePayoff (rationalQuittingBooleanPayoff reward tail)
    root.probability who action

/-- Exact rational prescribed-payoff fold along a finite chronological word. -/
def rationalQuittingFiniteWordPayoff
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players))
    (tail : Fin players → ℚ) : Fin players → ℚ :=
  roots.foldr (fun root value =>
    rationalQuittingRootExpectedPayoff reward value root) tail

/-- One rational unrestricted-response Bellman step. -/
def rationalQuittingCapStep
    (reward : RationalQuittingReward players)
    (root : RationalQuittingRoot players) (who : Fin players)
    (suffixCap : ℚ) : ℚ :=
  max
    (rationalQuittingRootPurePayoff reward 0 root who true)
    (rationalQuittingRootPurePayoff reward (Function.update 0 who suffixCap)
      root who false)

/-- Exact rational unrestricted-response cap fold along a finite word. -/
def rationalQuittingFiniteWordCap
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players))
    (who : Fin players) (suffixCap : ℚ) : ℚ :=
  roots.foldr (fun root cap => rationalQuittingCapStep reward root who cap)
    suffixCap

/-- Terminal payoff/cap boundary supplied by Always Continue. -/
def rationalQuittingAlwaysContinueBoundary
    (reward : RationalQuittingReward players) :
    (Fin players → ℚ) × (Fin players → ℚ) :=
  (0, fun who => max 0 (reward (quittingSingletonTerminal who) who))

/-- Fully executable payoff/cap pair for a rational finite word followed by
Always Continue. -/
def rationalQuittingFiniteWordSemanticPair
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) :
    (Fin players → ℚ) × (Fin players → ℚ) :=
  (rationalQuittingFiniteWordPayoff reward roots 0,
    fun who => rationalQuittingFiniteWordCap reward roots who
      (max 0 (reward (quittingSingletonTerminal who) who)))

theorem quittingRootPayoff_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (action : Fin players → Bool) (who : Fin players) :
    quittingRootPayoff (rationalQuittingRewardToReal reward)
        (fun player => (tail player : ℝ)) action who =
      (rationalQuittingRootPayoff reward tail action who : ℝ) := by
  unfold quittingRootPayoff rationalQuittingRootPayoff
  split <;> rfl

theorem quittingRootExpectedPayoff_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (root : RationalQuittingRoot players) (who : Fin players) :
    quittingRootExpectedPayoff (rationalQuittingRewardToReal reward)
        (fun player => (tail player : ℝ)) root.toPMF who =
      (rationalQuittingRootExpectedPayoff reward tail root who : ℝ) := by
  unfold quittingRootExpectedPayoff rationalQuittingRootExpectedPayoff
    rationalBooleanExpectedPayoff rationalBooleanProfileWeight
    rationalQuittingBooleanPayoff
  rw [_root_.Math.Probability.expect_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro action _
  rw [pmfPi_apply, ENNReal.toReal_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro player _
    cases haction : action player
    · simp
    · simp
  · exact quittingRootPayoff_rationalQuitting_eq_cast reward tail action who

/-- Forcing one rational coordinate to a pure Boolean endpoint. -/
def RationalQuittingRoot.force
    (root : RationalQuittingRoot players) (who : Fin players) (action : Bool) :
    RationalQuittingRoot players where
  probability := Function.update root.probability who (if action then 1 else 0)
  nonnegative := by
    intro player
    by_cases hplayer : player = who
    · subst player
      cases action <;> simp
    · simp [hplayer, root.nonnegative player]
  le_one := by
    intro player
    by_cases hplayer : player = who
    · subst player
      cases action <;> simp
    · simp [hplayer, root.le_one player]

theorem RationalQuittingRoot.force_toPMF
    (root : RationalQuittingRoot players) (who : Fin players) (action : Bool) :
    (root.force who action).toPMF =
      Function.update root.toPMF who (PMF.pure action) := by
  funext player
  apply eq_of_forall_toReal_eq
  intro choice
  by_cases hplayer : player = who
  · subst player
    cases action <;> cases choice <;>
      simp [RationalQuittingRoot.force, PMF.pure_apply]
  · cases choice <;>
      simp [RationalQuittingRoot.force, hplayer]

theorem quittingRootPurePayoff_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players) (tail : Fin players → ℚ)
    (root : RationalQuittingRoot players) (who : Fin players) (action : Bool) :
    (if action then
        quittingRootQuitPayoff (rationalQuittingRewardToReal reward)
          (fun player => (tail player : ℝ)) root.toPMF who
      else
        quittingRootContinuePayoff (rationalQuittingRewardToReal reward)
          (fun player => (tail player : ℝ)) root.toPMF who) =
      (rationalQuittingRootPurePayoff reward tail root who action : ℝ) := by
  have hexpected := quittingRootExpectedPayoff_rationalQuitting_eq_cast
    reward tail (root.force who action) who
  rw [RationalQuittingRoot.force_toPMF] at hexpected
  cases action <;> exact hexpected

theorem quittingFiniteRootWordPayoff_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players))
    (tail : Fin players → ℚ) (who : Fin players) :
    quittingFiniteRootWordPayoff (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF)
        (fun player => (tail player : ℝ)) who =
      (rationalQuittingFiniteWordPayoff reward roots tail who : ℝ) := by
  induction roots generalizing who with
  | nil => rfl
  | cons root roots ih =>
      simp only [List.map_cons, quittingFiniteRootWordPayoff, List.foldr_cons,
        rationalQuittingFiniteWordPayoff]
      have hsuffix :
          quittingFiniteRootWordPayoff (rationalQuittingRewardToReal reward)
              (List.map RationalQuittingRoot.toPMF roots)
              (fun player => (tail player : ℝ)) =
            fun player =>
              (rationalQuittingFiniteWordPayoff reward roots tail player : ℝ) := by
        funext player
        exact ih player
      change quittingRootExpectedPayoff (rationalQuittingRewardToReal reward)
          (quittingFiniteRootWordPayoff (rationalQuittingRewardToReal reward)
            (List.map RationalQuittingRoot.toPMF roots)
            (fun player => (tail player : ℝ))) root.toPMF who = _
      rw [hsuffix]
      exact quittingRootExpectedPayoff_rationalQuitting_eq_cast reward
        (rationalQuittingFiniteWordPayoff reward roots tail) root who

private theorem quittingCapStep_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players)
    (root : RationalQuittingRoot players) (who : Fin players)
    (suffixCap : ℚ) :
    max
        (quittingRootQuitPayoff (rationalQuittingRewardToReal reward) 0
          root.toPMF who)
        (quittingRootContinuePayoff (rationalQuittingRewardToReal reward)
          (Function.update 0 who (suffixCap : ℝ)) root.toPMF who) =
      (rationalQuittingCapStep reward root who suffixCap : ℝ) := by
  rw [rationalQuittingCapStep, Rat.cast_max]
  congr 1
  · have hzero :
        (0 : Fin players → ℝ) =
          fun player => ((0 : Fin players → ℚ) player : ℝ) := by
      funext player
      simp
    rw [hzero]
    simpa only [Bool.true_eq, ↓reduceIte] using
      (quittingRootPurePayoff_rationalQuitting_eq_cast
        reward (0 : Fin players → ℚ) root who true)
  · have hpure := quittingRootPurePayoff_rationalQuitting_eq_cast reward
      (Function.update 0 who suffixCap) root who false
    have htail :
        Function.update (0 : Fin players → ℝ) who (suffixCap : ℝ) =
          fun player =>
            ((Function.update (0 : Fin players → ℚ) who suffixCap) player : ℝ) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp
      · simp [hplayer]
    rw [htail]
    simpa only [Bool.false_eq_true, ↓reduceIte] using hpure

theorem quittingFiniteRootWordCap_rationalQuitting_eq_cast
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players))
    (who : Fin players) (suffixCap : ℚ) :
    quittingFiniteRootWordCap (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF) who (suffixCap : ℝ) =
      (rationalQuittingFiniteWordCap reward roots who suffixCap : ℝ) := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      simp only [List.map_cons, quittingFiniteRootWordCap, List.foldr_cons,
        rationalQuittingFiniteWordCap]
      change max
          (quittingRootQuitPayoff (rationalQuittingRewardToReal reward) 0
            root.toPMF who)
          (quittingRootContinuePayoff (rationalQuittingRewardToReal reward)
            (Function.update 0 who
              (quittingFiniteRootWordCap (rationalQuittingRewardToReal reward)
                (List.map RationalQuittingRoot.toPMF roots) who (suffixCap : ℝ)))
            root.toPMF who) = _
      rw [ih]
      exact quittingCapStep_rationalQuitting_eq_cast reward root who
        (rationalQuittingFiniteWordCap reward roots who suffixCap)

/-- The executable rational fold is exactly the actual terminal semantic pair
of its literal finite root stack followed by Always Continue. In particular,
the computed cap is the supremum over all behavioral unilateral responses. -/
theorem quittingTerminalSemanticPair_rationalFiniteWord_eq_cast
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) :
    quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) =
      (fun who => ((rationalQuittingFiniteWordSemanticPair reward roots).1 who : ℝ),
        fun who =>
          ((rationalQuittingFiniteWordSemanticPair reward roots).2 who : ℝ)) := by
  apply Prod.ext
  · funext who
    change quittingTerminalPayoff (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who = _
    rw [quittingTerminalPayoff_literalRootStack_eq_wordPayoff]
    have htail :
        quittingTerminalPayoff (rationalQuittingRewardToReal reward)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)) =
          (0 : Fin players → ℝ) := by
      funext player
      exact quittingTerminalPayoff_quittingAlwaysContinue
        (rationalQuittingRewardToReal reward) player
    rw [htail]
    change quittingFiniteRootWordPayoff (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF) 0 who =
      ((rationalQuittingFiniteWordSemanticPair reward roots).1 who : ℝ)
    have hzero :
        (0 : Fin players → ℝ) =
          fun player => ((0 : Fin players → ℚ) player : ℝ) := by
      funext player
      simp
    rw [hzero]
    exact quittingFiniteRootWordPayoff_rationalQuitting_eq_cast
      reward roots 0 who
  · funext who
    change quittingContinuationBestResponseValue (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who = _
    rw [quittingContinuationBestResponseValue_literalRootStack_eq_capFold,
      quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
    change quittingFiniteRootWordCap (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF) who
          (max (0 : ℝ) (reward (quittingSingletonTerminal who) who : ℝ)) =
      ((rationalQuittingFiniteWordSemanticPair reward roots).2 who : ℝ)
    have hseed :
        max (0 : ℝ) (reward (quittingSingletonTerminal who) who : ℝ) =
          (max (0 : ℚ) (reward (quittingSingletonTerminal who) who) : ℚ) := by
      simpa only [Rat.cast_zero] using
        (Rat.cast_max (K := ℝ) (0 : ℚ)
          (reward (quittingSingletonTerminal who) who)).symm
    rw [hseed]
    exact quittingFiniteRootWordCap_rationalQuitting_eq_cast reward roots who
      (max 0 (reward (quittingSingletonTerminal who) who))

end GameTheory
