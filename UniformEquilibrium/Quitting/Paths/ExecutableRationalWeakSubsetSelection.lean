import UniformEquilibrium.Quitting.Paths.ExecutableRationalSelectedOwnerRates
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakSubsetSelection

/-! # Actual-source and unrestricted-cap joins for rational weak-subset selection

Real designated-owner exclusion and singleton-column preemption for a rational
table transfer to the exact rational finite-word predicates.  The executable
first-hit word then retains its phase/date bounds while its rational debt bound
becomes an unrestricted behavioral terminal approximate-Nash certificate for
the very same literal root stack.
-/

namespace GameTheory

variable {players : ℕ}

/-- Real weak exclusion on literal words restricts exactly to rational root
words; no payoff approximation is used. -/
theorem rationalQuittingFiniteWordOwnerExclusionOn_of_real
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : QuittingFiniteWordWeakSubsetExclusion
      (rationalQuittingRewardToReal reward) owners) :
    RationalQuittingFiniteWordOwnerExclusionOn reward owners := by
  intro roots
  obtain ⟨owner, howner, hpayoff⟩ := hWE (roots.map RationalQuittingRoot.toPMF)
  refine ⟨owner, howner, ?_⟩
  have hpair := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots
  have hcoordinate := congrFun (congrArg Prod.fst hpair) owner
  have hcoordinate' : quittingTerminalPayoff
      (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) owner =
      ((rationalQuittingFiniteWordSemanticPair reward roots).1 owner : ℝ) := by
    simpa only [quittingTerminalSemanticPair] using hcoordinate
  have hreal : ((rationalQuittingFiniteWordSemanticPair reward roots).1 owner : ℝ) ≤
      (reward (quittingSingletonTerminal owner) owner : ℝ) := by
    rw [← hcoordinate']
    exact hpayoff
  exact_mod_cast hreal

/-- Actual-profile designated weak exclusion supplies the executable rational
finite-word owner scan. -/
theorem rationalQuittingFiniteWordOwnerExclusionOn_of_actual
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hexclusion : HasQuittingActualWeakSubsetExclusion
      (rationalQuittingRewardToReal reward) owners) :
    RationalQuittingFiniteWordOwnerExclusionOn reward owners :=
  rationalQuittingFiniteWordOwnerExclusionOn_of_real reward owners
    (finiteWordWeakSubsetExclusion_of_actual
      (rationalQuittingRewardToReal reward) owners hexclusion)

/-- Real strict singleton-column preemption of every designated owner is
exactly inherited by the rational table. -/
theorem rationalQuittingOwnersStrictPreempted_of_real
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hpreempted : ∀ owner ∈ owners, ∃ blocker, 0 <
      rationalQuittingRewardToReal reward
          (quittingSingletonTerminal blocker) blocker -
        rationalQuittingRewardToReal reward
          (quittingSingletonTerminal owner) blocker) :
    RationalQuittingOwnersStrictPreempted reward owners := by
  intro owner howner
  obtain ⟨blocker, hgap⟩ := hpreempted owner howner
  refine ⟨blocker, ?_⟩
  change (0 : ℝ) <
    (reward (quittingSingletonTerminal blocker) blocker : ℝ) -
      (reward (quittingSingletonTerminal owner) blocker : ℝ) at hgap
  exact_mod_cast hgap

/-- The executable rational first-hit word retains its literal quantitative
bounds and is, for that same word, approximate Nash against every behavioral
terminal deviation in the actual real quitting game. -/
theorem executableRationalSelectedOwnerFirstWord_actualDebt_nash_and_length_le
    (reward : RationalQuittingReward players)
    (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hpreempted : RationalQuittingOwnersStrictPreempted reward owners)
    (M : ℚ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (ε : ℚ) (hε : 0 < ε) :
    let initial := executableRationalSelectedOwnerDebt
      reward owners hWE hpreempted M hM hreward 0
    let scale := (128 * M + 24 * initial) / 3
    let phase := executableRationalSelectedOwnerFirstPhase
      reward owners hWE hpreempted M hM hreward ε hε
    let roots := executableRationalSelectedOwnerWords
      reward owners hWE hpreempted M hM hreward phase
    let profile := quittingLiteralRootStackProfile
      (rationalQuittingRewardToReal reward)
      (roots.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair
          (rationalQuittingRewardToReal reward) profile) ≤ (ε : ℝ) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
        (ε : ℝ) profile ∧
      phase ≤ Nat.ceil (scale / ε) ∧
      roots.length ≤ phase * executableRationalSelectedOwnerUniformPhaseRowBound
        (M : ℝ) (initial : ℝ) (ε : ℝ)
          (rationalQuittingSelectedOwnerPreemptionFloor
            reward owners hWE : ℝ) := by
  dsimp only
  let phase := executableRationalSelectedOwnerFirstPhase
    reward owners hWE hpreempted M hM hreward ε hε
  let roots := executableRationalSelectedOwnerWords
    reward owners hWE hpreempted M hM hreward phase
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  obtain ⟨hdebt, hphase, hlength⟩ :=
    executableRationalSelectedOwnerFirstWord_debt_and_length_le
      reward owners hWE hpreempted M hM hreward ε hε
  have hactualDebt : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair
        (rationalQuittingRewardToReal reward) profile) ≤ (ε : ℝ) := by
    change quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile
            (rationalQuittingRewardToReal reward)))) ≤ (ε : ℝ)
    rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast]
    exact_mod_cast hdebt
  exact ⟨hactualDebt,
    isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
      (rationalQuittingRewardToReal reward) profile hactualDebt,
    hphase, hlength⟩

end GameTheory
