import MathUE.DyadicChargedCalendarBound
import UniformEquilibrium.Quitting.Paths.ExecutableRationalWeakSubsetStage
import UniformEquilibrium.Quitting.Paths.RationalPositiveSingletonColumnSource
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Executable rational weak-subset dyadic selection

Literal finite source words are renewed at rational dyadic working levels.
The first M-stage runs even at equal initial debt. A fresh positive-column
EXIT retains ORIGINAL accuracy and stays absorbing at every subsequent level.
The output has an absolute date bound and its SAME independent finite laws.
Only existence of a fixed uniform target is asserted; no target is computed.
-/

namespace GameTheory

variable {players : ℕ}

private theorem rationalNeverDebt_le_table_bound
    (reward : RationalQuittingReward players) {M : ℚ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    rationalFiniteSourceDebt reward [] ≤ players * M := by
  simp only [rationalFiniteSourceDebt, rationalQuittingSemanticDebtSum,
    rationalQuittingFiniteWordSemanticPair, rationalQuittingFiniteWordPayoff,
    rationalQuittingFiniteWordCap, List.foldr_nil, Pi.zero_apply, sub_zero]
  calc
    _ ≤ ∑ _who : Fin players, M := by
      apply Finset.sum_le_sum
      intro who _
      have hM := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
      exact max_le hM (le_of_abs_le (hreward (quittingSingletonTerminal who) who))
    _ = players * M := by simp

private theorem rationalStageRows_eq_scalar (M working debt : ℚ) :
    rationalWeakSubsetMacrostepDateBound M working *
        (Nat.ceil (debt / rationalWeakSubsetDebtDrop M working) + 1) =
      Math.chargedCalendarRows M working debt := rfl

section Source

variable (reward : RationalQuittingReward players) (owners : Finset (Fin players))
  (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
  (M accuracy : ℚ) (haccuracy : 0 < accuracy) (haccuracyM : accuracy ≤ M)
  (hreward : ∀ terminal who, |reward terminal who| ≤ M)

local notation "hM" => lt_of_lt_of_le haccuracy haccuracyM
local notation "level" => Math.rationalDyadicLevel M
local notation "debt" => rationalFiniteSourceDebt reward
local notation "budget" => Math.dyadicChargedCalendarBudget M players

/-- One computed stage at the literal rational level M/2^index. -/
def executableRationalWeakSubsetDyadicStage
    (index : ℕ) (old : List (RationalQuittingRoot players)) : RationalWeakSubsetOutcome players :=
  executableRationalWeakSubsetStage reward owners hWE M (level index) accuracy
    (Math.rationalDyadicLevel_pos hM index) (Math.rationalDyadicLevel_le (hM).le index)
    haccuracy hreward old

local notation "stageAt" => executableRationalWeakSubsetDyadicStage reward owners hWE
  M accuracy haccuracy haccuracyM hreward

/-- No real comparison enters runtime: each level and each source are rational. -/
def executableRationalWeakSubsetDyadicOrbit : ℕ → RationalWeakSubsetOutcome players
  | 0 => .«continue» []
  | stages + 1 =>
      match executableRationalWeakSubsetDyadicOrbit stages with
      | .globalExit owner word => .globalExit owner word
      | .phaseDone word => stageAt stages word
      | .«continue» word => stageAt stages word

local notation "orbit" => executableRationalWeakSubsetDyadicOrbit reward owners hWE
  M accuracy haccuracy haccuracyM hreward

/-- Final zero-allowed working index, retaining the epsilon=M boundary. -/
def executableRationalWeakSubsetDyadicSelection : RationalWeakSubsetOutcome players :=
  orbit (Math.rationalDyadicAccuracyIndex M accuracy hM haccuracy + 1)

local notation "selected" => executableRationalWeakSubsetDyadicSelection reward owners hWE
  M accuracy haccuracy haccuracyM hreward
local notation "exitSpec" => fun index =>
  RationalWeakSubsetGlobalExitSpec reward owners M (level index) accuracy
    (Math.rationalDyadicLevel_pos hM index) (Math.rationalDyadicLevel_le (le_of_lt hM) index)
    haccuracy

noncomputable def RationalWeakSubsetDyadicInvariant
    (stages : ℕ) (outcome : RationalWeakSubsetOutcome players) : Prop :=
  match outcome with
  | .«continue» word => stages = 0 ∧ word = []
  | .phaseDone word => 0 < stages ∧ debt word < level (stages - 1) ∧
      word.length ≤ budget stages
  | .globalExit owner word => ∃ index < stages, exitSpec index owner word

local notation "invariant" => RationalWeakSubsetDyadicInvariant reward owners
  M accuracy haccuracy haccuracyM

theorem executableRationalWeakSubsetDyadicOrbit_invariant
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (stages : ℕ) : invariant stages (orbit stages) := by
  induction stages with
  | zero => exact ⟨rfl, rfl⟩
  | succ stages ih =>
      rw [executableRationalWeakSubsetDyadicOrbit]
      generalize hprevious : orbit stages = previous at ih ⊢
      cases previous with
      | globalExit owner word =>
          obtain ⟨index, hindex, hexit⟩ := ih
          exact ⟨index, hindex.trans (Nat.lt_succ_self stages), hexit⟩
      | «continue» old =>
          obtain ⟨hzero, rfl⟩ := ih
          subst stages
          have hstage := executableRationalWeakSubsetStage_spec reward owners hWE
            M (level 0) accuracy (Math.rationalDyadicLevel_pos hM 0)
            (Math.rationalDyadicLevel_le (hM).le 0) haccuracy hreward hsign []
          change (match stageAt 0 [] with
            | .phaseDone word => _
            | .globalExit owner word => _
            | .«continue» _ => False) at hstage
          change invariant (0 + 1) (stageAt 0 [])
          generalize hnext : stageAt 0 [] = next at hstage ⊢
          cases next with
          | «continue» word => exact False.elim hstage
          | globalExit owner word => exact ⟨0, Nat.zero_lt_one, hstage⟩
          | phaseDone word =>
              obtain ⟨added, hword, hlength, hdebt, _⟩ := hstage
              refine ⟨Nat.zero_lt_one, hdebt, ?_⟩
              rw [hword, List.append_nil]
              rw [rationalStageRows_eq_scalar] at hlength
              have hcost := Math.chargedCalendarRows_mono_debt M M hM le_rfl
                (rationalNeverDebt_le_table_bound reward hreward)
              exact hlength.trans (by simpa only
                [Math.rationalDyadicLevel_zero, Nat.zero_add,
                  Math.dyadicChargedCalendarBudget_one] using hcost)
      | phaseDone old =>
          obtain ⟨hstages, hdebt, hlength⟩ := ih
          have htwice : level (stages - 1) = 2 * level stages := by
            have h := Math.rationalDyadicLevel_succ M (stages - 1)
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hstages)] at h
            linarith
          have hupper : debt old ≤ 2 * level stages := by rw [htwice] at hdebt; linarith
          have hstage := executableRationalWeakSubsetStage_spec reward owners hWE
            M (level stages) accuracy (Math.rationalDyadicLevel_pos hM stages)
            (Math.rationalDyadicLevel_le (hM).le stages) haccuracy hreward hsign old
          change (match stageAt stages old with
            | .phaseDone word => _
            | .globalExit owner word => _
            | .«continue» _ => False) at hstage
          change invariant (stages + 1) (stageAt stages old)
          generalize hnext : stageAt stages old = next at hstage ⊢
          cases next with
          | «continue» word => exact False.elim hstage
          | globalExit owner word => exact ⟨stages, Nat.lt_succ_self stages, hstage⟩
          | phaseDone word =>
              obtain ⟨added, hword, hprefix, hsmall, _⟩ := hstage
              refine ⟨Nat.succ_pos stages, ?_, ?_⟩
              · simpa only [Nat.add_sub_cancel] using hsmall
              · rw [hword, List.length_append]
                rw [rationalStageRows_eq_scalar] at hprefix
                have hcost := Math.chargedCalendarRows_mono_debt M (level stages)
                  (Math.rationalDyadicLevel_pos hM stages)
                  (Math.rationalDyadicLevel_le (hM).le stages) hupper
                have hprefixBound := hprefix.trans hcost
                rw [Math.dyadicChargedCalendarBudget_succ M players stages hstages]
                omega

theorem executableRationalWeakSubsetDyadicSelection_debt_le
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    debt (selected).word ≤ accuracy := by
  let last := Math.rationalDyadicAccuracyIndex M accuracy hM haccuracy
  have hlevels := Math.rationalDyadicAccuracyIndex_spec hM haccuracy haccuracyM
  have hstate := executableRationalWeakSubsetDyadicOrbit_invariant reward owners hWE
    M accuracy haccuracy haccuracyM hreward hsign (last + 1)
  change invariant (last + 1) selected at hstate
  generalize hout : selected = outcome at hstate ⊢
  cases outcome with
  | «continue» word => exact False.elim (Nat.succ_ne_zero last hstate.1)
  | phaseDone word =>
      have hdebt : debt word < level last := by
        simpa only [Nat.add_sub_cancel] using hstate.2.1
      exact hdebt.le.trans hlevels.2
  | globalExit owner word =>
      obtain ⟨index, _, hexit⟩ := hstate
      exact hexit.2.2.2.1.trans (by linarith)

include haccuracy haccuracyM in
private theorem rationalSoloExitTolerance_eq_ratio
    (hplayers : 0 < players) :
    rationalSoloExitTolerance players M accuracy = accuracy / (2 * players * M) := by
  unfold rationalSoloExitTolerance
  apply min_eq_right
  have hn : (1 : ℚ) ≤ players := by exact_mod_cast Nat.succ_le_of_lt hplayers
  have hMq : 0 < M := hM
  apply (div_le_one (show 0 < (2 : ℚ) * players * M by positivity)).mpr
  nlinarith

theorem executableRationalWeakSubsetDyadicSelection_length_le_absolute
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    ((selected).word.length : ℝ) ≤
      1000000 * ((players : ℝ) + ((M : ℝ) / (accuracy : ℝ)) ^ 2 *
        Real.log (16 * players * (M : ℝ) / (accuracy : ℝ))) := by
  let last := Math.rationalDyadicAccuracyIndex M accuracy hM haccuracy
  have hplayers := rationalWeakSubset_players_pos reward owners hWE
  have hlevels := Math.rationalDyadicAccuracyIndex_spec hM haccuracy haccuracyM
  have hstate := executableRationalWeakSubsetDyadicOrbit_invariant reward owners hWE
    M accuracy haccuracy haccuracyM hreward hsign (last + 1)
  change invariant (last + 1) selected at hstate
  generalize hout : selected = outcome at hstate ⊢
  cases outcome with
  | «continue» word => exact False.elim (Nat.succ_ne_zero last hstate.1)
  | phaseDone word =>
      have hlength : (word.length : ℝ) ≤ (budget (last + 1) : ℝ) := by
        exact_mod_cast hstate.2.2
      exact hlength.trans
        (Math.dyadicChargedCalendarBudget_le_absolute haccuracy haccuracyM hplayers hlevels.1)
  | globalExit owner word =>
      obtain ⟨index, hindex, hexit⟩ := hstate
      have hindexLe : index ≤ last := Nat.le_of_lt_succ hindex
      have hworkingM := Math.rationalDyadicLevel_le (hM).le index
      have hlevel := hlevels.1.trans_le (Math.rationalDyadicLevel_antitone (hM).le hindexLe)
      have hcut := hexit.2.2.2.2.2
      rw [rationalSoloExitTolerance_eq_ratio M accuracy haccuracy haccuracyM hplayers] at hcut
      have htolerance : (1 : ℝ) /
          ((accuracy / (2 * players * M) : ℚ) : ℝ) =
          2 * players * (M : ℝ) / (accuracy : ℝ) := by
        push_cast
        field_simp [show (accuracy : ℝ) ≠ 0 by exact_mod_cast haccuracy.ne']
      rw [htolerance] at hcut
      have hMr : (0 : ℝ) < M := by exact_mod_cast hM
      have hfloor : (accuracy : ℝ) / (32 * (M : ℝ)) ≤
          (rationalPositiveColumnWorkingHazard M (level index) : ℝ) := by
        have hlevelR : (accuracy : ℝ) / 2 < (level index : ℝ) := by exact_mod_cast hlevel
        simp only [rationalPositiveColumnWorkingHazard, Rat.cast_div, Rat.cast_mul,
          Rat.cast_ofNat]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      have hscalar := Math.soloLogCutoff_le_absolute
        (show (0 : ℝ) < accuracy by exact_mod_cast haccuracy)
        (show (accuracy : ℝ) ≤ M by exact_mod_cast haccuracyM) hplayers
        (show (rationalPositiveColumnWorkingHazard M (level index) : ℝ) < 1 by
          exact_mod_cast rationalPositiveColumnWorkingHazard_lt_one hM hworkingM) hfloor
      apply (hcut.trans hscalar).trans
      have hlog : 0 ≤ Real.log (16 * players * (M : ℝ) / (accuracy : ℝ)) := by
        apply Real.log_nonneg
        have hn : (1 : ℝ) ≤ players := by exact_mod_cast Nat.succ_le_of_lt hplayers
        have har : (0 : ℝ) < accuracy := by exact_mod_cast haccuracy
        apply (le_div_iff₀ har).mpr
        have haccuracyMr : (accuracy : ℝ) ≤ M := by exact_mod_cast haccuracyM
        nlinarith
      have hterm : 0 ≤ ((M : ℝ) / (accuracy : ℝ)) ^ 2 *
          Real.log (16 * players * (M : ℝ) / (accuracy : ℝ)) := by positivity
      nlinarith [show (0 : ℝ) ≤ players from Nat.cast_nonneg players]

noncomputable section

/-- Full terminal debt and Nash for the SAME literal computed rational word. -/
theorem executableRationalWeakSubsetDyadicSelection_actualDebt_and_nash
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    let word := (selected).word
    let profile := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
      (word.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) profile) ≤
        (accuracy : ℝ) ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ) profile := by
  dsimp only
  have hdebt := executableRationalWeakSubsetDyadicSelection_debt_le reward owners hWE
    M accuracy haccuracy haccuracyM hreward hsign
  have hactual : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          ((selected).word.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))) ≤
      (accuracy : ℝ) := by
    rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast]
    exact_mod_cast hdebt
  exact ⟨hactual, isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le _ _ hactual⟩

/-- Exact independent finite laws, including the empty output, retain the
whole prescribed-payoff/unrestricted-cap pair of the computed word. -/
theorem executableRationalWeakSubsetDyadicSelection_finiteLaws
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    let word := (selected).word
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
        (rationalQuittingFiniteWordSemanticPair reward word).toReal ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) := by
  dsimp only
  let word := (selected).word
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  refine ⟨mixed, hmass, hpair, ?_⟩
  apply isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
  rw [hpair]
  change quittingTerminalSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward word).toReal ≤ (accuracy : ℝ)
  rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
  exact_mod_cast executableRationalWeakSubsetDyadicSelection_debt_le reward owners hWE
    M accuracy haccuracy haccuracyM hreward hsign

end
end Source

noncomputable section

/-- Rational-word exclusion ALONE, with designated-owner singleton signs,
selects one fixed uniform payoff through the canonical terminal all-errors
consumer. The target is not an executable output of the finite-word selector. -/
theorem exists_uniformEquilibriumPayoff_of_rationalFiniteWordOwnerExclusionOn
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    ∃ payoff : Payoff (Fin players),
      (quittingGame (rationalQuittingRewardToReal reward)).IsUniformEquilibriumPayoff
        none payoff := by
  let M := rationalQuittingTableAbsBound reward
  have hM := rationalQuittingTableAbsBound_pos reward
  have hreward := abs_reward_le_rationalQuittingTableAbsBound reward
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro error herror
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨accuracy, haccuracy0, haccuracyBound⟩ :=
    exists_rat_btwn (lt_min hMr herror)
  have haccuracy : (0 : ℚ) < accuracy := by exact_mod_cast haccuracy0
  have haccuracyM : accuracy ≤ M := by
    have h := haccuracyBound.le.trans (min_le_left _ _)
    exact_mod_cast h
  let word := (executableRationalWeakSubsetDyadicSelection reward owners hWE
    M accuracy haccuracy haccuracyM hreward).word
  let profile := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    (word.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hnash := (executableRationalWeakSubsetDyadicSelection_actualDebt_and_nash
    reward owners hWE M accuracy haccuracy haccuracyM hreward hsign).2
  refine ⟨profile, ?_⟩
  exact hnash.mono (haccuracyBound.le.trans (min_le_right _ _))

end
end GameTheory
