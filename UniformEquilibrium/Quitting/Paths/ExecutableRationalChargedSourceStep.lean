import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan
import UniformEquilibrium.Quitting.Root.RationalQuittingRootGridSelector
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDefectBudget

/-! # A charged rational auxiliary step over an actual finite source

The source pair is computed from the literal old word, including complete
behavioral response caps. The charged-margin test is rational. Positive
accuracy internally certifies the canonical root grid search; no root,
search-success oracle, annotated cap vector or selected equilibrium is input.
-/

namespace GameTheory

variable {players : ℕ}

/-- The exact rational charged-margin test at the actual old finite word. -/
def rationalFiniteSourceChargedMargin
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (workingAccuracy : ℚ) : Prop :=
  let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let debt := rationalQuittingSemanticDebtSum pair
  ∃ who : Fin players, pair.2 who - reward (quittingSingletonTerminal who) who ≤
    debt - workingAccuracy / 8

instance rationalFiniteSourceChargedMargin_decidable
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (workingAccuracy : ℚ) :
    Decidable (rationalFiniteSourceChargedMargin reward sourceRoots workingAccuracy) := by
  unfold rationalFiniteSourceChargedMargin
  infer_instance

/-- The packet's total-defect tolerance. Its denominator is the actual
player count, not the number of positive coordinates of the selected root. -/
def rationalChargedSourceRootAccuracy (players : ℕ) (M workingAccuracy : ℚ) : ℚ :=
  let tau := workingAccuracy / 8
  let absorptionFloor := tau / (4 * M + tau)
  absorptionFloor * tau / (8 * players)

private theorem rationalChargedSource_parameters {M workingAccuracy : ℚ}
    (hplayers : 0 < players) (hM : 0 < M) (haccuracy : 0 < workingAccuracy) :
    let tau := workingAccuracy / 8
    let absorptionFloor := tau / (4 * M + tau)
    let tolerance := rationalChargedSourceRootAccuracy players M workingAccuracy
    0 < absorptionFloor ∧ absorptionFloor ≤ 1 ∧ 0 < tolerance ∧
      tolerance ≤ tau / 8 ∧ tolerance ≤ absorptionFloor * tau / 8 := by
  let tau := workingAccuracy / 8
  let absorptionFloor := tau / (4 * M + tau)
  let tolerance := rationalChargedSourceRootAccuracy players M workingAccuracy
  have htau : 0 < tau := div_pos haccuracy (by norm_num)
  have hdenominator : 0 < 4 * M + tau := by positivity
  have hfloor : 0 < absorptionFloor := div_pos htau hdenominator
  have hfloorOne : absorptionFloor ≤ 1 := by
    apply (div_le_one hdenominator).2
    linarith
  have hcardOne : (1 : ℚ) ≤ players := by
    exact_mod_cast Nat.succ_le_of_lt hplayers
  have hcard : (0 : ℚ) < players := by exact_mod_cast hplayers
  have htolerance : 0 < tolerance := by
    dsimp only [tolerance, rationalChargedSourceRootAccuracy]
    positivity
  have hfloorTau : absorptionFloor * tau ≤ tau :=
    (mul_le_mul_of_nonneg_right hfloorOne htau.le).trans_eq (one_mul _)
  have hcardTau : tau ≤ tau * players := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hcardOne htau.le
  have htoleranceTau : tolerance ≤ tau / 8 := by
    change absorptionFloor * tau / (8 * (players : ℚ)) ≤ tau / 8
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 8 * players)).2
    nlinarith
  have hcardFloorTau : absorptionFloor * tau ≤ absorptionFloor * tau * players := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hcardOne (mul_nonneg hfloor.le htau.le)
  have htoleranceDrop : tolerance ≤ absorptionFloor * tau / 8 := by
    change absorptionFloor * tau / (8 * (players : ℚ)) ≤ absorptionFloor * tau / 8
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 8 * players)).2
    nlinarith
  exact ⟨hfloor, hfloorOne, htolerance, htoleranceTau, htoleranceDrop⟩

private theorem rationalChargedSource_players_pos
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (workingAccuracy : ℚ)
    (hcharged : rationalFiniteSourceChargedMargin reward sourceRoots workingAccuracy) :
    0 < players := by
  obtain ⟨who, _⟩ := hcharged
  exact lt_of_le_of_lt (Nat.zero_le who.val) who.isLt

/-- Canonical executable root selection against the actual continuation
B minus (D minus half the charged margin). The branch witness only proves
player positivity; it makes no computational choice of an owner or root. -/
def rationalFiniteSourceChargedRoot
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (M workingAccuracy : ℚ)
    (hM : 0 < M) (haccuracy : 0 < workingAccuracy)
    (hcharged : rationalFiniteSourceChargedMargin reward sourceRoots workingAccuracy) :
    RationalQuittingRoot players :=
  let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let debt := rationalQuittingSemanticDebtSum pair
  let tau := workingAccuracy / 8
  let tail := pair.2 - fun _ => debt - tau / 2
  let tolerance := rationalChargedSourceRootAccuracy players M workingAccuracy
  let htolerance := (rationalChargedSource_parameters
    (rationalChargedSource_players_pos reward sourceRoots workingAccuracy hcharged)
    hM haccuracy).2.2.1
  rationalQuittingRootGridSelector reward tail tolerance
    (rationalQuittingRootGridSearch_isSome_of_pos reward tail tolerance htolerance)

/-- The returned word adds precisely the selected rational row before the
entire original chronological source. It never replaces that source. -/
def rationalFiniteSourceChargedWord
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (M workingAccuracy : ℚ)
    (hM : 0 < M) (haccuracy : 0 < workingAccuracy)
    (hcharged : rationalFiniteSourceChargedMargin reward sourceRoots workingAccuracy) :
    List (RationalQuittingRoot players) :=
  rationalFiniteSourceChargedRoot reward sourceRoots M workingAccuracy hM haccuracy hcharged ::
    sourceRoots

/-- The selected row has absorption at least half the packet floor and
spends at least one eighth of floor times margin in actual total debt.
The stronger positive-accuracy statement does not need accuracy at most M. -/
theorem rationalFiniteSourceChargedRoot_absorption_and_prefix_debt
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (M workingAccuracy : ℚ)
    (hM : 0 < M) (haccuracy : 0 < workingAccuracy)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebt : workingAccuracy ≤ rationalQuittingSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward sourceRoots))
    (hcharged : rationalFiniteSourceChargedMargin reward sourceRoots workingAccuracy) :
    let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
    let debt := rationalQuittingSemanticDebtSum pair
    let tau := workingAccuracy / 8
    let absorptionFloor := tau / (4 * M + tau)
    let root := rationalFiniteSourceChargedRoot
      reward sourceRoots M workingAccuracy hM haccuracy hcharged
    ((absorptionFloor / 2 : ℚ) : ℝ) ≤ quittingRootAbsorptionMass root.toPMF ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
            root.toPMF pair.toReal) ≤
        ((debt - absorptionFloor * tau / 8 : ℚ) : ℝ) := by
  let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let debt := rationalQuittingSemanticDebtSum pair
  let tau := workingAccuracy / 8
  let absorptionFloor := tau / (4 * M + tau)
  let tolerance := rationalChargedSourceRootAccuracy players M workingAccuracy
  let shift := debt - tau / 2
  let tail : Fin players → ℚ := pair.2 - fun _ => shift
  let root := rationalFiniteSourceChargedRoot
    reward sourceRoots M workingAccuracy hM haccuracy hcharged
  have hplayers := rationalChargedSource_players_pos
    reward sourceRoots workingAccuracy hcharged
  have hparameters := rationalChargedSource_parameters hplayers hM haccuracy
  have htau : 0 < tau := div_pos haccuracy (by norm_num)
  have hfloor : 0 < absorptionFloor := hparameters.1
  have htoleranceTau : tolerance ≤ tau / 8 := hparameters.2.2.2.1
  have htoleranceDrop : tolerance ≤ absorptionFloor * tau / 8 :=
    hparameters.2.2.2.2
  have htauReal : (0 : ℝ) < tau := by exact_mod_cast htau
  have hrewardReal : ∀ terminal player,
      |rationalQuittingRewardToReal reward terminal player| ≤ (M : ℝ) := by
    intro terminal player
    unfold rationalQuittingRewardToReal
    exact_mod_cast hreward terminal player
  have hdefect : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (fun who => (tail who : ℝ)) root.toPMF ≤ (tolerance : ℝ) := by
    dsimp only [root, rationalFiniteSourceChargedRoot]
    exact rationalQuittingRootGridSelector_totalNashDefect_le
      reward tail tolerance _
  obtain ⟨who, hmargin⟩ := hcharged
  have hgapRat : tail who ≤ reward (quittingSingletonTerminal who) who - tau / 2 := by
    change pair.2 who - (debt - tau / 2) ≤
      reward (quittingSingletonTerminal who) who - tau / 2
    change pair.2 who - reward (quittingSingletonTerminal who) who ≤ debt - tau
      at hmargin
    linarith
  have hgap : (fun player => (tail player : ℝ)) who ≤
      rationalQuittingRewardToReal reward (quittingSingletonTerminal who) who -
        (tau : ℝ) / 2 := by
    unfold rationalQuittingRewardToReal
    have hcast : (tail who : ℝ) ≤
        ((reward (quittingSingletonTerminal who) who - tau / 2 : ℚ) : ℝ) := by
      exact_mod_cast hgapRat
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] using hcast
  have hcoordinate : quittingRootCoordinateNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player => (tail player : ℝ)) root.toPMF who ≤ ((tau : ℝ) / 2) / 4 := by
    have hcoordinateTotal : quittingRootCoordinateNashDefect
        (rationalQuittingRewardToReal reward)
        (fun player => (tail player : ℝ)) root.toPMF who ≤
          quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
            (fun player => (tail player : ℝ)) root.toPMF := by
      unfold quittingRootTotalNashDefect
      exact Finset.single_le_sum
        (fun player _ => quittingRootCoordinateNashDefect_nonneg
          (rationalQuittingRewardToReal reward)
          (fun candidate => (tail candidate : ℝ)) root.toPMF player)
        (Finset.mem_univ who)
    have hsmall : (tolerance : ℝ) ≤ (tau : ℝ) / 8 := by
      exact_mod_cast htoleranceTau
    exact (hcoordinateTotal.trans hdefect).trans (by linarith)
  have habsorptionRaw := belowSingleton_approximateRoot_absorptionMass_lowerBound
    (rationalQuittingRewardToReal reward) (fun player => (tail player : ℝ))
    root.toPMF who (div_pos htauReal (by norm_num)) hrewardReal hgap hcoordinate
  have hratio : ((absorptionFloor / 2 : ℚ) : ℝ) =
      ((tau : ℝ) / 2) / (2 * (2 * (M : ℝ) + (tau : ℝ) / 2)) := by
    rw [show 2 * (2 * (M : ℝ) + (tau : ℝ) / 2) = 4 * (M : ℝ) + tau by ring]
    dsimp only [absorptionFloor]
    push_cast
    ring
  have habsorption : ((absorptionFloor / 2 : ℚ) : ℝ) ≤
      quittingRootAbsorptionMass root.toPMF := by
    rw [hratio]
    exact habsorptionRaw
  have hshift : 0 ≤ shift := by
    change 0 ≤ debt - tau / 2
    change workingAccuracy ≤ debt at hdebt
    dsimp only [tau]
    linarith
  have hshiftReal : (0 : ℝ) ≤ shift := by exact_mod_cast hshift
  have htail : (fun player => (tail player : ℝ)) =
      pair.toReal.2 - fun _ => (shift : ℝ) := by
    funext player
    simp only [tail, RationalQuittingSemanticPair.toReal, Pi.sub_apply, Rat.cast_sub]
  rw [htail] at hdefect
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := rationalQuittingRewardToReal reward) pair.toReal
      (shift : ℝ) root.toPMF hshiftReal
  have hdebtCast : quittingTerminalSemanticDebtSum pair.toReal = (debt : ℝ) :=
    quittingTerminalSemanticDebtSum_rational_eq_cast pair
  have hshiftGap : (debt : ℝ) - (shift : ℝ) = (tau : ℝ) / 2 := by
    dsimp only [shift]
    push_cast
    ring
  rw [hdebtCast, hshiftGap] at hbudget
  have hspent : ((absorptionFloor * tau / 4 : ℚ) : ℝ) ≤
      quittingRootAbsorptionMass root.toPMF * ((tau : ℝ) / 2) := by
    have hmul := mul_le_mul_of_nonneg_right habsorption
      (show 0 ≤ (tau : ℝ) / 2 by positivity)
    calc
      ((absorptionFloor * tau / 4 : ℚ) : ℝ) =
          ((absorptionFloor / 2 : ℚ) : ℝ) * ((tau : ℝ) / 2) := by
        push_cast
        ring
      _ ≤ _ := hmul
  have hdefectDrop : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (pair.toReal.2 - fun _ => (shift : ℝ)) root.toPMF ≤
        ((absorptionFloor * tau / 8 : ℚ) : ℝ) :=
    hdefect.trans (by exact_mod_cast htoleranceDrop)
  refine ⟨habsorption, ?_⟩
  change quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
        root.toPMF pair.toReal) ≤ ((debt - absorptionFloor * tau / 8 : ℚ) : ℝ)
  rw [Rat.cast_sub]
  have hdropQuarter : ((absorptionFloor * tau / 4 : ℚ) : ℝ) =
      2 * ((absorptionFloor * tau / 8 : ℚ) : ℝ) := by
    push_cast
    ring
  linarith

/-- The same literal returned word has its exact rationally computed pair
and full behavioral debt bound. This includes Never and every post-calendar
reply; it is not merely acceptance against a finite response menu. -/
theorem rationalFiniteSourceChargedWord_spec
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) (M workingAccuracy : ℚ)
    (hM : 0 < M) (haccuracy : 0 < workingAccuracy)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebt : workingAccuracy ≤ rationalQuittingSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward sourceRoots))
    (hcharged : rationalFiniteSourceChargedMargin reward sourceRoots workingAccuracy) :
    let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
    let debt := rationalQuittingSemanticDebtSum pair
    let tau := workingAccuracy / 8
    let absorptionFloor := tau / (4 * M + tau)
    let root := rationalFiniteSourceChargedRoot
      reward sourceRoots M workingAccuracy hM haccuracy hcharged
    let word := rationalFiniteSourceChargedWord
      reward sourceRoots M workingAccuracy hM haccuracy hcharged
    let computed := rationalQuittingFiniteWordSemanticPair reward word
    let actual := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
      (word.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    word = root :: sourceRoots ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) actual =
        computed.toReal ∧
      ((absorptionFloor / 2 : ℚ) : ℝ) ≤ quittingRootAbsorptionMass root.toPMF ∧
      rationalQuittingSemanticDebtSum computed ≤ debt - absorptionFloor * tau / 8 ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) actual) ≤
        ((debt - absorptionFloor * tau / 8 : ℚ) : ℝ) := by
  dsimp only
  let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let root := rationalFiniteSourceChargedRoot
    reward sourceRoots M workingAccuracy hM haccuracy hcharged
  let word := rationalFiniteSourceChargedWord
    reward sourceRoots M workingAccuracy hM haccuracy hcharged
  let old := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    (sourceRoots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  let actual := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
    (word.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hword : word = root :: sourceRoots := rfl
  have hold : quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) old =
      pair.toReal := by
    simpa only [old, pair, RationalQuittingSemanticPair.toReal] using
      quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward sourceRoots
  have hprefix : quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) actual =
      quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
        root.toPMF pair.toReal := by
    dsimp only [actual]
    rw [hword, List.map_cons, quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation, hold]
  obtain ⟨habsorption, hdrop⟩ :=
    rationalFiniteSourceChargedRoot_absorption_and_prefix_debt
      reward sourceRoots M workingAccuracy hM haccuracy hreward hdebt hcharged
  have hactual := hdrop
  rw [← hprefix] at hactual
  have hcomputed : quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) actual =
      (rationalQuittingFiniteWordSemanticPair reward word).toReal := by
    simpa only [actual, RationalQuittingSemanticPair.toReal] using
      quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word
  have hactualDebtCast := quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast
    reward word
  have hrational : rationalQuittingSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward word) ≤
        rationalQuittingSemanticDebtSum pair -
          ((workingAccuracy / 8) / (4 * M + workingAccuracy / 8)) *
            (workingAccuracy / 8) / 8 := by
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) actual) = _
      at hactualDebtCast
    have hreal := hactual
    rw [hactualDebtCast] at hreal
    exact_mod_cast hreal
  exact ⟨hword, hcomputed, habsorption, hrational, hactual⟩

end GameTheory
