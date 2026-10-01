import UniformEquilibrium.Quitting.Paths.RationalPositiveSingletonColumnExit

/-! # Table-only positive-column exit

The positive rational reward bound is computed from the full finite raw table.
All real Nash, cap and payoff facts are consequences of this same rational
word and source column. No bound, selected root or successful search is input.
-/

namespace GameTheory

variable {players : ℕ}

/-- A positive rational bound computed from every actual reward coordinate. -/
def rationalQuittingTableAbsBound (reward : RationalQuittingReward players) : ℚ :=
  1 + ∑ terminal, ∑ who, |reward terminal who|

theorem rationalQuittingTableAbsBound_pos (reward : RationalQuittingReward players) :
    0 < rationalQuittingTableAbsBound reward := by
  have hsum : 0 ≤ ∑ terminal, ∑ who, |reward terminal who| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold rationalQuittingTableAbsBound
  linarith

theorem abs_reward_le_rationalQuittingTableAbsBound
    (reward : RationalQuittingReward players)
    (terminal : {S : Finset (Fin players) // S.Nonempty}) (who : Fin players) :
    |reward terminal who| ≤ rationalQuittingTableAbsBound reward := by
  have hplayer : |reward terminal who| ≤ ∑ player, |reward terminal player| :=
    Finset.single_le_sum (f := fun player => |reward terminal player|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ who)
  have hterminal : (∑ player, |reward terminal player|) ≤
      ∑ coalition, ∑ player, |reward coalition player| :=
    Finset.single_le_sum (f := fun coalition => ∑ player, |reward coalition player|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ terminal)
  unfold rationalQuittingTableAbsBound
  linarith

/-- Fully computed source-to-word exit. The source column is an erased proof
of the finite rational inequalities, not an extra selected strategic object. -/
def rationalPositiveSingletonColumnExitWord
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    List (RationalQuittingRoot players) :=
  rationalPositiveSingletonColumnWord reward owner
    (rationalQuittingTableAbsBound reward) (rationalQuittingTableAbsBound_pos reward)
    hcolumn accuracy haccuracy

theorem rationalPositiveSingletonColumnExitWord_length_le_log
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let M := rationalQuittingTableAbsBound reward
    ((rationalPositiveSingletonColumnExitWord
        reward owner hcolumn accuracy haccuracy).length : ℝ) ≤
      1 + Real.log (1 / (rationalSoloExitTolerance players M accuracy : ℝ)) /
        (-Real.log (1 - (rationalPositiveSingletonColumnHazard reward owner M : ℝ))) :=
  rationalPositiveSingletonColumnWord_length_le_log
    reward owner _ (rationalQuittingTableAbsBound_pos reward) hcolumn accuracy haccuracy

noncomputable section

/-- Actual exact stationary Nash at the table-computed rate. Only the
selected owner's own singleton is required to be nonnegative. -/
theorem rationalPositiveSingletonColumnExit_stationary_exact
    (reward : RationalQuittingReward players) (owner : Fin players)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner) :
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) 0
      (quittingStationaryProfile (rationalQuittingRewardToReal reward)
        (rationalQuittingSoloRoot owner
          (rationalPositiveSingletonColumnHazard reward owner
            (rationalQuittingTableAbsBound reward))).toPMF) :=
  rationalPositiveSingletonColumn_stationary_exact reward owner
    (rationalQuittingTableAbsBound_pos reward)
    (abs_reward_le_rationalQuittingTableAbsBound reward) howner hcolumn

/-- The actual finite exit keeps both its complete-deviation debt and its
delivery to the literal owner-singleton target below the requested accuracy. -/
theorem rationalPositiveSingletonColumnExitWord_debt_and_delivery
    (reward : RationalQuittingReward players) (owner : Fin players)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalPositiveSingletonColumnExitWord
      reward owner hcolumn accuracy haccuracy
    let profile := quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
      (word.map RationalQuittingRoot.toPMF)
      (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) profile) ≤
        (accuracy : ℝ) / 2 ∧
    ∀ who, |quittingTerminalPayoff (rationalQuittingRewardToReal reward) profile who -
      (reward (quittingSingletonTerminal owner) who : ℝ)| ≤ (accuracy : ℝ) / 2 := by
  constructor
  · exact rationalPositiveSingletonColumnProfile_debtSum_le reward owner _
      (rationalQuittingTableAbsBound_pos reward)
      (abs_reward_le_rationalQuittingTableAbsBound reward) howner hcolumn accuracy haccuracy
  · intro who
    exact rationalPositiveSingletonColumnProfile_delivery_le reward owner _
      (rationalQuittingTableAbsBound_pos reward)
      (abs_reward_le_rationalQuittingTableAbsBound reward) hcolumn accuracy haccuracy who

/-- The SAME table-computed finite exit has actual independent rational
date/Never laws and the exact full semantic pair, not just a finite menu cap. -/
theorem rationalPositiveSingletonColumnExitWord_finiteLaws
    (reward : RationalQuittingReward players) (owner : Fin players)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hcolumn : RationalQuittingStrictSingletonColumn reward owner)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let word := rationalPositiveSingletonColumnExitWord
      reward owner hcolumn accuracy haccuracy
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (word.map RationalQuittingRoot.toPMF)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) ∧
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
            word.length mixed)) ≤ (accuracy : ℝ) / 2 :=
  rationalPositiveSingletonColumnWord_finiteLaws reward owner _
    (rationalQuittingTableAbsBound_pos reward)
    (abs_reward_le_rationalQuittingTableAbsBound reward) howner hcolumn accuracy haccuracy

end

end GameTheory
