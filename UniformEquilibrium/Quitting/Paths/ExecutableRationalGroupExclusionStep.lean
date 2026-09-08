import UniformEquilibrium.Quitting.Paths.ExecutableRationalCapThresholdBlock
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWords
import UniformEquilibrium.Quitting.Root.RationalQuittingRootGridSelector
import UniformEquilibrium.Quitting.Terminal.GroupExclusionApproximatePrefixStep

/-! # Executable rational group-exclusion renewal step

One rational grid row spends the aggregate regret budget prescribed by group
exclusion.  The possibly real-valued exclusion weights occur only in the
erased correctness proof; the selected root and all source arithmetic remain
rational and executable.
-/

namespace GameTheory

variable {players : ℕ}

/-- Rational common-shift auxiliary continuation for group exclusion. -/
def rationalQuittingGroupExclusionAuxiliary
    (pair : RationalQuittingSemanticPair players) (beta : ℚ) : Fin players → ℚ :=
  pair.2 - fun _ => rationalQuittingSemanticDebtSum pair -
    (1 - beta) * rationalQuittingSemanticDebtSum pair / 2

/-- Aggregate rational root-defect budget retaining one quarter of the exact
group-exclusion debt gain. -/
def rationalQuittingGroupExclusionRootAccuracy
    (M beta : ℚ) (pair : RationalQuittingSemanticPair players) : ℚ :=
  (1 - beta) ^ 2 * rationalQuittingSemanticDebtSum pair ^ 2 /
    (32 * M + 8 * (1 - beta) * rationalQuittingSemanticDebtSum pair)

theorem rationalQuittingGroupExclusionRootAccuracy_pos
    (pair : RationalQuittingSemanticPair players) {M beta : ℚ}
    (hM : 0 < M) (hbeta : beta < 1)
    (hdebt : 0 < rationalQuittingSemanticDebtSum pair) :
    0 < rationalQuittingGroupExclusionRootAccuracy M beta pair := by
  unfold rationalQuittingGroupExclusionRootAccuracy
  positivity

/-- Executable rational grid root for one group-exclusion auxiliary row. -/
def rationalQuittingGroupExclusionRoot
    (reward : RationalQuittingReward players)
    (pair : RationalQuittingSemanticPair players) (M beta : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hdebt : 0 < rationalQuittingSemanticDebtSum pair) :
    RationalQuittingRoot players :=
  rationalQuittingRootGridSelector reward
    (rationalQuittingGroupExclusionAuxiliary pair beta)
    (rationalQuittingGroupExclusionRootAccuracy M beta pair)
    (rationalQuittingRootGridSearch_isSome_of_pos reward _ _
      (rationalQuittingGroupExclusionRootAccuracy_pos pair hM hbeta hdebt))

/-- The selected rational grid root satisfies its aggregate actual-regret
budget after casting to the real quitting semantics. -/
theorem rationalQuittingGroupExclusionRoot_totalDefect_le
    (reward : RationalQuittingReward players)
    (pair : RationalQuittingSemanticPair players) (M beta : ℚ)
    (hM : 0 < M) (hbeta : beta < 1)
    (hdebt : 0 < rationalQuittingSemanticDebtSum pair) :
    quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
        (fun player =>
          (rationalQuittingGroupExclusionAuxiliary pair beta player : ℝ))
        (rationalQuittingGroupExclusionRoot
          reward pair M beta hM hbeta hdebt).toPMF ≤
      (rationalQuittingGroupExclusionRootAccuracy M beta pair : ℝ) := by
  exact rationalQuittingRootGridSelector_totalNashDefect_le reward
    (rationalQuittingGroupExclusionAuxiliary pair beta)
    (rationalQuittingGroupExclusionRootAccuracy M beta pair) _

/-- One positive-debt group-exclusion row preserves the literal rational
source and obtains the packet's quarter-strength reciprocal debt decrease
against unrestricted actual behavioral responses. -/
theorem rationalQuittingGroupExclusionRoot_absorption_and_debt
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players))
    {M beta : ℚ} (hM : 0 < M) (hbeta : beta < 1)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion
      (rationalQuittingRewardToReal reward) (beta : ℝ))
    (hdebt : 0 < rationalFiniteSourceDebt reward roots) :
    let pair := rationalQuittingFiniteWordSemanticPair reward roots
    let root := rationalQuittingGroupExclusionRoot
      reward pair M beta hM hbeta hdebt
    (((1 - beta) * rationalFiniteSourceDebt reward roots /
        (8 * M + 2 * (1 - beta) * rationalFiniteSourceDebt reward roots) : ℚ) :
          ℝ) ≤ quittingRootAbsorptionMass root.toPMF ∧
      rationalFiniteSourceDebt reward (root :: roots) ≤
        rationalFiniteSourceDebt reward roots -
          (1 - beta) ^ 2 * rationalFiniteSourceDebt reward roots ^ 2 /
            (32 * M + 8 * (1 - beta) *
              rationalFiniteSourceDebt reward roots) := by
  dsimp only
  let pair : RationalQuittingSemanticPair players :=
    rationalQuittingFiniteWordSemanticPair reward roots
  let root := rationalQuittingGroupExclusionRoot
    reward pair M beta hM hbeta hdebt
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (roots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  obtain ⟨weight, hweight, hweightSum, hweightMax, hexclude⟩ :=
    hexclusion (roots.map RationalQuittingRoot.toPMF)
  have hrewardReal : ∀ terminal player,
      |rationalQuittingRewardToReal reward terminal player| ≤ (M : ℝ) := by
    intro terminal player
    unfold rationalQuittingRewardToReal
    exact_mod_cast hreward terminal player
  have hpairReal : quittingTerminalSemanticPair
      (rationalQuittingRewardToReal reward) profile = pair.toReal := by
    dsimp only [profile, pair]
    simpa only [RationalQuittingSemanticPair.toReal] using
      (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots)
  have hpairMem : pair.toReal ∈ quittingTerminalSemanticCarrier
      (rationalQuittingRewardToReal reward) := by
    rw [← hpairReal]
    exact subset_closure ⟨profile, rfl⟩
  have hexcludeReal : ∑ who, weight who *
      (pair.toReal.1 who - rationalQuittingRewardToReal reward
        (quittingSingletonTerminal who) who) ≤ 0 := by
    rw [← hpairReal]
    simpa only [profile, quittingTerminalSemanticPair] using hexclude
  have htotal := rationalQuittingGroupExclusionRoot_totalDefect_le
    reward pair M beta hM hbeta hdebt
  have hauxiliaryReal : (fun player =>
      (rationalQuittingGroupExclusionAuxiliary pair beta player : ℝ)) =
      pair.toReal.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair.toReal -
          (1 - (beta : ℝ)) * quittingTerminalSemanticDebtSum pair.toReal / 2 := by
    funext player
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    simp [rationalQuittingGroupExclusionAuxiliary,
      RationalQuittingSemanticPair.toReal]
  rw [hauxiliaryReal] at htotal
  have haccuracyCast :
      (rationalQuittingGroupExclusionRootAccuracy M beta pair : ℝ) =
        (1 - (beta : ℝ)) ^ 2 *
            quittingTerminalSemanticDebtSum pair.toReal ^ 2 /
          (32 * (M : ℝ) + 8 * (1 - (beta : ℝ)) *
            quittingTerminalSemanticDebtSum pair.toReal) := by
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    unfold rationalQuittingGroupExclusionRootAccuracy
    push_cast
    rfl
  have htotalBudget : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (pair.toReal.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair.toReal -
          (1 - (beta : ℝ)) * quittingTerminalSemanticDebtSum pair.toReal / 2)
      root.toPMF ≤
        (1 - (beta : ℝ)) ^ 2 *
            quittingTerminalSemanticDebtSum pair.toReal ^ 2 /
          (32 * (M : ℝ) + 8 * (1 - (beta : ℝ)) *
            quittingTerminalSemanticDebtSum pair.toReal) :=
    htotal.trans_eq haccuracyCast
  have hstep := nonconcentratedWeight_approximateAuxiliaryPrefix_debtDrop
    (rationalQuittingRewardToReal reward) pair.toReal root.toPMF weight
      hrewardReal hpairMem
      (by rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
          exact_mod_cast hdebt)
      (by exact_mod_cast hbeta) hweight hweightSum hweightMax hexcludeReal
      htotalBudget
  have hnewSemantic : quittingTerminalSemanticPair
      (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        ((root :: roots).map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile
          (rationalQuittingRewardToReal reward))) =
      quittingTerminalSemanticPrefix
        (rationalQuittingRewardToReal reward) root.toPMF pair.toReal := by
    rw [List.map_cons, quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation, hpairReal]
  constructor
  · convert hstep.1 using 1
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    push_cast
    rfl
  · have hnewCast :=
      quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast
        reward (root :: roots)
    rw [hnewSemantic] at hnewCast
    have holdCast : quittingTerminalSemanticDebtSum pair.toReal =
        (rationalFiniteSourceDebt reward roots : ℝ) := by
      rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
      rfl
    have hrhs : quittingTerminalSemanticDebtSum pair.toReal -
          (1 - (beta : ℝ)) ^ 2 *
            quittingTerminalSemanticDebtSum pair.toReal ^ 2 /
              (32 * (M : ℝ) + 8 * (1 - (beta : ℝ)) *
                quittingTerminalSemanticDebtSum pair.toReal) =
        ((rationalFiniteSourceDebt reward roots -
          (1 - beta) ^ 2 * rationalFiniteSourceDebt reward roots ^ 2 /
            (32 * M + 8 * (1 - beta) *
              rationalFiniteSourceDebt reward roots) : ℚ) : ℝ) := by
      rw [holdCast]
      push_cast
      rfl
    have hreal :
        (rationalFiniteSourceDebt reward (root :: roots) : ℝ) ≤
          ((rationalFiniteSourceDebt reward roots -
            (1 - beta) ^ 2 * rationalFiniteSourceDebt reward roots ^ 2 /
              (32 * M + 8 * (1 - beta) *
                rationalFiniteSourceDebt reward roots) : ℚ) : ℝ) := by
      calc
        _ = quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix
              (rationalQuittingRewardToReal reward) root.toPMF pair.toReal) := by
          simpa only [rationalFiniteSourceDebt] using hnewCast.symm
        _ ≤ _ := hstep.2
        _ = _ := hrhs
    exact_mod_cast hreal

end GameTheory
