import UniformEquilibrium.Quitting.Paths.ExecutableRationalCapThresholdBlock
import UniformEquilibrium.Quitting.Terminal.PayoffExclusionStrictDeficitStep

/-! # Executable rational strict-deficit renewal step

The strict payoff deficit selects a player from the current literal rational
word.  A rational grid root for the associated auxiliary continuation spends
the packet's prescribed aggregate regret budget and yields the corresponding
quarter-strength debt contraction against unrestricted behavioral responses.
-/

namespace GameTheory

variable {players : ℕ}

/-- Every rational finite word has a coordinate below its singleton reward by
the same fixed positive margin. -/
def RationalQuittingFiniteWordStrictSingletonDeficit
    (reward : RationalQuittingReward players) (gap : ℚ) : Prop :=
  ∀ roots : List (RationalQuittingRoot players), ∃ who,
    (rationalQuittingFiniteWordSemanticPair reward roots).1 who ≤
      reward (quittingSingletonTerminal who) who - gap

/-- Executable witness scan for the strict deficit at one rational word. -/
def rationalQuittingStrictDeficitPlayer
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (roots : List (RationalQuittingRoot players)) : Fin players :=
  Fin.find (fun who =>
    (rationalQuittingFiniteWordSemanticPair reward roots).1 who ≤
      reward (quittingSingletonTerminal who) who - gap) (hdeficit roots)

theorem rationalQuittingStrictDeficitPlayer_spec
    (reward : RationalQuittingReward players) (gap : ℚ)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (roots : List (RationalQuittingRoot players)) :
    (rationalQuittingFiniteWordSemanticPair reward roots).1
        (rationalQuittingStrictDeficitPlayer reward gap hdeficit roots) ≤
      reward (quittingSingletonTerminal
          (rationalQuittingStrictDeficitPlayer reward gap hdeficit roots))
        (rationalQuittingStrictDeficitPlayer reward gap hdeficit roots) - gap := by
  exact Fin.find_spec (hdeficit roots)

/-- The debt amount charged by one strict-deficit auxiliary row. -/
def rationalQuittingStrictDeficitPaid
    (pair : RationalQuittingSemanticPair players) (gap : ℚ) : ℚ :=
  min (rationalQuittingSemanticDebtSum pair) (gap / 2)

/-- Rational auxiliary continuation used by the strict-deficit grid search. -/
def rationalQuittingStrictDeficitAuxiliary
    (pair : RationalQuittingSemanticPair players) (gap : ℚ) : Fin players → ℚ :=
  pair.2 - fun _ => rationalQuittingSemanticDebtSum pair -
    rationalQuittingStrictDeficitPaid pair gap

/-- Total rational root-defect budget for one strict-deficit row. -/
def rationalQuittingStrictDeficitRootAccuracy
    (M gap : ℚ) (pair : RationalQuittingSemanticPair players) : ℚ :=
  gap / (4 * M + gap) * rationalQuittingStrictDeficitPaid pair gap / 4

theorem rationalQuittingStrictDeficitRootAccuracy_pos
    (pair : RationalQuittingSemanticPair players) {M gap : ℚ}
    (hM : 0 < M) (hgap : 0 < gap)
    (hdebt : 0 < rationalQuittingSemanticDebtSum pair) :
    0 < rationalQuittingStrictDeficitRootAccuracy M gap pair := by
  unfold rationalQuittingStrictDeficitRootAccuracy
    rationalQuittingStrictDeficitPaid
  have hpaid : 0 < min (rationalQuittingSemanticDebtSum pair) (gap / 2) := by
    exact lt_min hdebt (by positivity)
  positivity

/-- Executable rational grid root for the current strict-deficit auxiliary
continuation. -/
def rationalQuittingStrictDeficitRoot
    (reward : RationalQuittingReward players)
    (pair : RationalQuittingSemanticPair players) (M gap : ℚ)
    (hM : 0 < M) (hgap : 0 < gap)
    (hdebt : 0 < rationalQuittingSemanticDebtSum pair) :
    RationalQuittingRoot players :=
  rationalQuittingRootGridSelector reward
    (rationalQuittingStrictDeficitAuxiliary pair gap)
    (rationalQuittingStrictDeficitRootAccuracy M gap pair)
    (rationalQuittingRootGridSearch_isSome_of_pos reward _ _
      (rationalQuittingStrictDeficitRootAccuracy_pos pair hM hgap hdebt))

private theorem rationalQuittingStrictDeficitRoot_totalDefect_le
    (reward : RationalQuittingReward players)
    (pair : RationalQuittingSemanticPair players) (M gap : ℚ)
    (hM : 0 < M) (hgap : 0 < gap)
    (hdebt : 0 < rationalQuittingSemanticDebtSum pair) :
    quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
        (fun player =>
          (rationalQuittingStrictDeficitAuxiliary pair gap player : ℝ))
        (rationalQuittingStrictDeficitRoot
          reward pair M gap hM hgap hdebt).toPMF ≤
      (rationalQuittingStrictDeficitRootAccuracy M gap pair : ℝ) := by
  exact rationalQuittingRootGridSelector_totalNashDefect_le reward
    (rationalQuittingStrictDeficitAuxiliary pair gap)
    (rationalQuittingStrictDeficitRootAccuracy M gap pair) _

/-- One positive-debt rational strict-deficit row preserves the literal source,
has the packet's absorption floor, and spends the packet's aggregate root-error
budget in the total unrestricted-response debt ledger. -/
theorem rationalQuittingStrictDeficitRoot_absorption_and_debt
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players))
    {M gap : ℚ} (hM : 0 < M) (hgap : 0 < gap)
    (hdeficit : RationalQuittingFiniteWordStrictSingletonDeficit reward gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebt : 0 < rationalFiniteSourceDebt reward roots) :
    let pair := rationalQuittingFiniteWordSemanticPair reward roots
    let root := rationalQuittingStrictDeficitRoot reward pair M gap hM hgap hdebt
    ((gap / (2 * (4 * M + gap)) : ℚ) : ℝ) ≤
        quittingRootAbsorptionMass root.toPMF ∧
      rationalFiniteSourceDebt reward (root :: roots) ≤
        rationalFiniteSourceDebt reward roots -
          gap / (4 * (4 * M + gap)) *
            min (rationalFiniteSourceDebt reward roots) (gap / 2) := by
  dsimp only
  let pair : RationalQuittingSemanticPair players :=
    rationalQuittingFiniteWordSemanticPair reward roots
  let D := rationalQuittingSemanticDebtSum pair
  let paid := min D (gap / 2)
  let who := rationalQuittingStrictDeficitPlayer reward gap hdeficit roots
  let root := rationalQuittingStrictDeficitRoot reward pair M gap hM hgap hdebt
  have hMReal : ∀ terminal player,
      |rationalQuittingRewardToReal reward terminal player| ≤ (M : ℝ) := by
    intro terminal player
    unfold rationalQuittingRewardToReal
    exact_mod_cast hreward terminal player
  have hpairReal : quittingTerminalSemanticPair
      (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) =
      pair.toReal := by
    simpa only [pair, RationalQuittingSemanticPair.toReal] using
      (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots)
  have hpairMem : pair.toReal ∈ quittingTerminalSemanticCarrier
      (rationalQuittingRewardToReal reward) := by
    rw [← hpairReal]
    exact subset_closure ⟨_, rfl⟩
  have hdeficitReal : pair.toReal.1 who ≤
      rationalQuittingRewardToReal reward
          (quittingSingletonTerminal who) who - (gap : ℝ) := by
    have hdeficitRat := rationalQuittingStrictDeficitPlayer_spec
      reward gap hdeficit roots
    change (pair.1 who : ℝ) ≤
      (reward (quittingSingletonTerminal who) who : ℝ) - (gap : ℝ)
    exact_mod_cast (by simpa only [pair, who] using hdeficitRat)
  have htotal := rationalQuittingStrictDeficitRoot_totalDefect_le
    reward pair M gap hM hgap hdebt
  have hcoordinateLe : quittingRootCoordinateNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player =>
        (rationalQuittingStrictDeficitAuxiliary pair gap player : ℝ))
      root.toPMF who ≤
        quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
          (fun player =>
            (rationalQuittingStrictDeficitAuxiliary pair gap player : ℝ))
          root.toPMF := by
    unfold quittingRootTotalNashDefect
    exact Finset.single_le_sum
      (fun player _ => quittingRootCoordinateNashDefect_nonneg
        (rationalQuittingRewardToReal reward)
        (fun candidate =>
          (rationalQuittingStrictDeficitAuxiliary pair gap candidate : ℝ))
        root.toPMF player) (Finset.mem_univ who)
  have hcoefficientLeOne : gap / (4 * M + gap) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  have hpaidLe : paid ≤ gap / 2 := min_le_right _ _
  have haccuracyLe : rationalQuittingStrictDeficitRootAccuracy M gap pair ≤
      gap / 8 := by
    unfold rationalQuittingStrictDeficitRootAccuracy
    dsimp only [paid, rationalQuittingStrictDeficitPaid]
    have hgapNonneg : 0 ≤ gap := hgap.le
    have hpaidNonneg : 0 ≤ paid := by
      exact le_min (by simpa only [D, pair, rationalFiniteSourceDebt] using hdebt.le)
        (by positivity)
    nlinarith [mul_le_mul hcoefficientLeOne hpaidLe
      hpaidNonneg zero_le_one]
  have hcoordinate : quittingRootCoordinateNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player =>
        (rationalQuittingStrictDeficitAuxiliary pair gap player : ℝ))
      root.toPMF who ≤ ((gap / 8 : ℚ) : ℝ) := by
    exact hcoordinateLe.trans (htotal.trans (by exact_mod_cast haccuracyLe))
  have hauxiliaryReal : (fun player =>
      (rationalQuittingStrictDeficitAuxiliary pair gap player : ℝ)) =
      pair.toReal.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair.toReal -
          min (quittingTerminalSemanticDebtSum pair.toReal) ((gap : ℝ) / 2) := by
    funext player
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    simp [rationalQuittingStrictDeficitAuxiliary,
      rationalQuittingStrictDeficitPaid, RationalQuittingSemanticPair.toReal]
  rw [hauxiliaryReal] at hcoordinate htotal
  have htotal' : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (pair.toReal.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair.toReal -
          min (quittingTerminalSemanticDebtSum pair.toReal) ((gap : ℝ) / 2))
      root.toPMF ≤
        (rationalQuittingStrictDeficitRootAccuracy M gap pair : ℝ) := by
    simpa only [root] using htotal
  have htotalBudget : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (pair.toReal.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair.toReal -
          min (quittingTerminalSemanticDebtSum pair.toReal) ((gap : ℝ) / 2))
      root.toPMF ≤
        (gap : ℝ) / (4 * (M : ℝ) + gap) *
          min (quittingTerminalSemanticDebtSum pair.toReal) ((gap : ℝ) / 2) / 4 := by
    have hbudgetEq :
        (rationalQuittingStrictDeficitRootAccuracy M gap pair : ℝ) =
          (gap : ℝ) / (4 * (M : ℝ) + gap) *
            min (quittingTerminalSemanticDebtSum pair.toReal) ((gap : ℝ) / 2) / 4 := by
      rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
      unfold rationalQuittingStrictDeficitRootAccuracy
        rationalQuittingStrictDeficitPaid
      push_cast
      rfl
    exact htotal'.trans_eq hbudgetEq
  have hstep := strictDeficit_approximateAuxiliaryPrefix_absorption_and_debt
    (rationalQuittingRewardToReal reward) pair.toReal root.toPMF who
      (show (0 : ℝ) < (gap : ℝ) by exact_mod_cast hgap) hMReal hpairMem
      hdeficitReal (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hcoordinate)
      htotalBudget
  have hnewSemantic : quittingTerminalSemanticPair
      (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        ((root :: roots).map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) =
      quittingTerminalSemanticPrefix
        (rationalQuittingRewardToReal reward) root.toPMF pair.toReal := by
    rw [List.map_cons, quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation, hpairReal]
  constructor
  · convert hstep.1 using 1
    push_cast
    ring
  · have hnewCast :=
      quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast
        reward (root :: roots)
    rw [hnewSemantic] at hnewCast
    have holdCast : quittingTerminalSemanticDebtSum pair.toReal =
        (rationalFiniteSourceDebt reward roots : ℝ) := by
      rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
      rfl
    have hrhs : quittingTerminalSemanticDebtSum pair.toReal -
          (gap : ℝ) / (4 * (4 * (M : ℝ) + gap)) *
            min (quittingTerminalSemanticDebtSum pair.toReal) ((gap : ℝ) / 2) =
        ((rationalFiniteSourceDebt reward roots -
          gap / (4 * (4 * M + gap)) *
            min (rationalFiniteSourceDebt reward roots) (gap / 2) : ℚ) : ℝ) := by
      rw [holdCast]
      push_cast
      ring
    have hreal :
        (rationalFiniteSourceDebt reward (root :: roots) : ℝ) ≤
          ((rationalFiniteSourceDebt reward roots -
            gap / (4 * (4 * M + gap)) *
              min (rationalFiniteSourceDebt reward roots) (gap / 2) : ℚ) : ℝ) := by
      calc
        _ = quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix
              (rationalQuittingRewardToReal reward) root.toPMF pair.toReal) := by
          simpa only [rationalFiniteSourceDebt] using hnewCast.symm
        _ ≤ _ := hstep.2
        _ = _ := hrhs
    exact_mod_cast hreal

end GameTheory
