import UniformEquilibrium.Quitting.Root.RationalFiniteSourceCapThresholdScan
import UniformEquilibrium.Quitting.Root.RationalQuittingRootGridSelector
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Root.ProductRootProbabilityBridge
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDefectBudget

/-! # Executable rational auxiliary-root quadratic debt drop -/

namespace GameTheory

open Math.PMFProduct

variable {players : ℕ}

/-- Rational accuracy assigned to the executable auxiliary Boolean-root search. -/
def rationalAuxiliaryRootAccuracy (M C : ℚ) : ℚ :=
  min ((3 * C ^ 2 / (32 * M + 6 * C)) / 4) (3 * C / 32)

theorem rationalAuxiliaryRootAccuracy_pos {M C : ℚ}
    (hM : 0 < M) (hC : 0 < C) :
    0 < rationalAuxiliaryRootAccuracy M C := by
  unfold rationalAuxiliaryRootAccuracy
  apply lt_min <;> positivity

/-- The literal rational grid root selected for the cap-threshold auxiliary
continuation `B-C/2`. -/
def rationalAuxiliaryRootGridSelector
    (reward : RationalQuittingReward players)
    (pair : RationalQuittingSemanticPair players) (M C : ℚ)
    (hM : 0 < M) (hC : 0 < C) : RationalQuittingRoot players :=
  rationalQuittingRootGridSelector reward
    (pair.2 - fun _ => C / 2) (rationalAuxiliaryRootAccuracy M C)
    (rationalQuittingRootGridSearch_isSome_of_pos reward
      (pair.2 - fun _ => C / 2) (rationalAuxiliaryRootAccuracy M C)
      (rationalAuxiliaryRootAccuracy_pos hM hC))

/-- The executable rational auxiliary row spends one quarter of the exact
quadratic debt drop. -/
theorem rationalAuxiliaryRootGridSelector_debtSum_le_quarterQuadraticDrop
    (reward : RationalQuittingReward players)
    (pair : RationalQuittingSemanticPair players) (crossing : Fin players)
    {M C : ℚ} (hM : 0 < M) (hC : 0 < C)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtUpper : rationalQuittingSemanticDebtSum pair ≤ C)
    (hcrossing : pair.2 crossing -
      reward (quittingSingletonTerminal crossing) crossing ≤ C / 8) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
          (rationalAuxiliaryRootGridSelector reward pair M C hM hC).toPMF
          pair.toReal) ≤
      ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ) := by
  let root := rationalAuxiliaryRootGridSelector reward pair M C hM hC
  let drop : ℚ := 3 * C ^ 2 / (32 * M + 6 * C)
  let tolerance := rationalAuxiliaryRootAccuracy M C
  have hrewardReal : ∀ terminal player,
      |rationalQuittingRewardToReal reward terminal player| ≤ (M : ℝ) := by
    intro terminal player
    unfold rationalQuittingRewardToReal
    exact_mod_cast hreward terminal player
  have hdefectTolerance : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) root.toPMF ≤
        (tolerance : ℝ) := by
    dsimp only [root, tolerance, rationalAuxiliaryRootGridSelector]
    exact rationalQuittingRootGridSelector_totalNashDefect_le reward
      (pair.2 - fun _ => C / 2) (rationalAuxiliaryRootAccuracy M C) _
  have hdefectDrop : quittingRootTotalNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) root.toPMF ≤
        (drop / 4 : ℚ) := by
    exact hdefectTolerance.trans (by
      exact_mod_cast min_le_left (drop / 4) (3 * C / 32))
  have hcoordinateLeTotal : quittingRootCoordinateNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) root.toPMF crossing ≤
        quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
          (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) root.toPMF := by
    unfold quittingRootTotalNashDefect
    exact Finset.single_le_sum
      (fun player _ => quittingRootCoordinateNashDefect_nonneg
        (rationalQuittingRewardToReal reward)
        (fun candidate => ((pair.2 candidate - C / 2 : ℚ) : ℝ))
        root.toPMF player) (Finset.mem_univ crossing)
  have hcoordinate : quittingRootCoordinateNashDefect
      (rationalQuittingRewardToReal reward)
      (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) root.toPMF crossing ≤
        ((3 * C / 32 : ℚ) : ℝ) := by
    exact hcoordinateLeTotal.trans (hdefectTolerance.trans (by
      exact_mod_cast min_le_right (drop / 4) (3 * C / 32)))
  have hgap : (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) crossing ≤
      rationalQuittingRewardToReal reward
          (quittingSingletonTerminal crossing) crossing -
        ((3 * C / 8 : ℚ) : ℝ) := by
    have hgapRat : pair.2 crossing - C / 2 ≤
        reward (quittingSingletonTerminal crossing) crossing - 3 * C / 8 := by
      linarith
    unfold rationalQuittingRewardToReal
    have hgapReal : ((pair.2 crossing - C / 2 : ℚ) : ℝ) ≤
        ((reward (quittingSingletonTerminal crossing) crossing - 3 * C / 8 : ℚ) : ℝ) := by
      exact_mod_cast hgapRat
    simpa only [Rat.cast_sub] using hgapReal
  have habsorptionRaw := belowSingleton_approximateRoot_absorptionMass_lowerBound
    (rationalQuittingRewardToReal reward)
    (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) root.toPMF crossing
      (show (0 : ℝ) < ((3 * C / 8 : ℚ) : ℝ) by exact_mod_cast (by positivity :
        (0 : ℚ) < 3 * C / 8)) hrewardReal hgap (by
        simpa only [show ((3 * C / 8 : ℚ) : ℝ) / 4 =
          ((3 * C / 32 : ℚ) : ℝ) by push_cast; ring] using hcoordinate)
  have habsorption : ((3 * C / (32 * M + 6 * C) : ℚ) : ℝ) ≤
      quittingRootAbsorptionMass root.toPMF := by
    convert habsorptionRaw using 1
    push_cast
    field_simp
    ring
  have hpairTail :
      (fun player => ((pair.2 player - C / 2 : ℚ) : ℝ)) =
        pair.toReal.2 - fun _ => (C : ℝ) / 2 := by
    funext player
    simp [RationalQuittingSemanticPair.toReal]
  rw [hpairTail] at hdefectDrop
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := rationalQuittingRewardToReal reward) pair.toReal ((C : ℝ) / 2)
      root.toPMF (by positivity)
  have hdebtUpperReal : quittingTerminalSemanticDebtSum pair.toReal ≤ (C : ℝ) := by
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    exact_mod_cast hdebtUpper
  have habsorptionLe : quittingRootAbsorptionMass root.toPMF ≤ 1 :=
    quittingRootAbsorptionMass_le_one root.toPMF
  have hfirst :
      quittingTerminalSemanticDebtSum pair.toReal -
          quittingRootAbsorptionMass root.toPMF *
            (quittingTerminalSemanticDebtSum pair.toReal - (C : ℝ) / 2) ≤
        (C : ℝ) - quittingRootAbsorptionMass root.toPMF *
          ((C : ℝ) - (C : ℝ) / 2) := by
    nlinarith
  have hsecond :
      (C : ℝ) - quittingRootAbsorptionMass root.toPMF *
          ((C : ℝ) - (C : ℝ) / 2) ≤
        (C : ℝ) - ((3 * C / (32 * M + 6 * C) : ℚ) : ℝ) *
          ((C : ℝ) - (C : ℝ) / 2) := by
    have hhalfNonnegative : 0 ≤ (C : ℝ) - (C : ℝ) / 2 := by
      exact_mod_cast (by linarith [hC] : (0 : ℚ) ≤ C - C / 2)
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_right habsorption hhalfNonnegative) (C : ℝ)
  dsimp only [root] at hbudget ⊢
  calc
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
          (rationalAuxiliaryRootGridSelector reward pair M C hM hC).toPMF
          pair.toReal) ≤
      quittingTerminalSemanticDebtSum pair.toReal -
          quittingRootAbsorptionMass
            (rationalAuxiliaryRootGridSelector reward pair M C hM hC).toPMF *
            (quittingTerminalSemanticDebtSum pair.toReal - (C : ℝ) / 2) +
        quittingRootTotalNashDefect (rationalQuittingRewardToReal reward)
          (pair.toReal.2 - fun _ => (C : ℝ) / 2)
          (rationalAuxiliaryRootGridSelector reward pair M C hM hC).toPMF := hbudget
    _ ≤ (C : ℝ) -
        ((3 * C / (32 * M + 6 * C) : ℚ) : ℝ) *
          ((C : ℝ) - (C : ℝ) / 2) + ((drop / 4 : ℚ) : ℝ) := by
      linarith
    _ = ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ) := by
      dsimp only [drop]
      push_cast
      field_simp
      ring

end GameTheory
