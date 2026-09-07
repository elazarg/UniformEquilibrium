import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDefectBudget
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Root.ProductRootProbabilityBridge
import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloCapThreshold

/-! # Literal finite cap-threshold blocks with quantitative debt descent -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The auxiliary exact-Nash row following a threshold crossing spends a
fixed fraction of the remaining debt above `C / 2`. -/
theorem exists_auxiliaryExactRoot_debtSum_le_quadraticDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (crossing : ι)
    {M C : ℝ} (hM : 0 < M) (hC : 0 < C)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtUpper : quittingTerminalSemanticDebtSum pair ≤ C)
    (hcrossing : pair.2 crossing -
      reward (quittingSingletonTerminal crossing) crossing ≤ C / 8) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair.2 - (fun _ : ι => C / 2)) 0 root ∧
      3 * C / (16 * M + 3 * C) ≤ quittingRootAbsorptionMass root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) ≤
        C - 3 * C ^ 2 / (32 * M + 6 * C) := by
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward)
      (pair.2 - (fun _ : ι => C / 2))
  have hgap : (pair.2 - (fun _ : ι => C / 2)) crossing ≤
      reward (quittingSingletonTerminal crossing) crossing - 3 * C / 8 := by
    dsimp only [Pi.sub_apply]
    linarith
  have habsorptionRaw := belowSingleton_exactRoot_absorptionMass_lowerBound
    reward (pair.2 - (fun _ : ι => C / 2)) root crossing
      (show 0 < 3 * C / 8 by positivity) hreward hgap hnash
  have hdenom : 0 < 16 * M + 3 * C := by positivity
  have habsorption : 3 * C / (16 * M + 3 * C) ≤
      quittingRootAbsorptionMass root := by
    convert habsorptionRaw using 1
    field_simp
    ring
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair (C / 2) root (by positivity)
  have hdefect :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward (pair.2 - (fun _ : ι => C / 2)) root).mp hnash
  rw [hdefect, add_zero] at hbudget
  have habsorptionLe : quittingRootAbsorptionMass root ≤ 1 :=
    quittingRootAbsorptionMass_le_one root
  have hfirst :
      quittingTerminalSemanticDebtSum pair -
          quittingRootAbsorptionMass root *
            (quittingTerminalSemanticDebtSum pair - C / 2) ≤
        C - quittingRootAbsorptionMass root * (C - C / 2) := by
    nlinarith
  have hsecond :
      C - quittingRootAbsorptionMass root * (C - C / 2) ≤
        C - (3 * C / (16 * M + 3 * C)) * (C - C / 2) := by
    have hpositive : 0 < C - C / 2 := by linarith
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right habsorption hpositive.le) C
  refine ⟨root, hnash, habsorption, hbudget.trans (hfirst.trans ?_)⟩
  calc
    C - quittingRootAbsorptionMass root * (C - C / 2) ≤
        C - (3 * C / (16 * M + 3 * C)) * (C - C / 2) := hsecond
    _ = C - 3 * C ^ 2 / (32 * M + 6 * C) := by
      field_simp
      ring

private theorem quadraticDrop_le_half {M C : ℝ} (hM : 0 < M) (hC : 0 < C) :
    3 * C ^ 2 / (32 * M + 6 * C) ≤ C / 2 := by
  have hdenom : 0 < 32 * M + 6 * C := by positivity
  apply (div_le_iff₀ hdenom).2
  nlinarith [sq_nonneg C]

/-- An actual source with positive debt and a strictly preempted owner admits
a literal finite cap-threshold word with the exact quadratic debt drop and
the explicit logarithmic row bound. -/
theorem exists_literal_capThreshold_block_debtSum_le_quadraticDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (owner blocker : ι)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward source))
    (hpreempted : 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker) :
    let pair := quittingTerminalSemanticPair reward source
    let C := max (quittingTerminalSemanticDebtSum pair)
      (pair.2 owner - reward (quittingSingletonTerminal owner) owner)
    let θ := C / (32 * (M + C))
    let ell := reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker
    ∃ roots : List (ι → PMF Bool),
      roots.length ≤ 1 + quittingSoloCapThresholdHorizon M θ ell ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots source)) ≤
        C - 3 * C ^ 2 / (32 * M + 6 * C) := by
  dsimp only
  let pair := quittingTerminalSemanticPair reward source
  let D := quittingTerminalSemanticDebtSum pair
  let L := pair.2 owner - reward (quittingSingletonTerminal owner) owner
  let C := max D L
  let θ := C / (32 * (M + C))
  let ell := reward (quittingSingletonTerminal blocker) blocker -
    reward (quittingSingletonTerminal owner) blocker
  have hne : blocker ≠ owner := by
    intro heq
    subst blocker
    simp at hpreempted
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := by
    exact subset_closure (Set.mem_range_self source)
  have hDC : D ≤ C := le_max_left _ _
  have hLC : L ≤ C := le_max_right _ _
  have hC : 0 < C := lt_of_lt_of_le (by simpa [D, pair] using hdebtPos) hDC
  have hdenomTheta : 0 < 32 * (M + C) := by positivity
  have hθ0 : 0 < θ := by
    exact div_pos hC hdenomTheta
  have hθ1 : θ < 1 := by
    apply (div_lt_one hdenomTheta).2
    nlinarith
  have hthreshold : 4 * M * θ ≤ C / 8 := by
    have hratio : M / (M + C) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < M + C)).2
      linarith
    calc
      4 * M * θ = (M / (M + C)) * (C / 8) := by
        dsimp only [θ]
        field_simp
        ring
      _ ≤ 1 * (C / 8) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = C / 8 := one_mul _
  have hdropHalf : 3 * C ^ 2 / (32 * M + 6 * C) ≤ C / 2 :=
    quadraticDrop_le_half hM hC
  have hhalfDrop : C / 2 ≤ C - 3 * C ^ 2 / (32 * M + 6 * C) := by
    linarith
  let coin := quittingHazardCoin θ hθ0.le hθ1.le
  by_cases hearly : D ≤ C / 2
  · refine ⟨[], ?_, ?_⟩
    · simp
    · change D ≤ C - 3 * C ^ 2 / (32 * M + 6 * C)
      exact hearly.trans hhalfDrop
  by_cases hlow : ∃ crossing,
      pair.2 crossing - reward (quittingSingletonTerminal crossing) crossing ≤
        4 * M * θ
  · obtain ⟨crossing, hcrossing⟩ := hlow
    have hcrossingC : pair.2 crossing -
        reward (quittingSingletonTerminal crossing) crossing ≤ C / 8 :=
      hcrossing.trans hthreshold
    obtain ⟨root, hnash, habsorption, hdebt⟩ :=
      exists_auxiliaryExactRoot_debtSum_le_quadraticDrop
        reward pair crossing hM hC hreward hDC hcrossingC
    refine ⟨[root], ?_, ?_⟩
    · simp
    · change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root source)) ≤
        C - 3 * C ^ 2 / (32 * M + 6 * C)
      rw [quittingTerminalSemanticPair_rootThenContinuation]
      exact hdebt
  · push Not at hlow
    have hinitial : ∀ player,
        4 * M * θ < pair.2 player -
          reward (quittingSingletonTerminal player) player := by
      exact hlow
    obtain ⟨steps, crossing, hstepsPos, hstepsLe, hcrossingNe,
        hbefore, hcrossing, haffine, hdebtEq, hdebtUpper⟩ :=
      exists_first_solo_capThreshold_hit reward pair hne hM hreward hpair
        hθ0 hθ1 hinitial (by simpa only [ell] using hpreempted)
    have hstepsLe' : steps ≤ quittingSoloCapThresholdHorizon M θ ell := by
      simpa only [ell] using hstepsLe
    let reached := quittingSoloSemanticIterate reward owner coin pair steps
    have hreachedCarrier : reached ∈ quittingTerminalSemanticCarrier reward := by
      exact quittingSoloSemanticIterate_mem_carrier
        reward owner coin pair hpair steps
    have hreachedDebt : quittingTerminalSemanticDebtSum reached ≤ C := by
      exact hdebtUpper.trans (max_le hDC hLC)
    by_cases hreachedEarly : quittingTerminalSemanticDebtSum reached ≤ C / 2
    · refine ⟨List.replicate steps (quittingSoloStationaryRoot owner coin), ?_, ?_⟩
      · simp only [List.length_replicate]
        change steps ≤ 1 + quittingSoloCapThresholdHorizon M θ ell
        omega
      · rw [quittingTerminalSemanticPair_replicate_solo_word]
        change quittingTerminalSemanticDebtSum reached ≤
          C - 3 * C ^ 2 / (32 * M + 6 * C)
        exact hreachedEarly.trans hhalfDrop
    · have hcrossingC : reached.2 crossing -
          reward (quittingSingletonTerminal crossing) crossing ≤ C / 8 := by
        exact hcrossing.2.trans hthreshold
      obtain ⟨root, hnash, habsorption, hdebt⟩ :=
        exists_auxiliaryExactRoot_debtSum_le_quadraticDrop
          reward reached crossing hM hC hreward hreachedDebt hcrossingC
      refine ⟨root :: List.replicate steps
        (quittingSoloStationaryRoot owner coin), ?_, ?_⟩
      · simp only [List.length_cons, List.length_replicate]
        change steps + 1 ≤ 1 + quittingSoloCapThresholdHorizon M θ ell
        omega
      · rw [quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix,
          quittingFiniteRootWordSemanticPrefix_eq_foldr, List.foldr_cons]
        have hfold : List.foldr (quittingTerminalSemanticPrefix reward) pair
            (List.replicate steps (quittingSoloStationaryRoot owner coin)) =
            reached := by
          rw [← quittingFiniteRootWordSemanticPrefix_eq_foldr,
            ← quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix,
            quittingTerminalSemanticPair_replicate_solo_word]
        rw [hfold]
        change quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix reward root reached) ≤
          C - 3 * C ^ 2 / (32 * M + 6 * C)
        exact hdebt

end GameTheory
