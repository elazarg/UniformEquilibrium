import UniformEquilibrium.Quitting.Root.RationalApproximateQuittingRoot
import UniformEquilibrium.Quitting.Paths.FiniteSoloCapThresholdDescent

/-! # Rational approximate auxiliary roots with quadratic debt drop -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every row in a literal finite word has rational Quit probabilities. -/
def IsRationalQuittingRootWord (roots : List (ι → PMF Bool)) : Prop :=
  ∀ root ∈ roots, IsRationalQuittingRoot root

omit [Fintype ι] in
theorem isRationalQuittingRoot_soloStationaryRoot_of_rationalHazard
    (owner : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrational : ∃ probability : ℚ, t = (probability : ℝ)) :
    IsRationalQuittingRoot
      (quittingSoloStationaryRoot owner (quittingHazardCoin t ht0 ht1)) := by
  obtain ⟨probability, hprobability⟩ := hrational
  intro player
  by_cases hplayer : player = owner
  · subst player
    exact ⟨probability, by simp [quittingSoloStationaryRoot, hprobability]⟩
  · exact ⟨0, by simp [quittingSoloStationaryRoot, hplayer]⟩

/-- A rational approximate Nash row after a cap crossing spends one quarter
of the exact quadratic debt drop. -/
theorem exists_auxiliaryRationalRoot_debtSum_le_quarterQuadraticDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (crossing : ι)
    {M C : ℝ} (hM : 0 < M) (hC : 0 < C)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtUpper : quittingTerminalSemanticDebtSum pair ≤ C)
    (hcrossing : pair.2 crossing -
      reward (quittingSingletonTerminal crossing) crossing ≤ C / 8) :
    ∃ root : ι → PMF Bool,
      IsRationalQuittingRoot root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) ≤
        C - 3 * C ^ 2 / (128 * M + 24 * C) := by
  let drop := 3 * C ^ 2 / (32 * M + 6 * C)
  let tolerance := min (drop / 4) (3 * C / 32)
  have hdrop : 0 < drop := by dsimp only [drop]; positivity
  have htolerance : 0 < tolerance := by
    dsimp only [tolerance]
    exact lt_min (by positivity) (by positivity)
  obtain ⟨root, hrational, hdefectStrict⟩ :=
    exists_rational_quittingRootTotalNashDefect_lt
      reward (pair.2 - fun _ => C / 2) htolerance
  have hdefectDrop : quittingRootTotalNashDefect
      reward (pair.2 - fun _ => C / 2) root ≤ drop / 4 :=
    hdefectStrict.le.trans (min_le_left _ _)
  have hcoordinateLeTotal : quittingRootCoordinateNashDefect
      reward (pair.2 - fun _ => C / 2) root crossing ≤
        quittingRootTotalNashDefect
          reward (pair.2 - fun _ => C / 2) root := by
    unfold quittingRootTotalNashDefect
    exact Finset.single_le_sum
      (fun player _ => quittingRootCoordinateNashDefect_nonneg
        reward (pair.2 - fun _ => C / 2) root player)
      (Finset.mem_univ crossing)
  have hcoordinate : quittingRootCoordinateNashDefect
      reward (pair.2 - fun _ => C / 2) root crossing ≤ 3 * C / 32 :=
    hcoordinateLeTotal.trans (hdefectStrict.le.trans (min_le_right _ _))
  have hgap : (pair.2 - (fun _ : ι => C / 2)) crossing ≤
      reward (quittingSingletonTerminal crossing) crossing - 3 * C / 8 := by
    dsimp only [Pi.sub_apply]
    linarith
  have habsorptionRaw := belowSingleton_approximateRoot_absorptionMass_lowerBound
    reward (pair.2 - fun _ => C / 2) root crossing
      (show 0 < 3 * C / 8 by positivity) hreward hgap (by
        simpa only [show 3 * C / 8 / 4 = 3 * C / 32 by ring] using hcoordinate)
  have habsorption : 3 * C / (32 * M + 6 * C) ≤
      quittingRootAbsorptionMass root := by
    convert habsorptionRaw using 1
    field_simp
    ring
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair (C / 2) root (by positivity)
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
        C - (3 * C / (32 * M + 6 * C)) * (C - C / 2) := by
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_right habsorption
        (by linarith : 0 ≤ C - C / 2)) C
  refine ⟨root, hrational, hbudget.trans ?_⟩
  calc
    quittingTerminalSemanticDebtSum pair -
          quittingRootAbsorptionMass root *
            (quittingTerminalSemanticDebtSum pair - C / 2) +
        quittingRootTotalNashDefect
          reward (pair.2 - fun _ => C / 2) root ≤
      C - (3 * C / (32 * M + 6 * C)) * (C - C / 2) + drop / 4 := by
        linarith
    _ = C - 3 * C ^ 2 / (128 * M + 24 * C) := by
      dsimp only [drop]
      field_simp
      ring

/-- A rational cap-threshold block with the quarter quadratic drop. Rationality of the hazard is the
precise algebraic input needed for the solo rows; the final approximate Nash
row is selected by rational density. This theorem does not claim executable
grid search. -/
theorem exists_rational_literal_capThreshold_block_debtSum_le_quarterDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (owner blocker : ι)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward source))
    (hpreempted : 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    (hθRational :
      let pair := quittingTerminalSemanticPair reward source
      let C := max (quittingTerminalSemanticDebtSum pair)
        (pair.2 owner - reward (quittingSingletonTerminal owner) owner)
      let θ := C / (32 * (M + C))
      ∃ probability : ℚ, θ = (probability : ℝ)) :
    let pair := quittingTerminalSemanticPair reward source
    let C := max (quittingTerminalSemanticDebtSum pair)
      (pair.2 owner - reward (quittingSingletonTerminal owner) owner)
    let θ := C / (32 * (M + C))
    let ell := reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker
    ∃ roots : List (ι → PMF Bool),
      IsRationalQuittingRootWord roots ∧
      roots.length ≤ 1 + quittingSoloCapThresholdHorizon M θ ell ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots source)) ≤
        C - 3 * C ^ 2 / (128 * M + 24 * C) := by
  dsimp only at hθRational ⊢
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
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward :=
    subset_closure (Set.mem_range_self source)
  have hDC : D ≤ C := le_max_left _ _
  have hLC : L ≤ C := le_max_right _ _
  have hC : 0 < C := lt_of_lt_of_le (by simpa [D, pair] using hdebtPos) hDC
  have hdenomTheta : 0 < 32 * (M + C) := by positivity
  have hθ0 : 0 < θ := div_pos hC hdenomTheta
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
      _ ≤ 1 * (C / 8) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = C / 8 := one_mul _
  have hdropHalf : 3 * C ^ 2 / (128 * M + 24 * C) ≤ C / 2 := by
    have hdenom : 0 < 128 * M + 24 * C := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith [mul_pos hM hC]
  have hhalfDrop : C / 2 ≤ C - 3 * C ^ 2 / (128 * M + 24 * C) := by
    linarith
  let coin := quittingHazardCoin θ hθ0.le hθ1.le
  have hcoinRational : IsRationalQuittingRoot
      (quittingSoloStationaryRoot owner coin) :=
    isRationalQuittingRoot_soloStationaryRoot_of_rationalHazard
      owner hθ0.le hθ1.le hθRational
  by_cases hearly : D ≤ C / 2
  · refine ⟨[], ?_, by simp, ?_⟩
    · simp [IsRationalQuittingRootWord]
    · change D ≤ C - 3 * C ^ 2 / (128 * M + 24 * C)
      exact hearly.trans hhalfDrop
  by_cases hlow : ∃ crossing,
      pair.2 crossing - reward (quittingSingletonTerminal crossing) crossing ≤
        4 * M * θ
  · obtain ⟨crossing, hcrossing⟩ := hlow
    have hcrossingC : pair.2 crossing -
        reward (quittingSingletonTerminal crossing) crossing ≤ C / 8 :=
      hcrossing.trans hthreshold
    obtain ⟨root, hrational, hdebt⟩ :=
      exists_auxiliaryRationalRoot_debtSum_le_quarterQuadraticDrop
        reward pair crossing hM hC hreward hDC hcrossingC
    refine ⟨[root], ?_, by simp, ?_⟩
    · simpa [IsRationalQuittingRootWord] using hrational
    · change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root source)) ≤
        C - 3 * C ^ 2 / (128 * M + 24 * C)
      rw [quittingTerminalSemanticPair_rootThenContinuation]
      exact hdebt
  · push Not at hlow
    have hinitial : ∀ player, 4 * M * θ < pair.2 player -
        reward (quittingSingletonTerminal player) player := hlow
    obtain ⟨steps, crossing, hstepsPos, hstepsLe, hcrossingNe,
        hbefore, hcrossing, haffine, hdebtEq, hdebtUpper⟩ :=
      exists_first_solo_capThreshold_hit reward pair hne hM hreward hpair
        hθ0 hθ1 hinitial (by simpa only [ell] using hpreempted)
    have hstepsLe' : steps ≤ quittingSoloCapThresholdHorizon M θ ell := by
      simpa only [ell] using hstepsLe
    let reached := quittingSoloSemanticIterate reward owner coin pair steps
    have hreachedDebt : quittingTerminalSemanticDebtSum reached ≤ C :=
      hdebtUpper.trans (max_le hDC hLC)
    by_cases hreachedEarly : quittingTerminalSemanticDebtSum reached ≤ C / 2
    · refine ⟨List.replicate steps (quittingSoloStationaryRoot owner coin), ?_, ?_, ?_⟩
      · intro root hroot
        rw [List.mem_replicate] at hroot
        exact hroot.2 ▸ hcoinRational
      · simp only [List.length_replicate]
        change steps ≤ 1 + quittingSoloCapThresholdHorizon M θ ell
        omega
      · rw [quittingTerminalSemanticPair_replicate_solo_word]
        change quittingTerminalSemanticDebtSum reached ≤
          C - 3 * C ^ 2 / (128 * M + 24 * C)
        exact hreachedEarly.trans hhalfDrop
    · have hcrossingC : reached.2 crossing -
          reward (quittingSingletonTerminal crossing) crossing ≤ C / 8 :=
        hcrossing.2.trans hthreshold
      obtain ⟨root, hrational, hdebt⟩ :=
        exists_auxiliaryRationalRoot_debtSum_le_quarterQuadraticDrop
          reward reached crossing hM hC hreward hreachedDebt hcrossingC
      refine ⟨root :: List.replicate steps
        (quittingSoloStationaryRoot owner coin), ?_, ?_, ?_⟩
      · intro candidate hcandidate
        simp only [List.mem_cons, List.mem_replicate] at hcandidate
        rcases hcandidate with rfl | ⟨_, rfl⟩
        · exact hrational
        · exact hcoinRational
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
        exact hdebt

end GameTheory
