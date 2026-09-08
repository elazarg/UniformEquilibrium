import UniformEquilibrium.Quitting.Paths.ExecutableRationalAuxiliaryRootDebtDrop

/-! # Executable rational cap-threshold block selection

The selector operates on a literal rational finite source followed by Always
Continue.  All branch tests, solo iterates, and auxiliary-root acceptance
tests are rational.  Its correctness is stated for the actual unrestricted
behavioral response caps of the resulting literal root stack.
-/

namespace GameTheory

variable {players : ℕ}

/-- Total debt computed from a rational finite source word. -/
def rationalFiniteSourceDebt
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players)) : ℚ :=
  rationalQuittingSemanticDebtSum
    (rationalQuittingFiniteWordSemanticPair reward sourceRoots)

/-- The cap-threshold scale `max(D,B_i-s_i)` at a rational finite source. -/
def rationalFiniteSourceCapThresholdScale
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players))
    (owner : Fin players) : ℚ :=
  let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  max (rationalQuittingSemanticDebtSum pair)
    (pair.2 owner - reward (quittingSingletonTerminal owner) owner)

/-- The rational solo hazard selected by the cap-threshold construction. -/
def rationalCapThresholdSoloHazard (M C : ℚ) : ℚ :=
  C / (32 * (M + C))

private theorem rationalFirstCapThreshold_all_above
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps)
    {steps : ℕ}
    (hsteps : steps < rationalFirstSoloCapThresholdIndex
      reward owner hazard threshold source hexists) (player : Fin players) :
    threshold <
      (rationalQuittingSoloSemanticIterate reward owner hazard source steps).2 player -
        reward (quittingSingletonTerminal player) player := by
  exact lt_of_not_ge fun hle =>
    rationalFirstSoloCapThresholdIndex_before
      reward owner hazard threshold source hexists hsteps ⟨player, hle⟩

private theorem rationalFirstCapThreshold_debtSum_le_max
    (reward : RationalQuittingReward players)
    (source : RationalQuittingSemanticPair players) (owner : Fin players)
    {M hazard : ℚ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : source.toReal ∈
      quittingTerminalSemanticCarrier (rationalQuittingRewardToReal reward))
    (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard (4 * M * hazard) source steps) :
    rationalQuittingSemanticDebtSum
        (rationalQuittingSoloSemanticIterate reward owner hazard source
          (rationalFirstSoloCapThresholdIndex
            reward owner hazard (4 * M * hazard) source hexists)) ≤
      max (rationalQuittingSemanticDebtSum source)
        (source.2 owner - reward (quittingSingletonTerminal owner) owner) := by
  let steps := rationalFirstSoloCapThresholdIndex
    reward owner hazard (4 * M * hazard) source hexists
  have hrewardReal : ∀ terminal player,
      |rationalQuittingRewardToReal reward terminal player| ≤ (M : ℝ) := by
    intro terminal player
    unfold rationalQuittingRewardToReal
    exact_mod_cast hreward terminal player
  have hbefore : ∀ k, k < steps → ∀ player,
      4 * (M : ℝ) * (hazard : ℝ) <
        (quittingSoloSemanticIterate (rationalQuittingRewardToReal reward) owner
          (quittingHazardCoin (hazard : ℝ)
            (by exact_mod_cast hhazard0.le) (by exact_mod_cast hhazard1.le))
          source.toReal k).2 player -
            rationalQuittingRewardToReal reward
              (quittingSingletonTerminal player) player := by
    intro k hk player
    have habove := rationalFirstCapThreshold_all_above
      reward owner hazard (4 * M * hazard) source hexists hk player
    rw [quittingSoloSemanticIterate_rational_eq_cast
      reward owner ⟨hhazard0.le, hhazard1.le⟩ source k]
    simp only [RationalQuittingSemanticPair.toReal,
      rationalQuittingRewardToReal]
    exact_mod_cast habove
  have hbound := quittingSoloSemanticIterate_debtSum_le_max_of_before_threshold
    (rationalQuittingRewardToReal reward) source.toReal owner hrewardReal hsource
      (by exact_mod_cast hhazard0) (by exact_mod_cast hhazard1) steps hbefore
  rw [quittingSoloSemanticIterate_rational_eq_cast
    reward owner ⟨hhazard0.le, hhazard1.le⟩ source steps,
    quittingTerminalSemanticDebtSum_rational_eq_cast,
    quittingTerminalSemanticDebtSum_rational_eq_cast] at hbound
  simp only [RationalQuittingSemanticPair.toReal,
    rationalQuittingRewardToReal] at hbound
  exact_mod_cast hbound

private theorem rationalCapThreshold_parameters
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players))
    (owner : Fin players) {M : ℚ} (hM : 0 < M)
    (hdebtPos : 0 < rationalFiniteSourceDebt reward sourceRoots) :
    let C := rationalFiniteSourceCapThresholdScale reward sourceRoots owner
    let hazard := rationalCapThresholdSoloHazard M C
    0 < C ∧ 0 < hazard ∧ hazard < 1 ∧ 4 * M * hazard ≤ C / 8 := by
  dsimp only [rationalFiniteSourceCapThresholdScale,
    rationalFiniteSourceDebt, rationalCapThresholdSoloHazard]
  let pair := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let D := rationalQuittingSemanticDebtSum pair
  let L := pair.2 owner - reward (quittingSingletonTerminal owner) owner
  let C := max D L
  have hDC : D ≤ C := le_max_left _ _
  have hDpos : 0 < D := by
    simpa [D, pair, rationalFiniteSourceDebt] using hdebtPos
  have hC : 0 < C := lt_of_lt_of_le hDpos hDC
  have hdenom : 0 < 32 * (M + C) := by positivity
  have hhazard0 : 0 < C / (32 * (M + C)) := div_pos hC hdenom
  have hhazard1 : C / (32 * (M + C)) < 1 := by
    apply (div_lt_one hdenom).2
    nlinarith
  have hratio : M / (M + C) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℚ) < M + C)).2
    linarith
  have hthreshold : 4 * M * (C / (32 * (M + C))) ≤ C / 8 := by
    calc
      4 * M * (C / (32 * (M + C))) = (M / (M + C)) * (C / 8) := by
        field_simp
        ring
      _ ≤ 1 * (C / 8) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = C / 8 := one_mul _
  exact ⟨hC, hhazard0, hhazard1, hthreshold⟩

private theorem rationalCapThreshold_hit_exists
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players))
    (owner blocker : Fin players) {M : ℚ} (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < rationalFiniteSourceDebt reward sourceRoots)
    (hpreempted : 0 < reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker)
    (hinitial : ∀ player,
      4 * M * rationalCapThresholdSoloHazard M
          (rationalFiniteSourceCapThresholdScale reward sourceRoots owner) <
        (rationalQuittingFiniteWordSemanticPair reward sourceRoots).2 player -
          reward (quittingSingletonTerminal player) player) :
    ∃ steps, rationalSoloCapThresholdHit reward owner
      (rationalCapThresholdSoloHazard M
        (rationalFiniteSourceCapThresholdScale reward sourceRoots owner))
      (4 * M * rationalCapThresholdSoloHazard M
        (rationalFiniteSourceCapThresholdScale reward sourceRoots owner))
      (rationalQuittingFiniteWordSemanticPair reward sourceRoots) steps := by
  obtain ⟨hexists, _⟩ :=
    exists_rationalFirstSoloCapThresholdIndex_le_logHorizon
      reward sourceRoots owner blocker M
      (rationalCapThresholdSoloHazard M
        (rationalFiniteSourceCapThresholdScale reward sourceRoots owner))
      hM hreward
      (rationalCapThreshold_parameters reward sourceRoots owner hM hdebtPos).2.1
      (rationalCapThreshold_parameters reward sourceRoots owner hM hdebtPos).2.2.1
      hinitial hpreempted
  exact hexists

/-- The executable rational cap-threshold block. Its proof arguments certify
the valid source region but do not contribute to the computed rational word. -/
def executableRationalCapThresholdBlock
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players))
    (owner blocker : Fin players) (M : ℚ)
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < rationalFiniteSourceDebt reward sourceRoots)
    (hpreempted : 0 < reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker) :
    List (RationalQuittingRoot players) :=
  let source := rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let D := rationalQuittingSemanticDebtSum source
  let C := max D
    (source.2 owner - reward (quittingSingletonTerminal owner) owner)
  let hazard := rationalCapThresholdSoloHazard M C
  let hC := (rationalCapThreshold_parameters
    reward sourceRoots owner hM hdebtPos).1
  let hhazard0 := (rationalCapThreshold_parameters
    reward sourceRoots owner hM hdebtPos).2.1
  let hhazard1 := (rationalCapThreshold_parameters
    reward sourceRoots owner hM hdebtPos).2.2.1
  if _hearly : D ≤ C / 2 then []
  else if hlow : ∃ crossing : Fin players,
      source.2 crossing - reward (quittingSingletonTerminal crossing) crossing ≤
        4 * M * hazard then
    [rationalAuxiliaryRootGridSelector reward source M C hM hC]
  else
    let hinitial : ∀ player, 4 * M * hazard <
        source.2 player - reward (quittingSingletonTerminal player) player := by
      intro player
      exact lt_of_not_ge fun hle => hlow ⟨player, hle⟩
    let hexists := rationalCapThreshold_hit_exists reward sourceRoots owner blocker
      hM hreward hdebtPos hpreempted hinitial
    let steps := rationalFirstSoloCapThresholdIndex
      reward owner hazard (4 * M * hazard) source hexists
    let reached := rationalQuittingSoloSemanticIterate
      reward owner hazard source steps
    let solo := rationalQuittingSoloRoot owner hazard
    if _hreachedEarly : rationalQuittingSemanticDebtSum reached ≤ C / 2 then
      List.replicate steps solo
    else
      rationalAuxiliaryRootGridSelector reward reached M C hM hC ::
        List.replicate steps solo

/-- The executable block obeys the packet's sharp row count and quarter
quadratic decrease for the actual complete behavioral response caps. -/
theorem executableRationalCapThresholdBlock_length_and_debtSum_le
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players))
    (owner blocker : Fin players) (M : ℚ)
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hdebtPos : 0 < rationalFiniteSourceDebt reward sourceRoots)
    (hpreempted : 0 < reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker) :
    let C := rationalFiniteSourceCapThresholdScale reward sourceRoots owner
    let hazard := rationalCapThresholdSoloHazard M C
    let ell := reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker
    let block := executableRationalCapThresholdBlock
      reward sourceRoots owner blocker M hM hreward hdebtPos hpreempted
    block.length ≤
        1 + quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ) (ell : ℝ) ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
              (block.map RationalQuittingRoot.toPMF)
              (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
                (sourceRoots.map RationalQuittingRoot.toPMF)
                (quittingAlwaysContinueProfile
                  (rationalQuittingRewardToReal reward))))) ≤
        ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ) := by
  dsimp only
  let source : RationalQuittingSemanticPair players :=
    rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let D := rationalQuittingSemanticDebtSum source
  let C := max D
    (source.2 owner - reward (quittingSingletonTerminal owner) owner)
  let hazard := rationalCapThresholdSoloHazard M C
  let threshold := 4 * M * hazard
  let sourceProfile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (sourceRoots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hparameters := rationalCapThreshold_parameters
    reward sourceRoots owner hM hdebtPos
  have hC : 0 < C := by
    simpa only [C, D, source, rationalFiniteSourceCapThresholdScale,
      rationalFiniteSourceDebt] using hparameters.1
  have hhazard0 : 0 < hazard := by
    simpa only [hazard, C, D, source, rationalFiniteSourceCapThresholdScale,
      rationalFiniteSourceDebt] using hparameters.2.1
  have hhazard1 : hazard < 1 := by
    simpa only [hazard, C, D, source, rationalFiniteSourceCapThresholdScale,
      rationalFiniteSourceDebt] using hparameters.2.2.1
  have hthreshold : threshold ≤ C / 8 := by
    simpa only [threshold, hazard, C, D, source,
      rationalFiniteSourceCapThresholdScale, rationalFiniteSourceDebt] using
        hparameters.2.2.2
  have hDC : D ≤ C := le_max_left _ _
  have hLC : source.2 owner - reward (quittingSingletonTerminal owner) owner ≤ C :=
    le_max_right _ _
  have hdropHalf : 3 * C ^ 2 / (128 * M + 24 * C) ≤ C / 2 := by
    have hdenom : 0 < 128 * M + 24 * C := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith [mul_pos hM hC]
  have hhalfDrop : C / 2 ≤ C - 3 * C ^ 2 / (128 * M + 24 * C) := by
    linarith
  have hpair : quittingTerminalSemanticPair
      (rationalQuittingRewardToReal reward) sourceProfile = source.toReal := by
    dsimp only [sourceProfile, source]
    simpa [RationalQuittingSemanticPair.toReal] using
      (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward sourceRoots)
  have hsource : source.toReal ∈
      quittingTerminalSemanticCarrier (rationalQuittingRewardToReal reward) := by
    rw [← hpair]
    exact subset_closure (Set.mem_range_self sourceProfile)
  rw [executableRationalCapThresholdBlock]
  dsimp only
  split_ifs with hearly hlow hreachedEarly
  · constructor
    · simp
    · have hearly' : D ≤ C / 2 := by
        simpa only [D, C, source, rationalFiniteSourceCapThresholdScale,
          rationalFiniteSourceDebt] using hearly
      change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            sourceProfile) ≤
        ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ)
      rw [hpair, quittingTerminalSemanticDebtSum_rational_eq_cast]
      exact_mod_cast hearly'.trans hhalfDrop
  · obtain ⟨crossing, hcrossing⟩ := hlow
    have hcrossingC : source.2 crossing -
        reward (quittingSingletonTerminal crossing) crossing ≤ C / 8 := by
      exact hcrossing.trans hthreshold
    constructor
    · simp
    · change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
              [(rationalAuxiliaryRootGridSelector reward source M C hM hC).toPMF]
              sourceProfile)) ≤
        ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ)
      rw [quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix,
        quittingFiniteRootWordSemanticPrefix_eq_foldr]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [hpair]
      exact rationalAuxiliaryRootGridSelector_debtSum_le_quarterQuadraticDrop
        reward source crossing hM hC hreward hDC hcrossingC
  · have hinitial : ∀ player, threshold <
        source.2 player - reward (quittingSingletonTerminal player) player := by
      intro player
      exact lt_of_not_ge fun hle => hlow ⟨player, hle⟩
    let hexists := rationalCapThreshold_hit_exists reward sourceRoots owner blocker
      hM hreward hdebtPos hpreempted hinitial
    let steps := rationalFirstSoloCapThresholdIndex
      reward owner hazard threshold source hexists
    let reached := rationalQuittingSoloSemanticIterate
      reward owner hazard source steps
    let solo := rationalQuittingSoloRoot owner hazard
    obtain ⟨comparisonExists, hcomparisonBound⟩ :=
      exists_rationalFirstSoloCapThresholdIndex_le_logHorizon
        reward sourceRoots owner blocker M hazard hM hreward hhazard0 hhazard1
        hinitial hpreempted
    have hstepsLe : steps ≤
        quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ)
          ((reward (quittingSingletonTerminal blocker) blocker -
            reward (quittingSingletonTerminal owner) blocker : ℚ) : ℝ) := by
      exact (rationalFirstSoloCapThresholdIndex_le reward owner hazard threshold source
        hexists (rationalFirstSoloCapThresholdIndex_spec reward owner hazard threshold
          source comparisonExists)).trans hcomparisonBound
    have hreachedPair : quittingTerminalSemanticPair
        (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (List.replicate steps solo.toPMF) sourceProfile) = reached.toReal := by
      rw [show solo.toPMF = quittingSoloStationaryRoot owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hhazard0.le) (by exact_mod_cast hhazard1.le)) by
            exact rationalQuittingSoloRoot_toPMF_eq owner
              ⟨hhazard0.le, hhazard1.le⟩,
        quittingTerminalSemanticPair_replicate_solo_word, hpair,
        quittingSoloSemanticIterate_rational_eq_cast
          reward owner ⟨hhazard0.le, hhazard1.le⟩ source steps]
    constructor
    · change (List.replicate steps solo).length ≤
        1 + quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ)
          ((reward (quittingSingletonTerminal blocker) blocker -
            reward (quittingSingletonTerminal owner) blocker : ℚ) : ℝ)
      simp only [List.length_replicate]
      omega
    · simp only [List.map_replicate]
      change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
              (List.replicate steps solo.toPMF) sourceProfile)) ≤
        ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ)
      rw [hreachedPair, quittingTerminalSemanticDebtSum_rational_eq_cast]
      have hreachedEarly' : rationalQuittingSemanticDebtSum reached ≤ C / 2 := by
        simpa only [reached, steps, solo, hexists, threshold, hazard, C, D, source,
          rationalFiniteSourceCapThresholdScale, rationalFiniteSourceDebt] using
            hreachedEarly
      exact_mod_cast hreachedEarly'.trans hhalfDrop
  · have hinitial : ∀ player, threshold <
        source.2 player - reward (quittingSingletonTerminal player) player := by
      intro player
      exact lt_of_not_ge fun hle => hlow ⟨player, hle⟩
    let hexists := rationalCapThreshold_hit_exists reward sourceRoots owner blocker
      hM hreward hdebtPos hpreempted hinitial
    let steps := rationalFirstSoloCapThresholdIndex
      reward owner hazard threshold source hexists
    let reached := rationalQuittingSoloSemanticIterate
      reward owner hazard source steps
    let solo := rationalQuittingSoloRoot owner hazard
    let crossing := rationalFirstSoloCapThresholdPlayer
      reward owner hazard threshold source hexists
    obtain ⟨comparisonExists, hcomparisonBound⟩ :=
      exists_rationalFirstSoloCapThresholdIndex_le_logHorizon
        reward sourceRoots owner blocker M hazard hM hreward hhazard0 hhazard1
        hinitial hpreempted
    have hstepsLe : steps ≤
        quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ)
          ((reward (quittingSingletonTerminal blocker) blocker -
            reward (quittingSingletonTerminal owner) blocker : ℚ) : ℝ) := by
      exact (rationalFirstSoloCapThresholdIndex_le reward owner hazard threshold source
        hexists (rationalFirstSoloCapThresholdIndex_spec reward owner hazard threshold
          source comparisonExists)).trans hcomparisonBound
    have hreachedDebt : rationalQuittingSemanticDebtSum reached ≤ C := by
      have hbound := rationalFirstCapThreshold_debtSum_le_max
        reward source owner hreward hsource hhazard0 hhazard1 hexists
      simpa only [reached, steps, C, D] using hbound
    have hcrossingThreshold : reached.2 crossing -
        reward (quittingSingletonTerminal crossing) crossing ≤ threshold := by
      exact rationalFirstSoloCapThresholdPlayer_spec
        reward owner hazard threshold source hexists
    have hcrossingC : reached.2 crossing -
        reward (quittingSingletonTerminal crossing) crossing ≤ C / 8 :=
      hcrossingThreshold.trans hthreshold
    have hreachedPair : quittingTerminalSemanticPair
        (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (List.replicate steps solo.toPMF) sourceProfile) = reached.toReal := by
      rw [show solo.toPMF = quittingSoloStationaryRoot owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hhazard0.le) (by exact_mod_cast hhazard1.le)) by
            exact rationalQuittingSoloRoot_toPMF_eq owner
              ⟨hhazard0.le, hhazard1.le⟩,
        quittingTerminalSemanticPair_replicate_solo_word, hpair,
        quittingSoloSemanticIterate_rational_eq_cast
          reward owner ⟨hhazard0.le, hhazard1.le⟩ source steps]
    constructor
    · change (rationalAuxiliaryRootGridSelector reward reached M C hM hC ::
          List.replicate steps solo).length ≤
        1 + quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ)
          ((reward (quittingSingletonTerminal blocker) blocker -
            reward (quittingSingletonTerminal owner) blocker : ℚ) : ℝ)
      simp only [List.length_cons, List.length_replicate]
      omega
    · simp only [List.map_cons, List.map_replicate]
      change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
            (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
              ((rationalAuxiliaryRootGridSelector reward reached M C hM hC).toPMF ::
                List.replicate steps solo.toPMF) sourceProfile)) ≤
        ((C - 3 * C ^ 2 / (128 * M + 24 * C) : ℚ) : ℝ)
      rw [quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix,
        quittingFiniteRootWordSemanticPrefix_eq_foldr]
      simp only [List.foldr_cons]
      have hfold : List.foldr
          (quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward))
          (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward) sourceProfile)
          (List.replicate steps solo.toPMF) = reached.toReal := by
        rw [← quittingFiniteRootWordSemanticPrefix_eq_foldr,
          ← quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix]
        exact hreachedPair
      rw [hfold]
      exact rationalAuxiliaryRootGridSelector_debtSum_le_quarterQuadraticDrop
        reward reached crossing hM hC hreward hreachedDebt hcrossingC

end GameTheory
