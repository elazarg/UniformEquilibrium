import Research.Quitting.FinFourProducerAtlas.Source
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.CapBandRedistribution

/-!
# Full-debt cap-band target compactification

This file compiles one supplied four-player minimum-law source whose limiting
semantic point has positive debt in every coordinate.  It applies cap-band
redistribution to one fixed mover along the source's literal chronological
profiles, retains the selected finite cuts, and compactifies the exact target
semantic pairs and terminal laws.

The final alternative concerns the compact target limit: its total debt is
either strictly above the supplied global minimum or equal to it.  No finite
target profile is asserted to lie on the minimum fibre.  No paid-port, chord,
prefix, support-contraction, renewal, Nash, or uniform-equilibrium conclusion
is made here.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

/-- A literal cap-band response sequence selected from the chronological
profiles retained by a four-player minimum-atom producer. -/
structure FinFourFullDebtCapBandResponseSequence
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (M : ℝ) where
  chronologyProfiles : ℕ → (quittingGame reward).BehaviorProfile
  sourceIndex : ℕ → ℕ
  sourceIndex_strictMono : StrictMono sourceIndex
  mover : Fin 4
  limitingMoverDebt_pos :
    0 < quittingTerminalSemanticDebt source.point.1 mover
  epsilon : ℕ → ℝ
  epsilon_pos : ∀ rank, 0 < epsilon rank
  epsilon_tendsto_zero : Tendsto epsilon atTop (nhds 0)
  epsilon_le_quarter : ∀ rank,
    epsilon rank ≤ quittingTerminalSemanticDebt source.point.1 mover / 4
  source_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (chronologyProfiles (sourceIndex rank)),
        quittingTerminalOutcomeMass reward
          (chronologyProfiles (sourceIndex rank))))
    atTop (nhds source.point)
  sourceMoverDebt_gt_three_quarters : ∀ rank,
    3 * quittingTerminalSemanticDebt source.point.1 mover / 4 <
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (chronologyProfiles (sourceIndex rank))) mover
  cutData : ∀ rank, QuittingCapBandFiniteCut reward
    (chronologyProfiles (sourceIndex rank)) mover (epsilon rank)

namespace FinFourFullDebtCapBandResponseSequence

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal source profile at a selected chronological index. -/
def sourceProfile
    (sequence : FinFourFullDebtCapBandResponseSequence source M) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  sequence.chronologyProfiles (sequence.sourceIndex rank)

/-- The literal cap-band target profile at the same selected row. -/
def targetProfile
    (sequence : FinFourFullDebtCapBandResponseSequence source M) (rank : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  (sequence.cutData rank).targetProfile

/-- The source row is literally one retained chronological profile. -/
theorem sourceProfile_eq_chronologyProfile
    (sequence : FinFourFullDebtCapBandResponseSequence source M) (rank : ℕ) :
    sequence.sourceProfile rank =
      sequence.chronologyProfiles (sequence.sourceIndex rank) := rfl

/-- The target is definitionally a unilateral update of the selected source. -/
theorem targetProfile_eq_update
    (sequence : FinFourFullDebtCapBandResponseSequence source M) (rank : ℕ) :
    sequence.targetProfile rank = Function.update (sequence.sourceProfile rank)
      sequence.mover (sequence.cutData rank).targetStrategy := rfl

/-- Every target preserves the complete live-root prefix before its retained
finite cut. -/
theorem target_liveRoot_eq_source_of_lt
    (sequence : FinFourFullDebtCapBandResponseSequence source M)
    (rank time : ℕ) (htime : time < (sequence.cutData rank).cut) :
    quittingProfileLiveRoot reward (sequence.targetProfile rank) time =
      quittingProfileLiveRoot reward (sequence.sourceProfile rank) time :=
  (sequence.cutData rank).profileLiveRoot_target_eq_of_lt htime

/-- Every band width is strictly below the corresponding literal source
mover debt. -/
theorem epsilon_lt_sourceMoverDebt
    (sequence : FinFourFullDebtCapBandResponseSequence source M) (rank : ℕ) :
    sequence.epsilon rank < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sequence.sourceProfile rank))
        sequence.mover := by
  have hsource := sequence.sourceMoverDebt_gt_three_quarters rank
  have hepsilon := sequence.epsilon_le_quarter rank
  have hpositive := sequence.limitingMoverDebt_pos
  dsimp only [sourceProfile] at hsource ⊢
  nlinarith

/-- The response gain has a uniform half-limit-debt floor. -/
theorem half_limitingMoverDebt_le_payoffGain
    (sequence : FinFourFullDebtCapBandResponseSequence source M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    quittingTerminalSemanticDebt source.point.1 sequence.mover / 2 ≤
      quittingTerminalPayoff reward (sequence.targetProfile rank) sequence.mover -
        quittingTerminalPayoff reward (sequence.sourceProfile rank) sequence.mover := by
  have hgain := (sequence.cutData rank).sourceDebt_sub_epsilon_le_target_payoffGain
    (sequence.epsilon_pos rank) hreward
  have hsource := sequence.sourceMoverDebt_gt_three_quarters rank
  have hepsilon := sequence.epsilon_le_quarter rank
  dsimp only [sourceProfile, targetProfile] at hgain ⊢
  linarith

/-- The target mover debt is bounded by the vanishing cap-band width. -/
theorem targetMoverDebt_le_epsilon
    (sequence : FinFourFullDebtCapBandResponseSequence source M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sequence.targetProfile rank))
        sequence.mover ≤ sequence.epsilon rank := by
  exact (sequence.cutData rank).target_terminalSemanticDebt_le
    (sequence.epsilon_pos rank) hreward

/-- The selected finite cut retains a uniform literal source joint-reach
floor. -/
theorem limitingMoverDebt_div_four_mul_le_jointReach
    (sequence : FinFourFullDebtCapBandResponseSequence source M)
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    quittingTerminalSemanticDebt source.point.1 sequence.mover / (4 * M) ≤
      quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward (sequence.sourceProfile rank)) 0
        (sequence.cutData rank).cut := by
  have hreach :=
    (sequence.cutData rank).sourceDebt_sub_epsilon_le_two_mul_jointReach
      (sequence.epsilon_pos rank) hreward
  have hsource := sequence.sourceMoverDebt_gt_three_quarters rank
  have hepsilon := sequence.epsilon_le_quarter rank
  have hscaled : quittingTerminalSemanticDebt source.point.1 sequence.mover / 2 ≤
      2 * M * quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward (sequence.sourceProfile rank)) 0
        (sequence.cutData rank).cut := by
    dsimp only [sourceProfile] at hreach ⊢
    linarith
  rw [div_le_iff₀ (by positivity : 0 < 4 * M)]
  nlinarith

end FinFourFullDebtCapBandResponseSequence

/-- A full-debt minimum-law source produces a literal cap-band response
sequence for the fixed player `0`.  The chronological tail is selected only
to make the limiting debt comparison pointwise; the later compactification
may refine it further. -/
theorem nonempty_finFourFullDebtCapBandResponseSequence
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hfullDebt : ∀ who, 0 < quittingTerminalSemanticDebt source.point.1 who)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourFullDebtCapBandResponseSequence source M) := by
  classical
  obtain ⟨profiles, _, _, _, hjoint, _, _, _, _⟩ := source.atom.chronology
  let mover : Fin 4 := 0
  let limitingDebt := quittingTerminalSemanticDebt source.point.1 mover
  have hlimitingDebt : 0 < limitingDebt := hfullDebt mover
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward (profiles rank)) atTop
      (nhds source.point.1) :=
    continuous_fst.continuousAt.tendsto.comp hjoint
  have hsourceDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles rank)) mover) atTop
      (nhds limitingDebt) := by
    exact (continuous_quittingTerminalSemanticDebt mover).tendsto
      source.point.1 |>.comp hpair
  have hthreeQuarter : 3 * limitingDebt / 4 < limitingDebt := by
    nlinarith
  have heventually : ∀ᶠ rank in atTop,
      3 * limitingDebt / 4 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles rank)) mover :=
    hsourceDebt.eventually_const_lt hthreeQuarter
  rw [eventually_atTop] at heventually
  obtain ⟨start, hstart⟩ := heventually
  let sourceIndex : ℕ → ℕ := fun rank ↦ start + rank
  have hsourceIndex : StrictMono sourceIndex := by
    intro first second hlt
    exact Nat.add_lt_add_left hlt start
  let epsilon : ℕ → ℝ := fun rank ↦
    (limitingDebt / 4) * (1 / ((rank : ℝ) + 1))
  have hepsilonPos : ∀ rank, 0 < epsilon rank := by
    intro rank
    dsimp only [epsilon]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    have hbase :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (limitingDebt / 4)
    simpa only [epsilon, mul_zero] using hbase
  have hepsilonQuarter : ∀ rank, epsilon rank ≤ limitingDebt / 4 := by
    intro rank
    have hrank : 0 ≤ (rank : ℝ) := Nat.cast_nonneg rank
    have hdenominator : 1 ≤ (rank : ℝ) + 1 := by linarith
    have hinverse : 1 / ((rank : ℝ) + 1) ≤ 1 := by
      exact (div_le_one (by positivity)).2 hdenominator
    exact mul_le_of_le_one_right (by positivity) hinverse
  have hsourceGt : ∀ rank,
      3 * limitingDebt / 4 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles (sourceIndex rank))) mover := by
    intro rank
    exact hstart (sourceIndex rank) (by
      dsimp only [sourceIndex]
      omega)
  have hband : ∀ rank, epsilon rank < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (profiles (sourceIndex rank))) mover := by
    intro rank
    have hepsilon := hepsilonQuarter rank
    have hsource := hsourceGt rank
    nlinarith
  have hexists : ∀ rank, Nonempty (QuittingCapBandFiniteCut reward
      (profiles (sourceIndex rank)) mover (epsilon rank)) := by
    intro rank
    exact exists_quittingCapBandFiniteCut reward (profiles (sourceIndex rank))
      mover (epsilon rank) M hM (hepsilonPos rank) hreward (hband rank)
  let cutData : ∀ rank, QuittingCapBandFiniteCut reward
      (profiles (sourceIndex rank)) mover (epsilon rank) :=
    fun rank ↦ Classical.choice (hexists rank)
  exact ⟨{
    chronologyProfiles := profiles
    sourceIndex := sourceIndex
    sourceIndex_strictMono := hsourceIndex
    mover := mover
    limitingMoverDebt_pos := hlimitingDebt
    epsilon := epsilon
    epsilon_pos := hepsilonPos
    epsilon_tendsto_zero := hepsilonZero
    epsilon_le_quarter := hepsilonQuarter
    source_tendsto := by
      exact hjoint.comp hsourceIndex.tendsto_atTop
    sourceMoverDebt_gt_three_quarters := hsourceGt
    cutData := cutData
  }⟩

/-- The compact joint target subsequence of a literal full-debt cap-band
response sequence.  Source chronology and every selected cut remain visible
through `response` and `refinement`. -/
structure FinFourFullDebtCapBandTargetCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (M : ℝ) where
  response : FinFourFullDebtCapBandResponseSequence source M
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  targetPoint : QuittingTerminalSemanticLawPoint (Fin 4)
  targetPoint_mem : targetPoint ∈ quittingTerminalSemanticLawCarrier reward
  target_tendsto : Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (response.targetProfile (refinement rank)),
        quittingTerminalOutcomeMass reward
          (response.targetProfile (refinement rank))))
    atTop (nhds targetPoint)
  targetMoverDebt_tendsto_zero : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (response.targetProfile (refinement rank))) response.mover)
    atTop (nhds 0)

namespace FinFourFullDebtCapBandTargetCompactification

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The target semantic coordinate belongs to the terminal-semantic carrier. -/
theorem targetSemantic_mem
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) :
    compactification.targetPoint.1 ∈ quittingTerminalSemanticCarrier reward :=
  terminalSemanticLawCarrier_fst_mem_carrier compactification.targetPoint
    compactification.targetPoint_mem

/-- The compact target cannot have total debt below the supplied global
minimum. -/
theorem sourceDebt_le_targetDebt
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) :
    quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum compactification.targetPoint.1 :=
  source.minimum compactification.targetPoint.1 compactification.targetSemantic_mem

/-- The mover's debt vanishes at the compact target point. -/
theorem targetMoverDebt_eq_zero
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) :
    quittingTerminalSemanticDebt compactification.targetPoint.1
        compactification.response.mover = 0 := by
  have hpair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (compactification.response.targetProfile
          (compactification.refinement rank))) atTop
      (nhds compactification.targetPoint.1) :=
    continuous_fst.continuousAt.tendsto.comp compactification.target_tendsto
  have hdebt :=
    (continuous_quittingTerminalSemanticDebt
      compactification.response.mover).tendsto
        compactification.targetPoint.1 |>.comp hpair
  exact tendsto_nhds_unique hdebt compactification.targetMoverDebt_tendsto_zero

/-- The selected source rows still converge to the original joint minimum
after target compactification. -/
theorem source_tendsto
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward
          (compactification.response.sourceProfile
            (compactification.refinement rank)),
        quittingTerminalOutcomeMass reward
          (compactification.response.sourceProfile
            (compactification.refinement rank)))) atTop (nhds source.point) := by
  exact compactification.response.source_tendsto.comp
    compactification.refinement_strictMono.tendsto_atTop

/-- The original chronological indices retained after both selections are
strictly increasing. -/
theorem ancestryIndex_strictMono
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) :
    StrictMono (compactification.response.sourceIndex ∘
      compactification.refinement) :=
  compactification.response.sourceIndex_strictMono.comp
    compactification.refinement_strictMono

/-- The response gain floor persists on the compactifying refinement. -/
theorem half_limitingMoverDebt_le_payoffGain
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    quittingTerminalSemanticDebt source.point.1
          compactification.response.mover / 2 ≤
      quittingTerminalPayoff reward
          (compactification.response.targetProfile
            (compactification.refinement rank))
          compactification.response.mover -
        quittingTerminalPayoff reward
          (compactification.response.sourceProfile
            (compactification.refinement rank))
          compactification.response.mover :=
  compactification.response.half_limitingMoverDebt_le_payoffGain
    hreward (compactification.refinement rank)

/-- The literal source joint-reach floor persists on the same refinement. -/
theorem limitingMoverDebt_div_four_mul_le_jointReach
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M)
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    quittingTerminalSemanticDebt source.point.1
          compactification.response.mover / (4 * M) ≤
      quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward
          (compactification.response.sourceProfile
            (compactification.refinement rank))) 0
        (compactification.response.cutData
          (compactification.refinement rank)).cut :=
  compactification.response.limitingMoverDebt_div_four_mul_le_jointReach
    hM hreward (compactification.refinement rank)

/-- The final source ancestry is the composite of the chronological tail and
the compactifying strict refinement. -/
theorem sourceProfile_eq_chronologyProfile
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) (rank : ℕ) :
    compactification.response.sourceProfile
        (compactification.refinement rank) =
      compactification.response.chronologyProfiles
        ((compactification.response.sourceIndex ∘
          compactification.refinement) rank) := rfl

/-- The final target remains the literal cap-band update at the same retained
chronological row and cut. -/
theorem targetProfile_eq_update
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) (rank : ℕ) :
    compactification.response.targetProfile
        (compactification.refinement rank) =
      Function.update
        (compactification.response.sourceProfile
          (compactification.refinement rank))
        compactification.response.mover
        (compactification.response.cutData
          (compactification.refinement rank)).targetStrategy := rfl

end FinFourFullDebtCapBandTargetCompactification

/-- Joint compactness selects an exact semantic/law target limit while the
mover-debt estimate passes to zero along the same strict refinement. -/
theorem nonempty_finFourFullDebtCapBandTargetCompactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (response : FinFourFullDebtCapBandResponseSequence source M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourFullDebtCapBandTargetCompactification source M) := by
  let targetJoint : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) :=
    fun rank ↦
      (quittingTerminalSemanticPair reward (response.targetProfile rank),
        quittingTerminalOutcomeMass reward (response.targetProfile rank))
  have htargetMem : ∀ rank,
      targetJoint rank ∈ quittingTerminalSemanticLawCarrier reward := by
    intro rank
    exact quittingTerminalSemanticLawPoint_mem_carrier reward
      (response.targetProfile rank)
  obtain ⟨targetPoint, htargetPoint, refinement, hrefinement, htarget⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq
      htargetMem
  have hdebtNonneg : ∀ rank, 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (response.targetProfile (refinement rank))) response.mover := by
    intro rank
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      (quittingTerminalSemanticPair_mem_carrier reward _)
      response.mover
  have hdebtUpper : ∀ rank, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (response.targetProfile (refinement rank))) response.mover ≤
      response.epsilon (refinement rank) := by
    intro rank
    exact response.targetMoverDebt_le_epsilon hreward (refinement rank)
  have hepsilonSubsequence : Tendsto
      (fun rank ↦ response.epsilon (refinement rank)) atTop (nhds 0) :=
    response.epsilon_tendsto_zero.comp hrefinement.tendsto_atTop
  have hdebtZero : Tendsto (fun rank ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (response.targetProfile (refinement rank))) response.mover) atTop
      (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall hdebtNonneg
    · exact Filter.Eventually.of_forall hdebtUpper
    · exact hepsilonSubsequence
  exact ⟨{
    response := response
    refinement := refinement
    refinement_strictMono := hrefinement
    targetPoint := targetPoint
    targetPoint_mem := htargetPoint
    target_tendsto := htarget
    targetMoverDebt_tendsto_zero := hdebtZero
  }⟩

/-- The only branch-specific datum at an exact-minimum compact target.  Its
global minimality and killed mover coordinate follow from the supplied source
and compactification. -/
structure FinFourFullDebtCapBandMinimumTarget
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) : Prop where
  targetDebtSum_eq_source :
    quittingTerminalSemanticDebtSum compactification.targetPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1

namespace FinFourFullDebtCapBandMinimumTarget

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {compactification :
    FinFourFullDebtCapBandTargetCompactification source M}

/-- Debt-sum equality with the source minimum makes the target globally
minimal. -/
theorem target_is_globalMinimum
    (minimumTarget :
      FinFourFullDebtCapBandMinimumTarget compactification) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum compactification.targetPoint.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [minimumTarget.targetDebtSum_eq_source]
  exact source.minimum candidate hcandidate

/-- The selected mover coordinate vanishes at every compact target,
independently of the minimum-fibre branch. -/
theorem targetMoverDebt_eq_zero
    (_minimumTarget :
      FinFourFullDebtCapBandMinimumTarget compactification) :
    quittingTerminalSemanticDebt compactification.targetPoint.1
      compactification.response.mover = 0 :=
  compactification.targetMoverDebt_eq_zero

end FinFourFullDebtCapBandMinimumTarget

/-- The exact compact-target split produced by cap-band redistribution. -/
inductive FinFourFullDebtCapBandTargetAlternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) : Type
  | offMinimum
      (eta : ℝ) (eta_pos : 0 < eta)
      (targetDebt_eq_minimum_add_two_mul :
        quittingTerminalSemanticDebtSum compactification.targetPoint.1 =
          quittingTerminalSemanticDebtSum source.point.1 + 2 * eta)
      (eventually_targetDebt_ge_minimum_add_eta : ∀ᶠ rank in atTop,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (compactification.response.targetProfile
                (compactification.refinement rank))) ≥
          quittingTerminalSemanticDebtSum source.point.1 + eta) :
      FinFourFullDebtCapBandTargetAlternative compactification
  | minimum
      (targetDebt_eq_minimum :
        quittingTerminalSemanticDebtSum compactification.targetPoint.1 =
          quittingTerminalSemanticDebtSum source.point.1) :
      FinFourFullDebtCapBandTargetAlternative compactification

namespace FinFourFullDebtCapBandTargetAlternative

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {compactification :
    FinFourFullDebtCapBandTargetCompactification source M}

/-- Named conversion from the literal exact-minimum alternative field to the
minimal input expected by fixed-weight chord compactification. -/
theorem minimumTarget_of_minimum
    (targetDebt_eq_minimum :
      quittingTerminalSemanticDebtSum compactification.targetPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1) :
    FinFourFullDebtCapBandMinimumTarget compactification :=
  ⟨targetDebt_eq_minimum⟩

end FinFourFullDebtCapBandTargetAlternative

namespace FinFourFullDebtCapBandTargetCompactification

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- Every compact target is either separated above the minimum by a fixed
positive margin or lies on the minimum fibre. -/
theorem nonempty_targetAlternative
    (compactification :
      FinFourFullDebtCapBandTargetCompactification source M) :
    Nonempty (FinFourFullDebtCapBandTargetAlternative compactification) := by
  have htargetDebt : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (compactification.response.targetProfile
            (compactification.refinement rank)))) atTop
      (nhds (quittingTerminalSemanticDebtSum
        compactification.targetPoint.1)) := by
    have hpair : Tendsto (fun rank ↦
        quittingTerminalSemanticPair reward
          (compactification.response.targetProfile
            (compactification.refinement rank))) atTop
        (nhds compactification.targetPoint.1) :=
      continuous_fst.continuousAt.tendsto.comp compactification.target_tendsto
    exact continuous_quittingTerminalSemanticDebtSum.tendsto
      compactification.targetPoint.1 |>.comp hpair
  rcases lt_or_eq_of_le compactification.sourceDebt_le_targetDebt with
      hstrict | hequal
  · let eta := (quittingTerminalSemanticDebtSum
        compactification.targetPoint.1 -
          quittingTerminalSemanticDebtSum source.point.1) / 2
    have heta : 0 < eta := by
      dsimp only [eta]
      linarith
    have hidentity : quittingTerminalSemanticDebtSum
        compactification.targetPoint.1 =
          quittingTerminalSemanticDebtSum source.point.1 + 2 * eta := by
      dsimp only [eta]
      ring
    have hthreshold : quittingTerminalSemanticDebtSum source.point.1 + eta <
        quittingTerminalSemanticDebtSum compactification.targetPoint.1 := by
      rw [hidentity]
      linarith
    exact ⟨.offMinimum eta heta hidentity
      ((htargetDebt.eventually_const_lt hthreshold).mono fun _ h ↦ h.le)⟩
  · exact ⟨.minimum hequal.symm⟩

end FinFourFullDebtCapBandTargetCompactification

/-- A supplied full-debt minimum-atom producer yields one exact compact target
alternative.  This theorem selects only actual chronological profiles and
literal cap-band responses; downstream consumers remain separate. -/
theorem nonempty_finFourFullDebtCapBandTargetCompactification_and_alternative
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hfullDebt : ∀ who, 0 < quittingTerminalSemanticDebt source.point.1 who)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (Σ compactification :
        FinFourFullDebtCapBandTargetCompactification source M,
      FinFourFullDebtCapBandTargetAlternative compactification) := by
  obtain ⟨response⟩ := nonempty_finFourFullDebtCapBandResponseSequence
    source hfullDebt M hM hreward
  obtain ⟨compactification⟩ :=
    nonempty_finFourFullDebtCapBandTargetCompactification response hreward
  obtain ⟨alternative⟩ := compactification.nonempty_targetAlternative
  exact ⟨⟨compactification, alternative⟩⟩

end GameTheory
