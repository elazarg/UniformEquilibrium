import Research.Quitting.FinFourProducerAtlas.PositiveNeverQuantileTwoRelease
import Research.Quitting.FinFourProducerAtlas.Source
import UniformEquilibrium.Diagnostics.Quitting.AllContinuePrefixSemantics
import UniformEquilibrium.Diagnostics.Quitting.SilentPaddingTwoCutSource
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ArbitraryClockMinimumActualReachPaidPort

/-!
# Supplied escape product: off-minimum exit or exact minimum restart

This module classifies one supplied independent product descendant of a Fin4
minimum source.  Strictly larger debt enters the actual-reach paid-port waist.
Equality regenerates the exact product semantic/law point as a source with the
same hard residual and exposes the positive-Never two-release compiler.

The structure does not construct the product descendant or its replacement
ancestry.  Those are the missing reset-rigid escape-origin adapter.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

/-- Literal supplied data at the reset-rigid product escape origin. -/
structure FinFourEscapeProductRestart
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  originalProfiles : ℕ → (quittingGame reward).BehaviorProfile
  sourceIndex : ℕ
  productLaws : Fin 4 → PMF (Option ℕ)
  productProfile : (quittingGame reward).BehaviorProfile
  productProfile_eq :
    productProfile = quittingStoppingLawProfile reward productLaws
  ancestry : IsQuittingBehaviorReplacementAncestry
    (originalProfiles sourceIndex) productProfile
  neverProduct_pos : 0 < ∏ who, (productLaws who none).toReal
  owner : Fin 4
  outsider : Fin 4
  outsider_ne_owner : outsider ≠ owner
  ownerSingletonGain : ℝ
  ownerSingletonGain_pos : 0 < ownerSingletonGain
  ownerSingletonGain_le_reward :
    ownerSingletonGain ≤ reward (quittingSingletonTerminal owner) owner
  outsiderPairGain : ℝ
  outsiderPairGain_pos : 0 < outsiderPairGain
  outsiderPairGain_le_rewardGap :
    outsiderPairGain ≤
      reward ⟨{owner, outsider}, by simp⟩ outsider -
        reward (quittingSingletonTerminal owner) outsider

namespace FinFourEscapeProductRestart

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The exact joint semantic/law point of the supplied product profile. -/
def productPoint (data : FinFourEscapeProductRestart source) :
    QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPair reward data.productProfile,
    quittingTerminalOutcomeMass reward data.productProfile)

theorem productPoint_mem (data : FinFourEscapeProductRestart source) :
    data.productPoint ∈ quittingTerminalSemanticLawCarrier reward :=
  quittingTerminalSemanticLawPoint_mem_carrier reward data.productProfile

theorem productSemanticPair_mem (data : FinFourEscapeProductRestart source) :
    data.productPoint.1 ∈ quittingTerminalSemanticCarrier reward :=
  quittingTerminalSemanticPair_mem_carrier reward data.productProfile

/-- The supplied product cannot lie below the selected global minimum. -/
theorem sourceDebt_le_productDebt (data : FinFourEscapeProductRestart source) :
    quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalDebtSum reward data.productProfile := by
  rw [quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
  exact source.minimum _ (quittingTerminalSemanticPair_mem_carrier reward data.productProfile)

/-- Re-express the positive Never product using the product profile's exact
canonical stopping laws. -/
theorem productProfile_neverProduct_pos
    (data : FinFourEscapeProductRestart source) :
    0 < ∏ who,
      (quittingBehaviorStoppingLaw reward (data.productProfile who) none).toReal := by
  rw [data.productProfile_eq]
  simpa using data.neverProduct_pos

/-- The positive-Never release compiler attached to an exact minimum product. -/
def minimumReleaseInput
    (data : FinFourEscapeProductRestart source)
    (hminimum : quittingTerminalDebtSum reward data.productProfile =
      quittingTerminalSemanticDebtSum source.point.1) :
    FinFourPositiveNeverReleaseInput reward where
  profile := data.productProfile
  owner := data.owner
  outsider := data.outsider
  outsider_ne_owner := data.outsider_ne_owner
  neverProduct_pos := data.productProfile_neverProduct_pos
  ownerSingletonGain := data.ownerSingletonGain
  ownerSingletonGain_pos := data.ownerSingletonGain_pos
  ownerSingletonGain_le_reward := data.ownerSingletonGain_le_reward
  outsiderPairGain := data.outsiderPairGain
  outsiderPairGain_pos := data.outsiderPairGain_pos
  outsiderPairGain_le_rewardGap := data.outsiderPairGain_le_rewardGap
  minimum := by
    intro candidate hcandidate
    rw [show quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward data.productProfile) =
          quittingTerminalSemanticDebtSum source.point.1 by
      simpa only [quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using hminimum]
    exact source.minimum candidate hcandidate
  debt_eq_inf := by
    have heq : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward data.productProfile) =
        quittingTerminalSemanticDebtSum source.point.1 := by
      simpa only [quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using hminimum
    exact heq.trans source.debt_eq_inf
  debtInf_pos := source.inf_pos

/-- The exact equality arm, retaining the finite atom used for same-point
source regeneration. -/
structure MinimumRestart (data : FinFourEscapeProductRestart source) where
  debt_eq : quittingTerminalDebtSum reward data.productProfile =
    quittingTerminalSemanticDebtSum source.point.1
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  terminalMass_pos : 0 < data.productPoint.2 (some terminal)

namespace MinimumRestart

variable {data : FinFourEscapeProductRestart source}

/-- Equality with the positive global minimum forces the supplied product
cap to dominate every singleton reward. -/
theorem singletonReward_le_productCap
    (restart : MinimumRestart data) (who : Fin 4) :
    reward (quittingSingletonTerminal who) who ≤
      quittingContinuationBestResponseValue reward data.productProfile who := by
  have hdebt : quittingTerminalSemanticDebtSum data.productPoint.1 =
      quittingTerminalSemanticDebtSum source.point.1 := by
    simpa only [productPoint, quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
      using restart.debt_eq
  have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum data.productPoint.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [hdebt]
    exact source.minimum candidate hcandidate
  have hpositive : 0 < quittingTerminalSemanticDebtSum data.productPoint.1 := by
    rw [hdebt]
    exact source.minimumDebt_pos
  have hmargin := minimumTerminalSemantic_singletonMargin
    data.productPoint.1 data.productSemanticPair_mem hminimum hpositive who
  change reward (quittingSingletonTerminal who) who ≤
    data.productPoint.1.2 who
  linarith

/-- The literal all-Continue word of a prescribed finite depth. -/
def allContinueRoots
    (_restart : MinimumRestart data) (depth : ℕ) :
    List (Fin 4 → PMF Bool) :=
  List.replicate depth quittingAllContinueRoot

/-- The supplied product profile behind a literal all-Continue word. -/
def allContinueProfile
    (restart : MinimumRestart data) (depth : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (restart.allContinueRoots depth)
    data.productProfile

@[simp]
theorem allContinueRoots_length
    (restart : MinimumRestart data) (depth : ℕ) :
    (restart.allContinueRoots depth).length = depth := by
  simp [allContinueRoots]

/-- Every displayed root is literally deterministic all Continue. -/
theorem allContinueRoots_eq
    (restart : MinimumRestart data) (depth : ℕ) (root : Fin 4 → PMF Bool)
    (hroot : root ∈ restart.allContinueRoots depth) :
    root = quittingAllContinueRoot := by
  have h : depth ≠ 0 ∧ root = quittingAllContinueRoot := by
    simpa only [allContinueRoots, List.mem_replicate] using hroot
  exact h.2

/-- The literal word presentation is the canonical iterated all-Continue
prefix of the supplied product suffix. -/
theorem allContinueProfile_eq_iterate
    (restart : MinimumRestart data) (depth : ℕ) :
    restart.allContinueProfile depth =
      quittingAllContinuePrefixIterate reward data.productProfile depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [allContinueProfile, allContinueRoots, List.replicate_succ,
        quittingLiteralRootStackProfile_cons,
        quittingAllContinuePrefixIterate]
      exact congrArg
        (quittingRootThenContinuationProfile reward quittingAllContinueRoot) ih

/-- Every literal all-Continue word keeps the supplied product semantic pair. -/
theorem allContinueProfile_semanticPair_eq
    (restart : MinimumRestart data) (depth : ℕ) :
    quittingTerminalSemanticPair reward (restart.allContinueProfile depth) =
      quittingTerminalSemanticPair reward data.productProfile := by
  rw [restart.allContinueProfile_eq_iterate]
  exact quittingTerminalSemanticPair_allContinuePrefixIterate_eq
    reward data.productProfile restart.singletonReward_le_productCap depth

/-- Every literal all-Continue word keeps the complete supplied product law. -/
theorem allContinueProfile_terminalOutcomeMass_eq
    (restart : MinimumRestart data) (depth : ℕ) :
    quittingTerminalOutcomeMass reward (restart.allContinueProfile depth) =
      quittingTerminalOutcomeMass reward data.productProfile := by
  rw [restart.allContinueProfile_eq_iterate]
  exact quittingTerminalOutcomeMass_allContinuePrefix_eq
    reward data.productProfile depth

/-- The literal all-Continue word keeps the exact joint product point. -/
theorem allContinueProfile_point_eq
    (restart : MinimumRestart data) (depth : ℕ) :
    (quittingTerminalSemanticPair reward (restart.allContinueProfile depth),
      quittingTerminalOutcomeMass reward (restart.allContinueProfile depth)) =
        data.productPoint := by
  apply Prod.ext
  · exact restart.allContinueProfile_semanticPair_eq depth
  · exact restart.allContinueProfile_terminalOutcomeMass_eq depth

/-- Every literal all-Continue word is an exact cap--Nash stack against the
constant supplied product suffix. -/
theorem allContinueRoots_capNash
    (restart : MinimumRestart data) (depth : ℕ) :
    IsQuittingCapNashRootStack reward (restart.allContinueRoots depth)
      data.productProfile := by
  induction depth with
  | zero => exact isQuittingCapNashRootStack_nil reward data.productProfile
  | succ depth ih =>
      rw [show restart.allContinueRoots (depth + 1) =
          quittingAllContinueRoot :: restart.allContinueRoots depth by
        exact List.replicate_succ]
      rw [isQuittingCapNashRootStack_cons_iff]
      constructor
      · apply quittingAllContinueRoot_isZeroNash_of_singleton_le
        intro who
        have hcoordinate : quittingContinuationBestResponseValue reward
              (restart.allContinueProfile depth) who =
            quittingContinuationBestResponseValue reward data.productProfile who :=
          congrArg
          (fun pair : QuittingTerminalSemanticPair (Fin 4) => pair.2 who)
          (restart.allContinueProfile_semanticPair_eq depth)
        change reward (quittingSingletonTerminal who) who ≤
          quittingContinuationBestResponseValue reward
            (restart.allContinueProfile depth) who
        rw [hcoordinate]
        exact restart.singletonReward_le_productCap who
      · exact ih

/-- Joint survival through every displayed all-Continue word is exactly one. -/
theorem allContinueRoots_survival_eq_one
    (restart : MinimumRestart data) (depth : ℕ) :
    quittingCapNashStackContinueProduct (restart.allContinueRoots depth) = 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [allContinueRoots, List.replicate_succ,
        quittingCapNashStackContinueProduct_cons,
        quittingStationaryContinueMass_allContinueRoot, one_mul]
      exact ih

/-- Shifting past the whole all-Continue word returns definitionally to the
supplied product suffix. -/
theorem allContinueProfile_suffix_eq
    (restart : MinimumRestart data) (depth : ℕ) :
    quittingAllContinueProfileSpine reward (restart.allContinueProfile depth)
        (restart.allContinueRoots depth).length = data.productProfile := by
  exact quittingAllContinueProfileSpine_literalRootStackProfile_length
    reward (restart.allContinueRoots depth) data.productProfile

/-- One fixed finite product-suffix window captures more than half of the
selected atom and contains a literal positive row of that atom. -/
theorem exists_productCausalWindow (restart : MinimumRestart data) :
    ∃ cutoff : ℕ,
      data.productPoint.2 (some restart.terminal) / 2 <
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward data.productProfile time
              restart.terminal ∧
        ∃ mark < cutoff,
          0 < quittingStageCoalitionMass reward data.productProfile mark
            restart.terminal := by
  have hlaw : data.productPoint.2 (some restart.terminal) / 2 <
      quittingAbsorbedMassLimit reward data.productProfile restart.terminal := by
    change data.productPoint.2 (some restart.terminal) / 2 <
      data.productPoint.2 (some restart.terminal)
    linarith [restart.terminalMass_pos]
  obtain ⟨cutoff, _hcutoffPos, hwindow⟩ :=
    exists_positive_finite_stageCoalitionMass_window_gt
      reward data.productProfile restart.terminal hlaw
  have hsum : 0 < ∑ mark ∈ Finset.range cutoff,
      quittingStageCoalitionMass reward data.productProfile mark
        restart.terminal := by
    linarith [restart.terminalMass_pos]
  have hnonneg : ∀ mark ∈ Finset.range cutoff,
      0 ≤ quittingStageCoalitionMass reward data.productProfile mark
        restart.terminal := by
    intro mark _
    exact quittingStageCoalitionMass_nonneg reward _ _ _
  obtain ⟨mark, hmark, hmarkPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsum
  exact ⟨cutoff, hwindow, mark, Finset.mem_range.mp hmark, hmarkPos⟩

/-- The fixed product-suffix cutoff used by the regenerated chronology. -/
def productCutoff (restart : MinimumRestart data) : ℕ :=
  Classical.choose restart.exists_productCausalWindow

theorem productWindow_mass_gt_half (restart : MinimumRestart data) :
    data.productPoint.2 (some restart.terminal) / 2 <
      ∑ time ∈ Finset.range restart.productCutoff,
        quittingStageCoalitionMass reward data.productProfile time
          restart.terminal :=
  (Classical.choose_spec restart.exists_productCausalWindow).1

/-- A fixed actual date carrying the regenerated product atom. -/
def productMark (restart : MinimumRestart data) : ℕ :=
  Classical.choose (Classical.choose_spec restart.exists_productCausalWindow).2

theorem productMark_lt_productCutoff (restart : MinimumRestart data) :
    restart.productMark < restart.productCutoff :=
  (Classical.choose_spec
    (Classical.choose_spec restart.exists_productCausalWindow).2).1

theorem productMark_stageMass_pos (restart : MinimumRestart data) :
    0 < quittingStageCoalitionMass reward data.productProfile restart.productMark
      restart.terminal :=
  (Classical.choose_spec
    (Classical.choose_spec restart.exists_productCausalWindow).2).2

/-- The same positive atom occurs after the full all-Continue word with its
original mass. -/
theorem shiftedProductMark_stageMass_eq
    (restart : MinimumRestart data) (depth : ℕ) :
    quittingStageCoalitionMass reward (restart.allContinueProfile depth)
        ((restart.allContinueRoots depth).length + restart.productMark)
        restart.terminal =
      quittingStageCoalitionMass reward data.productProfile restart.productMark
        restart.terminal := by
  rw [allContinueProfile,
    quittingStageCoalitionMass_literalRootStack_add_length,
    restart.allContinueRoots_survival_eq_one, one_mul]

/-- The regenerated source uses the literal constant product suffix and an
all-Continue word of length `n + 1` as its internal atom chronology. -/
def sourceAtProduct (restart : MinimumRestart data) :
    FinFourMinimumAtomProducer reward bound := by
  let atom : QuittingMinimumLawCausalSuffixAtom reward data.productPoint := {
    terminal := restart.terminal
    terminalMass_pos := restart.terminalMass_pos
    chronology := by
      refine ⟨fun _ => data.productProfile, fun _ => restart.productCutoff,
        fun _ => restart.productMark,
        fun n => restart.allContinueRoots (n + 1), ?_, ?_, ?_, ?_, ?_⟩
      · exact tendsto_const_nhds
      · intro n
        exact restart.allContinueRoots_length (n + 1)
      · intro n
        exact restart.allContinueRoots_capNash (n + 1)
      · have heq : ∀ n,
            quittingTerminalDebtSum reward
                (quittingLiteralRootStackProfile reward
                  (restart.allContinueRoots (n + 1)) data.productProfile) =
              quittingTerminalDebtSumInf reward := by
          intro n
          have hproductDebt : quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward data.productProfile) =
              quittingTerminalSemanticDebtSum source.point.1 := by
            simpa only [productPoint,
              quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using
                restart.debt_eq
          rw [show quittingLiteralRootStackProfile reward
              (restart.allContinueRoots (n + 1)) data.productProfile =
                restart.allContinueProfile (n + 1) by rfl,
            quittingTerminalDebtSum_eq_terminalSemanticDebtSum,
            restart.allContinueProfile_semanticPair_eq,
            hproductDebt,
            source.debt_eq_inf]
        exact (tendsto_congr' (Eventually.of_forall heq)).2 tendsto_const_nhds
      · exact Eventually.of_forall fun n => by
          refine ⟨restart.productWindow_mass_gt_half,
            restart.productMark_lt_productCutoff,
            restart.productMark_stageMass_pos, ?_⟩
          rw [show n + 1 + restart.productMark =
              (restart.allContinueRoots (n + 1)).length +
                restart.productMark by
            rw [restart.allContinueRoots_length]]
          change 0 < quittingStageCoalitionMass reward
            (restart.allContinueProfile (n + 1))
            ((restart.allContinueRoots (n + 1)).length + restart.productMark)
              restart.terminal
          rw [restart.shiftedProductMark_stageMass_eq]
          exact restart.productMark_stageMass_pos
  }
  exact {
    residual := source.residual
    point := data.productPoint
    point_mem := data.productPoint_mem
    semantic_mem := data.productSemanticPair_mem
    minimum := by
      intro candidate hcandidate
      rw [show quittingTerminalSemanticDebtSum data.productPoint.1 =
          quittingTerminalSemanticDebtSum source.point.1 by
        simpa only [productPoint,
          quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using
            restart.debt_eq]
      exact source.minimum candidate hcandidate
    inf_pos := source.inf_pos
    debt_eq_inf := by
      calc
        quittingTerminalSemanticDebtSum data.productPoint.1 =
            quittingTerminalSemanticDebtSum source.point.1 := by
          simpa only [productPoint,
            quittingTerminalDebtSum_eq_terminalSemanticDebtSum] using
              restart.debt_eq
        _ = quittingTerminalDebtSumInf reward := source.debt_eq_inf
    atom := atom
  }

@[simp]
theorem sourceAtProduct_point_eq (restart : MinimumRestart data) :
    restart.sourceAtProduct.point = data.productPoint := rfl

@[simp]
theorem sourceAtProduct_residual_eq (restart : MinimumRestart data) :
    restart.sourceAtProduct.residual = source.residual := rfl

/-- The exact positive-Never release compiler attached to this restart. -/
def releaseInput (restart : MinimumRestart data) :
    FinFourPositiveNeverReleaseInput reward :=
  data.minimumReleaseInput restart.debt_eq

end MinimumRestart

/-- The supplied product descendant either exits strictly above the minimum
through an actual paid row, or is regenerated at its exact product law point
and carries the complete positive-Never two-release sequence. -/
theorem offMinimumPaidPort_or_minimumRestart
    (data : FinFourEscapeProductRestart source)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    (∃ port : QuittingOffMinimumActualReachPaidPort reward
          data.originalProfiles (quittingTerminalSemanticDebtSum source.point.1) M,
        port.sourceIndex = data.sourceIndex ∧
          port.target = data.productProfile) ∨
      Nonempty (MinimumRestart data) := by
  have hle := data.sourceDebt_le_productDebt
  rcases hle.lt_or_eq with hstrict | heq
  · left
    exact replacementAncestry_exists_offMinimumActualReachPaidPort
      reward data.originalProfiles
      (quittingTerminalSemanticDebtSum source.point.1) M source.minimumDebt_pos
      hreward data.sourceIndex data.productProfile data.ancestry hstrict
  · right
    have hminimum : quittingTerminalDebtSum reward data.productProfile =
        quittingTerminalSemanticDebtSum source.point.1 := heq.symm
    obtain ⟨terminal, hmass⟩ :=
      exists_positive_finiteLawAtom_of_finFourHardResidual_minimum
        reward bound source.residual data.productPoint data.productPoint_mem
          (data.minimumReleaseInput hminimum).minimum
    exact ⟨{
      debt_eq := hminimum,
      terminal := terminal,
      terminalMass_pos := hmass
    }⟩

end FinFourEscapeProductRestart

end GameTheory
