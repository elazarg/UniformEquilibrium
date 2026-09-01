import Research.Quitting.FinFourProducerAtlas.EscapeProductRestart
import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairSupportDescentAlternative

/-!
# Supplied reset-rigid escape support contraction

This module compactifies the literal singleton releases generated from an
accepted positive-Never product restart.  A strict singleton limit exits
through an actual-reach paid port.  An exact minimum limit is regenerated
with the incoming residual and supplies the nonempty-host moving-mark
compiler.  The escape product itself remains supplied data.

These are horizontal response profiles, not a temporal Nash chronology.  No
escape-origin producer, terminal exit consumer, or uniform equilibrium is
constructed here.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- One jointly convergent refinement of the literal singleton-release
profiles. -/
structure FinFourPositiveNeverSingletonCompactification
    (input : FinFourPositiveNeverReleaseInput reward) where
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  select : ℕ → ℕ
  select_strictMono : StrictMono select
  profiles_tendsto : Tendsto (fun rank =>
      (quittingTerminalSemanticPair reward (input.singletonProfile (select rank)),
        quittingTerminalOutcomeMass reward (input.singletonProfile (select rank))))
    atTop (nhds point)

namespace FinFourPositiveNeverSingletonCompactification

variable {input : FinFourPositiveNeverReleaseInput reward}

/-- Compactness of the exact semantic/law carrier selects a common strict
refinement of the singleton releases. -/
theorem nonempty (input : FinFourPositiveNeverReleaseInput reward) :
    Nonempty (FinFourPositiveNeverSingletonCompactification input) := by
  let points : ℕ → QuittingTerminalSemanticLawPoint (Fin 4) := fun rank =>
    (quittingTerminalSemanticPair reward (input.singletonProfile rank),
      quittingTerminalOutcomeMass reward (input.singletonProfile rank))
  have hmem : ∀ rank, points rank ∈ quittingTerminalSemanticLawCarrier reward :=
    fun rank => quittingTerminalSemanticLawPoint_mem_carrier reward _
  obtain ⟨point, hpoint, select, hselect, hlimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  exact ⟨{
    point := point
    point_mem := hpoint
    select := select
    select_strictMono := hselect
    profiles_tendsto := by
      change Tendsto (points ∘ select) atTop (nhds point)
      exact hlimit
  }⟩

/-- The compact singleton limit cannot lie below the global minimum. -/
theorem debtInf_le_pointDebt
    (compact : FinFourPositiveNeverSingletonCompactification input) :
    quittingTerminalDebtSumInf reward ≤
      quittingTerminalSemanticDebtSum compact.point.1 := by
  rw [← input.debt_eq_inf,
    quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
  exact input.minimum compact.point.1
    (terminalSemanticLawCarrier_fst_mem_carrier compact.point compact.point_mem)

/-- Total debt of the selected singleton profiles converges to the compact
limit's total debt. -/
theorem debt_tendsto
    (compact : FinFourPositiveNeverSingletonCompactification input) :
    Tendsto (fun rank => quittingTerminalDebtSum reward
        (input.singletonProfile (compact.select rank))) atTop
      (nhds (quittingTerminalSemanticDebtSum compact.point.1)) := by
  have hpair := continuous_fst.tendsto compact.point |>.comp compact.profiles_tendsto
  have hdebt := continuous_quittingTerminalSemanticDebtSum.tendsto compact.point.1
    |>.comp hpair
  simpa only [quittingTerminalDebtSum_eq_terminalSemanticDebtSum,
    Function.comp_def] using hdebt

/-- The selected fresh-row reaches still converge to the original positive
joint Never mass. -/
theorem reach_tendsto
    (compact : FinFourPositiveNeverSingletonCompactification input) :
    Tendsto (fun rank => input.reach (compact.select rank)) atTop
      (nhds input.neverProduct) :=
  input.reach_tendsto_neverProduct.comp compact.select_strictMono.tendsto_atTop

/-- The singleton terminal coordinate of the compact limit retains at least
the full joint Never mass. -/
theorem neverProduct_le_singletonMass
    (compact : FinFourPositiveNeverSingletonCompactification input) :
    input.neverProduct ≤
      compact.point.2 (some (quittingSingletonTerminal input.owner)) := by
  have hlaw : Tendsto (fun rank =>
      quittingTerminalOutcomeMass reward
          (input.singletonProfile (compact.select rank))
          (some (quittingSingletonTerminal input.owner))) atTop
      (nhds (compact.point.2 (some (quittingSingletonTerminal input.owner)))) :=
    ((continuous_apply (some (quittingSingletonTerminal input.owner))).comp
      continuous_snd).tendsto compact.point |>.comp compact.profiles_tendsto
  apply le_of_tendsto_of_tendsto' compact.reach_tendsto hlaw
  intro rank
  rw [← input.singletonStageMass_eq_reach (compact.select rank)]
  exact quittingStageCoalitionMass_le_terminalOutcomeMass reward _ _ _

/-- The singleton terminal coordinate of the compact limit is positive. -/
theorem singletonMass_pos
    (compact : FinFourPositiveNeverSingletonCompactification input) :
    0 < compact.point.2 (some (quittingSingletonTerminal input.owner)) :=
  input.neverProduct_pos.trans_le compact.neverProduct_le_singletonMass

end FinFourPositiveNeverSingletonCompactification

/-- Literal off-minimum output selected from a compact singleton-release
limit with strictly larger total debt. -/
structure FinFourPositiveNeverSingletonOffMinimumExit
    (input : FinFourPositiveNeverReleaseInput reward)
    (compact : FinFourPositiveNeverSingletonCompactification input)
    (M : ℝ) where
  rank : ℕ
  debt_gt : quittingTerminalDebtSumInf reward <
    quittingTerminalDebtSum reward (input.singletonProfile (compact.select rank))
  paidPort : QuittingOffMinimumActualReachPaidPort reward input.sourceProfile
    (quittingTerminalDebtSumInf reward) M
  paidPort_sourceIndex : paidPort.sourceIndex = compact.select rank
  paidPort_target : paidPort.target = input.singletonProfile (compact.select rank)

/-- Exact-minimum singleton limit regenerated with the incoming hard residual
and equipped with the shifted nonempty-host moving-mark family. -/
structure FinFourPositiveNeverSingletonMinimumRestart
    (source : FinFourMinimumAtomProducer reward bound)
    (input : FinFourPositiveNeverReleaseInput reward)
    (compact : FinFourPositiveNeverSingletonCompactification input) where
  pointDebt_eq_inf : quittingTerminalSemanticDebtSum compact.point.1 =
    quittingTerminalDebtSumInf reward
  start : ℕ
  reachFloor_le : ∀ rank, input.neverProduct / 4 ≤
    input.reach (compact.select (start + rank))

namespace FinFourPositiveNeverSingletonMinimumRestart

variable
  {input : FinFourPositiveNeverReleaseInput reward}
  {compact : FinFourPositiveNeverSingletonCompactification input}

/-- The cofinal index used by the regenerated moving family. -/
def selectedIndex
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact)
    (rank : ℕ) : ℕ :=
  compact.select (restart.start + rank)

theorem selectedIndex_strictMono
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    StrictMono restart.selectedIndex := by
  apply compact.select_strictMono.comp
  intro first second hlt
  exact Nat.add_lt_add_left hlt restart.start

/-- The complete same-residual source at the compact singleton minimum. -/
def sourceAtSingleton
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    FinFourMinimumAtomProducer reward bound :=
  source.regeneratedAtLawPoint compact.point
    (quittingSingletonTerminal input.owner) compact.point_mem
    (restart.pointDebt_eq_inf.trans source.debt_eq_inf.symm)
    compact.singletonMass_pos

@[simp]
theorem sourceAtSingleton_point_eq
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    restart.sourceAtSingleton.point = compact.point := rfl

@[simp]
theorem sourceAtSingleton_residual_eq
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    restart.sourceAtSingleton.residual = source.residual := rfl

/-- The selected singleton profiles converge to the regenerated source point. -/
theorem selectedSingleton_tendsto
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    Tendsto (fun rank =>
        (quittingTerminalSemanticPair reward
            (input.singletonProfile (restart.selectedIndex rank)),
          quittingTerminalOutcomeMass reward
            (input.singletonProfile (restart.selectedIndex rank))))
      atTop (nhds restart.sourceAtSingleton.point) := by
  change Tendsto (fun rank =>
      (quittingTerminalSemanticPair reward
          (input.singletonProfile (restart.selectedIndex rank)),
        quittingTerminalOutcomeMass reward
          (input.singletonProfile (restart.selectedIndex rank))))
    atTop (nhds compact.point)
  have hshift : StrictMono (fun rank => restart.start + rank) := by
    intro first second hlt
    exact Nat.add_lt_add_left hlt restart.start
  simpa only [selectedIndex, Function.comp_def] using
    compact.profiles_tendsto.comp hshift.tendsto_atTop

/-- The fixed singleton-host labels for the second release. -/
def labels
    (_restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    FinFourMovingMarkedPairLabels where
  pair := {input.owner}
  pair_nonempty := Finset.singleton_nonempty input.owner
  mover := input.outsider
  mover_not_mem := by simp [input.outsider_ne_owner]

/-- The literal singleton-to-pair release family at the same selected rows. -/
def moving
    (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact) :
    FinFourMovingMarkedPairMinimumSource restart.sourceAtSingleton where
  labels := restart.labels
  marked := fun rank => input.movingMark (restart.selectedIndex rank)
  purePair := fun rank => input.movingMarkPureHost (restart.selectedIndex rank)
  marked_mover_eq := fun _ => rfl
  marked_selectedAction_eq_true := fun _ => rfl
  purePair_coalition_eq := fun _ => rfl
  localGap_eq_rewardGap := fun rank => by
    simpa only [labels, FinFourMovingMarkedPairLabels.rewardGap,
      FinFourMovingMarkedPairLabels.sourceTerminal,
      FinFourMovingMarkedPairLabels.targetTerminal, Finset.pair_comm,
      quittingSingletonTerminal] using
        input.movingMark_localEndpointGap_eq (restart.selectedIndex rank)
  rewardGap_pos := by
    simpa only [labels, FinFourMovingMarkedPairLabels.rewardGap,
      FinFourMovingMarkedPairLabels.sourceTerminal,
      FinFourMovingMarkedPairLabels.targetTerminal, Finset.pair_comm,
      quittingSingletonTerminal] using
        input.outsiderPairGain_pos.trans_le input.outsiderPairGain_le_rewardGap
  reachFloor := input.neverProduct / 4
  reachFloor_pos := div_pos input.neverProduct_pos (by norm_num)
  reachFloor_le := fun rank => by
    change input.neverProduct / 4 ≤ quittingLiveMass reward
      (input.singletonProfile (restart.selectedIndex rank))
        (input.stage (restart.selectedIndex rank))
    rw [input.singletonLiveMass_at_stage_eq_reach]
    exact restart.reachFloor_le rank
  source_tendsto := restart.selectedSingleton_tendsto

end FinFourPositiveNeverSingletonMinimumRestart

/-- Compact singleton releases either leave the minimum fibre or regenerate
a complete moving-mark minimum source. -/
inductive FinFourPositiveNeverSingletonAlternative
    (source : FinFourMinimumAtomProducer reward bound)
    (input : FinFourPositiveNeverReleaseInput reward) (M : ℝ) : Type
  | offMinimum
      (compact : FinFourPositiveNeverSingletonCompactification input)
      (exit : FinFourPositiveNeverSingletonOffMinimumExit input compact M)
  | minimum
      (compact : FinFourPositiveNeverSingletonCompactification input)
      (restart : FinFourPositiveNeverSingletonMinimumRestart source input compact)

/-- Exhaustive compact-target split for the singleton release sequence. -/
theorem nonempty_finFourPositiveNeverSingletonAlternative
    (source : FinFourMinimumAtomProducer reward bound)
    (input : FinFourPositiveNeverReleaseInput reward)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourPositiveNeverSingletonAlternative source input M) := by
  obtain ⟨compact⟩ := FinFourPositiveNeverSingletonCompactification.nonempty input
  rcases compact.debtInf_le_pointDebt.lt_or_eq with hstrict | heq
  · have hevent : ∀ᶠ rank in atTop,
        quittingTerminalDebtSumInf reward <
          quittingTerminalDebtSum reward
            (input.singletonProfile (compact.select rank)) :=
      (tendsto_order.1 compact.debt_tendsto).1 _ hstrict
    rw [eventually_atTop] at hevent
    obtain ⟨rank, hrank⟩ := hevent
    let selected := rank
    obtain ⟨port, hsourceIndex, htarget⟩ :=
      replacementAncestry_exists_offMinimumActualReachPaidPort
        reward input.sourceProfile (quittingTerminalDebtSumInf reward) M
          input.debtInf_pos hreward (compact.select selected)
            (input.singletonProfile (compact.select selected))
              (input.source_to_singleton_ancestry (compact.select selected))
                (hrank selected le_rfl)
    exact ⟨.offMinimum compact {
      rank := selected
      debt_gt := hrank selected le_rfl
      paidPort := port
      paidPort_sourceIndex := hsourceIndex
      paidPort_target := htarget
    }⟩
  · have hevent : ∀ᶠ rank in atTop,
        input.neverProduct / 4 ≤ input.reach (compact.select rank) :=
      compact.select_strictMono.tendsto_atTop.eventually
        input.eventually_neverProduct_div_four_le_reach
    rw [eventually_atTop] at hevent
    obtain ⟨start, hstart⟩ := hevent
    exact ⟨.minimum compact {
      pointDebt_eq_inf := heq.symm
      start := start
      reachFloor_le := fun rank =>
        hstart (start + rank) (Nat.le_add_right start rank)
    }⟩

/-- The maximal honest supplied-source reset-rigid compiler.  It applies the
moving-mark consumer in the exact singleton-minimum arm.  The nested
existentials retain both exact restart equalities and every selected common
refinement. -/
theorem finFourResetRigidEscape_productExit_or_singletonExit_or_supportContraction
    (data : FinFourEscapeProductRestart source)
    (M weight : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    (∃ port : QuittingOffMinimumActualReachPaidPort reward data.originalProfiles
          (quittingTerminalSemanticDebtSum source.point.1) M,
        port.sourceIndex = data.sourceIndex ∧ port.target = data.productProfile) ∨
      ∃ product : data.MinimumRestart,
        (∃ compact : FinFourPositiveNeverSingletonCompactification
              product.releaseInput,
            Nonempty (FinFourPositiveNeverSingletonOffMinimumExit
              product.releaseInput compact M)) ∨
          ∃ compact : FinFourPositiveNeverSingletonCompactification
                product.releaseInput,
            ∃ singleton : FinFourPositiveNeverSingletonMinimumRestart
                product.sourceAtProduct product.releaseInput compact,
              Nonempty (FinFourMovingMarkedPairSupportDescentAlternative
                singleton.moving M weight hweight0 hweight1) := by
  rcases data.offMinimumPaidPort_or_minimumRestart hreward with
    hport | hproduct
  · exact Or.inl hport
  · obtain ⟨product⟩ := hproduct
    obtain ⟨singletonAlternative⟩ :=
      nonempty_finFourPositiveNeverSingletonAlternative
        product.sourceAtProduct product.releaseInput M hreward
    cases singletonAlternative with
    | offMinimum compact exit =>
        exact Or.inr ⟨product, Or.inl ⟨compact, ⟨exit⟩⟩⟩
    | minimum compact singleton =>
        obtain ⟨result⟩ :=
          nonempty_finFourMovingMarkedPairSupportDescentAlternative
            singleton.moving M weight hreward hweight0 hweight1
        exact Or.inr ⟨product, Or.inr ⟨compact, singleton, ⟨result⟩⟩⟩

end GameTheory
