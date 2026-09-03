/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.CompactProofRelevantAdapter
import MathUE.Topology.CompactRankedOutcome
import MathUE.Topology.CompactProjectiveExecution
import MathUE.Topology.CompactSurjectiveInverseLimit

/-!
# An interpreted compact executable trace grammar

`ExecutableTrace` is the literal five-constructor grammar consisting of a
compact-witness edge, a summable decoder, a finite closed case, a bounded
trace-visible rank, and composition.  Its evaluator produces a compact space
of proof-relevant executions.  In particular, composition retains both
component executions and imposes equality of the actual intermediate state.

The projective wrapper at the end uses these evaluated execution types as its
finite spaces.  Thus membership means that an execution was built by the
evaluator; legality is not an additional conclusion postulated by the
projective system.
-/

noncomputable section

namespace Math
namespace Topology

universe u

variable {State : Type u} [MetricSpace State] [CompleteSpace State]

/-- One evaluated grammar edge.  Its execution type retains all witnesses;
the source and target maps expose the actual semantic endpoints. -/
structure CompactExecutableStep (State : Type u)
    [TopologicalSpace State] where
  Execution : Type u
  executionTopology : TopologicalSpace Execution
  executionCompact : @CompactSpace Execution executionTopology
  executionFirstCountable :
    @FirstCountableTopology Execution executionTopology
  executionT2 : @T2Space Execution executionTopology
  source : Execution → State
  target : Execution → State
  source_continuous : @Continuous Execution State executionTopology
    inferInstance source
  target_continuous : @Continuous Execution State executionTopology
    inferInstance target

namespace CompactExecutableStep

variable {Witness Label : Type u}
  [TopologicalSpace Witness] [FirstCountableTopology Witness]
  [T2Space Witness]
  [TopologicalSpace Label] [FirstCountableTopology Label] [T2Space Label]

/-- Evaluate a compact-witness edge without discarding its witness or visible
label. -/
def ofCompactWitness
    (adapter : CompactProofRelevantAdapter State Witness Label State) :
    CompactExecutableStep State := by
  let Execution := adapter.executionSet
  let topology : TopologicalSpace Execution := inferInstance
  let compact : CompactSpace adapter.executionSet :=
    isCompact_iff_compactSpace.mp adapter.isCompact_executionSet
  let firstCountable : FirstCountableTopology adapter.executionSet :=
    inferInstance
  let t2 : T2Space adapter.executionSet := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := fun execution ↦ execution.1.1.1
    target := fun execution ↦ execution.1.2.2
    source_continuous := by fun_prop
    target_continuous := by fun_prop }

variable {Branch : Type u} [Fintype Branch]
  [TopologicalSpace Branch] [DiscreteTopology Branch]

/-- Evaluate a finite closed case.  The branch tag, witness, label, and child
all remain in the execution object. -/
def ofClosedCase
    (adapter : CompactClosedCaseAdapter Branch State Witness Label State) :
    CompactExecutableStep State := by
  let Execution := adapter.executionSet
  let topology : TopologicalSpace Execution := inferInstance
  let compact : CompactSpace adapter.executionSet :=
    isCompact_iff_compactSpace.mp adapter.isCompact_executionSet
  let firstCountable : FirstCountableTopology adapter.executionSet :=
    inferInstance
  let t2 : T2Space adapter.executionSet := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := fun execution ↦ execution.1.2.1.1
    target := fun execution ↦ execution.1.2.2.2
    source_continuous := by
      fun_prop
    target_continuous := by
      fun_prop }

variable {Stage : ℕ → Type u} {Visible Certificate : Type u}
  [∀ depth, TopologicalSpace (Stage depth)]
  [∀ depth, FirstCountableTopology (Stage depth)]
  [∀ depth, T2Space (Stage depth)]
  [MetricSpace Visible] [CompleteSpace Visible]
  [TopologicalSpace Certificate]

/-- Evaluate a summable finite-macro tower on its constructed inverse-limit
code.  One code retains every finite certificate coordinate. -/
def ofSummableDecoder
    (tower : SummableFiniteMacroTower Stage State Visible Certificate) :
    CompactExecutableStep State := by
  let decoder := tower.toSummableExecutableDecoder
  let Execution := decoder.CodePoint
  let topology : TopologicalSpace Execution := inferInstance
  let compact : CompactSpace decoder.CodePoint :=
    isCompact_iff_compactSpace.mp decoder.code_compact
  let firstCountable : FirstCountableTopology decoder.CodePoint :=
    inferInstance
  let t2 : T2Space decoder.CodePoint := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := decoder.initialSource
    target := decoder.decodedState
    source_continuous := decoder.continuous_stateTrack 0
    target_continuous := decoder.continuous_decodedState }

variable {TerminalCertificate SuccessorCertificate : Type u}
  [TopologicalSpace TerminalCertificate]
  [FirstCountableTopology TerminalCertificate]
  [T2Space TerminalCertificate]
  [TopologicalSpace SuccessorCertificate]
  [FirstCountableTopology SuccessorCertificate]
  [T2Space SuccessorCertificate]

/-- Evaluate a bounded trace-visible rank on its genuine recursive execution
type.  A terminal execution retains its terminal certificate; a successor
execution retains its successor certificate and the entire child history. -/
def ofBoundedRank
    (adapter : CompactRankedOutcomeAdapter State TerminalCertificate
      SuccessorCertificate State) :
    CompactExecutableStep State := by
  let Execution := adapter.ExecutionUpTo adapter.rankBound
  let topology : TopologicalSpace Execution := inferInstance
  let compact : CompactSpace Execution := inferInstance
  let firstCountable : FirstCountableTopology Execution := inferInstance
  let t2 : T2Space Execution := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := adapter.executionSource
    target := adapter.executionOutcome
    source_continuous :=
      (adapter.executionLayer adapter.rankBound).source_continuous
    target_continuous :=
      (adapter.executionLayer adapter.rankBound).outcome_continuous }

/-- The literal composability equation for two evaluated executions. -/
def composableSet (first second : CompactExecutableStep State) :
    Set (first.Execution × second.Execution) :=
  {execution | first.target execution.1 = second.source execution.2}

/-- Composition is the closed fiber product over equality of the literal
intermediate state. -/
def comp (first second : CompactExecutableStep State) :
    CompactExecutableStep State := by
  letI : TopologicalSpace first.Execution := first.executionTopology
  letI : CompactSpace first.Execution := first.executionCompact
  letI : FirstCountableTopology first.Execution :=
    first.executionFirstCountable
  letI : T2Space first.Execution := first.executionT2
  letI : TopologicalSpace second.Execution := second.executionTopology
  letI : CompactSpace second.Execution := second.executionCompact
  letI : FirstCountableTopology second.Execution :=
    second.executionFirstCountable
  letI : T2Space second.Execution := second.executionT2
  have hclosed : IsClosed (composableSet first second) := by
    exact isClosed_eq
      (first.target_continuous.comp continuous_fst)
      (second.source_continuous.comp continuous_snd)
  have hcompact : IsCompact (composableSet first second) :=
    hclosed.isCompact
  let Execution := composableSet first second
  let topology : TopologicalSpace Execution := inferInstance
  let compact : CompactSpace (composableSet first second) :=
    isCompact_iff_compactSpace.mp hcompact
  let firstCountable : FirstCountableTopology
      (composableSet first second) := inferInstance
  let t2 : T2Space (composableSet first second) := inferInstance
  exact {
    Execution := Execution
    executionTopology := topology
    executionCompact := compact
    executionFirstCountable := firstCountable
    executionT2 := t2
    source := fun execution ↦ first.source execution.1.1
    target := fun execution ↦ second.target execution.1.2
    source_continuous := by
      exact (first.source_continuous.comp continuous_fst).comp
        continuous_subtype_val
    target_continuous := by
      exact (second.target_continuous.comp continuous_snd).comp
        continuous_subtype_val }

end CompactExecutableStep

/-- Literal interpreted syntax of the five trace-visible constructors.  Each
atomic constructor accepts exactly the corresponding audited interface. -/
inductive ExecutableTrace (State : Type u)
    [MetricSpace State] [CompleteSpace State] : Type (u + 1)
  | compactWitness {Witness Label : Type u}
      [TopologicalSpace Witness] [FirstCountableTopology Witness]
      [T2Space Witness]
      [TopologicalSpace Label] [FirstCountableTopology Label] [T2Space Label]
      (adapter : CompactProofRelevantAdapter State Witness Label State)
  | summableDecoder {Stage : ℕ → Type u} {Visible Certificate : Type u}
      [∀ depth, TopologicalSpace (Stage depth)]
      [∀ depth, FirstCountableTopology (Stage depth)]
      [∀ depth, T2Space (Stage depth)]
      [MetricSpace Visible] [CompleteSpace Visible]
      [TopologicalSpace Certificate]
      (tower : SummableFiniteMacroTower Stage State Visible Certificate)
  | closedCase {Branch Witness Label : Type u}
      [Fintype Branch] [TopologicalSpace Branch] [DiscreteTopology Branch]
      [TopologicalSpace Witness] [FirstCountableTopology Witness]
      [T2Space Witness]
      [TopologicalSpace Label] [FirstCountableTopology Label] [T2Space Label]
      (adapter : CompactClosedCaseAdapter Branch State Witness Label State)
  | boundedRank {TerminalCertificate SuccessorCertificate : Type u}
      [TopologicalSpace TerminalCertificate]
      [FirstCountableTopology TerminalCertificate]
      [T2Space TerminalCertificate]
      [TopologicalSpace SuccessorCertificate]
      [FirstCountableTopology SuccessorCertificate]
      [T2Space SuccessorCertificate]
      (adapter : CompactRankedOutcomeAdapter State TerminalCertificate
        SuccessorCertificate State)
  | composition (first second : ExecutableTrace State)

namespace ExecutableTrace

/-- Evaluate syntax to its compact proof-relevant execution space. -/
def evaluate : ExecutableTrace State → CompactExecutableStep State
  | @compactWitness _ _ _ Witness Label witnessTopology witnessFirstCountable
      witnessT2 labelTopology labelFirstCountable labelT2 adapter =>
      @CompactExecutableStep.ofCompactWitness State _ Witness Label
        witnessTopology witnessFirstCountable witnessT2 labelTopology
        labelFirstCountable labelT2 adapter
  | @summableDecoder _ _ _ Stage Visible Certificate stageTopology
      stageFirstCountable stageT2 visibleMetric visibleComplete
      certificateTopology tower =>
      @CompactExecutableStep.ofSummableDecoder State _ _ Stage Visible
        Certificate stageTopology stageFirstCountable stageT2 visibleMetric
        visibleComplete certificateTopology tower
  | @closedCase _ _ _ Branch Witness Label branchFintype branchTopology
      branchDiscrete witnessTopology witnessFirstCountable witnessT2
      labelTopology labelFirstCountable labelT2 adapter =>
      @CompactExecutableStep.ofClosedCase State _ Witness Label
        witnessTopology witnessFirstCountable witnessT2 labelTopology
        labelFirstCountable labelT2 Branch branchFintype branchTopology
        branchDiscrete adapter
  | @boundedRank _ _ _ TerminalCertificate SuccessorCertificate
      terminalTopology terminalFirstCountable terminalT2 successorTopology
      successorFirstCountable successorT2 adapter =>
      @CompactExecutableStep.ofBoundedRank State _ TerminalCertificate
        SuccessorCertificate terminalTopology terminalFirstCountable
        terminalT2 successorTopology successorFirstCountable successorT2
        adapter
  | .composition first second =>
      CompactExecutableStep.comp (evaluate first) (evaluate second)

/-- An evaluated execution with its exact exposed endpoints. -/
def Realizes (trace : ExecutableTrace State) (source target : State) : Type u :=
  {execution : trace.evaluate.Execution //
    trace.evaluate.source execution = source ∧
      trace.evaluate.target execution = target}

/-- Composition retains the two executions and their literal common state. -/
def composeRealization
    {first second : ExecutableTrace State}
    {source middle target : State}
    (firstExecution : first.Realizes source middle)
    (secondExecution : second.Realizes middle target) :
    (ExecutableTrace.composition first second).Realizes source target := by
  let pair : first.evaluate.Execution × second.evaluate.Execution :=
    (firstExecution.1, secondExecution.1)
  have hcomposable : first.evaluate.target pair.1 =
      second.evaluate.source pair.2 := by
    rw [firstExecution.2.2, secondExecution.2.1]
  let combined : (CompactExecutableStep.comp first.evaluate
      second.evaluate).Execution := by
    change CompactExecutableStep.composableSet first.evaluate
      second.evaluate
    exact ⟨pair, hcomposable⟩
  let result : { execution : (CompactExecutableStep.comp first.evaluate
      second.evaluate).Execution //
    (CompactExecutableStep.comp first.evaluate second.evaluate).source
        execution = source ∧
      (CompactExecutableStep.comp first.evaluate second.evaluate).target
        execution = target } :=
    ⟨combined, ⟨firstExecution.2.1, secondExecution.2.2⟩⟩
  simpa only [Realizes, evaluate] using result

/-- Every trace has a compact proof-relevant execution space. -/
theorem compactSpace_execution (trace : ExecutableTrace State) :
    @CompactSpace trace.evaluate.Execution
      trace.evaluate.executionTopology :=
  trace.evaluate.executionCompact

end ExecutableTrace

/-! ## Literal finite execution towers -/

/-- A restriction-compatible tower of literal evaluated traces from one fixed
singleton source.  `Controller` is the common controller observable.
`Diagram depth` is the named finite syntax/diagram certificate at that depth;
its own restriction laws make shared occurrences literal rather than prose. -/
structure InterpretedExecutableTraceTower
    (State Controller : Type u) (Diagram : ℕ → Type u)
    [MetricSpace State] [CompleteSpace State]
    [TopologicalSpace Controller]
    [∀ depth, TopologicalSpace (Diagram depth)] where
  trace : ℕ → ExecutableTrace State
  initialSource : State
  restriction : ∀ smaller larger, smaller ≤ larger →
    (trace larger).evaluate.Execution →
      (trace smaller).evaluate.Execution
  restriction_continuous : ∀ smaller larger (hle : smaller ≤ larger),
    @Continuous (trace larger).evaluate.Execution
      (trace smaller).evaluate.Execution
      (trace larger).evaluate.executionTopology
      (trace smaller).evaluate.executionTopology
      (restriction smaller larger hle)
  restriction_id : ∀ depth execution,
    restriction depth depth le_rfl execution = execution
  restriction_trans : ∀ first second third
      (hfirst : first ≤ second) (hsecond : second ≤ third) execution,
    restriction first third (hfirst.trans hsecond) execution =
      restriction first second hfirst
        (restriction second third hsecond execution)
  source_eq_initial : ∀ depth execution,
    (trace depth).evaluate.source execution = initialSource
  restriction_source : ∀ smaller larger (hle : smaller ≤ larger)
      execution,
    (trace smaller).evaluate.source
        (restriction smaller larger hle execution) =
      (trace larger).evaluate.source execution
  restriction_target : ∀ smaller larger (hle : smaller ≤ larger)
      execution,
    (trace smaller).evaluate.target
        (restriction smaller larger hle execution) =
      (trace larger).evaluate.target execution
  controller : ∀ depth, (trace depth).evaluate.Execution → Controller
  controller_continuous : ∀ depth,
    @Continuous (trace depth).evaluate.Execution Controller
      (trace depth).evaluate.executionTopology inferInstance
      (controller depth)
  restriction_controller : ∀ smaller larger (hle : smaller ≤ larger)
      execution,
    controller smaller (restriction smaller larger hle execution) =
      controller larger execution
  diagram : ∀ depth, (trace depth).evaluate.Execution → Diagram depth
  diagram_continuous : ∀ depth,
    @Continuous (trace depth).evaluate.Execution (Diagram depth)
      (trace depth).evaluate.executionTopology inferInstance
      (diagram depth)
  diagramRestriction : ∀ smaller larger, smaller ≤ larger →
    Diagram larger → Diagram smaller
  diagramRestriction_continuous : ∀ smaller larger
      (hle : smaller ≤ larger),
    Continuous (diagramRestriction smaller larger hle)
  diagramRestriction_id : ∀ depth diagramPoint,
    diagramRestriction depth depth le_rfl diagramPoint = diagramPoint
  diagramRestriction_trans : ∀ first second third
      (hfirst : first ≤ second) (hsecond : second ≤ third) diagramPoint,
    diagramRestriction first third (hfirst.trans hsecond) diagramPoint =
      diagramRestriction first second hfirst
        (diagramRestriction second third hsecond diagramPoint)
  restriction_diagram : ∀ smaller larger (hle : smaller ≤ larger)
      execution,
    diagram smaller (restriction smaller larger hle execution) =
      diagramRestriction smaller larger hle (diagram larger execution)

namespace InterpretedExecutableTraceTower

variable {Controller : Type u} {Diagram : ℕ → Type u}
  [TopologicalSpace Controller]
  [∀ depth, TopologicalSpace (Diagram depth)]
  (tower : InterpretedExecutableTraceTower State Controller Diagram)

/-- The proof-relevant evaluated execution type at one finite depth. -/
abbrev Execution (depth : ℕ) := (tower.trace depth).evaluate.Execution

noncomputable instance executionTopology (depth : ℕ) :
    TopologicalSpace (tower.Execution depth) :=
  (tower.trace depth).evaluate.executionTopology

noncomputable instance executionCompact (depth : ℕ) :
    CompactSpace (tower.Execution depth) :=
  (tower.trace depth).evaluate.executionCompact

noncomputable instance executionFirstCountable (depth : ℕ) :
    FirstCountableTopology (tower.Execution depth) :=
  (tower.trace depth).evaluate.executionFirstCountable

noncomputable instance executionT2 (depth : ℕ) :
    T2Space (tower.Execution depth) :=
  (tower.trace depth).evaluate.executionT2

/-- Forget only that evaluator membership is carried in the type, obtaining
the generic projective-system interface with universal carriers. -/
def toCompactProjectiveExecutionSystem :
    CompactProjectiveExecutionSystem tower.Execution where
  executionSet := fun _ ↦ Set.univ
  execution_compact := fun _ ↦ isCompact_univ
  restriction := tower.restriction
  restriction_continuous := tower.restriction_continuous
  restriction_mem := by simp
  restriction_id := tower.restriction_id
  restriction_trans := tower.restriction_trans

/-- A cofinal sequence of literal finite trace executions therefore has one
common projective subsequence limit.  No legality predicate is assumed by
this theorem: each input and limit coordinate has evaluator execution type. -/
theorem exists_projectiveSubsequenceLimit
    (sequence : tower.toCompactProjectiveExecutionSystem.CofinalExecutionSequence) :
    Nonempty
      (tower.toCompactProjectiveExecutionSystem.ProjectiveSubsequenceLimit
        sequence) :=
  tower.toCompactProjectiveExecutionSystem.exists_projectiveSubsequenceLimit
    sequence

/-- A syntax/diagram family compatible under the tower's named restriction
maps. -/
structure CompatibleDiagram where
  point : ∀ depth, Diagram depth
  compatible : ∀ smaller larger (hle : smaller ≤ larger),
    tower.diagramRestriction smaller larger hle (point larger) = point smaller

/-- The strengthened projective output: one subsequence, one shared
controller, one compatible named diagram family, and one common pair of
exposed endpoints, all beginning at the literal singleton source. -/
structure SharedProjectiveSubsequenceLimit
    (sequence : tower.toCompactProjectiveExecutionSystem.CofinalExecutionSequence)
    where
  projective :
    tower.toCompactProjectiveExecutionSystem.ProjectiveSubsequenceLimit
      sequence
  sharedController : Controller
  controller_eq : ∀ depth,
    tower.controller depth (projective.limit.point depth).1 = sharedController
  controller_tendsto : ∀ depth,
    Filter.Tendsto (fun rank ↦ tower.controller depth
      (CompactProjectiveExecutionSystem.CofinalExecutionSequence.restrictedPoint
        tower.toCompactProjectiveExecutionSystem sequence
        (projective.subsequence rank) depth).1)
      Filter.atTop (nhds sharedController)
  compatibleDiagram : tower.CompatibleDiagram
  diagram_eq : ∀ depth,
    compatibleDiagram.point depth =
      tower.diagram depth (projective.limit.point depth).1
  diagram_tendsto : ∀ depth,
    Filter.Tendsto (fun rank ↦ tower.diagram depth
      (CompactProjectiveExecutionSystem.CofinalExecutionSequence.restrictedPoint
        tower.toCompactProjectiveExecutionSystem sequence
        (projective.subsequence rank) depth).1)
      Filter.atTop (nhds (compatibleDiagram.point depth))
  commonSource : State
  source_eq : ∀ depth,
    (tower.trace depth).evaluate.source
        (projective.limit.point depth).1 = commonSource
  source_eq_initial : commonSource = tower.initialSource
  commonTarget : State
  target_eq : ∀ depth,
    (tower.trace depth).evaluate.target
        (projective.limit.point depth).1 = commonTarget

/-- Restriction compatibility identifies the underlying evaluator executions
at two projective depths. -/
private theorem limit_restriction_eq
    {sequence : tower.toCompactProjectiveExecutionSystem.CofinalExecutionSequence}
    (projective :
      tower.toCompactProjectiveExecutionSystem.ProjectiveSubsequenceLimit
        sequence)
    (smaller larger : ℕ) (hle : smaller ≤ larger) :
    tower.restriction smaller larger hle
        (projective.limit.point larger).1 =
      (projective.limit.point smaller).1 := by
  exact congrArg Subtype.val (projective.limit.compatible smaller larger hle)

/-- A cofinal sequence of literal evaluated diagrams has one common
subsequence limit whose controller is shared at every depth and whose named
syntax certificates form one compatible diagram family. -/
theorem exists_sharedProjectiveSubsequenceLimit
    (sequence : tower.toCompactProjectiveExecutionSystem.CofinalExecutionSequence) :
    Nonempty (tower.SharedProjectiveSubsequenceLimit sequence) := by
  obtain ⟨projective⟩ := tower.exists_projectiveSubsequenceLimit sequence
  let sharedController :=
    tower.controller 0 (projective.limit.point 0).1
  have hcontroller : ∀ depth,
      tower.controller depth (projective.limit.point depth).1 =
        sharedController := by
    intro depth
    rw [← tower.restriction_controller 0 depth (Nat.zero_le depth)
      (projective.limit.point depth).1]
    exact congrArg (tower.controller 0)
      (tower.limit_restriction_eq projective 0 depth (Nat.zero_le depth))
  have hcontrollerTendsto : ∀ depth,
      Filter.Tendsto (fun rank ↦ tower.controller depth
        (CompactProjectiveExecutionSystem.CofinalExecutionSequence.restrictedPoint
          tower.toCompactProjectiveExecutionSystem sequence
          (projective.subsequence rank) depth).1)
        Filter.atTop (nhds sharedController) := by
    intro depth
    have hcontinuous : Continuous (fun point :
        tower.toCompactProjectiveExecutionSystem.ExecutionPoint depth ↦
          tower.controller depth point.1) :=
      (tower.controller_continuous depth).comp continuous_subtype_val
    have htendsto := hcontinuous.continuousAt.tendsto.comp
      (projective.restriction_tendsto depth)
    change Filter.Tendsto (fun rank ↦ tower.controller depth
      (CompactProjectiveExecutionSystem.CofinalExecutionSequence.restrictedPoint
        tower.toCompactProjectiveExecutionSystem sequence
        (projective.subsequence rank) depth).1)
      Filter.atTop
      (nhds (tower.controller depth (projective.limit.point depth).1))
      at htendsto
    rw [hcontroller depth] at htendsto
    exact htendsto
  let compatibleDiagram : tower.CompatibleDiagram := {
    point := fun depth ↦
      tower.diagram depth (projective.limit.point depth).1
    compatible := by
      intro smaller larger hle
      rw [← tower.restriction_diagram smaller larger hle
        (projective.limit.point larger).1]
      exact congrArg (tower.diagram smaller)
        (tower.limit_restriction_eq projective smaller larger hle) }
  have hdiagramTendsto : ∀ depth,
      Filter.Tendsto (fun rank ↦ tower.diagram depth
        (CompactProjectiveExecutionSystem.CofinalExecutionSequence.restrictedPoint
          tower.toCompactProjectiveExecutionSystem sequence
          (projective.subsequence rank) depth).1)
        Filter.atTop (nhds (compatibleDiagram.point depth)) := by
    intro depth
    have hcontinuous : Continuous (fun point :
        tower.toCompactProjectiveExecutionSystem.ExecutionPoint depth ↦
          tower.diagram depth point.1) :=
      (tower.diagram_continuous depth).comp continuous_subtype_val
    have htendsto := hcontinuous.continuousAt.tendsto.comp
      (projective.restriction_tendsto depth)
    change Filter.Tendsto (fun rank ↦ tower.diagram depth
      (CompactProjectiveExecutionSystem.CofinalExecutionSequence.restrictedPoint
        tower.toCompactProjectiveExecutionSystem sequence
        (projective.subsequence rank) depth).1)
      Filter.atTop
      (nhds (tower.diagram depth (projective.limit.point depth).1))
      at htendsto
    exact htendsto
  let commonTarget :=
    (tower.trace 0).evaluate.target (projective.limit.point 0).1
  have htarget : ∀ depth,
      (tower.trace depth).evaluate.target
          (projective.limit.point depth).1 = commonTarget := by
    intro depth
    rw [← tower.restriction_target 0 depth (Nat.zero_le depth)
      (projective.limit.point depth).1]
    exact congrArg (tower.trace 0).evaluate.target
      (tower.limit_restriction_eq projective 0 depth (Nat.zero_le depth))
  exact ⟨{
    projective := projective
    sharedController := sharedController
    controller_eq := hcontroller
    controller_tendsto := hcontrollerTendsto
    compatibleDiagram := compatibleDiagram
    diagram_eq := fun _ ↦ rfl
    diagram_tendsto := hdiagramTendsto
    commonSource := tower.initialSource
    source_eq := fun depth ↦
      tower.source_eq_initial depth (projective.limit.point depth).1
    source_eq_initial := rfl
    commonTarget := commonTarget
    target_eq := htarget }⟩

end InterpretedExecutableTraceTower

end Topology
end Math
