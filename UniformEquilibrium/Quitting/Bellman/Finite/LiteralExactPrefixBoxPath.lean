import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargedRelation
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-! # Literal exact-prefix words as full-box charged paths

Every supplied literal exact root word over an actual terminal profile
decodes to a path in the full boxed predecessor relation. The source keeps its
supplied decoration, including for the empty word. Endpoint payoff, outermost
root decoration, absorption charge, and path length are retained exactly.
No punishment-floor condition is imposed.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- An actual terminal profile, with a supplied simplex decoration, as a canonical
full-box state. -/
def quittingActualProfileBoxState
    (profile : (quittingGame reward).BehaviorProfile)
    (decoration : QuittingRootSimplex ι) :
    QuittingPunishmentFloorBoxState reward := by
  refine ⟨(fun who ↦ quittingTerminalPayoff reward profile who, decoration), ?_⟩
  constructor <;> intro who
  · have h := abs_quittingTerminalPayoff_le_quittingRewardBound reward profile who
    rw [abs_le] at h
    exact h.1
  · have h := abs_quittingTerminalPayoff_le_quittingRewardBound reward profile who
    rw [abs_le] at h
    exact h.2

@[simp] theorem quittingActualProfileBoxState_payoff
    (profile : (quittingGame reward).BehaviorProfile)
    (decoration : QuittingRootSimplex ι) :
    (quittingActualProfileBoxState profile decoration).1.1 =
      fun who ↦ quittingTerminalPayoff reward profile who := rfl

@[simp] theorem quittingActualProfileBoxState_decoration
    (profile : (quittingGame reward).BehaviorProfile)
    (decoration : QuittingRootSimplex ι) :
    (quittingActualProfileBoxState profile decoration).1.2 = decoration := rfl

/-- The exact boxed edge obtained by prepending one literal exact root to an
actual continuation profile. -/
def quittingLiteralExactOneRootBoxEdge
    (root : ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (tailDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward [root] terminal) :
    QuittingPunishmentFloorBoxEdge reward where
  tail := quittingActualProfileBoxState terminal tailDecoration
  current := quittingActualProfileBoxState
    (quittingLiteralRootStackProfile reward [root] terminal)
    (quittingSimplexOfRoot root)
  exactEdge := by
    change (fun who ↦ quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward [root] terminal) who) =
        quittingRootSuccessorPayoff reward
          (fun who ↦ quittingTerminalPayoff reward terminal who)
          (quittingRootOfSimplex (quittingSimplexOfRoot root)) ∧
      IsεQuittingRootEndpointNash reward
        (fun who ↦ quittingTerminalPayoff reward terminal who) 0
        (quittingRootOfSimplex (quittingSimplexOfRoot root))
    constructor
    · funext who
      rw [quittingRootOfSimplex_simplexOfRoot,
        quittingLiteralRootStackProfile_cons,
        quittingLiteralRootStackProfile_nil,
        quittingTerminalPayoff_rootThenContinuation_eq]
      unfold quittingRootSuccessorPayoff quittingRootExpectedPayoff
      rfl
    · rw [quittingRootOfSimplex_simplexOfRoot]
      exact hexact.1

@[simp] theorem quittingLiteralExactOneRootBoxEdge_root
    (root : ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (tailDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward [root] terminal) :
    (quittingLiteralExactOneRootBoxEdge root terminal tailDecoration hexact).root = root := by
  unfold quittingLiteralExactOneRootBoxEdge QuittingPunishmentFloorBoxEdge.root
  change quittingRootOfSimplex (quittingSimplexOfRoot root) = root
  rw [quittingRootOfSimplex_simplexOfRoot]

@[simp] theorem quittingLiteralExactOneRootBoxEdge_absorptionCharge
    (root : ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (tailDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward [root] terminal) :
    (quittingLiteralExactOneRootBoxEdge root terminal tailDecoration hexact).absorptionCharge =
      quittingRootAbsorptionMass root := by
  unfold QuittingPunishmentFloorBoxEdge.absorptionCharge
  rw [quittingLiteralExactOneRootBoxEdge_root]

/-- The one-root edge as a literal charged path from the decorated actual tail. -/
def quittingLiteralExactOneRootBoxPath
    (root : ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (tailDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward [root] terminal) :
    (quittingPunishmentFloorBoxChargedRelation reward).Path
      (quittingActualProfileBoxState terminal tailDecoration)
      (quittingActualProfileBoxState
        (quittingLiteralRootStackProfile reward [root] terminal)
        (quittingSimplexOfRoot root)) :=
  ChargedRelation.Path.single
    (quittingLiteralExactOneRootBoxEdge root terminal tailDecoration hexact)

@[simp] theorem quittingLiteralExactOneRootBoxPath_chargeSum
    (root : ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (tailDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward [root] terminal) :
    (quittingLiteralExactOneRootBoxPath root terminal tailDecoration hexact).chargeSum =
      quittingRootAbsorptionMass root := by
  change (quittingLiteralExactOneRootBoxEdge root terminal tailDecoration hexact).absorptionCharge +
    0 = quittingRootAbsorptionMass root
  rw [quittingLiteralExactOneRootBoxEdge_absorptionCharge]
  ring

/-- The outermost root decorates a nonempty word endpoint; the supplied decoration
is retained for the empty word. -/
def quittingLiteralExactWordEndpointDecoration
    (roots : List (ι → PMF Bool)) (sourceDecoration : QuittingRootSimplex ι) :
    QuittingRootSimplex ι :=
  match roots with
  | [] => sourceDecoration
  | root :: _ => quittingSimplexOfRoot root

/-- Canonical full-box endpoint of a literal root word over an actual source. -/
def quittingLiteralExactWordEndpointState
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι) :
    QuittingPunishmentFloorBoxState reward :=
  quittingActualProfileBoxState
    (quittingLiteralRootStackProfile reward roots terminal)
    (quittingLiteralExactWordEndpointDecoration roots sourceDecoration)

@[simp] theorem quittingLiteralExactWordEndpointState_nil
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι) :
    quittingLiteralExactWordEndpointState ([] : List (ι → PMF Bool)) terminal
      sourceDecoration = quittingActualProfileBoxState terminal sourceDecoration := rfl

@[simp] theorem quittingLiteralExactWordEndpointState_payoff
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι) :
    (quittingLiteralExactWordEndpointState roots terminal sourceDecoration).1.1 =
      fun who ↦ quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots terminal) who := rfl

@[simp] theorem quittingLiteralExactWordEndpointState_cons_decoration
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι) :
    (quittingLiteralExactWordEndpointState (root :: roots) terminal
      sourceDecoration).1.2 = quittingSimplexOfRoot root := rfl

private theorem isQuittingLiteralExactRootStack_single
    (root : ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (hexact : IsεQuittingRootEndpointNash reward
      (fun who ↦ quittingTerminalPayoff reward terminal who) 0 root) :
    IsQuittingLiteralExactRootStack reward [root] terminal := by
  rw [isQuittingLiteralExactRootStack_cons_iff]
  exact ⟨by simpa only [quittingLiteralRootStackProfile_nil], trivial⟩

/-- Decode an arbitrary literal exact root word into a full-box charged path. -/
def quittingLiteralExactWordBoxPath
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward roots terminal) :
    (quittingPunishmentFloorBoxChargedRelation reward).Path
      (quittingActualProfileBoxState terminal sourceDecoration)
      (quittingLiteralExactWordEndpointState roots terminal sourceDecoration) := by
  induction roots with
  | nil => exact ChargedRelation.Path.nil _
  | cons root roots ih =>
      rw [isQuittingLiteralExactRootStack_cons_iff] at hexact
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      let tailDecoration :=
        quittingLiteralExactWordEndpointDecoration roots sourceDecoration
      have hone : IsQuittingLiteralExactRootStack reward [root] suffix :=
        isQuittingLiteralExactRootStack_single root suffix (by
          simpa only [suffix] using hexact.1)
      exact (ih hexact.2).append (quittingLiteralExactOneRootBoxPath
        root suffix tailDecoration hone)

@[simp] theorem quittingLiteralExactWordBoxPath_nil
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward [] terminal) :
    quittingLiteralExactWordBoxPath [] terminal sourceDecoration hexact =
      ChargedRelation.Path.nil (quittingActualProfileBoxState terminal sourceDecoration) := rfl

/-- Decoding preserves the sum of the actual absorption masses of all roots. -/
theorem quittingLiteralExactWordBoxPath_chargeSum
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward roots terminal) :
    (quittingLiteralExactWordBoxPath roots terminal sourceDecoration hexact).chargeSum =
      (roots.map quittingRootAbsorptionMass).sum := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      rw [isQuittingLiteralExactRootStack_cons_iff] at hexact
      change
        ((quittingLiteralExactWordBoxPath roots terminal sourceDecoration hexact.2).append
          (quittingLiteralExactOneRootBoxPath root
            (quittingLiteralRootStackProfile reward roots terminal)
            (quittingLiteralExactWordEndpointDecoration roots sourceDecoration) _)).chargeSum = _
      rw [ChargedRelation.Path.chargeSum_append]
      rw [ih hexact.2]
      unfold quittingLiteralExactWordEndpointState
      rw [quittingLiteralExactOneRootBoxPath_chargeSum]
      simp only [List.map_cons, List.sum_cons]
      exact add_comm _ _

/-- Decoding uses exactly one full-box edge for each literal root. -/
theorem quittingLiteralExactWordBoxPath_length
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (sourceDecoration : QuittingRootSimplex ι)
    (hexact : IsQuittingLiteralExactRootStack reward roots terminal) :
    (quittingLiteralExactWordBoxPath roots terminal sourceDecoration hexact).length =
      roots.length := by
  induction roots with
  | nil => rfl
  | cons root roots ih =>
      rw [isQuittingLiteralExactRootStack_cons_iff] at hexact
      change
        ((quittingLiteralExactWordBoxPath roots terminal sourceDecoration hexact.2).append
          (quittingLiteralExactOneRootBoxPath root
            (quittingLiteralRootStackProfile reward roots terminal)
            (quittingLiteralExactWordEndpointDecoration roots sourceDecoration) _)).length = _
      rw [ChargedRelation.Path.length_append, ih hexact.2]
      change roots.length + 1 = (root :: roots).length
      rfl

end GameTheory

