import UniformEquilibrium.Quitting.Projective.RobustChargedRelation

/-! # Literal states, roots, and charges along robust paths -/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}
variable {tolerance bound : ℝ}

/-- The boxed state visited at a date of a robust charged path. Past its
terminal date the path remains at its target. -/
def quittingRobustChargedPathValue {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) : ℕ → QuittingRobustChargedState player bound :=
  match path with
  | .nil state => fun _ ↦ state
  | .cons edge rest => fun
      | 0 => (quittingFloorFreeRobustChargedRelation
          reward tolerance bound).src edge
      | time + 1 => quittingRobustChargedPathValue rest time

/-- The simplex root stored on a robust path edge. Past the path horizon an
arbitrary all-Continue root is returned; packet claims use only live dates. -/
def quittingRobustChargedPathRoot {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) : ℕ → QuittingRootSimplex player :=
  match path with
  | .nil _state => fun _ ↦
      quittingSimplexOfRoot (fun _ ↦ PMF.pure false)
  | .cons edge rest => fun
      | 0 => edge.1.1.2
      | time + 1 => quittingRobustChargedPathRoot rest time

@[simp] theorem quittingRobustChargedPathValue_zero {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) :
    quittingRobustChargedPathValue path 0 = source := by
  cases path <;> rfl

theorem quittingRobustChargedPath_step {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) {time : ℕ} (htime : time < path.length) :
    IsQuittingFloorFreeRobustEdge reward tolerance bound
      (quittingRobustChargedPathValue path time)
      (quittingRobustChargedPathRoot path time)
      (quittingRobustChargedPathValue path (time + 1)) := by
  induction path generalizing time with
  | nil state => simp at htime
  | cons edge rest ih =>
      cases time with
      | zero =>
          simp only [quittingRobustChargedPathValue,
            quittingRobustChargedPathRoot,
            quittingRobustChargedPathValue_zero]
          change IsQuittingFloorFreeRobustEdge reward tolerance bound
            edge.1.1.1 edge.1.1.2 edge.1.2
          exact edge.2
      | succ time =>
          have hrest : time < rest.length := by
            simpa only [Math.ChargedPathBudget.ChargedRelation.Path.length_cons,
              Nat.add_lt_add_iff_right] using htime
          simpa only [quittingRobustChargedPathValue,
            quittingRobustChargedPathRoot, Nat.succ_eq_add_one] using ih hrest

theorem quittingRobustChargedPath_chargeSum_eq {source target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) :
    path.chargeSum =
      ∑ time ∈ Finset.range path.length,
        quittingRootAbsorptionMass
          (quittingRootOfSimplex (quittingRobustChargedPathRoot path time)) := by
  induction path with
  | nil state => simp [quittingRobustChargedPathRoot]
  | cons edge rest ih =>
      rw [Math.ChargedPathBudget.ChargedRelation.Path.chargeSum_cons,
        Math.ChargedPathBudget.ChargedRelation.Path.length_cons,
        Finset.sum_range_succ']
      simp only [quittingRobustChargedPathRoot]
      have hedgeCharge :
          (quittingFloorFreeRobustChargedRelation reward tolerance bound).charge
              edge = quittingRootAbsorptionMass
                (quittingRootOfSimplex edge.1.1.2) := rfl
      rw [hedgeCharge, ih]
      ring

@[simp] theorem quittingRobustChargedPathValue_castTgt {source target target'}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) (h : target = target') (time : ℕ) :
    quittingRobustChargedPathValue (path.castTgt h) time =
      quittingRobustChargedPathValue path time := by
  subst h
  rfl

@[simp] theorem quittingRobustChargedPathRoot_castTgt {source target target'}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) (h : target = target') (time : ℕ) :
    quittingRobustChargedPathRoot (path.castTgt h) time =
      quittingRobustChargedPathRoot path time := by
  subst h
  rfl

@[simp] theorem quittingRobustChargedPathValue_castSrc {source source' target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) (h : source = source') (time : ℕ) :
    quittingRobustChargedPathValue (path.castSrc h) time =
      quittingRobustChargedPathValue path time := by
  subst h
  rfl

@[simp] theorem quittingRobustChargedPathRoot_castSrc {source source' target}
    (path : (quittingFloorFreeRobustChargedRelation reward tolerance bound).Path
      source target) (h : source = source') (time : ℕ) :
    quittingRobustChargedPathRoot (path.castSrc h) time =
      quittingRobustChargedPathRoot path time := by
  subst h
  rfl

end GameTheory
